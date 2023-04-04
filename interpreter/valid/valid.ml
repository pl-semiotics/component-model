module Source = Wasm.Source
open Source
open Ast
(*open Putil*)
open Etypes
open Elaborate
open Substitute
open Subtype
module I = Ast.IntAst

exception Invalid = Etypes.Invalid

let xyz err = raise (Sys_error ("xyz " ^ err))

module CA = Wasm.Ast

let infer_core_import (ctx : ctx) (cmd : CA.module_) (i : CA.import)
    : core_import_decl
  = { cid_name1 = Wasm.Utf8.encode i.it.CA.module_name @@ i.at
    ; cid_name2 = Wasm.Utf8.encode i.it.CA.item_name @@ i.at
    ; cid_desc = Wasm.Ast.import_type cmd i
    }
let infer_core_export (ctx : ctx) (cmd : CA.module_) (e : CA.export)
    : core_export_decl
  = { ced_name = Wasm.Utf8.encode e.it.CA.name @@ e.at
    ; ced_desc = Wasm.Ast.export_type cmd e
    }
let infer_core_module (ctx : ctx) (cmd : Wasm.Ast.module_) : core_module_type
  =
  { cmt_imports = List.map (infer_core_import ctx cmd) cmd.it.CA.imports
  ; cmt_instance = {
      cit_exports = List.map (infer_core_export ctx cmd) cmd.it.CA.exports
    }
  }

let check_uniqueness_ : 'a. string -> ('a -> string) -> 'a phrase list -> 'a phrase -> unit
  = fun err project all this ->
  if (List.length
        (List.filter (fun this' -> project this'.it = project this.it) all)
      <> 1)
  then raise (Invalid (this.at, err ^ project this.it))
  else ()
let check_uniqueness : 'a. string -> ('a -> string) -> 'a phrase list -> unit
  = fun err project all ->
  List.iter (check_uniqueness_ err project all) all

let find_core_instantiate_arg_named ctx cias name =
  try List.find (fun cia -> cia.it.I.c_ia_name.it = name.it) cias
  with Not_found ->
    raise (Invalid (name.at, "Expected to find instantiate arg " ^ name.it))
let find_core_export_named ctx cit name
  = try List.find (fun ced -> ced.ced_name.it = name.it) cit.cit_exports
    with Not_found ->
      raise (Invalid (name.at, "Expected to find export " ^ name.it))
let check_core_instantiate_import ctx cias cid
  = let cia = find_core_instantiate_arg_named ctx cias cid.cid_name1 in
    if (cia.it.I.c_ia_value.it.I.c_s_sort.it <> Ast.Core_instance)
    then raise (Invalid (cia.at, "Only two-level imports are suported"))
    else ();
    let cit = List.nth ctx.core_ctx.core_instances
                (Int32.to_int cia.it.I.c_ia_value.it.I.c_s_idx) in
    let ced = find_core_export_named ctx cit cid.cid_name2 in
    subtype_core_extern_desc ctx ced.ced_desc cid.cid_desc
let infer_core_export (ctx : ctx) (e : I.core_export) : core_export_decl
  = { ced_name = e.it.I.c_e_name
    ; ced_desc =
        let i = Int32.to_int e.it.I.c_e_value.it.I.c_s_idx in
        let open Wasm.Types in
        match e.it.I.c_e_value.it.I.c_s_sort.it with
        | Core_func -> ExternFuncType (List.nth ctx.core_ctx.core_funcs i)
        | Core_table -> ExternTableType (List.nth ctx.core_ctx.core_tables i)
        | Core_memory -> ExternMemoryType (List.nth ctx.core_ctx.core_mems i)
        | Core_global -> ExternGlobalType (List.nth ctx.core_ctx.core_globals i)
        | s -> raise (Invalid (e.at, "Cannot inline-export core sort "
                                     ^ show_core_sort' s))
    }
let infer_core_instance (ctx : ctx) (es : I.core_export list)
    : core_instance_type
  =  { cit_exports = List.map (infer_core_export ctx) es }
let infer_core_defn (ctx : ctx) (d : I.core_definition)
    : ctx
  = match d with
  | I.CoreModuleDef cmd ->
     let cmt = infer_core_module ctx cmd in
     { ctx with
       core_ctx = { ctx.core_ctx with
                    core_modules = ctx.core_ctx.core_modules @ [cmt] } }
  | I.CoreInstanceDef { it = I.Core_instantiate_module (cmid, cias);
                        at = at } ->
     let cmt = List.nth ctx.core_ctx.core_modules (Int32.to_int cmid) in
     List.iter (check_core_instantiate_import ctx cias) cmt.cmt_imports;
     check_uniqueness "Duplicate instantiate arg name "
       (fun x -> x.I.c_ia_name.it) cias;
     { ctx with
       core_ctx = { ctx.core_ctx with
                    core_instances = ctx.core_ctx.core_instances
                                     @ [cmt.cmt_instance]}}
  | I.CoreInstanceDef { it = I.Core_instantiate_inline es ; _ } ->
     check_uniqueness "Duplicate core export name "
       (fun x -> x.I.c_e_name.it) es;
     let i = infer_core_instance ctx es in
     { ctx with
       core_ctx = { ctx.core_ctx with
                    core_instances = ctx.core_ctx.core_instances @ [i] } }
  | I.CoreTypeDef cdt ->
     let t = elab_core_deftype_ ctx cdt in
     { ctx with
       core_ctx = { ctx.core_ctx with
                    core_types = ctx.core_ctx.core_types @ [t] } }

let rec mark_dead_sort_idxs (ctx : ctx) (sis : I.sort_idx list) : ctx
  = match sis with
  | [] -> ctx
  | si::sis' ->
     let ii = Int32.to_int si.it.I.s_idx in
     let ctx' = match si.it.I.s_sort.it with
       | Value ->
          { ctx with
            values =
              List.mapi (fun i vad ->
                  if i == ii
                  then (if not vad.ad_live
                        then raise (Invalid (si.at, "Cannot reuse dead value"))
                        else { vad with ad_live = false })
                  else vad) ctx.values }
       | Instance ->
          { ctx with
            instances =
              List.mapi (fun i iad ->
                  if i == ii
                  then
                    { itad_exports =
                        List.map (mark_dead_ed si.at) iad.itad_exports }
                  else iad) ctx.instances }
       | _ -> ctx
     in mark_dead_sort_idxs ctx' sis'
let mark_dead_ias (ctx : ctx) (ias : I.instantiate_arg list) : ctx
  = mark_dead_sort_idxs ctx (List.map (fun ia -> ia.it.I.ia_value) ias)
let mark_dead_ies (ctx : ctx) (ies : I.inline_export list) : ctx
  = mark_dead_sort_idxs ctx (List.map (fun ie -> ie.it.I.ie_value) ies)

let find_instantiate_arg_named (n : name) (ias : I.instantiate_arg list)
    : I.instantiate_arg
  = try List.find (fun ia -> ia.it.I.ia_name.it == n.it) ias
    with Not_found ->
      let at = match ias with | [] -> n.at | ia::_ -> ia.at in
      raise (Invalid (at, "Must provide import" ^ n.it))

let rec iibb_search_inst
      (ctx : ctx) (exps : extern_decl list) (i : int) (ed : extern_decl)
  =
  let find_ed' () =
    List.find (fun x -> x.ed_name.it.en_name.it == ed.ed_name.it.en_name.it)
      exps in
  match ed.ed_desc with
  | ED_type (DT_var (TV_bound i)) -> (* jackpot! *)
     let ed' = find_ed' () in
     (match ed'.ed_desc with
      | ED_type dt -> Some dt
      | _ -> raise (Invalid (ed'.ed_name.at,
                             "Cannot instantiate type import "
                             ^ ed.ed_name.it.en_name.it ^ "with non-type")))
  | ED_instance it ->
     let ed' = find_ed' () in
     (match ed'.ed_desc with
      | ED_instance it' ->
         List.find_map (iibb_search_inst ctx it'.it_exports (i + List.length it.it_evars))
           it.it_exports
      | _ -> raise (Invalid (ed'.ed_name.at,
                             "Cannot instantiate instance import "
                             ^ ed.ed_name.it.en_name.it ^ "with non-instance")))
  | _ -> None
let iibb_search_ed
      (ctx : ctx) (ias : I.instantiate_arg list) (i : int) (ed : extern_decl)
    : def_type option
  =
  let find_ia () = find_instantiate_arg_named ed.ed_name.it.en_name ias in
  match ed.ed_desc with
  | ED_type (DT_var (TV_bound i)) -> (* jackpot! *)
     (match (find_ia ()).it.I.ia_value.it with
      | { I.s_sort = { it = Type ; _ } ; I.s_idx = ti } ->
         Some (List.nth ctx.types (Int32.to_int ti))
      | _ -> raise (Invalid ((find_ia ()).at,
                             "Cannot instantiate type import "
                             ^ ed.ed_name.it.en_name.it ^ "with non-type")))
  | ED_instance it ->
     (match (find_ia ()).it.I.ia_value.it with
      | { I.s_sort = { it = Instance ; _ } ; I.s_idx = ii } ->
         let inst = (List.nth ctx.instances (Int32.to_int ii)) in
         let exps = List.map (fun x -> x.ad_contents) inst.itad_exports in
         List.find_map (iibb_search_inst ctx exps (i + List.length it.it_evars))
           it.it_exports
      | _ -> raise (Invalid ((find_ia ()).at,
                             "Cannot instantiate instance import "
                             ^ ed.ed_name.it.en_name.it ^ "with non-instance")))
  | _ -> None
let infer_instantiate_bvar_binding
      (ctx : ctx) (is : extern_decl list) (ias : I.instantiate_arg list) (i : int) (v : boundedtyvar)
    : def_type
  = match v with
  | Tbound_eq dt -> dt
  | Tbound_subr ->
     match List.find_map (iibb_search_ed ctx ias i) is with
     | None -> raise (Invalid (no_region, "!! Impossible: un-imported uvar"))
     | Some dt -> dt
let infer_instantiate_bvar_bindings
      (ctx : ctx) (ct : component_type) (ias : I.instantiate_arg list) : bsubst
  = List.mapi (fun i v -> Some (infer_instantiate_bvar_binding ctx ct.ct_imports ias i v))
      (List.rev ct.ct_uvars)

let infer_sort_idx_ed (ctx : ctx) (si : I.sort_idx) : extern_desc
  =
  let i = Int32.to_int si.it.I.s_idx in
  match si.it.I.s_sort.it with
  | CoreSort { it = Core_module ; _ } ->
     ED_core_module (List.nth ctx.core_ctx.core_modules i)
  | Func -> ED_func (List.nth ctx.funcs i)
  | Value -> ED_value (List.nth ctx.values i).ad_contents
  | Type -> ED_type (List.nth ctx.types i)
  | Instance ->
     ED_instance
       { it_evars = []; it_exports = List.map (fun x -> x.ad_contents)
                                       (List.nth ctx.instances i).itad_exports }
  | Component -> ED_component (List.nth ctx.components i)
  | _ -> raise (Invalid (si.at, "Cannot instantiate an import with sort "
                                ^ show_sort' si.it.I.s_sort.it))

let check_instantiate_import (ctx : ctx) (ias : I.instantiate_arg list) (im : extern_decl) : unit
  = let ia = find_instantiate_arg_named im.ed_name.it.en_name ias in
    let ed = infer_sort_idx_ed ctx ia.it.I.ia_value in
    subtype_extern_desc ctx ed im.ed_desc

let rec infer_component_defn (ctx : ctx) (d : I.definition)
    : ctx * extern_decl option * extern_decl option
  = match d.it with
  | I.CoreDef cd -> (infer_core_defn ctx cd, None, None)
  | I.ComponentDef c ->
     let ct = infer_component ctx c in
     ({ ctx with components = ctx.components @ [ct] }, None, None)
  | I.InstanceDef ({ it = I.Instantiate_component (cid, ias) ; _ }) ->
     let ct = List.nth ctx.components (Int32.to_int cid) in
     check_uniqueness "Duplicate instantiate arg name "
       (fun x -> x.I.ia_name.it) ias;
     let uvar_insts = infer_instantiate_bvar_bindings ctx ct ias in
     let ct_imports = List.map (subst_extern_decl (bsubst_subst uvar_insts))
                        ct.ct_imports in
     let ct_instance = subst_instance_type (bsubst_subst uvar_insts)
                         ct.ct_instance in
     List.iter (check_instantiate_import ctx ias) ct_imports;
     let ctx', bsubst = bound_to_uvars ctx ct_instance.it_evars in
     let ct_exports =
       List.map (fun x -> { ad_contents = subst_extern_decl
                                            (bsubst_subst bsubst) x
                          ; ad_live = true })
         ct_instance.it_exports in
     let ctx'' = mark_dead_ias ctx' ias in
     ({ ctx'' with
        instances = ctx''.instances @ [ { itad_exports = ct_exports } ] },
      None, None)
  | I.InstanceDef ({ it = I.Instantiate_inline ies; _ }) ->
     check_uniqueness "Duplicate inline export name "
       (fun x -> x.I.ie_name.it.en_name.it) ies;
     let ctx' = mark_dead_ies ctx ies in
     ({ ctx' with
        instances =
          ctx'.instances @
            [ { itad_exports =
                  List.map (fun ie ->
                      { ad_contents = { ed_name = ie.it.I.ie_name
                                      ; ed_desc = infer_sort_idx_ed ctx
                                                    ie.it.I.ie_value
                                      }
                      ; ad_live = true }) ies } ] }, None, None)
  | I.AliasDef a ->
     let ctx', at = resolve_alias ctx a in
     (match a.it.I.a_sort.it, at with
      | CoreSort { it = Core_module; _ }, Either.Left (CT_module cmt) ->
         ({ ctx' with
            core_ctx = { ctx'.core_ctx with
                         core_modules = ctx'.core_ctx.core_modules
                                        @ [ cmt ] } }, None, None)
      | CoreSort { it = Core_type; _ }, Either.Left ct ->
         ({ ctx' with
            core_ctx = { ctx'.core_ctx with
                         core_types = ctx'.core_ctx.core_types
                                      @ [ ct ] } }, None, None)
      | Func, Either.Right (DT_func_type ft) ->
         ({ ctx' with funcs = ctx'.funcs @ [ ft ] }, None, None)
      | Value, Either.Right (DT_val_type vt) ->
         ({ ctx' with values = ctx'.values @ [ { ad_contents = vt
                                               ; ad_live = true } ]
          }, None, None)
      | Type, Either.Right dt -> ({ ctx' with types = ctx'.types @ [ dt ] }
                                 ,None, None)
      | Instance, Either.Right (DT_instance_type it) ->
         let ctx'', bsubst = bound_to_uvars ctx' it.it_evars in
         let it_exports =
           List.map (fun x -> { ad_contents = subst_extern_decl
                                                (bsubst_subst bsubst) x
                              ; ad_live = true })
             it.it_exports in
         ({ ctx'' with
            instances = ctx''.instances
                        @ [ { itad_exports = it_exports } ]
          }, None, None)
      | Component, Either.Right (DT_component_type ct) ->
         ({ ctx' with components = ctx'.components @ [ ct ] }, None, None)
      | _, _ -> raise (Invalid (a.at, "!! Impossible: resolve_alias bad sort")))
  | I.TypeDef { it = I.Deftype_rsrc dtor; _ } ->
  (* This is the only place that resource types are valid,
     and they are generative here *)
     let i = Int32.of_int (List.length ctx.rtypes) in
     ({ ctx with
        rtypes = ctx.rtypes @ [ { rt_dtor = dtor } ];
        types = ctx.types @ [ DT_resource_type i ] }
     ,None, None)
  | I.TypeDef dt ->
     let dt' = elab_def_type ctx dt in
     ({ ctx with types = ctx.types @ [ dt' ] }, None, None)
  | _ -> xyz "icd"

and ctx_no_live_vals (ctx : ctx) : unit
  =
  let check_this : 'a. ('a alive_dead) -> unit
    = fun ad ->
    if ad.ad_live
    then raise (Invalid (no_region,
                         "All values must be dead at end of component!"))
    else () in
  let check_export_decl (ed : extern_decl_ad) : unit
    = match ed.ad_contents.ed_desc with
    | ED_value _ -> check_this ed
    | ED_instance _ -> check_this ed
    | _ -> () in
  let check_itad (itad : instance_type_ad) : unit
    = let _ = List.map check_export_decl itad.itad_exports in () in
  let _ = List.map check_this ctx.values in
  let _ = List.map check_itad ctx.instances in
  ()

and infer_component (ctx : ctx) (c : I.component) : component_type
  = build_component_type infer_component_defn ctx_no_live_vals ctx c.it.I.defns

(* good but unused
let atmap'
      (f : 'a -> Source.region -> 'b)
      (x : 'a Source.phrase)
    : 'b Source.phrase
  = { Source.it = f x.Source.it x.Source.at; Source.at = x.Source.at; }
let atmap (f : 'a -> 'b) : 'a Source.phrase -> 'b Source.phrase
  = atmap' (fun x r -> f x)
let atmap_c f ctx = atmap (f ctx)
let atmap_cc'
      (f : 'c -> 'a -> Source.region -> 'c * 'b)
      (ctx : 'c) (x : 'a Source.phrase)
    : 'c * 'b Source.phrase
  = let ctx', b = f ctx x.it x.at in
    ctx, { it = b; at = x.at }
let atmap_cc f = atmap_cc' (fun c x r -> f c x)*)

(*let atmap_ct f ctx c t = atmap (fun c' -> f ctx c' t) c*)

(*
(*let _check_component' ctx c t =
  unimplemented "check_component"
let _check_component
    : ctx -> I.component -> component_type option -> I.component_type =
    atmap_ct _check_component'*)
type cur_component_type =
  int (* de bruijn level into ctx.tyvars *) _component_type

let it_add (it1 : ('a, 'b) _instance_type) (it2 : ('a, 'b) _instance_type)
    : ('a, 'b) _instance_type
  = { i_exists = it1.it.i_exists @ it2.it.i_exists
    ; i_exports = it1.it.i_exports @ it2.it.i_exports
    } @@ span_regions it1.at it2.at

let ct_add : cur_component_type -> cur_component_type -> cur_component_type
  = fun ct1 ct2 ->
  { c_forall = ct1.it.c_forall @ ct2.it.c_forall
  ; c_imports = ct1.it.c_imports @ ct2.it.c_imports
  ; c_instance = it_add ct1.it.c_instance ct2.it.c_instance
  } @@ span_regions ct1.at ct2.at

let ct_finish : ctx -> cur_component_type -> component_type
  = fun ctx ct ->
  let resolve_binder (b : int) : type_bound
    = snd (List.nth ctx.tyvars b) in
  let tyvar_subst
    = fun tv ->
    (*let find_idx l =
      List.find_opt (fun (idx, el) -> el = tv)
        List.mapi (fun idx el -> (idx, el)) l
    match find_idx ct.it.c_forall with
    | Some idx -> Substr_nvar idx
    | None -> match find_idx ct.it.c_exists with
              | Some idx' -> Substr_nvar (List.len ct.it.c_forall + idx')
              | None -> *) unimplemented "tyvar_subst"
  in
  let fixup_tyvars
    = subst_extern_decl tyvar_subst in
  { c_forall = List.map resolve_binder ct.it.c_forall
  ; c_imports = List.map fixup_tyvars ct.it.c_imports
  ; c_instance = { i_exists = List.map resolve_binder
                                ct.it.c_instance.it.i_exists
                 ; i_exports = List.map fixup_tyvars
                                 ct.it.c_instance.it.i_exports
                 } @@ ct.it.c_instance.at
  } @@ ct.at

let ct_empty () : cur_component_type
  = { c_forall = []
    ; c_imports = []
    ; c_instance = { i_exists = []; i_exports = [] } @@ no_region }
    @@ no_region

let assert_no_values ctx =
  (* TODO *)
  ()

module CA = Wasm.Ast

let infer_core_import (ctx : ctx) (cmd : CA.module_) (i : CA.import)
    : core_import_decl
  = { ci_mod = Wasm.Utf8.encode i.it.CA.module_name @@ i.at
    ; ci_item = Wasm.Utf8.encode i.it.CA.item_name @@ i.at
    ; ci_desc = (*let open Wasm.ParseUtil in
                let pctx = empty_context () in
                pctx.types.list <- cmd.it.CA.types;
                pctx, i.it.CA.idesc*)
        Wasm.Ast.import_type cmd i
    } @@ i.at
let infer_core_export (ctx : ctx) (cmd : CA.module_) (e : CA.export)
    : core_export_decl
  = { ce_name = Wasm.Utf8.encode e.it.CA.name @@ e.at
    ; ce_desc = (*let open Wasm.ParseUtil in
                let open CA in
                let open Wasm.I32 in
                let pctx = empty_context () in
                pctx.types.list <- cmd.it.types;
                let at = e.it.edesc.at in
                pctx, match e.it.edesc.it with
                      | FuncExport v -> FuncImport v @@ at
                      | TableExport v ->
                         TableImport (List.nth cmd.it.tables
                                        (to_int_u v.it)).it.ttype @@ at
                      | MemoryExport v ->
                         MemoryImport (List.nth cmd.it.memories
                                        (to_int_u v.it)).it.mtype @@ at
                      | GlobalExport v ->
                         GlobalImport (List.nth cmd.it.globals
                                        (to_int_u v.it)).it.gtype @@ at*)
        Wasm.Ast.export_type cmd e
    } @@ e.at

let infer_core_module ctx cmd
  =
  { cm_imports = List.map (infer_core_import ctx cmd) cmd.it.CA.imports
  ; cm_instance = {
      ci_exports = List.map (infer_core_export ctx cmd) cmd.it.CA.exports
    } @@ cmd.at
  } @@ cmd.at

let unify_core_extern_desc ctx at ed1 ed2 =
  if Wasm.Types.match_extern_type ed1 ed2
  then ()
  else raise (Invalid (at, "Did not match expected type"))

let find_core_instantiate_arg_named ctx cias name =
  try List.find (fun cia -> cia.it.I.c_ia_name.it = name.it) cias
  with Not_found ->
    raise (Invalid (name.at, "Expected to find instantiate arg " ^ name.it))
let find_core_export_named ctx cit name
  = try List.find (fun ced -> ced.it.ce_name.it = name.it) cit.it.ci_exports
    with Not_found ->
      raise (Invalid (name.at, "Expected to find export " ^ name.it))
let check_core_instantiate_import ctx cias cid
  = let cia = find_core_instantiate_arg_named ctx cias cid.it.ci_mod in
    if (cia.it.I.c_ia_value.it.I.c_s_sort.it <> Ast.Core_instance)
    then raise (Invalid (cia.at, "Only two-level imports are suported"))
    else ();
    let cit = List.nth ctx.core.core_instances
                (Int32.to_int cia.it.I.c_ia_value.it.I.c_s_idx) in
    let ced = find_core_export_named ctx cit cid.it.ci_item in
    unify_core_extern_desc ctx cia.at ced.it.ce_desc cid.it.ci_desc
let check_core_instantiate_uniquenesses cias cia
  = if (List.length
          (List.filter (fun cia' -> cia'.it.I.c_ia_name.it =
                                      cia.it.I.c_ia_name.it) cias)
        <> 1)
    then raise (Invalid (cia.at, "Duplicate instantiate arg name "
                                 ^ cia.it.I.c_ia_name.it))
    else ()
let infer_core_definition ctx coredef
  = match coredef with
  | I.CoreModuleDef cmd ->
     let cmt = infer_core_module ctx cmd in
     ({ctx with
        core = {ctx.core with
                 core_modules = ctx.core.core_modules @ [cmt]}}
     ,ct_empty ())
  | I.CoreInstanceDef { it = I.Core_instantiate_module (cmid, cias);
                        at = at } ->
     let cmt = List.nth ctx.core.core_modules (Int32.to_int cmid) in
     List.iter (check_core_instantiate_import ctx cias) cmt.it.cm_imports;
     List.iter (check_core_instantiate_uniquenesses cias) cias;
     ({ctx with
        core = {ctx.core with
                 core_instances = ctx.core.core_instances
                                  @ [cmt.it.cm_instance]}}
     ,ct_empty ())
  | _ -> unimplemented "infer_core_definition"

let rec infer_definition ctx def
  = match def.it with
  | I.CoreDef cd -> infer_core_definition ctx cd
  | I.ComponentDef cmp ->
     let ct = infer_component ctx cmp in
     ({ctx with components = ctx.components @ [ct]}, ct_empty ())
  | I.InstanceDef id ->
     unimplemented "infer_definition id"
  | I.AliasDef ad ->
     unimplemented "infer_definition ad"
  | _ -> unimplemented "infer_definition"

and infer_component ctx c
  = let ctx', component_type =
      List.fold_left
        (fun (ctx, ct) def ->
          let ctx', dt = infer_definition ctx def in
          (ctx', ct_add ct dt))
        (empty_ctx (Some ctx), ct_empty ())
        c.it.I.defns in
    assert_no_values ctx';
    ct_finish ctx' component_type
    *)

(*let check_component (c : I.component) (_ : I.component_type option)
    : Etypes.component_type =
    unimplemented "check_component"
 *)
(*  let ctx = empty_ctx None in
  infer_component ctx c*)
  (*_check_component ctx c (Option.map (elab_component_type ctx) t)*)
