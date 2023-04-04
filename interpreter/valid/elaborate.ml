open Ast
module I = IntAst
open Wasm.Source
open Subtype
open Etypes
open Substitute

type vc_ctx = { vc_ctx_ctx : ctx; vc_ctx_cases : variant_case list }

let resolve_type_use (ctx : ctx) (t : int32) : def_type
  = let ti = Int32.to_int t in
    try List.nth ctx.types ti
    with Not_found ->  raise (Invalid (no_region, "No such type to use: " ^                                                    string_of_int ti))

let resolve_val_type_use (ctx : ctx) at (t : int32) : val_type
  = match resolve_type_use ctx t with
  | DT_val_type vt -> vt
  | _ -> raise (Invalid (at, "type use is not a value type"))

(* why don't we have the I.prim_val_type vs I.def_val_type split again? *)
let rec elab_def_val_type (ctx : ctx) (t : I.def_val_type) : val_type
  = match t.it with
  | I.Bool -> Bool
  | I.Signed s -> Signed s
  | I.Unsigned s -> Unsigned s
  | I.Float s -> Float s
  | I.Char -> Char
  | I.String -> List Char
  | I.List t' -> List (resolve_val_type_use ctx t.at t')
  | I.Record rfs -> Record (List.map (elab_record_field ctx) rfs)
  | I.Variant vcs -> elab_variant_cases ctx vcs
  | I.Tuple vts -> Record (List.mapi (elab_tuple_field ctx t.at) vts)
  | I.Flags ns -> Record (List.map (elab_flags_case ctx) ns)
  | I.Enum ns -> Variant (List.map (elab_enum_case ctx) ns)
  | I.Option t' -> Variant
                     [ { vc_name = "none" @@ t.at
                       ; vc_type = None
                       ; vc_default = None }
                     ; { vc_name = "some" @@ t.at
                       ; vc_type = Some (resolve_val_type_use ctx t.at t')
                       ; vc_default = None }
                     ]
  | I.Expected (t1, t2) ->
     Variant
       [ { vc_name = "ok" @@ t.at
         ; vc_type = Option.map (resolve_val_type_use ctx t.at) t1
         ; vc_default = None
         }
       ; { vc_name = "error" @@ t.at
         ; vc_type = Option.map (resolve_val_type_use ctx t.at) t2
         ; vc_default = None
         }
       ]
  | I.Union ts -> Variant (List.mapi (elab_union_case ctx t.at) ts)
  | I.Own t' ->
     let et' = resolve_type_use ctx t' in
     def_type_is_resource ctx et';
     Own et'
  | I.Borrow t' ->
     let et' = resolve_type_use ctx t' in
     def_type_is_resource ctx et';
     Borrow et'
and elab_record_field (ctx : ctx) (f : I.record_field) : record_field
  = { rf_name = f.it.I.rf_name
    ; rf_type = resolve_val_type_use ctx f.at f.it.I.rf_type }
and elab_variant_cases ctx (vcs : I.variant_case list)
  = let go cs c =
      let vc_ctx = { vc_ctx_ctx = ctx; vc_ctx_cases = cs } in
      let c' = elab_variant_case vc_ctx c in
      List.append cs [c']
    in
    Variant (List.fold_left go [] vcs)
and elab_variant_case (vc_ctx : vc_ctx) (c : I.variant_case) : variant_case
  = let t' = Option.map (resolve_val_type_use vc_ctx.vc_ctx_ctx c.at)
               c.it.I.vc_type in
    { vc_name = c.it.I.vc_name;
      vc_type = t';
      vc_default = Option.map (elab_variant_default vc_ctx t' c.at)
                     c.it.I.vc_default
    }
and elab_variant_default (vc_ctx : vc_ctx) (t' : val_type option) at (def : int32)
    : int32
  = match List.nth vc_ctx.vc_ctx_cases (Int32.to_int def) with
  | exception Failure _ ->
     raise (Invalid (at, "default case does not exist"))
  | vc' -> subtype_val_type_option vc_ctx.vc_ctx_ctx t' vc'.vc_type;
           def
and elab_tuple_field (ctx : ctx) at (i : int) (f : I.val_type) : record_field
  = { rf_name = string_of_int i @@ at; rf_type = resolve_val_type_use ctx at f }
and elab_flags_case (ctx : ctx) (n : name) : record_field
  = { rf_name = n; rf_type = Bool }
and elab_enum_case (ctx : ctx) (n : name) : variant_case
  = { vc_name = n; vc_type = None; vc_default = None }
and elab_union_case (ctx : ctx) at (i : int) (f : I.val_type) : variant_case
  = { vc_name = string_of_int i @@ at
    ; vc_type = Some (resolve_val_type_use ctx at f)
    ; vc_default = None
    }

type position =
  | Pos_none
  | Pos_param

let rec wf_val_type (ctx : ctx) (p : position) (t : val_type) : unit
  = match t with
  | Bool -> ()
  | Signed _ -> ()
  | Unsigned _ -> ()
  | Float _ -> ()
  | Char -> ()
  | List t -> wf_val_type ctx p t
  | Record rfs -> List.iter (wf_record_field ctx p rfs) rfs
  | Variant vcs -> List.iter (wf_variant_case ctx p vcs) vcs
  | Own (DT_resource_type rtidx) ->
     if Int32.to_int rtidx >= List.length (ctx.rtypes)
     then raise (Invalid (no_region, "resource type index does not exist"))
     else ()
  | Own (DT_var a) ->
     def_type_is_resource ctx (DT_var a)
  | Own _ -> raise (Invalid (no_region, "non-resource type in own/borrow"))
  | Borrow dt ->
     if p <> Pos_param
     then raise (Invalid (no_region, "borrow in non-parameter position"))
     else wf_val_type ctx p (Own dt)
and wf_record_field (ctx : ctx) (p : position) (rfs : record_field list) (rf : record_field) : unit
  = let rfs' = List.filter (fun rf' -> rf'.rf_name.it == rf.rf_name.it) rfs in
    if List.length rfs' <> 1
    then raise (Invalid (rf.rf_name.at, "duplicate record field name"))
    else wf_val_type ctx p rf.rf_type
and wf_variant_case (ctx : ctx) (p : position) (vcs : variant_case list) (vc : variant_case) : unit
  = let vcs' = List.filter (fun vc' -> vc'.vc_name.it == vc.vc_name.it) vcs in
    if List.length vcs' <> 1
    then raise (Invalid (vc.vc_name.at, "duplicate variant case name"))
    else ();
    (match vc.vc_default with
     | None -> ()
     | Some i ->
        match List.nth vcs (Int32.to_int i) with
        | exception Failure _ ->
           raise (Invalid (vc.vc_name.at, "default case does not exist"))
        | vc' -> subtype_val_type_option ctx vc.vc_type vc'.vc_type);
    (match vc.vc_type with
     | None -> ()
     | Some t -> wf_val_type ctx p t)

let elab_func_io (ctx : ctx) (p : position) (io : I.func_ios) : func_ios
  =
  let go t = let t' = resolve_val_type_use ctx no_region t in
             wf_val_type ctx p t'; t' in
  match io.it with
  | I.Fio_one t -> Fio_one (go t)
  | I.Fio_many ts -> Fio_many (List.map (fun (n, t) -> (n, go t)) ts)

let elab_func_type (ctx : ctx) (ft : I.func_type) : func_type
  = { ft_params = elab_func_io ctx Pos_param ft.it.I.ft_params
    ; ft_result = elab_func_io ctx Pos_none  ft.it.I.ft_result
    }

(*let elab_type_bound (ctx : ctx) (tb : I.type_bound) : type_bound
  = match tb.it with
  | I.Tbound_eq t -> Tbound_eq (resolve_type_use ctx t)
  | I.Tbound_subr -> Tbound_subr*)

let core_type_of_core_externdesc (ed : core_extern_desc) : core_type
  = let open Wasm.Types in
    match ed with
    | ExternFuncType ft -> CT_func ft
    | ExternTableType t -> CT_table t
    | ExternMemoryType t -> CT_memory t
    | ExternGlobalType t -> CT_global t

let resolve_core_alias_export
      (ctx : ctx) (i : core_instance_type) at (s : core_sort') (n : name)
    : core_type
  = let ed =
      try List.find (fun x -> x.ced_name.it == n.it) i.cit_exports
      with Not_found ->
        raise (Invalid (at, "No such export: " ^ n.it))
    in
    let open Wasm.Types in
    match s, ed.ced_desc with
    | Core_func, ExternFuncType _
      | Core_table, ExternTableType _
      | Core_memory, ExternMemoryType _
      | Core_global, ExternGlobalType _ ->
       core_type_of_core_externdesc ed.ced_desc
    | _, _ -> raise (Invalid (at, "Export of wrong sort: " ^ n.it))

let rec resolve_core_alias_outer
      (ctx : ctx) at (o : int) (i : int) (s : core_sort') : core_type
  = match o with
  | 0 ->
     (try
        match s with
        (*| Core_func -> CT_func (List.nth ctx.core_ctx.core_funcs i)*)
        (*| Core_table -> CT_table (List.nth ctx.core_ctx.core_tables i)*)
        (*| Core_memory -> CT_table (List.nth ctx.core_ctx.core_mems i)*)
        (*| Core_global -> CT_global (List.nth ctx.core_ctx.core_globals i)*)
        | Core_type -> List.nth ctx.core_ctx.core_types i
        | _ -> raise (Invalid (at, "Stateful outer aliases not allowed"))
      with | Not_found ->
              raise (Invalid (at, "No such index " ^ string_of_int i
                                  ^ " for sort " ^ show_core_sort' s)))
  | _ -> match ctx.parent_ctx with
         | Some ctx' ->
            resolve_core_alias_outer ctx' at (o - 1) i s
         | None ->
            raise (Invalid (at, "No such enclosing component"))

let resolve_core_alias (ctx : ctx) (a : I.core_alias) : core_type
  = match a.it.I.c_a_target.it with
  | I.Core_alias_export (i, n) ->
     resolve_core_alias_export
       ctx (List.nth ctx.core_ctx.core_instances (Int32.to_int i))
       a.it.I.c_a_target.at a.it.I.c_a_sort.it n
  | I.Core_alias_outer (o, i) ->
     resolve_core_alias_outer
       ctx a.it.I.c_a_target.at
       (Int32.to_int o) (Int32.to_int i)
       a.it.I.c_a_sort.it

let mark_dead_ed at ed =
  match ed.ad_contents.ed_desc with
  | ED_instance _ | ED_value _ ->
     if not ed.ad_live
     then raise (Invalid (at, "Cannot reuse dead value/instance"))
     else { ed with ad_live = false }
  | _ -> ed

let resolve_alias_export
      (ctx : ctx) (i : int32) at (s : sort') (n : name)
    : ctx * (core_type, def_type) Either.t
  = let i = Int32.to_int i in
    let ii = (List.nth ctx.instances i).itad_exports in
    let ed =
      try List.find (fun x -> x.ad_contents.ed_name.it.en_name.it == n.it) ii
      with | Not_found ->
              raise (Invalid (at, "No such export: " ^ n.it))
    in
    let ed' = mark_dead_ed at ed in
    let eds' = List.map (fun x -> if x.ad_contents.ed_name.it.en_name.it == n.it
                                  then ed' else x) ii in
    let ii' = { itad_exports = eds' } in
    let is' = List.mapi (fun i' x -> if i' == i then ii' else x)
                ctx.instances in
    let ctx' = { ctx with instances = is' } in
    (ctx', match s, ed.ad_contents.ed_desc with
           | CoreSort { it = Core_module; _ }, ED_core_module cmt ->
              Either.Left (CT_module cmt)
           | Func, ED_func ft -> Either.Right (DT_func_type ft)
           | Value, ED_value v -> Either.Right (DT_val_type v)
           | Type, ED_type t -> Either.Right t
           | Instance, ED_instance it -> Either.Right (DT_instance_type it)
           | Component, ED_component ct -> Either.Right (DT_component_type ct)
           | _ -> raise (Invalid (at, "Bad export alias")))

let rec resolve_alias_outer
      (ctx : ctx) at (o : int) (i : int)  (s : sort')
    : (core_type, def_type) Either.t
  = match o with
  | 0 ->
     (try
        match s with
        | CoreSort s' -> Either.Left (resolve_core_alias_outer ctx at 0 i s'.it)
        (* | Func -> Either.Right (DT_func_type (List.nth ctx.funcs i))*)
        (* | Value -> Either.Right (DT_val_type (List.nth ctx.values i))*)
        | Type -> Either.Right (List.nth ctx.types i)
        | Component ->
           Either.Right (DT_component_type (List.nth ctx.components i))
        (* | Instance ->
             Either.Right (DT_instance_type (List.nth ctx.instances i))*)
        | _ -> raise (Invalid (at, "Stateful outer aliases not allowed"))
      with | Not_found ->
              raise (Invalid (at, "No such index " ^ string_of_int i
                                  ^ " for sort " ^ show_sort' s)))
  | _ -> match ctx.parent_ctx with
         | Some ctx' ->
            resolve_alias_outer ctx' at (o - 1) i s
         | None ->
            raise (Invalid (at, "No such enclosing component"))

let resolve_alias (ctx : ctx) (a : I.alias) :
      ctx * (core_type, def_type) Either.t
  = match a.it.I.a_target.it with
  | I.Alias_export (i, n) ->
     resolve_alias_export
       ctx i a.at a.it.I.a_sort.it n
  | I.Alias_core_export (i, ns) ->
     (match a.it.I.a_sort.it with
      | CoreSort s' ->
         (ctx, Either.Left
                 (resolve_core_alias_export
                    ctx (List.nth ctx.core_ctx.core_instances (Int32.to_int i))
                    a.it.I.a_target.at
                    s'.it
                    ns))
      | _ ->
         raise (Invalid (a.at,
                         "Cannot look for non-core export of core instance")))
  | I.Alias_outer (o, i) ->
     (ctx, resolve_alias_outer
             ctx a.it.I.a_target.at
             (Int32.to_int o) (Int32.to_int i)
             a.it.I.a_sort.it)

let elab_core_deftype (ctx : ctx) (ct : I.core_deftype) : core_type
  = match ct.it with
  | I.Core_deftype_functype cft -> CT_func cft.it

let empty_core_module_type : core_module_type
  = { cmt_imports = [] ; cmt_instance = { cit_exports = [] } }

let elab_core_extern_desc (ced : I.core_externdesc)
  = let open Wasm.Types in
    let open Wasm.Ast in
    let open Wasm.ParseUtil in
    match (snd ced).it with
    | FuncImport i ->
       ExternFuncType (List.nth (fst ced).types.list (Int32.to_int i.it)).it
    | TableImport tt ->
       ExternTableType tt
    | MemoryImport mt ->
       ExternMemoryType mt
    | GlobalImport gt ->
       ExternGlobalType gt

let elab_core_moduledecl (ctx : ctx) (cmd : I.core_moduledecl)
    : ctx * core_module_type
  = match cmd.it with
  | I.Core_md_importdecl ci ->
     (ctx, { cmt_imports = [ { cid_name1 = ci.it.I.c_id_name1
                             ; cid_name2 = ci.it.I.c_id_name2
                             ; cid_desc = elab_core_extern_desc
                                            ci.it.I.c_id_ty } ]
           ; cmt_instance = { cit_exports = [] } })
  | I.Core_md_typedecl cdt ->
     let cdt' = elab_core_deftype ctx cdt in
     ({ ctx with core_ctx = { ctx.core_ctx with
                              core_types = ctx.core_ctx.core_types @ [cdt'] } },
      empty_core_module_type)
  | I.Core_md_aliasdecl ad ->
     (match ad.it.I.c_a_sort.it, ad.it.I.c_a_target.it with
      | Core_type, I.Core_alias_outer _ ->
         let ct = resolve_core_alias ctx ad in
         ({ ctx with
            core_ctx = { ctx.core_ctx with
                         core_types = ctx.core_ctx.core_types @ [ct] } },
          empty_core_module_type)
      | _, _ -> raise (Invalid (cmd.at, "Only outer type aliases allowed in core module types")))
  | I.Core_md_exportdecl ed ->
     (ctx, { cmt_imports = []
           ; cmt_instance = {
               cit_exports = [ { ced_name = ed.it.I.c_ed_name
                               ; ced_desc = elab_core_extern_desc
                                              ed.it.I.c_ed_ty } ] } })

let elab_core_moduletype (ctx : ctx) (cmt : I.core_moduletype)
    : core_module_type
  = let rec go ctx' cmt' decls =
      match decls with
      | [] -> cmt'
      | d::ds ->
         let ctx'', cmt'' = elab_core_moduledecl ctx' d in
         let cmt''' =
           { cmt_imports = cmt'.cmt_imports @ cmt''.cmt_imports
           ; cmt_instance =
               { cit_exports = cmt'.cmt_instance.cit_exports
                               @ cmt''.cmt_instance.cit_exports } } in
         go ctx'' cmt''' ds
    in go (empty_ctx (Some ctx)) empty_core_module_type (cmt.it.I.decls)

let elab_core_deftype_ (ctx : ctx) (cdt : I.core_deftype_)
    : core_type
  = match cdt.it with
  | I.Core_deftype__deftype cdt -> elab_core_deftype ctx cdt
  | I.Core_deftype__moduletype cmt -> CT_module (elab_core_moduletype ctx cmt)

let unvar_instance_type (it : instance_type)
    : boundedtyvar list * instance_type
  = (it.it_evars, { it_evars = [] ; it_exports = it.it_exports })

(*let instance_type_to_ad (it : instance_type)
    : boundedtyvar list * instance_type_ad
  = (it.it_evars,
     { itad_exports =
         List.map (fun ed -> { ad_contents = ed
                             ; ad_live = true })
           it.it_exports })*)

let rec elab_extern_desc (ctx : ctx) (ed : I.exportdesc)
    : boundedtyvar list * extern_desc
  =
  let go_it it = let v, it' = unvar_instance_type it in (v, ED_instance it') in
  match ed.it with
  | I.Export_sort_id (s, id) ->
     let dt = List.nth ctx.types (Int32.to_int id) in
     (match s.it, dt with
      | Func, DT_func_type ft -> ([], ED_func ft)
      | Component, DT_component_type ct -> ([], ED_component ct)
      | Instance, DT_instance_type it -> go_it it
      | Value, DT_val_type vt -> ([], ED_value vt)
      | Type, _ -> ([], ED_type dt)
      | _, _ -> raise (Invalid (ed.at, "Export type doesn't match sort")))
  | I.Export_core_mod cmt ->
    ([], ED_core_module (elab_core_moduletype ctx cmt))
  | I.Export_func ft ->
     ([], ED_func (elab_func_type ctx ft))
  | I.Export_comp ct ->
     ([], ED_component (elab_component_type ctx ct))
  | I.Export_inst it ->
     go_it (elab_instance_type ctx it)
  | I.Export_val vt ->
     ([], ED_value (resolve_val_type_use ctx ed.at vt))
  | I.Export_type { it = I.Tbound_eq dt ;  _ } ->
     ([], ED_type (resolve_type_use ctx dt))
  | I.Export_type { it = I.Tbound_subr ; _ } ->
     ([Tbound_subr], ED_type (DT_var (TV_bound 0)))

and elab_instance_decl (ctx : ctx) (id : I.instance_decl)
    : ctx * extern_decl option
  = match id.it with
  | I.Instance_type t ->
     let t' = elab_def_type ctx t in
     (match t' with
      | DT_resource_type _ -> raise (Invalid (id.at, "Resource type can not appear in instance declarator"))
      | _ ->
         let ctx' = { ctx with types = ctx.types @ [t'] } in
         (ctx', None))
  | I.Instance_alias a ->
     (match a.it.I.a_sort.it with
      | CoreSort { it = Core_type; _ } ->
         let ctx', t = resolve_alias ctx a in
         (match t with
          | Either.Left ct ->
            let ctx'' = { ctx' with
                         core_ctx = { ctx.core_ctx with
                                      core_types = ctx.core_ctx.core_types
                                                   @ [ct] } } in
            (ctx'', None)
          | _ -> raise (Invalid (no_region,
                                 "core type alias produced non-core-type")))
      | Type ->
         let ctx', t = resolve_alias ctx a in
         (match t with
          | Either.Right t ->
             let ctx'' = { ctx' with types = ctx.types @ [t] } in
             (ctx'', None)
          | _ -> raise (Invalid (no_region,
                                 "type alias produced non-type")))
      | _ ->
         raise
           (Invalid
              (no_region,
               "non-(core) type alias not allowed in instance type declarator"
     )))
  | I.Instance_export ed ->
     let v, ed' = elab_extern_desc ctx ed.it.I.ed_type in
     let ctx', bsub = bound_to_evars ctx v in
     let ed'' = subst_extern_desc (bsubst_subst bsub) ed' in
     (ctx', Some { ed_name = ed.it.I.ed_name ; ed_desc = ed'' })

(* todo: check for uniquneess of names *)
and finish_instance_type (ctx : ctx) (decls : extern_decl list) : instance_type
  = let esubst = List.init (List.length ctx.evars) (fun i -> Some (DT_var (TV_bound i))) in
    let subst = esubst_subst [esubst] in
    { it_evars = List.map (fun (t, _) -> t) (List.rev ctx.evars)
    ; it_exports = List.map (subst_extern_decl subst) decls
    }

and elab_instance_type (ctx : ctx) (it : I.instance_type) : instance_type
  = let rec go ctx ds = match ds with
      | [] -> (ctx, [])
      | d::ds ->
         let ctx', d' = elab_instance_decl ctx d in
         let ctx'', ds' = go ctx' ds in
         match d' with
         | None -> ctx'', ds'
         | Some d' -> ctx'', d'::ds' in
    let ctx', ds' = go (empty_ctx (Some ctx)) it.it in
    finish_instance_type ctx' ds'

and elab_component_decl (ctx : ctx) (cd : I.component_decl)
    : ctx * extern_decl option * extern_decl option
  = match cd.it with
  | I.Component_import id ->
     let v, ed' = elab_extern_desc ctx id.it.I.id_type in
     let ctx', bsub = bound_to_uvars ctx v in
     let ed'' = subst_extern_desc (bsubst_subst bsub) ed' in
     (ctx', Some { ed_name = id.it.I.id_name ; ed_desc = ed'' }, None)
  | I.Component_instance id ->
     let ctx', export = elab_instance_decl ctx id in
     (ctx, None, export)

and finish_component_type (ctx : ctx) (is : extern_decl list) (es : extern_decl list) : component_type
  = let it = finish_instance_type ctx es in
    let usubst = List.init (List.length ctx.uvars) (fun i -> Some (DT_var (TV_bound i))) in
    let subst = usubst_subst [usubst] in
    { ct_uvars = List.rev ctx.uvars
    ; ct_imports = List.map (subst_extern_decl subst) is
    ; ct_instance = subst_instance_type subst it
    }

and elab_def_type (ctx : ctx) (dt : I.def_type) : def_type
  = match dt.it with
  | I.Deftype_val dvt -> DT_val_type (elab_def_val_type ctx dvt)
  | I.Deftype_func ft -> DT_func_type (elab_func_type ctx ft)
  | I.Deftype_inst it -> DT_instance_type (elab_instance_type ctx it)
  | I.Deftype_comp ct -> DT_component_type (elab_component_type ctx ct)
  | I.Deftype_rsrc _ ->
     raise (Invalid (dt.at,
                     "Resource type declaration can't appear here"))

and build_component_type : 'a. (ctx -> 'a -> ctx * extern_decl option * extern_decl option) -> (ctx -> unit) -> ctx -> 'a list -> component_type
  = fun f ff ctx ds ->
  let rec go ctx ds = match ds with
    | [] -> (ctx, [], [])
    | d::ds ->
       let ctx', id, ed = f ctx d in
       let ctx'', is, es = go ctx' ds in
       let is' = match id with
         | None -> is
         | Some i -> i::is in
       let es' = match ed with
         | None -> es
         | Some e -> e::es in
       ctx'', is', es' in
  let ctx', is, es = go (empty_ctx (Some ctx)) ds in
  ff ctx';
  finish_component_type ctx' is es


and elab_component_type (ctx : ctx) (ct : I.component_type) : component_type
  = build_component_type elab_component_decl (fun _ -> ()) ctx ct.it

(*
type tyvar =
  (* (None, i) is a de bruijn index for a bound variable
     (Some ctxlevel, i) is a context index paired with a de bruijn level
     for free variables present in the context *)
  int option * int

type core_func_type = Wasm.Ast.type_

(*type core_extern_desc = Wasm.ParseUtil.context * Wasm.Ast.import_desc*)
type core_extern_desc = Wasm.Types.extern_type

type core_export_decl = core_export_decl' Source.phrase
and core_export_decl' =
  { ce_name : name
  ; ce_desc : core_extern_desc }
type core_import_decl = core_import_decl' Source.phrase
and core_import_decl' =
  { ci_mod  : name
  ; ci_item : name
  ; ci_desc : core_extern_desc }

type core_instance_type = core_instance_type' Source.phrase
and core_instance_type' =
  { ci_exports : core_export_decl list }
type core_module_type = core_module_type' Source.phrase
and core_module_type' =
  { cm_imports : core_import_decl list
  ; cm_instance : core_instance_type }

type core_def_type = core_def_type' Source.phrase
and core_def_type' =
  | CDeftype_func of core_func_type
  | CDeftype_module of core_module_type

type record_field = record_field' Source.phrase
and record_field' =
  {
    rf_name : name;
    rf_type : val_type;
  }
and variant_case = variant_case' Source.phrase
and variant_case' =
  {
    vc_name : name;
    vc_type : val_type option;
    vc_default : name option;
  }
and val_type =
  | Bool
  | Signed of val_int_size | Unsigned of val_int_size
  | Float of val_float_size
  | Char
  | List of val_type
  | Record of record_field list
  | Variant of variant_case list
  | Var of tyvar (* must point to a val_type if it appears here! *)

type result_type = result_type' Source.phrase
and result_type' =
  | Result_one of val_type
  | Result_many of (name * val_type) list
type func_type = func_type' Source.phrase
and func_type' =
  { ft_params : result_type
  ; ft_result : result_type }

type 'a not_marked = 'a
type 'a dead_marked = 'a * bool

type type_bound = type_bound' Source.phrase
and type_bound' = type_cstr list

and type_cstr = type_cstr' Source.phrase
and type_cstr' =
  | Cstr_sub of def_type
  | Cstr_sup of def_type
  | Cstr_sort of sort

and extern_desc = (def_type not_marked) _extern_desc
and 'a _extern_desc = 'a _extern_desc' Source.phrase
and 'a _extern_desc' =
  | E_core_mod of core_module_type
  | E_component_def of 'a
  | E_type of def_type
and extern_decl = (def_type not_marked) _extern_decl
and 'a _extern_decl = 'a _extern_decl' Source.phrase
and 'a _extern_decl' =
  { e_name : name; e_desc : 'a _extern_desc }

and instance_type = (def_type not_marked, type_bound) _instance_type
and ('a, 'b) _instance_type = ('a, 'b) _instance_type' Source.phrase
and ('a, 'b) _instance_type' =
  { i_exists : 'b list
  ; i_exports : 'a _extern_decl list }
and component_type = type_bound _component_type
and 'b _component_type = 'b _component_type' Source.phrase
and 'b _component_type' =
  { c_forall : 'b list
  ; c_imports : extern_decl list
  ; c_instance : (def_type not_marked, 'b) _instance_type }

and def_type = def_type' Source.phrase
and def_type' =
  | Deftype_var of tyvar
  | Deftype_val of val_type
  | Deftype_func of func_type
  | Deftype_inst of instance_type
  | Deftype_comp of component_type

type core_ctx =
  { core_types     : core_def_type          list
  ; core_funcs     : core_func_type         list
  ; core_modules   : core_module_type       list
  ; core_instances : core_instance_type     list
  ; core_tables    : Wasm.Types.table_type  list
  ; core_mems      : Wasm.Types.memory_type list
  ; core_globals   : Wasm.Types.global_type list
  }
and ctx =
  { parent : ctx option
  (* local type definition, if present; export view *)
  ; tyvars : (def_type option * type_bound) list
  ; core : core_ctx
  ; types : def_type list
  ; components : component_type list
  ; instances : (def_type dead_marked, type_bound) _instance_type list
  ; funcs : func_type list
  ; values : val_type dead_marked list
  }

let empty_core_ctx () =
  { core_types     = []
  ; core_funcs     = []
  ; core_modules   = []
  ; core_instances = []
  ; core_tables    = []
  ; core_mems      = []
  ; core_globals   = [] }
let empty_ctx parent =
  { parent     = parent
  ; tyvars     = []
  ; core       = empty_core_ctx ()
  ; types      = []
  ; components = []
  ; instances  = []
  ; funcs      = []
  ; values     = [] }

type subst_r =
  | Substr_none : subst_r
  | Substr_nvar : tyvar -> subst_r
  | Substr_deft : def_type -> subst_r
  | Substr_valt : val_type -> subst_r
type subst = tyvar -> subst_r

let subst_extern_desc (s : subst) (e : extern_desc) : extern_desc
  = unimplemented "sed"
let subst_extern_decl (s : subst) (e : extern_decl) : extern_decl
  = { e_name = e.it.e_name
    ; e_desc = subst_extern_desc s e.it.e_desc } @@ e.at

*)
