open Wasm_components
open Wasm_components.Script
open Wasm.Source


(* Errors & Tracing *)

module Script = Wasm.Error.Make ()
module Abort = Wasm.Error.Make ()
module Assert = Wasm.Error.Make ()
module IO = Wasm.Error.Make ()

exception Abort = Abort.Error
exception Assert = Assert.Error
exception IO = IO.Error

let trace name = if !Flags.trace then print_endline ("-- " ^ name)


(* File types *)

let binary_ext = "wasm"
let sexpr_ext = "wat"
let script_binary_ext = "bin.wast"
let script_ext = "wast"
let js_ext = "js"

let dispatch_file_ext on_binary on_sexpr on_script_binary on_script on_js file =
  if Filename.check_suffix file binary_ext then
    on_binary file
  else if Filename.check_suffix file sexpr_ext then
    on_sexpr file
  else if Filename.check_suffix file script_binary_ext then
    on_script_binary file
  else if Filename.check_suffix file script_ext then
    on_script file
  else if Filename.check_suffix file js_ext then
    on_js file
  else
    raise (Sys_error (file ^ ": unrecognized file type"))


(* Output *)
(*
let create_binary_file file _ get_module =
  trace ("Encoding (" ^ file ^ ")...");
  let s = Wasm.Encode.encode (get_module ()) in
  let oc = open_out_bin file in
  try
    trace "Writing...";
    output_string oc s;
    close_out oc
  with exn -> close_out oc; raise exn

let create_sexpr_file file _ get_module =
  trace ("Writing (" ^ file ^ ")...");
  let oc = open_out file in
  try
    Wasm.Print.module_ oc !Flags.width (get_module ());
    close_out oc
  with exn -> close_out oc; raise exn

let create_script_file mode file get_script _ =
  trace ("Writing (" ^ file ^ ")...");
  let oc = open_out file in
  try
    Wasm.Print.script oc !Flags.width mode (get_script ());
    close_out oc
  with exn -> close_out oc; raise exn

let create_js_file file get_script _ =
  trace ("Converting (" ^ file ^ ")...");
  let js = Wasm.Js.of_script (get_script ()) in
  let oc = open_out file in
  try
    trace "Writing...";
    output_string oc js;
    close_out oc
  with exn -> close_out oc; raise exn

let output_file =
  dispatch_file_ext
    create_binary_file
    create_sexpr_file
    (create_script_file `Binary)
    (create_script_file `Textual)
    create_js_file

let output_stdout get_module =
  trace "Printing...";
  Wasm.
  Print.module_ stdout !Wasm_components.Flags.width (get_module ())

 *)
(* Input *)

let error at category msg =
  trace ("Error: ");
  prerr_endline (Wasm.Source.string_of_region at ^ ": " ^ category ^ ": " ^ msg);
  false

let input_from get_script run =
  try
    let script = get_script () in
    trace "Running...";
    run script;
    true
  with
  | Wasm.Decode.Code (at, msg) -> error at "decoding error" msg
  | Wasm.Parse.Syntax (at, msg) -> error at "syntax error" msg
  | Syntax (at, msg) -> error at "syntax error" msg
  | Valid.Invalid (at, msg) -> error at "invalid module" msg
  | Wasm.Import.Unknown (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Link (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Trap (at, msg) -> error at "runtime trap" msg
  | Wasm.Eval.Exhaustion (at, msg) -> error at "resource exhaustion" msg
  | Wasm.Eval.Crash (at, msg) -> error at "runtime crash" msg
  | Wasm.Encode.Code (at, msg) -> error at "encoding error" msg
  | Script.Error (at, msg) -> error at "script error" msg
  | IO (at, msg) -> error at "i/o error" msg
  | Assert (at, msg) -> error at "assertion failure" msg
  | Abort _ -> false

let input_script start name lexbuf run =
  input_from (fun _ -> Wasm_components.Parse.parse name lexbuf start) run

let input_sexpr name lexbuf run =
  input_from (fun _ ->
      let x, c = Wasm_components.Parse.parse name lexbuf
                   Wasm_components.Parse.Component in
      [Component (x, Textual c @@ no_region) @@ no_region]) run
    (*let var_opt, def = Wasm_components.Parse.parse name lexbuf Wasm_components.Parse.Component in
    let def' = Wasm_components.Desugar.desugar_component (Wasm_components.Desugar.SC (Wasm_components.Desugar.empty_ctx () None)) def in
    [Component (var_opt, def') @@ no_region]) run*)

let input_binary name buf run =
  input_from (fun _ ->
    raise (Sys_error "i don't do this yet (2)")
    (*[Module (None, Encoded (name, buf) @@ no_region) @@ no_region]*)) run

let input_sexpr_file input file run =
  trace ("Loading (" ^ file ^ ")...");
  let ic = open_in file in
  try
    let lexbuf = Lexing.from_channel ic in
    trace "Parsing...";
    let success = input file lexbuf run in
    close_in ic;
    success
  with exn -> close_in ic; raise exn

let input_binary_file file run =
  trace ("Loading (" ^ file ^ ")...");
  let ic = open_in_bin file in
  try
    let len = in_channel_length ic in
    let buf = Bytes.make len '\x00' in
    really_input ic buf 0 len;
    trace "Decoding...";
    let success = input_binary file (Bytes.to_string buf) run in
    close_in ic;
    success
  with exn -> close_in ic; raise exn

let input_js_file file run =
  raise (Sys_error (file ^ ": unrecognized input file type"))

let input_file file run =
  trace ("Input file (\"" ^ String.escaped file ^ "\")...");
  dispatch_file_ext
    input_binary_file
    (input_sexpr_file input_sexpr)
    (input_sexpr_file (input_script Wasm_components.Parse.Script))
    (input_sexpr_file (input_script Wasm_components.Parse.Script))
    input_js_file
    file run

let input_string string run =
  trace ("Running (\"" ^ String.escaped string ^ "\")...");
  let lexbuf = Lexing.from_string string in
  trace "Parsing...";
  input_script Wasm_components.Parse.Script "string" lexbuf run


(* Interactive *)

let continuing = ref false

let lexbuf_stdin buf len =
  let prompt = if !continuing then "  " else "> " in
  print_string prompt; flush_all ();
  continuing := true;
  let rec loop i =
    if i = len then i else
    let ch = input_char stdin in
    Bytes.set buf i ch;
    if ch = '\n' then i + 1 else loop (i + 1)
  in
  let n = loop 0 in
  if n = 1 then continuing := false else trace "Parsing...";
  n

let input_stdin run =
  let lexbuf = Lexing.from_function lexbuf_stdin in
  let rec loop () =
    let success = input_script Wasm_components.Parse.Script "stdin" lexbuf run in
    if not success then Lexing.flush_input lexbuf;
    if Lexing.(lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len - 1) then
      continuing := false;
    loop ()
  in
  try loop () with End_of_file ->
    print_endline "";
    trace "Bye."

let print_component_type x t =
  ()
(* Printing *)
(*
let print_import m im =
  let open Wasm.Types in
  let category, annotation =
    match Wasm.Ast.import_type m im with
    | ExternFuncType t -> "func", string_of_func_type t
    | ExternTableType t -> "table", string_of_table_type t
    | ExternMemoryType t -> "memory", string_of_memory_type t
    | ExternGlobalType t -> "global", string_of_global_type t
  in
  Printf.printf "  import %s \"%s\" \"%s\" : %s\n"
    category (Wasm.Ast.string_of_name im.it.Wasm.Ast.module_name)
      (Wasm.Ast.string_of_name im.it.Wasm.Ast.item_name) annotation

let print_export m ex =
  let open Wasm.Types in
  let category, annotation =
    match Wasm.Ast.export_type m ex with
    | ExternFuncType t -> "func", string_of_func_type t
    | ExternTableType t -> "table", string_of_table_type t
    | ExternMemoryType t -> "memory", string_of_memory_type t
    | ExternGlobalType t -> "global", string_of_global_type t
  in
  Printf.printf "  export %s \"%s\" : %s\n"
    category (Wasm.Ast.string_of_name ex.it.Wasm.Ast.name) annotation

let print_module x_opt m =
  Printf.printf "module%s :\n"
    (match x_opt with None -> "" | Some x -> " " ^ x.it);
  List.iter (print_import m) m.it.Wasm.Ast.imports;
  List.iter (print_export m) m.it.Wasm.Ast.exports;
  flush_all ()

let print_values vs =
  let ts = List.map Wasm.Values.type_of_value vs in
  Printf.printf "%s : %s\n"
    (Wasm.Values.string_of_values vs) (Types.string_of_value_types ts);
  flush_all ()

let string_of_nan = function
  | Wasm.Script.CanonicalNan -> "nan:canonical"
  | Wasm.Script.ArithmeticNan -> "nan:arithmetic"

let type_of_result r =
  match r with
  | Wasm.Script.LitResult v -> Wasm.Values.type_of_value v.it
  | Wasm.Script.NanResult n -> Types.NumType (Wasm.Values.type_of_num n.it)
  | Wasm.Script.RefResult t -> Types.RefType t

let string_of_result r =
  match r with
  | Wasm.Script.LitResult v -> Wasm.Values.string_of_value v.it
  | Wasm.Script.NanResult nanop ->
    (match nanop.it with
    | Wasm.Values.I32 _ | Wasm.Values.I64 _ -> assert false
    | Wasm.Values.F32 n | Wasm.Values.F64 n -> string_of_nan n
    )
  | RefResult t -> Types.string_of_refed_type t

let string_of_results = function
  | [r] -> string_of_result r
  | rs -> "[" ^ String.concat " " (List.map string_of_result rs) ^ "]"

let print_results rs =
  let ts = List.map type_of_result rs in
  Printf.printf "%s : %s\n"
    (string_of_results rs) (Types.string_of_value_types ts);
  flush_all ()
 *)

(* Configuration *)

module Map = Map.Make(String)

let quote : script ref = ref []
let scripts : script Map.t ref = ref Map.empty
let modules : Wasm.Ast.module_ Map.t ref = ref Map.empty
let instances : Wasm.Instance.module_inst Map.t ref = ref Map.empty
(*let registry : Wasm.Instance.module_inst Map.t ref = ref Map.empty*)

let bind map x_opt y =
  let map' =
    match x_opt with
    | None -> !map
    | Some x -> Map.add x.it y !map
  in map := Map.add "" y map'

let lookup category map x_opt at =
  let key = match x_opt with None -> "" | Some x -> x.it in
  try Map.find key !map with Not_found ->
    IO.error at
      (if key = "" then "no " ^ category ^ " defined"
       else "unknown " ^ category ^ " " ^ key)

let lookup_script = lookup "script" scripts
let lookup_module = lookup "module" modules
let lookup_instance = lookup "module" instances

(*
let lookup_registry module_name item_name _t =
  match Wasm.Instance.export (Map.find module_name !registry) item_name with
  | Some ext -> ext
  | None -> raise Not_found
            *)

(* Running *)

let rec run_definition def : Wasm_components.Ast.IntAst.component
  = match def.it with
  | Textual c ->
     Wasm_components.Desugar.desugar_component c
  | Encoded (name, bs) ->
     raise (Sys_error "Binary modules not yet supported")
  | Quoted (name, s) ->
     trace "Parsing quote...";
     let x, c =
       Wasm_components.Parse.parse name (Lexing.from_string s)
         Wasm_components.Parse.Component in
     run_definition (Textual c @@ no_region)

(*
let run_action act : Wasm.Values.value list =
  match act.it with
  | Wasm.Script.Invoke (x_opt, name, vs) ->
    trace ("Invoking function \"" ^ Wasm.Ast.string_of_name name ^ "\"...");
    let inst = lookup_instance x_opt act.at in
    (match Wasm.Instance.export inst name with
    | Some (Wasm.Instance.ExternFunc f) ->
      let Wasm.Types.FuncType (ins, out) = Func.type_of f in
      if List.length vs <> List.length ins then
        Script.error act.at "wrong number of arguments";
      List.iter2 (fun v t ->
        if Wasm.Values.type_of_value v.it <> t then
          Script.error v.at "wrong type of argument"
      ) vs ins;
      Wasm.Eval.invoke f (List.map (fun v -> v.it) vs)
    | Some _ -> Assert.error act.at "export is not a function"
    | None -> Assert.error act.at "undefined export"
    )

 | Get (x_opt, name) ->
    trace ("Getting global \"" ^ Wasm.Ast.string_of_name name ^ "\"...");
    let inst = lookup_instance x_opt act.at in
    (match Wasm.Instance.export inst name with
    | Some (Wasm.Instance.ExternGlobal gl) -> [Global.load gl]
    | Some _ -> Assert.error act.at "export is not a global"
    | None -> Assert.error act.at "undefined export"
    )

let assert_result at got expect =
  let open Wasm.Values in
  if
    List.length got <> List.length expect ||
    List.exists2 (fun v r ->
      match r with
      | Wasm.Script.LitResult v' -> v <> v'.it
      | Wasm.Script.NanResult nanop ->
        (match nanop.it, v with
        | F32 CanonicalNan, Num (F32 z) ->
          z <> F32.pos_nan && z <> F32.neg_nan
        | F64 CanonicalNan, Num (F64 z) ->
          z <> F64.pos_nan && z <> F64.neg_nan
        | F32 ArithmeticNan, Num (F32 z) ->
          let pos_nan = F32.to_bits F32.pos_nan in
          Int32.logand (F32.to_bits z) pos_nan <> pos_nan
        | F64 ArithmeticNan, Num (F64 z) ->
          let pos_nan = F64.to_bits F64.pos_nan in
          Int64.logand (F64.to_bits z) pos_nan <> pos_nan
        | _, _ -> false
        )
      | Wasm.Script.RefResult t ->
        (match t, v with
        | Types.FuncRefType, Ref (Instance.FuncRef _)
        | Types.ExternRefType, Ref (Wasm.Script.ExternRef _) -> false
        | _ -> true
        )
    ) got expect
  then begin
    print_string "Result: "; print_values got;
    print_string "Expect: "; print_results expect;
    Assert.error at "wrong return values"
  end
 *)
let assert_message at name msg re =
  if
    String.length msg < String.length re ||
    String.sub msg 0 (String.length re) <> re
  then begin
    print_endline ("Result: \"" ^ msg ^ "\"");
    print_endline ("Expect: \"" ^ re ^ "\"");
    Assert.error at ("wrong " ^ name ^ " error")
  end

let run_assertion ass =
  match ass.it with
  | AssertMalformed (def, re) ->
    trace "Asserting malformed...";
    (match ignore (run_definition def) with
     (*    | exception Decode.Code (_, msg) -> assert_message ass.at "decoding" msg re*)
    | exception Parse.Syntax (_, msg) -> assert_message ass.at "parsing" msg re
    | _ -> Assert.error ass.at "expected decoding/parsing error"
    )

  | AssertInvalid (def, re) ->
    trace "Asserting invalid...";
    (match
      let m = run_definition def in
      Valid.infer_component (Etypes.empty_ctx None) m
    with
    | exception Wasm_components.Valid.Invalid (_, msg) ->
      assert_message ass.at "validation" msg re
    | _ -> Assert.error ass.at "expected validation error"
    )
(*
  | Wasm.Script.AssertUnlinkable (def, re) ->
    trace "Asserting unlinkable...";
    let m = run_definition def in
    if not !Flags.unchecked then Wasm.Valid.check_module m;
    (match
      let imports = Import.link m in
      ignore (Wasm.Eval.init m imports)
    with
    | exception (Import.Unknown (_, msg) | Wasm.Eval.Link (_, msg)) ->
      assert_message ass.at "linking" msg re
    | _ -> Assert.error ass.at "expected linking error"
    )

  | Wasm.Script.AssertUninstantiable (def, re) ->
    trace "Asserting trap...";
    let m = run_definition def in
    if not !Flags.unchecked then Wasm.Valid.check_module m;
    (match
      let imports = Import.link m in
      ignore (Wasm.Eval.init m imports)
    with
    | exception Wasm.Eval.Trap (_, msg) ->
      assert_message ass.at "instantiation" msg re
    | _ -> Assert.error ass.at "expected instantiation error"
    )

  | Wasm.Script.AssertReturn (act, rs) ->
    trace ("Asserting return...");
    let got_vs = run_action act in
    let expect_rs = List.map (fun r -> r.it) rs in
    assert_result ass.at got_vs expect_rs

  | Wasm.Script.AssertTrap (act, re) ->
    trace ("Asserting trap...");
    (match run_action act with
    | exception Wasm.Eval.Trap (_, msg) -> assert_message ass.at "runtime" msg re
    | _ -> Assert.error ass.at "expected runtime error"
    )

  | Wasm.Script.AssertExhaustion (act, re) ->
    trace ("Asserting exhaustion...");
    (match run_action act with
    | exception Wasm.Eval.Exhaustion (_, msg) ->
      assert_message ass.at "exhaustion" msg re
    | _ -> Assert.error ass.at "expected exhaustion error"
    )
 *)
let rec run_command (cmd : Wasm_components.Script.command) : unit =
  match cmd.it with
  | Component (x_opt, def) ->
     let c = run_definition def in
     if not !Flags.unchecked then begin
         trace "Checking...";
         let t = Valid.infer_component (Etypes.empty_ctx None) c in
         if !Flags.print_sig then begin
             trace "Signature:";
             print_component_type x_opt t
           end
       end;
     (*bind scripts x_opt [cmd];
     bind components x_opt m;*)
     () (* TODO: actually run it *)
  | Assertion ass ->
    quote := cmd :: !quote;
    if not !Flags.dry then begin
      run_assertion ass
    end
  | Meta cmd ->
     run_meta cmd
and run_meta cmd =
  match cmd.it with
  | Script (x_opt, script) ->
    run_quote_script script;
    bind scripts x_opt (lookup_script None cmd.at)

  | Input (x_opt, file) ->
    (try if not (input_file file run_quote_script) then
      Abort.error cmd.at "aborting"
    with Sys_error msg -> IO.error cmd.at msg);
    bind scripts x_opt (lookup_script None cmd.at);
    if x_opt <> None then begin
      bind modules x_opt (lookup_module None cmd.at);
      if not !Flags.dry then begin
        bind instances x_opt (lookup_instance None cmd.at)
      end
    end

(*  | Output (x_opt, Some file) ->
    (try
      output_file file
        (fun () -> lookup_script x_opt cmd.at)
        (fun () -> lookup_module x_opt cmd.at)
    with Sys_error msg -> IO.error cmd.at msg)

  | Output (x_opt, None) ->
    (try output_stdout (fun () -> lookup_module x_opt cmd.at)
    with Sys_error msg -> IO.error cmd.at msg)*)
(*  match cmd.it with
  | Module (x_opt, def) ->
    quote := cmd :: !quote;
    let m = run_definition def in
    if not !Flags.unchecked then begin
      trace "Checking...";
      Wasm.Valid.check_module m;
      if !Flags.print_sig then begin
        trace "Signature:";
        print_module x_opt m
      end
    end;
    bind scripts x_opt [cmd];
    bind modules x_opt m;
    if not !Flags.dry then begin
      trace "Initializing...";
      let imports = Import.link m in
      let inst = Wasm.Eval.init m imports in
      bind instances x_opt inst
    end

  | Register (name, x_opt) ->
    quote := cmd :: !quote;
    if not !Flags.dry then begin
      trace ("Registering module \"" ^ Wasm.Ast.string_of_name name ^ "\"...");
      let inst = lookup_instance x_opt cmd.at in
      registry := Map.add (Utf8.encode name) inst !registry;
      Import.register name (lookup_registry (Utf8.encode name))
    end

  | Action act ->
    quote := cmd :: !quote;
    if not !Flags.dry then begin
      let vs = run_action act in
      if vs <> [] then print_values vs
    end

  | Meta cmd ->
    run_meta cmd

and run_meta cmd =
  match cmd.it with
  | Script (x_opt, script) ->
    run_quote_script script;
    bind scripts x_opt (lookup_script None cmd.at)

  | Input (x_opt, file) ->
    (try if not (input_file file run_quote_script) then
      Abort.error cmd.at "aborting"
    with Sys_error msg -> IO.error cmd.at msg);
    bind scripts x_opt (lookup_script None cmd.at);
    if x_opt <> None then begin
      bind modules x_opt (lookup_module None cmd.at);
      if not !Flags.dry then begin
        bind instances x_opt (lookup_instance None cmd.at)
      end
    end

  | Output (x_opt, Some file) ->
    (try
      output_file file
        (fun () -> lookup_script x_opt cmd.at)
        (fun () -> lookup_module x_opt cmd.at)
    with Sys_error msg -> IO.error cmd.at msg)

  | Output (x_opt, None) ->
    (try output_stdout (fun () -> lookup_module x_opt cmd.at)
    with Sys_error msg -> IO.error cmd.at msg)*)

and run_script script =
  List.iter run_command script

and run_quote_script (script : Wasm_components.Script.script) =
  let save_quote = !quote in
  quote := [];
  (try run_script script with exn -> quote := save_quote; raise exn);
  bind scripts None (List.rev !quote);
  quote := !quote @ save_quote

let run_file file = input_file file run_script
let run_string string = input_string string run_script
let run_stdin () = input_stdin run_script
