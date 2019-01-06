open ZUtil
open ImpSyntax
open ImpCommon

let indent ls =
  List.map (fun l -> "  " ^ l) ls

let rec stmt_py' = function
  | Snop ->
      []
  | Sset (x, e) ->
      mkstr "%s = %s"
        (implode x)
        (ImpPretty.expr_pretty e)
      :: []
  | Salloc (x, e1, e2) ->
      mkstr "%s = %s * [%s]"
        (implode x)
        (ImpPretty.expr_pretty e1)
        (ImpPretty.expr_pretty e2)
      :: []
  | Swrite (x, e1, e2) ->
      mkstr "%s[%s] = %s"
        (implode x)
        (ImpPretty.expr_pretty e1)
        (ImpPretty.expr_pretty e2)
      :: []
  | Scall (x, f, es) ->
      mkstr "%s = %s(%s)"
        (implode x)
        (implode f)
        (es |> List.map ImpPretty.expr_pretty
            |> String.concat ", ")
      :: []
  | Sseq (p1, p2) ->
      stmt_py' p1 @ stmt_py' p2
  | Sifelse (e, p1, Snop) ->
      mkstr "if %s:" (ImpPretty.expr_pretty e)
        :: indent (stmt_py' p1)
  | Sifelse (e, p1, p2) ->
      mkstr "if %s:" (ImpPretty.expr_pretty e)
        :: indent (stmt_py' p1)
      @ "else:"
        :: indent (stmt_py' p2)
  | Swhile (e, p1) ->
      mkstr "while %s:" (ImpPretty.expr_pretty e)
        :: indent (stmt_py' p1)

let stmt_py s =
  String.concat "\n" (stmt_py' s)

let func_py' = function
  | Func (name, params, body, ret) ->
      mkstr "def %s(%s):"
        (implode name)
        (params |> List.map implode
                |> String.concat ", ")
      :: indent (stmt_py' body)
      @  indent ((mkstr "return %s" (ImpPretty.expr_pretty ret)) :: [])

let func_py f =
  String.concat "\n" (func_py' f)

let prog_py' = function
  | Prog (funcs, body, ret) ->
      List.map func_py funcs
      @ stmt_py' body
      @ mkstr "print %s" (ImpPretty.expr_pretty ret)
      :: []

let implib_py = String.concat "\n"
  [ "import sys"
  ; "import time"
  ; ""
  ; "def print_val(v):"
  ; "  print(v)"
  ; "  return 0"
  ; ""
  ; "def flush():"
  ; "  sys.stdout.flush()"
  ; ""
  ; "def sleep(i):"
  ; "  time.sleep(i / 1000)"
  ; ""
  ; "def read_bool():"
  ; "  s = sys.stdin.readline().rstrip()"
  ; "  if s == \"True\":"
  ; "    return True"
  ; "  else:"
  ; "    return False"
  ; ""
  ; "def read_int():"
  ; "  s = sys.stdin.readline().rstrip()"
  ; "  try:"
  ; "    return int(s)"
  ; "  except:"
  ; "    return 0"
  ; ""
  ; "def read_str():"
  ; "  return sys.stdin.readline().rstrip()"
  ; ""
  ; ""
  ]

let prog_py p =
  p |> prog_py'
    |> String.concat "\n"
    |> (^) implib_py

let run_py p =
  (* prepare imp *)
  let (tmp, toc) = Filename.open_temp_file "IMPTEST" ".py" in
  output_string toc (prog_py p);
  close_out toc;
  (* run imp prog in python, get results *)
  let (ic, oc, ec) = Unix.open_process_full ("python " ^ tmp) [||] in
  !ImpLib.inputs
    |> List.rev
    |> String.concat "\n"
    |> output_string oc;
  close_out oc; (* flush is not sufficient *)
  let res = ic_str ic in
  let err = ic_str ec in
  let ret = Unix.close_process_full (ic, oc, ec) in
  (* clean up and return *)
  let _ = Unix.system ("rm " ^ tmp) in
  (res, err, ret)

let process_status_str = function
  | Unix.WEXITED i -> mkstr "WEXITED %d" i
  | Unix.WSIGNALED i -> mkstr "WSIGNALED %d" i
  | Unix.WSTOPPED i -> mkstr "WSTOPPED %d" i

let result_pretty (res, err, ret) =
  mkstr "stdout:\n%s\n\nstderr:\n%s\n\nstatus:\n%s\n"
    res err (process_status_str ret)

let results_match ir (res, err, ret) =
  match ret with
  | Unix.WEXITED 0 ->
      let ir_str =
        ir |> ImpPretty.result_pretty
           |> (fun x -> x :: !ImpLib.outputs)
           |> List.rev
           |> String.concat "\n"
      in
      ir_str = res
  | Unix.WEXITED 1 ->
      begin match ir with
      | None -> true
      | _ -> false
      end
  | _ -> false
