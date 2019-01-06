open ImpSyntax
open ZUtil

let val_coq = function
  | Vbool b -> mkstr "(Vbool %s)" (string_of_bool b)
  | Vint i  -> mkstr "(Vint %s)" (Big.to_string i)
  | Vstr s  -> mkstr "(Vstr \"%s\")" (implode s)
  | Vaddr a -> mkstr "(Vaddr %s)" (Big.to_string a)

let var_coq x =
  mkstr "\"%s\"" (implode x)

let op1_coq = function
  | Oneg -> "Oneg"
  | Onot -> "Onot"

let op2_coq = function
  | Oadd  -> "Oadd"
  | Osub  -> "Osub"
  | Omul  -> "Omul"
  | Odiv  -> "Odiv"
  | Omod  -> "Omod"
  | Oeq   -> "Oeq"
  | Olt   -> "Olt"
  | Ole   -> "Ole"
  | Oconj -> "Oconj"
  | Odisj -> "Odisj"

let rec expr_coq = function
  | Eval v ->
      mkstr "(Eval %s)"
        (val_coq v)
  | Evar x ->
      mkstr "(Evar %s)"
        (var_coq x)
  | Eop1 (op, e1) ->
      mkstr "(Eop1 %s %s)"
        (op1_coq op)
        (expr_coq e1)
  | Eop2 (op, e1, e2) ->
      mkstr "(Eop2 %s %s %s)"
        (op2_coq op)
        (expr_coq e1)
        (expr_coq e2)
  | Elen e1 ->
      mkstr "(Elen %s)" (expr_coq e1)
  | Eidx (e1, e2) ->
      mkstr "(Eidx %s %s)"
        (expr_coq e1)
        (expr_coq e2)

let indent ls =
  List.map (fun l -> "  " ^ l) ls

let rec add_to_last s = function
  | [] -> failwith "add_to_last: empty list!"
  | [x] -> [x ^ s]
  | x :: l -> x :: add_to_last s l

let list_coq ss =
  ss |> List.map (fun s -> s ^ " :: ")
     |> String.concat ""
     |> mkstr "(%snil)"

let exprs_coq es =
  list_coq (List.map expr_coq es)

let store_coq sr =
  let aux (x, v) =
    mkstr "(%s, %s)"
      (var_coq x)
      (val_coq v)
  in
  list_coq (List.map aux sr)

let rec stmt_coq' = function
  | Snop ->
      "Snop" :: []
  | Sset (x, e) ->
      mkstr "(Sset %s %s)"
        (var_coq x)
        (expr_coq e)
      :: []
  | Salloc (x, e1, e2) ->
      mkstr "(Salloc %s %s %s)"
        (var_coq x)
        (expr_coq e1)
        (expr_coq e2)
      :: []
  | Swrite (x, e1, e2) ->
      mkstr "(Swrite %s %s %s)"
        (var_coq x)
        (expr_coq e1)
        (expr_coq e2)
      :: []
  | Scall (x, f, es) ->
      mkstr "(Scall %s %s %s)"
        (var_coq x)
        (var_coq f)
        (exprs_coq es)
      :: []
  | Sifelse (e, p1, p2) ->
      mkstr "(Sifelse %s " (expr_coq e)
        :: indent (stmt_coq' p1)
        @ add_to_last ")" (indent (stmt_coq' p2))
  | Swhile (e, p1) ->
      mkstr "(Swhile %s " (expr_coq e)
        :: add_to_last ")" (indent (stmt_coq' p1))
  | Sseq (p1, p2) ->
      "(Sseq " :: stmt_coq' p1
      @ add_to_last ")" (stmt_coq' p2)

let stmt_coq s =
  String.concat "\n" (stmt_coq' s)

let func_coq' = function
  | Func (name, params, body, ret) ->
      mkstr "(Func %s %s"
        (var_coq name)
        (list_coq (List.map var_coq params))
      :: indent (stmt_coq' body)
      @  add_to_last ")" (indent (expr_coq ret :: []))

let func_coq f =
  String.concat "\n" (func_coq' f)

let prog_coq' = function
  | Prog (funcs, body, ret) ->
      mkstr "(Prog ["
      :: String.concat ";\n" (add_to_last "]" (List.map func_coq funcs))
      :: stmt_coq' body
      @ (expr_coq ret ^ ")") :: []

let prog_coq p =
  String.concat "\n" (prog_coq' p)
