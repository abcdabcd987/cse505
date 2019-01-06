open ZUtil
open ImpSyntax

let char_of_digit d =
  Char.chr (Char.code '0' + d)

let rand_big n =
  let s =
    n |> Random.int
      |> (+) 1
      |> range
      |> List.map (fun _ -> Random.int 10)
      |> List.map char_of_digit
      |> implode
  in
  if Random.bool () then
    Big.of_string s
  else
    Big.opp (Big.of_string s)

let rand_char () =
  Char.chr (32 + Random.int (127 - 32))

let rand_list gen arg n =
  n |> Random.int
    |> range
    |> List.map (fun _ -> gen arg)

let rand_var () =
  [ 'x'
  ; char_of_digit (Random.int 10)
  ]

let rand_val () =
  match Random.int 3 with
  | 0 -> Vint (rand_big 20)
  | 1 -> Vbool (Random.bool ())
  | 2 -> Vstr (rand_list rand_char () 50)
  | _ -> failwith "rand_val"

let rand_op1 () =
  match Random.int 2 with
  | 0 -> Oneg
  | 1 -> Onot
  | _ -> failwith "rand_op1"

let rand_op2 () =
  match Random.int 10 with
  | 0 -> Oadd
  | 1 -> Osub
  | 2 -> Omul
  | 3 -> Odiv
  | 4 -> Omod
  | 5 -> Oeq
  | 6 -> Olt
  | 7 -> Ole
  | 8 -> Oconj
  | 9 -> Odisj
  | _ -> failwith "rand_op2"

let rec rand_expr size =
  if size <= 1 then
    match Random.int 2 with
    | 0 -> Eval (rand_val ())
    | 1 -> Evar (rand_var ())
    | _ -> failwith "rand_expr in size <= 1"
  else
    match Random.int 6 with
    | 0 -> Eval (rand_val ())
    | 1 -> Evar (rand_var ())
    | 2 -> Eop1 (rand_op1 (), rand_expr (size - 1))
    | 3 -> Eop2 (rand_op2 (), rand_expr (size / 2), rand_expr (size / 2))
    | 4 -> Elen (rand_expr (size - 1))
    | 5 -> Eidx (rand_expr (size / 2), rand_expr (size / 2))
    | _ -> failwith "rand_expr"

let rec rand_stmt size =
  if size <= 1 then
    match Random.int 4 with
    | 0 -> Snop
    | 1 -> Sset (rand_var (), rand_expr 7)
    | 2 -> Salloc (rand_var (), rand_expr 5, rand_expr 5)
    | 3 -> Swrite (rand_var (),  rand_expr 5, rand_expr 5)
    | _ -> failwith "rand_stmt in size <= 1"
  else
    match Random.int 7 with
    | 0 -> Snop
    | 1 -> Sset (rand_var (), rand_expr 7)
    | 2 -> Salloc (rand_var (), rand_expr 5, rand_expr 5)
    | 3 -> Swrite (rand_var (), rand_expr 5, rand_expr 5)
    | 4 -> Sseq (rand_stmt (size / 2), rand_stmt (size / 2))
    | 5 -> Sifelse (rand_expr 5, rand_stmt (size / 2), rand_stmt (size /2))
    | 6 -> Swhile (rand_expr 5, rand_stmt (size - 1))
    | _ -> failwith "rand_stmt"

let rand_func size =
  Func ( rand_var ()
       , rand_list rand_var () size
       , rand_stmt size
       , rand_expr size
       )

let rand_prog size =
  Prog ( rand_list rand_func size size
       , rand_stmt size
       , rand_expr size
       )
