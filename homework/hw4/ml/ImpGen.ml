open ImpSyntax
open ImpCommon

let (|>) x f = f x

let rand_int () =
  (if Random.bool () then 1 else -1) * Random.int 100

let rand_elt l =
  List.nth l (Random.int (List.length l))

(* NOTE : typ only heuristic to help avoid generating bogus code *)

type typ =
  | Tint
  | Tbool
  | Taddr

let has_typ t v =
  match t, v with
  | Tint, Vint _ -> true
  | Tbool, Vbool _ -> true
  | Taddr, Vaddr _ -> true
  | _, _ -> false

let rand_typ () =
  match Random.int 3 with
  | 0 -> Tint
  | 1 -> Tbool
  | 2 -> Taddr
  | _ -> failwith "rand_typ"

let gen_op1 t1 t =
  match t1, t with
  | Tint, Tint -> Neg
  | Tbool, Tbool -> Not
  | _, _ -> failwith "gen_op1"

let gen_op2 t1 t2 t =
  match t1, t2, t with
  | Tint, Tint, Tint ->
      begin match Random.int 5 with
      | 0 -> Add
      | 1 -> Sub
      | 2 -> Mul
      | 3 -> Div
      | 4 -> Mod
      | _ -> failwith "gen_op2 i i i"
      end
  | Tint, Tint, Tbool ->
      begin match Random.int 3 with
      | 0 -> Eq
      | 1 -> Lt
      | 2 -> Le
      | _ -> failwith "gen_op2 i i b"
      end
  | Tbool, Tbool, Tbool ->
      begin match Random.int 3 with
      | 0 -> Eq
      | 1 -> Conj
      | 2 -> Disj
      | _ -> failwith "gen_op2 b b b"
      end
   | _, _, Tbool ->
       Eq
   | _, _, _ -> failwith "gen_op2"

let rand_var t store =
  store |> List.filter (function (x, v) -> has_typ t v)
        |> rand_elt
        |> fst

let rec gen_expr (t : typ) (s : store) (h : heap) (n : int) =
  match t with
  | Tint ->
      if n <= 1 then
        begin match Random.int 2 with
        | 0 -> Eval (Vint (rand_int ()))
        | 1 -> Evar (rand_var Tint s)
        | _ -> failwith "gen_expr i 1"
        end
      else
        begin match Random.int 6 with
        | 0 -> Eval (Vint (rand_int ()))
        | 1 -> Evar (rand_var Tint s)
        | 2 -> Eop1 ( gen_op1 Tint Tint
                    , gen_expr Tint s h (n - 1)
                    )
        | 3 -> Eop2 ( gen_op2 Tint Tint Tint
                    , gen_expr Tint s h (n / 2)
                    , gen_expr Tint s h (n / 2)
                    )
        | 4 -> Elen (gen_expr Taddr s h (n - 1))
        | 5 -> (* unsound *)
               Eidx ( gen_expr Taddr s h (n / 2)
                    , gen_expr Tint s h (n / 2)
                    )
        | _ -> failwith "gen_expr i n"
        end
  | Tbool ->
      if n <= 1 then
        begin match Random.int 2 with
        | 0 -> Eval (Vbool (Random.bool ()))
        | 1 -> Evar (rand_var Tbool s)
        | _ -> failwith "gen_expr b 1"
        end
    else
        begin match Random.int 5 with
        | 0 -> Eval (Vbool (Random.bool ()))
        | 1 -> Evar (rand_var Tbool s)
        | 2 -> Eop1 ( gen_op1 Tbool Tbool
                    , gen_expr Tbool s h (n - 1)
                    )
        | 3 ->
            begin match Random.int 3 with
            | 0 -> Eop2 ( gen_op2 Tint Tint Tbool
                        , gen_expr Tint s h (n / 2)
                        , gen_expr Tint s h (n / 2)
                        )
            | 1 -> Eop2 ( gen_op2 Tbool Tbool Tbool
                        , gen_expr Tint s h (n / 2)
                        , gen_expr Tint s h (n / 2)
                        )
            | 2 -> Eop2 ( Eq
                        , gen_expr (rand_typ ()) s h (n / 2)
                        , gen_expr (rand_typ ()) s h (n / 2)
                        )
            | _ -> failwith "gen_expr b n 3"
            end
        | 4 -> (* unsound *)
               Eidx ( gen_expr Taddr s h (n / 2)
                    , gen_expr Tint s h (n / 2)
                    )
        | _ -> failwith "gen_expr b n"
        end
| Taddr ->
      if n <= 1 then
        Evar (rand_var Taddr s)
      else
        begin match Random.int 2 with
        | 0 -> Evar (rand_var Taddr s)
        | 1 -> (* unsound *)
               Eidx ( gen_expr Taddr s h (n / 2)
                    , gen_expr Tint s h (n / 2)
                    )
        | _ -> failwith "gen_expr a n"
        end

let char_of_digit d =
  Char.chr (Char.code '0' + d)

let rand_var () =
  [ 'x'
  ; char_of_digit (Random.int 10)
  ]

let rec gen_stmt (s : store) (h : heap) (n : int) =
  if n <= 1 then
    match Random.int 3 with
    | 0 -> Sset ( rand_var ()
                , gen_expr (rand_typ ()) s h 7
                )
    | 1 -> Salloc ( rand_var ()
                  , gen_expr Tint s h 5
                  , gen_expr (rand_typ ()) s h 5
                  )
    | 2 -> Sassign ( gen_expr Taddr s h 5
                   , gen_expr Tint s h 5
                   , gen_expr (rand_typ ()) s h 5
                   )
    | _ -> failwith "gen_stmt 1"
  else
    match Random.int 6 with
    | 0 -> Sset ( rand_var ()
                , gen_expr (rand_typ ()) s h 7
                )
    | 1 -> Salloc ( rand_var ()
                  , gen_expr Tint s h 5
                  , gen_expr (rand_typ ()) s h 5
                  )
    | 2 -> Sassign ( gen_expr Taddr s h 5
                   , gen_expr Tint s h 5
                   , gen_expr (rand_typ ()) s h 5
                   )
    | 3 -> Sseq ( gen_stmt s h (n / 2)
                , gen_stmt s h (n / 2)
                )
    | 4 -> Sifelse ( gen_expr Tbool s h 5
                   , gen_stmt s h (n / 2)
                   , gen_stmt s h (n / 2)
                   )
    | 5 -> Swhile ( gen_expr Tbool s h 5
                  , gen_stmt s h (n - 1)
                  )
    | _ -> failwith "gen_stmt 1"

let gen n =
  Sseq ( Sset (['x'; '0'], Eval (Vint 0)),
  Sseq ( Sset (['x'; '1'], Eval (Vbool false)),
  Sseq ( Salloc (['x'; '2'], Eval (Vint 3), Eval (Vint 0)),
  (gen_stmt [ (['x'; '0'], Vint 0)
            ; (['x'; '1'], Vbool false)
            ; (['x'; '2'], Vaddr 0)
            ]
            [Vint 3; Vint 0; Vint 0; Vint 0]
            n))))
