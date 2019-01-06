open ImpSyntax
open ZUtil

(* hack to avoid circular build *)
let pretty : (heap -> coq_val -> string) ref =
  ref (fun _ _ -> "")

(* log all I/O for testing vs. python *)
let inputs : (string list) ref =
  ref []

let input () =
  let s = read_line () in
  inputs := s :: !inputs; s

let outputs : (string list) ref =
  ref []

let output h v =
  let s = !pretty h v in
  outputs := s :: !outputs;
  print_endline s

let extcall name args h =
  match implode name, args with
  | "print_val", [v] ->
      output h v;
      (Vint Big.zero, h)
  | "flush", [] ->
      flush stdout;
      (Vint Big.zero, h)
  | "sleep", [Vint i] ->
      let ms = (Big_int.float_of_big_int i) /. 1000.0 in
      ignore (Unix.select [] [] [] ms);
      (Vint Big.zero, h)
  | "read_bool", [] ->
      begin match input () with
      | "True"  -> (Vbool true, h)
      | "False" -> (Vbool false, h)
      | s -> begin
          prerr_endline ("extcall: read_bool could not parse " ^ s);
          (Vbool false, h)
        end
      end
  | "read_int", [] -> begin
      let s = input () in
      try (Vint (Big.of_string s), h)
      with _ ->
        prerr_endline ("extcall: read_int could not parse " ^ s);
        (Vint Big.zero, h)
    end
  | "read_str", [] ->
      (Vstr (explode (input ())), h)
  | f, _ -> begin
      prerr_endline ("extcall: bogus call to " ^ f);
      (Vint Big.zero, h)
    end
