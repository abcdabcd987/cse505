let (|>) x f = f x

let flip f a b = f b a

let mkstr = Printf.sprintf

let range n =
  let rec loop i acc =
    if i < 0 then
      acc
    else
      loop (i - 1) (i :: acc)
  in
    loop (n - 1) []

let explode s =
  let rec loop i acc =
    if i < 0 then
      acc
    else
      loop (i - 1) (String.get s i :: acc)
  in
  loop (String.length s - 1) []

let implode cs =
  let s = Bytes.create (List.length cs) in
  let rec loop i = function
    | [] -> s
    | c :: cs -> begin
        Bytes.set s i c;
        loop (i + 1) cs
      end
  in
  Bytes.to_string (loop 0 cs)

let readlines' ic =
  let rec loop ls =
    let next =
      try Some (input_line ic)
      with End_of_file -> None
    in
    match next with
    | None -> List.rev ls
    | Some l -> loop (l :: ls)
  in
  loop []

let readlines path =
  let f = open_in path in
  let ls = readlines' f in
  close_in f;
  ls

let ic_str ic =
  String.concat "\n" (readlines' ic)

let file_str path =
  String.concat "\n" (readlines path)

let str_file path s =
  let f = open_out path in
  output_string f s;
  close_out f

let big_len l =
  Big.of_int (List.length l)

let big_nth l i =
  List.nth l (Big.to_int i)

let big_range n =
  let rec loop i acc =
    if Big.lt i Big.zero then
      acc
    else
      loop (Big.sub i Big.one) (i :: acc)
  in
    loop (Big.sub n Big.one) []
