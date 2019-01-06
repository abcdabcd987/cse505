open ZUtil
open ImpSyntax
open ImpCommon

let _ = begin
  ImpLib.pretty := begin
    fun h v -> ImpPretty.result_pretty (Some (h, v))
  end;
  Random.self_init ()
end

let usage () =
  List.iter print_endline
    [ "Usage: Imp [options] program.imp                            "
    ; "                                                            "
    ; "Interpret, print, or test Imp programs.                     "
    ; "                                                            "
    ; "OPTIONS:                                                    "
    ; "  --interp    interpret Imp program                         "
    ; "  --fuel N    interpret up to N steps                       "
    ; "  --pretty    pretty print Imp program                      "
    ; "  --python    print translation to Python                   "
    ; "  --coq       print Coq AST                                 "
    ; "  --test      compare interp and Python output              "
    ; "  --rand N    print random Imp program (N controls size)    "
    ; "  --help      display this usage information                "
    ; "                                                            "
    ];
  exit 1

let flags =
  ref [ "mode" , "interp"
      ; "fuel" , "1000000"
      ; "src"  , ""
      ; "size" , ""
      ]

let setflag f v =
  flags := (f, v) :: !flags

let getflag f =
  List.assoc f !flags

let parse_args () =
  let rec loop = function
    | "-help" :: _
    | "--help" :: _ ->
        usage ()
    | "--interp" :: t ->
        setflag "mode" "interp";
        loop t
    | "--fuel" :: n :: t ->
        setflag "fuel" n;
        loop t
    | "--pretty" :: t ->
        setflag "mode" "pretty";
        loop t
    | "--python" :: t ->
        setflag "mode" "python";
        loop t
    | "--coq" :: t ->
        setflag "mode" "coq";
        loop t
    | "--test" :: t ->
        setflag "mode" "test";
        loop t
    | "--rand" :: n :: t ->
        setflag "mode" "rand";
        setflag "size" n;
        loop t
    | s :: t ->
        if String.get s 0 = '-' then begin
          print_endline ("ERROR: unknown flag " ^ s);
          usage ()
        end else begin
          setflag "src" s;
          loop t
        end
    | [] ->
        ()
  in begin
    Sys.argv
      |> Array.to_list
      |> List.tl
      |> loop
  end

let parse' lexbuf =
  try ImpParser.file ImpLexer.token lexbuf with
  | ImpLexer.SyntaxError msg ->
      Printf.fprintf stderr "%a: %s\n"
        ImpLexer.print_lexpos lexbuf msg;
      exit 1
  | ImpParser.Error ->
      Printf.fprintf stderr "%a: syntax error\n"
        ImpLexer.print_lexpos lexbuf;
      exit 1

let parse path =
  let ic = open_in path in
  let lexbuf = Lexing.from_channel ic in
  ImpLexer.set_fname lexbuf path;
  let p = parse' lexbuf in
  close_in ic;
  p

let interp p =
  let interp =
    ImpInterp.interp_p
  in
  let n =
    let s = getflag "fuel" in
    try Big.of_string s
    with _ -> failwith ("Could not parse fuel big int " ^ s)
  in
  interp n p

let _ =
  parse_args ();
  match getflag "mode" with
  | "interp" ->
      let p = parse (getflag "src") in
      print_endline (ImpPretty.result_pretty (interp p))
  | "pretty" ->
      let p = parse (getflag "src") in
      print_endline (ImpPretty.prog_pretty p)
  | "python" ->
      let p = parse (getflag "src") in
      print_endline (ImpPy.prog_py p)
  | "coq" ->
      let p = parse (getflag "src") in
      print_endline (ImpCoq.prog_coq p)
  | "test" ->
      let p = parse (getflag "src") in
      let iRes = interp p in
      let pRes = ImpPy.run_py p in
      print_endline
        (mkstr "# Imp:\n\n%s\n\n# Python:\n\n%s\n"
          (ImpPretty.result_pretty iRes)
          (ImpPy.result_pretty pRes));
      if ImpPy.results_match iRes pRes then
        print_endline "PASS"
      else begin
        print_endline "FAIL";
        exit 1
      end
  | "rand" ->
      "size"
        |> getflag
        |> int_of_string
        |> ImpRand.rand_prog
        |> ImpPretty.prog_pretty
        |> print_endline
  | _ ->
      failwith "ERROR: bad mode"
