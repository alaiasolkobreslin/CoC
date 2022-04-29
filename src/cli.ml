open Arg

type command =
  | Lex
  | Parse
  | Typecheck
  | Irgen

type parse_data = 
  {
    commands : command list;
    files : string list;
    out_dir : string;
  }

let commands_list = ref []
let files_list = ref []
let output_path = ref ""

let update_commands new_command =
  commands_list := new_command::(!commands_list)

let update_files file = 
  files_list := file::(!files_list)

let parse_lex = "--lex", Unit (fun () -> update_commands Lex), 
                "\tgenerate output from lexical analysis"
let parse_parse = "--parse", Unit (fun () -> update_commands Parse),
                  "\tgenerate output from syntactic analysis"
let parse_typecheck = "--typecheck", Unit (fun () -> update_commands Typecheck),
                      "\tgenerate output from semantic analysis"
let parse_irgen = "--irgen", Unit (fun () -> update_commands Irgen),
                  "\tgenerate intermediate code"
let parse_out_dir = "-D ", String (fun str -> output_path := str),
                    "<path> Specify where to place generated diagnostic files"

let spec = align [parse_lex; parse_parse; parse_typecheck; parse_irgen;
                  parse_out_dir]

let usage_msg = "hazelc [--lex files | --parse files |" ^
                " --typecheck files | --irgen files]"

let parse_command () =
  parse spec update_files usage_msg;
  {
    commands = !commands_list |> List.rev;
    files = !files_list |> List.rev;
    out_dir = !output_path
  }