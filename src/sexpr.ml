type sexpr =
  | SNode of string
  | SList of sexpr list

let indent = 2

(** [iter_sep f_val f_sep lst] is equivalent to [List.iter f_val lst],
    except it also performs [f_val ()] between each item in the
    list. *)
let rec iter_sep f_val f_sep = function
  | [] -> ()
  | hd :: [] -> f_val hd
  | hd :: tl -> f_val hd; f_sep (); iter_sep f_val f_sep tl

let rec pp_print_sexpr fmt = function
  | SNode node ->
    Format.pp_print_string fmt node;
    Format.pp_print_cut fmt ()
  | SList lst ->
    Format.pp_open_box fmt indent;
    Format.pp_print_string fmt "(";
    iter_sep (pp_print_sexpr fmt) (Format.pp_print_space fmt) lst;
    Format.pp_print_string fmt ")";
    Format.pp_close_box fmt ()