module TST2

open TST

let rec in_tst (t:tst0) (s:string) : bool =
  match t, String.list_of_string s with
  | L, _ 
  | _, [] -> false
  | N (l, m, r, c, w), x::xs ->
      in_tst l s || in_tst r s ||
      (x = c && (if xs = [] then w else in_tst m (String.string_of_list xs)))

// Si tengo una letra que es menor a todo un arbol y
// la primer letra de la palabra a buscar es menor a la letra
// Entonces la palabra no esta en el arbol.

//    Letra de s   <=   c   <   todas las letras de t
//    ─────●────────────●──────[════ t ════]──────▶
let rec member_not_in_tree_gt (c:int) (t:tst0) (s:string)
  : Lemma (requires all_gt c t /\
                    (match String.list_of_string s with
                     | x::_ -> FStar.Char.int_of_char x <= c
                     | [] -> True))
          (ensures not (in_tst t s)) =
  match t with
  | L -> ()
  | N (l, _, r, _, _) -> member_not_in_tree_gt c l s; member_not_in_tree_gt c r s

// Si todo t es > c y s empieza con algo <= c, s no está en t
let rec member_not_in_tree_lt (c:int) (t:tst0) (s:string)
  : Lemma (requires all_lt c t /\
                    (match String.list_of_string s with
                     | x::_ -> FStar.Char.int_of_char x >= c
                     | [] -> True))
          (ensures not (in_tst t s)) =
  match t with
  | L -> ()
  | N (l, _, r, _, _) -> member_not_in_tree_lt c l s; member_not_in_tree_lt c r s

let rec lookup_ok (t:tst) (s:string) : Lemma (lookup t s == in_tst t s) =
    match t, String.list_of_string s with
  | L, _ -> ()
  | _, [] -> ()
  | N (l, m, r, c, w), x::xs -> 
    let x' = FStar.Char.int_of_char x in
    let c' = FStar.Char.int_of_char c in
    if x' < c' then (lookup_ok l s; member_not_in_tree_gt c' r s)
    else if x' > c' then (lookup_ok r s; member_not_in_tree_lt c' l s)
    else if x' = c' && xs = [] then (member_not_in_tree_lt c' l s; member_not_in_tree_gt c' r s)
    else (
      member_not_in_tree_lt c' l s;
      member_not_in_tree_gt c' r s;
      String.list_of_string_of_list xs;
      lookup_ok m (String.string_of_list xs)
    )
