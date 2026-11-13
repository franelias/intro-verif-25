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

//    letra de s   <=   c   <   todas las letras de t
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
  | N (l, m, r, c, w), x::xs -> let x' = FStar.Char.int_of_char x
                                in let c' = FStar.Char.int_of_char c in
                                if x' < c' then (lookup_ok l s; member_not_in_tree_gt c' r s)
                                           else if x' > c' then (lookup_ok r s; member_not_in_tree_lt c' l s)
                                                           else if x' = c' && xs = [] then (member_not_in_tree_lt c' l s; member_not_in_tree_gt c' r s)
                                                                                      else (member_not_in_tree_lt c' l s; member_not_in_tree_gt c' r s; lookup_ok m (String.string_of_list xs))

let ej = insert (insert (insert L "casa") "ca") "cosa"

let _ = assert_norm (lookup ej "casa")
let _ = assert_norm (lookup ej "ca")      // prefijo insertado después
let _ = assert_norm (lookup ej "cosa")    // rama derecha del nodo 'a'

let _ = assert_norm (not (lookup ej "cas"))    // prefijo, pero w = false
let _ = assert_norm (not (lookup ej "c"))
let _ = assert_norm (not (lookup ej "casas"))  // se pasa del final
let _ = assert_norm (not (lookup ej "perro"))  // se cae del árbol
let _ = assert_norm (not (lookup ej ""))       // palabra vacía
let _ = assert_norm (not (lookup L "casa"))    // árbol vacío

// "ab" en un árbol vacío: cadena por el medio, w solo al final
let _ = assert_norm (insert L "ab" == N (L, N (L, L, L, 'b', true), L, 'a', false))

// insertar algo que ya está, o la palabra vacía, no cambia nada
let _ = assert_norm (insert ej "casa" == ej)
let _ = assert_norm (insert ej "" == ej)

let _ = assert_norm (insert (insert L "ab") "b" <> insert (insert L "b") "ab")
let _ = assert_norm (lookup (insert (insert L "ab") "b") "b"
                   = lookup (insert (insert L "b") "ab") "b")

// - Invariante opcional: "ningún nodo está muerto". Lo podés agregar a is_tst o como predicado aparte, y probar que insert y delete lo preservan. Es lo que distingue en el tipo al delete con poda del perezoso. Si no lo pedís, las dos versiones son igual de "correctas" respecto a lookup.

// borrar algo que no está no cambia nada
let _ = assert_norm (delete ej "perro" == ej)
let _ = assert_norm (delete ej "cas" == ej)     // prefijo: s tiene m ≠ L, no se poda
let _ = assert_norm (delete ej "casas" == ej)
let _ = assert_norm (delete ej "" == ej)

// la palabra borrada desaparece y las demás siguen
let _ = assert_norm (not (lookup (delete ej "ca") "ca"))
let _ = assert_norm (lookup (delete ej "ca") "casa")
let _ = assert_norm (lookup (delete ej "ca") "cosa")

// sin poda: "ca" tiene "sa" colgando, solo se apaga un w
let _ = assert_norm (delete ej "ca" == insert (insert L "casa") "cosa")

// con poda: se va toda la rama o-s-a
let _ = assert_norm (delete ej "cosa" == insert (insert L "casa") "ca")
// con poda: se va s-a, pero la 'a' de "ca" queda
let _ = assert_norm (delete ej "casa" == insert (insert L "ca") "cosa")

// borrar la única palabra deja el árbol vacío
let _ = assert_norm (delete (insert L "casa") "casa" == L)
let _ = assert_norm (delete (delete (delete ej "ca") "casa") "cosa" == L)

// ---- necesitan extract_min0 ----

// merge: raíz 'b' con hermanos 'a' y 'c'
let abc = insert (insert (insert L "b") "a") "c"
let _ = assert_norm (delete abc "b" == N (N (L, L, L, 'a', true), L, L, 'c', true))
let _ = assert_norm (delete abc "a" == insert (insert L "b") "c")
let _ = assert_norm (delete abc "c" == insert (insert L "b") "a")

// extract_min tiene que bajar: r = 'd' con hijo izquierdo 'c'
let bdc = insert (insert (insert (insert L "b") "a") "d") "c"
let _ = assert_norm (delete bdc "b" ==
  N (N (L, L, L, 'a', true), L, N (L, L, L, 'd', true), 'c', true))

// el nodo que sube arrastra su subárbol del medio
let bcx = insert (insert (insert L "b") "a") "cx"
let _ = assert_norm (lookup (delete bcx "b") "cx")
let _ = assert_norm (lookup (delete bcx "b") "a")