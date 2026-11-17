module Clase04.BST

open FStar.Mul
open FStar.List.Tot

let max (x y : int) : int = if x > y then x else y

type bst =
  | L
  | N of bst & int & bst

let rec insert (x: int) (t: bst) : bst =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: admite duplicados *)
    if x <= y
    then N (insert x l, y, r)
    else N (l, y, insert x r)

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) == 1 + size t) =
  match t with
  | L -> ()
  | N (l, n, r) -> if x <= n then insert_size x l else insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height (insert x t) <= 1 + height t)
= match t with
  | L -> ()
  | N (l, n, r) -> if x <= n then insert_height x l else insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l, n, r) -> if x <= n then insert_mem x l else insert_mem x r

(* ¿Puede demostrar también que:
     height t <= height (insert x t)
   ? ¿Cuál es la forma "más fácil" de hacerlo? *)

let rec insert_height' (x:int) (t:bst)
: Lemma (height (insert x t) <= 1 + height t /\ height t <= height (insert x t))
= match t with
  | L -> ()
  | N (l, n, r) -> if x <= n then insert_height' x l else insert_height' x r

let rec extract_min (t: bst) : option (int & bst) =
  match t with
  | L -> None
  | N (L, x, r) -> Some (x, r)
  | N (l, x, r) ->
    match extract_min l with
    | None -> None
    | Some (y, l') -> Some (y, N (l', x, r))

let delete_root (t: bst) : Pure bst (requires N? t) (ensures fun _ -> True) =
  let N (l, _, r) = t in
  match extract_min r with
  | None -> l
  | Some (x, r') -> N (l, x, r')

let rec delete (x: int) (t: bst) : bst =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete x l, y, r)
    else if x > y then N (l, y, delete x r)
    else delete_root t

let rec delete_root_L (t:bst) : Lemma (requires extract_min t == None) (ensures t == L) =
  match t with
  | L -> ()
  | N (l, _, _) -> delete_root_L l

let rec extract_min_size (t:bst)
  : Lemma (requires Some? (extract_min t))
          (ensures (let Some (_, t') = extract_min t in size t' == size t - 1)) =
  match t with
  | N (L, _, _) -> ()
  | N (l, _, _) -> extract_min_size l

let delete_root_size (t:bst) : Lemma (requires N? t) (ensures size (delete_root t) == size t - 1) =
  let N (l, _, r) = t in
  match extract_min r with
  | None -> delete_root_L r
  | Some (x, r') -> extract_min_size r

(* Un poco más difícil. Require un lema auxiliar sobre extract_min:
declárelo y demuéstrelo. Si le parece conveniente, puede modificar
las definiciones de delete, delete_root y extract_min. *)
let rec delete_size (x:int) (t:bst) : Lemma (delete x t == t \/ size (delete x t) == size t - 1) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    if x < y then delete_size x l
    else if x > y then delete_size x r
    else delete_root_size t

(* Versión más fuerte del lema anterior. *)
let rec delete_size_mem (x:int) (t:bst)
: Lemma (requires member x t)
        (ensures size (delete x t) == size t - 1)
= match t with
  | N (l, y, r) ->
    if x < y then delete_size_mem x l
    else if x > y then delete_size_mem x r
    else delete_root_size t

let length_lists (l1 l2 l3 : list int) : Lemma (length (l1 @ l2 @ l3) = length l1 + length l2 + length l3) = ()

let rec to_list_length (t:bst) : Lemma (length (to_list t) == size t) =
  match t with
  | L -> ()
  | N (l, y, r) -> length_lists (to_list l) [y] (to_list r); to_list_length l; to_list_length r

(* Contestar en texto (sin intentar formalizar):
    ¿Es cierto que `member x (insert y (insert x t))`? ¿Cómo se puede probar? Si
    ¿Es cierto que `delete x (insert x t) == t`? No, el árbol admite duplicados
*)

