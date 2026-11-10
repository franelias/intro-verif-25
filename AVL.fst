module AVL

let max (x y : int) : int = if x > y then x else y

// Un nodo del arbol guarda el valor del nodo
// y la áltura en la que se encuentra.
type avl0 =
  | L
  | N of avl0 & int & nat & avl0

// Todos los valores de t son menores a x
let rec all_lt (x: int) (t: avl0) : bool =
  match t with
  | L -> true
  | N (l, y, _, r) -> all_lt x l && y < x && all_lt x r

// Todos los valores de t son mayores a x
let rec all_gt (x: int) (t: avl0) : bool =
  match t with
  | L -> true
  | N (l, y, _, r) -> all_gt x l && y > x && all_gt x r

let rec is_bst (t: avl0) : bool =
  match t with
  | L -> true
  | N (l, x, _, r) -> is_bst l && is_bst r && all_lt x l && all_gt x r

// Altura calculada por recursión.
// Ver si usar la del nodo.
let rec height (t: avl0) : nat =
  match t with
  | L -> 0
  | N (l, x, _, r) -> 1 + max (height l) (height r)

// Altura calculada por el dato del nodo.
let hgt (t: avl0) : nat = height t
  // match t with
  // | L -> 0
  // | N (l, x, h, r) -> h

// Balance factor: la diferencia entre la altura del subárbol 
// de la derecha y el de la izquierda
let bf (t: avl0) : int =
  match t with
  | L -> 0
  | N (l, x, _, r) -> hgt r - hgt l

let rec is_balanced (t:avl0) : bool =
  match t with
  | L -> true
  | N (l, x, _, r) -> is_balanced l && is_balanced r && bf t >= -1 && bf t <= 1

let rec heights_ok (t:avl0) : bool =
  match t with
  | L -> true
  | N (l, _, h, r) -> heights_ok l && heights_ok r && h = 1 + max (hgt l) (hgt r)

let is_avl (t:avl0) : bool = is_bst t && is_balanced t && heights_ok t

let create_node (l:avl0) (x:int) (r:avl0) = N(l, x, 1 + max (hgt l) (hgt r), r)

let rotate_right (t:avl0) : avl0 =
  match t with
    | L -> L
    | N ( N (l, y, _, r'), x, _, r) -> create_node l y (create_node r' x r)
    | _ -> t


//    x                  y
//   / \                / \
//  l   y      ==>     x   r
//     / \            / \
//    l'  r          l   l'
let rotate_left (t:avl0) : avl0 =
  match t with
    | L -> L
    | N (l, x, _, N(l', y, _, r) ) -> create_node (create_node l x l') y r
    | _ -> t

let balance (l:avl0) (x:int) (r:avl0) : avl0 =
  let t = (create_node l x r) in
  if bf t < -1 then if bf l <= 0 then rotate_right t
                                 else rotate_right (create_node (rotate_left l) x r)
               else if bf t > 1 then if bf r >= 0 then rotate_left t
                                                  else rotate_left (create_node l x (rotate_right r))
                                else t

let rec insert0 (x: int) (t: avl0) : avl0 =
  match t with
  | L -> N (L, x, 1, L)
  | N (l, y, h, r) ->
    if x = y then t
    else if x < y then balance (insert0 x l) y r
                  else balance l y (insert0 x r)