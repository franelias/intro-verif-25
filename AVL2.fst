module AVL2

open AVL

let balance_all_lt (y:int) (l:avl0) (x:int) (r:avl0) : Lemma (requires all_lt y l /\ x < y /\ all_lt y r) (ensures all_lt y (balance l x r)) =
  ()

let balance_all_gt (y:int) (l:avl0) (x:int) (r:avl0) : Lemma (requires all_gt y l /\ x > y /\ all_gt y r) (ensures all_gt y (balance l x r)) =
  ()

//       y = 6; x = 5
//   2
//  / \
// 1   4

//       y = 6
//   2
//  / \
// 1   4
//      \
//       5
// Si tengo x < y tal que y es mas grande que todo el arbol,
// Si inserto x esa invariante se sigue cumpliendo.
let rec insert0_all_lt (x:int) (t:avl0) (y:int)
  : Lemma (requires all_lt y t /\ x < y)
          (ensures all_lt y (insert0 x t))
          (decreases t)
  = match t with
    | L -> ()
    | N (l, n, _, r) -> insert0_all_lt x l y;
                        insert0_all_lt x r y;
                        balance_all_lt y (insert0 x l) n r;
                        balance_all_lt y l n (insert0 x r)

let rec insert0_all_gt (x:int) (t:avl0) (y:int)
  : Lemma (requires all_gt y t /\ x > y)
          (ensures all_gt y (insert0 x t))
  = match t with
    | L -> ()
    | N (l, n, _, r) -> insert0_all_gt x l y;
                        insert0_all_gt x r y;
                        balance_all_gt y (insert0 x l) n r;
                        balance_all_gt y l n (insert0 x r)

let rec all_lt_trans (x y:int) (t:avl0)
  : Lemma (requires all_lt x t /\ x <= y) (ensures all_lt y t) =
  match t with
  | L -> ()
  | N (l, _, _, r) -> all_lt_trans x y l; all_lt_trans x y r

let rec all_gt_trans (x y:int) (t:avl0)
  : Lemma (requires all_gt x t /\ x >= y) (ensures all_gt y t) =
  match t with
  | L -> ()
  | N (l, _, _, r) -> all_gt_trans x y l; all_gt_trans x y r

// Para probar is_bst sobre rotate_left hay que probar que create_node (create_node l x l') y r es un bst.
// (create_node l x l') es trivialmente un bst, x es mayor que todo l y menor que todo l' por construcción del bst.
// Solo quedaría demostrar inductivamente que y es mayor que el nuevo nodo.
let rotate_left_bst (t:avl0) : Lemma (requires is_bst t) (ensures is_bst (rotate_left t)) = 
  match t with
  | L -> ()
  | N (l, x, _, N(l', y, _, r) ) -> all_lt_trans x y l
  | otherwise -> ()

let rotate_right_bst (t:avl0) : Lemma (requires is_bst t) (ensures is_bst (rotate_right t)) =
  match t with
  | L -> ()
  | N ( N (l, y, _, r'), x, _, r) -> all_gt_trans x y r
  | otherwise -> ()

let balance_bst (l:avl0) (x:int) (r:avl0) : Lemma (requires is_bst l /\ is_bst r /\ all_lt x l /\ all_gt x r) (ensures is_bst (balance l x r)) =
  let t = (create_node l x r) in
  if bf t < -1 then if bf l <= 0 then rotate_right_bst t
                                 else (rotate_left_bst l; rotate_right_bst (create_node (rotate_left l) x r))
               else if bf t > 1 then if bf r >= 0 then rotate_left_bst t
                                                  else (rotate_right_bst r; rotate_left_bst (create_node l x (rotate_right r)))
                                else ()

let rec insert0_bst (x:int) (t:avl0) : Lemma (requires is_bst t) (ensures is_bst (insert0 x t)) (decreases t) =
  match t with
    | L -> ()
    | N (l, n, _, r) ->  if x = n then () else if x < n then (insert0_bst x l; insert0_all_lt x l n; balance_bst (insert0 x l) n r) else (insert0_bst x r; insert0_all_gt x r n; balance_bst l n (insert0 x r))

let balance_balanced (l:avl0) (x:int) (r:avl0)
  : Lemma (requires is_balanced l /\ is_balanced r /\ heights_ok l /\ heights_ok r /\
                    hgt l - hgt r <= 2 /\ hgt r - hgt l <= 2)
          (ensures (let t = balance l x r in
                    let m = max (hgt l) (hgt r) in
                    is_balanced t /\ heights_ok t /\
                    m <= hgt t /\ hgt t <= m + 1 /\
                    ((hgt l - hgt r <= 1 /\ hgt r - hgt l <= 1) ==> hgt t == m + 1)))
  =   let t = (create_node l x r) in
      if bf t < -1 then if bf l <= 0 then ()
                                     else ()
                   else if bf t > 1 then if bf r >= 0 then ()
                                                      else ()
                                    else ()

// Garantiza que el insert deja el árbol balanceado
// y que el resultado del mismo difiere como mucho en 1 de altura.
let rec insert0_balanced (x:int) (t:avl0) : Lemma (requires is_balanced t /\ heights_ok t) (ensures (let t' = insert0 x t in
                                                                                                    is_balanced t' /\ heights_ok t' /\ hgt t <= hgt t' /\ hgt t' <= hgt t + 1) ) (decreases t) =
  match t with
  | L -> ()
  | N (l, y, h, r) -> insert0_balanced x l;
                      insert0_balanced x r;
                      balance_balanced (insert0 x l) y r;
                      balance_balanced  l y (insert0 x r)

let insert0_avl (x:int) (t:avl0) : Lemma (requires is_avl t) (ensures is_avl (insert0 x t)) =
  insert0_balanced x t; insert0_bst x t

type avl = t:avl0{is_avl t}

let insert (x:int) (t:avl) : avl =
  insert0_avl x t;
  insert0 x t

let _ = assert (insert 3 L = N (L, 3, 1, L))
let _ = assert (insert 4 (N (L, 3, 1, L)) = N (L, 3, 2, N (L, 4, 1, L)))

// Se puede demostrar la correctitud del height guardado en el nodo