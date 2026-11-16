module TST

// Un nodo tiene la forma N (left, middle, right, letra, es_palabra)
type tst0 =
  | L
  | N of tst0 & tst0 & tst0 & FStar.Char.char & bool

let rec all_lt (c:int) (t:tst0) : bool =
  match t with
  | L -> true
  | N (l, _, r, c', _) ->
    FStar.Char.int_of_char c' < c && all_lt c l && all_lt c r

let rec all_gt (c:int) (t:tst0) : bool =
  match t with
  | L -> true
  | N (l, _, r, c', _) ->
    FStar.Char.int_of_char c' > c && all_gt c l && all_gt c r

// No se permiten nodos muertos, como por ejemplo N (L, L, L, 'a', false)
let rec is_tst (t:tst0) : bool =
  match t with
  | L -> true
  | N (l, m, r, c, w) ->
  let c' = FStar.Char.int_of_char c in
  (w || N? m) &&
  is_tst l && is_tst m && is_tst r && all_lt c' l && all_gt c' r

type tst = t:tst0{is_tst t}

let rec lookup' (t:tst) (s:list String.char) : bool =
  match t, s with
  | L, _ -> false
  | _, [] -> false
  | N (l, m, r, c, w), x::xs ->
    let x' = FStar.Char.int_of_char x in
    let c' = FStar.Char.int_of_char c in
    if x' < c' then lookup' l s
    else if x' > c' then lookup' r s
    else if x' = c' && xs = [] then w
    else lookup' m xs

let lookup (t:tst) (s:string) : bool = lookup' t (String.list_of_string s)

let rec insert0' (t:tst0) (s:list String.char) : tst0 =
  match s with
  | [] -> t
  | x::xs ->
    match t with
    | L -> (
      match xs with
      | [] -> N (L, L, L, x, true)
      | otherwise -> N (L, insert0' L xs, L, x, false)
    )
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then N (insert0' l s, m, r, c, w)
      else if x' > c' then N (l, m, insert0' r s, c, w)
      else if x' = c' && xs = [] then N (l, m, r, c, true)
      else N (l, insert0' m xs, r, c, w)

let insert0 (t:tst0) (s:string) : tst0 = insert0' t (String.list_of_string s)

let rec insert0'_all_lt (c:int) (t:tst0) (x:String.char) (xs:list String.char) : Lemma (requires all_lt c t /\ FStar.Char.int_of_char x < c) (ensures all_lt c (insert0' t (x::xs))) =
  match t with
  | L -> ()
  | N (l, _, r, c', _) -> insert0'_all_lt c l x xs; insert0'_all_lt c r x xs

let rec insert0'_all_gt (c:int) (t:tst0) (x:String.char) (xs:list String.char) : Lemma (requires all_gt c t /\ FStar.Char.int_of_char x > c) (ensures all_gt c (insert0' t (x::xs))) =
  match t with
  | L -> ()
  | N (l, _, r, c', _) -> insert0'_all_gt c l x xs; insert0'_all_gt c r x xs

let rec insert0'_tst (t:tst0) (s:list String.char)
  : Lemma (requires is_tst t) (ensures is_tst (insert0' t s)) =
  match s with
  | [] -> ()
  | x::xs -> 
    match t with
    | L -> (
      match xs with
      | [] -> ()
      | otherwise -> insert0'_tst L xs
    )
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then (let l' = insert0' l s in (insert0'_all_lt c' l x xs; insert0'_tst l s))
      else if x' > c' then (let r' = insert0' r s in (insert0'_all_gt c' r x xs; insert0'_tst r s))
      else if x' = c' && xs = [] then ()
      else insert0'_tst m xs

let insert0_tst (t:tst0) (s:string)
  : Lemma (requires is_tst t) (ensures is_tst (insert0 t s)) =
  insert0'_tst t (String.list_of_string s)

let insert (t:tst) (s:string) : tst =
  insert0_tst t s;
  insert0 t s

let rec extract_min0 (t:tst0{N? t}) : ((String.char & tst0 & bool) & tst0) =
  match t with
  | N (L, m, r, c, w) -> ((c, m, w), r)
  | N (l, m, r, c, w) ->
    let (min, l') = extract_min0 l in
    (min, N(l', m, r, c, w))

let merge0 (l r:tst0) : tst0 =
  match l, r with
  | L, _ -> r
  | _, L -> l
  | otherwise ->
    let ((c', m', w'), r') = extract_min0 r in
    N (l, m', r', c', w')

// Solamente se prunea si el nodo quedó sin subarbol medio o
// ninguna palabra termina en el nodo (no es parte de ninguna palabra).
let prune0 (l m r:tst0) (c:String.char) (w:bool) : tst0 =
  if (not w) && m = L
  then merge0 l r
  else N (l, m, r, c, w)

let rec delete0' (t:tst0) (s:list String.char) : tst0 =
  match s with
  | [] -> t
  | x::xs ->
    match t with
    | L -> L
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then N (delete0' l s, m, r, c, w)
      else if x' > c' then N (l, m, delete0' r s, c, w)
      else if x' = c' && xs = [] then prune0 l m r c false
      else prune0 l (delete0' m xs) r c w

let delete0 (t:tst0) (s:string) : tst0 = delete0' t (String.list_of_string s)

let rec extract_min0_all_lt (c:int) (t:tst0)
  : Lemma (requires N? t /\ all_lt c t)
          (ensures (let ((c', _, _), t') = extract_min0 t in
                    FStar.Char.int_of_char c' < c /\ all_lt c t')) =
  match t with
  | N (L, _, _, _, _) -> ()
  | N (l, _, _, _, _) -> extract_min0_all_lt c l

let merge0_all_lt (c:int) (l r:tst0)
  : Lemma (requires all_lt c l /\ all_lt c r) (ensures all_lt c (merge0 l r)) =
  match l, r with
  | L, _ -> ()
  | _, L -> ()
  | otherwise -> extract_min0_all_lt c l; extract_min0_all_lt c r

let rec delete0'_all_lt (c:int) (t:tst0) (x:String.char) (xs:list String.char) 
  : Lemma (requires all_lt c t) (ensures all_lt c (delete0' t (x::xs))) =
  match t with
  | L -> ()
  | N (l, _, r, c', _) -> merge0_all_lt c l r; delete0'_all_lt c l x xs; delete0'_all_lt c r x xs

let rec extract_min0_all_gt (c:int) (t:tst0)
  : Lemma (requires N? t /\ all_gt c t)
          (ensures (let ((c', _, _), t') = extract_min0 t in
                    FStar.Char.int_of_char c' > c /\ all_gt c t')) =
  match t with
  | N (L, _, _, _, _) -> ()
  | N (l, _, _, _, _) -> extract_min0_all_gt c l

let merge0_all_gt (c:int) (l r:tst0)
  : Lemma (requires all_gt c l /\ all_gt c r) (ensures all_gt c (merge0 l r)) =
  match l, r with
  | L, _ -> ()
  | _, L -> ()
  | otherwise -> extract_min0_all_gt c l; extract_min0_all_gt c r

let rec delete0'_all_gt (c:int) (t:tst0) (x:String.char) (xs:list String.char) 
  : Lemma (requires all_gt c t) (ensures all_gt c (delete0' t (x::xs))) =
  match t with
  | L -> ()
  | N (l, _, r, c', _) -> merge0_all_gt c l r; delete0'_all_gt c l x xs; delete0'_all_gt c r x xs

let rec all_gt_trans (c c':int) (t:tst0) : Lemma (requires all_gt c t /\ c >= c') (ensures all_gt c' t) =
  match t with
  | L -> ()
  | N (l, _, r, c'', _) -> all_gt_trans c c' l; all_gt_trans c c' r

let rec extract_min0_tst (t:tst0{N? t})
: Lemma (requires is_tst t)
        (ensures (let ((c', m', w'), t') = extract_min0 t
                  in (w' || N? m') /\ is_tst t' /\ is_tst m' /\ all_gt (FStar.Char.int_of_char c') t')) =
  match t with
  | N (L, m, r, c, w) -> ()
  | N (l, m, r, c, w) ->
    let ((c', m', _), t') = extract_min0 l in
    extract_min0_tst l;
    extract_min0_all_lt (FStar.Char.int_of_char c) l;
    all_gt_trans (FStar.Char.int_of_char c) (FStar.Char.int_of_char c') r

let rec all_lt_trans (c c':int) (t:tst0) : Lemma (requires all_lt c t /\ c <= c') (ensures all_lt c' t) =
  match t with
  | L -> ()
  | N (l, _, r, c'', _) -> all_lt_trans c c' l; all_lt_trans c c' r

let merge0_tst (c:int) (l r:tst0) : Lemma (requires is_tst l && is_tst r && all_lt c l && all_gt c r) (ensures is_tst (merge0 l r)) =
  match l, r with
  | L, _ -> ()
  | _, L -> ()
  | otherwise ->
      let ((c', m', w'), r') = extract_min0 r in
      extract_min0_tst r;
      extract_min0_all_gt c r;
      all_lt_trans c (FStar.Char.int_of_char c') l
      
  // N (l, m', r', c', w')
  // Hay que demostrar que N (l, m', r', c', w') es tst
  // l tiene que ser tst
  // r' tiene que ser tst
  // c' tiene que ser mas grande que l
  // c' tiene que ser mas chico que r'
  // El nodo pertenece a una palabra

let rec delete0'_tst (t:tst0) (s:list String.char)
  : Lemma (requires is_tst t) (ensures is_tst (delete0' t s)) =
  match s with
  | [] -> ()
  | x::xs -> 
    match t with
    | L -> ()
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then (let l' = delete0' t s in delete0'_all_lt c' l x xs; delete0'_tst l s)
      else if x' > c' then (let l' = delete0' t s in delete0'_all_gt c' r x xs; delete0'_tst r s)
      else if x' = c' && xs = [] then merge0_tst c' l r
      else delete0'_tst m xs; merge0_tst c' l r

let delete0_tst (t:tst0) (s:string) : Lemma (requires is_tst t) (ensures is_tst (delete0 t s)) =
  delete0'_tst t (String.list_of_string s)

let delete (t:tst) (s:string) : tst =
  delete0_tst t s;
  delete0 t s