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

let rec is_tst (t:tst0) : bool =
  match t with
  | L -> true
  | N (l, m, r, c, _) ->
  let c' = FStar.Char.int_of_char c in
  is_tst l && is_tst m && is_tst r && all_lt c' l && all_gt c' r

type tst = t:tst0{is_tst t}

let rec lookup (t:tst) (s:string) : bool =
  match t, String.list_of_string s with
  | L, _ -> false
  | _, [] -> false
  | N (l, m, r, c, w), x::xs ->
    let x' = FStar.Char.int_of_char x in
    let c' = FStar.Char.int_of_char c in
    if x' < c' then lookup l s
    else if x' > c' then lookup r s
    else if x' = c' && xs = [] then w
    else lookup m (String.string_of_list xs)

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
      else if x' > c' then N  (l, m, insert0' r s, c, w)
      else if x' = c' && xs = [] then N (l, m, r, c, true)
      else N (l, insert0' m xs, r, c, w)

let insert0 (t:tst0) (s:string) : tst0 = insert0' t (String.list_of_string s)

let insert0_tst (t:tst0) (s:string)
  : Lemma (requires is_tst t) (ensures is_tst (insert0 t s)) =
  admit()

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

let delete0_tst (t:tst0) (s:string) : Lemma (requires is_tst t) (ensures is_tst (delete0 t s)) = admit()

let delete (t:tst) (s:string) : tst =
  delete0_tst t s;
  delete0 t s