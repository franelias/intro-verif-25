module TST3

open Container
open TST

type no_empty_string = (s:string{String.strlen s > 0})

instance tst_son_container0
  : container0 no_empty_string tst = {
    empty = L;
    is_empty = L?;

    mem = (fun (s:no_empty_string) t -> lookup t s);
    ins = (fun (s:no_empty_string) t -> insert t s);
    del = (fun (s:no_empty_string) t -> delete t s);
}

let models (t:tst) (ss:TSet.set no_empty_string) : prop =
  forall (s:no_empty_string). lookup t s <==> TSet.mem s ss

let rec first_word' (t:tst) =
  match t with
  | L -> []
  | N (_, m, _, c, w) -> if w then [c] else c :: first_word' m

// Por construcción, el primer nodo es parte de la primer palabra
// insertada en el árbol cuando el árbol no es vacío.
let first_word (t:tst) : string = String.string_of_list (first_word' t)

let rec at_least_one (t:tst{N? t}) : Lemma (lookup t (first_word t)) =
  String.list_of_string_of_list (first_word' t);
  match t with
  | L -> ()
  | N (_, m, _, _, w) -> if w then () else (at_least_one m; String.list_of_string_of_list (first_word' m))

// Se prueba que si el árbol es vacío, no hay elementos, y si no lo es, hay al menos uno.
let is_empty_ok_lem (t:tst) : Lemma (is_empty t <==> models t TSet.empty) =
  if L? t then () else at_least_one t

let rec insert0_ok_lem (t:tst) (s s':list String.char)
  : Lemma (ensures is_tst (insert0' t s) /\
                   (lookup' (insert0' t s) s' <==> (lookup' t s' \/ (s' = s /\ Cons? s)))) =
  insert0'_tst t s;
  match s, s' with
  | [], _ -> ()
  | _, [] -> ()
  | x::xs, y::ys ->
    match t with
    | L -> (
      match xs with
      | [] -> ()
      | _ -> insert0_ok_lem L xs ys
    )
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then insert0_ok_lem l s s'
      else if x' > c' then insert0_ok_lem r s s'
      else if x' = c' && xs = [] then ()
      else insert0_ok_lem m xs ys

// lookup (insert t s) s' <==> TSet.mem s' (TSet.union ss (TSet.singleton s))
let ins_ok_lem (s:no_empty_string) (t:tst) (ss:TSet.set no_empty_string) : Lemma (requires t `models` ss)
                                                                                 (ensures  ins s t
                                                                                           `models`
                                                                                           // ss U {x}
                                                                                           TSet.union ss (TSet.singleton s)) =
  introduce forall (s':no_empty_string).
      lookup (insert t s) s' <==> TSet.mem s' (TSet.union ss (TSet.singleton s))
  with (
    String.string_of_list_of_string s;
    String.string_of_list_of_string s';
    insert0_ok_lem t (String.list_of_string s) (String.list_of_string s')
  )

// Si c es más grande que todos los nodos de t,
// la primer letra de cualquier palabra de t es más chica que c
let rec all_lt_lookup (c:int) (t:tst) (x:String.char) (xs:list String.char)
  : Lemma (requires all_lt c t /\ lookup' t (x::xs))
          (ensures FStar.Char.int_of_char x < c) =
  match t with
  | L -> ()
  | N (l, m, r, c0, w) ->
    let x' = FStar.Char.int_of_char x in
    let c0' = FStar.Char.int_of_char c0 in
    if x' < c0' then all_lt_lookup c l x xs
    else if x' > c0' then all_lt_lookup c r x xs
    else ()

// Si c es más chica que todos los nodos de t,
// la primer letra de cualquier palabra de t es más grande que c
let rec all_gt_lookup (c:int) (t:tst) (x:String.char) (xs:list String.char)
  : Lemma (requires all_gt c t /\ lookup' t (x::xs))
          (ensures FStar.Char.int_of_char x > c) =
  match t with
  | L -> ()
  | N (l, m, r, c0, w) ->
    let x' = FStar.Char.int_of_char x in
    let c0' = FStar.Char.int_of_char c0 in
    if x' < c0' then all_gt_lookup c l x xs
    else if x' > c0' then all_gt_lookup c r x xs
    else ()

// extract_min0 solo saca el más chico del árbol t, no hace nada mas.
let rec extract_min0_ok_lem (t:tst{N? t}) (y:String.char) (ys:list String.char)
  : Lemma (let ((c', m', w'), t') = extract_min0 t in
                is_tst t' /\ is_tst m' /\
                (lookup' t (y::ys) <==>
                ((y = c' /\ (if ys = [] then w' else lookup' m' ys)) \/ lookup' t' (y::ys)))) =
  extract_min0_tst t;
  match t with
  | N (L, m, r, c, w) ->
    Classical.move_requires (all_gt_lookup (FStar.Char.int_of_char c) r y) ys
  | N (l, m, r, c, w) ->
    extract_min0_ok_lem l y ys;
    extract_min0_all_lt (FStar.Char.int_of_char c) l

let merge0_ok_lem (c:int) (l r:tst) (s:list String.char) : Lemma (requires all_lt c l /\ all_gt c r)
                                                                 (ensures is_tst (merge0 l r) /\ (lookup' (merge0 l r) s <==> (lookup' l s \/ lookup' r s))) =
  merge0_tst c l r;
  match l, r, s with
  | L, _, _ -> ()
  | _, L, _ -> ()
  | _, _, [] -> ()
  | _, _, y::ys ->
    let ((c', _, _), _) = extract_min0 r in
    extract_min0_ok_lem r y ys;
    extract_min0_tst r;
    extract_min0_all_gt c r;
    Classical.move_requires (all_lt_lookup c l y) ys;
    Classical.move_requires (all_gt_lookup (FStar.Char.int_of_char c') (snd (extract_min0 r)) y) ys

let prune0_ok_lem (c:String.char) (l m r:tst) (w:bool) (y:String.char) (ys:list String.char)
  : Lemma (requires all_lt (FStar.Char.int_of_char c) l /\ all_gt (FStar.Char.int_of_char c) r)
          (ensures is_tst (prune0 l m r c w) /\
                   (lookup' (prune0 l m r c w) (y::ys) <==>
                    (let y' = FStar.Char.int_of_char y in
                     let c' = FStar.Char.int_of_char c in
                     if y' < c' then lookup' l (y::ys)
                     else if y' > c' then lookup' r (y::ys)
                     else if ys = [] then w
                     else lookup' m ys))) =
  if (not w) && m = L
  then (merge0_ok_lem (FStar.Char.int_of_char c) l r (y::ys);
        Classical.move_requires (all_lt_lookup (FStar.Char.int_of_char c) l y) ys;
        Classical.move_requires (all_gt_lookup (FStar.Char.int_of_char c) r y) ys)
  else ()

let rec delete0_ok_lem (t:tst) (s s':list String.char) : Lemma (lookup' (delete t (String.string_of_list s)) s' <==> (lookup' t s' /\ s' <> s)) =
  String.list_of_string_of_list s;
  match s, s' with
  | [], _ -> ()
  | _, [] -> ()
  | x::xs, y::ys ->
    match t with
    | L -> ()
    | N (l, m, r, c, w) ->
      let x' = FStar.Char.int_of_char x in
      let c' = FStar.Char.int_of_char c in
      if x' < c' then delete0_ok_lem l s s'
      else if x' > c' then delete0_ok_lem r s s'
      else if x' = c' && xs = [] then prune0_ok_lem c l m r false y ys
      else (String.list_of_string_of_list xs;
            delete0_ok_lem m xs ys;
            prune0_ok_lem c l (delete m (String.string_of_list xs)) r w y ys)

// lookup (delete t s) s' <==> TSet.mem s' (TSet.intersect ss (TSet.complement (TSet.singleton s)))
let del_ok_lem (s:no_empty_string) (t:tst) (ss:TSet.set no_empty_string) : Lemma (requires t `models` ss)
                                                                                 (ensures  del s t
                                                                                           `models`
                                                                                           // ss \ {x}
                                                                                           TSet.intersect ss (TSet.complement <| TSet.singleton s)) =
  introduce forall (s':no_empty_string).
      lookup (delete t s) s' <==> TSet.mem s' (TSet.intersect ss (TSet.complement (TSet.singleton s)))
  with (
    String.string_of_list_of_string s;
    String.string_of_list_of_string s';
    delete0_ok_lem t (String.list_of_string s) (String.list_of_string s')
  )

instance tst_son_container_laws (a:eqtype)
  : container_laws no_empty_string tst #_ = {
    models = models;
    empty_ok = (fun _ -> ());
    is_empty_ok = is_empty_ok_lem;
    mem_ok = (fun _ _ _ -> ());
    ins_ok = ins_ok_lem;
    del_ok = del_ok_lem;
}
