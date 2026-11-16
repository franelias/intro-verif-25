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

let ins_ok_lem (s:no_empty_string) (t:tst) (ss:TSet.set no_empty_string) : Lemma (requires t `models` ss)
                                                                                 (ensures  ins s t
                                                                                           `models`
                                                                                           // ss U {x}
                                                                                           TSet.union ss (TSet.singleton s)) =
  admit()

let del_ok_lem (s:no_empty_string) (t:tst) (ss:TSet.set no_empty_string) : Lemma (requires t `models` ss)
                                                                                 (ensures  del s t
                                                                                           `models`
                                                                                           // ss \ {x}
                                                                                           TSet.intersect ss (TSet.complement <| TSet.singleton s)) = admit() 

instance tst_son_container_laws (a:eqtype)
  : container_laws no_empty_string tst #_ = {
    models = models;
    empty_ok = (fun _ -> ());
    is_empty_ok = is_empty_ok_lem;
    mem_ok = (fun _ _ _ -> ());
    ins_ok = ins_ok_lem;
    del_ok = del_ok_lem;
}
