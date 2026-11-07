module Clase04.Fib

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul

let abs (x : int)   : nat = if x >= 0 then x else -x
let max (x y : int) : int = if x > y then x else y

let rec fac (x:int) : int =
  if x <= 0 then 1 else x * fac (x - 1)

let rec fac_is_pos (x:int) : Lemma (requires True) (ensures fac x > 0) =
  if x <= 0
  then ()
  else fac_is_pos (x-1)

let suma_fac (x y : int) : pos =
  fac_is_pos x;
  fac_is_pos y;
  fac x + fac y

let rec fac_is_gt (x:int) : Lemma (requires x >= 3) (ensures fac x > x) =
  if x = 3
  then ()
  else fac_is_gt (x-1)

(* N-ésimo número triangular. *)
let rec triang (n:nat) : int =
  if n = 0 then 0 else triang (n - 1) + n

// 1   + 2  + ... + 100
// 100 + 99 + ... + 1
// 101 + 101 + ... + 101 = 101 * 100
// suma = 101 * 100 / 2 = 5050
(* https://en.wikipedia.org/wiki/Arithmetic_progression#History *)
let rec gauss (n:nat) : Lemma (triang n == n * (1 + n) / 2) =
  if n = 0 then ()
  else gauss (n-1)

let rec fib (x:nat) : nat =
  if x = 0 then 1
  else if x = 1 then 1
  else fib (x - 1) + fib (x - 2)

(* Fibonacci en tiempo lineal *)
let rec fib_lin' (x:nat) : (int & int) =
  if x = 0 then (1, 1)
   else
      let (a, b) = fib_lin' (x - 1) in
      (b, a + b)
let fib_lin (n:nat) : int = fst (fib_lin' n)

(* Demuestre que es correcta. *)
let fib_lin_ok (n:nat) : Lemma (fib_lin n == fib n) =
  let rec fib_lin_aux (n:nat) : Lemma ((fst (fib_lin' (n)) == fib (n)) /\ (snd (fib_lin' (n)) == fib(n+1))) =
    if n = 0 then () else fib_lin_aux (n-1)
  in fib_lin_aux n

// fib_lin n
// ==
// fst (fib_lin' n)
// == (a, b) = fib_lin' (n - 1)
// fst (b, a + b)
// ==
// b
// ==
// snd (fib_lin' (n - 1))

// HI fib_lin_ok : fst (fib_lin' (n-1)) == fib (n-1)

(* Fibonacci en tiempo lineal con recursión de cola (esencialmente
un bucle while). *)
let rec fib_tail' (a b : nat) (n : nat) : Tot nat (decreases n) =
  if n = 0 then a
  else fib_tail' b (a + b) (n - 1)
let fib_tail (n:nat) : nat = fib_tail' 1 1 n

(* Demuestre que es correcta. Va a necesitar un lema auxiliar para fib_tail'. *)
let fib_tail_ok (n:nat) : Lemma (fib_tail n == fib n) =
  let rec fib_tail_aux (n k:nat) : Lemma (ensures fib_tail' (fib k) (fib (k+1)) n == (fib (n+k))) (decreases n)  =
    if n = 0 then () else fib_tail_aux (n-1) (k+1)
  in fib_tail_aux n 0

// fib_tail n
// ==
// fib_tail' (fib 0) (fib 1) n
// ==
// fib_tail' 1 2 (n - 1)
// ==
// fib_tail' (fib 1) (fib 0 + fib 1) (n - 1)
// ==
// Lemma
// ==
// fib n


// HI: fib_tail (n-1) == fib (n-1)
//     fib_tail' 1 1 (n-1) == fib (n-1)

// fib_tail' (fib k) (fib (k+1)) 3 / k = 0
// fib_tail' 1 1 3 / k = 0
// fib_tail' 1 2 2 / k = 1
// fib_tail' 2 3 1 / k = 2 => fib_tail' (fib 2) (fib 3) 1 = fib 3
// fib_tail' 3 5 0 / k = 3 => fib_tail' (fib 3) (fib 4) 0 = fib 3

// fib_tail' (fib k) (fib (k+1)) n == (fib n+k)
// HI: fib_tail' (fib k) (fib (k+1)) (n-1) == (fib n-1+k)

// fib_tail n
// ==
// fib_tail' (fib 0) (fib 1) n
// ==
// fib_tail' 1 2 (n - 1)
// ==
// fib_tail' (fib 1) (fib 0 + fib 1) (n - 1)
// ==
// Lemma
// ==
// fib n-1+1
// ==
// fib n