module Heapsort
open FStar.Exn
open FStar.All

type heap =
  | Leaf : heap
  | Node : n:nat -> heap -> heap -> heap

val size : heap -> Tot nat
let rec size h =
  match h with
  | Leaf -> 0
  | Node n h1 h2 -> 1 + size h1 + size h2

val in_heap : nat -> heap -> Tot bool
let rec in_heap x h =
  match h with
  | Leaf -> false
  | Node n h1 h2 -> x = n || in_heap x h1 || in_heap x h2


val all : p:(nat -> Tot bool) -> h:heap ->
            Tot (r:bool{r <==> (forall x. in_heap x h ==> p x)})
let rec all p h =
  match h with
  | Leaf -> true
  | Node n h1 h2 -> p n && all p h1 && all p h2

val lt : nat -> nat -> Tot bool
let lt n1 n2 = n1 < n2

val gt : nat -> nat -> Tot bool
let gt n1 n2 = n1 > n2


val is_heap : heap -> (nat -> nat -> Tot bool) -> Tot bool
let rec is_heap h c =
  match h with
  | Leaf -> true
  | Node n h1 h2 -> all (c n) h1 && all (c n) h2 && is_heap h1 c && is_heap h2 c
  
val is_minHeap : heap -> Tot bool
let rec is_minHeap h = is_heap h lt

val insertMinHeap : n:nat -> h:heap{is_minHeap h} -> 
    Tot (o:heap{is_minHeap o /\ (forall m. in_heap m o <==> (in_heap m h \/ m = n))}) (decreases h)
let rec insertMinHeap n h =
  match h with 
  | Leaf -> Node n Leaf Leaf
  | Node m h1 h2 -> if m = n then h else 
                    (if m < n then Node m (insertMinHeap n h2) h1 
                    else Node n (insertMinHeap m h2) h1)

val siftDown: n:nat -> l:heap -> r:heap -> Tot (o:heap) (decreases ((size l)+(size r)))
let rec siftDown n l r = 
  match l with 
  | Leaf -> Node n Leaf Leaf
  | Node m1 m1l m1r ->
    match r with
    | Leaf -> 
        if n < m1 then (Node n l Leaf)
        else (Node m1 (Node n Leaf Leaf) Leaf)
    | Node m2 m2l m2r -> 
        if n < m1 && n < m2 then Node n l r
        else if m1 < m2 then Node m1 (siftDown n m1l m1r) r
        else  Node m2 l (siftDown n m2l m2r)

val leftRem: h:heap -> Tot (n:nat * o:heap)
let rec leftRem h = 
    match h with
        | Leaf -> (0,Leaf) 
        | Node m Leaf Leaf -> (m, Leaf)
        | Node m l r -> 
          match (leftRem l) with
          | (m1, l2) -> (m1, Node m r l2)


val deleteMin: h:heap -> Tot (o:heap)
let deleteMin h = 
        match h with
        | Leaf -> Leaf
        | Node m l r -> 
          match leftRem l with 
          | (m1, l2) -> siftDown m1 r l2

val peekMin : h:heap{is_minHeap h} -> Tot (n:nat{ forall m. (in_heap m h ==> n <= m) } )
let peekMin h =
  match h with 
  | Leaf -> 0
  | Node n _ _ -> n

val peek : h:heap -> Tot (n:nat)
let peek h =
  match h with 
  | Leaf -> 0
  | Node n _ _ -> n
  

val printAndDelete: h:heap -> ML unit
let rec printAndDelete h =
  match h with 
  | Leaf -> ()
  | Node _ _ _ ->
  let v1 = peek h in
  FStar.IO.print_string ("Min" ^ string_of_int(v1) ^ "\n"); 
  printAndDelete(deleteMin h) 

val checking : unit -> ML unit
let checking () =
  let h1 = insertMinHeap 3 Leaf in
  let h2 = insertMinHeap 5 h1 in 
  let h3 = insertMinHeap 9 h2 in 
  let h4 = insertMinHeap 7 h3 in 
  let h5 = insertMinHeap 2 h4 in 
  let h6 = insertMinHeap 4 h5 in 
  printAndDelete h6
  (*
  FStar.IO.print_string ("Min" ^ string_of_int(peekMin h6) ^ "\n");
  let h7 = deleteMin h6 in
  FStar.IO.print_string ("Min" ^ string_of_int(peekMin h7) ^ "\n");
  let h8 = deleteMin h7 in
  FStar.IO.print_string ("Min" ^ string_of_int(peekMin h8) ^ "\n");
  let h9 = deleteMin h8 in
  FStar.IO.print_string ("Min" ^ string_of_int(peekMin h9) ^ "\n")
*)

let main = checking()
