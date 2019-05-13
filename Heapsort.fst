module Heapsort
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

val lte : nat -> nat -> Tot bool
let lte n1 n2 = n1 <= n2

val is_heap : heap -> (nat -> nat -> Tot bool) -> Tot bool
let rec is_heap h c =
  match h with
  | Leaf -> true
  | Node n h1 h2 -> all (c n) h1 && all (c n) h2 && is_heap h1 c && is_heap h2 c
  
val is_minHeap : heap -> Tot bool
let rec is_minHeap h = is_heap h lte


val heapLeft: h:heap{is_minHeap h} -> l:heap{is_minHeap l}
let heapLeft h =
  match h with 
  | Leaf -> Leaf
  | Node m l r -> l

val heapRight: h:heap{is_minHeap h} -> r:heap{is_minHeap r}
let heapRight h =
  match h with 
  | Leaf -> Leaf
  | Node m l r -> r

val heapVal: h:heap{is_minHeap h} -> n:nat
let heapVal h =
  match h with 
  | Leaf -> 0
  | Node m l r -> m

val insertMinHeap : n:nat -> h:heap{is_minHeap h} -> 
      Tot (o:heap{is_minHeap o /\ (forall m. in_heap m o <==> (in_heap m h \/ m = n))}) 
        (decreases h)
let rec insertMinHeap n h =
  match h with 
  | Leaf -> Node n Leaf Leaf
  | Node m h1 h2 -> if m = n then h else 
                    (if m < n then Node m (insertMinHeap n h2) h1 
                    else Node n (insertMinHeap m h2) h1)

val siftDown: n:nat -> l:heap{is_minHeap l} -> r:heap{is_minHeap r} -> 
      Tot (o:heap{ is_minHeap o /\ (forall x. in_heap x o ==> (x = n) \/ (in_heap x l) \/ (in_heap x r)) }) 
        (decreases ((size l)+(size r)))
let rec siftDown n l r = 
  match l with 
  | Leaf -> Node n Leaf Leaf
  | Node m1 m1l m1r ->
    match r with
    | Leaf -> 
        if n <= m1 then (Node n l Leaf)
        else (Node m1 (Node n Leaf Leaf) Leaf)
    | Node m2 m2l m2r -> 
        if n <= m1 && n <= m2 then Node n l r
        else if m1 <= n && m1 <= m2 then (Node m1 (siftDown n m1l m1r) r)
        else (Node m2 l (siftDown n m2l m2r) )

val leftRem: h:heap{is_minHeap h} -> 
                Tot (n:nat * o:heap{is_minHeap o /\ (forall x. in_heap x o ==> in_heap x h)})
let rec leftRem h = 
    match h with
        | Leaf -> (0,Leaf) 
        | Node m Leaf Leaf -> (m, Leaf)
        | Node m l r -> 
          match (leftRem l) with
          | (m1, l2) -> (m1, Node m r l2)
val peekMin : h:heap{is_minHeap h} -> Tot (n:nat{ forall m. (in_heap m h ==> n <= m) } )
let peekMin h =
  match h with 
  | Leaf -> 0
  | Node n _ _ -> n

val deleteMin: h:heap{is_minHeap h} -> 
                Tot (o:heap{is_minHeap o})
                (decreases (size h))
let deleteMin h = 
        match h with
        | Leaf -> Leaf
        | Node m l r -> 
          match leftRem l with 
          | (m1, l2) -> siftDown m1 r l2



val peek : h:heap -> Tot (n:nat)
let peek h =
  match h with 
  | Leaf -> 0
  | Node n _ _ -> n

(*val printAndDelete: h:heap -> ML unit*)
val printAndDelete: h:heap{is_minHeap h} -> ML unit
let rec printAndDelete h =
  match h with 
  | Leaf -> ()
  | Node _ _ _ ->
  let v1 = peekMin h in
  FStar.IO.print_string ("Min " ^ string_of_int(v1) ^ "\n"); 
  match (deleteMin h) with 
  | Leaf -> ()
  | Node x Leaf Leaf ->  FStar.IO.print_string ("Min " ^ string_of_int(x) ^ "\n")
  | Node _ _ _ ->  printAndDelete( (deleteMin h) ) 

(* Doesn't work... Need to show that the heap gets smaller
val heapsort: h:heap{is_minHeap h} -> Tot (n:(list nat)) (decreases (size h))
let rec heapsort h =
  match h with 
  | Leaf -> []
  | Node _ _ _ ->
  let n = peekMin h in
  let h1 = deleteMin h in
  match h1 with 
  | Leaf -> []
  | Node x Leaf Leaf -> n::x::[]
  | Node _ _ _ -> n::(heapsort h1)
*)
val checking : unit -> ML unit
let checking () =
  let h1 = insertMinHeap 3 Leaf in
  let h2 = insertMinHeap 5 h1 in 
  let h3 = insertMinHeap 9 h2 in 
  let h4 = insertMinHeap 7 h3 in 
  let h5 = insertMinHeap 2 h4 in 
  let h6 = insertMinHeap 1 h5 in 
  let h7 = insertMinHeap 4 h6 in 
  let h8 = insertMinHeap 10 h7 in 
  let h9 = insertMinHeap 6 h8 in 
  let h10 = insertMinHeap 8 h9 in 
  printAndDelete h10
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
