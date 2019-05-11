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
    Tot (o:heap{is_minHeap o /\ (forall m. in_heap m o <==> (in_heap m h \/ m = n))}) (decreases h)
let rec insertMinHeap n h =
  match h with 
  | Leaf -> Node n Leaf Leaf
  | Node m h1 h2 -> if m = n then h else 
                    (if m < n then Node m (insertMinHeap n h2) h1 
                    else Node n (insertMinHeap m h2) h1)

(* doesn't work*)
(**)
(*val siftDown: n:nat -> l:heap{is_minHeap l /\ ~(in_heap n l)} -> r:heap{is_minHeap r /\ ~(in_heap n r)}  -> 
    Tot (o:heap{is_minHeap o}) (decreases ((size l)+(size r)))*)
//val siftDown: n:nat -> l:heap -> r:heap  -> Tot (o:heap) (decreases ((size l)+(size r)))
val siftDown: n:nat -> l:heap{is_minHeap l} -> r:heap{is_minHeap r}  -> Tot (o:heap{is_minHeap o}) (decreases ((size l)+(size r)))
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
///////
val siftDown_lemma: n:nat -> l:heap{is_minHeap l} -> r:heap{is_minHeap r}  -> 
    Lemma (ensures
      ((heapVal l = 0) ==> is_minHeap (Node n Leaf Leaf))
      \/ ( ~(heapVal l = 0) /\ (heapVal r = 0) /\ n  <= (heapVal l)  ==> is_minHeap (Node n l Leaf))
      \/ ( ~(heapVal l = 0) /\ (heapVal r = 0) /\  n > (heapVal l)  ==> is_minHeap (Node (heapVal l) (Node n Leaf Leaf) Leaf) )
      \/ (~(heapVal r = 0) /\ ~(heapVal l = 0) /\ (heapVal l) > n /\ (heapVal r) > n ==> is_minHeap (Node n l r))
      \/ (~(heapVal r = 0) /\ ~(heapVal l = 0) /\ (heapVal l) <= n /\ (heapVal l) <= (heapVal r) ==> is_minHeap (Node (heapVal l) (siftDown n (heapLeft l) (heapRight l)) r) )
      \/ (~(heapVal r = 0) /\ ~(heapVal l = 0) /\ (heapVal r) < n /\ (heapVal r) < (heapVal l) ==> is_minHeap (Node (heapVal r) l (siftDown n (heapLeft r) (heapRight r) ) ) )
      ) [SMTPat (siftDown n l r)]
let rec siftDown_lemma n l r = 
  match l with 
  | Leaf -> ()
  | Node m1 m1l m1r ->
    match r with
    | Leaf -> 
        if n <= m1 then ()
        else ()
    | Node m2 m2l m2r -> 
        if n <= m1 && n <= m2 then (assert(is_minHeap (Node n l r))) 
        else if m1 <= n && m1 <= m2 then (assert(is_minHeap m1r); assert(is_minHeap m1l); (siftDown_lemma m1 (siftDown n m1l m1r) r) )
        else (assert(is_minHeap m2r); assert(is_minHeap m2l);  (siftDown_lemma m2 l (siftDown n m2l m2r)) )

(*
val leftRem: h:heap{is_minHeap h} -> Tot (n:nat * o:heap{is_minHeap o})*)
val leftRem: h:heap -> Tot (n:nat * o:heap)
let rec leftRem h = 
    match h with
        | Leaf -> (0,Leaf) 
        | Node m Leaf Leaf -> (m, Leaf)
        | Node m l r -> 
          match (leftRem l) with
          | (m1, l2) -> (m1, Node m r l2)

(*val deleteMin: h:heap{is_minHeap h} -> Tot (o:heap{is_minHeap h})*)
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

(*val printAndDelete: h:heap -> ML unit*)
val printAndDelete: h:heap{is_minHeap h} -> ML unit
let rec printAndDelete h =
  match h with 
  | Leaf -> ()
  | Node _ _ _ ->
  let v1 = peek h in
  FStar.IO.print_string ("Min " ^ string_of_int(v1) ^ "\n"); 
  match (deleteMin h) with 
  | Leaf -> ()
  | Node x Leaf Leaf ->  FStar.IO.print_string ("Min " ^ string_of_int(x) ^ "\n")
  | Node _ _ _ ->  printAndDelete( (deleteMin h) ) 

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
