module Steel.Kont

open Steel.Effect
open Steel.Memory
module L = Steel.SpinLock
open Steel.Permissions
open FStar.Ghost
open Steel.Reference
open Steel.SteelT.Basics
open Steel.Primitive.ForkJoin

module U = FStar.Universe


//assume val sorry : #a:Type -> #p:_ -> #q:_ -> unit -> SteelT a p q

let ret #a (x:a) : SteelT a emp (fun _ -> emp) =
  Steel?.reflect (returnc _ x (fun _ -> emp)) // expected that I need to do this instead of just `x`?

(* Continuations into unit, but parametrized by the final heap
 * proposition and with an implicit framing. I think ideally these would
 * also be parametric in the final type (instead of being hardcoded to
 * unit) but that means fork needs to be extended to be polymorphic in
 * at least one of the branches. *)
type steelK (t:Type) (pre : hprop) (post:post_t t) =
  #frame:(hprop) -> #postf:hprop ->
  (x:t -> SteelT unit (frame `star` post x) (fun _ -> postf)) ->
  SteelT unit (frame `star` pre) (fun _ -> postf)

(* The classic continuation monad *)
let return #a (x:a) : steelK a emp (fun _ -> emp) =
  fun k -> k x

let bind #a #b #pre #post #post'
  (m : steelK a pre post)
  (f : (x:a -> steelK b (post x) post'))
  : steelK b pre post'
 = fun k -> m (fun x -> f x k)

(* Identity cont with frame, to eliminate a steelK *)
let idk #frame #a (x:a) : SteelT a frame (fun x -> frame) =
  Steel?.reflect (returnc _ x (fun _ -> frame))

(* Helper. Needed because of #1948 mostly *)
let change_pre #a #pre1 #pre2 #post
               (f : unit -> SteelT a pre1 post)
               (_ : squash (pre1 == pre2)) :
               (unit -> SteelT a pre2 post) = f

val kfork : #p:hprop -> #q:hprop -> (unit -> steelK unit p (fun _ -> q)) -> steelK (thread q) p (fun _ -> emp)
let kfork (#p:hprop) (#q:hprop) (f : unit -> steelK unit p (fun _ -> q))
: steelK (thread q) p (fun _ -> emp)
=
  assume (forall p. emp `star` p == p);
  assume (forall p. p `star` emp == p);
  fun (#frame:hprop) (#postf:hprop)
    (k : (x:(thread q) -> SteelT unit (frame `star` emp) (fun _ -> postf))) ->
    let t1 () : SteelT unit p (fun _ -> q) =
      let k : (unit -> SteelT unit q (fun _ -> q)) = fun () -> idk #q () in
      f () #emp #q k
    in
    let t2 (t:thread q) () : SteelT unit frame (fun _ -> postf) = k t in
    let ff () : SteelT unit (p `star` frame) (fun _ -> postf)
              = fork #p #q #frame #postf t1 t2
    in
    assume (star p frame == star frame p);
    let ff2 : unit -> SteelT unit (star frame p) (fun _ -> postf) = change_pre ff () in
    ff2 ()

(* just a flip of the usual frame *)
assume val frame' : #a:_ -> #pre:_ -> #post:_ ->
                    (f: unit -> SteelT a pre post) ->
                    (frame : hprop) ->
                    SteelT a (frame `star` pre) (fun x -> frame `star` (post x))

let kjoin #p (t : thread p) : steelK unit emp (fun _ -> p) =
 fun #f k -> frame' (fun () -> join t) f; k ()

val kframe : #a:Type -> #p:hprop -> #q:(post_t a) ->
             (f : hprop) ->
             steelK a p q ->
             steelK a (f `star` p) (fun x -> f `star` q x)

let kframe #a #p #q (f : hprop) (c : steelK a p q)
  : steelK a (f `star` p) (fun x -> f `star` q x)
  = fun #f0 #postf
      (k : (x:a -> SteelT unit (f0 `star` (f `star` q x)) (fun _ -> postf))) ->
      assume (f0 `star` (f `star` p) == (f0 `star` f) `star` p);
      assume (forall x. f0 `star` (f `star` q x) == (f0 `star` f) `star` q x);
      let k' (x:a) : SteelT unit ((f0 `star` f) `star` q x) (fun _ -> postf) =
          change_pre (fun () -> k x) () ()
      in
      let cc0 () : SteelT unit ((f0 `star` f) `star` p) (fun _ -> postf) =
        c #(f0 `star` f) #postf k'
      in
      let cc () : SteelT unit (f0 `star` (f `star` p)) (fun _ -> postf) =
        change_pre cc0 () ()
      in
      cc ()

let cancel #p #q (c : steelK unit (p `star` emp) q) : steelK unit p q =
  assume (p `star` emp == p);
  c

assume val q : int -> hprop
assume val f : unit -> steelK unit emp (fun _ -> emp)
assume val g : i:int -> steelK unit emp (fun _ -> q i)
assume val h : unit -> steelK unit emp (fun _ -> emp)

let example () : steelK unit emp (fun _ -> q 1 `star` q 2) =
  assume (forall h. star h emp == h /\ star emp h == h);
  let spawn2 (f : (x:int -> steelK unit emp (fun _ -> q x))) : steelK (thread (q 1) & thread (q 2)) emp (fun _ -> emp) =
    pid1 <-- kfork (fun () -> f 1);
    pid2 <-- kfork (fun () -> f 2);
    return (pid1, pid2)
  in
  f ();;
  p1p2 <-- spawn2 g;
  let (p1,p2) = p1p2 in
  kjoin p1;;
  kframe (q 1) begin
    kjoin p2;;
    kframe (q 2) begin
      return ()
    end
  end
