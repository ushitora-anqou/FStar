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

assume val l_assoc : unit -> Lemma (forall h1 h2 h3. star (star h1 h2) h3 `equiv` star h1 (star h2 h3))
assume val l_comm : unit -> Lemma (forall h1 h2. star h1 h2 `equiv` star h2 h1)
assume val l_id : unit -> Lemma (forall h. star h emp `equiv` h /\ star emp h `equiv` h)
assume val l_frame : unit -> Lemma (forall h1 h2 h3. equiv h1 h2 ==> equiv (star h1 h3) (star h2 h3))

(* Some helpers *)
private
val reshuffle0 (#p #q : hprop)
              (_ : squash (p `equiv` q))
   : SteelT unit p (fun _ -> q)

private
let reshuffle0 #p #q peq =
  Steel.SteelAtomic.Basics.lift_atomic_to_steelT
    (fun () -> Steel.Effect.Atomic.change_hprop p q (fun m -> ()))

assume val sorry : #a:Type -> #p:_ -> #q:_ -> unit -> SteelT a p q

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
let return a (x:a) : steelK a emp (fun _ -> emp) =
  fun k -> k x

let bind a b pre post post'
  (m : steelK a pre post)
  (f : (x:a -> steelK b (post x) post'))
  : steelK b pre post'
 = fun k -> m (fun x -> f x k)
 
let himplies h1 h2 =
  forall m. interp h1 m ==> interp h2 m

(* Helper. Needed because of #1948 mostly *)
let change_pre #a #b #pre1 #pre2 #post
  (f : (x:b -> SteelT a (pre1 x) (post x)))
  : Pure (x:b -> SteelT a (pre2 x) (post x)) (requires (forall x. pre1 x `equiv` pre2 x)) (ensures (fun _ -> True))
  = fun x -> reshuffle0 (); f x

(* How does this not exist in FStar.Classical?? *)
let forall_elim #a (#p:a -> Type0) ($l : unit -> Lemma (forall x. p x)) (x:a) : Lemma (p x) = l ()
let forall_elim_2 #a #b (#p:a -> b -> Type0) ($l : unit -> Lemma (forall x y. p x y)) (x:a) (y:b) : Lemma (p x y) = l ()
let forall_elim_3 #a #b #c (#p:a -> b -> c -> Type0) ($l : unit -> Lemma (forall x y z. p x y z)) (x:a) (y:b) (z:c) : Lemma (p x y z) = l ()

(* Only deals with equivalences really *)
let subcomp (a:Type) pre1 pre2 post1 post2 (f : steelK a pre1 post1)
    : Pure (steelK a pre2 post2)
           (requires (pre2 `equiv` pre1 /\ (forall x. post1 x `equiv` post2 x)))
           (ensures (fun _ -> True)) =
  fun #frame #postf (k : (x:a -> SteelT unit (frame `star` (post2 x)) (fun _ -> postf))) ->
  forall_elim_3 l_frame pre1 pre2 frame;
  forall_elim_2 l_comm pre1 frame;
  forall_elim_2 l_comm pre2 frame;
  let aux (x:a) : Lemma ((frame `star` post1 x) `equiv` (frame `star` post2 x)) =
    forall_elim_3 l_frame (post1 x) (post2 x) frame;
    forall_elim_2 l_comm (post1 x) frame;
    forall_elim_2 l_comm (post2 x) frame
  in
  FStar.Classical.forall_intro aux;
  change_pre (f #frame #postf) (change_pre k)

let refine_mprop_const #fp (phi:prop) : refine_mprop fp =
  fun _ -> phi

let if_then_else (a:Type u#aa) pre1 pre2 post1 post2
                 (f : steelK a pre1 post1)
                 (g : steelK a pre2 post2)
                 (p:Type0) : Type =
  let p : prop = squash p in
  let rp = refine_mprop_const p in
  let rnp = refine_mprop_const (~p) in
  steelK a ((refine pre1 rp) `h_or` (refine pre2 rnp))
           (fun x -> ((refine (post1 x) rp) `h_or` (refine (post2 x) rnp)))

#push-options "--admit_smt_queries true" // todo: revise
reifiable reflectable
layered_effect {
  SteelK : a:Type -> pre:pre_t -> post:(post_t a) -> Effect
  with
  repr = steelK;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}
#pop-options

assume val ksorry : #a:Type -> #p:_ -> #q:_ -> unit -> SteelK a p q

assume Pure_wp_monotonic:
  (forall (a:Type) (wp:pure_wp a).
     (forall p q. (forall x. p x ==> q x) ==>
             (wp p ==> wp q)))

let lift_pure_SteelK (a:Type) (wp:pure_wp a)
                     (p:hprop)
                     (f : unit -> PURE a wp)
                     : Pure (steelK a p (fun _ -> p)) (requires (wp (fun _ -> True))) (ensures (fun _ -> True))
  = (fun k -> k (f ()))

sub_effect PURE ~> SteelK = lift_pure_SteelK

(* Sanity check *)
let test_lift #p #q (f : unit -> SteelK unit p (fun _ -> q)) : SteelK unit p (fun _ -> q) =
  ();
  f ();
  ()

(* Identity cont with frame, to eliminate a SteelK *)
let idk #frame #a (x:a) : SteelT a frame (fun x -> frame) =
  Steel?.reflect (returnc _ x (fun _ -> frame))

val kfork : #p:hprop -> #q:hprop -> (unit -> SteelK unit p (fun _ -> q)) -> SteelK (thread q) p (fun _ -> emp)
let kfork (#p:hprop) (#q:hprop) (f : unit -> SteelK unit p (fun _ -> q))
: SteelK (thread q) p (fun _ -> emp)
=
  SteelK?.reflect (
  l_id ();
  fun (#frame:hprop) (#postf:hprop)
    (k : (x:(thread q) -> SteelT unit (frame `star` emp) (fun _ -> postf))) ->
    let t1 () : SteelT unit p (fun _ -> q) =
      let k : (unit -> SteelT unit q (fun _ -> q)) = fun () -> idk #q () in
      let r : steelK _ _ _ = reify (f ()) in 
      reshuffle0 ();
      r #emp #q (fun x -> reshuffle0 (); k x)
    in
    let t2 (t:thread q) () : SteelT unit frame (fun _ -> postf) = reshuffle0 (); k t in
    let ff () : SteelT unit (p `star` frame) (fun _ -> postf)
              = fork #p #q #frame #postf t1 t2
    in
    l_comm ();
    let ff2 : unit -> SteelT unit (star frame p) (fun _ -> postf) = change_pre ff in
    ff2 ())

(* just a flip of the usual frame *)
assume val frame' : #a:_ -> #pre:_ -> #post:_ ->
                    (f: unit -> SteelT a pre post) ->
                    (frame : hprop) ->
                    SteelT a (frame `star` pre) (fun x -> frame `star` (post x))

let kjoin #p (t : thread p) : SteelK unit emp (fun _ -> p) =
 SteelK?.reflect (fun #f k -> frame' (fun () -> join t) f; k ())

val kframe : #a:Type -> #p:hprop -> #q:(post_t a) ->
             (f : hprop) ->
             ($c : (unit -> SteelK a p q)) ->
             SteelK a (f `star` p) (fun x -> f `star` q x)

let kframe #a #p #q (f : hprop) ($c : (unit -> SteelK a p q))
  : SteelK a (f `star` p) (fun x -> f `star` q x)
  = SteelK?.reflect (fun #f0 #postf
      (k : (x:a -> SteelT unit (f0 `star` (f `star` q x)) (fun _ -> postf))) ->
      l_assoc ();
      l_comm (); (* blasting with AC.. seems to work fine *)
      let k' (x:a) : SteelT unit ((f0 `star` f) `star` q x) (fun _ -> postf) =
          change_pre (fun () -> k x) ()
      in
      let cc0 () : SteelT unit ((f0 `star` f) `star` p) (fun _ -> postf) =
        reify (c ()) #(f0 `star` f) #postf k'
      in
      let cc () : SteelT unit (f0 `star` (f `star` p)) (fun _ -> postf) =
        change_pre cc0 ()
      in
      cc ())

let cancel #p #q (c : steelK unit (p `star` emp) q) : steelK unit p q =
  l_id ();
  subcomp _ _ _ _ _ c

assume val q : int -> hprop
assume val f : unit -> SteelK unit emp (fun _ -> emp)
assume val g : i:int -> SteelK unit emp (fun _ -> q i)
assume val h : unit -> SteelK unit emp (fun _ -> emp)

private
val reshufflek (#p #q : hprop)
              (_ : squash (p `equiv` q))
   : SteelK unit p (fun _ -> q)

private
let reshufflek #p #q peq =
  ()
  
let example () : SteelK unit emp (fun _ -> q 1 `star` q 2) =
  let spawn2 (f : (x:int -> SteelK unit emp (fun _ -> q x))) : SteelK (thread (q 1) & thread (q 2)) emp (fun _ -> emp) =
    let pid1 = kfork (fun () -> f 1) in
    let pid2 = kfork (fun () -> f 2) in
    (pid1, pid2)
  in
  f ();
  let p1p2 = spawn2 g in
  let p1 = fst p1p2 in
  let p2 = snd p1p2 in
  kjoin p1;
  // GM: gah, I think I have to write it like this since SteelK doesn't really
  // carry any logical payload, so lifts from pure things lose their spec.
  let p : squash (equiv (q 1) (star (q 1) emp)) = forall_elim l_id (q 1) in
  reshufflek ();
  kframe (q 1) (fun () ->
    h ();
    kjoin p2
  )
