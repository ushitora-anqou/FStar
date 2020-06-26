(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.Effect.Atomic
open FStar.PCM
open Steel.Memory

let observability = bool

#push-options "--query_stats" //crappy workaround
let has_eq_observability () = ()
#pop-options
let observable = true
let unobservable = false

let atomic_repr a opened_invariants f pre post =
    action_except a opened_invariants pre post

let return a x o p = fun _ -> x

let bind a b o o1 o2 pre_f post_f post_g f g =
  fun m0 ->
    let x = f () in
    g x ()

let subcomp a op o pre post f = f

inline_for_extraction
let lift_pure_steel_atomic a op p wp f
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ -> let x = f () in x

let lift_atomic_to_steelT f = Steel.Effect.add_action (reify (f()))
let as_atomic_action f = SteelAtomic?.reflect f
let new_invariant i p = SteelAtomic?.reflect (Steel.Memory.new_invariant i p)
let with_invariant i f = SteelAtomic?.reflect (Steel.Memory.with_invariant i (reify (f())))
let frame frame f = SteelAtomic?.reflect (Steel.Memory.frame frame (reify (f ())))
let change_slprop p q proof = SteelAtomic?.reflect (Steel.Memory.change_slprop p q proof)

open NMSTTotal
open MSTTotal

let not_affine (p : slprop) = forall m1 m2. interp p m1 ==> interp p m2 ==> m1 == m2

val intro_star_pat (p q:slprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires disjoint mp mq)
    (ensures interp (p `star` q) (join mp mq))
    [SMTPat (interp (p `star` q) (join mp mq))]
let intro_star_pat = intro_star

val elim_star_pat (p q:slprop) (m:hmem (p `star` q))
  : Lemma
    (requires
      interp (p `star` q) m)
    (ensures exists ml mr.
      disjoint ml mr /\ m == join ml mr /\ interp p ml /\ interp q mr)
    [SMTPat (interp (p `star` q) m)]
let elim_star_pat = elim_star

let witness_h_exists (#a:Type) (#opened:_) (#p:a -> slprop) (_:unit)
  : SteelAtomic (Ghost.erased a) opened unobservable
                (h_exists p) (fun x -> p x)
  =
  SteelAtomic?.reflect begin
  let pre m0 =
    inames_ok opened m0
    /\ interp (h_exists p `star` locks_invariant opened m0) m0
  in
  let post m0 (x:Ghost.erased a) m1 =
    inames_ok opened m1
    /\ interp (p x `star` locks_invariant opened m1) m1
    /\ preserves_frame opened (h_exists p) (p x) m0 m1
  in
  let postn m0 (xn:(Ghost.erased a & nat)) m1 =
    post m0 (fst xn) m1
  in
  let body7 (tpn:tape&nat) (m0:mem) : PURE ((Ghost.erased a & nat) & mem)
                                         (fun p -> pre m0 /\
                                                (forall (x:(Ghost.erased a & nat)) (m1:mem).
                                                  postn m0 x m1 /\ mem_evolves m0 m1 ==> p (x,m1)))
  =



//let star (p1 p2: slprop u#a) : slprop u#a =
//  fun (h: heap) -> exists (h1 h2 : heap).
//        h1 `disjoint` h2 /\
//        h == join h1 h2 /\
//        interp p1 h1 /\
//        interp p2 h2

    let tp, n = tpn in
    assert (interp (h_exists p `star` locks_invariant opened m0) m0);
    let starprop (ml mr : mem) = ml `disjoint` mr /\
                         m0 == join ml mr /\
                         interp (h_exists p) ml /\
                         interp (locks_invariant opened m0) mr
    in
    elim_star (h_exists p) (locks_invariant opened m0) m0;
    let starprop1 ml : prop = exists mr. starprop ml mr in // this prop annotation seems needed
    let ml : Ghost.erased mem = FStar.IndefiniteDescription.indefinite_description_tot mem starprop1 in
    assert (starprop1 ml);
    let starpropml mr : prop = starprop ml mr in
    assert (exists mr. starpropml mr);
    let mr : Ghost.erased mem = FStar.IndefiniteDescription.indefinite_description_tot mem starpropml in
    assert (interp (h_exists p) ml /\ interp (locks_invariant opened m0) mr);
    assert (interp (h_exists p) ml);
    Steel.Memory.elim_h_exists p ml;
    assert (exists x. interp (p x) ml);
    let x = FStar.IndefiniteDescription.indefinite_description_tot a (fun x -> interp (p x) ml) in
    assert (interp (p x) ml);
    assert (interp (p x) ml /\ interp (locks_invariant opened m0) mr);
    Steel.Memory.intro_star (p x) (locks_invariant opened m0) ml mr;
    // COULD THIS HELP?
    assume (forall x y m. interp (p x) m /\ interp (p y) m ==> x == y);
    let key0 (m :mem) : Lemma (requires interp (h_exists p) m)
                              (ensures (interp (p x) m)) =
        Steel.Memory.elim_h_exists p m;
        assert (exists y. interp (p y) m);
        let y = FStar.IndefiniteDescription.indefinite_description_tot a
                 (fun y -> interp (p y) m) in
        assert (interp (p y) m);
        assume (interp (p x) m);
        ()
    in
    let key () : Lemma (forall m. interp (h_exists p) m ==> interp (p x) m) =
      Classical.forall_intro (Classical.move_requires key0)
    in
    admit ();
    key ();
    let sub (frame:slprop)
      : Lemma (requires (interp ((h_exists p `star` frame) `star` locks_invariant opened m0) m0))
              (ensures  (interp ((p x        `star` frame) `star` locks_invariant opened m0) m0))
      =
           elim_star (h_exists p `star` frame) (locks_invariant opened m0) m0;
           admit ()
    in
    Classical.forall_intro (Classical.move_requires sub);
    assert (forall frame.
             (interp ((h_exists p `star` frame) `star` locks_invariant opened m0) m0)
             ==>
             (interp ((p x `star` frame) `star` locks_invariant opened m0)) m0);
    assert (preserves_frame opened (h_exists p) (p x) m0 m0);
    assert (interp (p x `star` locks_invariant opened m0) m0);
    ((x, n), m0)
  in
  let body8 (tpn:tape&nat) : MSTATETOT (Ghost.erased a & nat) mem mem_evolves
                                (requires pre)
                                (ensures postn)
  =
     MSTATETOT?.reflect (body7 tpn)
  in
  let body9 : NMSTTotal.repr (Ghost.erased a)
                                mem mem_evolves
                                (requires pre)
                                (ensures post)
  =
      body8
  in
  let body10 () : MstTot (Ghost.erased a) opened (h_exists p) (fun x -> p x) =
    NMSTATETOT?.reflect body9
  in
  let act : atomic_repr (Ghost.erased a) opened unobservable (h_exists p) (fun x -> p x) =
    body10
  in
  act
  end

let lift_h_exists_atomic #a #u p = SteelAtomic?.reflect (Steel.Memory.lift_h_exists #u p)
let elim_pure #uses p = SteelAtomic?.reflect (Steel.Memory.elim_pure #uses p)
