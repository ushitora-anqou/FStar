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

(* TODO: I am awful, please split me up *)
let witness_h_exists (#a:Type) (#opened:_) (#p:(a -> slprop){is_frame_monotonic p}) ()
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
    let tp, n = tpn in
    assert (interp (h_exists p `star` locks_invariant opened m0) m0);
    let (ml, mr) = id_elim_star (h_exists p) (locks_invariant opened m0) m0 in
    assert (interp (h_exists p) ml);
    assert (interp (locks_invariant opened m0) mr);
    let x = id_elim_exists p ml in
    assert (interp (p x) ml);
    assert (interp (p x) m0);
    assert (interp (p x) ml /\ interp (locks_invariant opened m0) mr);
    assert (forall y frame. interp (p y `star` frame) ml ==> interp (p x `star` frame) ml);
    let sub (frame:slprop)
      : Lemma (requires (interp ((h_exists p `star` frame)) m0))
              (ensures  (interp ((p x        `star` frame)) m0))
      =
         let (m1, m2) = id_elim_star (h_exists p) frame m0 in
         let y = id_elim_exists p m1 in
         assert (interp (p y) m1);
         intro_star (p y) frame m1 m2;
         ()
    in
    Classical.forall_intro (Classical.move_requires sub);
    let frameinv (frame:slprop) :
      Lemma (requires (interp ((h_exists p `star` frame) `star` locks_invariant opened m0) m0))
            (ensures  (interp ((p x        `star` frame) `star` locks_invariant opened m0) m0))
      =
      star_associative (h_exists p) frame (locks_invariant opened m0);
      sub (frame `star` locks_invariant opened m0);
      star_associative (p x) frame (locks_invariant opened m0);
      ()
    in
    Classical.forall_intro (Classical.move_requires frameinv);
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
