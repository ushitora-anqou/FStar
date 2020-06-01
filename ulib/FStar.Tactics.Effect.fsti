(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.Effect

open FStar.Reflection.Types
open FStar.Tactics.Types
open FStar.Tactics.Result

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

private
let __tac_wp a = proofstate -> (__result a -> Tot Type0) -> Tot Type0

private
let __tac (a:Type) (wp:__tac_wp a) = ps0:proofstate -> DIV (__result a) (wp ps0)

private
let __ret (a:Type) (x:a)
  : __tac a (fun ps0 p -> p (Success x ps0))
  = fun ps0 -> Success x ps0

private
unfold let __g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed e q -> post (Failed e q))

private
unfold let __g_compact (a:Type) (wp:__tac_wp a) : __tac_wp a =
    fun ps post -> forall k. (forall (r:__result a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp ps k

private
unfold let __bind_wp (r:range) (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) =
    __g_compact b (__g_bind a b wp f)


#push-options "--admit_smt_queries true"
(* monadic bind *)
private
let __bind (a:Type) (b:Type)
           (wp1:__tac_wp a) (wp2 : a -> __tac_wp b)
           (t1:__tac a wp1) (t2: (x:a -> __tac b (wp2 x)))
  : __tac b (__bind_wp range_0 _ _ wp1 wp2)
  = fun ps ->
        //let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
        let ps = incr_depth ps in
        let r = t1 ps in
        match r with
        | Success a ps' ->
            //let ps' = set_proofstate_range ps' (FStar.Range.prims_to_fstar_range r2) in
            // Force evaluation of __tracepoint q even on the interpreter
            begin match tracepoint ps' with
            | () -> t2 a (decr_depth ps')
            end
        | Failed e ps' -> Failed e ps'
#pop-options

private
let __subcomp (a:Type) (wp1 wp2 : __tac_wp a) (tau : __tac a wp1)
  : Pure (__tac a wp2)
         (requires (forall ps0 p. wp2 ps0 p ==> wp1 ps0 p))
         (ensures (fun _ -> True))
  = tau

private
let __if_then_else (a:Type) (wp1 wp2 : __tac_wp a)
                   (f : __tac a wp1) (g : __tac a wp2)
                   (q:Type0)
  : Type
  = __tac a ((* __g_compact a  *)(fun ps0 p -> (q ==> wp1 ps0 p) /\ ((~q) ==> wp2 ps0 p)))

(* Actions *)
private
let __get ()
  : __tac proofstate (fun ps0 p -> p (Success ps0 ps0))
  = fun s0 -> Success s0 s0

private
let __raise (a:Type0) (e:exn) // GM: FIXME: needed to force type0
  : __tac a (fun ps0 p -> p (Failed e ps0))
  = fun (ps:proofstate) -> Failed #a e ps

layered_effect {
  TAC : (a:Type) -> (wp:__tac_wp a) -> Effect
  with repr         = __tac
     ; bind         = __bind
     ; return       = __ret
     ; subcomp      = __subcomp
     ; if_then_else = __if_then_else
     ; __get        = __get
     ; __raise      = __raise
}

private
let monotonic #a (wp : pure_wp a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

private
unfold
let __lift_pure_wp #a (wp : pure_wp a) : __tac_wp a =
  fun ps0 p -> wp (fun x -> p (Success x ps0))

let lift_pure_tac (a:Type) (wp:pure_wp a{monotonic wp}) (f : unit -> PURE a wp)
  : Tot (__tac a (__lift_pure_wp wp))
  = fun ps -> Success (f ()) ps

sub_effect PURE ~> TAC = lift_pure_tac

private
unfold
let lift_div_tac (a:Type) (wp:pure_wp a{monotonic wp}) (f : unit -> DIV a wp)
  : Tot (__tac a (__lift_pure_wp wp))
  = fun ps -> Success (f ()) ps

sub_effect DIV ~> TAC = lift_div_tac

(* Hoare variant *)
effect TacH (a:Type) (pre : proofstate -> Tot Type0) (post : proofstate -> __result a -> Tot Type0) =
    TAC a (fun ps post' -> pre ps /\ (forall r. post ps r ==> post' r))

(* "Total" variant *)
effect Tac (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ _ -> True))

(* Metaprograms that succeed *)
effect TacS (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ps r -> Success? r))

(* A variant that doesn't prove totality (nor type safety!) *)
effect TacF (a:Type) = TacH a (requires (fun _ -> False)) (ensures (fun _ _ -> True))


let get ()
  : TAC proofstate (fun ps0 p -> p (Success ps0 ps0))
  = TAC?.__get ()
  
let raise (#a:Type) (e:exn) 
  : TAC a (fun ps0 p -> p (Failed e ps0))
  = TAC?.__raise a e

val with_tactic (t : unit -> Tac unit) (p:Type u#a) : Type u#a

// This will run the tactic in order to (try to) produce a term of type t
// It should not lead to any inconsistency, as any time this term appears
// during typechecking, it is forced to be fully applied and the tactic
// is run. A failure of the tactic is a typechecking failure.
val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

val assert_by_tactic (p:Type) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t (squash p)) (range_of t)))
         (ensures (fun _ -> p))

(* We don't peel off all `with_tactic`s in negative positions, so give the SMT a way to reason about them *)
val by_tactic_seman : tau:(unit -> Tac unit) -> phi:Type -> Lemma (with_tactic tau phi ==> phi)
                                                                  [SMTPat (with_tactic tau phi)]

(* One can always bypass the well-formedness of metaprograms. It does not matter
 * as they are only run at typechecking time, and if they get stuck, the compiler
 * will simply raise an error. *)
let assume_safe (#a:Type) (tau:unit -> TacF a) : Tac a = admit (); tau ()

private let tac a b = a -> Tac b
private let tactic a = tac unit a

(* A hook to preprocess a definition before it is typechecked and elaborated. This
 * attribute should be used for top-level lets. The tactic [tau] will be called
 * on a quoting of the definition of the let (if many, once for each) and the result
 * of the tactic will replace the definition. There are no goals involved,
 * nor any proof obligation to be done by the tactic. *)
val preprocess_with (tau : term -> Tac term) : Tot unit

(* A hook to postprocess a definition, after typechecking, and rewrite it
 * into a (provably equal) shape chosen by the user. This can be used to implement
 * custom transformations previous to extraction, such as selective inlining.
 * When ran added to a definition [let x = E], the [tau] metaprogram
 * is presented with a goal of the shape [E = ?u] for a fresh uvar [?u].
 * The metaprogram should then both instantiate [?u] and prove the equivalence
 * to [E]. *)
val postprocess_with (tau : unit -> Tac unit) : Tot unit

(* Similar semantics to [postprocess_with], but the metaprogram only runs before
 * extraction, and hence typechecking and the logical environment should not be
 * affected at all. *)
val postprocess_for_extraction_with (tau : unit -> Tac unit) : Tot unit

#set-options "--no_tactics"

val unfold_with_tactic (t:unit -> Tac unit) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))
