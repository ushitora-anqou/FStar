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

module Steel.Channel.Simplex

open Steel.SpinLock
open Steel.HigherReference
open Steel.Memory.Tactics

let sprot = p:prot { more p }

noeq
type chan_val = {
  chan_prot : sprot;
  chan_msg  : msg_t chan_prot;
  chan_ctr  : nat
}

let trace_ref (p:prot) = reference (partial_trace_of p) extended_to

noeq
type chan_t (p:prot) = {
  send: ref chan_val;
  recv: ref chan_val;
  trace: trace_ref p;
}

let half : perm u#1 = half_perm full

let step (s:sprot) (x:msg_t s) = step s x

let chan_inv_step_p (vrecv vsend:chan_val) : prop =
  (vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg /\
   vsend.chan_ctr == vrecv.chan_ctr + 1)

let chan_inv_step (vrecv vsend:chan_val) =
  pure (chan_inv_step_p vrecv vsend)

let chan_inv_cond (vsend:chan_val) (vrecv:chan_val) =
    if vsend.chan_ctr = vrecv.chan_ctr
    then pure (vsend == vrecv)
    else chan_inv_step vrecv vsend

let trace_until #p (r:trace_ref p) (vr:chan_val) =
  h_exists (fun (tr:partial_trace_of p) ->
                   pts_to_ref r full tr `star`
                   pure (until tr == step vr.chan_prot vr.chan_msg))

let chan_inv_recv #p (c:chan_t p) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star`
      trace_until c.trace vrecv `star`
      chan_inv_cond vsend vrecv)

let chan_inv #p (c:chan_t p) : hprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

assume val h_admit (#a:Type) (#p:hprop) (q:a -> hprop) : SteelT a p q

noeq
type chan p = {
  chan_chan : chan_t p;
  chan_lock : lock (chan_inv chan_chan)
}

let in_state_prop (p:prot) (vsend:chan_val) : prop =
  p == step vsend.chan_prot vsend.chan_msg

let in_state_hprop (p:prot) (vsend:chan_val) : hprop = pure (in_state_prop p vsend)

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pts_to r half vsend `star` in_state_hprop p vsend)

let sender #q (c:chan q) (p:prot) = in_state c.chan_chan.send p
let receiver #q (c:chan q) (p:prot) = in_state c.chan_chan.recv p

let msg t p = Msg unit (fun _ -> p)
let init_chan_val (p:prot) = v:chan_val {v.chan_prot == msg unit p}

open Steel.Permissions


#set-options "--print_implicits --print_universes --print_effect_args --print_bound_var_types"
#set-options "--print_effect_args --print_full_names"

let new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)
  = let q = msg unit p in
    let v : chan_val = { chan_prot = q; chan_msg = (); chan_ctr = 0 } in
    let vp : init_chan_val p = v in
    let send = steel_frame_t (fun _ -> alloc v) in
    let recv = steel_frame_t #(pts_to send full v `star` emp) #_ #_ #_ (fun _ -> alloc #_ v) in
    (* let recv = steel_frame_t #(pts_to send full v `star` emp) #_ #_ #_ #(_ by (resolve_frame ())) (fun _ -> alloc #_ v) in *)
    h_admit (fun c -> sender c p `star` receiver c p)
