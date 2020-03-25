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
open Steel.Channel.Protocol
open Steel.Effect
open Steel.Memory

/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
///
/// DoWhile (Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret bool)))
let prot : Type u#1 = protocol unit

val chan (p:prot) : Type0

val sender (#p:prot) (c:chan p) (next_action:prot) : hprop u#1

val receiver (#p:prot) (c:chan p) (next_action:prot) : hprop u#1

val new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)
