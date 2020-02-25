module Steel.Primitive.ForkJoin
open Steel.Effect
open Steel.Memory
module L = Steel.SpinLock
open Steel.Permissions
open FStar.Ghost
open Steel.Reference
open Steel.SteelT.Basics

let maybe_p (p:hprop) (v:bool) = if v then p else emp

let lock_inv_pred (r:ref bool) (p:hprop) (v:bool) : hprop =
  pts_to r full v `star` maybe_p p v

let lock_inv (r:ref bool) (p:hprop)
  : hprop
  = h_exists (lock_inv_pred r p)

noeq
type thread (p:hprop) = {
  r:ref bool;
  l:L.lock (lock_inv r p)
}

let intro_maybe_p_false (p:hprop)
  : SteelT unit emp (fun _ -> maybe_p p false)
  = h_assert (maybe_p p false)

let intro_maybe_p_true (p:hprop)
  : SteelT unit p (fun _ -> maybe_p p true)
  = h_assert (maybe_p p true)

let new_thread (p:hprop)
  : SteelT (thread p) emp (fun _ -> emp)
  = intro_maybe_p_false p;
    h_assert (maybe_p p false);
    h_intro_emp_l (maybe_p p false);
    let r = frame #(ref bool) #emp #(fun r -> pts_to r full false)
                  (fun () -> alloc false)
                  (maybe_p p false) in
    intro_h_exists false (lock_inv_pred r p);
    let l  = L.new_lock (lock_inv r p) in
    let t  =  { r = r ; l = l } in
    return t

let finish (#p:hprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full v `star` p) (fun _ -> emp)
  = frame (fun _ -> write t.r true) p;
    h_assert (pts_to t.r full true `star` p);
    h_commute (pts_to t.r full true) p;
    frame (fun _ -> intro_maybe_p_true p) (pts_to t.r full true);
    h_commute (maybe_p p true) (pts_to t.r full true);
    intro_h_exists true (lock_inv_pred t.r p);
    L.release t.l

let acquire (#p:hprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full b)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_affine (pts_to t.r full b) (maybe_p p b);
    return b

let spawn (#p #q:hprop)
          ($f: (unit -> SteelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelT unit p (fun _ -> emp)
  = h_intro_emp_l p;
    let b  = frame (fun () -> acquire t) p in
    h_commute (pts_to t.r full b) p;
    let _ = frame f (pts_to t.r full b) in
    h_commute q (pts_to t.r full b);
    finish t b

let fork (#a:Type) (#p #q #r #s:hprop)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)
  = h_intro_emp_l (p `star` r);
    let t : thread q = frame (fun _ -> new_thread q) (p `star` r) in
    h_assert (emp `star` (p `star` r));
    h_elim_emp_l (p `star` r);
    par (spawn f t) (g t);
    h_elim_emp_l s

let pre (#p:hprop) (t:thread p) (b:bool) : hprop = lock_inv_pred t.r p b
let post (p:hprop) (b:bool) (_:unit) : hprop = p

let join_case_true (#p:hprop) (t:thread p) (_:unit)
  : SteelT unit (pre t true) (post p true)
  = h_commute _ (maybe_p p true);
    h_assert (maybe_p p true `star` pts_to t.r full true);
    h_affine (maybe_p p true) (pts_to t.r full true);
    h_assert (maybe_p p true)

let join_case_false (#p:hprop) (t:thread p) (loop: (t:thread p -> SteelT unit emp (fun _ -> p))) (_:unit)
  : SteelT unit (pre t false) (post p false)
  = intro_h_exists false (lock_inv_pred t.r p);
    L.release t.l;
    loop t

let rec join (#p:hprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_assert (pts_to t.r full b `star` maybe_p p b);
    h_assert (pre t b);
    cond b (pre t) (post p) (join_case_true t) (join_case_false t (join #p))
    // if b
    // then (h_assert (pts_to t.r full true `star` maybe_p p true);
    //       elim_wand (pure (true==true)) p)
    // else (intro_h_exists false (lock_inv_pred t.r p); L.release t.l; join t)