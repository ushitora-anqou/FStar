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
module FStar.Math.Lemmas

open FStar.Mul
open FStar.Math.Lib

#reset-options "--initial_fuel 0 --max_fuel 0"

(*** Addition/substraction ***)

let paren_add_left a b c = ()

let paren_add_right a b c = ()

let addition_is_associative a b c = ()

let subtraction_is_distributive a b c = ()

let swap_add_plus_minus a b c = ()



(*** Multiplication ***)

let lemma_mult_le_left a b c = ()

let lemma_mult_le_right a b c = ()

let lemma_mult_lt_left a b c = ()

let lemma_mult_lt_right a b c = ()

let lemma_mult_lt_sqr n m k = ()

let distributivity_add_left a b c = ()

let distributivity_add_right a b c = ()

let distributivity_sub_left a b c = ()

let distributivity_sub_right a b c = ()

let paren_mul_left a b c = ()

let paren_mul_right a b c = ()

let swap_mul a b = ()

let neg_mul_left a b = ()

let neg_mul_right a b = ()

let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b

let mul_binds_tighter a b c = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"
let mul_ineq1 a b c d = ()

#reset-options "--initial_fuel 0 --max_fuel 0"

let nat_times_nat_is_nat a b = ()

let pos_times_pos_is_pos a b = ()

let bounded_multiple_is_zero (x:int) (n:pos) = ()

let lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:pos) =
  assert (0 * n == 0);
  bounded_multiple_is_zero x n

let lemma_mul_sub_distr a b c = ()

let multiplication_order_lemma a b p = ()


(*** Division/Modulo ***)

let euclidean_division_definition a b = ()

let modulo_lemma a b = ()

let lemma_div_mod a p = ()

let lemma_mod_lt a p = ()

let small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a) = ()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 1"

let lemma_mod_plus_0 a b p =
  let z: int = a + b * p in
  lemma_div_mod a p;
  lemma_div_mod z p

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_mod_plus_1 a b p =
  lemma_div_mod (a+b*p) p;
  lemma_mod_lt a p;
  lemma_mod_lt (a + b * p) p

let lemma_eq_trans_2 w x y z = ()

let lemma_mod_plus a b p =
  lemma_div_mod a p;
  lemma_div_mod (a + b * p) p;
  lemma_mod_lt a p;
  lemma_mod_lt (a + b * p) p;
  lemma_mod_plus_0 a b p;
  lemma_mod_plus_1 a b p;
  cut (a + b * p - p * ((a + b * p) / p) = a - p * (a / p));
  let w = (a + b * p) % p in
  let x = a + b * p - p * ((a + b * p) / p) in
  let z = a % p in
  let y = a - p * (a / p) in
  lemma_eq_trans_2 w x y z


#set-options "--z3rlimit 100"

let add_div_mod_1 a n =
  lemma_div_mod a n;
  lemma_div_mod (a + n) n;
  // ((a + n) % n) == a % n + (a / n) * n + n - ((a + n) / n) * n
  distributivity_add_left (a / n) 1 n;
  distributivity_sub_left (a / n + 1) ((a + n) / n) n;
  // (((a + n) % n) == a % n + (a / n + 1 - (a + n) / n) * n
  lt_multiple_is_equal ((a + n) % n) (a % n) (a / n + 1 - (a + n) / n) n;
  ()

#push-options "--z3rlimit 20"
let sub_div_mod_1 (a:int) (n:pos) : Lemma ((a - n) % n == a % n /\ (a - n) / n == a / n - 1) =
  lemma_div_mod a n;
  lemma_div_mod (a - n) n;
  // ((a - n) % n) == a % n - n + (a / n) * n - ((a - n) / n) * n
  distributivity_add_left (a / n) 1 n;
  distributivity_sub_left (a / n - 1) ((a - n) / n) n;
  // ((a - n) % n) == a % n + (a / n - 1 - (a - n) / n) * n
  lt_multiple_is_equal ((a - n) % n) (a % n) (a / n - 1 - (a - n) / n) n;
  ()
#pop-options

#push-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --z3rlimit 30"


let rec lemma_div_mod_plus a b n =
  if b = 0 then ()
  else if b > 0 then
  (
    lemma_div_mod_plus a (b - 1) n;
    sub_div_mod_1 (a + b * n) n
  )
  else // b < 0
  (
    lemma_div_mod_plus a (b + 1) n;
    add_div_mod_1 (a + b * n) n
  )
#pop-options

let small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0) = ()

let lemma_div_plus (a:int) (b:int) (n:pos) = lemma_div_mod_plus a b n

let cancel_mul_div (a:int) (n:pos) =
  small_div 0 n;
  lemma_div_plus 0 a n

let cancel_mul_mod (a:int) (n:pos) =
  small_mod 0 n;
  lemma_mod_plus 0 a n

let multiple_modulo_lemma (a:int) (n:pos) = cancel_mul_mod a n

let mod_add_both (a:int) (b:int) (x:int) (n:pos) =
  assert (a % n == b % n);
  lemma_div_mod a n;
  lemma_div_mod b n;
  lemma_div_mod (a + x) n;
  lemma_div_mod (b + x) n;
  assert ((a + x) % n == a + x - n * ((a + x) / n));
  assert ((b + x) % n == b + x - n * ((b + x) / n));
  assert ((a + x) % n - (b + x) % n == a - b + n * ((b + x) / n - (a + x) / n));
  lemma_div_mod_plus (b%n + x) (b/n) n;
  lemma_div_mod_plus (a%n + x) (a/n) n;
  swap_mul n (b/n); swap_mul n (a/n); (* ugh *)
  assert ((a + x) % n - (b + x) % n == a - b + n * (b/n + (b%n + x)/n - a/n - (a%n + x)/n));
  assert ((a + x) % n - (b + x) % n == a - b + n * (b/n - a/n));
  distributivity_sub_right n (b/n) (a/n);
  assert ((a + x) % n - (b + x) % n == 0)

let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n

let lemma_mod_sub_0 a = ()

let lemma_mod_sub_1 a b =
  small_mod a b;
  assert ((a%b) == a);
  assert ((-a)%b == b - a)

let lemma_mod_mul_distr_l_0 a b p = ()

let rec lemma_mod_mul_distr_l a b n =
  if b = 0 then
  (
    assert (a * 0 == 0 /\ ((a % n) * 0) == 0);
    small_mod 0 n
  )
  else if b > 0 then
  (
    lemma_mod_mul_distr_l a (b - 1) n;
    distributivity_sub_right a b 1;
    distributivity_sub_right (a % n) b 1;
    // (a * b - a) % n == ((a % n) * b - (a % n)) % n
    lemma_mod_sub_distr ((a % n) * b) a n;
    // (a * b - a) % n = ((a % n) * b - a) % n
    mod_add_both (a * b - a) ((a % n) * b - a) a n
  )
  else
  (
    lemma_mod_mul_distr_l a (b + 1) n;
    distributivity_add_right a b 1;
    distributivity_add_right (a % n) b 1;
    // (a * b + a) % n == ((a % n) * b + (a % n)) % n
    lemma_mod_add_distr ((a % n) * b) a n;
    // (a * b + a) % n = ((a % n) * b + a) % n
    mod_add_both (a * b + a) ((a % n) * b + a) (-a) n
  )

let lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) =
    assert (a * (b % n) == (b % n) * a);
    lemma_mod_mul_distr_l b a n

let lemma_mod_injective p a b = ()

let lemma_div_exact a p = ()

let div_exact_r (a:int) (n:pos) = lemma_div_exact a n

let lemma_mod_spec a p =
  lemma_div_mod a p;
  assert (a = p * (a / p) + a % p);
  assert (a % p = a - p * (a / p));
  assert (a - (a % p) = p * (a / p));
  lemma_mod_plus 0 (a / p) p;
  assert ((p * (a / p)) % p = 0);
  lemma_div_exact (p * (a / p)) p

let lemma_mod_spec2 a p =
  lemma_mod_spec a p

let lemma_mod_plus_distr_l a b p =
  let q = (a - (a % p)) / p in
  lemma_mod_spec2 a p;
  lemma_mod_plus (a % p + b) q p

let lemma_mod_plus_distr_r a b p =
  lemma_mod_plus_distr_l b a p

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --max_ifuel 0"


let lemma_mod_plus_mul_distr a b c p =
  let init = ((a + b) * c) % p in
                                     //  ((a + b) * c) % p
  lemma_mod_mul_distr_l (a + b) c p; //= (((a + b) % p) * c) % p
  swap_mul ((a + b) % p) c;          //= (c * ((a + b) % p)) % p
  lemma_mod_mul_distr_l c ((a + b) % p) p; //= (c % p * ((a + b) % p)) % p
  let reached = (c % p * ((a + b) % p)) % p in
  assert (init = reached);
  lemma_mod_plus_distr_l a b p;
  lemma_mod_plus_distr_l b (a % p) p

#reset-options "--initial_fuel 0 --max_fuel 0 --max_ifuel 0"

let lemma_mod_mod a b p =
  lemma_mod_lt b p;
  modulo_lemma (b % p) p

let modulo_range_lemma a b = ()

let small_modulo_lemma_1 a b = ()

let small_modulo_lemma_2 a b = ()

let division_propriety a b = ()

(* Internal lemmas for proving the definition of division *)
val division_definition_lemma_1: a:int -> b:pos -> m:int{a - b < m * b} ->
    Lemma (m > a / b - 1)
let division_definition_lemma_1 a b m =
  if a / b - 1 < 0 then () else begin
    division_propriety a b;
    multiplication_order_lemma m (a / b - 1) b
  end
val division_definition_lemma_2: a:int -> b:pos -> m:int{m * b <= a} ->
    Lemma (m < a / b + 1)
let division_definition_lemma_2 a b m =
  division_propriety a b;
  multiplication_order_lemma (a / b + 1) m b

let division_definition a b m =
  division_definition_lemma_1 a b m;
  division_definition_lemma_2 a b m

let division_addition_lemma a b n = division_definition (a + n * b) b (a / b + n)


#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"
let modulo_distributivity a b c =
  euclidean_division_definition a c;
  euclidean_division_definition b c;
  euclidean_division_definition (a % c + b % c) c;
  division_addition_lemma (a - (a / c) * c + b - (b / c) * c) c (a / c + b / c)

let modulo_addition_lemma (a:int) (n:pos) (b:int) = lemma_mod_plus a b n

let lemma_mod_sub (a:int) (n:pos) (b:int) = lemma_mod_plus a (-b) n

let mod_mult_exact (a:int) (n:pos) (q:pos) =
  pos_times_pos_is_pos n q;
  lemma_div_mod a (n * q);
  let k = a / (n * q) in
  paren_mul_right k q n;
  // a == (k * q) * n
  cancel_mul_mod (k * q) n

let mod_mul_div_exact (a:int) (b:pos) (n:pos) =
  pos_times_pos_is_pos b n;
  lemma_div_mod a (b * n);
  let k = a / (b * n) in
  paren_mul_right k n b;
  // a == (k * n) * b
  cancel_mul_div (k * n) b;
  // a / b = k * n
  cancel_mul_mod k n

let euclidean_div_axiom a b = ()

#reset-options "--initial_fuel 0 --max_fuel 0"

let multiply_fractions (a:int) (n:pos) = ()

let lemma_eucl_div_bound a b q = ()

let nat_over_pos_is_nat a b = ()

let multiple_division_lemma (a:int) (n:pos) = cancel_mul_div a n

let small_division_lemma_1 a b = ()

let small_division_lemma_2 (a:int) (n:pos) = lemma_div_mod a n

(* Lemma: Division distributivity under special condition *)
#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --z3rlimit 30"
let division_sub_lemma (a:int) (n:pos) (b:nat) = lemma_div_plus a (-b) n
#reset-options


let lemma_div_le_ (a:int) (b:int) (d:pos) : Lemma
  (requires (a <= b /\ a / d > b / d))
  (ensures  (False))
  = lemma_div_mod a d;
    lemma_div_mod b d;
    cut (d * (a / d) + a % d <= d * (b / d) + b % d);
    cut (d * (a / d) - d * (b / d) <= b % d - a % d);
    distributivity_sub_right d (a/d) (b/d);
    cut (b % d < d /\ a % d < d);
    cut (d * (a/d - b/d) <= d)

let lemma_div_le a b d =
  if a / d > b / d then lemma_div_le_ a b d

let division_multiplication_lemma (a:int) (b:pos) (c:pos) =
  pos_times_pos_is_pos b c;
  lemma_div_mod a b;
  lemma_div_mod (a / b) c;
  lemma_div_mod a (b * c);
  let k1 = a / b - ((a / b) / c) * c in // k1 = (a / b) % c
  let k2 = a - (a / (b * c)) * (b * c) in // k2 = a % (b * c)
  distributivity_sub_left (a / b) (((a / b) / c) * c) b;
  paren_mul_right ((a / b) / c) c b;
  swap_mul b c;
  // k1 * b == (a / b) * b - ((a / b) / c) * (b * c)
  // k1 * b - k2 == (a / (b * c) - (a / b) / c) * (b * c) - a % b
  lemma_mult_le_right b 0 k1;
  lemma_mult_le_right b k1 (c - 1);
  distributivity_sub_left c 1 b;
  // 0 <= k1 <= (c - 1)
  // 0 <= k1 * b <= (c - 1) * b
  // 0 <= k2 < b * c
  // 1 - b * c <= k1 * b - k2 <= b * c - b
  distributivity_sub_left (a / (b * c)) ((a / b) / c) (b * c);
  bounded_multiple_is_zero (a / (b * c) - (a / b) / c) (b * c)


let lemma_mul_pos_pos_is_pos (x:pos) (y:pos) : Lemma (x*y > 0) = ()
let lemma_mul_nat_pos_is_nat (x:nat) (y:pos) : Lemma (x*y >= 0) = ()

#push-options "--z3rlimit 400"
let modulo_division_lemma_0 (a:nat) (b:pos) (c:pos) : Lemma
  (a / (b*c) <= a /\ (a - (a / (b * c)) * (b * c)) / b = a / b - ((a / (b * c)) * c))
  = slash_decr_axiom a (b*c);
    cut ( (a / (b*c)) * (b * c) = ((a / (b * c)) * c) * b);
    lemma_div_mod a (b*c);
    division_sub_lemma a b ((a / (b*c)) * c)
#pop-options

let modulo_division_lemma a b c =
  division_addition_lemma (a - (a / (b * c)) * (b * c)) b ((a / (b * c)) * c);
  let x = (a - (a / (b * c)) * (b * c)) in
  let y = ((a / (b * c)) * c) in
  cut ((x + y * b) % b = x % b);
  lemma_mul_pos_pos_is_pos b c;
  let bc:pos = b * c in
  let a_bc = a/bc in
  distributivity_sub_left a a_bc bc;
  paren_mul_right (a / (b * c)) c b;
  paren_mul_left (a / (b * c)) c b;
  modulo_division_lemma_0 a b c;
  euclidean_division_definition a (b * c);
  division_multiplication_lemma a b c;
  euclidean_division_definition (a / b) c

#set-options "--z3rlimit 150"

let modulo_modulo_lemma (a:int) (b:pos) (c:pos) =
  pos_times_pos_is_pos b c;
  lemma_div_mod a (b * c);
  paren_mul_right (a / (b * c)) c b;
  swap_mul b c;
  lemma_mod_plus (a % (b * c)) ((a / (b * c)) * c) b

let modulo_add p a b c =
  modulo_distributivity a b p;
  modulo_distributivity a c p

let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

let modulo_sub p a b c =
  modulo_add p (-a) (a + b) (a + c)

let lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) =
  small_mod b n;
  small_mod c n;
  mod_add_both (a + b) (a + c) (-a) n



(*** Powers of 2 ***)

#reset-options "--initial_fuel 1 --max_fuel 1"

let pow2_double_sum n = ()

let pow2_double_mult n = ()

let rec pow2_lt_compat n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_lt_compat (n-1) m; pow2_lt_compat n (n-1)

let rec pow2_le_compat n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_lt_compat n m

let rec pow2_plus n m =
  match n with
  | 0 -> ()
  | _ -> pow2_plus (n - 1) m

let pow2_minus n m =
  if n = m then ()
  else
    begin
    pow2_lt_compat n m;
    pow2_plus (n - m) m;
    slash_star_axiom (pow2 (n - m)) (pow2 m) (pow2 n)
    end

let lemma_div_lt_nat a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

let lemma_div_lt a n m =
  if a >= 0 then lemma_div_lt_nat a n m

let mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)
  =
  mod_mul_div_exact a 2 (pow2 (m - 1))
#set-options "--z3rlimit 10"

let pow2_multiplication_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_division_lemma (a * pow2 (c - b)) (pow2 b)

let pow2_multiplication_division_lemma_2 a b c =
  pow2_plus c (b - c);
  division_multiplication_lemma (a * pow2 c) (pow2 c) (pow2 (b - c));
  multiple_division_lemma a (pow2 c)

let pow2_multiplication_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_modulo_lemma (a * pow2 (c - b)) (pow2 b)


// GM, 2019-06-25: Not sure why validity makes a difference here, it's probably
// just noise.
#push-options "--z3rlimit 500 --smtencoding.valid_intro true --smtencoding.valid_elim true"

let pow2_multiplication_modulo_lemma_2 a b c =
  euclidean_division_definition a (pow2 (b - c));
  let q = pow2 (b - c) in
  let r = a % pow2 (b - c) in
  assert(a = q * (a / q) + a % q);
  pow2_plus (b - c) c;
  paren_mul_right (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  paren_mul_left (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  modulo_addition_lemma ((a % pow2 (b - c)) * pow2 c) (pow2 b) (a / pow2 (b - c));
  multiplication_order_lemma (pow2 (b - c)) (a % pow2 (b - c)) (pow2 c);
  small_modulo_lemma_1 ((a % pow2 (b - c)) * pow2 c) (pow2 b)

#pop-options

let pow2_modulo_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_division_lemma a (pow2 b) (pow2 (c - b))

let pow2_modulo_division_lemma_2 a b c =
  pow2_le_compat b c;
  small_division_lemma_1 (a % pow2 c) (pow2 b)

let pow2_modulo_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_modulo_lemma a (pow2 b) (pow2 (c - b))

let pow2_modulo_modulo_lemma_2 a b c =
  pow2_le_compat b c;
  small_modulo_lemma_1 (a % pow2 c) (pow2 b)
