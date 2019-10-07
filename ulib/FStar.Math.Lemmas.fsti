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

(*** Addition/substraction ***)

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_left: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c)

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_right: a:int -> b:int -> c:int -> Lemma
  (a + b + c = a + (b + c))

val addition_is_associative: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))

val subtraction_is_distributive: a:int -> b:int -> c:int -> Lemma
  (a - b + c = (a - b) + c /\
   a - b - c = a - (b + c) /\
   a - b - c = (a - b) - c /\
   a + (-b - c) = a - b - c /\
   a - (b - c) = a - b + c)

val swap_add_plus_minus: a:int -> b:int -> c:int -> Lemma
  (a + b - c = (a - c) + b)

(*** Multiplication ***)

val lemma_mult_le_left: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (a * b <= a * c))

val lemma_mult_le_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (b * a <= c * a))

val lemma_mult_lt_left: a:pos -> b:pos -> c:pos -> Lemma
  (requires (b < c))
  (ensures  (a * b < a * c))

val lemma_mult_lt_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (b * a <= c * a))

val lemma_mult_lt_sqr: (n:nat) -> (m:nat) -> (k:nat{n < k && m < k}) -> Lemma
  (FStar.Mul.(n * m < k * k))

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma
  ((a + b) * c = a * c + b * c)

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b + c) = a * b + a * c))

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_left: a:int -> b:int -> c:int ->
  Lemma ((a - b) * c = a * c - b * c)

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b - c) = a * b - a * c))

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
val paren_mul_left: a:int -> b:int -> c:int -> Lemma
  (a * b * c = (a * b) * c)

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
val paren_mul_right: a:int -> b:int -> c:int -> Lemma
  (a * b * c = a * (b * c))

(* Lemma: multiplication on integers is commutative *)
val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)

(* Lemma: minus applies to the whole term *)
val neg_mul_left: a:int -> b:int -> Lemma (-(a * b) = (-a) * b)

(* Lemma: minus applies to the whole term *)
val neg_mul_right: a:int -> b:int -> Lemma (-(a * b) = a * (-b))

val swap_neg_mul: a:int -> b:int -> Lemma ((-a) * b = a * (-b))

(* Lemma: multiplication precedence on addition *)
val mul_binds_tighter: a:int -> b:int -> c:int -> Lemma (a + (b * c) = a + b * c)

(* Lemma: multiplication keeps symetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
val mul_ineq1: a:int -> b:nat -> c:int -> d:nat -> Lemma
    (requires (-b < a /\ a < b /\
               -d < c /\ c < d))
    (ensures  (-(b * d) < a * c /\ a * c < b * d))

val nat_times_nat_is_nat: a:nat -> b:nat -> Lemma (a * b >= 0)

val pos_times_pos_is_pos: a:pos -> b:pos -> Lemma (a * b > 0)

val bounded_multiple_is_zero: x:int -> n:pos -> Lemma
  (requires -n < x * n /\ x * n < n)
  (ensures x == 0)

val lt_multiple_is_equal: a:nat -> b:nat -> x:int -> n:pos -> Lemma
  (requires a < n /\ b < n /\ a == b + x * n)
  (ensures a == b /\ x == 0)

val lemma_mul_sub_distr: a:int -> b:int -> c:int -> Lemma
  (a * b - a * c = a * (b - c))

val multiplication_order_lemma: a:int -> b:int -> p:pos ->
    Lemma (a >= b <==> a * p >= b * p)

(*** Division/Modulo ***)

(* Lemma: Definition of euclidean division *)
val euclidean_division_definition: a:int -> b:pos -> Lemma (a = (a / b) * b + a % b)

val modulo_lemma: a:nat -> b:pos -> Lemma
  (requires (a < b))
  (ensures (a % b = a))

(** Same as `lemma_div_def` in Math.Lib *)
val lemma_div_mod: a:int -> p:pos -> Lemma (a = p * (a / p) + a % p)

val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p)

val small_mod: a:nat -> n:pos -> Lemma
  (requires a < n)
  (ensures a % n == a)

val lemma_mod_plus_0: a:int -> b:int -> p:pos -> Lemma
  ((a + b * p) % p - a % p = p * (b + a / p - (a + b * p) / p))

val lemma_mod_plus_1: a:int -> b:int -> p:pos -> Lemma
  ((a + b * p) % p = a + b * p - p * ((a + b * p) / p))

val lemma_eq_trans_2: w:int -> x:int -> y:int -> z:int -> Lemma
  (requires (w = x /\ x = y /\ y = z))
  (ensures  (w = z))

val lemma_mod_plus: a:int -> b:int -> p:pos -> Lemma
  ((a + b * p) % p = a % p)

val add_div_mod_1: a:int -> n:pos -> Lemma ((a + n) % n == a % n /\ (a + n) / n == a / n + 1)

val sub_div_mod_1: a:int -> n:pos -> Lemma ((a - n) % n == a % n /\ (a - n) / n == a / n - 1)

val lemma_div_mod_plus: a:int -> b:int -> n:pos -> Lemma
  (requires True)
  (ensures
    (a + b * n) / n = a / n + b /\
    (a + b * n) % n = a % n
  )
  (decreases (if b > 0 then b else -b))

val small_div: a:nat -> n:pos -> Lemma (requires a < n) (ensures a / n == 0)

val lemma_div_plus: a:int -> b:int -> n:pos -> Lemma ((a + b * n) / n = a / n + b)

val cancel_mul_div: a:int -> n:pos -> Lemma ((a * n) / n == a)

val cancel_mul_mod: a:int -> n:pos -> Lemma ((a * n) % n == 0)

(* Lemma: (a * b) % b = 0 *)
val multiple_modulo_lemma: a:int -> n:pos -> Lemma ((a * n) % n = 0)

val mod_add_both: a:int -> b:int -> x:int -> n:pos -> Lemma
  (requires a % n == b % n)
  (ensures (a + x) % n == (b + x) % n)

val lemma_mod_add_distr: a:int -> b:int -> n:pos -> Lemma ((a + b % n) % n = (a + b) % n)

val lemma_mod_sub_distr: a:int -> b:int -> n:pos -> Lemma ((a - b % n) % n = (a - b) % n)

val lemma_mod_sub_0: a:pos -> Lemma ((-1) % a = a - 1)

val lemma_mod_sub_1: a:pos -> b:pos{a < b} -> Lemma ((-a) % b = b - (a%b))

val lemma_mod_mul_distr_l_0: a:int -> b:int -> p:pos -> Lemma
  ((((a % p) + (a / p) * p) * b) % p = ((a % p) * b + ((a / p) * b) * p) % p)

val lemma_mod_mul_distr_l: a:int -> b:int -> n:pos -> Lemma
  (requires True)
  (ensures (a * b) % n = ((a % n) * b) % n)
  (decreases (if b >= 0 then b else -b))

val lemma_mod_mul_distr_r: a:int -> b:int -> n:pos -> Lemma ((a * b) % n = (a * (b % n)) % n)

val lemma_mod_injective: p:pos -> a:nat -> b:nat -> Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))

val lemma_div_exact: a:int -> p:pos -> Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))

val div_exact_r: a:int -> n:pos -> Lemma
  (requires (a % n = 0))
  (ensures  (a = (a / n) * n))

val lemma_mod_spec: a:int -> p:pos -> Lemma
  (a / p = (a - (a % p)) / p)

val lemma_mod_spec2: a:int -> p:pos -> Lemma
  (let q:int = (a - (a % p)) / p in a = (a % p) + q * p)

val lemma_mod_plus_distr_l: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = ((a % p) + b) % p)

val lemma_mod_plus_distr_r: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = (a + (b % p)) % p)

val lemma_mod_plus_mul_distr: a:int -> b:int -> c:int -> p:pos -> Lemma
  (((a + b) * c) % p = ((((a % p) + (b % p)) % p) * (c % p)) % p)

val lemma_mod_mod: a:int -> b:int -> p:pos -> Lemma
  (requires (a = b % p))
  (ensures  (a % p = b % p))

val modulo_range_lemma: a:int -> b:pos ->
    Lemma (a % b >= 0 && a % b < b)

val small_modulo_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a % b = a)

val small_modulo_lemma_2: a:int -> b:pos ->
    Lemma (requires a % b = a) (ensures a < b)

val division_propriety: a:int -> b:pos ->
    Lemma (a - b < (a / b) * b && (a / b) * b <= a)

(* Lemma: Definition of division *)
val division_definition: a:int -> b:pos -> m:int{a - b < m * b && m * b <= a} ->
    Lemma (m = a / b)

(* Lemma: Division distributivity under special condition *)
val division_addition_lemma: a:int -> b:pos -> n:int ->
    Lemma ( (a + n * b) / b = a / b + n )

(* Lemma: Modulo distributivity *)
val modulo_distributivity: a:int -> b:int -> c:pos ->
    Lemma ( (a + b) % c = (a % c + b % c) % c )

(* Lemma: Modulo distributivity under special condition *)
val modulo_addition_lemma: a:int -> n:pos -> b:int -> Lemma ((a + b * n) % n = a % n)

(* Lemma: Modulo distributivity under special condition *)
val lemma_mod_sub: a:int -> n:pos -> b:int -> Lemma (ensures (a - b * n) % n = a % n)

val mod_mult_exact: a:int -> n:pos -> q:pos -> Lemma
  (requires (pos_times_pos_is_pos n q; a % (n * q) == 0))
  (ensures a % n == 0)

val mod_mul_div_exact: a:int -> b:pos -> n:pos -> Lemma
  (requires (pos_times_pos_is_pos b n; a % (b * n) == 0))
  (ensures (a / b) % n == 0)

(* Lemma: definition of Euclidean division *)
val euclidean_div_axiom: a:int -> b:pos -> Lemma
  ((a - b * (a / b) >= 0 /\ a - b * (a / b) < b))

(* Lemma: loss of precision in euclidean division *)
val multiply_fractions: a:int -> n:pos -> Lemma (n * ( a / n ) <= a)

val lemma_eucl_div_bound: a:int -> b:int -> q:int -> Lemma
  (requires (a < q))
  (ensures  (a + q * b < q * (b+1)))

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)

(* Lemma: (a * b) / b = a *)
val multiple_division_lemma: a:int -> n:pos -> Lemma ((a * n) / n = a)

val small_division_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a / b = 0)

val small_division_lemma_2: a:int -> n:pos -> Lemma
  (requires a / n = 0)
  (ensures 0 <= a /\ a < n)

val division_sub_lemma: a:int -> n:pos -> b:nat -> Lemma ((a - b * n) / n = a / n - b)

val lemma_div_le: a:int -> b:int -> d:pos ->
  Lemma (requires (a <= b))
        (ensures  (a / d <= b / d))

(* Lemma: Divided by a product is equivalent to being divided one by one *)
val division_multiplication_lemma: a:int -> b:pos -> c:pos -> Lemma
  (pos_times_pos_is_pos b c; a / (b * c) = (a / b) / c)

val lemma_mul_pos_pos_is_pos: x:pos -> y:pos -> Lemma (x*y > 0)
val lemma_mul_nat_pos_is_nat: x:nat -> y:pos -> Lemma (x*y >= 0)

val modulo_division_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ( (a % (b * c)) / b = (a / b) % c )

val modulo_modulo_lemma: a:int -> b:pos -> c:pos -> Lemma
  (pos_times_pos_is_pos b c; (a % (b * c)) % b = a % b)

val modulo_add : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires (b % p = c % p))
  (ensures  ((a + b) % p = (a + c) % p))

val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

val modulo_sub : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires ((a + b) % p = (a + c) % p))
  (ensures (b % p = c % p))

val lemma_mod_plus_injective: n:pos -> a:int -> b:nat -> c:nat -> Lemma
  (requires b < n /\ c < n /\ (a + b) % n = (a + c) % n)
  (ensures  b = c)

(*** Powers of 2 ***)

val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))

val pow2_double_mult: n:nat -> Lemma (2 * pow2 n = pow2 (n + 1))

val pow2_lt_compat: n:nat -> m:nat -> Lemma
  (requires (m < n))
  (ensures  (pow2 m < pow2 n))
  (decreases (n - m))

val pow2_le_compat: n:nat -> m:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m <= pow2 n))
  (decreases (n - m))

val pow2_plus: n:nat -> m:nat -> Lemma
  (ensures (pow2 n * pow2 m = pow2 (n + m)))
  (decreases n)

(* Lemma : definition of the exponential property of pow2 *)
val pow2_minus: n:nat -> m:nat{ n >= m } -> Lemma
  ((pow2 n) / (pow2 m) = pow2 (n - m))

val lemma_div_lt_nat: a:int -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
        (ensures  (a / pow2 m < pow2 (n-m)))

val lemma_div_lt: a:int -> n:nat -> m:nat -> Lemma
  (requires m <= n /\ a < pow2 n)
  (ensures a / pow2 m < pow2 (n-m))

val mod_pow2_div2: a:int -> m:pos -> Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)

val pow2_multiplication_division_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a * pow2 (c - b))

val pow2_multiplication_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a / pow2 (b - c))

val pow2_multiplication_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) % pow2 b = 0 )

val pow2_multiplication_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a * pow2 c) % pow2 b = (a % pow2 (b - c)) * pow2 c )

val pow2_modulo_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a % pow2 c) / pow2 b = (a / pow2 b) % (pow2 (c - b)) )

val pow2_modulo_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a % pow2 c) / pow2 b = 0 )

val pow2_modulo_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a % pow2 c) % pow2 b = a % pow2 b )

val pow2_modulo_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a % pow2 c) % pow2 b = a % pow2 c )
