set_option maxRecDepth 20000

/-!
# JSP-000598 — Lean 4.20.0, no Mathlib

Question: Can two distinct central binomial coefficients have exactly the same prime divisors?
Answer: No.

We formalize the bounded case by explicit computation for m < n ≤ 20.
Each pair is distinguished by a prime divisor found by brute force enumeration.
-/

-- # Basic definitions

def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def centralBinom (n : Nat) : Nat := binom (2 * n) n

def samePrimes (a b : Nat) : Prop := ∀ p, PrimeP p → (p ∣ a ↔ p ∣ b)

-- # Prime proving infrastructure (copied from JSP-000307 template)

theorem mod_eq_zero_of_dvd {m n : Nat} (h : m ∣ n) : n % m = 0 := by
  cases h with | intro k hk => rw [hk]; exact Nat.mul_mod_right m k

private theorem le_of_dvd_pos {m n : Nat} (hn : 0 < n) (h : m ∣ n) : m ≤ n := by
  cases h with
  | intro k hk =>
    cases Nat.eq_zero_or_pos k with
    | inl hk0 => rw [hk, hk0, Nat.mul_zero] at hn; exact absurd hn (Nat.lt_irrefl 0)
    | inr hk0 => rw [hk]; exact Nat.le_mul_of_pos_right m hk0

theorem primeP_of_cert (p : Nat) (h2 : 2 ≤ p)
    (h : ((List.range (p + 1)).all fun m =>
      decide (p % m ≠ 0) || decide (m = 1) || decide (m = p)) = true) :
    PrimeP p := by
  refine ⟨h2, fun m hm => ?_⟩
  have hmp : m ≤ p := le_of_dvd_pos (by omega) hm
  have hall := List.all_eq_true.mp h m (by rw [List.mem_range]; omega)
  have hmod : p % m = 0 := mod_eq_zero_of_dvd hm
  rw [Bool.or_eq_true] at hall
  cases hall with
  | inr hpq => exact Or.inr (decide_eq_true_eq.mp hpq)
  | inl hab =>
    rw [Bool.or_eq_true] at hab
    cases hab with
    | inl hne => exact absurd hmod (decide_eq_true_eq.mp hne)
    | inr h1 => exact Or.inl (decide_eq_true_eq.mp h1)
theorem primeP_2 : PrimeP 2 := primeP_of_cert 2 (by decide) (by decide)
theorem primeP_3 : PrimeP 3 := primeP_of_cert 3 (by decide) (by decide)
theorem primeP_5 : PrimeP 5 := primeP_of_cert 5 (by decide) (by decide)
theorem primeP_7 : PrimeP 7 := primeP_of_cert 7 (by decide) (by decide)
theorem primeP_11 : PrimeP 11 := primeP_of_cert 11 (by decide) (by decide)
theorem primeP_13 : PrimeP 13 := primeP_of_cert 13 (by decide) (by decide)
theorem primeP_17 : PrimeP 17 := primeP_of_cert 17 (by decide) (by decide)
theorem primeP_19 : PrimeP 19 := primeP_of_cert 19 (by decide) (by decide)
theorem primeP_23 : PrimeP 23 := primeP_of_cert 23 (by decide) (by decide)
theorem primeP_29 : PrimeP 29 := primeP_of_cert 29 (by decide) (by decide)
theorem primeP_31 : PrimeP 31 := primeP_of_cert 31 (by decide) (by decide)
theorem primeP_37 : PrimeP 37 := primeP_of_cert 37 (by decide) (by decide)

-- # Helpers

theorem samePrimes_symm (a b : Nat) : samePrimes a b → samePrimes b a := by
  intro h p hp
  have h1 := h p hp
  exact h1.symm

theorem distinguish_via_prime {a b p : Nat} (hp : PrimeP p)
    (hb : p ∣ b) (ha : ¬ p ∣ a) :
    ¬ samePrimes a b := by
  intro h
  have h1 : p ∣ a ↔ p ∣ b := h p hp
  have h2 : p ∣ a := h1.mpr hb
  exact ha h2

-- # Individual pair theorems

theorem pair_0_1 : ¬ samePrimes (centralBinom 0) (centralBinom 1) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_0_2 : ¬ samePrimes (centralBinom 0) (centralBinom 2) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_2 : ¬ samePrimes (centralBinom 1) (centralBinom 2) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_0_3 : ¬ samePrimes (centralBinom 0) (centralBinom 3) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_3 : ¬ samePrimes (centralBinom 1) (centralBinom 3) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_2_3 : ¬ samePrimes (centralBinom 2) (centralBinom 3) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_0_4 : ¬ samePrimes (centralBinom 0) (centralBinom 4) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_1_4 : ¬ samePrimes (centralBinom 1) (centralBinom 4) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_2_4 : ¬ samePrimes (centralBinom 2) (centralBinom 4) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_3_4 : ¬ samePrimes (centralBinom 3) (centralBinom 4) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_0_5 : ¬ samePrimes (centralBinom 0) (centralBinom 5) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_5 : ¬ samePrimes (centralBinom 1) (centralBinom 5) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_2_5 : ¬ samePrimes (centralBinom 2) (centralBinom 5) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_5 : ¬ samePrimes (centralBinom 3) (centralBinom 5) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_4_5 : ¬ samePrimes (centralBinom 4) (centralBinom 5) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_0_6 : ¬ samePrimes (centralBinom 0) (centralBinom 6) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_6 : ¬ samePrimes (centralBinom 1) (centralBinom 6) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_2_6 : ¬ samePrimes (centralBinom 2) (centralBinom 6) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_3_6 : ¬ samePrimes (centralBinom 3) (centralBinom 6) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_4_6 : ¬ samePrimes (centralBinom 4) (centralBinom 6) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_5_6 : ¬ samePrimes (centralBinom 5) (centralBinom 6) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_0_7 : ¬ samePrimes (centralBinom 0) (centralBinom 7) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_7 : ¬ samePrimes (centralBinom 1) (centralBinom 7) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_2_7 : ¬ samePrimes (centralBinom 2) (centralBinom 7) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_3_7 : ¬ samePrimes (centralBinom 3) (centralBinom 7) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_4_7 : ¬ samePrimes (centralBinom 4) (centralBinom 7) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_5_7 : ¬ samePrimes (centralBinom 5) (centralBinom 7) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_6_7 : ¬ samePrimes (centralBinom 6) (centralBinom 7) :=
  distinguish_via_prime primeP_13 (by decide) (by decide)

theorem pair_0_8 : ¬ samePrimes (centralBinom 0) (centralBinom 8) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_8 : ¬ samePrimes (centralBinom 1) (centralBinom 8) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_2_8 : ¬ samePrimes (centralBinom 2) (centralBinom 8) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_3_8 : ¬ samePrimes (centralBinom 3) (centralBinom 8) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_4_8 : ¬ samePrimes (centralBinom 4) (centralBinom 8) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_5_8 : ¬ samePrimes (centralBinom 5) (centralBinom 8) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_6_8 : ¬ samePrimes (centralBinom 6) (centralBinom 8) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_7_8 : ¬ samePrimes (centralBinom 7) (centralBinom 8) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_0_9 : ¬ samePrimes (centralBinom 0) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_1_9 : ¬ samePrimes (centralBinom 1) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_2_9 : ¬ samePrimes (centralBinom 2) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_3_9 : ¬ samePrimes (centralBinom 3) (centralBinom 9) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_4_9 : ¬ samePrimes (centralBinom 4) (centralBinom 9) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_5_9 : ¬ samePrimes (centralBinom 5) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_6_9 : ¬ samePrimes (centralBinom 6) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_7_9 : ¬ samePrimes (centralBinom 7) (centralBinom 9) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_8_9 : ¬ samePrimes (centralBinom 8) (centralBinom 9) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_0_10 : ¬ samePrimes (centralBinom 0) (centralBinom 10) :=
  distinguish_via_prime primeP_2 (by decide) (by decide)

theorem pair_1_10 : ¬ samePrimes (centralBinom 1) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_2_10 : ¬ samePrimes (centralBinom 2) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_3_10 : ¬ samePrimes (centralBinom 3) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_4_10 : ¬ samePrimes (centralBinom 4) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_5_10 : ¬ samePrimes (centralBinom 5) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_6_10 : ¬ samePrimes (centralBinom 6) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_7_10 : ¬ samePrimes (centralBinom 7) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_8_10 : ¬ samePrimes (centralBinom 8) (centralBinom 10) :=
  distinguish_via_prime primeP_17 (by decide) (by decide)

theorem pair_9_10 : ¬ samePrimes (centralBinom 9) (centralBinom 10) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_0_11 : ¬ samePrimes (centralBinom 0) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_11 : ¬ samePrimes (centralBinom 1) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_11 : ¬ samePrimes (centralBinom 2) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_11 : ¬ samePrimes (centralBinom 3) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_11 : ¬ samePrimes (centralBinom 4) (centralBinom 11) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_5_11 : ¬ samePrimes (centralBinom 5) (centralBinom 11) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_6_11 : ¬ samePrimes (centralBinom 6) (centralBinom 11) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_11 : ¬ samePrimes (centralBinom 7) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_11 : ¬ samePrimes (centralBinom 8) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_11 : ¬ samePrimes (centralBinom 9) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_11 : ¬ samePrimes (centralBinom 10) (centralBinom 11) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_0_12 : ¬ samePrimes (centralBinom 0) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_12 : ¬ samePrimes (centralBinom 1) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_12 : ¬ samePrimes (centralBinom 2) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_12 : ¬ samePrimes (centralBinom 3) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_12 : ¬ samePrimes (centralBinom 4) (centralBinom 12) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_5_12 : ¬ samePrimes (centralBinom 5) (centralBinom 12) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_6_12 : ¬ samePrimes (centralBinom 6) (centralBinom 12) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_12 : ¬ samePrimes (centralBinom 7) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_12 : ¬ samePrimes (centralBinom 8) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_12 : ¬ samePrimes (centralBinom 9) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_12 : ¬ samePrimes (centralBinom 10) (centralBinom 12) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_11_12 : ¬ samePrimes (centralBinom 11) (centralBinom 12) :=
  distinguish_via_prime primeP_23 (by decide) (by decide)

theorem pair_0_13 : ¬ samePrimes (centralBinom 0) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_13 : ¬ samePrimes (centralBinom 1) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_13 : ¬ samePrimes (centralBinom 2) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_13 : ¬ samePrimes (centralBinom 3) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_13 : ¬ samePrimes (centralBinom 4) (centralBinom 13) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_5_13 : ¬ samePrimes (centralBinom 5) (centralBinom 13) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_6_13 : ¬ samePrimes (centralBinom 6) (centralBinom 13) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_13 : ¬ samePrimes (centralBinom 7) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_13 : ¬ samePrimes (centralBinom 8) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_13 : ¬ samePrimes (centralBinom 9) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_13 : ¬ samePrimes (centralBinom 10) (centralBinom 13) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_11_13 : ¬ samePrimes (centralBinom 11) (centralBinom 13) :=
  distinguish_via_prime primeP_23 (by decide) (by decide)

theorem pair_12_13 : ¬ samePrimes (centralBinom 12) (centralBinom 13) :=
  distinguish_via_prime primeP_5 (by decide) (by decide)

theorem pair_0_14 : ¬ samePrimes (centralBinom 0) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_1_14 : ¬ samePrimes (centralBinom 1) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_2_14 : ¬ samePrimes (centralBinom 2) (centralBinom 14) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_3_14 : ¬ samePrimes (centralBinom 3) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_4_14 : ¬ samePrimes (centralBinom 4) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_5_14 : ¬ samePrimes (centralBinom 5) (centralBinom 14) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_6_14 : ¬ samePrimes (centralBinom 6) (centralBinom 14) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_14 : ¬ samePrimes (centralBinom 7) (centralBinom 14) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_8_14 : ¬ samePrimes (centralBinom 8) (centralBinom 14) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_9_14 : ¬ samePrimes (centralBinom 9) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_10_14 : ¬ samePrimes (centralBinom 10) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_11_14 : ¬ samePrimes (centralBinom 11) (centralBinom 14) :=
  distinguish_via_prime primeP_23 (by decide) (by decide)

theorem pair_12_14 : ¬ samePrimes (centralBinom 12) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_13_14 : ¬ samePrimes (centralBinom 13) (centralBinom 14) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_0_15 : ¬ samePrimes (centralBinom 0) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_1_15 : ¬ samePrimes (centralBinom 1) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_2_15 : ¬ samePrimes (centralBinom 2) (centralBinom 15) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_3_15 : ¬ samePrimes (centralBinom 3) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_4_15 : ¬ samePrimes (centralBinom 4) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_5_15 : ¬ samePrimes (centralBinom 5) (centralBinom 15) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_6_15 : ¬ samePrimes (centralBinom 6) (centralBinom 15) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_15 : ¬ samePrimes (centralBinom 7) (centralBinom 15) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_8_15 : ¬ samePrimes (centralBinom 8) (centralBinom 15) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_9_15 : ¬ samePrimes (centralBinom 9) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_10_15 : ¬ samePrimes (centralBinom 10) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_11_15 : ¬ samePrimes (centralBinom 11) (centralBinom 15) :=
  distinguish_via_prime primeP_23 (by decide) (by decide)

theorem pair_12_15 : ¬ samePrimes (centralBinom 12) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_13_15 : ¬ samePrimes (centralBinom 13) (centralBinom 15) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_14_15 : ¬ samePrimes (centralBinom 14) (centralBinom 15) :=
  distinguish_via_prime primeP_29 (by decide) (by decide)

theorem pair_0_16 : ¬ samePrimes (centralBinom 0) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_1_16 : ¬ samePrimes (centralBinom 1) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_2_16 : ¬ samePrimes (centralBinom 2) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_3_16 : ¬ samePrimes (centralBinom 3) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_4_16 : ¬ samePrimes (centralBinom 4) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_5_16 : ¬ samePrimes (centralBinom 5) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_6_16 : ¬ samePrimes (centralBinom 6) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_7_16 : ¬ samePrimes (centralBinom 7) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_8_16 : ¬ samePrimes (centralBinom 8) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_9_16 : ¬ samePrimes (centralBinom 9) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_10_16 : ¬ samePrimes (centralBinom 10) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_11_16 : ¬ samePrimes (centralBinom 11) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_12_16 : ¬ samePrimes (centralBinom 12) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_13_16 : ¬ samePrimes (centralBinom 13) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_14_16 : ¬ samePrimes (centralBinom 14) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_15_16 : ¬ samePrimes (centralBinom 15) (centralBinom 16) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_0_17 : ¬ samePrimes (centralBinom 0) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_1_17 : ¬ samePrimes (centralBinom 1) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_2_17 : ¬ samePrimes (centralBinom 2) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_3_17 : ¬ samePrimes (centralBinom 3) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_4_17 : ¬ samePrimes (centralBinom 4) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_5_17 : ¬ samePrimes (centralBinom 5) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_6_17 : ¬ samePrimes (centralBinom 6) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_7_17 : ¬ samePrimes (centralBinom 7) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_8_17 : ¬ samePrimes (centralBinom 8) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_9_17 : ¬ samePrimes (centralBinom 9) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_10_17 : ¬ samePrimes (centralBinom 10) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_11_17 : ¬ samePrimes (centralBinom 11) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_12_17 : ¬ samePrimes (centralBinom 12) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_13_17 : ¬ samePrimes (centralBinom 13) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_14_17 : ¬ samePrimes (centralBinom 14) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_15_17 : ¬ samePrimes (centralBinom 15) (centralBinom 17) :=
  distinguish_via_prime primeP_31 (by decide) (by decide)

theorem pair_16_17 : ¬ samePrimes (centralBinom 16) (centralBinom 17) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_0_18 : ¬ samePrimes (centralBinom 0) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_18 : ¬ samePrimes (centralBinom 1) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_18 : ¬ samePrimes (centralBinom 2) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_18 : ¬ samePrimes (centralBinom 3) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_18 : ¬ samePrimes (centralBinom 4) (centralBinom 18) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_5_18 : ¬ samePrimes (centralBinom 5) (centralBinom 18) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_6_18 : ¬ samePrimes (centralBinom 6) (centralBinom 18) :=
  distinguish_via_prime primeP_19 (by decide) (by decide)

theorem pair_7_18 : ¬ samePrimes (centralBinom 7) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_18 : ¬ samePrimes (centralBinom 8) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_18 : ¬ samePrimes (centralBinom 9) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_18 : ¬ samePrimes (centralBinom 10) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_11_18 : ¬ samePrimes (centralBinom 11) (centralBinom 18) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_12_18 : ¬ samePrimes (centralBinom 12) (centralBinom 18) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_13_18 : ¬ samePrimes (centralBinom 13) (centralBinom 18) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_14_18 : ¬ samePrimes (centralBinom 14) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_15_18 : ¬ samePrimes (centralBinom 15) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_16_18 : ¬ samePrimes (centralBinom 16) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_17_18 : ¬ samePrimes (centralBinom 17) (centralBinom 18) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_0_19 : ¬ samePrimes (centralBinom 0) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_19 : ¬ samePrimes (centralBinom 1) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_19 : ¬ samePrimes (centralBinom 2) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_19 : ¬ samePrimes (centralBinom 3) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_19 : ¬ samePrimes (centralBinom 4) (centralBinom 19) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_5_19 : ¬ samePrimes (centralBinom 5) (centralBinom 19) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_6_19 : ¬ samePrimes (centralBinom 6) (centralBinom 19) :=
  distinguish_via_prime primeP_23 (by decide) (by decide)

theorem pair_7_19 : ¬ samePrimes (centralBinom 7) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_19 : ¬ samePrimes (centralBinom 8) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_19 : ¬ samePrimes (centralBinom 9) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_19 : ¬ samePrimes (centralBinom 10) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_11_19 : ¬ samePrimes (centralBinom 11) (centralBinom 19) :=
  distinguish_via_prime primeP_11 (by decide) (by decide)

theorem pair_12_19 : ¬ samePrimes (centralBinom 12) (centralBinom 19) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_13_19 : ¬ samePrimes (centralBinom 13) (centralBinom 19) :=
  distinguish_via_prime primeP_3 (by decide) (by decide)

theorem pair_14_19 : ¬ samePrimes (centralBinom 14) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_15_19 : ¬ samePrimes (centralBinom 15) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_16_19 : ¬ samePrimes (centralBinom 16) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_17_19 : ¬ samePrimes (centralBinom 17) (centralBinom 19) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_18_19 : ¬ samePrimes (centralBinom 18) (centralBinom 19) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_0_20 : ¬ samePrimes (centralBinom 0) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_1_20 : ¬ samePrimes (centralBinom 1) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_2_20 : ¬ samePrimes (centralBinom 2) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_3_20 : ¬ samePrimes (centralBinom 3) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_4_20 : ¬ samePrimes (centralBinom 4) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_5_20 : ¬ samePrimes (centralBinom 5) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_6_20 : ¬ samePrimes (centralBinom 6) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_7_20 : ¬ samePrimes (centralBinom 7) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_8_20 : ¬ samePrimes (centralBinom 8) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_9_20 : ¬ samePrimes (centralBinom 9) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_10_20 : ¬ samePrimes (centralBinom 10) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_11_20 : ¬ samePrimes (centralBinom 11) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_12_20 : ¬ samePrimes (centralBinom 12) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_13_20 : ¬ samePrimes (centralBinom 13) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_14_20 : ¬ samePrimes (centralBinom 14) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_15_20 : ¬ samePrimes (centralBinom 15) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_16_20 : ¬ samePrimes (centralBinom 16) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_17_20 : ¬ samePrimes (centralBinom 17) (centralBinom 20) :=
  distinguish_via_prime primeP_7 (by decide) (by decide)

theorem pair_18_20 : ¬ samePrimes (centralBinom 18) (centralBinom 20) :=
  distinguish_via_prime primeP_37 (by decide) (by decide)

theorem pair_19_20 : ¬ samePrimes (centralBinom 19) (centralBinom 20) :=
  distinguish_via_prime primeP_13 (by decide) (by decide)

-- # Bundled bounded theorem

theorem jsp_000598_bounded :
    ∀ m n, m < n → n ≤ 20 → ¬ samePrimes (centralBinom m) (centralBinom n) := by
  intro m n hmn hn20
  have hndisj : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 := by omega
  rcases hndisj with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · omega
  · -- n = 1
    have hmd : m = 0 := by omega
    rcases hmd with rfl
    exact pair_0_1
  · -- n = 2
    have hmd : m = 0 ∨ m = 1 := by omega
    rcases hmd with (rfl | rfl)
    · exact pair_0_2
    · exact pair_1_2
  · -- n = 3
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hmd with (rfl | rfl | rfl)
    · exact pair_0_3
    · exact pair_1_3
    · exact pair_2_3
  · -- n = 4
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl)
    · exact pair_0_4
    · exact pair_1_4
    · exact pair_2_4
    · exact pair_3_4
  · -- n = 5
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_5
    · exact pair_1_5
    · exact pair_2_5
    · exact pair_3_5
    · exact pair_4_5
  · -- n = 6
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_6
    · exact pair_1_6
    · exact pair_2_6
    · exact pair_3_6
    · exact pair_4_6
    · exact pair_5_6
  · -- n = 7
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_7
    · exact pair_1_7
    · exact pair_2_7
    · exact pair_3_7
    · exact pair_4_7
    · exact pair_5_7
    · exact pair_6_7
  · -- n = 8
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_8
    · exact pair_1_8
    · exact pair_2_8
    · exact pair_3_8
    · exact pair_4_8
    · exact pair_5_8
    · exact pair_6_8
    · exact pair_7_8
  · -- n = 9
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_9
    · exact pair_1_9
    · exact pair_2_9
    · exact pair_3_9
    · exact pair_4_9
    · exact pair_5_9
    · exact pair_6_9
    · exact pair_7_9
    · exact pair_8_9
  · -- n = 10
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_10
    · exact pair_1_10
    · exact pair_2_10
    · exact pair_3_10
    · exact pair_4_10
    · exact pair_5_10
    · exact pair_6_10
    · exact pair_7_10
    · exact pair_8_10
    · exact pair_9_10
  · -- n = 11
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_11
    · exact pair_1_11
    · exact pair_2_11
    · exact pair_3_11
    · exact pair_4_11
    · exact pair_5_11
    · exact pair_6_11
    · exact pair_7_11
    · exact pair_8_11
    · exact pair_9_11
    · exact pair_10_11
  · -- n = 12
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_12
    · exact pair_1_12
    · exact pair_2_12
    · exact pair_3_12
    · exact pair_4_12
    · exact pair_5_12
    · exact pair_6_12
    · exact pair_7_12
    · exact pair_8_12
    · exact pair_9_12
    · exact pair_10_12
    · exact pair_11_12
  · -- n = 13
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_13
    · exact pair_1_13
    · exact pair_2_13
    · exact pair_3_13
    · exact pair_4_13
    · exact pair_5_13
    · exact pair_6_13
    · exact pair_7_13
    · exact pair_8_13
    · exact pair_9_13
    · exact pair_10_13
    · exact pair_11_13
    · exact pair_12_13
  · -- n = 14
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_14
    · exact pair_1_14
    · exact pair_2_14
    · exact pair_3_14
    · exact pair_4_14
    · exact pair_5_14
    · exact pair_6_14
    · exact pair_7_14
    · exact pair_8_14
    · exact pair_9_14
    · exact pair_10_14
    · exact pair_11_14
    · exact pair_12_14
    · exact pair_13_14
  · -- n = 15
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_15
    · exact pair_1_15
    · exact pair_2_15
    · exact pair_3_15
    · exact pair_4_15
    · exact pair_5_15
    · exact pair_6_15
    · exact pair_7_15
    · exact pair_8_15
    · exact pair_9_15
    · exact pair_10_15
    · exact pair_11_15
    · exact pair_12_15
    · exact pair_13_15
    · exact pair_14_15
  · -- n = 16
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_16
    · exact pair_1_16
    · exact pair_2_16
    · exact pair_3_16
    · exact pair_4_16
    · exact pair_5_16
    · exact pair_6_16
    · exact pair_7_16
    · exact pair_8_16
    · exact pair_9_16
    · exact pair_10_16
    · exact pair_11_16
    · exact pair_12_16
    · exact pair_13_16
    · exact pair_14_16
    · exact pair_15_16
  · -- n = 17
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_17
    · exact pair_1_17
    · exact pair_2_17
    · exact pair_3_17
    · exact pair_4_17
    · exact pair_5_17
    · exact pair_6_17
    · exact pair_7_17
    · exact pair_8_17
    · exact pair_9_17
    · exact pair_10_17
    · exact pair_11_17
    · exact pair_12_17
    · exact pair_13_17
    · exact pair_14_17
    · exact pair_15_17
    · exact pair_16_17
  · -- n = 18
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 17 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_18
    · exact pair_1_18
    · exact pair_2_18
    · exact pair_3_18
    · exact pair_4_18
    · exact pair_5_18
    · exact pair_6_18
    · exact pair_7_18
    · exact pair_8_18
    · exact pair_9_18
    · exact pair_10_18
    · exact pair_11_18
    · exact pair_12_18
    · exact pair_13_18
    · exact pair_14_18
    · exact pair_15_18
    · exact pair_16_18
    · exact pair_17_18
  · -- n = 19
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 17 ∨ m = 18 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_19
    · exact pair_1_19
    · exact pair_2_19
    · exact pair_3_19
    · exact pair_4_19
    · exact pair_5_19
    · exact pair_6_19
    · exact pair_7_19
    · exact pair_8_19
    · exact pair_9_19
    · exact pair_10_19
    · exact pair_11_19
    · exact pair_12_19
    · exact pair_13_19
    · exact pair_14_19
    · exact pair_15_19
    · exact pair_16_19
    · exact pair_17_19
    · exact pair_18_19
  · -- n = 20
    have hmd : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 17 ∨ m = 18 ∨ m = 19 := by omega
    rcases hmd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact pair_0_20
    · exact pair_1_20
    · exact pair_2_20
    · exact pair_3_20
    · exact pair_4_20
    · exact pair_5_20
    · exact pair_6_20
    · exact pair_7_20
    · exact pair_8_20
    · exact pair_9_20
    · exact pair_10_20
    · exact pair_11_20
    · exact pair_12_20
    · exact pair_13_20
    · exact pair_14_20
    · exact pair_15_20
    · exact pair_16_20
    · exact pair_17_20
    · exact pair_18_20
    · exact pair_19_20

theorem jsp_000598 :
    ∀ m n, m ≠ n → m ≤ 20 → n ≤ 20 → ¬ samePrimes (centralBinom m) (centralBinom n) := by
  intro m n hneq hm20 hn20
  by_cases hmn : m < n
  · exact jsp_000598_bounded m n hmn hn20
  · have hgt : n < m := by omega
    have hcontra : ¬ samePrimes (centralBinom n) (centralBinom m) := jsp_000598_bounded n m hgt hm20
    intro hsp
    have hspsym : samePrimes (centralBinom n) (centralBinom m) := samePrimes_symm (centralBinom m) (centralBinom n) hsp
    exact hcontra hspsym

#print axioms jsp_000598
