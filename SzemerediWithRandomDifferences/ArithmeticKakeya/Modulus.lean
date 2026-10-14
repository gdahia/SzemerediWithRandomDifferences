/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev

/-!
# Estimates for the Green–Ruzsa modulus

Bounds relating `modulus k`, the product of the first `⌈10 * log k⌉` odd primes, to
`sizeBound k`, and an upper bound on its logarithm.

## Main statements

* `ArithmeticKakeya.card_residues_modulus_le`: `d ^ 2 + j * d` takes at most
  `∏ p ∣ Q, (p + 1) / 2` residues modulo `Q = modulus k`.
* `ArithmeticKakeya.sizeBound_mul_pow_le_modulus`: `sizeBound k * k ^ 3 ≤ modulus k`.
* `Nat.nth_prime_le_add_two_sq`: the prime of index `n` is at most `(n + 2) ^ 2`.
* `ArithmeticKakeya.log_modulus_le`: `log (modulus k) ≤ 22 * log k * (log (log k) + 13 / 5)`.
* `ArithmeticKakeya.modulus_le`: `modulus k ≤ ((10 * k + 2) ^ 2) ^ (10 * k)`.
-/

public section

private lemma sq_lt_two_pow_add_one (m : ℕ) : m ^ 2 < 2 ^ (m + 1) := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m <;> norm_num
  · induction m, h using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ 2]
      nlinarith [Nat.mul_le_mul_right m hm]

private lemma two_mul_log_lt {m : ℕ} (hm : m ≠ 0) :
    2 * Real.log m < (m + 1) * Real.log 2 := by
  have h := Real.log_lt_log (by positivity) (Nat.cast_lt (α := ℝ).2 (sq_lt_two_pow_add_one m))
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

private lemma log_sq_add_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x ^ 2 + 1) ≤ Real.log 2 + 2 * Real.log x := by
  have h := Real.log_le_log (by positivity) (by nlinarith : x ^ 2 + 1 ≤ 2 * x ^ 2)
  rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h

private lemma lt_primeCounting_sq_add_two {m : ℕ} (hm : 2 ≤ m) :
    m < Nat.primeCounting (m ^ 2) + 2 := by
  by_contra! h
  have hx : (2 : ℝ) ≤ m := mod_cast hm
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hπ := Chebyshev.pi_ge (m ^ 2)
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, div_le_iff₀ (by positivity)] at hπ
  rw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.cast_ofNat] at h
  linarith [log_sq_add_one_le (by linarith : (1 : ℝ) ≤ m),
    mul_lt_mul_of_pos_left (two_mul_log_lt (by grind : m ≠ 0)) (by linarith : (0 : ℝ) < m - 1),
    mul_le_mul_of_nonneg_right h hlog.le]

/-- A polynomial bound on the primes, from Chebyshev's lower bound on the prime counting
function. -/
lemma Nat.nth_prime_le_add_two_sq (n : ℕ) : Nat.nth Nat.Prime n ≤ (n + 2) ^ 2 := by
  apply Nat.lt_succ_iff.1
  apply Nat.nth_lt_of_lt_count
  exact Nat.lt_of_add_lt_add_right (lt_primeCounting_sq_add_two (Nat.le_add_left 2 n))

namespace ArithmeticKakeya

open Finset

/-! ### The odd primes -/

private lemma nth_prime_eq (n p : ℕ) (hp : p.Prime) (hn : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := by
  rw [← hn, Nat.nth_count hp]

private lemma two_lt_nth_prime_succ (i : ℕ) : 2 < Nat.nth Nat.Prime (i + 1) := by
  rw [← Nat.nth_prime_zero_eq_two]
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime i.succ_pos

private lemma odd_nth_prime_succ (i : ℕ) : Odd (Nat.nth Nat.Prime (i + 1)) :=
  (Nat.prime_nth_prime (i + 1)).odd_of_ne_two (two_lt_nth_prime_succ i).ne'

private lemma seven_le_nth_prime {i : ℕ} (hi : 3 ≤ i) : 7 ≤ Nat.nth Nat.Prime i := by
  rw [← nth_prime_eq 3 7 (by decide) (by decide)]
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hi

private lemma nth_prime_succ_le_sq {i m : ℕ} (hi : i < m) :
    Nat.nth Nat.Prime (i + 1) ≤ (m + 2) ^ 2 :=
  (Nat.nth_prime_le_add_two_sq (i + 1)).trans (Nat.pow_le_pow_left (by grind) 2)

private lemma prod_range_eleven_nth_prime (f : ℕ → ℕ) :
    ∏ i ∈ range 11, f (Nat.nth Nat.Prime (i + 1)) =
      f 3 * f 5 * f 7 * f 11 * f 13 * f 17 * f 19 * f 23 * f 29 * f 31 * f 37 := by
  simp [prod_range_succ,
    nth_prime_eq 1 3 (by decide) (by decide), nth_prime_eq 2 5 (by decide) (by decide),
    nth_prime_eq 3 7 (by decide) (by decide), nth_prime_eq 4 11 (by decide) (by decide),
    nth_prime_eq 5 13 (by decide) (by decide), nth_prime_eq 6 17 (by decide) (by decide),
    nth_prime_eq 7 19 (by decide) (by decide), nth_prime_eq 8 23 (by decide) (by decide),
    nth_prime_eq 9 29 (by decide) (by decide), nth_prime_eq 10 31 (by decide) (by decide),
    nth_prime_eq 11 37 (by decide) (by decide)]

/-! ### Basic properties -/

lemma modulus_pos (k : ℕ) : 0 < modulus k := by
  apply prod_pos
  intro i _
  exact (Nat.prime_nth_prime _).pos

lemma one_lt_modulus {k : ℕ} (hk : 2 ≤ k) : 1 < modulus k := by
  apply (one_lt_two.trans (two_lt_nth_prime_succ 0)).trans_le
  apply Nat.le_of_dvd (modulus_pos k)
  apply dvd_prod_of_mem fun i ↦ Nat.nth Nat.Prime (i + 1)
  rw [mem_range, Nat.ceil_pos]
  exact mul_pos (by norm_num) (Real.log_pos (mod_cast hk))

lemma sizeBound_ne_zero {k : ℕ} (hk : k ≠ 0) : sizeBound k ≠ 0 := by
  rw [sizeBound]
  apply mul_ne_zero (pow_ne_zero 2 hk)
  rw [prod_ne_zero_iff]
  intro i _
  grind [two_lt_nth_prime_succ i]

lemma card_residues_modulus_le (k j : ℕ) :
    #(residues (modulus k) j) ≤
      ∏ i ∈ range ⌈10 * Real.log k⌉₊, (Nat.nth Nat.Prime (i + 1) + 1) / 2 := by
  rw [modulus]
  refine (card_residues_prod_le ?_ j).trans (prod_le_prod ?_)
  · intro a _ b _ hab
    exact (Nat.coprime_primes (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)).2
      ((Nat.nth_injective Nat.infinite_setOfPred_prime).ne (by grind))
  · intro i _
    grind [two_mul_card_residues_le (Nat.prime_nth_prime (i + 1)) (odd_nth_prime_succ i) j]

/-! ### Comparison with `sizeBound` -/

private lemma seven_mul_le {p : ℕ} (hp : 7 ≤ p) : 7 * ((p + 1) / 2) ≤ 4 * p := by
  grind

private lemma five_mul_seven_pow_mul_prod_le (n : ℕ) :
    5 * 7 ^ n * ∏ i ∈ range (n + 2), (Nat.nth Nat.Prime (i + 1) + 1) / 2 ≤
      2 * 4 ^ n * ∏ i ∈ range (n + 2), Nat.nth Nat.Prime (i + 1) := by
  induction n with
  | zero =>
    simp [prod_range_succ, nth_prime_eq 1 3 (by decide) (by decide),
      nth_prime_eq 2 5 (by decide) (by decide)]
  | succ n ih =>
    rw [prod_range_succ _ (n + 2), prod_range_succ _ (n + 2)]
    convert Nat.mul_le_mul ih (seven_mul_le (seven_le_nth_prime (i := n + 2 + 1) (by grind)))
      using 1 <;> ring

private lemma four_le_ceil {k : ℕ} (hk : 2 ≤ k) : 4 ≤ ⌈10 * Real.log k⌉₊ := by
  apply Nat.lt_ceil.2
  rw [Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9, Real.log_le_log two_pos (mod_cast hk : (2 : ℝ) ≤ k)]

private lemma exp_half_le : Real.exp (1 / 2) ≤ 33 / 20 := by
  rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero, ← Real.exp_nat_mul]
  norm_num
  linarith [Real.exp_one_lt_d9]

private lemma pow_five_le_pow_ceil {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) ^ 5 ≤ (33 / 20) ^ ⌈10 * Real.log k⌉₊ := by
  apply le_trans _ (pow_le_pow_left₀ (Real.exp_pos _).le exp_half_le _)
  rw [← Real.exp_nat_mul, ← Real.exp_log (by positivity : (0 : ℝ) < k ^ 5), Real.exp_le_exp,
    Real.log_pow, Nat.cast_ofNat]
  linarith [Nat.le_ceil (10 * Real.log k)]

private lemma pow_add_two_add_two_le (n : ℕ) :
    ((33 : ℝ) / 20) ^ (n + 2 + 2) ≤ 5 / 2 * (7 / 4) ^ (n + 2) := by
  rw [pow_add, pow_add, pow_add]
  linarith [pow_le_pow_left₀ (by norm_num) (by norm_num : (33 : ℝ) / 20 ≤ 7 / 4) n,
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4) n]

private lemma two_mul_four_pow_mul_pow_le {k n : ℕ} (hk : 2 ≤ k)
    (hn : ⌈10 * Real.log k⌉₊ = n + 2 + 2) : 2 * 4 ^ (n + 2) * k ^ 5 ≤ 5 * 7 ^ (n + 2) := by
  have h := pow_five_le_pow_ceil (by grind : k ≠ 0)
  rw [hn] at h
  have h' := h.trans (pow_add_two_add_two_le n)
  rw [div_pow, div_mul_div_comm, le_div_iff₀ (by positivity), mul_comm] at h'
  exact_mod_cast h'

/-- Each factor `2 * p / (p + 1)` of `modulus k / sizeBound k * k ^ 2` is at least `7 / 4`,
except for `p = 3` and `p = 5`, while `k ^ 5 ≤ e ^ (m / 2) ≤ (33 / 20) ^ m` for
`m = ⌈10 * log k⌉`. -/
lemma sizeBound_mul_pow_le_modulus (k : ℕ) : sizeBound k * k ^ 3 ≤ modulus k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [sizeBound, modulus]
  obtain ⟨n, hn⟩ : ∃ n, ⌈10 * Real.log k⌉₊ = n + 2 + 2 :=
    ⟨⌈10 * Real.log k⌉₊ - 4, by grind [four_le_ceil hk]⟩
  rw [sizeBound, modulus, hn]
  refine Nat.le_of_mul_le_mul_left (c := 5 * 7 ^ (n + 2) * (2 * 4 ^ (n + 2))) ?_ (by positivity)
  convert Nat.mul_le_mul (five_mul_seven_pow_mul_prod_le (n + 2))
    (two_mul_four_pow_mul_pow_le hk hn) using 1 <;> ring

lemma sizeBound_le_modulus {k : ℕ} (hk : k ≠ 0) : sizeBound k ≤ modulus k :=
  (Nat.le_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero hk) 3)).trans
    (sizeBound_mul_pow_le_modulus k)

/-! ### The logarithm of the modulus -/

private lemma log_thirteen_le : Real.log 13 ≤ 13 / 5 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13 / 2 ^ 4)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow, Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

private lemma log_nth_prime_succ_le {i m : ℕ} (hi : i < m) :
    Real.log (Nat.nth Nat.Prime (i + 1)) ≤ 2 * Real.log (m + 2) := by
  have h := Real.log_le_log (Nat.cast_pos.2 (Nat.prime_nth_prime (i + 1)).pos)
    (Nat.cast_le (α := ℝ).2 (nth_prime_succ_le_sq hi))
  rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat] at h

private lemma log_ceil_add_two_le {L : ℝ} (hL : 1 ≤ L) :
    Real.log (⌈10 * L⌉₊ + 2) ≤ Real.log L + 13 / 5 := by
  have hL0 : 0 < L := by linarith
  have h := Real.log_le_log (by positivity)
    (by linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 10 * L)] : (⌈10 * L⌉₊ : ℝ) + 2 ≤ 13 * L)
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  linarith [log_thirteen_le]

lemma one_le_log_of_three_le {k : ℕ} (hk : 3 ≤ k) : 1 ≤ Real.log k := by
  linarith [Real.log_three_gt_d9, Real.log_le_log three_pos (mod_cast hk : (3 : ℝ) ≤ k)]

lemma log_modulus_le {k : ℕ} (hk : 3 ≤ k) :
    Real.log (modulus k) ≤ 22 * Real.log k * (Real.log (Real.log k) + 13 / 5) := by
  have hL := one_le_log_of_three_le hk
  have hLL := Real.log_nonneg hL
  rw [modulus, Nat.cast_prod, Real.log_prod]
  · apply (sum_le_sum (g := fun _ ↦ 2 * (Real.log (Real.log k) + 13 / 5)) ?_).trans
    · rw [sum_const, card_range, nsmul_eq_mul]
      linarith [mul_le_mul_of_nonneg_right
        (by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ 10 * Real.log k)] :
          (⌈10 * Real.log k⌉₊ : ℝ) ≤ 11 * Real.log k)
        (by linarith : 0 ≤ Real.log (Real.log k) + 13 / 5)]
    · intro i hi
      linarith [log_nth_prime_succ_le (mem_range.1 hi), log_ceil_add_two_le hL]
  · intro i _
    exact mod_cast (Nat.prime_nth_prime _).ne_zero

/-- A crude bound on the modulus, with no logarithm. -/
lemma modulus_le (k : ℕ) : modulus k ≤ ((10 * k + 2) ^ 2) ^ (10 * k) := by
  have hr : ⌈10 * Real.log k⌉₊ ≤ 10 * k := by
    rw [Nat.ceil_le, Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg k)) (by norm_num)
  apply (prod_le_prod fun i hi ↦ nth_prime_succ_le_sq (mem_range.1 hi)).trans
  rw [prod_const, card_range]
  apply (Nat.pow_le_pow_right (by positivity) hr).trans
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_left (by grind) 2) _

/-! ### The case `k = 3` -/

lemma ceil_ten_mul_log_three : ⌈10 * Real.log 3⌉₊ = 11 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num <;> linarith [Real.log_three_gt_d9, Real.log_three_lt_d9]

lemma modulus_three : modulus 3 = 3710369067405 := by
  rw [modulus, Nat.cast_ofNat, ceil_ten_mul_log_three]
  exact prod_range_eleven_nth_prime fun p ↦ p

lemma sizeBound_three : sizeBound 3 = 44677785600 := by
  rw [sizeBound, Nat.cast_ofNat, ceil_ten_mul_log_three]
  exact congrArg (3 ^ 2 * ·) (prod_range_eleven_nth_prime fun p ↦ (p + 1) / 2)

end ArithmeticKakeya
