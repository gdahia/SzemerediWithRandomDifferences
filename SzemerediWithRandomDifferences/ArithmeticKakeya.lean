/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Defs
public import SzemerediWithRandomDifferences.ArithmeticProgression
import SzemerediWithRandomDifferences.ArithmeticKakeya.Construction
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus
import SzemerediWithRandomDifferences.ArithmeticKakeya.Threshold

/-!
# The Green–Ruzsa construction for arithmetic Kakeya

Small sets of natural numbers containing a `k`-term arithmetic progression with every common
difference in an initial segment. Progressions are `Combinatorics.ArithmeticProgression ℕ k`.

The statement is Theorem 1.2 of Green and Ruzsa, *On the arithmetic Kakeya conjecture of Katz
and Tao*, [arXiv:1712.02108](https://arxiv.org/abs/1712.02108), in the form given by the
construction in Section 5 of that paper.

Let `Q` be the product of the first `⌈10 * log k⌉` odd primes. For `d < Q`, take the
progression starting at the residue of `d ^ 2` modulo `Q`, and let `S` be the union of these
progressions. For a fixed `j`, the `j`-th terms satisfy
`4 * (d ^ 2 + j * d) = (2 * d + j) ^ 2 - j ^ 2`, so modulo each prime `p` dividing `Q` they
lie in a set of `(p + 1) / 2` residues. Hence `#S ≤ k ^ 2 * ∏ p, (p + 1) / 2`. The set of
numbers with `t` digits in base `Q`, each digit in `S`, has a progression for every common
difference below `Q ^ t`. Taking `t` minimal with `n < Q ^ t` and shifting by one gives a subset
of `{1, …, k * Q * n}`.

The parameters `modulus`, `c` and `n₀` are defined in
`SzemerediWithRandomDifferences.ArithmeticKakeya.Defs`.

## Main statements

* `ArithmeticKakeya.exists_subset_Icc_card_le_rpow`: for `k ≥ 3` and `n ≥ n₀ k`, a subset of
  `{1, …, k * Q * n}` of size at most `n ^ (1 - c / log (log k))` with a `k`-term progression
  of every common difference in `{1, …, n}`.
-/

public section

namespace ArithmeticKakeya

open Combinatorics Finset

/-- **Green–Ruzsa**, Theorem 1.2. For `k ≥ 3` and `n ≥ n₀ k`, some `Y ⊆ {1, …, k * Q * n}`
with `#Y ≤ n ^ (1 - c / log (log k))` contains a `k`-term arithmetic progression with every
common difference `d ∈ {1, …, n}`, where `Q = modulus k`. -/
theorem exists_subset_Icc_card_le_rpow {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hn : n₀ k ≤ n) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * modulus k * n) ∧
      #Y ≤ (n : ℝ) ^ (1 - c / Real.log (Real.log k)) ∧
      ∀ d ∈ Icc 1 n, ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  have hk0 : k ≠ 0 := by omega
  have hQ : 1 < modulus k := one_lt_modulus (by omega)
  have hB : sizeBound k ≠ 0 := sizeBound_ne_zero hk0
  have hn0 : n ≠ 0 := (Nat.pos_of_ne_zero (pow_ne_zero _ (by omega)) |>.trans_le hn).ne'
  obtain ⟨Y, hY, hcard, hAP⟩ :=
    exists_subset_Icc_card_le_pow_log hQ hk0 hn0 fun j _ ↦ card_residues_modulus_le k j
  refine ⟨Y, hY, ?_, hAP⟩
  calc (#Y : ℝ)
      ≤ (sizeBound k : ℝ) ^ (Nat.log (modulus k) n + 1) := mod_cast hcard
    _ ≤ sizeBound k * (n : ℝ) ^ (Real.log (sizeBound k) / Real.log (modulus k)) :=
      pow_log_succ_le_mul_rpow hB hQ hn0
    _ ≤ (n : ℝ) ^ (1 - c / Real.log (Real.log k)) :=
      mul_rpow_le_rpow_of_pow_le hB (sizeBound_le_modulus hk0) hQ (one_le_mul_saving hk) hn

end ArithmeticKakeya
