/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Szemeredi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
public import SzemerediWithRandomDifferences.CommonDiffs
import SzemerediWithRandomDifferences.ArithmeticKakeya.Construction
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus
import SzemerediWithRandomDifferences.ArithmeticKakeya.Threshold

/-!
# The Green–Ruzsa construction for arithmetic Kakeya

Small sets of natural numbers containing a `k`-term arithmetic progression with every common
difference in an initial segment. Progressions are `Combinatorics.ArithmeticProgression ℕ k`.

The statement is a theorem of Green and Ruzsa, *On the arithmetic Kakeya conjecture of Katz
and Tao*, in the form given by the construction in Section 5 of the arXiv version. It is
Theorem 1.2 of the arXiv version, [arXiv:1712.02108](https://arxiv.org/abs/1712.02108), and
Theorem 1.7 of the published version, Period. Math. Hungar. (2019),
[doi:10.1007/s10998-018-0270-z](https://doi.org/10.1007/s10998-018-0270-z). It is Theorem 2.2
of Dahia, *Szemerédi's theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859), which cites the published version.

Let `Q` be the product of the first `⌈10 * log k⌉` odd primes. For `d < Q`, take the
progression starting at the residue of `d ^ 2` modulo `Q`, and let `S` be the union of these
progressions. For a fixed `j`, the `j`-th terms satisfy
`4 * (d ^ 2 + j * d) = (2 * d + j) ^ 2 - j ^ 2`, so modulo each prime `p` dividing `Q` they
lie in a set of `(p + 1) / 2` residues. Hence `#S ≤ k ^ 2 * ∏ p, (p + 1) / 2`. The set of
numbers with `t` digits in base `Q`, each digit in `S`, has a progression for every common
difference below `Q ^ t`. Taking `t` minimal with `n < Q ^ t` and shifting by one gives a subset
of `{1, …, k * Q * n}`.

The parameters `modulus`, `c` and `n₀` are defined in
`SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters`.

## Main statements

* `ArithmeticKakeya.exists_card_le_rpow_forall_exists_arithmeticProgression`: for `k ≥ 3` and
  `n ≥ n₀ k`, a subset of `{1, …, k * Q * n}` of size at most `n ^ (1 - c / log (log k))` with
  a `k`-term progression of every common difference in `{1, …, n}`.
* `ArithmeticKakeya.exists_card_le_rpow_forall_mem_commonDiffs`: the same set in `ℤ`, with its
  common differences stated through `Combinatorics.ArithmeticProgression.commonDiffs`.
-/

public section

namespace ArithmeticKakeya

open Combinatorics Finset

/-- **Green–Ruzsa**, Theorem 1.2 of the arXiv version and Theorem 1.7 of the published version.
For `k ≥ 3` and `n ≥ n₀ k`, some `Y ⊆ {1, …, k * Q * n}`
with `#Y ≤ n ^ (1 - c / log (log k))` contains a `k`-term arithmetic progression with every
common difference `d ∈ {1, …, n}`, where `Q = modulus k`. -/
theorem exists_card_le_rpow_forall_exists_arithmeticProgression {k : ℕ} (hk : 3 ≤ k) {n : ℕ}
    (hn : n₀ k ≤ n) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * modulus k * n) ∧
      #Y ≤ (n : ℝ) ^ (1 - c / Real.log (Real.log k)) ∧
      ∀ d ∈ Icc 1 n, ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  have hk0 : k ≠ 0 := by grind
  have hQ : 1 < modulus k := one_lt_modulus (by grind)
  have hn0 : n ≠ 0 := ((pow_pos (modulus_pos k) _).trans_le hn).ne'
  obtain ⟨Y, hY, hcard, hAP⟩ :=
    exists_card_le_pow_log_forall_exists_arithmeticProgression hQ hk0 hn0 fun j _ ↦
      card_residues_modulus_le k j
  refine ⟨Y, hY, ?_, hAP⟩
  apply (Nat.cast_le (α := ℝ).2 hcard).trans
  rw [Nat.cast_pow]
  apply (pow_log_succ_le_mul_rpow (sizeBound_ne_zero hk0) hQ hn0).trans
  exact mul_rpow_le_rpow_of_pow_le (sizeBound_le_modulus hk0) hQ (one_le_mul_saving hk) hn

/-- The Green–Ruzsa theorem for sets of integers: for `k ≥ 3` and `n ≥ n₀ k`, some
`Y ⊆ {1, …, k * Q * n}` with `#Y ≤ n ^ (1 - c / log (log k))` contains a `k`-term arithmetic
progression with every common difference `d ∈ {1, …, n}`, where `Q = modulus k`. -/
lemma exists_card_le_rpow_forall_mem_commonDiffs {k : ℕ} (hk : 3 ≤ k) {n : ℕ}
    (hn : n₀ k ≤ n) :
    ∃ Y : Finset ℤ, Y ⊆ Icc 1 ((k * modulus k * n : ℕ) : ℤ) ∧
      #Y ≤ (n : ℝ) ^ (1 - c / Real.log (Real.log k)) ∧
      ∀ d ∈ Icc 1 (n : ℤ), d ∈ ArithmeticProgression.commonDiffs k Y := by
  obtain ⟨Y, hYM, hcard, hY⟩ := exists_card_le_rpow_forall_exists_arithmeticProgression hk hn
  refine ⟨Y.map Nat.castEmbedding, ?_, by rwa [card_map], ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    grind [hYM hy, Nat.castEmbedding_apply]
  · intro d hd
    lift d to ℕ using (by grind)
    exact ArithmeticProgression.natCast_mem_commonDiffs_map (hY d (by grind))

end ArithmeticKakeya
