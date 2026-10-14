/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.RandomDifferences

/-!
# Proof of Szemerédi's theorem with random differences

This module proves the declaration stated in `Challenge.lean`, Theorem 1.1 of Dahia,
*Szemerédi's theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859), deriving it from
`RandomDifferences.setBernoulli_isAvoidable_le_exp`. The constant `c` is `ArithmeticKakeya.c`.

The random set of differences is Mathlib's `setBer(Set.Icc 1 n, p)`, the distribution of the
subset of `{1, …, n}` that contains each element independently with probability `p`. A `k`-term
arithmetic progression with first term `a` and common difference `d ≠ 0` consists of the numbers
`a + i * d` for `i < k`.
-/

@[expose] public section

open Finset ProbabilityTheory unitInterval

namespace RandomDifferences

/-- The constant in the exponent of the threshold. -/
noncomputable def c : ℝ := 1 / 100

/-- The constant in the threshold for progressions of length `k` in sets of density `δ`. -/
noncomputable def C (k : ℕ) (δ : ℝ) : ℝ := ack (4 * k + 2) (k + ⌈2 / δ⌉₊)

/-- **Szemerédi's theorem with random differences.** Let `k ≥ 3` and `δ > 0`, and let `D` be a
`p`-random subset of `{1, …, n}`, where `p ≥ C k δ * n ^ (-c / log (log k))`. The probability
that some subset of `{1, …, n}` with at least `δ * n` elements contains no `k`-term arithmetic
progression with common difference in `D` is at most `exp (-n ^ (1 - c / log (log k)))`. -/
theorem szemeredi_setBernoulli_exists_avoiding_le_exp {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} {p : I} (hp : C k δ * n ^ (-c / Real.log (Real.log k)) ≤ p) :
    setBer(Set.Icc 1 n, p)
      {D | ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧
        ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S} ≤
      ENNReal.ofReal (Real.exp (-n ^ (1 - c / Real.log (Real.log k)))) := by
  simp only [← isAvoidable_iff]
  exact setBernoulli_isAvoidable_le_exp hk hδ hp

end RandomDifferences
