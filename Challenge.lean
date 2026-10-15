/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Computability.Ackermann
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Szemerédi's theorem with random differences

The threshold `p ≥ C * n ^ (-c / log (log k))` for Szemerédi's theorem with random differences,
with `c = 1 / 100` and `C` a value of the Ackermann function `ack`. This is Theorem 1.1 of
Dahia, *Szemerédi's theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859), with explicit constants. No lower bound on
`n` is assumed, since `p ≤ 1` forces `n ≥ C`. This module imports Mathlib alone and the proof is
in the companion `Solution` module.

Sets of numbers are sets of integers. The random set of differences is Mathlib's
`setBer(Set.Icc 1 (n : ℤ), p)`, the distribution of the subset of `{1, …, n}` that contains each
element independently with probability `p`. A `k`-term
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
    setBer(Set.Icc 1 (n : ℤ), p)
      {D | ∃ S : Finset ℤ, S ⊆ Icc 1 (n : ℤ) ∧ δ * n ≤ #S ∧
        ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S} ≤
      ENNReal.ofReal (Real.exp (-n ^ (1 - c / Real.log (Real.log k)))) :=
  sorry

end RandomDifferences
