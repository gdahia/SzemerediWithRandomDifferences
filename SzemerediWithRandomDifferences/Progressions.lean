/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval

/-!
# Progressions in a subset of `{1, …, n}`

`RandomDifferences.progressions k n S` is the set of pairs `(a, d)` with `a` and `d` in
`{1, …, n}` such that `S` contains the `k`-term arithmetic progression `a + i * d`, `i < k`.
Varnavides' theorem bounds its size from below, and the pigeonhole argument over translates
uses it to find many common differences.
-/

public section

namespace RandomDifferences

open Finset

/-- The pairs `(a, d)` with `a` and `d` in `{1, …, n}` such that `a + i * d ∈ S` for `i < k`. -/
def progressions (k n : ℕ) (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (Icc 1 (n : ℤ) ×ˢ Icc 1 (n : ℤ)).filter fun (a, d) ↦ ∀ i < k, a + i * d ∈ S

lemma mem_progressions {k n : ℕ} {S : Finset ℤ} {a d : ℤ} :
    (a, d) ∈ progressions k n S ↔
      a ∈ Icc 1 (n : ℤ) ∧ d ∈ Icc 1 (n : ℤ) ∧ ∀ i < k, a + i * d ∈ S := by
  simp [progressions, and_assoc]

end RandomDifferences
