/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Szemeredi
public import Mathlib.Algebra.Ring.CharZero

/-!
# Common differences of the arithmetic progressions in a set

`Combinatorics.ArithmeticProgression.commonDiffs k S` is the set of common differences of the
`k`-term arithmetic progressions with nonzero common difference contained in `S`. As for
`Combinatorics.ArithmeticProgression.IsSubset`, `S` is a set, a finset, or any other collection
with a membership relation.
-/

@[expose] public section

namespace Combinatorics.ArithmeticProgression

variable {α β γ : Type*} [AddMonoid α] [Membership α β] [Membership α γ]

/-- The common differences of the `k`-term arithmetic progressions contained in `S`. -/
def commonDiffs (k : ℕ) (S : β) : Set α :=
  {d | ∃ P : ArithmeticProgression α k, P.diff = d ∧ P.IsSubset S}

lemma commonDiffs_mono (k : ℕ) {S : β} {T : γ} (h : ∀ x ∈ S, x ∈ T) :
    commonDiffs k S ⊆ commonDiffs k T := by
  rintro d ⟨P, rfl, hP⟩
  refine ⟨P, rfl, ?_⟩
  intro i
  exact h _ (hP i)

lemma mem_commonDiffs {α β : Type*} [Semiring α] [Membership α β] {k : ℕ} {S : β} {d : α} :
    d ∈ commonDiffs k S ↔ d ≠ 0 ∧ ∃ a, ∀ i < k, a + i * d ∈ S := by
  constructor
  · rintro ⟨P, rfl, hP⟩
    refine ⟨P.diff_ne_zero, P.start, ?_⟩
    intro i hi
    simpa [term] using hP ⟨i, hi⟩
  · rintro ⟨hd, a, ha⟩
    refine ⟨⟨a, d, hd⟩, rfl, ?_⟩
    intro i
    simpa [term] using ha i i.isLt

lemma disjoint_commonDiffs {α β : Type*} [Semiring α] [Membership α β] {k : ℕ} {S : β}
    {D : Set α} :
    Disjoint (commonDiffs k S) D ↔ ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S := by
  simp [Set.disjoint_right, mem_commonDiffs]

/-- A common difference of a set of natural numbers is a common difference of its image in a
semiring of characteristic zero, such as `ℤ`. -/
lemma natCast_mem_commonDiffs_map {α : Type*} [Semiring α] [CharZero α] {k : ℕ}
    {S : Finset ℕ} {d : ℕ} (h : d ∈ commonDiffs k S) :
    (d : α) ∈ commonDiffs k (S.map Nat.castEmbedding) := by
  obtain ⟨hd, a, ha⟩ := mem_commonDiffs.1 h
  refine mem_commonDiffs.2 ⟨by simpa, a, ?_⟩
  intro i hi
  exact Finset.mem_map.2 ⟨a + i * d, ha i hi, by simp⟩

end Combinatorics.ArithmeticProgression
