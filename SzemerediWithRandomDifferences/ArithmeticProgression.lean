/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Arithmetic progressions

Nonconstant arithmetic progressions of a fixed length `k` in an additive monoid, given by an
initial term and a nonzero common difference.
-/

@[expose] public section

namespace Combinatorics

/-- A nonconstant arithmetic progression of length `k` in an additive monoid. -/
@[ext]
structure ArithmeticProgression (α : Type*) [AddMonoid α] (k : ℕ) where
  /-- The initial term of the arithmetic progression. -/
  start : α
  /-- The common difference of the arithmetic progression. -/
  diff : α
  diff_ne_zero : diff ≠ 0

namespace ArithmeticProgression

/-- The term of `P` indexed by `i`. -/
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff

/-- The proposition that every term of `P` belongs to `s`, where `s` is a set, a finset, or
any other collection with a membership relation. -/
def IsSubset {α β : Type*} [AddMonoid α] [Membership α β] {k : ℕ}
    (P : ArithmeticProgression α k) (s : β) : Prop :=
  ∀ i, P.term i ∈ s

end ArithmeticProgression
end Combinatorics
