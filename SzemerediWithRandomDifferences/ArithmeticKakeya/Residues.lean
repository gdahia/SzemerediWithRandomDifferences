/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Residues of `d ^ 2 + j * d`

The number of residues modulo `Q` taken by `d ^ 2 + j * d` as `d` varies. Completing the square
shows that an odd prime `p` has `(p + 1) / 2` such residues, and the Chinese remainder theorem
makes the count submultiplicative over coprime moduli.

## Main statements

* `ArithmeticKakeya.two_mul_card_residues_le`: at most `(p + 1) / 2` residues modulo an odd
  prime `p`.
* `ArithmeticKakeya.card_residues_prod_le`: the count for a product of pairwise coprime moduli
  is at most the product of the counts.
-/

public section

open Finset

/-- If `f` is invariant under a self-map `σ` of `s` with at most one fixed point, then every
fibre of `f` except possibly one has at least two elements, so `f` takes at most
`(#s + 1) / 2` values on `s`. -/
theorem Finset.two_mul_card_image_le_card_add_one {α β : Type*} [DecidableEq β] {s : Finset α}
    {f : α → β} {σ : α → α} (hσ : ∀ a ∈ s, σ a ∈ s) (hf : ∀ a ∈ s, f (σ a) = f a)
    (hfix : ∀ a ∈ s, ∀ b ∈ s, σ a = a → σ b = b → a = b) : 2 * #(s.image f) ≤ #s + 1 := by
  sorry

namespace ArithmeticKakeya

/-- The residues modulo `Q` of the numbers `d ^ 2 + j * d`. -/
def residues (Q j : ℕ) : Finset ℕ :=
  (range Q).image fun d ↦ (d ^ 2 + j * d) % Q

theorem mem_residues {Q j r : ℕ} : r ∈ residues Q j ↔ ∃ d < Q, (d ^ 2 + j * d) % Q = r := by
  simp [residues]

/-- The residue of `d ^ 2 + j * d` belongs to `residues Q j` for every `d`, not only `d < Q`. -/
theorem mod_mem_residues {Q : ℕ} (hQ : Q ≠ 0) (j d : ℕ) :
    (d ^ 2 + j * d) % Q ∈ residues Q j := by
  sorry

/-- The count of residues is the size of the image of `d ↦ d ^ 2 + j * d` on `ZMod Q`. -/
private theorem card_residues_eq_card_image (Q : ℕ) [NeZero Q] (j : ℕ) :
    #(residues Q j) = #(univ.image fun d : ZMod Q ↦ d ^ 2 + j * d) := by
  sorry

/-- Modulo an odd prime `p`, the polynomial `d ^ 2 + j * d` takes at most `(p + 1) / 2`
values. -/
theorem two_mul_card_residues_le {p : ℕ} (hp : p.Prime) (hodd : Odd p) (j : ℕ) :
    2 * #(residues p j) ≤ p + 1 := by
  sorry

theorem card_residues_mul_le {m n : ℕ} (hmn : m.Coprime n) (j : ℕ) :
    #(residues (m * n) j) ≤ #(residues m j) * #(residues n j) := by
  sorry

theorem card_residues_prod_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : (s : Set ι).Pairwise (Function.onFun Nat.Coprime q)) (j : ℕ) :
    #(residues (∏ i ∈ s, q i) j) ≤ ∏ i ∈ s, #(residues (q i) j) := by
  sorry

end ArithmeticKakeya
