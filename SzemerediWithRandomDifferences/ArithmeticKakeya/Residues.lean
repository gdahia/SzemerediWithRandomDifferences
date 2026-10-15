/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
lemma Finset.two_mul_card_image_le_card_add_one {α β : Type*} [DecidableEq β] {s : Finset α}
    {f : α → β} {σ : α → α} (hσ : ∀ a ∈ s, σ a ∈ s) (hf : ∀ a ∈ s, f (σ a) = f a)
    (hfix : ∀ a ∈ s, ∀ b ∈ s, σ a = a → σ b = b → a = b) : 2 * #(s.image f) ≤ #s + 1 := by
  classical
  have key : ∀ b ∈ s.image f,
      2 ≤ #{a ∈ s | f a = b} + if b ∈ image f {a ∈ s | σ a = a} then 1 else 0 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    split_ifs with h
    · exact Nat.succ_le_succ (card_pos.2 ⟨a, by grind⟩)
    · exact one_lt_card.2 ⟨σ a, by grind, a, by grind, by grind⟩
  have h := sum_le_sum key
  rw [sum_const, smul_eq_mul, sum_add_distrib, ← card_eq_sum_card_image, ← card_filter] at h
  apply (mul_comm 2 _).trans_le (h.trans (Nat.add_le_add_left _ _))
  apply (card_le_card (t := image f {a ∈ s | σ a = a}) (by grind)).trans
  apply card_image_le.trans
  apply card_le_one.2
  grind

namespace ArithmeticKakeya

/-- The residues modulo `Q` of the numbers `d ^ 2 + j * d`. -/
def residues (Q j : ℕ) : Finset ℕ :=
  (range Q).image fun d ↦ (d ^ 2 + j * d) % Q

lemma mem_residues {Q j r : ℕ} : r ∈ residues Q j ↔ ∃ d < Q, (d ^ 2 + j * d) % Q = r := by
  simp [residues]

/-- The residue of `d ^ 2 + j * d` belongs to `residues Q j` for every `d`, not only `d < Q`. -/
lemma mod_mem_residues {Q : ℕ} (hQ : Q ≠ 0) (j d : ℕ) : (d ^ 2 + j * d) % Q ∈ residues Q j := by
  rw [mem_residues]
  refine ⟨d % Q, Nat.mod_lt _ (by grind), ?_⟩
  exact ((Nat.mod_modEq d Q).pow 2).add ((Nat.mod_modEq d Q).mul_left j)

/-- The count of residues is the size of the image of `d ↦ d ^ 2 + j * d` on `ZMod Q`. -/
private lemma card_residues_eq_card_image (Q : ℕ) [NeZero Q] (j : ℕ) :
    #(residues Q j) = #(univ.image fun d : ZMod Q ↦ d ^ 2 + j * d) := by
  rw [← card_image_of_injective _ (ZMod.val_injective Q)]
  congr 1
  ext r
  simp only [mem_residues, mem_image, mem_univ, true_and, exists_exists_eq_and]
  constructor
  · rintro ⟨d, -, rfl⟩
    exact ⟨d, mod_cast ZMod.val_natCast Q (d ^ 2 + j * d)⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨d, hd, rfl⟩ : ∃ d < Q, (d : ZMod Q) = x := ⟨x.val, x.val_lt, x.natCast_zmod_val⟩
    exact ⟨d, hd, mod_cast (ZMod.val_natCast Q (d ^ 2 + j * d)).symm⟩

/-- Modulo an odd prime `p`, the polynomial `d ^ 2 + j * d` takes at most `(p + 1) / 2`
values. -/
lemma two_mul_card_residues_le {p : ℕ} (hp : p.Prime) (hodd : Odd p) (j : ℕ) :
    2 * #(residues p j) ≤ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [← Nat.cast_ofNat, Ne, ZMod.natCast_eq_zero_iff,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    grind
  rw [card_residues_eq_card_image]
  refine (two_mul_card_image_le_card_add_one (σ := fun d : ZMod p ↦ -j - d) ?_ ?_ ?_).trans_eq
    (by simp [ZMod.card])
  · simp
  · intro a _
    ring
  · intro a _ b _ ha hb
    apply mul_left_cancel₀ h2
    linear_combination hb - ha

lemma card_residues_mul_le {m n : ℕ} (hmn : m.Coprime n) (j : ℕ) :
    #(residues (m * n) j) ≤ #(residues m j) * #(residues n j) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [residues]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [residues]
  rw [← card_product]
  apply card_le_card_of_injOn fun r ↦ (r % m, r % n)
  · intro r hr
    obtain ⟨d, -, rfl⟩ := mem_residues.1 hr
    simp only [mem_coe, mem_product, Nat.mod_mul_right_mod, Nat.mod_mul_left_mod]
    exact ⟨mod_mem_residues hm.ne' j d, mod_mem_residues hn.ne' j d⟩
  · intro a ha b hb hab
    obtain ⟨d, -, rfl⟩ := mem_residues.1 ha
    obtain ⟨e, -, rfl⟩ := mem_residues.1 hb
    rw [Prod.mk.injEq] at hab
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hmn).1 hab).eq_of_lt_of_lt
      (Nat.mod_lt _ (Nat.mul_pos hm hn)) (Nat.mod_lt _ (Nat.mul_pos hm hn))

lemma card_residues_prod_le {ι : Type*} {s : Finset ι} {q : ι → ℕ}
    (hq : (s : Set ι).Pairwise (Function.onFun Nat.Coprime q)) (j : ℕ) :
    #(residues (∏ i ∈ s, q i) j) ≤ ∏ i ∈ s, #(residues (q i) j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [residues]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    refine (card_residues_mul_le (Nat.coprime_prod_right_iff.2 ?_) j).trans
      (Nat.mul_le_mul_left _ (ih (hq.mono (by simp))))
    intro i hi
    exact hq (mem_insert_self a s) (mem_insert_of_mem hi) (by grind)

end ArithmeticKakeya
