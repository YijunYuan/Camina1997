/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.GroupTheory.SparsePowers
public import Camina1997.GroupTheory.WreathSupport

/-!
# Isolating sparse wreath-product commutators

If a base function is supported on one block of sparse powers, the commutator
of two of its translates is supported only at the identity coordinate. It is
trivial unless both translating exponents belong to that block.

Reference: Lubotzky–Wilson (1984), pp. 398–399.
-/

@[expose] public section

open scoped commutatorElement

namespace Camina1997.LubotzkyWilson

open RegularWreathProduct

variable {A : Type*} [Group A] {q r s : ℕ}

/-- A nontrivial translated commutator identifies its block and its sole coordinate. -/
theorem shifted_commutator_support (hq : 2 < q)
    (θ : Multiplicative (ZMod (q ^ (s + 1))) → A)
    (hθ : ∀ z : ZMod (q ^ (s + 1)), θ (Multiplicative.ofAdd z) ≠ 1 →
      ∃ a : ℕ, r < a ∧ a ≤ s ∧ z = (q : ZMod (q ^ (s + 1))) ^ a)
    (i j : ℕ) (k : ZMod (q ^ (s + 1)))
    (hc : ⁅θ (Multiplicative.ofAdd (k + q ^ i)),
      θ (Multiplicative.ofAdd (k + q ^ j))⁆ ≠ 1) :
    r < i ∧ i ≤ s ∧ r < j ∧ j ≤ s ∧ k = 0 := by
  have hi : θ (Multiplicative.ofAdd (k + q ^ i)) ≠ 1 := by
    intro he
    exact hc (by rw [he]; simp [commutatorElement_def])
  have hj : θ (Multiplicative.ofAdd (k + q ^ j)) ≠ 1 := by
    intro he
    exact hc (by rw [he]; simp [commutatorElement_def])
  have hne : k + (q : ZMod (q ^ (s + 1))) ^ i ≠ k + q ^ j := by
    intro he
    exact hc (by rw [he]; simp)
  exact sparse_powers_separation hq k (hθ _ hi) (hθ _ hj) hne

/-- The sparse commutator is the single-coordinate copy of its value at zero. -/
theorem cyclicShift_commutator_eq_single (hq : 2 < q)
    (θ : Multiplicative (ZMod (q ^ (s + 1))) → A)
    (hθ : ∀ z : ZMod (q ^ (s + 1)), θ (Multiplicative.ofAdd z) ≠ 1 →
      ∃ a : ℕ, r < a ∧ a ≤ s ∧ z = (q : ZMod (q ^ (s + 1))) ^ a)
    (i j : ℕ) :
    ⁅cyclicShift (q ^ (s + 1)) (q ^ i) * baseHom θ *
        (cyclicShift (q ^ (s + 1)) (q ^ i))⁻¹,
      cyclicShift (q ^ (s + 1)) (q ^ j) * baseHom θ *
        (cyclicShift (q ^ (s + 1)) (q ^ j))⁻¹⁆ =
      singleHom (1 : Multiplicative (ZMod (q ^ (s + 1))))
        ⁅θ (Multiplicative.ofAdd (q ^ i)), θ (Multiplicative.ofAdd (q ^ j))⁆ := by
  classical
  rw [commutator_cyclicShift_baseHom]
  ext x
  · by_cases hx : x = 1
    · subst x
      rw [baseHom_left, singleHom_left, Pi.mulSingle_eq_same]
      change ⁅θ (Multiplicative.ofAdd (0 + q ^ i)), θ (Multiplicative.ofAdd (0 + q ^ j))⁆ = _
      rw [zero_add, zero_add]
    · have hc : ⁅θ (Multiplicative.ofAdd (x.toAdd + q ^ i)),
          θ (Multiplicative.ofAdd (x.toAdd + q ^ j))⁆ = 1 := by
        by_contra hne
        have hk := (shifted_commutator_support hq θ hθ i j x.toAdd hne).2.2.2.2
        exact hx (congrArg Multiplicative.ofAdd hk)
      rw [baseHom_left, singleHom_left, hc, Pi.mulSingle_eq_of_ne hx]
  · rfl

/-- Exponents outside the support block produce the identity commutator. -/
theorem cyclicShift_commutator_eq_one_of_not_mem (hq : 2 < q)
    (θ : Multiplicative (ZMod (q ^ (s + 1))) → A)
    (hθ : ∀ z : ZMod (q ^ (s + 1)), θ (Multiplicative.ofAdd z) ≠ 1 →
      ∃ a : ℕ, r < a ∧ a ≤ s ∧ z = (q : ZMod (q ^ (s + 1))) ^ a)
    (i j : ℕ) (hij : ¬(r < i ∧ i ≤ s ∧ r < j ∧ j ≤ s)) :
    ⁅cyclicShift (q ^ (s + 1)) (q ^ i) * baseHom θ *
        (cyclicShift (q ^ (s + 1)) (q ^ i))⁻¹,
      cyclicShift (q ^ (s + 1)) (q ^ j) * baseHom θ *
        (cyclicShift (q ^ (s + 1)) (q ^ j))⁻¹⁆ = 1 := by
  rw [cyclicShift_commutator_eq_single hq θ hθ]
  have hc : ⁅θ (Multiplicative.ofAdd (q ^ i)), θ (Multiplicative.ofAdd (q ^ j))⁆ = 1 := by
    by_contra hne
    have hs := shifted_commutator_support hq θ hθ i j 0 (by simpa using hne)
    exact hij ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
  rw [hc, map_one]

end Camina1997.LubotzkyWilson
