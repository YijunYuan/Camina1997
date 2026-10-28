/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.GroupTheory.FiniteDerived

/-!
# Supported elements and commutators in regular wreath products

Conjugation by an acting element translates the base function. Two such
translates have the coordinatewise commutator used in the Lubotzky–Wilson
construction.
-/

@[expose] public section

open scoped commutatorElement

namespace RegularWreathProduct

variable {A Q : Type*} [Group A] [Group Q]

/-- Conjugation translates the argument of a base function. -/
theorem conjugate_inl_baseHom (q : Q) (f : Q → A) :
    (inl q : A ≀ᵣ Q) * baseHom f * (inl q)⁻¹ =
      baseHom (fun x => f (q⁻¹ * x)) := by
  ext x <;> simp

/-- The commutator of two base functions is computed pointwise. -/
theorem commutator_baseHom (f g : Q → A) :
    ⁅baseHom f, baseHom g⁆ = baseHom (fun x => ⁅f x, g x⁆) := by
  ext x <;> simp [commutatorElement_def]

/-- The commutator of translated base functions has an explicit coordinate formula. -/
theorem commutator_conjugate_inl_baseHom (q r : Q) (f : Q → A) :
    ⁅(inl q : A ≀ᵣ Q) * baseHom f * (inl q)⁻¹,
      (inl r : A ≀ᵣ Q) * baseHom f * (inl r)⁻¹⁆ =
      baseHom (fun x => ⁅f (q⁻¹ * x), f (r⁻¹ * x)⁆) := by
  rw [conjugate_inl_baseHom, conjugate_inl_baseHom, commutator_baseHom]

/-- The cyclic acting element whose conjugation shifts the base argument forward by `k`. -/
def cyclicShift (n : ℕ) (k : ZMod n) : A ≀ᵣ Multiplicative (ZMod n) :=
  inl (Multiplicative.ofAdd (-k))

@[simp]
theorem cyclicShift_zero (n : ℕ) : cyclicShift (A := A) n 0 = 1 := by
  simp [cyclicShift]

theorem cyclicShift_add (n : ℕ) (i j : ZMod n) :
    cyclicShift (A := A) n (i + j) = cyclicShift n i * cyclicShift n j := by
  ext <;> simp [cyclicShift, add_comm]

theorem cyclicShift_one_pow (n m : ℕ) :
    cyclicShift (A := A) n 1 ^ m = cyclicShift n (m : ZMod n) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← cyclicShift_add, Nat.cast_add, Nat.cast_one]

/-- Cyclic shifts have the forward-translation commutator convention of Lubotzky–Wilson. -/
theorem commutator_cyclicShift_baseHom (n : ℕ) (i j : ZMod n)
    (f : Multiplicative (ZMod n) → A) :
    ⁅cyclicShift n i * baseHom f * (cyclicShift n i)⁻¹,
      cyclicShift n j * baseHom f * (cyclicShift n j)⁻¹⁆ =
      baseHom (fun x => ⁅f (Multiplicative.ofAdd (x.toAdd + i)),
        f (Multiplicative.ofAdd (x.toAdd + j))⁆) := by
  rw [cyclicShift, cyclicShift, commutator_conjugate_inl_baseHom]
  congr 1
  funext x
  simp [add_comm]

/-- Put a base-group element at one coordinate of the regular wreath product. -/
def singleHom [DecidableEq Q] (x : Q) : A →* (A ≀ᵣ Q) :=
  baseHom.comp (MonoidHom.mulSingle (fun _ : Q => A) x)

@[simp]
theorem singleHom_left [DecidableEq Q] (x : Q) (a : A) :
    (singleHom x a).left = Pi.mulSingle x a := rfl

@[simp]
theorem singleHom_right [DecidableEq Q] (x : Q) (a : A) :
    (singleHom x a).right = 1 := rfl

theorem singleHom_injective [DecidableEq Q] (x : Q) :
    Function.Injective (singleHom (A := A) x) := by
  intro a b h
  have he := congrArg (fun w : A ≀ᵣ Q => w.left x) h
  simpa only [singleHom_left, Pi.mulSingle_eq_same] using he

end RegularWreathProduct
