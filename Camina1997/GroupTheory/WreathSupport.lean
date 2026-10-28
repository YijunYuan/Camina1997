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

end RegularWreathProduct
