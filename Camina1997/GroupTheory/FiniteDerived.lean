/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Finite p-groups embed in derived subgroups

The constant functions embed a finite group in a regular wreath product.
A cyclic shift writes every such constant function as a commutator.

Reference: Lubotzky–Wilson (1984), p. 398, with an explicit proof of the
finite p-group case of the derived-subgroup embedding used there.
-/

@[expose] public section

open scoped commutatorElement

namespace RegularWreathProduct

variable {A Q : Type*} [Group A] [Group Q]

/-- The inclusion of the base function group in a regular wreath product. -/
def baseHom : (Q → A) →* (A ≀ᵣ Q) where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp

@[simp]
theorem baseHom_left (f : Q → A) : (baseHom f).left = f := rfl

@[simp]
theorem baseHom_right (f : Q → A) : (baseHom f).right = 1 := rfl

/-- Constant functions form a copy of the base group. -/
def constantHom : A →* (A ≀ᵣ Q) where
  toFun a := baseHom (fun _ => a)
  map_one' := rfl
  map_mul' a b := by ext <;> simp [baseHom]

theorem constantHom_injective : Function.Injective (constantHom (A := A) (Q := Q)) := by
  intro a b h
  exact congrArg (fun f : A ≀ᵣ Q => f.left 1) h

/-- The commutator with a shift is the multiplicative difference of a base function. -/
theorem commutator_inl_baseHom (q : Q) (f : Q → A) :
    ⁅(inl q : A ≀ᵣ Q), baseHom f⁆ = baseHom (fun x => f (q⁻¹ * x) * (f x)⁻¹) := by
  ext x <;> simp [commutatorElement_def]

end RegularWreathProduct

namespace Camina1997

universe u

variable {A : Type u} [Group A] [Finite A]

/-- The finite cyclic shift realizes each constant base function as one commutator. -/
theorem constantWreath_mem_commutator (a : A) :
    RegularWreathProduct.constantHom (Q := Multiplicative (ZMod (Nat.card A))) a ∈
      commutator (A ≀ᵣ Multiplicative (ZMod (Nat.card A))) := by
  let : NeZero (Nat.card A) := ⟨Nat.card_pos.ne'⟩
  let q : Multiplicative (ZMod (Nat.card A)) := Multiplicative.ofAdd (-1)
  let f : Multiplicative (ZMod (Nat.card A)) → A := fun x => a ^ x.toAdd.val
  have hpow (z : ZMod (Nat.card A)) : a ^ (z + 1).val = a * a ^ z.val := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod,
      ← pow_eq_pow_mod _ (pow_card_eq_one' (x := a)), pow_succ']
  have he :
      ⁅(RegularWreathProduct.inl q : A ≀ᵣ Multiplicative (ZMod (Nat.card A))),
        RegularWreathProduct.baseHom f⁆ =
      RegularWreathProduct.constantHom (Q := Multiplicative (ZMod (Nat.card A))) a := by
    rw [RegularWreathProduct.commutator_inl_baseHom]
    ext x
    · change a ^ (-(-1) + x.toAdd).val * (a ^ x.toAdd.val)⁻¹ = a
      rw [neg_neg, add_comm, hpow, mul_inv_cancel_right]
    · rfl
  rw [← he, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)

/-- The constant-function embedding, with its codomain restricted to the derived subgroup. -/
noncomputable def finiteDerivedEmbedding :
    A →* commutator (A ≀ᵣ Multiplicative (ZMod (Nat.card A))) :=
  (RegularWreathProduct.constantHom (Q := Multiplicative (ZMod (Nat.card A)))).codRestrict _
    constantWreath_mem_commutator

theorem finiteDerivedEmbedding_injective :
    Function.Injective (finiteDerivedEmbedding (A := A)) := by
  intro a b h
  exact RegularWreathProduct.constantHom_injective (congrArg Subtype.val h)

/-- A finite regular wreath product of p-groups is again a p-group. -/
theorem _root_.IsPGroup.regularWreathProduct {p : ℕ} [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q] (hA : IsPGroup p A) (hQ : IsPGroup p Q) :
    IsPGroup p (A ≀ᵣ Q) := by
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  apply IsPGroup.of_card (n := a * Nat.card Q + b)
  rw [RegularWreathProduct.card, ha, hb, pow_add, pow_mul]

/-- The finite group containing the derived embedding is a p-group whenever the source is. -/
theorem isPGroup_finiteDerivedTarget {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) :
    IsPGroup p (A ≀ᵣ Multiplicative (ZMod (Nat.card A))) := by
  let : NeZero (Nat.card A) := ⟨Nat.card_pos.ne'⟩
  apply hA.regularWreathProduct
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  apply IsPGroup.of_card (n := n)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card, hn]

/-- Every finite p-group embeds in the derived subgroup of another finite p-group. -/
theorem exists_finite_pGroup_derived_embedding {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) :
    ∃ F : Type u, ∃ hF : Group F, letI := hF
      Finite F ∧ IsPGroup p F ∧ ∃ e : A →* commutator F, Function.Injective e := by
  let : NeZero (Nat.card A) := ⟨Nat.card_pos.ne'⟩
  exact ⟨A ≀ᵣ Multiplicative (ZMod (Nat.card A)), inferInstance, inferInstance,
    isPGroup_finiteDerivedTarget hA, finiteDerivedEmbedding, finiteDerivedEmbedding_injective⟩

end Camina1997
