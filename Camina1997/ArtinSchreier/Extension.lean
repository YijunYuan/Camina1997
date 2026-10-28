/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Polynomial
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic Artin–Schreier extensions

The concrete quotient by `X ^ p - X - C a` has a power basis of dimension `p`.
When `a` is not an Artin–Schreier image, this quotient is a field. Translation
of the adjoined root by elements of `ZMod p` gives its cyclic Galois action.

Reference: Camina (1997), Theorem 1, p. 103.
-/

@[expose] public section

open Polynomial

namespace Camina1997.ArtinSchreier

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] (a : F)

local notation "L" => AdjoinRoot (X ^ p - X - C a)
local notation "y" => AdjoinRoot.root (X ^ p - X - C a)

/-- The quotient by a rootless Artin–Schreier polynomial is a field. -/
theorem isField_adjoinRoot [CharP F p] (ha : ∀ x : F, x ^ p - x ≠ a) : IsField L :=
  AdjoinRoot.isField_iff_irreducible.mpr (irreducible_X_pow_sub_X_sub_C a ha)

/-- The powers of the canonical root form the canonical quotient power basis. -/
noncomputable def powerBasis : PowerBasis F L :=
  (AdjoinRoot.isAdjoinRootMonic _ (monic_X_pow_sub_X_sub_C a)).powerBasis

@[simp]
theorem powerBasis_gen : (powerBasis (p := p) a).gen = y := rfl

@[simp]
theorem powerBasis_dim : (powerBasis (p := p) a).dim = p :=
  natDegree_X_pow_sub_X_sub_C a

/-- The basis `1, y, ..., y^(p-1)` indexed by `Fin p`. -/
noncomputable def rootBasis : Module.Basis (Fin p) F L :=
  (powerBasis a).basis.reindex (finCongr (powerBasis_dim a))

@[simp]
theorem rootBasis_apply (i : Fin p) : rootBasis a i = y ^ (i : ℕ) := by
  simp [rootBasis]

/-- Every quotient element is a sum of the first `p` powers of the adjoined root. -/
theorem sum_rootBasis_repr (z : L) :
    ∑ i : Fin p, (rootBasis a).repr z i • y ^ (i : ℕ) = z := by
  simpa only [rootBasis_apply] using (rootBasis a).sum_repr z

/-- The concrete quotient has degree `p`, including before irreducibility is imposed. -/
theorem finrank_adjoinRoot : Module.finrank F L = p :=
  (powerBasis (p := p) a).finrank.trans (powerBasis_dim a)

instance instFiniteDimensionalAdjoinRoot : FiniteDimensional F L := (powerBasis a).finite

instance instNontrivialAdjoinRoot : Nontrivial L :=
  (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow_sub_X_sub_C a)).mpr (by
    rw [degree_eq_natDegree (monic_X_pow_sub_X_sub_C a).ne_zero,
      natDegree_X_pow_sub_X_sub_C]
    exact_mod_cast (Fact.out : p.Prime).pos)

omit [Fact p.Prime] in
/-- The adjoined root satisfies its defining Artin–Schreier equation. -/
theorem root_pow_sub : y ^ p - y = algebraMap F L a := by
  have h := AdjoinRoot.eval₂_root (X ^ p - X - C a)
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    AdjoinRoot.algebraMap_eq] using h

variable [CharP F p]

instance instCharPAdjoinRoot : CharP L p :=
  CharP.of_ringHom_of_ne_zero (algebraMap F L) p (Fact.out : p.Prime).ne_zero

private theorem zmod_cast_pow (c : ZMod p) :
    (ZMod.castHom (dvd_refl p) F c) ^ p = ZMod.castHom (dvd_refl p) F c := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
  simp only [map_natCast]
  exact map_natCast (frobenius F p) n

/-- Translation of the canonical root by a prime-field element. -/
noncomputable def translationHom (c : ZMod p) : L →ₐ[F] L :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F L)
    (y + algebraMap F L (ZMod.castHom (dvd_refl p) F c)) (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      change (y + algebraMap F L (ZMod.castHom (dvd_refl p) F c)) ^ p -
        (y + algebraMap F L (ZMod.castHom (dvd_refl p) F c)) - algebraMap F L a = 0
      rw [add_pow_char, ← map_pow, zmod_cast_pow]
      have h := root_pow_sub (p := p) a
      linear_combination h)

@[simp]
theorem translationHom_root (c : ZMod p) : translationHom a c y =
    y + algebraMap F L (ZMod.castHom (dvd_refl p) F c) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem translationHom_zero : translationHom (p := p) a 0 = AlgHom.id F L := by
  apply AdjoinRoot.algHom_ext
  simp

theorem translationHom_add (c d : ZMod p) :
    translationHom a (c + d) = (translationHom a c).comp (translationHom a d) := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, translationHom_root, map_add, AlgHom.commutes, add_assoc]

/-- Translation by `c` is inverted by translation by `-c`. -/
noncomputable def translation (c : ZMod p) : L ≃ₐ[F] L :=
  AlgEquiv.ofAlgHom (translationHom a c) (translationHom a (-c))
    (by rw [← translationHom_add, add_neg_cancel, translationHom_zero])
    (by rw [← translationHom_add, neg_add_cancel, translationHom_zero])

@[simp]
theorem translation_root (c : ZMod p) : translation a c y =
    y + algebraMap F L (ZMod.castHom (dvd_refl p) F c) :=
  translationHom_root a c

/-- The additive prime field acts by translations on the Artin–Schreier quotient. -/
noncomputable def translationAction : Multiplicative (ZMod p) →* (L ≃ₐ[F] L) where
  toFun c := translation a c.toAdd
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact translationHom_zero a
  map_mul' c d := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact translationHom_add a c.toAdd d.toAdd

theorem translation_injective : Function.Injective (translation (p := p) a) := by
  intro c d h
  have hy := congrArg (fun e : L ≃ₐ[F] L => e y) h
  simp only [translation_root, add_right_inj] at hy
  exact (ZMod.castHom_injective F)
    ((RingHom.injective (algebraMap F L)) hy)

theorem translationAction_injective : Function.Injective (translationAction (p := p) a) :=
  (translation_injective a).comp Multiplicative.toAdd.injective

/-- Every automorphism of a rootless Artin–Schreier quotient is a unique translation. -/
theorem translationAction_bijective (ha : ∀ x : F, x ^ p - x ≠ a) :
    Function.Bijective (translationAction (p := p) a) := by
  let : IsDomain L := AdjoinRoot.isDomain_of_prime
    (irreducible_X_pow_sub_X_sub_C a ha).prime
  apply (translationAction_injective a).bijective_of_nat_card_le
  calc
    Nat.card (L ≃ₐ[F] L) ≤ Nat.card (L →ₐ[F] L) :=
      Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
    _ ≤ Module.finrank F L := card_algHom_le_finrank F L L
    _ = p := finrank_adjoinRoot a
    _ = Nat.card (Multiplicative (ZMod p)) := by
      simp [Nat.card_eq_fintype_card]

/-- The full automorphism group is the additive group of the prime field. -/
noncomputable def automorphismEquiv (ha : ∀ x : F, x ^ p - x ≠ a) :
    Multiplicative (ZMod p) ≃* (L ≃ₐ[F] L) :=
  MulEquiv.ofBijective (translationAction a) (translationAction_bijective a ha)

/-- The quotient has exactly `p` automorphisms over the ground field. -/
theorem card_aut (ha : ∀ x : F, x ^ p - x ≠ a) : Nat.card (L ≃ₐ[F] L) = p := by
  rw [← Nat.card_congr (automorphismEquiv a ha).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The automorphism group of a rootless Artin–Schreier quotient is cyclic. -/
theorem isCyclic_aut (ha : ∀ x : F, x ^ p - x ≠ a) : IsCyclic (L ≃ₐ[F] L) :=
  isCyclic_of_surjective (translationAction a) (translationAction_bijective a ha).2

/-- A rootless Artin–Schreier polynomial produces a Galois extension of degree `p`. -/
theorem isGalois_adjoinRoot (ha : ∀ x : F, x ^ p - x ≠ a) :
    letI : Fact (Irreducible (X ^ p - X - C a)) :=
      ⟨irreducible_X_pow_sub_X_sub_C a ha⟩
    IsGalois F L := by
  let : Fact (Irreducible (X ^ p - X - C a)) :=
    ⟨irreducible_X_pow_sub_X_sub_C a ha⟩
  apply IsGalois.of_card_aut_eq_finrank
  rw [card_aut a ha, finrank_adjoinRoot]

end Camina1997.ArtinSchreier
