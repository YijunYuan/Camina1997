/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Cocycle

/-!
# The semilinear automorphisms in Witt's construction

The two additive equations construct actual automorphisms of the Artin–Schreier
quotient, acting on the base field by its given action and translating the root.

Reference: Camina (1997), the Witt algorithm, pp. 103–104; Witt (1936), p. 240.
-/

@[expose] public section

open Polynomial

namespace Camina1997.Witt

variable {G K : Type*} [Group G] [Field K] [MulSemiringAction G K]
variable {p : ℕ} [Fact p.Prime] [CharP K p] (γ : K)

local notation "A" => AdjoinRoot (X ^ p - X - C γ)
local notation "y" => AdjoinRoot.root (X ^ p - X - C γ)

/-- Transport the coefficients by `s` and translate the Artin–Schreier root by `d`. -/
noncomputable def liftHom (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) : A →+* A :=
  AdjoinRoot.lift ((algebraMap K A).comp (MulSemiringAction.toRingHom G K s))
    (y + algebraMap K A d) (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, RingHom.comp_apply]
      change (y + algebraMap K A d) ^ p - (y + algebraMap K A d) -
        algebraMap K A (s • γ) = 0
      rw [add_pow_char, ← map_pow]
      have hroot := ArtinSchreier.root_pow_sub (p := p) γ
      have hmap := congrArg (algebraMap K A) hd
      simp only [map_sub] at hmap
      linear_combination hroot - hmap)

@[simp]
theorem liftHom_root (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) :
    liftHom γ s d hd y = y + algebraMap K A d :=
  AdjoinRoot.lift_root _

@[simp]
theorem liftHom_algebraMap (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) (x : K) :
    liftHom γ s d hd (algebraMap K A x) = algebraMap K A (s • x) :=
  AdjoinRoot.lift_of _

/-- The increments compose by the same rule as semilinear affine maps. -/
theorem liftHom_comp (s t : G) (d e : K)
    (hd : s • γ - γ = d ^ p - d) (he : t • γ - γ = e ^ p - e)
    (hde : (s * t) • γ - γ = (d + s • e) ^ p - (d + s • e)) :
    (liftHom γ s d hd).comp (liftHom γ t e he) = liftHom γ (s * t) (d + s • e) hde := by
  apply AdjoinRoot.ringHom_ext
  · ext x
    simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq, liftHom_algebraMap,
      mul_smul]
  · simp only [RingHom.comp_apply, liftHom_root, map_add, liftHom_algebraMap]
    ring

theorem liftHom_one (h : (1 : G) • γ - γ = (0 : K) ^ p - 0) :
    liftHom γ (1 : G) 0 h = RingHom.id A := by
  apply AdjoinRoot.ringHom_ext
  · ext x
    simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq, liftHom_algebraMap,
      one_smul, RingHom.id_apply]
  · simp

/-- Compatibility with the Artin–Schreier equation is preserved by composition. -/
theorem increment_mul (s t : G) (d e : K)
    (hd : s • γ - γ = d ^ p - d) (he : t • γ - γ = e ^ p - e) :
    (s * t) • γ - γ = (d + s • e) ^ p - (d + s • e) := by
  have h := congrArg (fun x : K => s • x) he
  have hp : s • (e ^ p) = (s • e) ^ p :=
    map_pow (MulSemiringAction.toRingHom G K s) e p
  simp only [smul_sub, hp] at h
  rw [mul_smul, add_pow_char]
  linear_combination hd + h

/-- The inverse increment is `-s⁻¹(d)`. -/
theorem increment_inv (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) :
    s⁻¹ • γ - γ = (-(s⁻¹ • d)) ^ p - (-(s⁻¹ • d)) := by
  have h := congrArg (fun x : K => s⁻¹ • x) hd
  have hp : s⁻¹ • (d ^ p) = (s⁻¹ • d) ^ p :=
    map_pow (MulSemiringAction.toRingHom G K s⁻¹) d p
  simp only [smul_sub, inv_smul_smul, hp] at h
  rw [show (-(s⁻¹ • d)) ^ p = -((s⁻¹ • d) ^ p) from
    map_neg (frobenius K p) (s⁻¹ • d)]
  linear_combination -h

/-- The semilinear root translation is an automorphism of the actual quotient ring. -/
noncomputable def liftEquiv (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) : A ≃+* A where
  __ := liftHom γ s d hd
  invFun := liftHom γ s⁻¹ (-(s⁻¹ • d)) (increment_inv γ s d hd)
  left_inv x := by
    have h : (liftHom γ s⁻¹ (-(s⁻¹ • d)) (increment_inv γ s d hd)).comp
        (liftHom γ s d hd) = RingHom.id A := by
      apply AdjoinRoot.ringHom_ext
      · ext z
        simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq, liftHom_algebraMap,
          inv_smul_smul, RingHom.id_apply]
      · simp only [RingHom.comp_apply, liftHom_root, map_add, liftHom_algebraMap,
          map_neg, RingHom.id_apply]
        ring
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (liftHom γ s d hd).comp
        (liftHom γ s⁻¹ (-(s⁻¹ • d)) (increment_inv γ s d hd)) = RingHom.id A := by
      apply AdjoinRoot.ringHom_ext
      · ext z
        simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq, liftHom_algebraMap,
          smul_inv_smul, RingHom.id_apply]
      · simp only [RingHom.comp_apply, liftHom_root, map_add, liftHom_algebraMap,
          smul_inv_smul, map_neg, RingHom.id_apply]
        ring
    exact DFunLike.congr_fun h x

@[simp]
theorem liftEquiv_root (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) :
    liftEquiv γ s d hd y = y + algebraMap K A d :=
  liftHom_root γ s d hd

@[simp]
theorem liftEquiv_algebraMap (s : G) (d : K) (hd : s • γ - γ = d ^ p - d) (x : K) :
    liftEquiv γ s d hd (algebraMap K A x) = algebraMap K A (s • x) :=
  liftHom_algebraMap γ s d hd x

omit [MulSemiringAction G K] in
private theorem zmod_cast_pow (a : ZMod p) :
    (ZMod.castHom (dvd_refl p) K a) ^ p = ZMod.castHom (dvd_refl p) K a := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  simp only [map_natCast]
  exact map_natCast (frobenius K p) n

private theorem smul_zmod_cast (a : ZMod p) (s : G) :
    s • ZMod.castHom (dvd_refl p) K a = ZMod.castHom (dvd_refl p) K a := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  simp only [map_natCast]
  exact map_natCast (MulSemiringAction.toRingHom G K s) n

/-- The automorphism assigned to the central coordinates `(s, a)` in Witt's construction. -/
noncomputable def wittLift (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (s : G) (a : ZMod p) : A ≃+* A :=
  liftEquiv γ s (δ s + ZMod.castHom (dvd_refl p) K a) (by
    rw [add_pow_char, zmod_cast_pow, hγ]
    ring)

@[simp]
theorem wittLift_root (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (s : G) (a : ZMod p) :
    wittLift γ δ hγ s a y = y + algebraMap K A (δ s + ZMod.castHom (dvd_refl p) K a) :=
  liftEquiv_root _ _ _ _

@[simp]
theorem wittLift_algebraMap (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (s : G) (a : ZMod p) (x : K) :
    wittLift γ δ hγ s a (algebraMap K A x) = algebraMap K A (s • x) :=
  liftEquiv_algebraMap _ _ _ _ _

/-- The cocycle gives the exact composition rule of the lifted automorphisms. -/
theorem wittLift_mul (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (c : G → G → ZMod p)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) = ZMod.castHom (dvd_refl p) K (c s t))
    (s t : G) (a b : ZMod p) :
    wittLift γ δ hγ s a * wittLift γ δ hγ t b =
      wittLift γ δ hγ (s * t) (a + b + c s t) := by
  apply RingEquiv.toRingHom_injective
  apply AdjoinRoot.ringHom_ext
  · ext x
    simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq]
    change wittLift γ δ hγ s a (wittLift γ δ hγ t b (algebraMap K A x)) =
      wittLift γ δ hγ (s * t) (a + b + c s t) (algebraMap K A x)
    simp only [wittLift_algebraMap, mul_smul]
  · change wittLift γ δ hγ s a (wittLift γ δ hγ t b y) =
      wittLift γ δ hγ (s * t) (a + b + c s t) y
    simp only [wittLift_root, map_add, wittLift_algebraMap, smul_zmod_cast]
    have h := congrArg (algebraMap K A) (hδ s t)
    simp only [map_add, map_sub] at h
    linear_combination h

@[simp]
theorem wittLift_one (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hδ1 : δ 1 = 0) : wittLift γ δ hγ 1 0 = 1 := by
  apply RingEquiv.toRingHom_injective
  apply AdjoinRoot.ringHom_ext
  · ext x
    simp only [RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq]
    change wittLift γ δ hγ 1 0 (algebraMap K A x) = algebraMap K A x
    simp only [wittLift_algebraMap, one_smul]
  · change wittLift γ δ hγ 1 0 y = y
    simp [hδ1]

/-- Distinct central coordinates give distinct automorphisms when the base action is faithful. -/
theorem wittLift_injective [FaithfulSMul G K] (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s) :
    Function.Injective (fun z : G × ZMod p => wittLift γ δ hγ z.1 z.2) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  change wittLift γ δ hγ s a = wittLift γ δ hγ t b at h
  have hs : s = t := by
    apply eq_of_smul_eq_smul (α := K)
    intro x
    apply (algebraMap K A).injective
    have hx := congrArg (fun e : A ≃+* A => e (algebraMap K A x)) h
    simpa only [wittLift_algebraMap] using hx
  subst t
  have hy := congrArg (fun e : A ≃+* A => e y) h
  simp only [wittLift_root] at hy
  have hab : ZMod.castHom (dvd_refl p) K a = ZMod.castHom (dvd_refl p) K b :=
    add_left_cancel ((algebraMap K A).injective (add_left_cancel hy))
  exact Prod.ext rfl (ZMod.castHom_injective K hab)

section BaseAlgebra

variable {F : Type*} [CommSemiring F] [Algebra F K]

/-- If the base action fixes `F`, each lift is an `F`-algebra automorphism. -/
noncomputable def wittLiftAlgEquiv (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x)
    (s : G) (a : ZMod p) : A ≃ₐ[F] A where
  __ := wittLift γ δ hγ s a
  commutes' x := by
    change wittLift γ δ hγ s a (algebraMap K A (algebraMap F K x)) =
      algebraMap K A (algebraMap F K x)
    rw [wittLift_algebraMap, hF]

@[simp]
theorem wittLiftAlgEquiv_toRingEquiv (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x)
    (s : G) (a : ZMod p) :
    (wittLiftAlgEquiv γ δ hγ hF s a).toRingEquiv = wittLift γ δ hγ s a := rfl

theorem wittLiftAlgEquiv_mul (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x)
    (c : G → G → ZMod p)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) = ZMod.castHom (dvd_refl p) K (c s t))
    (s t : G) (a b : ZMod p) :
    wittLiftAlgEquiv γ δ hγ hF s a * wittLiftAlgEquiv γ δ hγ hF t b =
      wittLiftAlgEquiv γ δ hγ hF (s * t) (a + b + c s t) := by
  apply AlgEquiv.toRingEquiv_injective
  exact wittLift_mul γ δ hγ c hδ s t a b

theorem wittLiftAlgEquiv_injective [FaithfulSMul G K] (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x) :
    Function.Injective (fun z : G × ZMod p => wittLiftAlgEquiv γ δ hγ hF z.1 z.2) := by
  intro z w h
  exact wittLift_injective γ δ hγ (congrArg AlgEquiv.toRingEquiv h)

end BaseAlgebra

end Camina1997.Witt
