/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Adjustment
public import Camina1997.Witt.PrimeKernel
public import Camina1997.ArtinSchreier.Semilinear
public import Camina1997.ArtinSchreier.LaurentParameter

/-!
# Central lifting in Laurent-series coordinates

The reduced central Galois lift is transported through the proved uniformizer
coordinates. Both the action and the ramification index are retained.

Reference: Camina (1997), Theorem 3, p. 105.
-/

@[expose] public section

open Polynomial

namespace Camina1997.Witt

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

variable (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p]
  [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))]

/-- Central lifting preserves Laurent coordinates, the full Galois group, and total ramification. -/
theorem exists_laurent_centralLift {E : Type*} [Group E] [Finite E]
    (eF : F ≃+* K) (q : E →* (K ≃ₐ[F] K))
    (hq : Function.Surjective q) (hker : Nat.card q.ker = p)
    (hcentral : q.ker ≤ Subgroup.center E)
    (hval : ∀ (g : K ≃ₐ[F] K) (x : K), (g x).orderTop = x.orderTop)
    (hbase : ∀ x : F, (algebraMap F K x).orderTop =
      Nat.card (K ≃ₐ[F] K) • (eF x).orderTop) :
    ∃ a : Algebra F K, letI := a
      FiniteDimensional F K ∧ IsGalois F K ∧
      ∃ ρ : E ≃* (K ≃ₐ[F] K),
        (∀ (g : E) (x : K), (ρ g x).orderTop = x.orderTop) ∧
        ∀ x : F, (algebraMap F K x).orderTop = Nat.card E • (eF x).orderTop := by
  let S := GroupExtension.ofPrimeKernel q hq hker
  have hrange : S.inl.range = q.ker := S.range_inl_eq_ker_rightHom
  obtain ⟨r, m, hm, hpm, hr, _, _, hdegree, hgal, ρ, hrestrict⟩ :=
    exists_reduced_galois_centralLift_laurentBase F eF S (hrange ▸ hcentral) 0
  have hr' : r.orderTop = (-(m : ℤ) : WithTop ℤ) := by exact_mod_cast hr
  let : Fact (Irreducible (X ^ p - X - C r)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm r hr⟩
  let A := AdjoinRoot (X ^ p - X - C r)
  let aA : Algebra F A := inferInstance
  let := aA
  let : FiniteDimensional F A := FiniteDimensional.trans F K A
  let : IsGalois F A := hgal
  obtain ⟨π, hπ⟩ := ArtinSchreier.exists_weightedOrder_eq r m hpm 1
  have hπO : π ∈ ArtinSchreier.weightedInteger r m hm hpm hr' := by
    rw [ArtinSchreier.mem_weightedInteger, hπ]
    exact zero_le_one
  let e := ArtinSchreier.laurentParameterEquiv r m hm hpm hr' ⟨π, hπO⟩ hπ
  have he (x : K) : ArtinSchreier.weightedOrder r m (e x) = x.orderTop :=
    ArtinSchreier.weightedOrder_laurentParameterEquiv r m hm hpm hr' ⟨π, hπO⟩ hπ x
  have he' (x : A) : (e.symm x).orderTop = ArtinSchreier.weightedOrder r m x := by
    simpa only [AlgEquiv.apply_symm_apply] using (he (e.symm x)).symm
  have hρval (g : E) (x : A) :
      ArtinSchreier.weightedOrder r m (ρ g x) = ArtinSchreier.weightedOrder r m x :=
    ArtinSchreier.weightedOrder_semilinear r m hm hpm hr' (ρ g).toRingEquiv
      (q g).toRingEquiv (hrestrict g) (hval (q g)) x
  have hcard : Nat.card E = Nat.card (K ≃ₐ[F] K) * p := card_centralExtension S
  have hbaseA (x : F) : ArtinSchreier.weightedOrder r m (algebraMap F A x) =
      Nat.card E • (eF x).orderTop := by
    rw [IsScalarTower.algebraMap_apply F K A, ArtinSchreier.weightedOrder_algebraMap,
      hbase, smul_smul, hcard, Nat.mul_comm]
  let β : F →+* K := e.symm.toRingHom.comp (algebraMap F A)
  let a := β.toAlgebra
  refine ⟨a, ?_⟩
  let := a
  let e' : A ≃ₐ[F] K := { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  refine ⟨e'.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e',
    ρ.trans (AlgEquiv.autCongr e'), ?_, ?_⟩
  · intro g x
    change (e.symm (ρ g (e x))).orderTop = x.orderTop
    rw [he', hρval, he]
  · intro x
    change (e.symm (algebraMap F A x)).orderTop = Nat.card E • (eF x).orderTop
    rw [he', hbaseA]

end Camina1997.Witt
