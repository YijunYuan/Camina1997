/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Laurent
public import Camina1997.GroupTheory.CentralStep

/-!
# Totally ramified Laurent realization of finite p-groups

Induction by central subgroups of order p uses the constructed reduced
Artin–Schreier lift at every step. The result retains the full Galois group
and the exact scaling of the base valuation.

Reference: Camina (1997), Theorem 3, p. 105.
-/

@[expose] public section

namespace Camina1997.Witt

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

/-- Every finite p-group is the full Galois group of a totally ramified Laurent extension.

The base field is any specified copy of the prime-field Laurent series. The algebra
structure on the target, all automorphisms, and the valuation scaling are constructed.
-/
theorem exists_laurent_galois_realization
    (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p] (eF : F ≃+* K)
    (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G) :
    ∃ a : Algebra F K, letI := a
      FiniteDimensional F K ∧ IsGalois F K ∧
      ∃ ρ : G ≃* (K ≃ₐ[F] K),
        (∀ (g : G) (x : K), (ρ g x).orderTop = x.orderTop) ∧
        ∀ x : F, (algebraMap F K x).orderTop = Nat.card G • (eF x).orderTop := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    rcases subsingleton_or_nontrivial G with htriv | hnontriv
    · let := htriv
      let a := eF.toRingHom.toAlgebra
      refine ⟨a, ?_⟩
      let := a
      let e : F ≃ₐ[F] K := { eF with commutes' := fun _ => rfl }
      have hsub : Subsingleton (K ≃ₐ[F] K) := by
        refine ⟨fun f g => ?_⟩
        ext x : 1
        obtain ⟨y, rfl⟩ := eF.surjective x
        change f (algebraMap F K y) = g (algebraMap F K y)
        rw [f.commutes, g.commutes]
      let := hsub
      let ρ : G ≃* (K ≃ₐ[F] K) := MulEquiv.ofBijective (1 : G →* (K ≃ₐ[F] K))
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨1, Subsingleton.elim _ _⟩⟩
      refine ⟨e.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e, ρ, ?_, ?_⟩
      · intro g x
        have he : ρ g = 1 := Subsingleton.elim _ _
        rw [he]
        rfl
      · intro x
        let : Unique G := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
        rw [← hn, Nat.card_unique, one_smul]
        rfl
    · let := hnontriv
      obtain ⟨N, hN, hc, hcard, hquot, hlt⟩ := hG.exists_central_prime_step
      let := hN
      obtain ⟨a, hfin, hgal, ρ, hval, hbase⟩ :=
        ih (Nat.card (G ⧸ N)) (by omega) (G ⧸ N) hquot rfl
      let := a
      let := hfin
      let := hgal
      let q : G →* (K ≃ₐ[F] K) := ρ.toMonoidHom.comp (QuotientGroup.mk' N)
      have hq : Function.Surjective q := ρ.surjective.comp (QuotientGroup.mk'_surjective N)
      have hker : q.ker = N := by
        ext g
        change ρ (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
        rw [map_eq_one_iff ρ ρ.injective]
        exact QuotientGroup.eq_one_iff g
      rw [← hn]
      apply exists_laurent_centralLift F eF q hq (hker ▸ hcard) (hker ▸ hc)
      · intro g x
        obtain ⟨s, rfl⟩ := ρ.surjective g
        exact hval s x
      · intro x
        rw [hbase, ← Nat.card_congr ρ.toEquiv]

end Camina1997.Witt
