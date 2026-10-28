/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Reduced
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The Artin–Schreier quotient as a vector space

The image of `x ↦ x ^ p - x` is a prime-field subspace. For Laurent series,
projection restricts to a linear equivalence from the reduced representatives.

Reference: Camina (1997), Lemmas 2–3, p. 105.
-/

@[expose] public section

namespace Camina1997.ArtinSchreier

variable {p : ℕ} [Fact p.Prime]

section General

variable (p) (A : Type*) [CommRing A] [Module (ZMod p) A] [CharP A p]

/-- The Artin–Schreier map is linear over the prime field. -/
def wpLinearMap : A →ₗ[ZMod p] A :=
  ((frobenius A p).toAddMonoidHom - AddMonoidHom.id A).toZModLinearMap p

@[simp] theorem wpLinearMap_apply (x : A) : wpLinearMap p A x = x ^ p - x := rfl

/-- The actual vector-space quotient by Artin–Schreier images. -/
abbrev ASQuotient := A ⧸ LinearMap.range (wpLinearMap p A)

/-- Projection of a parameter to its Artin–Schreier class. -/
def classMap : A →ₗ[ZMod p] ASQuotient p A := (wpLinearMap p A).range.mkQ

@[simp] theorem classMap_eq_zero_iff (x : A) :
    classMap p A x = 0 ↔ ∃ μ : A, μ ^ p - μ = x :=
  Submodule.Quotient.mk_eq_zero _

end General

local notation "K" => LaurentSeries (ZMod p)

/-- Scalar multiples of reduced parameters remain reduced. -/
theorem IsReduced.smul {r : K} (hr : IsReduced r) (c : ZMod p) : IsReduced (c • r) :=
  ⟨fun i hi => by simp [HahnSeries.coeff_smul, hr.1 i hi],
    fun n hn hd => by simp [HahnSeries.coeff_smul, hr.2 n hn hd]⟩

/-- The subspace of reduced Laurent parameters. -/
def reducedSubmodule (p : ℕ) [Fact p.Prime] : Submodule (ZMod p) (LaurentSeries (ZMod p)) where
  carrier := {r | IsReduced (p := p) r}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := IsReduced.add
  smul_mem' := fun c _ h => h.smul c

/-- Projection of a reduced parameter to its Artin–Schreier class. -/
noncomputable def reducedClassMap : reducedSubmodule p →ₗ[ZMod p] ASQuotient p K :=
  (classMap p K).comp (reducedSubmodule p).subtype

/-- Reduced representatives identify the quotient without choosing roots. -/
theorem reducedClassMap_bijective : Function.Bijective (reducedClassMap (p := p)) := by
  constructor
  · intro r s h
    apply Subtype.ext
    have he : (r : K) - s ∈ (wpLinearMap p K).range :=
      (Submodule.Quotient.eq _).mp h
    obtain ⟨μ, hμ⟩ := he
    exact r.property.eq_of_sub_eq_pow_sub s.property hμ.symm
  · intro q
    obtain ⟨f, rfl⟩ := (wpLinearMap p K).range.mkQ_surjective q
    obtain ⟨r, μ, hr, hμ⟩ := exists_reduced f
    refine ⟨⟨r, hr⟩, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-μ, ?_⟩
    change wpLinearMap p K (-μ) = r - f
    rw [map_neg, wpLinearMap_apply]
    linear_combination hμ

/-- The canonical linear identification with reduced representatives. -/
noncomputable def reducedQuotientEquiv : reducedSubmodule p ≃ₗ[ZMod p] ASQuotient p K :=
  LinearEquiv.ofBijective reducedClassMap reducedClassMap_bijective

@[simp] theorem reducedQuotientEquiv_apply (r : reducedSubmodule p) :
    reducedQuotientEquiv r = classMap p K (r : K) := rfl

/-- Zero denotes the constant term; the other indices are the positive pole orders prime to p. -/
abbrev ReducedIndex (p : ℕ) := {n : ℕ // n = 0 ∨ ¬p ∣ n}

/-- The reduced monomial with the indicated pole order, with index zero giving the constant one. -/
noncomputable def reducedMonomial (i : ReducedIndex p) : reducedSubmodule p :=
  ⟨HahnSeries.single (-(i.val : ℤ)) 1, by
    change IsReduced _
    rcases i.property with hi | hi
    · simpa [hi] using isReduced_single_zero (p := p) 1
    · exact isReduced_single_neg (by
        by_contra h
        have : i.val = 0 := by omega
        exact hi (by rw [this]; exact dvd_zero p)) hi 1⟩

@[simp] theorem coeff_reducedMonomial (i j : ReducedIndex p) :
    (reducedMonomial i : K).coeff (-(j.val : ℤ)) = if j = i then 1 else 0 := by
  simp [reducedMonomial, HahnSeries.coeff_single, Subtype.ext_iff]

/-- Laurent coefficients separate the reduced monomials. -/
theorem linearIndependent_reducedMonomial :
    LinearIndependent (ZMod p) (reducedMonomial (p := p)) := by
  classical
  rw [linearIndependent_iff']
  intro s g h i hi
  have hc := congrArg (fun r : reducedSubmodule p => (r : K).coeff (-(i.val : ℤ))) h
  simpa [Submodule.coe_sum, Submodule.coe_smul, HahnSeries.coeff_sum,
    HahnSeries.coeff_smul, hi] using hc

/-- The reduced monomial classes in the actual quotient. -/
noncomputable def quotientMonomial (i : ReducedIndex p) : ASQuotient p K :=
  reducedClassMap (reducedMonomial i)

/-- The constant class and all prime-to-p negative monomial classes are linearly independent. -/
theorem linearIndependent_quotientMonomial :
    LinearIndependent (ZMod p) (quotientMonomial (p := p)) := by
  change LinearIndependent (ZMod p)
    ((reducedClassMap (p := p)) ∘ (reducedMonomial (p := p)))
  exact (linearIndependent_reducedMonomial (p := p)).map' (reducedClassMap (p := p))
    (LinearMap.ker_eq_bot.mpr (reducedClassMap_bijective (p := p)).1)

/-- A reduced parameter is a finite linear combination of the reduced monomials. -/
theorem IsReduced.mem_span_monomial {r : K} (hr : IsReduced r) :
    r ∈ Submodule.span (ZMod p) (Set.range fun i : ReducedIndex p =>
      (reducedMonomial i : K)) := by
  classical
  have hsum : ∑ i ∈ hr.finite_support.toFinset, HahnSeries.single i (r.coeff i) = r := by
    ext j
    rw [HahnSeries.coeff_sum]
    calc
      (∑ i ∈ hr.finite_support.toFinset, (HahnSeries.single i (r.coeff i) : K).coeff j) =
          (HahnSeries.single j (r.coeff j) : K).coeff j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          simp [Ne.symm hij]
        · intro hj
          have hc : r.coeff j = 0 := by
            by_contra hc
            exact hj ((Set.Finite.mem_toFinset _).mpr hc)
          simp [hc]
      _ = r.coeff j := HahnSeries.coeff_single_same _ _
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  have hc : r.coeff i ≠ 0 := (Set.Finite.mem_toFinset _).mp hi
  have hin : i ≤ 0 := le_of_not_gt fun h => hc (hr.1 i h)
  have he : -(i.natAbs : ℤ) = i := by rw [Int.natCast_natAbs, abs_of_nonpos hin, neg_neg]
  have hidx : i.natAbs = 0 ∨ ¬p ∣ i.natAbs := by
    by_cases hz : i.natAbs = 0
    · exact Or.inl hz
    · refine Or.inr fun hd => hc ?_
      have hzero := hr.2 i.natAbs (Nat.pos_of_ne_zero hz) hd
      rwa [he] at hzero
  have hs : HahnSeries.single i (r.coeff i) =
      r.coeff i • (reducedMonomial ⟨i.natAbs, hidx⟩ : K) := by
    change HahnSeries.single i (r.coeff i) =
      r.coeff i • (HahnSeries.single (-(i.natAbs : ℤ)) 1 : K)
    rw [he]
    ext j
    simp [HahnSeries.coeff_smul, HahnSeries.coeff_single]
  rw [hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.natAbs, hidx⟩, rfl⟩)

/-- Every Artin–Schreier class is spanned by the constant and prime-to-p pole classes. -/
theorem span_quotientMonomial :
    Submodule.span (ZMod p) (Set.range (quotientMonomial (p := p))) = ⊤ := by
  apply top_unique
  intro q _
  obtain ⟨r, rfl⟩ := (reducedClassMap_bijective (p := p)).2 q
  have hr := r.property.mem_span_monomial
  change classMap p K (r : K) ∈ _
  generalize (r : K) = x at hr ⊢
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-- The constant class and the prime-to-p negative monomial classes form a basis. -/
noncomputable def quotientBasis : Module.Basis (ReducedIndex p) (ZMod p) (ASQuotient p K) :=
  Module.Basis.mk (linearIndependent_quotientMonomial (p := p))
    (by rw [span_quotientMonomial])

@[simp] theorem quotientBasis_apply (i : ReducedIndex p) :
    quotientBasis i = quotientMonomial i := Module.Basis.mk_apply _ _ _

/-- The pole orders 1+np supply infinitely many reduced monomials. -/
instance infinite_reducedIndex : Infinite (ReducedIndex p) := by
  let f : ℕ → ReducedIndex p := fun n => ⟨p * n + 1, Or.inr (by
    intro h
    have hd : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_right p n)).mpr h
    exact (Fact.out : p.Prime).not_dvd_one hd)⟩
  apply Infinite.of_injective f
  intro n m h
  have he : p * n + 1 = p * m + 1 := congrArg Subtype.val h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  nlinarith

/-- The Laurent Artin–Schreier quotient has infinite dimension over its prime field. -/
theorem not_moduleFinite_quotient : ¬Module.Finite (ZMod p) (ASQuotient p K) := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite (quotientMonomial (p := p))
    (linearIndependent_quotientMonomial (p := p))

end Camina1997.ArtinSchreier
