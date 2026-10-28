/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.IntegerTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation

/-!
# Evaluation at a uniformizer of an Artin–Schreier extension

Power-series evaluation takes values in the complete valuation ring. A nonzero
series factors as a power of the variable times a unit, so evaluation at an
element of weighted order one preserves its order.
-/

@[expose] public section

open Polynomial Filter
open scoped Topology

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ

/-- Units of the valuation ring have weighted order zero. -/
theorem weightedOrder_integer_of_isUnit {x : O} (hx : IsUnit x) :
    weightedOrder γ m (x : L) = 0 :=
  (Valuation.integer.integers (weightedValuation γ m hm hpm hγ).toValuation).one_of_isUnit hx

/-- A power-series homomorphism taking the variable to a uniformizer preserves finite order. -/
theorem weightedOrder_map_powerSeries (φ : PowerSeries k →+* O)
    (hφ : weightedOrder γ m (φ PowerSeries.X : L) = 1)
    {f : PowerSeries k} (hf : f ≠ 0) :
    weightedOrder γ m (φ f : L) = (f.order.toNat : WithTop ℤ) := by
  have hu := weightedOrder_integer_of_isUnit γ m hm hpm hγ
    ((PowerSeries.isUnit_divided_by_X_pow_order hf).map φ)
  have hp := (weightedValuation γ m hm hpm hγ).map_pow (φ PowerSeries.X : L) f.order.toNat
  simp only [weightedValuation_apply, hφ] at hp
  have he := congrArg (fun a : PowerSeries k => (φ a : L))
    (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
  simp only [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow] at he
  rw [← he, weightedOrder_mul γ m hm hpm hγ, hu, add_zero, hp]
  simp

/-- Such a homomorphism has zero kernel, hence is injective. -/
theorem injective_powerSeriesHom_of_weightedOrder_X (φ : PowerSeries k →+* O)
    (hφ : weightedOrder γ m (φ PowerSeries.X : L) = 1) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro f hf
  by_contra hne
  have he := weightedOrder_map_powerSeries γ m hm hpm hγ φ hφ hne
  have hz : φ f = 0 := hf
  simp only [hz, ZeroMemClass.coe_zero, weightedOrder_zero] at he
  exact WithTop.coe_ne_top he.symm

section Evaluation

open scoped PowerSeries.WithPiTopology

/-- Evaluate a power series at a uniformizer, with values in the complete valuation ring. -/
noncomputable def powerSeriesEval (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) : PowerSeries k →+* O := by
  let : UniformSpace k := ⊥
  let := weightedValued γ m hm hpm hγ
  let := weightedInteger_t2Space γ m hm hpm hγ
  let := weightedInteger_completeSpace γ m hm hpm hγ
  let := weightedInteger_isLinearTopology γ m hm hpm hγ
  let : IsUniformAddGroup O := IsUniformInducing.isUniformAddGroup (O).subtype ⟨rfl⟩
  exact PowerSeries.eval₂Hom (φ := constantIntegerHom γ m hm hpm hγ)
    continuous_of_discreteTopology
    (weightedInteger_isTopologicallyNilpotent γ m hm hpm hγ hπ)

@[simp]
theorem powerSeriesEval_X (π : O) (hπ : weightedOrder γ m (π : L) = 1) :
    powerSeriesEval γ m hm hpm hγ π hπ PowerSeries.X = π := by
  let : UniformSpace k := ⊥
  let := weightedValued γ m hm hpm hγ
  simpa only [powerSeriesEval, PowerSeries.coe_eval₂Hom] using
    PowerSeries.eval₂_X (constantIntegerHom γ m hm hpm hγ) π

@[simp]
theorem powerSeriesEval_C (π : O) (hπ : weightedOrder γ m (π : L) = 1) (c : k) :
    powerSeriesEval γ m hm hpm hγ π hπ (PowerSeries.C c) =
      constantIntegerHom γ m hm hpm hγ c := by
  let : UniformSpace k := ⊥
  let := weightedValued γ m hm hpm hγ
  simpa only [powerSeriesEval, PowerSeries.coe_eval₂Hom] using
    PowerSeries.eval₂_C (constantIntegerHom γ m hm hpm hγ) π c

/-- Evaluation is continuous for coefficientwise convergence of power series. -/
theorem continuous_powerSeriesEval (π : O) (hπ : weightedOrder γ m (π : L) = 1) :
    letI : UniformSpace k := ⊥
    letI := weightedValued γ m hm hpm hγ
    Continuous (powerSeriesEval γ m hm hpm hγ π hπ) := by
  let : UniformSpace k := ⊥
  let := weightedValued γ m hm hpm hγ
  let := weightedInteger_t2Space γ m hm hpm hγ
  let := weightedInteger_completeSpace γ m hm hpm hγ
  let := weightedInteger_isLinearTopology γ m hm hpm hγ
  let : IsUniformAddGroup O := IsUniformInducing.isUniformAddGroup (O).subtype ⟨rfl⟩
  simpa only [powerSeriesEval, PowerSeries.coe_eval₂Hom] using
    PowerSeries.continuous_eval₂ (φ := constantIntegerHom γ m hm hpm hγ)
      continuous_of_discreteTopology
      (weightedInteger_isTopologicallyNilpotent γ m hm hpm hγ hπ)

/-- The evaluation is the convergent sum of its evaluated monomials. -/
theorem hasSum_powerSeriesEval (π : O) (hπ : weightedOrder γ m (π : L) = 1)
    (f : PowerSeries k) :
    letI := weightedValued γ m hm hpm hγ
    HasSum (fun n : ℕ => constantIntegerHom γ m hm hpm hγ (PowerSeries.coeff n f) * π ^ n)
      (powerSeriesEval γ m hm hpm hγ π hπ f) := by
  let : UniformSpace k := ⊥
  let := weightedValued γ m hm hpm hγ
  let := weightedInteger_t2Space γ m hm hpm hγ
  let := weightedInteger_completeSpace γ m hm hpm hγ
  let := weightedInteger_isLinearTopology γ m hm hpm hγ
  let : IsUniformAddGroup O := IsUniformInducing.isUniformAddGroup (O).subtype ⟨rfl⟩
  simpa only [powerSeriesEval, PowerSeries.coe_eval₂Hom] using
    PowerSeries.hasSum_eval₂ (φ := constantIntegerHom γ m hm hpm hγ)
      continuous_of_discreteTopology
      (weightedInteger_isTopologicallyNilpotent γ m hm hpm hγ hπ) f

/-- Evaluation at a uniformizer preserves the order of every nonzero power series. -/
theorem weightedOrder_powerSeriesEval (π : O) (hπ : weightedOrder γ m (π : L) = 1)
    {f : PowerSeries k} (hf : f ≠ 0) :
    weightedOrder γ m (powerSeriesEval γ m hm hpm hγ π hπ f : L) =
      (f.order.toNat : WithTop ℤ) :=
  weightedOrder_map_powerSeries γ m hm hpm hγ _ (by simpa using hπ) hf

theorem powerSeriesEval_injective (π : O) (hπ : weightedOrder γ m (π : L) = 1) :
    Function.Injective (powerSeriesEval γ m hm hpm hγ π hπ) :=
  injective_powerSeriesHom_of_weightedOrder_X γ m hm hpm hγ _ (by simpa using hπ)

end Evaluation

section Digits

variable [CharP k p]

/-- Subtracting a residue constant from an integer leaves a multiple of any uniformizer. -/
theorem exists_constant_add_uniformizer_mul (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) :
    ∃ s : k × O, x = constantIntegerHom γ m hm hpm hγ s.1 + π * s.2 := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  obtain ⟨c, hc⟩ := exists_constant_sub_weightedOrder_pos γ m hpm x.property
  have hπne : (π : L) ≠ 0 := by
    intro hz
    rw [hz, weightedOrder_zero] at hπ
    exact WithTop.coe_ne_top hπ.symm
  let y : L := ((x : L) - algebraMap K L (HahnSeries.C c)) / (π : L)
  have hy : (0 : WithTop ℤ) ≤ weightedOrder γ m y := by
    have he : weightedOrder γ m ((x : L) - algebraMap K L (HahnSeries.C c)) =
        weightedOrder γ m y + 1 := by
      rw [← div_mul_cancel₀ ((x : L) - algebraMap K L (HahnSeries.C c)) hπne,
        weightedOrder_mul γ m hm hpm hγ, hπ]
    rw [he] at hc
    by_cases hz : y = 0
    · simp [hz]
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((weightedOrder_eq_top γ m y).not.mpr hz)
      rw [← hn] at hc ⊢
      have hn' : (0 : ℤ) < n + 1 := by exact_mod_cast hc
      exact_mod_cast (show (0 : ℤ) ≤ n by omega)
  refine ⟨(c, ⟨y, hy⟩), ?_⟩
  apply Subtype.ext
  change (x : L) = algebraMap K L (HahnSeries.C c) + (π : L) * y
  dsimp [y]
  rw [mul_div_cancel₀ _ hπne]
  ring

/-- One residue digit and the integral remainder after division by the uniformizer. -/
noncomputable def uniformizerStep (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) : k × O :=
  Classical.choose (exists_constant_add_uniformizer_mul γ m hm hpm hγ π hπ x)

theorem uniformizerStep_spec (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) :
    x = constantIntegerHom γ m hm hpm hγ (uniformizerStep γ m hm hpm hγ π hπ x).1 +
      π * (uniformizerStep γ m hm hpm hγ π hπ x).2 :=
  Classical.choose_spec (exists_constant_add_uniformizer_mul γ m hm hpm hγ π hπ x)

/-- Successive integral remainders in expansion with respect to a uniformizer. -/
noncomputable def uniformizerRemainder (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) : ℕ → O
  | 0 => x
  | n + 1 => (uniformizerStep γ m hm hpm hγ π hπ
      (uniformizerRemainder π hπ x n)).2

/-- The residue digit of the `n`th remainder. -/
noncomputable def uniformizerCoefficient (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) (n : ℕ) : k :=
  (uniformizerStep γ m hm hpm hγ π hπ (uniformizerRemainder γ m hm hpm hγ π hπ x n)).1

theorem uniformizerRemainder_eq (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) (n : ℕ) :
    uniformizerRemainder γ m hm hpm hγ π hπ x n =
      constantIntegerHom γ m hm hpm hγ (uniformizerCoefficient γ m hm hpm hγ π hπ x n) +
        π * uniformizerRemainder γ m hm hpm hγ π hπ x (n + 1) :=
  uniformizerStep_spec γ m hm hpm hγ π hπ _

/-- A finite initial segment of the expansion has an explicit integral remainder. -/
theorem uniformizer_partial_expansion (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) (n : ℕ) :
    x = (∑ i ∈ Finset.range n,
      constantIntegerHom γ m hm hpm hγ (uniformizerCoefficient γ m hm hpm hγ π hπ x i) *
        π ^ i) + π ^ n * uniformizerRemainder γ m hm hpm hγ π hπ x n := by
  induction n with
  | zero => simp [uniformizerRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      x = (∑ i ∈ Finset.range n,
        constantIntegerHom γ m hm hpm hγ (uniformizerCoefficient γ m hm hpm hγ π hπ x i) *
          π ^ i) + π ^ n * uniformizerRemainder γ m hm hpm hγ π hπ x n := ih
      _ = _ := by rw [uniformizerRemainder_eq γ m hm hpm hγ π hπ x n]; ring

/-- The power series whose coefficients are the successive residue digits. -/
noncomputable def uniformizerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) : PowerSeries k :=
  PowerSeries.mk (uniformizerCoefficient γ m hm hpm hγ π hπ x)

@[simp]
theorem coeff_uniformizerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) (n : ℕ) :
    PowerSeries.coeff n (uniformizerSeries γ m hm hpm hγ π hπ x) =
      uniformizerCoefficient γ m hm hpm hγ π hπ x n :=
  PowerSeries.coeff_mk _ _

/-- The finite residue-digit expansions converge to the original integer. -/
theorem tendsto_uniformizer_partial_expansion (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) :
    letI := weightedValued γ m hm hpm hγ
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      constantIntegerHom γ m hm hpm hγ (uniformizerCoefficient γ m hm hpm hγ π hπ x i) *
        π ^ i) atTop (𝓝 x) := by
  let := weightedValued γ m hm hpm hγ
  rw [tendsto_subtype_rng]
  have hb := nhds_basis_uniformity
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ) (x := (x : L))
  rw [hb.tendsto_right_iff]
  intro n _
  filter_upwards [eventually_ge_atTop (n.natAbs + 1)] with j hj
  have he := congrArg (fun a : O => (a : L))
    (uniformizer_partial_expansion γ m hm hpm hγ π hπ x j)
  change (x : L) = (↑(∑ i ∈ Finset.range j,
      constantIntegerHom γ m hm hpm hγ (uniformizerCoefficient γ m hm hpm hγ π hπ x i) *
        π ^ i) : L) + (π : L) ^ j *
          (uniformizerRemainder γ m hm hpm hγ π hπ x j : L) at he
  change (n : WithTop ℤ) < weightedOrder γ m ((x : L) - _)
  rw [(sub_eq_iff_eq_add).mpr (he.trans (add_comm _ _)), weightedOrder_mul γ m hm hpm hγ]
  have hp := (weightedValuation γ m hm hpm hγ).map_pow (π : L) j
  change weightedOrder γ m ((π : L) ^ j) = j • weightedOrder γ m (π : L) at hp
  rw [hp, hπ, nsmul_one]
  have hn : n < (j : ℤ) := by omega
  have hr : (0 : WithTop ℤ) ≤ weightedOrder γ m
      (uniformizerRemainder γ m hm hpm hγ π hπ x j : L) :=
    (uniformizerRemainder γ m hm hpm hγ π hπ x j).property
  exact (show (n : WithTop ℤ) < (j : WithTop ℤ) by exact_mod_cast hn).trans_le
    (by simpa only [zero_add, add_zero, add_comm] using add_le_add_left hr (j : WithTop ℤ))

/-- Evaluating the successive residue digits recovers the given integer. -/
theorem powerSeriesEval_uniformizerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (x : O) :
    powerSeriesEval γ m hm hpm hγ π hπ (uniformizerSeries γ m hm hpm hγ π hπ x) = x := by
  let := weightedValued γ m hm hpm hγ
  let := weightedInteger_t2Space γ m hm hpm hγ
  have hs := (hasSum_powerSeriesEval γ m hm hpm hγ π hπ
    (uniformizerSeries γ m hm hpm hγ π hπ x)).tendsto_sum_nat
  apply tendsto_nhds_unique hs
  simpa only [coeff_uniformizerSeries] using
    tendsto_uniformizer_partial_expansion γ m hm hpm hγ π hπ x

theorem powerSeriesEval_surjective (π : O) (hπ : weightedOrder γ m (π : L) = 1) :
    Function.Surjective (powerSeriesEval γ m hm hpm hγ π hπ) := fun x =>
  ⟨uniformizerSeries γ m hm hpm hγ π hπ x,
    powerSeriesEval_uniformizerSeries γ m hm hpm hγ π hπ x⟩

/-- Expansion at any uniformizer identifies the valuation ring with power series over `k`. -/
noncomputable def powerSeriesEquiv (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) : PowerSeries k ≃+* O :=
  RingEquiv.ofBijective (powerSeriesEval γ m hm hpm hγ π hπ)
    ⟨powerSeriesEval_injective γ m hm hpm hγ π hπ,
      powerSeriesEval_surjective γ m hm hpm hγ π hπ⟩

@[simp]
theorem powerSeriesEquiv_apply (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (f : PowerSeries k) :
    powerSeriesEquiv γ m hm hpm hγ π hπ f = powerSeriesEval γ m hm hpm hγ π hπ f := rfl

end Digits

end Camina1997.ArtinSchreier
