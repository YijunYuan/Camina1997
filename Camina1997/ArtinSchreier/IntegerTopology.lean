/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Completeness
public import Camina1997.ArtinSchreier.Residue
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# The complete valuation ring of the reduced-pole extension

The integral elements form a closed, complete, linearly topologized ring.
Uniformizers are topologically nilpotent, so power series can be evaluated there.
-/

@[expose] public section

open Polynomial Filter
open scoped Topology Uniformity

namespace Valued

/-- The valuation ring has an ideal basis of neighborhoods of zero. -/
theorem integer_isLinearTopology {R Γ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ] [h : Valued R Γ] :
    IsLinearTopology h.v.integer h.v.integer := by
  refine IsLinearTopology.mk_of_hasBasis h.v.integer
    (p := fun _ : h.v.ValueGroup₀ˣ => True)
    (s := fun a => h.v.ltIdeal
      (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (h.v : R →*₀ Γ))).toMonoidHom a)) ?_
  rw [nhds_subtype_eq_comap]
  have hb := (Valued.hasBasis_nhds_zero R Γ).comap
    (Subtype.val : h.v.integer → R)
  convert hb using 1
  ext a x
  simp only [SetLike.mem_coe, Valuation.mem_ltIdeal_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    Valuation.restrict_lt_iff_lt_embedding, Units.coe_map]
  rfl

end Valued

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ) (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ

/-- The weighted topology is Hausdorff. -/
theorem weightedValued_t2Space :
    letI := weightedValued γ m hm hpm hγ
    T2Space L := by
  let := weightedValued γ m hm hpm hγ
  exact (rootBasisUniformEquiv γ m hm hpm hγ).toHomeomorph.symm.t2Space

/-- The valuation ring inherits the Hausdorff topology. -/
theorem weightedInteger_t2Space :
    letI := weightedValued γ m hm hpm hγ
    T2Space O := by
  let := weightedValued γ m hm hpm hγ
  let := weightedValued_t2Space γ m hm hpm hγ
  infer_instance

/-- Integral elements are closed in the weighted valuation topology. -/
theorem isClosed_weightedInteger :
    letI := weightedValued γ m hm hpm hγ
    IsClosed (O : Set L) := by
  let := weightedValued γ m hm hpm hγ
  exact Valued.isClosed_integer L

/-- The valuation ring is complete for the topology induced from the quotient field. -/
theorem weightedInteger_completeSpace :
    letI := weightedValued γ m hm hpm hγ
    CompleteSpace O := by
  let := weightedValued γ m hm hpm hγ
  let := weightedValued_completeSpace γ m hm hpm hγ
  exact (isClosed_weightedInteger γ m hm hpm hγ).isComplete.completeSpace_coe

/-- Every integer order ball is closed, so order bounds pass to limits. -/
theorem isClosed_weightedOrder_ge (n : ℤ) :
    letI := weightedValued γ m hm hpm hγ
    IsClosed {x : L | (n : WithTop ℤ) ≤ weightedOrder γ m x} := by
  let := weightedValued γ m hm hpm hγ
  obtain ⟨a, ha⟩ := exists_weightedOrder_eq γ m hpm n
  have h := Valued.isClosed_closedBall L (Valued.v.restrict a)
  simp only [Valuation.restrict_le_iff] at h
  change IsClosed {x : L | weightedOrder γ m a ≤ weightedOrder γ m x} at h
  simpa only [ha] using h

/-- Open valuation balls give a basis of ideals in the integer ring. -/
theorem weightedInteger_isLinearTopology :
    letI := weightedValued γ m hm hpm hγ
    IsLinearTopology O O := by
  let := weightedValued γ m hm hpm hγ
  exact Valued.integer_isLinearTopology

/-- Powers of an element of weighted order one converge to zero. -/
theorem weightedValued_tendsto_pow_zero {π : L} (hπ : weightedOrder γ m π = 1) :
    letI := weightedValued γ m hm hpm hγ
    Tendsto (fun n : ℕ => π ^ n) atTop (𝓝 0) := by
  let := weightedValued γ m hm hpm hγ
  have hb := nhds_basis_uniformity
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ) (x := (0 : L))
  rw [hb.tendsto_right_iff]
  intro n _
  filter_upwards [eventually_ge_atTop (n.natAbs + 1)] with j hj
  rw [zero_sub, weightedOrder_neg]
  have hp := (weightedValuation γ m hm hpm hγ).map_pow π j
  change weightedOrder γ m (π ^ j) = j • weightedOrder γ m π at hp
  rw [hp, hπ]
  have hn : n < (j : ℤ) := by omega
  rw [nsmul_one]
  exact_mod_cast hn

/-- A uniformizer in the valuation ring is topologically nilpotent. -/
theorem weightedInteger_isTopologicallyNilpotent
    {π : O} (hπ : weightedOrder γ m (π : L) = 1) :
    letI := weightedValued γ m hm hpm hγ
    IsTopologicallyNilpotent π := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun n : ℕ => π ^ n) atTop (𝓝 0)
  rw [tendsto_subtype_rng]
  exact weightedValued_tendsto_pow_zero γ m hm hpm hγ hπ

end Camina1997.ArtinSchreier
