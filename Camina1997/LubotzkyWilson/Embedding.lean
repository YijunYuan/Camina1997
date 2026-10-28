/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.GroupTheory.FiniteDerived
public import Camina1997.LubotzkyWilson.TwoGenerator
public import Camina1997.ProP.QuotientTower
public import Camina1997.ProP.ProductEmbedding

/-!
# The Lubotzky–Wilson embedding for a countably based pro-`p` group

The finite quotients of a countably based pro-`p` group embed in finite derived
groups. Their product embeds in the closed two-generator hull constructed by
Lubotzky and Wilson. This gives the auxiliary finitely generated pro-`p` group
needed for Camina's universality theorem.

The sparse-coordinate base is `p²`, which is greater than two for every prime
and keeps all cyclic groups of `p`-power order.

Reference: Lubotzky–Wilson (1984), pp. 398–399; Camina (1997), Corollary 2.
-/

@[expose] public section

open scoped Topology

namespace Camina1997.LubotzkyWilson

universe u

section FiniteDerivedProduct

variable (A : ℕ → Type u) [∀ n, Group (A n)] [∀ n, Finite (A n)]
  [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)]
  [∀ n, TopologicalSpace (A n ≀ᵣ Multiplicative (ZMod (Nat.card (A n))))]

/-- The product of the constant-function embeddings into finite derived groups. -/
noncomputable def finiteDerivedProductHom :
    ContinuousMonoidHom (∀ n, A n)
      (∀ n, commutator (A n ≀ᵣ Multiplicative (ZMod (Nat.card (A n))))) where
  toFun a n := finiteDerivedEmbedding (a n)
  map_one' := funext fun _ => map_one finiteDerivedEmbedding
  map_mul' _ _ := funext fun _ => map_mul finiteDerivedEmbedding _ _
  continuous_toFun := continuous_pi fun n =>
    (show Continuous (finiteDerivedEmbedding (A := A n)) from continuous_of_discreteTopology).comp
      (continuous_apply n)

/-- The product of the finite derived embeddings is injective. -/
theorem finiteDerivedProductHom_injective : Function.Injective (finiteDerivedProductHom A) := by
  intro a b h
  funext n
  exact finiteDerivedEmbedding_injective (congrFun h n)

/-- The product of the finite derived embeddings is a closed embedding into Hausdorff targets. -/
theorem finiteDerivedProductHom_isClosedEmbedding
    [∀ n, T2Space (A n ≀ᵣ Multiplicative (ZMod (Nat.card (A n))))] :
    Topology.IsClosedEmbedding (finiteDerivedProductHom A) :=
  (finiteDerivedProductHom A).continuous.isClosedEmbedding (finiteDerivedProductHom_injective A)

end FiniteDerivedProduct

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsProPGroup p G] [Filter.IsCountablyGenerated (𝓝 (1 : G))]

/-- The Lubotzky–Wilson construction embeds every countably based pro-`p` group as a closed
subgroup of a topologically finitely generated pro-`p` group. -/
theorem exists_topologicallyFG_proP_closedEmbedding :
    ∃ H : Type u, ∃ hH : Group H, letI := hH
      ∃ tH : TopologicalSpace H, letI := tH
        IsProPGroup p H ∧ TopologicallyFG H ∧
          ∃ e : ContinuousMonoidHom G H, Topology.IsClosedEmbedding e := by
  obtain ⟨N, hfinite, hpgroup, hdiag⟩ :=
    IsProPGroup.exists_closedEmbedding_quotient_product (p := p) (G := G)
  let A (n : ℕ) := G ⧸ (N n).toSubgroup
  let (n : ℕ) : Finite (A n) := hfinite n
  let (n : ℕ) : DiscreteTopology (A n) :=
    inferInstanceAs (DiscreteTopology (G ⧸ (N n).toOpenSubgroup.toSubgroup))
  let (n : ℕ) : NeZero (Nat.card (A n)) := ⟨Nat.card_pos.ne'⟩
  let F (n : ℕ) := A n ≀ᵣ Multiplicative (ZMod (Nat.card (A n)))
  let (n : ℕ) : Finite (F n) := inferInstance
  let (n : ℕ) : TopologicalSpace (F n) := ⊥
  let (n : ℕ) : DiscreteTopology (F n) := ⟨rfl⟩
  have hF (n : ℕ) : IsPGroup p (F n) := isPGroup_finiteDerivedTarget (hpgroup n)
  have hq : 2 < p ^ 2 := by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hmul : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
    simpa only [pow_two] using lt_of_lt_of_le (by decide : 2 < 2 * 2) hmul
  let H := twoGeneratorHull F (p ^ 2)
  let e : ContinuousMonoidHom G H :=
    (derivedProductEmbedding F (p ^ 2) hq).comp
      ((finiteDerivedProductHom A).comp (IsProPGroup.quotientDiagonal N))
  have he : Topology.IsClosedEmbedding e :=
    (derivedProductEmbedding_isClosedEmbedding F (p ^ 2) hq).comp
      ((finiteDerivedProductHom_isClosedEmbedding A).comp hdiag)
  exact ⟨H, inferInstance, inferInstance,
    isProP_twoGeneratorHull F (p ^ 2) hF hq ⟨2, rfl⟩,
    topologicallyFG_twoGeneratorHull F (p ^ 2), e, he⟩

end Camina1997.LubotzkyWilson
