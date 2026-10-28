/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Embedding a product into a closed subgroup

A closed subgroup of a product containing every one-coordinate image contains
the entire product image. The proof approximates each point by its restrictions
to finite sets of coordinates. For compact source groups and Hausdorff targets,
injective coordinate maps give a closed embedding into that subgroup.
-/

@[expose] public section

open scoped Topology

namespace Camina1997

variable {ι : Type*} [DecidableEq ι] {W : ι → Type*}
  [∀ i, Group (W i)] [∀ i, TopologicalSpace (W i)]

/-- A closed subgroup containing every one-coordinate part of a point contains the point. -/
theorem pi_mem_of_mulSingle_mem (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (w : ∀ i, W i) (hw : ∀ i, Pi.mulSingle i (w i) ∈ H) : w ∈ H := by
  let trunc : Finset ι → ∀ i, W i := fun s i => if i ∈ s then w i else 1
  have htrunc : ∀ s, trunc s ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : trunc ∅ = 1 := by funext i; simp [trunc]
      rw [he]
      exact H.one_mem
    | @insert i s hi hs =>
      have heq : trunc (insert i s) = Pi.mulSingle i (w i) * trunc s := by
        funext j
        by_cases hij : i = j
        · subst j
          simp [trunc, hi]
        · simp [trunc, Ne.symm hij]
      rw [heq]
      exact H.mul_mem (hw i) hs
  have htendsto : Filter.Tendsto trunc Filter.atTop (𝓝 w) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with s hs
    have hi : i ∈ s := hs (by simp)
    simp [trunc, hi]
  exact hH.mem_of_tendsto htendsto (Filter.Eventually.of_forall htrunc)

variable {D : ι → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]

/-- The product of coordinate homomorphisms lands in a closed subgroup whenever all of its
one-coordinate images do. -/
theorem product_map_mem_of_mulSingle_mem (e : ∀ i, ContinuousMonoidHom (D i) (W i))
    (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (hsingle : ∀ i d, Pi.mulSingle i (e i d) ∈ H) (d : ∀ i, D i) :
    (fun i => e i (d i)) ∈ H :=
  pi_mem_of_mulSingle_mem H hH _ (fun i => hsingle i (d i))

/-- The continuous product homomorphism into a closed subgroup containing its coordinate images. -/
def productIntoClosedSubgroup (e : ∀ i, ContinuousMonoidHom (D i) (W i))
    (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (hsingle : ∀ i d, Pi.mulSingle i (e i d) ∈ H) :
    ContinuousMonoidHom (∀ i, D i) H where
  toFun d := ⟨fun i => e i (d i), product_map_mem_of_mulSingle_mem e H hH hsingle d⟩
  map_one' := Subtype.ext (funext fun i => map_one (e i))
  map_mul' d d' := Subtype.ext (funext fun i => map_mul (e i) (d i) (d' i))
  continuous_toFun :=
    (continuous_pi fun i => (e i).continuous.comp (continuous_apply i)).subtype_mk _

@[simp]
theorem productIntoClosedSubgroup_apply (e : ∀ i, ContinuousMonoidHom (D i) (W i))
    (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (hsingle : ∀ i d, Pi.mulSingle i (e i d) ∈ H) (d : ∀ i, D i) (i : ι) :
    (productIntoClosedSubgroup e H hH hsingle d : ∀ i, W i) i = e i (d i) := rfl

/-- Coordinatewise injectivity makes the product homomorphism into the subgroup injective. -/
theorem productIntoClosedSubgroup_injective (e : ∀ i, ContinuousMonoidHom (D i) (W i))
    (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (hsingle : ∀ i d, Pi.mulSingle i (e i d) ∈ H)
    (he : ∀ i, Function.Injective (e i)) :
    Function.Injective (productIntoClosedSubgroup e H hH hsingle) := by
  intro d d' h
  funext i
  exact he i (congrArg (fun z : H => (z : ∀ i, W i) i) h)

/-- Compact products embed as closed subgroups when every coordinate map is injective and
the target groups are Hausdorff. -/
theorem productIntoClosedSubgroup_isClosedEmbedding [∀ i, CompactSpace (D i)]
    [∀ i, T2Space (W i)] (e : ∀ i, ContinuousMonoidHom (D i) (W i))
    (H : Subgroup (∀ i, W i)) (hH : IsClosed (H : Set (∀ i, W i)))
    (hsingle : ∀ i d, Pi.mulSingle i (e i d) ∈ H)
    (he : ∀ i, Function.Injective (e i)) :
    Topology.IsClosedEmbedding (productIntoClosedSubgroup e H hH hsingle) :=
  (productIntoClosedSubgroup e H hH hsingle).continuous.isClosedEmbedding
    (productIntoClosedSubgroup_injective e H hH hsingle he)

end Camina1997
