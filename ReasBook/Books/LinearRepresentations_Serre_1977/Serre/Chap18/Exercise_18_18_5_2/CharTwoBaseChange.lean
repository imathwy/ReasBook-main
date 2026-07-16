import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleDegrees
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Base change of the permutation-augmentation representation (support for Exercise 18.5.2)

This file proves, over an **arbitrary** field extension `k₀ → k` and a finite nonempty `G`-set `X`,
that the scalar extension of the permutation-augmentation representation over `k₀` is equivalent to
the permutation-augmentation representation over `k`:

`scalarExtension (permutationAugmentationRepresentation k₀ G X) ≅ permutationAugmentationRepresentation k G X`.

This is a *structural* base-change statement (no characteristic restriction, no invertibility of
`|G|` or `|X|`), used in the characteristic-`2` branch of the completeness sub-lemma where Maschke's
theorem (and hence the character ⟹ isomorphism route) is unavailable.
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation
open scoped TensorProduct

namespace Representation

universe u v w

/-- Precomposing a representation equivalence with a monoid homomorphism on the group. -/
def Equiv.precomp {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]
    {V : Type*} [AddCommGroup V] [Module k V] {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => by
    have := e.isIntertwining' (f h)
    simpa using this)

/-- The coefficientwise base-change map on the permutation modules, induced by the algebra map
`k₀ → k`. -/
private def augBaseChangeCoeff (k₀ : Type u) [Field k₀] (k : Type v) [Field k] [Algebra k₀ k]
    (X : Type*) : (X →₀ k₀) →ₗ[k₀] (X →₀ k) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap k₀ k)

private theorem augBaseChangeCoeff_single {k₀ : Type u} [Field k₀] {k : Type v} [Field k]
    [Algebra k₀ k] {X : Type*} (x : X) (r : k₀) :
    augBaseChangeCoeff k₀ k X (Finsupp.single x r) = Finsupp.single x (algebraMap k₀ k r) := by
  rw [augBaseChangeCoeff, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply]

private theorem augLinearMap_augBaseChangeCoeff {k₀ : Type u} [Field k₀] {k : Type v} [Field k]
    [Algebra k₀ k] {X : Type*} (f : X →₀ k₀) :
    permutationAugmentationLinearMap k X (augBaseChangeCoeff k₀ k X f)
      = algebraMap k₀ k (permutationAugmentationLinearMap k₀ X f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single x r =>
      rw [augBaseChangeCoeff_single]
      simp [permutationAugmentationLinearMap]

private theorem augBaseChangeCoeff_ofMulAction {k₀ : Type u} [Field k₀] {k : Type v} [Field k]
    [Algebra k₀ k] {G : Type w} [Group G] {X : Type*} [MulAction G X] (g : G) (f : X →₀ k₀) :
    augBaseChangeCoeff k₀ k X (ofMulAction k₀ G X g f)
      = ofMulAction k G X g (augBaseChangeCoeff k₀ k X f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single x r =>
      rw [ofMulAction_single, augBaseChangeCoeff_single, augBaseChangeCoeff_single,
        ofMulAction_single]

private theorem scalarExtension_apply_eq_baseChange {k₀ : Type u} [Field k₀] {k : Type v} [Field k]
    [Algebra k₀ k] {G : Type w} [Group G] {W : Type*} [AddCommGroup W] [Module k₀ W]
    (ρ : Representation k₀ G W) (g : G) :
    (scalarExtension (k := k) ρ) g = LinearMap.baseChange k (ρ g) := rfl

/-- **Base change of the augmentation representation.**  Over any field extension `k₀ → k` and a
finite nonempty `G`-set `X`, the scalar extension of the permutation-augmentation representation over
`k₀` is equivalent to the permutation-augmentation representation over `k`. -/
theorem scalarExtension_permutationAugmentationRepresentation_equiv
    {k₀ : Type u} [Field k₀] {k : Type v} [Field k] [Algebra k₀ k]
    {G : Type w} [Group G] {X : Type*} [MulAction G X] [Finite X] [Nonempty X] :
    Nonempty
      ((Representation.scalarExtension (k := k)
          (permutationAugmentationRepresentation k₀ G X)).Equiv
        (permutationAugmentationRepresentation k G X)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let W₀ := (permutationAugmentationSubrepresentation k₀ G X).toSubmodule
  let W := (permutationAugmentationSubrepresentation k G X).toSubmodule
  -- The coefficient map sends the `k₀`-augmentation kernel into the `k`-augmentation kernel.
  have hmem : ∀ z : ↥W₀, augBaseChangeCoeff k₀ k X (z : X →₀ k₀) ∈ W := by
    intro z
    have hz : permutationAugmentationLinearMap k₀ X (z : X →₀ k₀) = 0 := by
      have hz' : (z : X →₀ k₀) ∈ LinearMap.ker (permutationAugmentationLinearMap k₀ X) := z.2
      rwa [LinearMap.mem_ker] at hz'
    rw [show W = LinearMap.ker (permutationAugmentationLinearMap k X) from rfl,
      LinearMap.mem_ker, augLinearMap_augBaseChangeCoeff, hz, map_zero]
  -- The underlying `k`-linear base-change map into the permutation module.
  let E : k ⊗[k₀] ↥W₀ →ₗ[k] (X →₀ k) :=
    LinearMap.liftBaseChange k ((augBaseChangeCoeff k₀ k X).comp (Submodule.subtype W₀))
  have hE : ∀ (a : k) (z : ↥W₀),
      E (a ⊗ₜ[k₀] z) = a • augBaseChangeCoeff k₀ k X (z : X →₀ k₀) := by
    intro a z
    rfl
  have hrange : ∀ t : k ⊗[k₀] ↥W₀, E t ∈ W := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact W.zero_mem
    | tmul a z => rw [hE]; exact W.smul_mem a (hmem z)
    | add p q hp hq => rw [map_add]; exact W.add_mem hp hq
  -- Codomain-restrict to land in the augmentation kernel `W`.
  let e₀lin : k ⊗[k₀] ↥W₀ →ₗ[k] ↥W := LinearMap.codRestrict W E hrange
  have he0 : ∀ z : k ⊗[k₀] ↥W₀, (e₀lin z : X →₀ k) = E z := by
    intro z
    exact LinearMap.codRestrict_apply W E z
  -- Coercion of the subrepresentation actions to the ambient permutation actions.
  have hρcoe : ∀ (g : G) (z : ↥W),
      ((permutationAugmentationRepresentation k G X) g z : X →₀ k) = ofMulAction k G X g (z : X →₀ k) :=
    fun _ _ => rfl
  have hρ0coe : ∀ (g : G) (z : ↥W₀),
      ((permutationAugmentationRepresentation k₀ G X) g z : X →₀ k₀)
        = ofMulAction k₀ G X g (z : X →₀ k₀) :=
    fun _ _ => rfl
  -- Equivariance of the base-change map.
  have hequiv : ∀ g : G,
      e₀lin ∘ₗ ((scalarExtension (k := k) (permutationAugmentationRepresentation k₀ G X)) g)
        = ((permutationAugmentationRepresentation k G X) g) ∘ₗ e₀lin := by
    intro g
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul a w =>
        apply Subtype.ext
        rw [LinearMap.comp_apply, LinearMap.comp_apply,
          scalarExtension_apply_eq_baseChange, LinearMap.baseChange_tmul, hρcoe]
        simp only [he0, hE]
        rw [hρ0coe, map_smul, augBaseChangeCoeff_ofMulAction]
  -- Dimension count.
  haveI : FiniteDimensional k₀ ↥W₀ := inferInstance
  haveI : FiniteDimensional k ↥W := inferInstance
  haveI : FiniteDimensional k (k ⊗[k₀] ↥W₀) := inferInstance
  have hfin_dom : Module.finrank k (k ⊗[k₀] ↥W₀) = Nat.card X - 1 := by
    rw [Module.finrank_baseChange]
    exact permutationAugmentationSubrepresentation_finrank (F := k₀) (G := G) (X := X)
  have hfin_cod : Module.finrank k (↥W) = Nat.card X - 1 :=
    permutationAugmentationSubrepresentation_finrank (F := k) (G := G) (X := X)
  have hfin_eq : Module.finrank k (k ⊗[k₀] ↥W₀) = Module.finrank k (↥W) := by
    rw [hfin_dom, hfin_cod]
  -- Surjectivity of the base-change map.
  have hsurj : Function.Surjective e₀lin := by
    intro y
    let fy : X →₀ k := (y : X →₀ k)
    let x₀ : X := Classical.arbitrary X
    have hsmem : ∀ x : X,
        (Finsupp.single x (1 : k₀) - Finsupp.single x₀ (1 : k₀)) ∈ W₀ := by
      intro x
      rw [show W₀ = LinearMap.ker (permutationAugmentationLinearMap k₀ X) from rfl,
        LinearMap.mem_ker, map_sub]
      simp [permutationAugmentationLinearMap]
    let svec : X → ↥W₀ := fun x => ⟨_, hsmem x⟩
    have haug : ∀ x : X,
        augBaseChangeCoeff k₀ k X ((svec x : X →₀ k₀))
          = Finsupp.single x (1 : k) - Finsupp.single x₀ (1 : k) := by
      intro x
      show augBaseChangeCoeff k₀ k X (Finsupp.single x 1 - Finsupp.single x₀ 1) = _
      rw [map_sub, augBaseChangeCoeff_single, augBaseChangeCoeff_single, map_one]
    have hAf : permutationAugmentationLinearMap k X fy = 0 := by
      have hy : (fy : X →₀ k) ∈ LinearMap.ker (permutationAugmentationLinearMap k X) := y.2
      rwa [LinearMap.mem_ker] at hy
    have hsum0 : ∑ x ∈ fy.support, fy x = 0 := by
      have hval : permutationAugmentationLinearMap k X fy = ∑ x ∈ fy.support, fy x := by
        simp [permutationAugmentationLinearMap, Finsupp.lsum_apply, Finsupp.sum]
      rw [← hval]; exact hAf
    refine ⟨∑ x ∈ fy.support, fy x ⊗ₜ[k₀] svec x, ?_⟩
    apply Subtype.ext
    rw [he0, map_sum]
    have hterm : ∀ x ∈ fy.support,
        E (fy x ⊗ₜ[k₀] svec x)
          = fy x • (Finsupp.single x (1 : k) - Finsupp.single x₀ (1 : k)) := by
      intro x hx
      rw [hE, haug]
    rw [Finset.sum_congr rfl hterm]
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ x ∈ fy.support, fy x • Finsupp.single x (1 : k) = fy := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      exact Finsupp.sum_single fy
    have h2 : ∑ x ∈ fy.support, fy x • Finsupp.single x₀ (1 : k) = 0 := by
      rw [← Finset.sum_smul, hsum0, zero_smul]
    rw [h1, h2, sub_zero]
  -- Equal dimensions + surjectivity ⟹ bijectivity.
  have hbij : Function.Bijective e₀lin :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mpr hsurj, hsurj⟩
  let e : (k ⊗[k₀] ↥W₀) ≃ₗ[k] ↥W := LinearEquiv.ofBijective e₀lin hbij
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  have hcoe : (e : (k ⊗[k₀] ↥W₀) →ₗ[k] ↥W) = e₀lin := rfl
  rw [hcoe]
  exact hequiv g

end Representation
