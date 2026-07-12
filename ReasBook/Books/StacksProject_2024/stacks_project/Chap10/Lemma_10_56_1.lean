import Mathlib

open scoped DirectSum
open HomogeneousIdeal

universe u v w

section

/- Domain triage:
* source-facing: graded Nakayama over the irrelevant ideal for `ℤ`-graded modules.
* core/canonical owners: `HomogeneousIdeal.irrelevant`, `DirectSum.Decomposition`,
  `SetLike.GradedSMul`, and `LinearMap.reduceModIdeal`.
* bridge/view: reduction modulo the canonical ideal `S₊.toIdeal`.

Primitive data are the graded ring `𝒜`, the graded module pieces, and the canonical irrelevant
ideal `S₊`. The public theorems are source-facing graded Nakayama statements built from those
owners, not replacement owners for the ordinary ungraded Nakayama API.

Relevant owner declarations sampled for this refinement:
* `HomogeneousIdeal.irrelevant`
* `LinearMap.reduceModIdeal`
* `subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent`
* `span_eq_top_of_quotient_span_eq_top_of_isNilpotent`

The last two give the same ungraded statement-shapes but are not exact replacements here: the
graded irrelevance hypothesis carries additional source-facing content.
-/

local instance : AddAction ℕ ℤ := AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

variable {A : Type u} {M : Type v} {N : Type w}
variable [CommRing A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable (𝒜 : ℕ → Submodule A A)

local notation "S₊" => (HomogeneousIdeal.irrelevant 𝒜)

section GradedModule

variable (ℳ : ℤ → Submodule A M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- A finite graded module admits a finite homogeneous generating set. -/
theorem exists_finset_homogeneous_span_eq_top [Module.Finite A M] :
    ∃ s : Finset M,
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
        Submodule.span A (s : Set M) = ⊤ := sorry

/-- Lemma 10.56.1 (1): if `S₊ M = M` and `M` is finite, then `M` is the zero module.
The canonical Lean conclusion is `Subsingleton M`. -/
-- Proof sketch: choose homogeneous generators of minimal degree and use `S₊ M = M` to force the
-- minimal-degree generator to vanish, then induct on the number of generators.
theorem subsingleton_of_irrelevant_ideal_smul_top_eq_top
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := sorry

/-- Lemma 10.56.1 (1), source-facing submodule form. -/
theorem eq_bot_of_irrelevant_ideal_smul_eq_top
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    (⊤ : Submodule A M) = ⊥ := by
  let _ : Subsingleton M := subsingleton_of_irrelevant_ideal_smul_top_eq_top 𝒜 hM
  exact (⊤ : Submodule A M).eq_bot_of_subsingleton

/-- Lemma 10.56.1 (2): if `M = N + S₊ N'` with `N'` finite, then the `ℤ`-graded submodule `N`
already equals `M`. -/
-- Proof sketch: pass to the quotient `M / N`, where the image of `N'` is finite and is equal to
-- its own `S₊`-multiple, then apply part (1).
theorem eq_top_of_sup_irrelevant_ideal_smul_eq_top
    {N N' : Submodule A M}
    (hN : N.IsHomogeneous ℳ)
    (hN' : N'.IsHomogeneous ℳ)
    (hN'fg : N'.FG)
    (hM : N ⊔ S₊.toIdeal • N' = ⊤) :
    N = ⊤ := sorry

end GradedModule

section GradedLinearMap

variable (ℳ : ℤ → Submodule A M) (ℕₘ : ℤ → Submodule A N)
variable [GradedRing 𝒜]
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℕₘ] [SetLike.GradedSMul 𝒜 ℕₘ]

/-- Lemma 10.56.1 (3): a map of `ℤ`-graded modules is surjective if the induced map modulo `S₊` is
surjective and the target is finite as a graded module. The quotient reduction is expressed by the
canonical owner `LinearMap.reduceModIdeal`. -/
-- Proof sketch: apply part (2) to the image submodule of `f`, using the surjectivity on quotients
-- to write the target as the image plus `S₊` times the whole target.
theorem surjective_of_irrelevant_reduceModIdeal_surjective
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i))
    [Module.Finite A M]
    (hquot : Function.Surjective (f.reduceModIdeal S₊.toIdeal)) :
    Function.Surjective f := sorry

end GradedLinearMap

section GradedModule

variable (ℳ : ℤ → Submodule A M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- Lemma 10.56.1 (4): a finite set of homogeneous elements generating `M / S₊ M` already
generates the finite `ℤ`-graded module `M`. -/
-- Proof sketch: map the direct sum of the twists `S(-dᵢ)` attached to the chosen homogeneous
-- generators to `M` and apply part (3) to the induced surjective map on the quotients modulo `S₊`.
theorem span_eq_top_of_quotient_span_eq_top_of_homogeneous
    [Module.Finite A M]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan :
      Submodule.span A
        ((S₊.toIdeal • (⊤ : Submodule A M)).mkQ '' (s : Set M)) = ⊤) :
    Submodule.span A (s : Set M) = ⊤ := sorry

end GradedModule

end
