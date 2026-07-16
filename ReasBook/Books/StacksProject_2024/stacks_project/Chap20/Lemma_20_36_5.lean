import StacksProject_2024.stacks_project.Chap20.Lemma_20_36_4

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma `20.36.5`:
- primary domain: sheaf-cohomology towers of `A`-module sheaves on a topological space, together
  with the canonical Mittag-Leffler owner for sequential inverse systems;
- sampled owner declarations:
  * `siteModuleCohomologyTower` from `Chap21/Lemma_21_22_1`;
  * `siteModuleCohomologyModuleTower` and `siteModuleCohomologyTransitionMapLinear` from
    `Lemma_20_36_4`;
  * `topologicalSpaceModuleStepShortExactCondition` from `Lemma_20_36_3`;
  * `SequentialInverseSystem.transitionMap` and `SequentialInverseSystem.IsMittagLeffler` from
    `Definition_12_31_2`;
- best owner abstraction: this lemma is `source-facing`; its `core/canonical` owners are the
  cohomology towers `siteModuleCohomologyTower` and `siteModuleCohomologyModuleTower`, the
  canonical linear transition-map bridge `siteModuleCohomologyTransitionMapLinear`, the stepwise
  short-exactness predicate `topologicalSpaceModuleStepShortExactCondition`, and the canonical
  cohomology comparison maps into stage `1`;
- primitive data: the tower `ℱ`, the degree `p`, the stepwise short exactness hypothesis, and the
  finite-length / finite-intersection hypothesis on the actual images of the canonical
  comparison maps;
- derived API: the image submodules in stage `1`, their intersection, and the final
  Mittag-Leffler conclusion.

Source/core/bridge triage:
- `source-facing`: the intersection-of-images hypothesis and the final Mittag-Leffler theorem;
- `core/canonical`: `siteModuleCohomologyTower`, `siteModuleCohomologyModuleTower`,
  `topologicalSpaceModuleStepShortExactCondition`, `SequentialInverseSystem.transitionMap`, and
  `SequentialInverseSystem.IsMittagLeffler`;
- `bridge/view`: the canonical `A`-linear structure on stagewise cohomology groups and on their
  transition maps, exposed by `siteModuleCohomologyTransitionMapLinear`.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open CategoryTheory.SequentialInverseSystem
open scoped ZeroObject

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- The image in stage `1` of the degree-`q` cohomology map coming from the positive stage
`n + 1`, written in the canonical `A`-module structure on
`siteModuleCohomologyModuleTower ℱ q`. Equivalently, this is the image into stage `0` of
the shifted module-valued cohomology tower `(siteModuleCohomologyModuleTower ℱ q).shift 1`. -/
abbrev topologicalSpaceModuleCohomologyToFirstImage
    (ℱ : SequentialInverseSystem ModSheaf) (q n : ℕ) :
    Submodule A ((siteModuleCohomologyFunctor q).obj (ℱ.obj (op 1))) :=
  LinearMap.range <|
    siteModuleCohomologyTransitionMapLinear
      ℱ q (Nat.succ_le_succ (Nat.zero_le n))

/-- The intersection of the images of the degree-`q` cohomology maps into stage `1`. -/
def topologicalSpaceModuleCohomologyToFirstImageIntersection
    (ℱ : SequentialInverseSystem ModSheaf) (q : ℕ) :
    Submodule A ((siteModuleCohomologyFunctor q).obj (ℱ.obj (op 1))) :=
  ⨅ n : ℕ, topologicalSpaceModuleCohomologyToFirstImage ℱ q n

/-- Helper for Lemma 20.36.5: the intersection of the images into stage `1` is contained in each
individual image. -/
lemma topologicalSpaceModuleCohomologyToFirstImageIntersection_le
    (ℱ : SequentialInverseSystem ModSheaf) (q n : ℕ) :
    topologicalSpaceModuleCohomologyToFirstImageIntersection ℱ q ≤
      topologicalSpaceModuleCohomologyToFirstImage ℱ q n := by
  intro x hx
  -- Membership in the infimum means membership in every stagewise image.
  exact (Submodule.mem_iInf _).1 hx n

/-- Helper for Lemma 20.36.5: if one stagewise image into stage `1` has finite length, then the
fixed intersection of all such images has finite length as well. -/
lemma topologicalSpaceModuleCohomologyToFirstImageIntersection_isFiniteLength_of_stage
    (ℱ : SequentialInverseSystem ModSheaf) (q n : ℕ)
    (hfinite : IsFiniteLength A (topologicalSpaceModuleCohomologyToFirstImage ℱ q n)) :
    IsFiniteLength A (topologicalSpaceModuleCohomologyToFirstImageIntersection ℱ q) := by
  let hle :=
    topologicalSpaceModuleCohomologyToFirstImageIntersection_le ℱ q n
  let ι :
      ↥(topologicalSpaceModuleCohomologyToFirstImageIntersection ℱ q) →ₗ[A]
        ↥(topologicalSpaceModuleCohomologyToFirstImage ℱ q n) :=
    Submodule.inclusion hle
  -- The fixed intersection is a submodule of the chosen finite-length image, so finite length
  -- descends along the injective subtype inclusion.
  exact IsFiniteLength.of_injective hfinite (Submodule.inclusion_injective hle)

-- Proof sketch: apply the criterion of Lemma `20.35.2` to the principal ideal `(f)` and the tail
-- of the canonical module-valued cohomology tower starting at stage `1`. Under the stepwise short
-- exactness hypothesis, the ideal-power tower `(f)^n ℱ_{m + 1}` is identified with the shifted
-- tower `ℱ_{m + 1 - n}`, so the eventual ranges `N_n` are controlled by the images of
-- `H^{p + 1}(X, ℱ_m) → H^{p + 1}(X, ℱ_1)`. The finite-length or Noetherian finite-intersection
-- hypothesis then yields the required ACC input, and Lemma `20.35.2` gives the Mittag-Leffler
-- property for the tail `n ↦ H^p(X, ℱ_{n + 1})`.
/-- Lemma 20.36.5: let `A` be a ring, let `f ∈ A`, let `X` be a topological space, and let
`(ℱ_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X`. Assume the
stepwise short exactness condition `(1)` from Lemma `20.36.1`. Also assume that the degree
`p + 1` cohomology image `Im(H^{p + 1}(X, ℱ_{n + 1}) → H^{p + 1}(X, ℱ_1))` has
finite length as an `A`-module for some positive stage `n + 1`, or `A` is Noetherian and the
intersection of these images is a finite `A`-module. Then the tail inverse system of
`A`-modules `n ↦ H^p(X, ℱ_{n + 1})`, formalized by
`(siteModuleCohomologyModuleTower ℱ p).shift 1`, satisfies the Mittag-Leffler condition. -/
@[stacks 0DXG]
theorem topologicalSpaceModuleCohomologyTower_isMittagLeffler_of_principalIdeal_stepShortExactCondition_of_imageFiniteLength_or_intersectionFinite
    (f : A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (p : ℕ)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ)
    (hfinite :
      (∃ n : ℕ, IsFiniteLength A (topologicalSpaceModuleCohomologyToFirstImage
        ℱ (p + 1) n)) ∨
      (IsNoetherianRing A ∧
        Module.Finite A (topologicalSpaceModuleCohomologyToFirstImageIntersection
          ℱ (p + 1)))) :
    ((siteModuleCohomologyModuleTower ℱ p).shift 1).IsMittagLeffler := by
  sorry

end

end CategoryTheory
