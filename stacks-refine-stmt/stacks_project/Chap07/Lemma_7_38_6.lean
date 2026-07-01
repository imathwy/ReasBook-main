import Mathlib
import stacks_project.Chap07.Definition_7_14_1
import stacks_project.Chap07.Lemma_7_32_8
import stacks_project.Chap07.Lemma_7_34_2
import stacks_project.Chap07.Lemma_7_38_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology

universe w v₁ v₂ u₁ u₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.38.6:
- primary domain: points of Grothendieck sites and morphisms of sites;
- sampled owner API:
  `IsMorphismOfSites`,
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `Point.sheafFiberComapIso`,
  the instance `IsMorphismOfSites J typesGrothendieckTopology p.fiber` from Lemma 7.32.8;
- source/core/bridge triage:
  `source-facing`: the pointwise hypothesis that each composite `u ⋙ Φ.fiber` comes from a point
    of `(C, J)`, indexed canonically by `P.FullSubcategory`;
  `core/canonical`: the owner predicate `IsMorphismOfSites J K u`;
  `bridge/view`: the theorem below, which upgrades the source-facing pointwise condition along a
    conservative family of points to the canonical morphism-of-sites owner.

Primitive data are only the continuous functor `u`, the conservative family `P`, and the
pointwise realization hypothesis on `P.FullSubcategory`. Exactness of stalk functors and the
induced morphism-of-sites structure are derived owner API, so this file should remain a thin
bridge rather than introducing any parallel wrapper around `IsMorphismOfSites`.
-/
-- Proof sketch: for each point `Φ` in the conservative family, choose a point of `(C, J)` whose
-- fiber functor is `u ⋙ Φ.fiber`. Then the stalk functor at `Φ` after applying the inverse-image
-- functor `u.sheafPullback` identifies with the stalk functor of that chosen point, hence is exact.
-- Exactness of `u.sheafPullback` can be checked on a conservative family of points by
-- Lemma 7.38.2, so `u` defines a morphism of sites by Definition 7.14.1.
/-- Lemma 7.38.6: if `u : C ⥤ D` is continuous, `P` is a conservative family of points of
`(D, K)`, and for every point `Φ` in `P` the composite fiber functor `u ⋙ Φ.fiber` defines a point
of `(C, J)`, then `u` defines a morphism of sites `f : (D, K) ⟶ (C, J)`. -/
theorem isMorphismOfSites_of_conservativeFamilyOfPoints_of_pointwiseComposite
    (u : C ⥤ D) [u.IsContinuous J K]
    (P : ObjectProperty (Point.{w} K))
    (hP : P.IsConservativeFamilyOfPoints)
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber) :
    IsMorphismOfSites J K u := sorry

end
