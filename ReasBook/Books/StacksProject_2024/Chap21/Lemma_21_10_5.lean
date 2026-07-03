import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat)]

/-
Domain-style sampling for Lemma 21.10.5:
- primary domain: right derived functors of the canonical inclusion `sheafToPresheaf` for abelian
  sheaves on a site, and the canonical cohomology-presheaf owner `Sheaf.cohomologyPresheafFunctor`;
- sampled owner declarations:
  `sheafToPresheaf`,
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.cohomologyPresheaf`,
  `CategoryTheory.evaluation`;
- best owner abstraction: the functor-level comparison between
  `(sheafToPresheaf J AddCommGrpCat).rightDerived p` and `Sheaf.cohomologyPresheafFunctor J p`;
- primitive data: the site `(C, J)` and the cohomological degree `p`;
- derived API here: objectwise evaluation at a sheaf `F`, yielding the comparison with
  `F.cohomologyPresheaf p`.

Source/core/bridge triage:
- `source-facing`: the functor-level comparison identifying the degree-`p` right derived functor of
  the inclusion with the cohomology presheaf functor;
- `core/canonical`: the owners `sheafToPresheaf`, `Sheaf.cohomologyPresheafFunctor`, and
  `Sheaf.cohomologyPresheaf`;
- `bridge/view`: evaluating the source-facing functor isomorphism at a specific abelian sheaf `F`.

The objectwise statement below is therefore derived API and should be obtained from the owner
theorem rather than carried as a parallel primitive result.
-/

-- The left-exactness clause of the textbook lemma is already available in mathlib as the instance
-- `PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat)`.
-- Proof sketch: compute the higher right derived functors of the inclusion `sheafToPresheaf`
-- on injective resolutions of abelian sheaves. Applying the inclusion to an injective resolution
-- leaves the objectwise sections complexes, and taking degree-`p` homology gives the cohomology
-- presheaf `U ↦ H^p(U, F)`.
/-- Lemma 21.10.5: the right derived functor of the inclusion
`Sheaf J AddCommGrpCat ⥤ Cᵒᵖ ⥤ AddCommGrpCat` in degree `p` is canonically isomorphic to the
cohomology presheaf `F ↦ (U ↦ H^p(U, F))`; the left exactness of the inclusion is supplied by the
existing `PreservesFiniteLimits` instance on `sheafToPresheaf`. -/
theorem abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor (p : ℕ) :
    IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
      (Sheaf.cohomologyPresheafFunctor J p) := sorry

-- Proof sketch: evaluate the functor-level isomorphism from
-- `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor` at the abelian sheaf `F`.
/-- Evaluated at an abelian sheaf `F`, the `p`-th right derived functor of the inclusion into
presheaves is the cohomology presheaf of `F`. -/
theorem abelianSheafInclusion_rightDerived_obj_is_cohomologyPresheaf
    (F : Sheaf J AddCommGrpCat) (p : ℕ) :
    IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj F)
      (F.cohomologyPresheaf p) := by
  let h :
      IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
        (Sheaf.cohomologyPresheafFunctor J p) :=
    abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor p
  let ⟨e⟩ := h
  simpa [Sheaf.cohomologyPresheaf] using
    (show IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj F)
        ((Sheaf.cohomologyPresheafFunctor J p).obj F) from
      ⟨e.app F⟩)
