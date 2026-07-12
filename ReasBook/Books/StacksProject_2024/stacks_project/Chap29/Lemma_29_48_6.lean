import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksProject_2024.Chap29.Lemma_29_48_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- A morphism `g : Z ⟶ X` is covered by finitely many closed subschemes mapping isomorphically to
`X` if there are finitely many closed subschemes of `Z` whose composites with `g` are
isomorphisms and whose supports cover all points of `Z`. -/
def IsCoveredByFinitelyManyClosedSubschemesWithIsoToBase
    {X Z : Scheme.{u}} (g : Z ⟶ X) : Prop :=
  ∃ (m : ℕ) (piece : Fin m → Z.IdealSheafData),
    (∀ j, IsIso ((piece j).subschemeι ≫ g)) ∧
    ∀ z : Z, ∃ j : Fin m, z ∈ ((piece j).support : Set Z)

/-- A morphism `f : Y ⟶ X` embeds into a finite locally free `X`-scheme which is covered by
finitely many closed subschemes mapping isomorphically to `X` if there is a closed immersion
`i : Y ⟶ Z` over `X` into such a scheme `Z`. -/
def HasClosedImmersionIntoFiniteLocallyFreeCoveredByClosedSubschemesWithIsoToBase
    {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ (Z : Scheme.{u}) (i : Y ⟶ Z) (g : Z ⟶ X),
    IsClosedImmersion i ∧
    i ≫ g = f ∧
    IsFiniteLocallyFree g ∧
    g.IsCoveredByFinitelyManyClosedSubschemesWithIsoToBase

end Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme-level `IsFinite` owner, and direct local search confirmed
  that Chapter 29 records finite locally free morphisms through the source-facing owner
  `IsFiniteLocallyFree`, with `LocallyOfType ringHomFiniteFree` available only as the affine-local
  bridge;
- the surjective finite locally free clauses below therefore use `IsFiniteLocallyFree` directly;
- `Lemma_29_2_4.lean` and `Lemma_29_44_6.lean` fix the current pullback/base-change notation
  `pullback f π`, `pullback.fst f π`, and `pullback.snd f π`.
- the source lemma is existential, and the reusable inner witness package is recorded as the
  source-facing morphism property
  `Scheme.Hom.HasClosedImmersionIntoFiniteLocallyFreeCoveredByClosedSubschemesWithIsoToBase`.
-/

/-- Lemma 29.48.6: if `f : Y ⟶ X` is finite and `X` is affine, then after a surjective finite
locally free cover `X' ⟶ X`, the base change `pullback f π` admits a closed immersion into a
finite locally free `X'`-scheme `Z'` which is set-theoretically covered by finitely many closed
subschemes mapping isomorphically to `X'`. -/
@[stacks 04MI]
theorem exists_finiteLocallyFree_cover_embedding_into_split_finiteLocallyFree
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] (hf : IsFinite f) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      Surjective π ∧
      IsFiniteLocallyFree π ∧
      (pullback.snd f π).HasClosedImmersionIntoFiniteLocallyFreeCoveredByClosedSubschemesWithIsoToBase :=
  sorry

end AlgebraicGeometry
