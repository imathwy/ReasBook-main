import Mathlib
import StacksProject_2024.Chap13.Lemma_13_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {S : MorphismProperty D} {S' : MorphismProperty D'}
  {F : D ⥤ D'} {G : D' ⥤ D}

/- Domain-style sampling:
- primary domain: pointwise left/right derived values along localization functors, together with
  the Hom-set comparison induced by an underived adjunction;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.leftDerivedValue`,
  `Adjunction.homEquiv`;
- owner abstraction:
  `source-facing`: the Stacks lemma compares the localized Hom-sets attached to the chosen
    pointwise derived values at `K` and `M`;
  `core/canonical`: the project owners `rightDerivedValue` / `leftDerivedValue` built on the
    mathlib pointwise derived-functor API, together with the underived adjunction owner
    `Adjunction.homEquiv`;
  `bridge/view`: the owner introduced in this file,
    `Adjunction.pointwiseDerivedHomEquiv`, built directly from those canonical ingredients.

Primitive data are exactly the adjunction `adj : G ⊣ F` and the pointwise derivability hypotheses
at the two chosen objects. The Hom-set equivalence is derived API, so this file should expose that
equivalence directly rather than through a second public wrapper family. We keep this source-facing
bridge instead of collapsing it to `Adjunction.derived`, because that functor-level owner requires
stronger absolute-derived hypotheses and would change the local source semantics.
-/

-- Proof sketch: express `Hom_{(S')⁻¹D'}(M, RF(K))` and `Hom_{S⁻¹D}(LG(M), K)` using the
-- pointwise right/left derived-value constructions together with the localization Hom-colimit
-- formulas from Chapter 4. Then commute the two colimits, apply the underived adjunction
-- `adj.homEquiv` termwise, and transport the result back to the localized Hom-sets.
namespace Adjunction

/-- Internal notation for the source Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomSource
    (F : D ⥤ D') (S : MorphismProperty D) (S' : MorphismProperty D')
    (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K] :=
  (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K

/-- Internal notation for the target Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomTarget
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (M : D') (K : D)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :=
  leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K

private def IsCanonicalPointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K) : Prop :=
  ∀ {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M']
    (φ : M' ⟶ F.obj K'),
      e (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
        leftDerivedValueMap S' (G ⋙ S.Q) m ≫
          leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv

-- Proof sketch: construct the comparison family by transporting the Chapter 4 left/right
-- localization Hom descriptions through the underived adjunction `adj.homEquiv`, then descend
-- through the pointwise right/left derived-value presentations. The same denominator formulas
-- give both naturality laws and the normalization on basic fraction generators, and these three
-- clauses characterize the family uniquely.
private theorem existsUnique_pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ∃! e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K,
      IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e := by
  sorry

/-- Lemma 13.30.1: if `F` is right adjoint to `G`, if the pointwise right derived value of
`F ⋙ S'.Q` is defined at `K`, and if the pointwise left derived value of `G ⋙ S.Q` is defined at
`M`, then the localized Hom-sets
`Hom_{(S')⁻¹\mathcal D'}(M, RF(K))` and `Hom_{S⁻¹\mathcal D}(LG(M), K)` are canonically
equivalent. -/
noncomputable def pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
      (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K) :=
  Classical.choose (existsUnique_pointwiseDerivedHomEquiv adj S S' K M)

private theorem pointwiseDerivedHomEquiv_spec
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    IsCanonicalPointwiseDerivedHomEquiv adj S S' K M
      (pointwiseDerivedHomEquiv adj S S' K M) := by
  rcases Classical.choose_spec (existsUnique_pointwiseDerivedHomEquiv adj S S' K M) with ⟨he, -⟩
  exact he

theorem pointwiseDerivedHomEquiv_naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K : D} {M₁ M₂ : D'} (m : M₁ ⟶ M₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₁]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₂]
    (f : (S'.Q.obj M₂) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) :
    adj.pointwiseDerivedHomEquiv S S' K M₁ ((S'.Q.map m) ≫ f) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫ adj.pointwiseDerivedHomEquiv S S' K M₂ f :=
by
  sorry

theorem pointwiseDerivedHomEquiv_naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K₁ K₂ : D} {M : D'} (k : K₁ ⟶ K₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₁]
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₂]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (f : (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K₁) :
    adj.pointwiseDerivedHomEquiv S S' K₂ M (f ≫ rightDerivedValueMap S (F ⋙ S'.Q) k) =
      adj.pointwiseDerivedHomEquiv S S' K₁ M f ≫ S.Q.map k :=
by
  sorry

end Adjunction

end

end CategoryTheory
