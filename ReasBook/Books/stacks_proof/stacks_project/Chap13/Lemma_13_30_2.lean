import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Adjunction

section

variable {C : Type u₁} {D : Type u₂} {ι : Type w}
  [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
variable [G.Additive]

/-- A homotopy between maps into `K` transports across the Hom-equivalence induced by
`adj.mapHomologicalComplex c`. -/
noncomputable def homotopy_mapHomologicalComplex_homEquiv
    (adj : G ⊣ F) (c : ComplexShape ι)
    {L : HomologicalComplex D c} {K : HomologicalComplex C c}
    {f g : (G.mapHomologicalComplex c).obj L ⟶ K} (h : Homotopy f g) :
    Homotopy
      (((adj.mapHomologicalComplex c).homEquiv L K) f)
      (((adj.mapHomologicalComplex c).homEquiv L K) g) := by
  letI : F.Additive := adj.right_adjoint_additive
  simpa [Adjunction.homEquiv_unit] using
    (F.mapHomotopy h).compLeft ((adj.mapHomologicalComplex c).unit.app L)

end

end Adjunction

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [HasZeroMorphisms 𝒜] [HasZeroMorphisms ℬ]
  [CategoryWithHomology 𝒜] [CategoryWithHomology ℬ]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

local notation "QisA" => HomologicalComplex.quasiIso 𝒜 (up ℤ)
local notation "QisB" => HomologicalComplex.quasiIso ℬ (up ℤ)

/- Domain-style sampling:
- primary domain: pointwise left/right derived values on cochain complexes, compared through an
  underived adjunction between the base categories, at the quasi-isomorphism and homology layer;
- sampled owner declarations:
  `Adjunction.pointwiseDerivedHomEquiv`,
  `Adjunction.pointwiseDerivedHomEquiv_naturality_left`,
  `Adjunction.pointwiseDerivedHomEquiv_naturality_right`,
  `HomologicalComplex.quasiIso`,
  `MorphismProperty.Q`;
- owner abstraction:
  `source-facing`: the Stacks lemma comparing
    `Hom_{D(ℬ)}(M, RF(K))` and `Hom_{D(𝒜)}(LG(M), K)` for cochain complexes;
  `core/canonical`: `Adjunction.pointwiseDerivedHomEquiv` applied to the lifted adjunction on
    cochain complexes and the canonical localization functors `QisA.Q` and `QisB.Q`;
  `bridge/view`: `Adjunction.mapHomologicalComplex`, which lifts `G ⊣ F` to complexes.

Primitive data are the adjunction `adj : G ⊣ F` and the pointwise derivability hypotheses at
`K` and `M`. The Hom-equivalence and its two naturality identities are derived API, so this file
should expose them by reusing the owners above instead of rebuilding parallel local machinery.
-/

-- Proof sketch: specialize the general pointwise derived-adjunction construction to the
-- quasi-isomorphism localizations of cochain complexes in the two ambient categories. The
-- underived adjunction `G ⊣ F` is applied termwise on complexes, and Lemma `13.30.2` is exactly
-- the resulting specialization of the canonical owner from Lemma `13.30.1`.
section

variable (adj : G ⊣ F)

section

/- Lemma 13.30.2: for an adjoint pair `G ⊣ F` of additive functors between abelian categories,
if the pointwise right derived functor of `F` is defined at the complex `K` and the pointwise
left derived functor of `G` is defined at the complex `M`, then there is a canonical
isomorphism
`Hom_{D(\mathcal B)}(M^\bullet, RF(K^\bullet)) ≃ Hom_{D(\mathcal A)}(LG(M^\bullet), K^\bullet)`.
This recall is stated over the weaker canonical quasi-isomorphism layer:
`HasZeroMorphisms`, `CategoryWithHomology`, and the pointwise-derived hypotheses suffice for the
specialization of `Adjunction.pointwiseDerivedHomEquiv` along
`adj.mapHomologicalComplex (up ℤ)`. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv QisA QisB

end

section

/- The Hom-equivalence of Lemma 13.30.2 is natural in the complex of `ℬ`; this is the direct
specialization of `Adjunction.pointwiseDerivedHomEquiv_naturality_left` to cochain complexes and
quasi-isomorphisms. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv_naturality_left QisA QisB

end

section

/- The Hom-equivalence of Lemma 13.30.2 is natural in the complex of `𝒜`; this is the direct
specialization of `Adjunction.pointwiseDerivedHomEquiv_naturality_right` to cochain complexes and
quasi-isomorphisms. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv_naturality_right QisA QisB

end

end

end

end CategoryTheory
