import Mathlib
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [IsGrothendieckAbelian.{v} (RingedSpace.Modules X)]

/- Domain-style sampling for Lemma 20.38.2:
- primary domain: inverse systems of cochain complexes of `\mathcal O_X`-modules on a ringed
  space, evaluated on opens by the sections functor and then passed to cohomology;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`,
  `(RingedSpace.ringCatSheaf X)`,
  `(RingedSpace.Modules X)`,
  `SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)`;
- best owner abstraction: the tower owner is `SequentialInverseSystem`, while the ambient module
  category is the ringed-space owner `(RingedSpace.Modules X)` over `(RingedSpace.ringCatSheaf X)`; sections over an open
  are taken by the canonical evaluation functor on `(RingedSpace.ringCatSheaf X)`, followed by forgetting the
  module structure to abelian groups;
- primitive data: the ringed space `X`, the inverse system
  `ℱ : ℕᵒᵖ ⥤ CochainComplex (RingedSpace.Modules X) ℤ`, and an open subset `U`;
- derived API: the degreewise section towers, the cohomology-sheaf tower, and the canonical limit
  comparison morphism on cohomology sheaves.

Source/core/bridge triage:
- `source-facing`: the basiswise hypotheses and the final isomorphism statement for cohomology
  sheaves of inverse limits;
- `core/canonical`: `SequentialInverseSystem`, `transitionMap`, `IsMittagLeffler`,
  `(RingedSpace.ringCatSheaf X)`, `(RingedSpace.Modules X)`, and evaluation on opens;
- `bridge/view`: the cochain-level towers obtained by applying sections and then homology on
  opens.

This file should therefore reuse the chapter owners `SequentialInverseSystem`, `(RingedSpace.ringCatSheaf X)`,
and `(RingedSpace.Modules X)`, rather than keep parallel local copies of the same ambient data. -/

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

/-- The sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian groups. -/
private abbrev sectionsAsAbelianFunctor (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U) ⋙
    forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}

/-- The module-valued sections functor over `U` is additive. -/
private instance sectionsEvaluation_additive (U : Opens X.carrier) :
    (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).Additive where
  map_add := by
    intro M N f g
    change
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
          ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map (f + g)) =
        (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map f) +
          (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map g)
    rw [(SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map_add,
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map_add]

/-- The abelian-valued sections functor over `U` is additive. -/
private instance sectionsAsAbelianFunctor_additive (U : Opens X.carrier) :
    (sectionsAsAbelianFunctor X U).Additive where
  map_add := by
    intro M N f g
    change
      (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).map
          ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map (f + g)) =
        (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).map
            ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map f) +
          (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).map
            ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map g)
    rw [show
      (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map (f + g) =
        (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map f +
          (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map g by
        simpa using
          (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map_add]
    simpa using
      (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).map_add

/-- Applying sections over `U` termwise to a cochain complex of `\mathcal O_X`-modules. -/
private abbrev sectionsComplexFunctor (U : Opens X.carrier) :
    CpxX ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (sectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- For a tower of complexes and a fixed open `U`, this is the inverse system
`n ↦ \mathcal F_n^i(U)` of degree-`i` abelian groups. -/
abbrev complexSectionDegreeInverseSystem
    (ℱ : ℕᵒᵖ ⥤ CpxX) (U : Opens X.carrier) (i : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  ℱ ⋙ sectionsComplexFunctor X U ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) i

/-- For a tower of complexes and a fixed open `U`, this is the inverse system
`n ↦ H^i(\mathcal F_n^\bullet(U))` of cohomology groups. -/
abbrev complexSectionCohomologyInverseSystem
    (ℱ : ℕᵒᵖ ⥤ CpxX) (U : Opens X.carrier) (i : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  ℱ ⋙ sectionsComplexFunctor X U ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) i

/-- The underlying abelian sheaf of the degree-`m` cohomology sheaf of a cochain complex of
`\mathcal O_X`-modules. -/
abbrev complexCohomologySheaf (K : CpxX) (m : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj
    ((HomologicalComplex.homologyFunctor (RingedSpace.Modules X) (ComplexShape.up ℤ) m).obj K)

/-- The inverse system `n ↦ H^m(\mathcal F_n^\bullet)` of cohomology sheaves attached to a tower
of cochain complexes of `\mathcal O_X`-modules. -/
abbrev complexCohomologySheafTower
    (ℱ : ℕᵒᵖ ⥤ CpxX) (m : ℤ) :
    ℕᵒᵖ ⥤ Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  ℱ ⋙
    HomologicalComplex.homologyFunctor (RingedSpace.Modules X) (ComplexShape.up ℤ) m ⋙
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The canonical comparison morphism
`H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet)` for a
termwise inverse limit of cochain complexes of `\mathcal O_X`-modules. -/
abbrev complexCohomologySheafLimitComparison
    (ℱ : ℕᵒᵖ ⥤ CpxX) (m : ℤ)
    [HasLimit ℱ] [HasLimit (complexCohomologySheafTower X ℱ m)] :
    complexCohomologySheaf X (limit ℱ) m ⟶
      limit (complexCohomologySheafTower X ℱ m) :=
  limit.post ℱ
    (HomologicalComplex.homologyFunctor (RingedSpace.Modules X) (ComplexShape.up ℤ) m ⋙
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))

-- Proof sketch: on each `U ∈ 𝓑`, shift the section complexes so that Lemma `15.87.3` applies in
-- degree `0`, giving `H^m((\varprojlim_n \mathcal F_n^\bullet)(U)) ≅ \varprojlim_n
-- H^m(\mathcal F_n^\bullet(U))`. The eventual constancy assumption identifies this limit with
-- `H^m(\mathcal F_{n₀}^\bullet(U))`. Since every open admits a covering by members of `𝓑`, the
-- objectwise identifications on `𝓑` glue to isomorphisms of the associated cohomology sheaves.
/-- Lemma 20.38.2: let `(X, \mathcal O_X)` be a ringed space and let `(\mathcal F_n^\bullet)_n`
be an inverse system of complexes of `\mathcal O_X`-modules. Assume there is a family `𝓑` of
open subsets covering every open subset of `X` such that for each `U ∈ 𝓑` the inverse systems
`n ↦ \mathcal F_n^{m-2}(U)`, `n ↦ \mathcal F_n^{m-1}(U)`, and
`n ↦ H^{m-1}(\mathcal F_n^\bullet(U))` have vanishing `R^1 \!\varprojlim`, and such that
`n ↦ H^m(\mathcal F_n^\bullet(U))` is constant for `n ≥ n₀`. Then, for the termwise inverse
limit complex `\mathcal F^\bullet = \varprojlim_n \mathcal F_n^\bullet`, the canonical maps
`H^m(\mathcal F^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet) ⟶
H^m(\mathcal F_{n₀}^\bullet)` are isomorphisms of abelian sheaves on `X`. -/
theorem cohomologySheaf_limitComparison_and_eventualProjection_isIso_of_basis_hypotheses
    (ℱ : ℕᵒᵖ ⥤ CpxX) (m : ℤ) (𝓑 : Set (Opens X.carrier)) (n₀ : ℕ)
    (hcover :
      ∀ W : Opens X.carrier, ∃ ι : Type u, ∃ V : ι → Opens X.carrier,
        (∀ i, V i ∈ 𝓑) ∧ iSup V = W)
    (hdegree_m_sub_two :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        IsMittagLeffler (complexSectionDegreeInverseSystem X ℱ U (m - 2)))
    (hdegree_m_sub_one :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        IsMittagLeffler (complexSectionDegreeInverseSystem X ℱ U (m - 1)))
    (hcohomology_m_sub_one :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        IsMittagLeffler (complexSectionCohomologyInverseSystem X ℱ U (m - 1)))
    (heventually_constant :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 → ∀ n : ℕ, ∀ hn : n₀ ≤ n,
        IsIso ((complexSectionCohomologyInverseSystem X ℱ U m).transitionMap hn)) :
    IsIso (complexCohomologySheafLimitComparison X ℱ m) ∧
      IsIso (limit.π (complexCohomologySheafTower X ℱ m) (op n₀)) := sorry

end

end AlgebraicGeometry.RingedSpace
