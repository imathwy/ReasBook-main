import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `SheafOfModules.IsQuasicoherent` and
-- `Sheaf.cohomologyPresheafFunctor`; local Chapter 12 provides
-- `CohomologicalDeltaFunctor.IsUniversal`. The source-facing surface therefore uses the full
-- subcategory of quasi-coherent modules, the actual sheaf cohomology functor evaluated on the top
-- open, and the Chapter 12 universal cohomological `δ`-functor owner.

/-- The category of quasi-coherent `\mathcal O_X`-modules. -/
@[stacks 0BDY]
abbrev QCoh (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

/-- The degree-`n` global sheaf cohomology functor on quasi-coherent `\mathcal O_X`-modules. -/
@[stacks 0BDY]
noncomputable abbrev qcohGlobalCohomologyFunctor (X : Scheme.{u}) (n : ℕ) :
    QCoh X ⥤ AddCommGrpCat :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
      Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) n ⋙
        (CategoryTheory.evaluation ((Opens X)ᵒᵖ) AddCommGrpCat).obj (op (⊤ : Opens X))

variable {X : Scheme.{u}}

/-- A target module admits a monomorphism from `ℱ` and has vanishing higher global cohomology. -/
structure HigherGlobalCohomologyKillingTarget (ℱ ℱ' : X.Modules) : Prop where
  /-- The chosen target receives a monomorphism from the source module. -/
  mono : ∃ i : ℱ ⟶ ℱ', Mono i
  /-- All positive-degree global cohomology groups of the target vanish. -/
  globalCohomology_isZero :
    ∀ p : ℕ, 1 ≤ p →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ').H' p (⊤ : Opens X))

/-- Lemma 30.4.3 (1): let `X` be a quasi-compact scheme with affine diagonal. Every
quasi-coherent `\mathcal O_X`-module embeds into a quasi-coherent module whose higher global
cohomology vanishes. -/
@[stacks 0BDY]
theorem exists_quasicoherent_embedding_globalCohomology_isZero
    [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ ℱ' : X.Modules,
      ℱ'.IsQuasicoherent ∧ HigherGlobalCohomologyKillingTarget ℱ ℱ' := sorry

/-- Lemma 30.4.3 (2): for a quasi-compact scheme with affine diagonal, the global cohomology
functors `H^n(X, -)` on quasi-coherent `\mathcal O_X`-modules carry a universal cohomological
`δ`-functor structure. -/
@[stacks 0BDY]
theorem exists_universal_qcoh_globalCohomology_deltaFunctor
    (X : Scheme.{u}) [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    ∃ T : CohomologicalDeltaFunctor (QCoh X) AddCommGrpCat,
      (∀ n : ℕ, (T n).obj = qcohGlobalCohomologyFunctor X n) ∧ T.IsUniversal := sorry

end AlgebraicGeometry.Scheme
