import Mathlib
import StacksProject_2024.Chap30.Lemma_30_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Opposite

noncomputable section

universe u v

/- Domain-style sampling for Equation 30.23.3.1:
- semantic recall hits: `AlgebraicGeometry.Scheme.IdealSheafData`,
  `AlgebraicGeometry.Scheme.CoherentFormalModules`, and the local coherent owner
  `RingedSpace.Coh`;
- source/core/bridge triage:
  * source-facing: the completion functor `\textit{Coh}(\mathcal O_X) → \textit{Coh}(X, I)`,
    `\mathcal F ↦ \mathcal F^\wedge`;
  * core/canonical: the categories `RingedSpace.Coh X.toRingedSpace` and
    `Scheme.CoherentFormalModules X I`;
  * bridge/view: the affine-open section modules of the `n`th completion stage, identified with
    the quotient of `\mathcal F(U)` by `I(U)^n \mathcal F(U)`.
- best owner abstraction: a chosen functor together with the source-facing affine quotient
  specification, rather than a bare alias for the ambient functor type.
-/

/-- The affine-open section module `\mathcal F(U) / I(U)^n \mathcal F(U)` attached to a coherent
`\mathcal O_X`-module `\mathcal F`. -/
abbrev coherentCompletionSourceStageSections
    {X : Scheme.{u}} (I : X.IdealSheafData) (ℱ : RingedSpace.Coh X.toRingedSpace)
    (U : X.affineOpens) (n : ℕ) :=
  ↑((ℱ.obj).val.obj (op U.1)) ⧸
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) ↑((ℱ.obj).val.obj (op U.1)))

/-- The affine-open section module of stage `n` of a coherent formal module. -/
abbrev coherentCompletionTargetStageSections
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : Scheme.CoherentFormalModules X I)
    (U : X.affineOpens) (n : ℕ) :=
  ↑((((M.obj).obj (op n)).obj).val.obj (op U.1))

/-- A chosen completion functor
`\textit{Coh}(\mathcal{O}_X) \to \textit{Coh}(X, \mathcal{I})`,
`\mathcal F \mapsto \mathcal F^\wedge`, recorded as a functor together with the source-facing
affine-open quotient description of its stages. The transition maps remain part of the canonical
owner `Scheme.CoherentFormalModules X I`. -/
structure CoherentCompletionFunctor (X : Scheme.{u}) (I : X.IdealSheafData)
    extends RingedSpace.Coh X.toRingedSpace ⥤ Scheme.CoherentFormalModules X I where
  /-- On affine-open sections, the `n`th stage of the completion of `\mathcal F` is the quotient
  `\mathcal F(U) / I(U)^n \mathcal F(U)`. -/
  stageSectionsLinearEquiv :
    ∀ (ℱ : RingedSpace.Coh X.toRingedSpace) (U : X.affineOpens) (n : ℕ),
      coherentCompletionSourceStageSections I ℱ U n ≃ₗ[Γ(X, U.1)]
        coherentCompletionTargetStageSections I (toFunctor.obj ℱ) U n

/-- The affine-open stage comparison carried by a chosen completion functor. -/
abbrev coherentCompletionFunctor_stageSectionsLinearEquiv
    {X : Scheme.{u}} {I : X.IdealSheafData} (ctx : CoherentCompletionFunctor X I)
    (ℱ : RingedSpace.Coh X.toRingedSpace) (U : X.affineOpens) (n : ℕ) :
    coherentCompletionSourceStageSections I ℱ U n ≃ₗ[Γ(X, U.1)]
      coherentCompletionTargetStageSections I (ctx.obj ℱ) U n :=
  ctx.stageSectionsLinearEquiv ℱ U n

/- 30.23.3.1: the completion functor
`\textit{Coh}(\mathcal{O}_ X) \longrightarrow \textit{Coh}(X, \mathcal{I})`,
`\mathcal{F} \longmapsto \mathcal{F}^\wedge`, formalized as a chosen functor into the canonical
target category `Scheme.CoherentFormalModules X I` with the expected affine-open quotient stages.
-/
#check CoherentCompletionFunctor
