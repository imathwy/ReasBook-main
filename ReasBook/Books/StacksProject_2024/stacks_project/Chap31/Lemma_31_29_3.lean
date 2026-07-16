import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap31.Lemma_31_29_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the sheaf-of-modules sections API and stalk maps;
-- local Chapter 31 precedent fixes reflexive hulls and rank-one reflexive modules in
-- `Scheme.Modules`.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- The set of points where a section, represented as a morphism from the tensor-unit model of
`\mathcal O_X`, induces an isomorphism on stalks. -/
def rankOneReflexiveSectionIsoLocusSet {ℱ : X.Modules} (s : 𝟙_ X.Modules ⟶ ℱ) : Set X :=
  {x : X | IsIso (RingedSpace.moduleStalkHom x s)}

/-- The recursive sequence
`\mathcal O_X, \mathcal F, \mathcal F^{[2]}, \mathcal F^{[3]}, ...`, where
`\mathcal F^{[n+1]} = (\mathcal F \otimes \mathcal F^{[n]})^{**}` for positive `n`. -/
def rankOneReflexiveSectionPower (ℱ : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | 1 => ℱ
  | n + 2 => reflexiveHull (ℱ ⊗ rankOneReflexiveSectionPower ℱ (n + 1))

/-- The transition maps in the section-power sequence, induced by multiplication by the section
`s`. -/
noncomputable def rankOneReflexiveSectionPowerMap {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    ∀ n : ℕ, rankOneReflexiveSectionPower ℱ n ⟶
      rankOneReflexiveSectionPower ℱ (n + 1)
  | 0 => s
  | n + 1 =>
      (λ_ (rankOneReflexiveSectionPower ℱ (n + 1))).inv ≫
        tensorHom s (𝟙 (rankOneReflexiveSectionPower ℱ (n + 1))) ≫
          toReflexiveHull (ℱ ⊗ rankOneReflexiveSectionPower ℱ (n + 1))

/-- The sequential diagram
`\mathcal O_X \to \mathcal F \to \mathcal F^{[2]} \to ...` attached to a section of a
rank-one reflexive coherent module. -/
noncomputable def rankOneReflexiveSectionPowerDiagram {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) : ℕ ⥤ X.Modules :=
  Functor.ofSequence (rankOneReflexiveSectionPowerMap s)

/-- Lemma 31.29.3 (1): let `X` be an integral locally Noetherian normal scheme, let `\mathcal F`
be a rank-one coherent reflexive `\mathcal O_X`-module, and let
`s : \mathcal O_X \to \mathcal F` be the morphism associated to a global section. The locus where
`s` induces an isomorphism on stalks is open. -/
@[stacks 0EBN]
theorem isOpen_rankOneReflexiveSectionIsoLocusSet
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    IsOpen (rankOneReflexiveSectionIsoLocusSet s) := sorry

/-- Lemma 31.29.3 (2): with notation as in part (1), if `U` is the open subscheme where the
section `s` trivializes `\mathcal F`, then `j_* \mathcal O_U` is the colimit of
`\mathcal O_X \xrightarrow{s} \mathcal F \xrightarrow{s} \mathcal F^{[2]}
\xrightarrow{s} ...`, where
`\mathcal F^{[n+1]} = (\mathcal F \otimes_{\mathcal O_X} \mathcal F^{[n]})^{**}`. -/
@[stacks 0EBN]
theorem pushforward_tensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    Nonempty
      (((Scheme.Modules.pushforward U.ι).obj
          (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules)) ≅
        colimit (rankOneReflexiveSectionPowerDiagram s)) := sorry

end AlgebraicGeometry.Scheme.Modules
