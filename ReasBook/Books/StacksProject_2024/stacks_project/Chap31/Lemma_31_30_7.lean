import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced the canonical scheme-morphism finite-presentation owner
-- `AlgebraicGeometry.Scheme.Hom.FinitePresentation` and the sheaf-module owner
-- `SheafOfModules.IsFinitePresentation`. Local Chapter 31 inspection found the existing
-- relative `Proj` presentation owner `RelativeProjPresentation` and the finite-type bridge
-- `RelativeProjFiniteTypeAlgebraHypothesis`, but no built-in sheaf-level owner for a finitely
-- presented quasi-coherent graded `\mathcal O_S`-algebra. This item therefore records the finite
-- presentation strengthening on that local relative-`Proj` presentation surface.

/-- The commutative-ring-valued structure sheaf of a scheme, as a sheaf on its open subsets. -/
private abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The finite-presentation analogue of `RelativeProjFiniteTypeAlgebraHypothesis` for a chosen
relative `Proj` presentation `P : RelativeProjPresentation p`.

This records the finite-type consequences from Lemma 31.30.2 together with the remaining
morphism-side finite-presentation components and finite presentation of every twist. -/
@[stacks 0D4D]
class RelativeProjFinitePresentationAlgebraHypothesis
    (P : outParam (RelativeProjPresentation p)) : Prop extends
    RelativeProjFiniteTypeAlgebraHypothesis P where
  /-- The structural morphism of the relative `Proj` presentation is locally of finite
  presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation p
  /-- The structural morphism of the relative `Proj` presentation is quasi-separated. -/
  quasiSeparated : QuasiSeparated p
  /-- Every twist `\mathcal O_X(d)` in the presentation is a finite presentation
  `\mathcal O_X`-module. -/
  twist_isFinitePresentation : ∀ d : ℤ, (P.twist d).IsFinitePresentation

/-- A finite-presentation relative `Proj` algebra hypothesis exposes local finite presentation of
the structural morphism. -/
@[stacks 0D4D]
instance instLocallyOfFinitePresentationOfRelativeProjFinitePresentationAlgebraHypothesis
    (P : outParam (RelativeProjPresentation p))
    [h : RelativeProjFinitePresentationAlgebraHypothesis P] :
    LocallyOfFinitePresentation p :=
  h.locallyOfFinitePresentation

/-- A finite-presentation relative `Proj` algebra hypothesis exposes quasi-separatedness of the
structural morphism. -/
@[stacks 0D4D]
instance instQuasiSeparatedOfRelativeProjFinitePresentationAlgebraHypothesis
    (P : outParam (RelativeProjPresentation p))
    [h : RelativeProjFinitePresentationAlgebraHypothesis P] :
    QuasiSeparated p :=
  h.quasiSeparated

/-- A finite-presentation relative `Proj` algebra hypothesis makes every twist in the chosen
presentation a finite presentation `\mathcal O_X`-module. -/
@[stacks 0D4D]
theorem RelativeProjFinitePresentationAlgebraHypothesis.isFinitePresentation_twist
    {P : RelativeProjPresentation p}
    (h : RelativeProjFinitePresentationAlgebraHypothesis P) (d : ℤ) :
    (P.twist d).IsFinitePresentation := sorry

/-- Lemma 31.30.7 (1): let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If `\mathcal A` is a finitely presented `\mathcal O_S`-algebra, then
`p` is of finite presentation.

The current project represents the source hypothesis through
`RelativeProjFinitePresentationAlgebraHypothesis P` for a chosen relative `Proj` presentation `P`.
-/
@[stacks 0D4D]
theorem relativeProj_finitePresentation_of_finitePresentationAlgebra
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h𝒜qc : ∀ n : ℤ, (𝒜 n).IsQuasicoherent)
    (P : RelativeProjPresentation p)
    (hfp : RelativeProjFinitePresentationAlgebraHypothesis P) :
    FinitePresentation p := sorry

/-- Lemma 31.30.7 (2): under the same hypotheses, for every integer `d`, the twist
`\mathcal O_X(d)` is an `\mathcal O_X`-module of finite presentation.

The twist family is the one attached to the chosen relative `Proj` presentation `P`. -/
@[stacks 0D4D]
theorem relativeProj_twist_isFinitePresentation_of_finitePresentationAlgebra
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h𝒜qc : ∀ n : ℤ, (𝒜 n).IsQuasicoherent)
    (P : RelativeProjPresentation p)
    (hfp : RelativeProjFinitePresentationAlgebraHypothesis P)
    (d : ℤ) :
    (P.twist d).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Hom
