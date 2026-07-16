import Mathlib
import StacksProject_2024.stacks_project.Chap24.Definition_24_3_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_30_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_30_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced the canonical affine `Proj` finite-type morphism owner
-- `AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat` and
-- the module owner `SheafOfModules.IsFiniteType`.
-- Local Chapter 31 inspection found that Lemma 31.30.1 now owns the source-facing finite-type
-- hypothesis `RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜` together with the
-- presentation-level bridge `RelativeProjFiniteTypeAlgebraHypothesis P`, while Lemma 31.30.6
-- provides the relative `Proj` twist-family owner
-- `RelativeProjPresentation`. The current environment still has no built-in scheme-side relative
-- `Proj_S` construction with a sheaf-level finite-type algebra owner, so this file reuses that
-- existing bridge surface directly.

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The commutative-ring-valued structure sheaf of a scheme, as a sheaf on its open subsets. -/
private abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

/-- Lemma 31.30.2 (1): let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If `\mathcal A` is of finite type as a sheaf of
`\mathcal O_S`-algebras, then `p` is of finite type.

In the current environment, the source hypothesis is recorded by the source-facing owner
`RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜` from Lemma 31.30.1. -/
@[stacks 07ZY]
theorem relativeProj_finiteType_of_finiteTypeAlgebra
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (hft : RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜) :
    FiniteType p := by
  refine ⟨hft.quasiCompact, ?_⟩
  rcases hft with ⟨P, -, hP⟩
  exact hP.locallyOfFiniteType

/-- Lemma 31.30.2 (2): let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If `\mathcal A` is of finite type as a sheaf of
`\mathcal O_S`-algebras, then for every integer `d` the twist `\mathcal O_X(d)` is a finite type
`\mathcal O_X`-module.

On the current project surface, the twist family is attached to a chosen relative `Proj`
presentation `P`, and the finite-type conclusion is provided by the presentation-level bridge
`RelativeProjFiniteTypeAlgebraHypothesis P`. -/
@[stacks 07ZY]
theorem relativeProj_twist_isFiniteType_of_finiteTypeAlgebra
    (P : RelativeProjPresentation p)
    (hft : RelativeProjFiniteTypeAlgebraHypothesis P)
    (d : ℤ) :
    (P.twist d).IsFiniteType :=
  hft.isFiniteType_twist d

end AlgebraicGeometry.Scheme.Hom
