import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` surfaced only low-level mathlib hypercover objects, so
-- this item follows the verified local Chapter 25 owner `HypercoveringOf`; the source's
-- `\check H^p(K, \mathcal I)` is exposed by the canonical alternating-coface sections complex.

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max w v})]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- The Čech sections complex attached to a hypercovering of `𝒢` and an abelian sheaf
`\mathcal I`, i.e. the alternating coface complex of the degreewise groups
`H^0(K_n, \mathcal I)`. -/
abbrev hypercoveringOfSectionsComplex
    (K : HypercoveringOf J 𝒢)
    (ℐ : Sheaf J AddCommGrpCat.{max w v}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).obj
    (K.simplicial.rightOp ⋙ SemiRepresentableFamily.toPresheaf.op ⋙
      h0OverPresheafFunctor ℐ)

/-- The Čech cohomology of a hypercovering with coefficients in `\mathcal I`, defined as the
cohomology of the canonical sections complex. -/
abbrev hypercoveringOfCechCohomology
    (K : HypercoveringOf J 𝒢)
    (ℐ : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (hypercoveringOfSectionsComplex K ℐ).homology p

/- Lemma 25.6.3 (1): the degree-`0` statement is exactly `HypercoveringOf.h0Fork_isLimit`; the
injectivity hypothesis on `\mathcal I` is unused in degree `0`. -/
#check HypercoveringOf.h0Fork_isLimit

/-- Lemma 25.6.3 (2): for a hypercovering `K` of `𝒢` and an injective sheaf of abelian groups
`\mathcal I`, the positive-degree Čech cohomology groups of `K` with coefficients in
`\mathcal I` vanish. -/
theorem hypercoveringOfCechCohomology_succ_isZero_of_injective
    (K : HypercoveringOf J 𝒢)
    (ℐ : Sheaf J AddCommGrpCat.{max w v}) [Injective ℐ]
    (p : ℕ) :
    IsZero (hypercoveringOfCechCohomology K ℐ (p + 1)) := sorry

end CategoryTheory
