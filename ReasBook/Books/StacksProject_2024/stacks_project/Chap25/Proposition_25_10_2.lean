import StacksProject_2024.Chap25.Lemma_25_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite
open scoped TerminalPresheaf

noncomputable section

universe w v u

namespace CategoryTheory

attribute [local instance] Limits.hasEqualizers_of_hasPullbacks_and_binary_products

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasBinaryProducts C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max w v})]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

-- Semantic search note: `lean_leansearch` recalled mathlib's one-hypercover API; this file uses
-- the local Chapter 25 `HypercoveringOf` owner and its terminal-presheaf specialization from
-- Definition 25.6.1, together with the Chapter 25 comparison package of Lemma 25.6.4.

/-- The equality relation saying that two Čech cohomology classes become equal after pulling back
along two morphisms from a common hypercovering refinement. The induced Čech maps are written by
applying the alternating-coface complex to the underlying simplicial morphisms and then taking
homology. -/
def hypercoveringOfCechCohomologyCommonRefinementEq
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    {K L M : HypercoveringOf J 𝒢}
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (fK : M.simplicial ⟶ K.simplicial)
    (fL : M.simplicial ⟶ L.simplicial)
    (ξK : hypercoveringOfCechCohomology K ℱ i)
    (ξL : hypercoveringOfCechCohomology L ℱ i) : Prop :=
  let cechMapK :
      hypercoveringOfCechCohomology K ℱ i ⟶
        hypercoveringOfCechCohomology M ℱ i :=
    HomologicalComplex.homologyMap
      ((alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).map
        (Functor.whiskerRight
          ((Functor.whiskerRight fK SemiRepresentableFamily.toPresheaf).rightOp)
          (h0OverPresheafFunctor ℱ))) i
  let cechMapL :
      hypercoveringOfCechCohomology L ℱ i ⟶
        hypercoveringOfCechCohomology M ℱ i :=
    HomologicalComplex.homologyMap
      ((alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).map
        (Functor.whiskerRight
          ((Functor.whiskerRight fL SemiRepresentableFamily.toPresheaf).rightOp)
          (h0OverPresheafFunctor ℱ))) i
  cechMapK ξK = cechMapL ξL

/-- Proposition 25.10.2 (1): every global cohomology class of an abelian sheaf on a site with
fibre products and products of pairs is represented on the Čech cohomology of some
hypercovering. The global cohomology group is formalized as the cohomology of the terminal
presheaf. -/
@[stacks 09VZ]
theorem siteSheafCohomology_exists_hypercovering_preimage
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (ξ :
      (hypercoveringOfSheafCohomology
        (*ₚ[C] : Cᵒᵖ ⥤ Type (max w v)) i).obj ℱ) :
    ∃ (K : HypercoveringOf J (*ₚ[C] : Cᵒᵖ ⥤ Type (max w v)))
      (comparison : HypercoveringOfCechComparison K i)
      (ξK : hypercoveringOfCechCohomology K ℱ i),
      (comparison.app ℱ) ξK = ξ := sorry

/-- Proposition 25.10.2 (2): if two Čech cohomology classes on hypercoverings have the same image
in global cohomology, then after passing to a common hypercovering refinement they become equal. -/
@[stacks 09VZ]
theorem siteSheafCohomology_hypercovering_representatives_common_refinement
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (K L : HypercoveringOf J (*ₚ[C] : Cᵒᵖ ⥤ Type (max w v)))
    (comparisonK : HypercoveringOfCechComparison K i)
    (comparisonL : HypercoveringOfCechComparison L i)
    (ξK : hypercoveringOfCechCohomology K ℱ i)
    (ξL : hypercoveringOfCechCohomology L ℱ i)
    (hξ : (comparisonK.app ℱ) ξK = (comparisonL.app ℱ) ξL) :
    ∃ (M : HypercoveringOf J (*ₚ[C] : Cᵒᵖ ⥤ Type (max w v)))
      (fK : M.simplicial ⟶ K.simplicial)
      (fL : M.simplicial ⟶ L.simplicial),
      hypercoveringOfCechCohomologyCommonRefinementEq ℱ i fK fL ξK ξL := sorry

end CategoryTheory
