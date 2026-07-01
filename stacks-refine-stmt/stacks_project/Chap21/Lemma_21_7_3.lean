import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

/-- Lemma 21.7.3: for a sheaf of modules on a ringed site, every positive-degree cohomology class
becomes zero after restricting to a suitable covering of the base object. -/
-- Proof sketch: view `ℱ` as an abelian sheaf via `SheafOfModules.toSheaf 𝒪`, represent `ξ` by a
-- cocycle in an injective resolution, and use exactness in positive degree together with the local
-- surjectivity characterization of exactness for sheaves to refine to a cover on which the cocycle
-- is locally a coboundary.
theorem exists_cover_restrict_eq_zero_of_positive_cohomology_class
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat] [HasExt (Sheaf J AddCommGrpCat)]
    {𝒪 : Sheaf J RingCat.{max u v}} (ℱ : SheafOfModules 𝒪) {U : C} {n : ℕ}
    (hn : 0 < n) (ξ : ((SheafOfModules.toSheaf 𝒪).obj ℱ).H' n U) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ((((SheafOfModules.toSheaf 𝒪).obj ℱ).cohomologyPresheaf n).map I.f.op) ξ = 0 := sorry
