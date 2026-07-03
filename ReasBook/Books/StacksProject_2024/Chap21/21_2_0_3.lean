import Mathlib

open CategoryTheory

universe v u

/- 21.2.0.3: for a sheaf `F` of abelian groups on a site `(C, J)`, a chosen injective
resolution `I`, and `i : ℕ`, the explicit source-facing model for `H^i(C, F)` is the `i`-th
homology of the global-sections complex `Γ(C, I^•)`. The owner abstraction for cohomology itself
is the canonical sheaf-cohomology object `F.H i`; this file therefore records only the bridge
expression, instead of introducing a duplicate local alias for it. -/
#check ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C),
  [HasSheafify J AddCommGrpCat.{v}] → [HasGlobalSectionsFunctor J AddCommGrpCat.{v}] →
  (F : Sheaf J AddCommGrpCat.{v}) → (I : InjectiveResolution F) → (i : ℕ) →
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) i).obj
      (((Sheaf.Γ J AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
