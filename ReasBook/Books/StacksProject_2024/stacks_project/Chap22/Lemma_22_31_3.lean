import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

-- Semantic recall hits: `Functor.rightDerivedNatTrans`, `Functor.rightDerivedNatIso`, and
-- `Functor.rightDerivedNatIso_hom`.
-- The Chapter 22 specialization takes `C` to the homotopy category of DG `B`-modules, `D` to its
-- localization at quasi-isomorphisms, and `H` to the localized DG `A`-module category.

/- Lemma 22.31.3 (1): a homomorphism `f : N ⟶ N'` of differential graded `(A, B)`-bimodules
acts by precomposition on the internal-Hom functors. Once `RHom(N', -)` and `RHom(N, -)` are
presented as right derived functors of the localized underived Hom functors `homN'` and `homN`,
the induced morphism on derived internal-Hom functors is exactly the canonical owner
`Functor.rightDerivedNatTrans`. -/
recall CategoryTheory.Functor.rightDerivedNatTrans

/- Lemma 22.31.3 (2): if `f : N ⟶ N'` is a quasi-isomorphism, then precomposition with `f`
is an isomorphism of derived internal-Hom functors. In this right-derived-functor formulation,
the quasi-isomorphism hypothesis is represented by the localized underived precomposition
isomorphism `precompIso`, and the induced derived isomorphism is the canonical owner
`Functor.rightDerivedNatIso`. -/
recall CategoryTheory.Functor.rightDerivedNatIso

/- The isomorphism version has as its underlying morphism the natural transformation induced by
the hom part of the localized precomposition isomorphism; this is the canonical companion theorem
`Functor.rightDerivedNatIso_hom`. -/
recall CategoryTheory.Functor.rightDerivedNatIso_hom

section

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W]
variable {homN' homN : C ⥤ H}
variable (RHomN' RHomN : D ⥤ H)
variable (unitN' : homN' ⟶ L ⋙ RHomN') (unitN : homN ⟶ L ⋙ RHomN)
variable [RHomN'.IsRightDerivedFunctor unitN' W] [RHomN.IsRightDerivedFunctor unitN W]

/- Source-facing specialization of Lemma 22.31.3 (1). -/
#check
  (Functor.rightDerivedNatTrans RHomN' RHomN unitN' unitN W :
    (homN' ⟶ homN) → (RHomN' ⟶ RHomN))

/- Source-facing specialization of Lemma 22.31.3 (2). -/
#check
  (Functor.rightDerivedNatIso RHomN' RHomN unitN' unitN W :
    (homN' ≅ homN) → (RHomN' ≅ RHomN))

/- Source-facing specialization of the companion theorem identifying the `hom` of the induced
derived isomorphism with the induced derived natural transformation. -/
#check
  (Functor.rightDerivedNatIso_hom RHomN' RHomN unitN' unitN W :
    ∀ precompIso : homN' ≅ homN,
      (RHomN'.rightDerivedNatIso RHomN unitN' unitN W precompIso).hom =
        RHomN'.rightDerivedNatTrans RHomN unitN' unitN W precompIso.hom)

end
