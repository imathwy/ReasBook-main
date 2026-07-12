import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import StacksProject_2024.Chap22.ModuleCatHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat A) (up ℤ)

-- Semantic search note: `lean_leansearch` pointed to `DerivedCategory.Qh` and the
-- K-projective/K-injective comparison lemmas. Local Chapter 22 precedent still has only a
-- partial property `(P)` owner and a generic property `(I)` context, so this file states the
-- source Hom-identifications at the canonical `IsKProjective`/`IsKInjective` derived-category
-- layer, with the resolution quasi-isomorphism represented by its invertibility after `Qh`.

/-- The comparison map in Lemma 22.22.3 (1), from morphisms `P ⟶ N` in the homotopy category to
morphisms `M ⟶ N` in the derived category, obtained by localizing and transporting along the
chosen derived isomorphism `Q.map q`. -/
noncomputable def projectiveResolutionHomComparison
    (P M N : DGMod) (q : P ⟶ M)
    [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    ((KQ).obj P ⟶ (KQ).obj N) →
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  fun f ↦
    (asIso (DerivedCategory.Q.map q)).inv ≫
      (DerivedCategory.Qh.map f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N)

/-- Lemma 22.22.3 (1): if `q : P ⟶ M` is a `P`-resolution, represented here by a
K-projective source whose image under the derived-category localization is isomorphic to `M`,
then morphisms `M ⟶ N` in
`D(A, d)` are computed as morphisms `P ⟶ N` in
`K(Mod_(A,d))`. -/
@[stacks 09KY]
theorem derivedHom_bijective_of_kProjectiveResolution
    (P M N : DGMod) (q : P ⟶ M)
    [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    Function.Bijective (projectiveResolutionHomComparison P M N q) := by
  let e :
      DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj M :=
    asIso (DerivedCategory.Q.map q)
  have hpreD :
      Function.Bijective
        (fun g :
          DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N ↦
          e.inv ≫ g) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_epi e.inv).1 h
    · intro g
      refine ⟨e.hom ≫ g, ?_⟩
      simp
  have hq :
      Function.Bijective
        (DerivedCategory.Qh.map :
          ((KQ).obj P ⟶ (KQ).obj N) →
            (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N)) := by
    simpa using IsKProjective.Qh_map_bijective P ((KQ).obj N)
  simpa [Function.comp] using hpreD.comp hq

/-- Companion equivalence for Lemma 22.22.3 (1): the comparison map from morphisms
`P ⟶ N` in the homotopy category to morphisms `M ⟶ N` in the derived category. -/
noncomputable def derivedHomEquivOfKProjectiveResolution
    (P M N : DGMod) (q : P ⟶ M)
    [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    ((KQ).obj P ⟶ (KQ).obj N) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  Equiv.ofBijective
    (projectiveResolutionHomComparison P M N q)
    (derivedHom_bijective_of_kProjectiveResolution P M N q)

/-- The comparison map in Lemma 22.22.3 (2), from morphisms `M ⟶ I` in the homotopy category to
morphisms `M ⟶ N` in the derived category, obtained by localizing and transporting along the
chosen derived isomorphism `Q.map i`. -/
noncomputable def injectiveResolutionHomComparison
    (M N I : DGMod) (i : N ⟶ I)
    [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    ((KQ).obj M ⟶ (KQ).obj I) →
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  fun f ↦
    (DerivedCategory.Qh.map f : DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj I) ≫
      (asIso (DerivedCategory.Q.map i)).inv

/-- Lemma 22.22.3 (2): if `i : N ⟶ I` is an `I`-resolution, represented here by a
K-injective target whose image under the derived-category localization is isomorphic to `N`,
then morphisms `M ⟶ N` in
`D(A, d)` are computed as morphisms `M ⟶ I` in
`K(Mod_(A,d))`. -/
@[stacks 09KY]
theorem derivedHom_bijective_of_kInjectiveResolution
    (M N I : DGMod) (i : N ⟶ I)
    [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    Function.Bijective (injectiveResolutionHomComparison M N I i) := by
  let e :
      DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj I :=
    asIso (DerivedCategory.Q.map i)
  have hpostD :
      Function.Bijective
        (fun g :
          DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj I ↦
          g ≫ e.inv) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono e.inv).1 h
    · intro g
      refine ⟨g ≫ e.hom, ?_⟩
      simp [Category.assoc]
  have hq :
      Function.Bijective
        (DerivedCategory.Qh.map :
          ((KQ).obj M ⟶ (KQ).obj I) →
            (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj I)) := by
    simpa using IsKInjective.Qh_map_bijective ((KQ).obj M) I
  simpa [Function.comp] using hpostD.comp hq

/-- Companion equivalence for Lemma 22.22.3 (2): the comparison map from morphisms
`M ⟶ I` in the homotopy category to morphisms `M ⟶ N` in the derived category. -/
noncomputable def derivedHomEquivOfKInjectiveResolution
    (M N I : DGMod) (i : N ⟶ I)
    [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    ((KQ).obj M ⟶ (KQ).obj I) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  Equiv.ofBijective
    (injectiveResolutionHomComparison M N I i)
    (derivedHom_bijective_of_kInjectiveResolution M N I i)

end CochainComplex
