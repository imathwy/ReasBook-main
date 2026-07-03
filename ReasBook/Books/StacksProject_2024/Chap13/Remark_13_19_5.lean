import Mathlib
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_19_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: morphisms from bounded-above projective cochain complexes in the homotopy and
  derived categories of an abelian category;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective`,
  `homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `DerivedCategory.isIso_Q_map_iff_quasiIso`,
  `NatIso.isIso_map_iff`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source, and its `IsKProjective` instance is derived API feeding the chapter owner
  theorem `homotopyCategory_to_derived_bijective_of_boundedAbove_projective`;
- primitive data: a quasi-isomorphism `α : K ⟶ L` and a source complex `P : ProjectiveMinus 𝒜`;
- derived API: bijectivity of postcomposition by `α` in the homotopy category.

This remark is therefore a `bridge/view`: it should take the source-facing owner
`ProjectiveMinus 𝒜` directly and transport postcomposition bijectivity from the derived category
through the chapter comparison theorem for that owner, rather than rebuilding boundedness and
termwise-projective data locally.
-/

-- Proof sketch: `13.19.8` already identifies morphisms out of `P` in the homotopy category with
-- morphisms out of `P` in the derived category. The quasi-isomorphism `α` becomes an isomorphism
-- in the derived category, where postcomposition is therefore bijective. Transporting that
-- bijection back across the two comparison maps gives the homotopy-category bijection.
/-- Remark 13.19.5: if `α : K^• ⟶ L^•` is a quasi-isomorphism and `P^•` is a bounded-above
cochain complex of projective objects, then postcomposition with `α` induces a bijection
`Hom_{K(\mathcal A)}(P^•, K^•) ≃ Hom_{K(\mathcal A)}(P^•, L^•)`. -/
theorem homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Bijective
      (fun g : (quotient 𝒜 (up ℤ)).obj P ⟶ (quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (quotient 𝒜 (up ℤ)).map α) := by
  let Q := quotient 𝒜 (up ℤ)
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  have hpostD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono (Qh.map (Q.map α))).1 h
    · intro g
      refine ⟨g ≫ inv (Qh.map (Q.map α)), ?_⟩
      simp [Category.assoc]
  have hK := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P K
  have hL := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L
  have hcomp :
      ((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
        fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α) =
      (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) ∘
        (Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) := by
    funext g
    simp [Functor.map_comp]
  have hbijcomp :
      Function.Bijective
        (((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
          fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α)) := by
    rw [hcomp]
    exact hpostD.comp hK
  exact (Function.Bijective.of_comp_iff' hL _).mp hbijcomp

end CochainComplex
