import Mathlib
import stacks_project.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: morphisms in the homotopy category into bounded-below injective cochain
  complexes and their comparison with the derived category;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `CochainComplex.isKInjective_of_injective`;
- best owner abstraction: the bounded-below injective target is canonically owned by
  `CochainComplex.InjectivePlus 𝒜`; K-injectivity and the comparison map to the derived category
  are derived API from that owner, so the remark should take the owner directly rather than
  repeating separate bounded-below and termwise-injective hypotheses;
- primitive data: a quasi-isomorphism `α : K ⟶ L` and a bounded-below injective target
  `I : InjectivePlus 𝒜`;
- derived API: bijectivity of precomposition by `α` on morphisms into `I` in the homotopy
  category.

Source/core/bridge triage:
- `source-facing`: the textbook bijectivity statement below;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: the canonical `IsKInjective` instance on `InjectivePlus 𝒜`.
-/

-- Proof sketch: bounded-below complexes of injectives are K-injective by
-- `CochainComplex.PlusWithTermsIn.instIsKInjective`. The owner theorem
-- `CochainComplex.IsKInjective.Qh_map_bijective` identifies morphisms into `I^•` in the homotopy
-- category with morphisms into `I^•` in the derived category. Since the quasi-isomorphism `α`
-- becomes an isomorphism in the derived category, `Iso.homCongr` gives the resulting
-- precomposition equivalence there, and transport across the two `Qh.map` bijections yields the
-- claimed bijection in `K(\mathcal A)`.
/-- Remark 13.18.5: if `α : K^• ⟶ L^•` is a quasi-isomorphism and `I^•` is a bounded-below
cochain complex of injective objects, then precomposition with `α` induces a bijection
`Hom_{K(\mathcal A)}(L^•, I^•) ≃ Hom_{K(\mathcal A)}(K^•, I^•)`. -/
theorem homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) :
    Function.Bijective
      (fun g : (quotient 𝒜 (up ℤ)).obj L ⟶ (quotient 𝒜 (up ℤ)).obj I ↦
        (quotient 𝒜 (up ℤ)).map α ≫ g) := by
  let Q := quotient 𝒜 (up ℤ)
  letI : (I : CochainComplex 𝒜 ℤ).IsKInjective := inferInstance
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  let eα : Qh.obj (Q.obj K) ≅ Qh.obj (Q.obj L) := asIso (Qh.map (Q.map α))
  have hpreD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I) ↦ Qh.map (Q.map α) ≫ g) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (eα.symm.homCongr (Iso.refl _)).injective (by simpa [eα] using h)
    · intro g
      obtain ⟨g', hg'⟩ := (eα.symm.homCongr (Iso.refl _)).surjective g
      refine ⟨g', ?_⟩
      simpa [eα] using hg'
  let hL := IsKInjective.Qh_map_bijective (Q.obj L) I
  let hK := IsKInjective.Qh_map_bijective (Q.obj K) I
  have hcomp :
      ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
        fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) =
      (fun g : Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I) ↦ Qh.map (Q.map α) ≫ g) ∘
        (Qh.map : (Q.obj L ⟶ Q.obj I) → (Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I))) := by
    funext g
    simp
  have hbijcomp :
      Function.Bijective
        ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
          fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) := by
    rw [hcomp]
    exact hpreD.comp hL
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

end CochainComplex
