import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Remark 13.18.5: the bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
private abbrev boundedBelowTermsIn (P : CategoryTheory.ObjectProperty 𝒜) :=
  CategoryTheory.ObjectProperty.FullSubcategory fun K : Plus 𝒜 ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace boundedBelowTermsIn

/-- Helper for Remark 13.18.5: a bounded-below complex with terms in `P` coerces to its
underlying cochain complex. -/
private instance instCoeOutCochainComplex (P : CategoryTheory.ObjectProperty 𝒜) :
    CoeOut (boundedBelowTermsIn (𝒜 := 𝒜) P) (CochainComplex 𝒜 ℤ) where
  coe K := K.obj.obj

/-- Helper for Remark 13.18.5: every bounded-below complex with terms in `P` has a lower degree
bound. -/
private theorem exists_isStrictlyGE {P : CategoryTheory.ObjectProperty 𝒜}
    (K : boundedBelowTermsIn (𝒜 := 𝒜) P) :
    ∃ a : ℤ, (K : CochainComplex 𝒜 ℤ).IsStrictlyGE a :=
  (CochainComplex.plus_iff 𝒜 (K : CochainComplex 𝒜 ℤ)).1 K.obj.property

/-- Helper for Remark 13.18.5: each term of a bounded-below complex with terms in `P` again
satisfies `P`. -/
private theorem term_mem {P : CategoryTheory.ObjectProperty 𝒜}
    (K : boundedBelowTermsIn (𝒜 := 𝒜) P) (n : ℤ) :
    P ((K : CochainComplex 𝒜 ℤ).X n) := by
  simpa using K.property n

end boundedBelowTermsIn

/-- Helper for Remark 13.18.5: the bounded-below cochain complexes whose terms are injective
objects. -/
private abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  boundedBelowTermsIn (𝒜 := 𝒜) (isInjective 𝒜)

/-- Helper for Remark 13.18.5: a bounded-below cochain complex of injective objects is
K-injective. -/
private theorem boundedBelow_injective_isKInjective (I : InjectivePlus 𝒜) :
    CochainComplex.IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := boundedBelowTermsIn.exists_isStrictlyGE (𝒜 := 𝒜) I
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) :=
    boundedBelowTermsIn.term_mem (𝒜 := 𝒜) I
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

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
  letI : (I : CochainComplex 𝒜 ℤ).IsKInjective :=
    boundedBelow_injective_isKInjective (𝒜 := 𝒜) I
  -- First pass to the derived category, where a quasi-isomorphism becomes an isomorphism.
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  let eα : Qh.obj (Q.obj K) ≅ Qh.obj (Q.obj L) := asIso (Qh.map (Q.map α))
  -- Precomposition with an isomorphism is bijective on the derived-category Hom-set.
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
  -- Then compare homotopy and derived morphisms using K-injectivity of the target owner.
  let hL := IsKInjective.Qh_map_bijective (Q.obj L) I
  let hK := IsKInjective.Qh_map_bijective (Q.obj K) I
  -- This compatibility identifies precomposition before and after applying `Qh.map`.
  have hcomp :
      ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
        fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) =
      (fun g : Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I) ↦ Qh.map (Q.map α) ≫ g) ∘
        (Qh.map : (Q.obj L ⟶ Q.obj I) → (Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I))) := by
    funext g
    simp
  -- Compose the derived-category bijection with the comparison bijection for `L`.
  have hbijcomp :
      Function.Bijective
        ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
          fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) := by
    rw [hcomp]
    exact hpreD.comp hL
  -- Finally strip off the comparison bijection for `K`.
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

end CochainComplex
