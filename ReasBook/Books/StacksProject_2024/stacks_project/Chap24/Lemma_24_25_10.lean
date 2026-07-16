import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.stacks_project.Chap24.Definition_24_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace DifferentialGradedModule

/- Semantic search note: `lean_leansearch` was unavailable in this runner, so the owner/API choice
was checked against Chapter 24's `IsGradedInjective` owner and the Chapter 13 homotopy-lifting
pattern `exists_homotopy_lift_to_boundedBelow_injective`. -/

section

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "KQ" => HomotopyCategory.quotient A (up ℤ)

/-- In the homotopy category, precomposition with a quasi-isomorphism is bijective on morphisms
into a K-injective target. This is the canonical owner behind Lemma 24.25.10. -/
theorem homotopyCategory_precomp_bijective_of_quasiIso_to_isKInjective
    {M M' I : CochainComplex A ℤ} (b : M ⟶ M')
    [QuasiIso b] [I.IsKInjective] :
    Function.Bijective
      (fun a' : (KQ).obj M' ⟶ (KQ).obj I ↦
        (KQ).map b ≫ a') := by
  have hb : IsIso (Qh.map ((KQ).map b)) := by
    change IsIso ((KQ ⋙ Qh).map b)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso A) b)).2
      ((isIso_Q_map_iff_quasiIso A b).2 inferInstance)
  let e : Qh.obj ((KQ).obj M) ≅ Qh.obj ((KQ).obj M') :=
    asIso (Qh.map ((KQ).map b))
  have hpreD :
      Function.Bijective
        (fun a' : Qh.obj ((KQ).obj M') ⟶ Qh.obj ((KQ).obj I) ↦
          Qh.map ((KQ).map b) ≫ a') := by
    refine ⟨?_, ?_⟩
    · intro a'₁ a'₂ ha'
      exact (e.symm.homCongr (Iso.refl _)).injective (by simpa [e] using ha')
    · intro a'
      obtain ⟨a'', ha''⟩ := (e.symm.homCongr (Iso.refl _)).surjective a'
      refine ⟨a'', ?_⟩
      simpa [e] using ha''
  let hM' := CochainComplex.IsKInjective.Qh_map_bijective ((KQ).obj M') I
  let hM := CochainComplex.IsKInjective.Qh_map_bijective ((KQ).obj M) I
  have hcomp :
      ((Qh.map :
          ((KQ).obj M ⟶ (KQ).obj I) →
            (Qh.obj ((KQ).obj M) ⟶ Qh.obj ((KQ).obj I))) ∘
        fun a' : (KQ).obj M' ⟶ (KQ).obj I ↦ (KQ).map b ≫ a') =
      (fun a' : Qh.obj ((KQ).obj M') ⟶ Qh.obj ((KQ).obj I) ↦
          Qh.map ((KQ).map b) ≫ a') ∘
        (Qh.map :
          ((KQ).obj M' ⟶ (KQ).obj I) →
            (Qh.obj ((KQ).obj M') ⟶ Qh.obj ((KQ).obj I))) := by
    funext a'
    simp
  have hbijcomp :
      Function.Bijective
        ((Qh.map :
            ((KQ).obj M ⟶ (KQ).obj I) →
              (Qh.obj ((KQ).obj M) ⟶ Qh.obj ((KQ).obj I))) ∘
          fun a' : (KQ).obj M' ⟶ (KQ).obj I ↦
            (KQ).map b ≫ a') := by
    rw [hcomp]
    exact hpreD.comp hM'
  exact (Function.Bijective.of_comp_iff' hM _).mp hbijcomp

/-- Lemma 24.25.10: in the canonical cochain-complex presentation of
`\mathrm{Mod}(\mathcal A, d)` over a ringed site, every morphism `a : M ⟶ I` into a K-injective
target extends along a quasi-isomorphism `b : M ⟶ M'` up to homotopy. In Chapter 24 this is the
lifting statement used for graded-injective K-injective dg-modules; the graded-injective
assumption is redundant for the lift itself once K-injectivity is available. -/
@[stacks 0FSX]
theorem exists_homotopy_lift_of_quasiIso_to_isKInjective
    {M M' I : CochainComplex A ℤ} (a : M ⟶ I) (b : M ⟶ M')
    [QuasiIso b] [I.IsKInjective] :
    ∃ a' : M' ⟶ I, Nonempty (Homotopy (b ≫ a') a) := by
  obtain ⟨a', ha'⟩ :=
    (homotopyCategory_precomp_bijective_of_quasiIso_to_isKInjective b).surjective
      ((KQ).map a)
  obtain ⟨a', rfl⟩ := (KQ).map_surjective a'
  refine ⟨a', ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa [Functor.map_comp] using ha'

end

end DifferentialGradedModule
