import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_149_2
import stacks_proof.stacks_project.Chap10.Lemma_10_131_9
import stacks_proof.stacks_project.Chap10.Lemma_10_148_3
import stacks_proof.stacks_project.Chap10.Lemma_10_138_9
import stacks_proof.stacks_project.Chap10.Lemma_10_149_1
import stacks_proof.stacks_project.Chap10.Lemma_10_149_4
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

open scoped TensorProduct
open Algebra TensorProduct
open Algebra.Extension
open TensorProduct.AlgebraTensorModule

universe u v w x y

namespace Algebra.Extension

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable (R) (P : Extension A B)

variable {R} {P}

/-- Helper for Lemma 10.149.5: the `A`-relative quotient from the infinitesimal self-presentation
to the canonical section quotient has kernel exactly the section-image ideal `J' / J²`. -/
lemma selfPresentation_section_quotient_a_relative_ker_eq
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)) = Jbar := by
  intro P0 Jbar
  -- Proof comment: after unfolding the canonical quotient extension, the source algebra map is
  -- the quotient map `P0.infinitesimal.Ring → P0.infinitesimal.Ring ⧸ Jbar`.
  change RingHom.ker
      (Ideal.Quotient.mkₐ A Jbar :
        P0.infinitesimal.Ring →+* P0.infinitesimal.Ring ⧸ Jbar) = Jbar
  simpa using (Ideal.Quotient.mkₐ_ker A Jbar)

/-- Helper for Lemma 10.149.5: the canonical quotient map from the infinitesimal self-presentation
to the section quotient is surjective. -/
lemma selfPresentation_section_quotient_a_relative_surjective
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Surjective (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)) := by
  intro P0 Jbar
  -- Proof comment: once the quotient ring is exposed, surjectivity is the standard quotient-map
  -- surjectivity.
  change Function.Surjective
      (Ideal.Quotient.mkₐ A Jbar :
        P0.infinitesimal.Ring →ₐ[A] P0.infinitesimal.Ring ⧸ Jbar)
  simpa using (Ideal.Quotient.mkₐ_surjective A Jbar)

/-- Helper for Lemma 10.149.5: the `A`-relative conormal sequence for the canonical section
quotient is the standard conormal sequence for the quotient by the section-image ideal. -/
theorem selfPresentation_section_quotient_a_relative_exact
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Exact
        ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap)
        (KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) ∧
      Function.Surjective
        (KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) := by
  intro P0 Jbar
  -- Proof comment: this is Lemma 10.131.9 specialized to the quotient by the explicit
  -- section-image ideal.
  exact kaehlerDifferential_exact_cotangent_tensor_of_surjective
    (R := A)
    (S := P0.infinitesimal.Ring)
    (S' := P0.infinitesimal.Ring ⧸ Jbar)
    Jbar
    (selfPresentation_section_quotient_a_relative_ker_eq (A := A) (B := B) l)
    (selfPresentation_section_quotient_a_relative_surjective (A := A) (B := B) l)

/-- Helper for Lemma 10.149.5: the `R₀`-relative conormal sequence for the canonical section
quotient is again the standard quotient conormal sequence, now viewed over the larger base `R₀`. -/
theorem selfPresentation_section_quotient_r_relative_exact
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Exact
        ((KaehlerDifferential.kerCotangentToTensor R₀ P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap)
        (KaehlerDifferential.mapBaseChange R₀ P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) ∧
      Function.Surjective
        (KaehlerDifferential.mapBaseChange R₀ P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) := by
  intro P0 Jbar
  -- Proof comment: this is the same quotient conormal exactness as in the `A`-relative case,
  -- with only the ground ring changed from `A` to `R₀`.
  exact kaehlerDifferential_exact_cotangent_tensor_of_surjective
    (R := R₀)
    (S := P0.infinitesimal.Ring)
    (S' := P0.infinitesimal.Ring ⧸ Jbar)
    Jbar
    (selfPresentation_section_quotient_a_relative_ker_eq (A := A) (B := B) l)
    (selfPresentation_section_quotient_a_relative_surjective (A := A) (B := B) l)

/-- Helper for Lemma 10.149.5: each explicit section generator maps, under the `A`-relative
conormal map for the canonical quotient, to the corresponding differential class. -/
theorem selfPresentation_section_quotient_a_relative_generator_toCotangent
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let sectionGenerator :
        P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
        (P0.infinitesimal.Ring ⧸ Jbar)).comp
      (Ideal.Cotangent.equivOfEq Jbar
        (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
        (selfPresentation_section_quotient_a_relative_ker_eq
          (A := A) (B := B) l).symm).toLinearMap)
      (Ideal.toCotangent Jbar ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩) =
      1 ⊗ₜ[P0.infinitesimal.Ring] KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
  intro P0 Jbar sectionGenerator
  -- Proof comment: this is exactly the concrete generator formula from Lemma 10.131.9, applied to
  -- the quotient ideal `Jbar`.
  simpa [sectionGenerator] using
    kerCotangentToTensorOfKerEq_toCotangent
      (R := A)
      (S := P0.infinitesimal.Ring)
      (S' := P0.infinitesimal.Ring ⧸ Jbar)
      Jbar
      (selfPresentation_section_quotient_a_relative_ker_eq (A := A) (B := B) l)
      ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩

/-- Helper for Lemma 10.149.5: each chosen section generator already lies in the image of the
`A`-relative conormal map for the canonical quotient. -/
theorem selfPresentation_section_quotient_a_relative_generator_mem_range
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let sectionGenerator :
        P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    1 ⊗ₜ[P0.infinitesimal.Ring] KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator ∈
      LinearMap.range
        ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap) := by
  intro P0 Jbar sectionGenerator
  -- Proof comment: witness the target element by the corresponding cotangent class of the chosen
  -- section generator.
  refine ⟨Ideal.toCotangent Jbar ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩, ?_⟩
  simpa [sectionGenerator] using
    selfPresentation_section_quotient_a_relative_generator_toCotangent
      (A := A) (B := B) l x

/-- Helper for Lemma 10.149.5: the identity range on the cotangent space of the self-presentation
already spans the whole module over the canonical quotient ring. -/
theorem selfPresentation_section_quotient_cotangentSpace_identity_span_top
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
    Submodule.span Q.Ring
      (Set.range (fun x : P0.CotangentSpace ↦ x)) = ⊤ := by
  intro P0 Q
  -- Proof comment: the identity map is surjective, so its range spans the whole module.
  simpa using
    (LinearMap.range_eq_top.2
      (show Function.Surjective
          (LinearMap.id : P0.CotangentSpace →ₗ[Q.Ring] P0.CotangentSpace) from
          fun x ↦ ⟨x, rfl⟩))

/-- Helper for Lemma 10.149.5: a surjective family spans the whole target module. -/
lemma submodule_span_range_eq_top_of_surjective
    {R₀ : Type*} {M₀ : Type*} [Semiring R₀] [AddCommMonoid M₀] [Module R₀ M₀]
    {ι : Type*} (v : ι → M₀) (hv : Function.Surjective v) :
    Submodule.span R₀ (Set.range v) = ⊤ := by
  -- Proof comment: surjectivity identifies the range with the whole ambient set, whose span is
  -- tautologically all of `M₀`.
  rw [Set.range_eq_univ.2 hv]
  simp

end Algebra.Extension
