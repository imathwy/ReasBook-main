import Mathlib
import stacks_project.Chap15.Definition_15_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct
open Algebra

universe u v w

noncomputable section

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v} {κ : Type w}

/-- The conormal map from the tensorized naive cotangent complex of `P` to the composite
presentation `Q.comp P` sends cycles to cycles. -/
-- Proof sketch: apply functoriality of `Extension.Cotangent.map` with respect to `Q.toComp P`,
-- then use compatibility of cotangent complexes under presentation morphisms. Since the source
-- element lies in the kernel of the tensorized differential of `P`, its image lies in
-- `H₁` of the composite presentation.
theorem tensor_presentation_conormal_map_mem_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : C ⊗[B] P.toExtension.Cotangent)
    (hx : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex)) :
    LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x ∈
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex := sorry

/-- The canonical map from the first homology of the tensorized naive cotangent complex of `P`
to the first homology of the composite presentation `Q.comp P` for an arbitrary presentation
`Q` of `C` over `B`. -/
noncomputable def tensor_presentation_cotangent_h1_to_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      (Q.comp P).toExtension.H1Cotangent :=
  (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)).restrict
    (tensor_presentation_conormal_map_mem_comp_generators_h1 P Q)

/-- The canonical map from the first homology of the tensorized naive cotangent complex of `P`
to `H¹(L_{C/A})`, computed from the canonical self-presentation of `C` over `B`. -/
noncomputable def tensor_presentation_cotangent_h1_to_h1_cotangent
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      H1Cotangent A C :=
  ((Generators.self B C).comp P).equivH1Cotangent.toLinearMap ∘ₗ
    tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)

/-- Any presentation `Q` of `C` over `B` computes the same left Jacobi-Zariski map as the
canonical self-presentation of `C` over `B`. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_eq_of_generators
    (P : Generators A B ι) (Q : Generators B C κ) :
    tensor_presentation_cotangent_h1_to_h1_cotangent C P =
      (Q.comp P).equivH1Cotangent.toLinearMap ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := sorry

/-- The two conormal maps for the composite presentation `Q.comp P` compose to zero. -/
theorem compPresentationConormalSequence_comp_eq_zero
    (P : Generators A B ι) (Q : Generators B C κ) :
    (Extension.Cotangent.map (Q.ofComp P).toExtensionHom).comp
      (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) =
        0 := sorry

/-- The source-facing conormal short complex
`C ⊗[B] I/I² ⟶ K/K² ⟶ J/J²`
attached to the composite presentation `Q.comp P`, where `I`, `J`, and `K` are the kernel ideals
of `P`, `Q`, and `Q.comp P`. -/
noncomputable def compPresentationConormalSequence
    (P : Generators A B ι) (Q : Generators B C κ) :
    ShortComplex (ModuleCat.{max u (max v w)} C) :=
  let α :
      ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) →ₗ[C]
        ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent :=
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
        (Q.comp P).toExtension.Cotangent).symm.toLinearMap ∘ₗ
      LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) ∘ₗ
      (ULift.moduleEquiv :
        ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) ≃ₗ[C]
          (C ⊗[B] P.toExtension.Cotangent)).toLinearMap
  let β :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent →ₗ[C]
        ULift.{max u (max v w), max u w} Q.toExtension.Cotangent :=
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u w} Q.toExtension.Cotangent ≃ₗ[C]
        Q.toExtension.Cotangent).symm.toLinearMap ∘ₗ
      Extension.Cotangent.map (Q.ofComp P).toExtensionHom ∘ₗ
      (ULift.moduleEquiv :
        ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
          (Q.comp P).toExtension.Cotangent).toLinearMap
  let h : β.comp α = 0 := by
    ext x
    simpa [α, β, LinearMap.comp_assoc] using
      congrArg (fun y : Q.toExtension.Cotangent ↦ y.val) <|
        LinearMap.congr_fun (compPresentationConormalSequence_comp_eq_zero P Q) x.down
  ModuleCat.shortComplexOfCompEqZero α β h

/-- The leftmost two maps in the presentation-level Jacobi-Zariski sequence compose to zero. -/
theorem presentationJacobiZariskiLeftSequence_comp_eq_zero
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    (H1Cotangent.map A B C C).comp
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P) =
        0 := sorry

/-- The source-facing left three-term Jacobi-Zariski short complex
`H₁(NL_{B/A} ⊗[B] C) ⟶ H¹(L_{C/A}) ⟶ H¹(L_{C/B})`,
where the left term is represented by the kernel of the tensorized differential attached to the
chosen presentation `P`, and the first map is the canonical one induced by the self-presentation
of `C` over `B`. -/
noncomputable def presentationJacobiZariskiLeftSequence
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    ShortComplex (ModuleCat.{max u v} C) :=
  let α :
      LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
        ULift.{max u v, u} (H1Cotangent A C) :=
    (ULift.moduleEquiv :
      ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C] H1Cotangent A C).symm.toLinearMap ∘ₗ
      tensor_presentation_cotangent_h1_to_h1_cotangent C P
  let β :
      ULift.{max u v, u} (H1Cotangent A C) →ₗ[C]
        ULift.{max u v, u} (H1Cotangent B C) :=
    (ULift.moduleEquiv :
      ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C] H1Cotangent B C).symm.toLinearMap ∘ₗ
      H1Cotangent.map A B C C ∘ₗ
      (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C] H1Cotangent A C).toLinearMap
  let h : β.comp α = 0 := by
    ext x
    change (((H1Cotangent.map A B C C)
        ((tensor_presentation_cotangent_h1_to_h1_cotangent C P) x) :
          LinearMap.ker ((Generators.self B C).toExtension.cotangentComplex))).val = 0
    simpa using congrArg Subtype.val
      (LinearMap.congr_fun (presentationJacobiZariskiLeftSequence_comp_eq_zero C P) x)
  ModuleCat.shortComplexOfCompEqZero α β h

-- Proof sketch: `Generators.Cotangent.exact Q P` already gives exactness of the lower conormal
-- row for the composite presentation. The local complete intersection hypothesis on `Q` makes the
-- kernel ideal `J` Koszul-regular, hence `H₁`-regular; applying Lemma `15.32.5` to the induced
-- ideals identifies the kernel of `K/K² → J/J²` with `(I / I²) ⊗[B] C`, which yields injectivity
-- of the left map.
section

variable [Finite κ]

/-- Lemma 15.33.6: for a chosen presentation `P : A[x_s] → B` and a chosen finite presentation
`Q : B[y_t] → C` indexed by a finite type `κ`, whose kernel ideal is Koszul-regular, the conormal
sequence of the induced composite presentation is exact on the left:
`0 → C ⊗[B] I/I² → K/K² → J/J² → 0`. Here `I`, `J`, and `K` are the kernel ideals of `P`, `Q`,
and `Q.comp P`. -/
theorem comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    (compPresentationConormalSequence P Q).ShortExact := sorry

-- Proof sketch: use the injective conormal sequence above to identify the kernel of
-- `H1Cotangent.map A B C C` with the first homology of the tensorized naive cotangent complex of
-- `P`, then combine this with the Jacobi-Zariski exact sequence
-- `jacobi_zariski_exact_sequence` for the remaining four terms.
/-- For a finite local complete intersection presentation `Q : B[y_t] → C` indexed by a finite
type `κ`, the
Jacobi-Zariski sequence extends on the left by the first homology of the tensorized naive
cotangent complex of `P`, namely
`0 → H₁(NL_{B/A} ⊗[B] C) → H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`,
where `H₁(NL_{B/A} ⊗[B] C)` is written as the kernel of the tensorized differential attached to
the chosen presentation `P`. -/
theorem jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := sorry

/-- The presentation-level left Jacobi-Zariski short complex is exact under the Koszul-regular
kernel hypothesis. -/
theorem presentationJacobiZariskiLeftSequence_exact_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    (presentationJacobiZariskiLeftSequence C P).Exact :=
  (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).2

/-- The left map in the presentation-level Jacobi-Zariski short complex is injective under the
Koszul-regular kernel hypothesis. -/
theorem presentationJacobiZariskiLeftSequence_injective_f_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) :=
  (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).1

end

end
