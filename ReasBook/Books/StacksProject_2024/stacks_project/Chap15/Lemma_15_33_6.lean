import Mathlib
import StacksProject_2024.Chap10.Lemma_10_134_2
import StacksProject_2024.Chap10.Lemma_10_134_4_Jacobi_Zariski_sequence
import StacksProject_2024.Chap15.Lemma_15_30_3
import StacksProject_2024.Chap15.Lemma_15_32_4

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

/-- Helper for Lemma 15.33.6: after tensoring `P` up to `C`, the conormal map induced by
`Q.toComp P` still commutes with the cotangent differential. -/
theorem tensor_presentation_conormal_map_comp_cotangentComplex
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : C ⊗[B] P.toExtension.Cotangent) :
    (Q.comp P).toExtension.cotangentComplex
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x) =
      ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange C)
        (LinearMap.baseChange C P.toExtension.cotangentComplex x) := by
  -- Tensor the untensorized chain-map identity pointwise across the presentation `P`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c y
    -- On pure tensors, reduce to the owner compatibility before retensoring by `c`.
    rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul]
    exact congrArg (fun z ↦ c • z)
      (Extension.CotangentSpace.map_cotangentComplex
        ((Q.toComp P).toExtensionHom) y).symm
  · intro x y hx hy
    -- Additivity of all maps upgrades the pure-tensor calculation to arbitrary tensors.
    simp [map_add, hx, hy]

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
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex := by
  -- Rewrite the target differential through the tensorized compatibility square.
  change
    (Q.comp P).toExtension.cotangentComplex
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x) = 0
  rw [tensor_presentation_conormal_map_comp_cotangentComplex P Q x]
  -- The source hypothesis says exactly that the tensorized differential of `P` vanishes on `x`.
  have hx0 : LinearMap.baseChange C P.toExtension.cotangentComplex x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  rw [hx0, map_zero]

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

/-- Helper for Lemma 15.33.6: tensoring a composite of a conormal map with the source cotangent
differential agrees with first tensoring the differential and then applying the lifted map. -/
theorem tensor_presentation_liftBaseChange_comp_cotangentComplex
    (P : Generators A B ι)
    {M : Type*} [AddCommGroup M] [Module B M] [Module C M] [IsScalarTower B C M]
    (φ : P.toExtension.CotangentSpace →ₗ[B] M)
    (x : C ⊗[B] P.toExtension.Cotangent) :
    LinearMap.liftBaseChange C (φ.comp P.toExtension.cotangentComplex) x =
      (LinearMap.liftBaseChange C φ) (LinearMap.baseChange C P.toExtension.cotangentComplex x) := by
  -- Evaluate the tensorized composite on pure tensors and extend by additivity.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c y
    -- On pure tensors the two descriptions are the same scalar multiple of `φ (d y)`.
    rw [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    rfl
  · intro x y hx hy
    -- Additivity upgrades the pure-tensor identity to arbitrary tensors.
    rw [map_add, hx, hy]
    rw [(LinearMap.baseChange C P.toExtension.cotangentComplex).map_add]
    exact ((LinearMap.liftBaseChange C φ).map_add _ _).symm

/-- Helper for Lemma 15.33.6: postcomposing the tensorized conormal map by a morphism of
composite presentations agrees with tensoring the composite morphism itself. -/
theorem tensor_presentation_postcomp_liftBaseChange_cotangent
    (P : Generators A B ι) (Q : Generators B C κ)
    {κ' : Type*} (Q' : Generators B C κ')
    (f : (Q.comp P).Hom (Q'.comp P))
    (x : C ⊗[B] P.toExtension.Cotangent) :
    Extension.Cotangent.map f.toExtensionHom
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x) =
      LinearMap.liftBaseChange C
        (Extension.Cotangent.map ((f.comp (Q.toComp P)).toExtensionHom)) x := by
  -- Reduce to pure tensors and use functoriality of `Extension.Cotangent.map`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c y
    rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.liftBaseChange_tmul]
    exact congrArg (fun z ↦ c • z) <| by
      simpa [Generators.Hom.toExtensionHom_comp, Extension.Cotangent.map_comp]
  · intro x y hx hy
    -- Additivity upgrades the pure-tensor computation to arbitrary tensors.
    simp [map_add, hx, hy]

/-- Helper for Lemma 15.33.6: the `map_sub_map` homotopy term vanishes on tensorized source
cycles, so the two ambient tensorized conormal maps agree there. -/
theorem tensorized_cycle_map_eq_on_ker_of_map_sub_map
    (P : Generators A B ι) (Q : Generators B C κ)
    {κ' : Type*} (Q' : Generators B C κ')
    (f : (Q.comp P).Hom (Q'.comp P))
    (x : C ⊗[B] P.toExtension.Cotangent)
    (hx : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex)) :
    LinearMap.liftBaseChange C
        (Extension.Cotangent.map ((f.comp (Q.toComp P)).toExtensionHom)) x =
      LinearMap.liftBaseChange C
        (Extension.Cotangent.map (Q'.toComp P).toExtensionHom) x := by
  -- Route correction: compare the raw tensorized maps first, so the `map_sub_map` homotopy term
  -- can be killed directly by the cycle condition before descending to `restrict`.
  have hsub :=
    congrArg
      (fun φ : P.toExtension.Cotangent →ₗ[B] (Q'.comp P).toExtension.Cotangent ↦
        LinearMap.liftBaseChange C φ x)
      (Extension.Cotangent.map_sub_map
        ((f.comp (Q.toComp P)).toExtensionHom)
        ((Q'.toComp P).toExtensionHom))
  change
    (LinearMap.liftBaseChange C
        (Extension.Cotangent.map ((f.comp (Q.toComp P)).toExtensionHom) -
          Extension.Cotangent.map (Q'.toComp P).toExtensionHom) x) =
      LinearMap.liftBaseChange C
        ((((f.comp (Q.toComp P)).toExtensionHom).sub ((Q'.toComp P).toExtensionHom)) ∘ₗ
          P.toExtension.cotangentComplex) x at hsub
  rw [tensor_presentation_liftBaseChange_comp_cotangentComplex
      (P := P)
      (φ := ((f.comp (Q.toComp P)).toExtensionHom).sub ((Q'.toComp P).toExtensionHom))
      (x := x)] at hsub
  have hx0 : LinearMap.baseChange C P.toExtension.cotangentComplex x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  rw [hx0, map_zero] at hsub
  simpa [LinearMap.sub_apply, sub_eq_zero] using hsub

/-- Helper for Lemma 15.33.6: the tensorized cycle map into `H₁` of a composite presentation is
natural in the chosen presentation of `C` over `B`. -/
theorem tensor_presentation_cotangent_h1_to_comp_generators_h1_naturality
    (P : Generators A B ι) (Q : Generators B C κ)
    {κ' : Type*} (Q' : Generators B C κ')
    (f : (Q.comp P).Hom (Q'.comp P)) :
    Extension.H1Cotangent.map f.toExtensionHom ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q =
          tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q' := by
  -- Compare the restricted maps by first comparing their ambient tensorized conormal maps.
  ext x
  -- The left map is the postcomposition of the raw tensorized conormal map with `f`.
  change
    Extension.Cotangent.map f.toExtensionHom
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x.1) =
      LinearMap.liftBaseChange C
        (Extension.Cotangent.map (Q'.toComp P).toExtensionHom) x.1
  rw [tensor_presentation_postcomp_liftBaseChange_cotangent]
  -- The cycle-level comparison kills the `map_sub_map` homotopy term on the source kernel.
  exact tensorized_cycle_map_eq_on_ker_of_map_sub_map P Q Q' f x.1 x.2

/-- Any presentation `Q` of `C` over `B` computes the same left Jacobi-Zariski map as the
canonical self-presentation of `C` over `B`. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_eq_of_generators
    (P : Generators A B ι) (Q : Generators B C κ) :
    tensor_presentation_cotangent_h1_to_h1_cotangent C P =
      (Q.comp P).equivH1Cotangent.toLinearMap ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := by
  let f : (Q.comp P).Hom ((Generators.self B C).comp P) :=
    Generators.defaultHom (Q.comp P) ((Generators.self B C).comp P)
  -- Rewrite through the canonical comparison with the self-presentation of `C` over `B`.
  calc
    tensor_presentation_cotangent_h1_to_h1_cotangent C P
        = ((Generators.self B C).comp P).equivH1Cotangent.toLinearMap ∘ₗ
            (Extension.H1Cotangent.map f.toExtensionHom ∘ₗ
              tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q) := by
            rw [tensor_presentation_cotangent_h1_to_h1_cotangent]
            rw [← tensor_presentation_cotangent_h1_to_comp_generators_h1_naturality
              (P := P) (Q := Q) (Q' := Generators.self B C) f]
    _ = (((Generators.self B C).comp P).equivH1Cotangent.toLinearMap ∘ₗ
          Extension.H1Cotangent.map f.toExtensionHom) ∘ₗ
            tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := by
          rw [LinearMap.comp_assoc]
    _ = (Q.comp P).equivH1Cotangent.toLinearMap ∘ₗ
          tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := by
          rw [Generators.equivH1Cotangent_naturality (f := f)]

/-- The two conormal maps for the composite presentation `Q.comp P` compose to zero. -/
theorem compPresentationConormalSequence_comp_eq_zero
    (P : Generators A B ι) (Q : Generators B C κ) :
    (Extension.Cotangent.map (Q.ofComp P).toExtensionHom).comp
      (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) =
        0 := by
  -- The owner exactness theorem already packages the vanishing of the composite conormal map.
  simpa only using (Generators.Cotangent.exact Q P).linearMap_comp_eq_zero

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

/-- Helper for Lemma 15.33.6: rewriting the owner map `H1Cotangent.map A B C C` through the
self-presentation of `C` over `B` reduces it to the presentation morphism
`(Generators.self B C).ofComp P`. -/
theorem h1Cotangent_map_eq_self_ofComp_on_selfcomp
    (P : Generators A B ι) :
    (H1Cotangent.map A B C C).comp (((Generators.self B C).comp P).equivH1Cotangent.toLinearMap) =
      (Generators.self B C).equivH1Cotangent.toLinearMap ∘ₗ
        Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom := by
  -- Compare the two owner maps after unfolding both canonical `H₁` identifications.
  ext x
  simp only [LinearMap.comp_apply, H1Cotangent.map, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv, Extension.H1Cotangent.equiv]
  simpa [Generators.Hom.toExtensionHom_comp] using congrArg Subtype.val <|
    DFunLike.congr_fun
      (Extension.H1Cotangent.map_eq
        (((Generators.defaultHom (Generators.self A C) (Generators.self B C)).comp
            (Generators.defaultHom ((Generators.self B C).comp P) (Generators.self A C))).toExtensionHom)
        (((Generators.defaultHom (Generators.self B C) (Generators.self B C)).comp
            ((Generators.self B C).ofComp P)).toExtensionHom)) x

/-- Helper for Lemma 15.33.6: rewriting the owner map `H1Cotangent.map A B C C` through an
arbitrary presentation `Q` of `C` over `B` reduces it to the induced morphism `Q.ofComp P`. -/
theorem h1Cotangent_map_eq_ofComp_on_comp
    (P : Generators A B ι) (Q : Generators B C κ) :
    (H1Cotangent.map A B C C).comp ((Q.comp P).equivH1Cotangent.toLinearMap) =
      Q.equivH1Cotangent.toLinearMap ∘ₗ
        Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom := by
  -- Compare the two owner maps after unfolding both canonical `H₁` identifications.
  ext x
  simp only [LinearMap.comp_apply, H1Cotangent.map, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv, Extension.H1Cotangent.equiv]
  simpa [Generators.Hom.toExtensionHom_comp] using congrArg Subtype.val <|
    DFunLike.congr_fun
      (Extension.H1Cotangent.map_eq
        (((Generators.defaultHom (Generators.self A C) (Generators.self B C)).comp
            (Generators.defaultHom (Q.comp P) (Generators.self A C))).toExtensionHom)
        (((Generators.defaultHom Q (Generators.self B C)).comp
            (Q.ofComp P)).toExtensionHom)) x

/-- The leftmost two maps in the presentation-level Jacobi-Zariski sequence compose to zero. -/
theorem presentationJacobiZariskiLeftSequence_comp_eq_zero
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    (H1Cotangent.map A B C C).comp
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P) =
        0 := by
  -- Route correction: rewrite the owner map through the self-presentation of `C` over `B`,
  -- then reduce to the vanishing of the raw composite conormal map for `P` and `self B C`.
  rw [tensor_presentation_cotangent_h1_to_h1_cotangent]
  change
    ((H1Cotangent.map A B C C).comp (((Generators.self B C).comp P).equivH1Cotangent.toLinearMap)).comp
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)) =
      0
  rw [h1Cotangent_map_eq_self_ofComp_on_selfcomp (P := P)]
  have hzero :
      Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C) =
        0 := by
      ext x
      -- On cycles, the induced `H₁` map is computed by the underlying cotangent map.
      change
        (Extension.Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom
            (LinearMap.liftBaseChange C
              (Extension.Cotangent.map ((Generators.self B C).toComp P).toExtensionHom) x.1)).val = 0
      simpa [tensor_presentation_cotangent_h1_to_comp_generators_h1, LinearMap.comp_apply] using
        LinearMap.congr_fun
          (compPresentationConormalSequence_comp_eq_zero P (Generators.self B C)) x.1
  calc
    ((Generators.self B C).equivH1Cotangent.toLinearMap ∘ₗ
          Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom) ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)
      = (Generators.self B C).equivH1Cotangent.toLinearMap ∘ₗ
          (Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom ∘ₗ
            tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)) := by
          ext x
          rfl
    _ = 0 := by rw [hzero, LinearMap.comp_zero]

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
  (ModuleCat.shortComplexOfCompEqZero
      (R := C)
      (M := LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex))
      (N := ULift.{max u v, u} (H1Cotangent A C))
      (L := ULift.{max u v, u} (H1Cotangent B C))
      α β h :
    ShortComplex (ModuleCat.{max u v} C))

-- Proof sketch: `Generators.Cotangent.exact Q P` already gives exactness of the lower conormal
-- row for the composite presentation. The local complete intersection hypothesis on `Q` makes the
-- kernel ideal `J` Koszul-regular, hence `H₁`-regular; applying Lemma `15.32.5` to the induced
-- ideals identifies the kernel of `K/K² → J/J²` with `(I / I²) ⊗[B] C`, which yields injectivity
-- of the left map.
section

variable [Finite κ]

/-- Helper for Lemma 15.33.6: every Koszul-regular ideal is automatically `H₁`-regular. -/
theorem Ideal.IsKoszulRegularIdeal.isH1Regular_of_koszulRegular
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsKoszulRegularIdeal) :
    I.IsH1RegularIdeal := by
  -- Unpack the local Koszul-regular witnesses and convert each one to an `H₁`-regular witness.
  rw [Ideal.isKoszulRegularIdeal_iff] at hI
  rw [Ideal.isH1RegularIdeal_iff]
  intro p hp hIp
  rcases hI p hp hIp with ⟨g, hg, r, f, hf, hspan⟩
  exact ⟨g, hg, r, f,
    RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence hf, hspan⟩

/-- Helper for Lemma 15.33.6: the owner map from the composite presentation ring
`A[x_s, y_t]` to the chosen `B[y_t]`-presentation ring is surjective. -/
theorem comp_presentation_owner_map_surjective
    (P : Generators A B ι) (Q : Generators B C κ) :
    Function.Surjective (Q.ofComp P).toAlgHom.toRingHom := by
  -- Follow the source quotient route first: build a section on `B[y_t]` by sending each `y_t`
  -- to the corresponding `inl` variable and each coefficient of `B` to a polynomial in the
  -- `inr` variables via the chosen presentation `P`.
  intro x
  let S : Q.Ring → Prop := fun y => ∃ a, (Q.ofComp P).toAlgHom.toRingHom a = y
  change S x
  refine MvPolynomial.induction_on x ?_ ?_ ?_
  · intro b
    -- Constants lift through the section `σ'` of `P`, then are reinserted as `inr` variables.
    refine ⟨MvPolynomial.rename Sum.inr (P.σ' b), ?_⟩
    change
      MvPolynomial.aeval (Sum.elim MvPolynomial.X fun i ↦ MvPolynomial.C (P.val i))
          (MvPolynomial.rename Sum.inr (P.σ' b)) =
        MvPolynomial.C b
    rw [MvPolynomial.aeval_rename]
    simpa using congrArg MvPolynomial.C (P.aeval_val_σ' b)
  · intro p q hp hq
    -- Additivity lets us combine preimages of the two summands.
    rcases hp with ⟨p', hp'⟩
    rcases hq with ⟨q', hq'⟩
    refine ⟨p' + q', ?_⟩
    rw [map_add, hp', hq']
  · intro p n hp
    -- Multiplication by a variable lifts by multiplying with the matching `inl` variable.
    rcases hp with ⟨p', hp'⟩
    refine ⟨p' * MvPolynomial.X (Sum.inl n), ?_⟩
    rw [map_mul, hp']
    simp [Algebra.Generators.ofComp]

/-- Helper for Lemma 15.33.6: quotienting the composite presentation ring by the kernel of the
owner map `(Q.ofComp P)` recovers the chosen `B[y_t]`-presentation ring. -/
noncomputable def comp_presentation_quotient_kernel_ringEquiv
    (P : Generators A B ι) (Q : Generators B C κ) :
    ((Q.comp P).toExtension.Ring ⧸ RingHom.ker ((Q.ofComp P).toAlgHom.toRingHom)) ≃+*
      Q.toExtension.Ring :=
  RingHom.quotientKerEquivOfSurjective (comp_presentation_owner_map_surjective P Q)

/-- Helper for Lemma 15.33.6: the quotient-kernel equivalence for `(Q.ofComp P)` composes with
the quotient map to recover the owner ring hom itself. -/
theorem comp_presentation_quotient_kernel_ringEquiv_comp_quotient_mk
    (P : Generators A B ι) (Q : Generators B C κ) :
    (comp_presentation_quotient_kernel_ringEquiv P Q).toRingHom.comp
        (Ideal.Quotient.mk (RingHom.ker ((Q.ofComp P).toAlgHom.toRingHom))) =
      (Q.ofComp P).toAlgHom.toRingHom := by
  -- This is the defining property of `RingHom.quotientKerEquivOfSurjective`.
  rfl

/-- Helper for Lemma 15.33.6: the owner map `(Q.ofComp P)` has kernel equal to the lifted source
kernel ideal coming from `P`. -/
theorem comp_presentation_owner_ker_eq_map_source_ker
    (P : Generators A B ι) (Q : Generators B C κ) :
    RingHom.ker ((Q.ofComp P).toAlgHom.toRingHom) =
      Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker := by
  -- This is exactly the kernel formula already packaged by `Generators.map_toComp_ker`.
  simpa using (Generators.map_toComp_ker Q P).symm

/-- Helper for Lemma 15.33.6: after quotienting the composite presentation by the lifted kernel
of `P`, the image of the composite kernel is exactly the kernel ideal of `Q`. -/
theorem comp_presentation_quotient_kernel_map_eq_target_kernel
    (P : Generators A B ι) (Q : Generators B C κ) :
    let Icomp : Ideal (Q.comp P).toExtension.Ring :=
      Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
    let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
    ∃ e : ((Q.comp P).toExtension.Ring ⧸ Icomp) ≃+* Q.toExtension.Ring,
      Ideal.map e.toRingHom (K.map (Ideal.Quotient.mk Icomp)) = Q.toExtension.ker := by
  let Icomp : Ideal (Q.comp P).toExtension.Ring :=
    Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
  let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
  let e : ((Q.comp P).toExtension.Ring ⧸ Icomp) ≃+* Q.toExtension.Ring :=
    (Ideal.quotEquivOfEq
      (comp_presentation_owner_ker_eq_map_source_ker (P := P) (Q := Q)).symm).trans
      (comp_presentation_quotient_kernel_ringEquiv P Q)
  refine ⟨e, ?_⟩
  -- The transported quotient equivalence still factors the owner map `(Q.ofComp P)`.
  have hecomp :
      e.toRingHom.comp (Ideal.Quotient.mk Icomp) = (Q.ofComp P).toAlgHom.toRingHom := by
    ext x
    change
      comp_presentation_quotient_kernel_ringEquiv P Q
          (Ideal.quotEquivOfEq
            (comp_presentation_owner_ker_eq_map_source_ker (P := P) (Q := Q)).symm
            (Ideal.Quotient.mk Icomp x)) =
        (Q.ofComp P).toAlgHom.toRingHom x
    calc
      comp_presentation_quotient_kernel_ringEquiv P Q
          (Ideal.quotEquivOfEq
            (comp_presentation_owner_ker_eq_map_source_ker (P := P) (Q := Q)).symm
            (Ideal.Quotient.mk Icomp x))
        = comp_presentation_quotient_kernel_ringEquiv P Q
            (Ideal.Quotient.mk
              (RingHom.ker ((Q.ofComp P).toAlgHom.toRingHom)) x) := by
                simpa using
                  congrArg (comp_presentation_quotient_kernel_ringEquiv P Q)
                    (Ideal.quotEquivOfEq_mk
                      (comp_presentation_owner_ker_eq_map_source_ker
                        (P := P) (Q := Q)).symm x)
      _ = (Q.ofComp P).toAlgHom.toRingHom x := rfl
  -- Mapping the composite kernel through this factorization is exactly `map_ofComp_ker`.
  calc
    Ideal.map e.toRingHom (K.map (Ideal.Quotient.mk Icomp))
        = Ideal.map (e.toRingHom.comp (Ideal.Quotient.mk Icomp)) K := by
            rw [Ideal.map_map]
    _ = Q.toExtension.ker := by
          rw [hecomp]
          simpa [K] using (Generators.map_ofComp_ker Q P)

/-- Helper for Lemma 15.33.6: the quotient ideal `K / Icomp` inherited from the composite
presentation is `H₁`-regular once `Q.ker` is Koszul-regular. -/
theorem comp_presentation_quotient_kernel_isH1Regular
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    let Icomp : Ideal (Q.comp P).toExtension.Ring :=
      Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
    let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
    Ideal.IsH1RegularIdeal (K.map (Ideal.Quotient.mk Icomp)) := by
  let Icomp : Ideal (Q.comp P).toExtension.Ring :=
    Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
  let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
  rcases comp_presentation_quotient_kernel_map_eq_target_kernel P Q with ⟨e, he⟩
  letI : Algebra ((Q.comp P).toExtension.Ring ⧸ Icomp) Q.toExtension.Ring := e.toRingHom.toAlgebra
  have hff :
      (algebraMap ((Q.comp P).toExtension.Ring ⧸ Icomp) Q.toExtension.Ring).FaithfullyFlat := by
    simpa using
      (RingHom.FaithfullyFlat.of_bijective e.bijective : e.toRingHom.FaithfullyFlat)
  -- Descend Koszul-regularity across the quotient equivalence, then forget to `H₁`-regularity.
  have hKoszul :
      Ideal.IsKoszulRegularIdeal
        (Ideal.map (algebraMap ((Q.comp P).toExtension.Ring ⧸ Icomp) Q.toExtension.Ring)
          (K.map (Ideal.Quotient.mk Icomp))) := by
    have hmap :
        Ideal.map (algebraMap ((Q.comp P).toExtension.Ring ⧸ Icomp) Q.toExtension.Ring)
            (K.map (Ideal.Quotient.mk Icomp)) = Q.toExtension.ker := by
      simpa using he
    rw [hmap]
    exact hQ
  have hsource :
      Ideal.IsKoszulRegularIdeal (K.map (Ideal.Quotient.mk Icomp)) :=
    Ideal.IsKoszulRegularIdeal.of_faithfullyFlat hff hKoszul
  exact Ideal.IsKoszulRegularIdeal.isH1Regular_of_koszulRegular hsource

/-- Helper for Lemma 15.33.6: once the quotient ideal `K / Icomp` is `H₁`-regular, Lemma
`15.32.5` gives the key ideal equality `Icomp ∩ K² = Icomp * K`. -/
theorem comp_presentation_inf_sq_eq_mul
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    let Icomp : Ideal (Q.comp P).toExtension.Ring :=
      Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
    let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
    Icomp ⊓ K ^ 2 = Icomp * K := by
  let Icomp : Ideal (Q.comp P).toExtension.Ring :=
    Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
  let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
  have hIK : Icomp ≤ K := by
    -- The composite kernel contains the lifted source kernel as its left summand.
    have hsup : K = Icomp ⊔ Ideal.comap (Q.ofComp P).toAlgHom Q.toExtension.ker := by
      simpa [Icomp, K] using (Generators.ker_comp_eq_sup Q P)
    rw [hsup]
    exact le_sup_left
  have hreg : Ideal.IsH1RegularIdeal (K.map (Ideal.Quotient.mk Icomp)) :=
    comp_presentation_quotient_kernel_isH1Regular P Q hQ
  -- TODO: restore the dependency-closed proof by reusing Lemma 15.32.5 once its current import
  -- chain compiles again; the required closing statement is exactly the standard criterion
  -- `Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal Icomp K hIK hreg`.
  let _ := hIK
  let _ := hreg
  sorry

/-- Helper for Lemma 15.33.6: if a pure tensor generator from `P.ker / P.ker²` maps to zero in
the composite conormal module, then its image in the composite presentation ring lies in `K²`. -/
theorem comp_presentation_left_conormal_tmul_mk_eq_zero_iff
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : ↥P.toExtension.ker) :
    LinearMap.liftBaseChange C
        (Extension.Cotangent.map (Q.toComp P).toExtensionHom)
        ((1 : C) ⊗ₜ[B] Extension.Cotangent.mk x) = 0 ↔
      (Q.toComp P).toAlgHom.toRingHom x.1 ∈ ((Q.comp P).toExtension.ker) ^ 2 := by
  let y : ↥((Q.comp P).toExtension.ker) :=
    ⟨(Q.toComp P).toAlgHom.toRingHom x.1, by
      -- The image of a source-kernel element lies in the mapped source kernel, hence in `K`.
      have hxmap :
          (Q.toComp P).toAlgHom.toRingHom x.1 ∈
            Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker :=
        Ideal.mem_map_of_mem _ x.2
      have hIcomp_le_K :
          Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker ≤
            (Q.comp P).toExtension.ker := by
        -- The source-kernel summand is the left summand in the standard kernel decomposition.
        have hsup :
            (Q.comp P).toExtension.ker =
              Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker ⊔
                Ideal.comap (Q.ofComp P).toAlgHom Q.toExtension.ker := by
          simpa using (Generators.ker_comp_eq_sup Q P)
        rw [hsup]
        exact le_sup_left
      exact hIcomp_le_K hxmap⟩
  -- Evaluate the tensorized map on the pure tensor and rewrite vanishing in the cotangent module
  -- as the square-membership criterion for the represented kernel element.
  rw [LinearMap.liftBaseChange_tmul, one_smul, Extension.Cotangent.map_mk]
  change Extension.Cotangent.mk y = 0 ↔ (y : (Q.comp P).toExtension.Ring) ∈ ((Q.comp P).toExtension.ker) ^ 2
  simpa [y] using (Ideal.toCotangent_eq_zero ((Q.comp P).toExtension.ker) y)

/-- Helper for Lemma 15.33.6: a pure tensor generator in the kernel of the left conormal map
already represents an element of the textbook intersection `Icomp ∩ K²`. -/
theorem comp_presentation_left_conormal_tmul_mk_mem_inf_sq
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : ↥P.toExtension.ker)
    (hzero :
      LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom)
          ((1 : C) ⊗ₜ[B] Extension.Cotangent.mk x) = 0) :
    let Icomp : Ideal (Q.comp P).toExtension.Ring :=
      Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
    let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
    (Q.toComp P).toAlgHom.toRingHom x.1 ∈ Icomp ⊓ K ^ 2 := by
  let Icomp : Ideal (Q.comp P).toExtension.Ring :=
    Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
  let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
  refine ⟨?_, ?_⟩
  · -- Membership in `Icomp` is tautological from `x ∈ P.ker`.
    exact Ideal.mem_map_of_mem _ x.2
  · -- The previous lemma turns vanishing in cotangent into membership in `K²`.
    simpa [K] using
      (comp_presentation_left_conormal_tmul_mk_eq_zero_iff (P := P) (Q := Q) x).1 hzero

/-- Helper for Lemma 15.33.6: the local-complete-intersection ideal equality
`Icomp ∩ K² = Icomp * K` should force injectivity of the left conormal map for the composite
presentation. -/
theorem comp_presentation_left_conormal_injective_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    Function.Injective
      (LinearMap.liftBaseChange C
        (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) := by
  let Icomp : Ideal (Q.comp P).toExtension.Ring :=
    Ideal.map (Q.toComp P).toAlgHom.toRingHom P.toExtension.ker
  let K : Ideal (Q.comp P).toExtension.Ring := (Q.comp P).toExtension.ker
  have hIK : Icomp ⊓ K ^ 2 = Icomp * K :=
    comp_presentation_inf_sq_eq_mul P Q hQ
  -- Route correction: the source proof computes the kernel after transporting the source to the
  -- quotient model `Icomp / (Icomp * K)`. The new lemmas above already verify the key generator
  -- step: a kernel representative lands in `Icomp ⊓ K²`, hence in `Icomp * K` by `hIK`.
  --
  -- TODO: finish the quotient transport in the ambient module `F := (K : Submodule _ _)` once the
  -- prerequisite quotient-kernel API from Lemma 15.27.3 is available in this workspace. The
  -- intended route is to identify `C ⊗[B] P.toExtension.Cotangent` with the quotient model for
  -- `Icomp.submoduleOf F`, rewrite the left conormal map as the corresponding quotient inclusion,
  -- and then kill its kernel using `hIK`.
  let _ := hIK
  sorry

/-- Lemma 15.33.6: for a chosen presentation `P : A[x_s] → B` and a chosen finite presentation
`Q : B[y_t] → C` indexed by a finite type `κ`, whose kernel ideal is Koszul-regular, the conormal
sequence of the induced composite presentation is exact on the left:
`0 → C ⊗[B] I/I² → K/K² → J/J² → 0`. Here `I`, `J`, and `K` are the kernel ideals of `P`, `Q`,
and `Q.comp P`. -/
theorem comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    (compPresentationConormalSequence P Q).ShortExact := by
  -- Route correction: the quotient-kernel transport layer is now isolated in the helper above.
  -- Once that injectivity bridge is available, the remaining packaging to `ShortExact` is routine.
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
  have hExactαβ : Function.Exact α β := by
    -- Rewrite the lifted row back to the canonical conormal sequence before applying exactness.
    let e₁ :
        ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) ≃ₗ[C]
          (C ⊗[B] P.toExtension.Cotangent) :=
      ULift.moduleEquiv
    let e₂ :
        ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
          (Q.comp P).toExtension.Cotangent :=
      ULift.moduleEquiv
    let e₃ :
        ULift.{max u (max v w), max u w} Q.toExtension.Cotangent ≃ₗ[C]
          Q.toExtension.Cotangent :=
      ULift.moduleEquiv
    have h₁₂ :
        α ∘ₗ e₁.symm.toLinearMap =
          e₂.symm.toLinearMap ∘ₗ
            LinearMap.liftBaseChange C
              (Extension.Cotangent.map (Q.toComp P).toExtensionHom) := by
      ext x
      rfl
    have h₂₃ :
        β ∘ₗ e₂.symm.toLinearMap =
          e₃.symm.toLinearMap ∘ₗ
            Extension.Cotangent.map (Q.ofComp P).toExtensionHom := by
      ext x
      rfl
    exact Function.Exact.of_ladder_linearEquiv_of_exact h₁₂ h₂₃ (Generators.Cotangent.exact Q P)
  have hExact : (compPresentationConormalSequence P Q).Exact := by
    -- The short complex exactness predicate is the function-level exactness of the packaged row.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    change Function.Exact α β
    exact hExactαβ
  have hMono : Mono (compPresentationConormalSequence P Q).f := by
    -- Injectivity of the raw left conormal map survives the ULift identifications.
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    change
      ULift.up
          (LinearMap.liftBaseChange C
            (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x.down) =
        ULift.up
          (LinearMap.liftBaseChange C
            (Extension.Cotangent.map (Q.toComp P).toExtensionHom) y.down) at hxy
    apply ULift.ext
    exact comp_presentation_left_conormal_injective_of_koszul_regular_kernel P Q hQ <| by
      simpa using congrArg ULift.down hxy
  have hEpi : Epi (compPresentationConormalSequence P Q).g := by
    -- Surjectivity of the raw right conormal map also survives the ULift identifications.
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := Generators.Cotangent.surjective_map_ofComp Q P z.down
    refine ⟨⟨y⟩, ?_⟩
    change ULift.up (Extension.Cotangent.map (Q.ofComp P).toExtensionHom y) = z
    apply ULift.ext
    simpa using hy
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Lemma 15.33.6: injectivity of the ambient tensorized conormal map restricts to
injectivity on source cycles. -/
theorem tensor_presentation_cotangent_h1_to_comp_generators_h1_injective_of_conormal_injective
    (P : Generators A B ι) (Q : Generators B C κ)
    (hinj :
      Function.Injective
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom))) :
    Function.Injective
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q) := by
  intro x y hxy
  apply Subtype.ext
  exact hinj (congrArg Subtype.val hxy)

/-- Helper for Lemma 15.33.6: exactness for a chosen finite presentation `Q` transports through
the canonical comparison with the owner `H₁(L_{C/A}) → H₁(L_{C/B})`. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_exact_of_comp_exact
    (P : Generators A B ι) (Q : Generators B C κ)
    (hExact :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
        (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom)) :
    Function.Exact
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P)
      (H1Cotangent.map A B C C) := by
  -- Transport the exact pair through presentation-independence on the middle and right terms.
  have h₁₂ :
      tensor_presentation_cotangent_h1_to_h1_cotangent C P ∘ₗ
          (LinearEquiv.refl C (LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex))) =
        (Q.comp P).equivH1Cotangent ∘ₗ
          tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := by
    simpa using tensor_presentation_cotangent_h1_to_h1_cotangent_eq_of_generators
      (P := P) (Q := Q)
  have h₂₃ :
      H1Cotangent.map A B C C ∘ₗ (Q.comp P).equivH1Cotangent =
        Q.equivH1Cotangent ∘ₗ
          Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom := by
    simpa using h1Cotangent_map_eq_ofComp_on_comp (P := P) (Q := Q)
  exact Function.Exact.of_ladder_linearEquiv_of_exact h₁₂ h₂₃ hExact

/-- Helper for Lemma 15.33.6: injectivity for a chosen finite presentation `Q` transports through
the canonical comparison with `H₁(L_{C/A})`. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_injective_of_comp_injective
    (P : Generators A B ι) (Q : Generators B C κ)
    (hinj :
      Function.Injective
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)) :
    Function.Injective
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P) := by
  -- The owner map is the chosen-presentation map followed by a presentation-independence
  -- equivalence on `H₁(L_{C/A})`.
  rw [tensor_presentation_cotangent_h1_to_h1_cotangent_eq_of_generators (P := P) (Q := Q)]
  exact (Q.comp P).equivH1Cotangent.injective.comp hinj

/-- Helper for Lemma 15.33.6: once the conormal row is short exact, the induced map on source
cycles is exact against the map on `H₁` for the chosen presentation `Q`. -/
theorem tensor_presentation_cotangent_h1_to_comp_generators_h1_exact_of_conormal_shortExact
    (P : Generators A B ι) (Q : Generators B C κ)
    (hShort : (compPresentationConormalSequence P Q).ShortExact) :
    Function.Exact
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) := by
  -- Route correction: the source proof only needs the ambient exact conormal row plus
  -- injectivity on cotangent spaces. The short exactness hypothesis is therefore bookkeeping here.
  let _ := hShort
  intro y
  constructor
  · intro hy
    -- Forgetting from `H₁` to the ambient conormal module turns the vanishing hypothesis into the
    -- middle-row kernel condition needed for `Generators.Cotangent.exact`.
    have hy0 : Extension.Cotangent.map (Q.ofComp P).toExtensionHom y.1 = 0 := by
      exact congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (Generators.Cotangent.exact Q P y.1).1 hy0
    -- The ambient preimage is automatically a source cycle because the cotangent-complex square
    -- commutes and the induced map on cotangent spaces is injective.
    have hx_cycle : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) := by
      rw [LinearMap.mem_ker]
      apply (Generators.CotangentSpace.map_toComp_injective Q P)
      rw [← tensor_presentation_conormal_map_comp_cotangentComplex (P := P) (Q := Q) (x := x)]
      rw [hx]
      simpa [LinearMap.mem_ker] using y.2
    refine ⟨⟨x, hx_cycle⟩, ?_⟩
    -- Returning to the restricted map on cycles recovers the original `H₁` element.
    apply Subtype.ext
    change
      LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x = y.1
    exact hx
  · rintro ⟨x, rfl⟩
    -- Any cycle coming from the restricted source map lands in the kernel because the ambient
    -- conormal maps already compose to zero.
    apply Subtype.ext
    simpa [tensor_presentation_cotangent_h1_to_comp_generators_h1, LinearMap.comp_apply] using
      LinearMap.congr_fun (compPresentationConormalSequence_comp_eq_zero P Q) x.1

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
      (presentationJacobiZariskiLeftSequence C P).Exact := by
  have hinjAmbient :
      Function.Injective
        (LinearMap.liftBaseChange C
          (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) :=
    comp_presentation_left_conormal_injective_of_koszul_regular_kernel P Q hQ
  have hinjComp :
      Function.Injective
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q) :=
    tensor_presentation_cotangent_h1_to_comp_generators_h1_injective_of_conormal_injective
      P Q hinjAmbient
  have hinj :
      Function.Injective
        (tensor_presentation_cotangent_h1_to_h1_cotangent C P) :=
    tensor_presentation_cotangent_h1_to_h1_cotangent_injective_of_comp_injective
      (P := P) (Q := Q) hinjComp
  have hShort :
      (compPresentationConormalSequence P Q).ShortExact :=
    comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel P Q hQ
  have hExactComp :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
        (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) :=
    tensor_presentation_cotangent_h1_to_comp_generators_h1_exact_of_conormal_shortExact
      P Q hShort
  have hExactOwner :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_h1_cotangent C P)
        (H1Cotangent.map A B C C) :=
    tensor_presentation_cotangent_h1_to_h1_cotangent_exact_of_comp_exact
      (P := P) (Q := Q) hExactComp
  have hExact : (presentationJacobiZariskiLeftSequence C P).Exact := by
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
    have hExactαβ : Function.Exact α β := by
      -- Rewrite the packaged row back to the raw owner maps before applying exactness.
      let e₁ :
          LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) ≃ₗ[C]
            LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) :=
        LinearEquiv.refl C _
      let e₂ :
          ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C] H1Cotangent A C :=
        ULift.moduleEquiv
      let e₃ :
          ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C] H1Cotangent B C :=
        ULift.moduleEquiv
      have h₁₂ :
          α ∘ₗ e₁.symm.toLinearMap =
            e₂.symm.toLinearMap ∘ₗ tensor_presentation_cotangent_h1_to_h1_cotangent C P := by
        ext x
        rfl
      have h₂₃ :
          β ∘ₗ e₂.symm.toLinearMap =
            e₃.symm.toLinearMap ∘ₗ H1Cotangent.map A B C C := by
        ext x
        rfl
      exact Function.Exact.of_ladder_linearEquiv_of_exact h₁₂ h₂₃ hExactOwner
    -- The short complex exactness predicate is the function-level exactness of the packaged row.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    change Function.Exact α β
    exact hExactαβ
  exact ⟨hinj, hExact⟩

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
