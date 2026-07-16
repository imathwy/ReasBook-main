import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_119_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps:
- primary domain: determinant lines of finite projective modules and the canonical comparison map
  attached to a short exact sequence;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `shortComplexOfShortExact`,
  * `determinantLineMap`,
  * `CategoryTheory.ShortComplex.π₁.mapIso`,
  * `CategoryTheory.ShortComplex.π₂.mapIso`,
  * `CategoryTheory.ShortComplex.π₃.mapIso`;
- best owner abstraction: the canonical comparison map is the owner-level
  `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso` on a short exact `ShortComplex`;
  the presentation-to-`ShortComplex` bridge is `shortComplexOfShortExact`, and the linear-map
  naturality theorem below is therefore a `bridge/view`;
- primitive data: an isomorphism of short exact sequences;
- derived API: the determinant-line maps induced on the left, middle, and right terms and the
  resulting tensor-product comparison map.
-/

namespace CategoryTheory.ShortComplex

namespace ShortExact

section Naturality

variable {S T : ShortComplex (ModuleCat R)}
variable [Module.Finite R S.X₁] [Module.Projective R S.X₁]
variable [Module.Finite R S.X₂] [Module.Projective R S.X₂]
variable [Module.Finite R S.X₃] [Module.Projective R S.X₃]
variable [Module.Finite R T.X₁] [Module.Projective R T.X₁]
variable [Module.Finite R T.X₂] [Module.Projective R T.X₂]
variable [Module.Finite R T.X₃] [Module.Projective R T.X₃]

/-- Helper for Lemma 15.119.3: `TensorProduct.congr` sends a pure tensor to the pure tensor of the
transported factors. -/
theorem tensorproduct_congr_apply_tmul
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') (x : A) (y : B) :
    TensorProduct.congr e₁ e₂ (x ⊗ₜ[R] y) = e₁ x ⊗ₜ[R] e₂ y := by
  -- Proof comment: `TensorProduct.congr` is defined on pure tensors by applying each
  -- equivalence to its corresponding factor.
  rfl

/-- Helper for Lemma 15.119.3: transporting a pure tensor by linear equivalences and then by
their inverses recovers the original pure tensor. -/
theorem tensorproduct_congr_symm_apply_tmul
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') (x : A) (y : B) :
    TensorProduct.congr e₁.symm e₂.symm
      (TensorProduct.congr e₁ e₂ (x ⊗ₜ[R] y)) = x ⊗ₜ[R] y := by
  -- Proof comment: evaluate both `TensorProduct.congr` maps on the pure tensor and cancel the
  -- two inverse linear equivalences factorwise.
  rw [tensorproduct_congr_apply_tmul]
  rw [tensorproduct_congr_apply_tmul]
  simp

/-- Helper for Lemma 15.119.3: transporting a tensor product by inverse linear equivalences is the
inverse of transporting by the forward linear equivalences. -/
theorem tensorproduct_congr_symm_eq
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') :
    TensorProduct.congr e₁.symm e₂.symm = (TensorProduct.congr e₁ e₂).symm := by
  exact (TensorProduct.congr_symm e₁ e₂).symm

/-- Helper for Lemma 15.119.3: determinant-line maps respect composition of linear equivalences. -/
theorem determinantLineMap_trans
    {A B C : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    [AddCommGroup C] [Module R C] [Module.Finite R C] [Module.Projective R C]
    (e₁ : A ≃ₗ[R] B) (e₂ : B ≃ₗ[R] C) :
    determinantLineMap (e₁.trans e₂) = (determinantLineMap e₁).trans (determinantLineMap e₂) := by
  -- Proof comment: both determinant-line equivalences are induced by the same composite exterior
  -- algebra map, so they agree by extensionality on determinant-line elements.
  ext x
  change (ExteriorAlgebra.map (e₁.trans e₂).toLinearMap) x =
      ((determinantLineMap e₂) ((determinantLineMap e₁) x) : ExteriorAlgebra R C)
  rw [determinantLineMap_apply, determinantLineMap_apply]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rfl

/-- Helper for Lemma 15.119.3: the determinant-line map of the identity equivalence is the
identity on the determinant line. -/
theorem determinantLineMap_refl
    {A : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A] :
    determinantLineMap (LinearEquiv.refl R A) = LinearEquiv.refl R (Module.det R A) := by
  -- Proof comment: both equivalences are induced by the identity exterior-algebra map.
  ext x
  rw [determinantLineMap_apply]
  simp

/-- Helper for Lemma 15.119.3: a determinant-line map followed by the map of the inverse
equivalence is the identity. -/
theorem determinantLineMap_trans_symm
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) :
    (determinantLineMap e).trans (determinantLineMap e.symm) =
      LinearEquiv.refl R (Module.det R A) := by
  -- Proof comment: this is `determinantLineMap_trans` specialized to `e ≪≫ e.symm`.
  rw [← determinantLineMap_trans]
  simpa using (determinantLineMap_refl (R := R) (A := A))

/-- Helper for Lemma 15.119.3: the determinant-line map of the inverse equivalence followed by the
forward map is the identity. -/
theorem determinantLineMap_symm_trans
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) :
    (determinantLineMap e.symm).trans (determinantLineMap e) =
      LinearEquiv.refl R (Module.det R B) := by
  -- Proof comment: this is the same cancellation on the other side.
  rw [← determinantLineMap_trans]
  simpa using (determinantLineMap_refl (R := R) (A := B))

/-- Helper for Lemma 15.119.3: applying the determinant-line map of a linear equivalence and then
the map of its inverse recovers the original determinant-line element. -/
theorem determinantLineMap_apply_symm_apply
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) (x : Module.det R A) :
    determinantLineMap e.symm (determinantLineMap e x) = x := by
  -- Proof comment: evaluate the composite cancellation equality on the chosen determinant-line
  -- element.
  simpa [LinearEquiv.trans_apply] using
    congrArg (fun ψ : Module.det R A ≃ₗ[R] Module.det R A ↦ ψ x)
      (determinantLineMap_trans_symm (R := R) e)

/-- Helper for Lemma 15.119.3: applying the determinant-line map of the inverse equivalence and
then the forward map recovers the original determinant-line element. -/
theorem determinantLineMap_symm_apply_apply
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) (x : Module.det R B) :
    determinantLineMap e (determinantLineMap e.symm x) = x := by
  -- Proof comment: this is the same pointwise cancellation on the target determinant line.
  simpa [LinearEquiv.trans_apply] using
    congrArg (fun ψ : Module.det R B ≃ₗ[R] Module.det R B ↦ ψ x)
      (determinantLineMap_symm_trans (R := R) e)

/-- Helper for Lemma 15.119.3: the determinant-line map of the inverse linear equivalence is the
inverse of the determinant-line map. -/
theorem determinantLineMap_symm
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) :
    determinantLineMap e.symm = (determinantLineMap e).symm := by
  ext x
  simpa using
    (LinearEquiv.eq_symm_apply (determinantLineMap e)).2
      (determinantLineMap_symm_apply_apply (R := R) e x)

/-- Helper for Lemma 15.119.3: the forward determinant-line tensor transport followed by the
inverse transport is the identity on pure tensors. -/
theorem tensorproduct_congr_determinantLineMap_roundtrip_apply
    (e₁ : S.X₁ ≃ₗ[R] T.X₁) (e₃ : S.X₃ ≃ₗ[R] T.X₃)
    (x₁ : Module.det R S.X₁) (x₃ : Module.det R S.X₃) :
    TensorProduct.congr
      (determinantLineMap e₁.symm)
      (determinantLineMap e₃.symm)
      (TensorProduct.congr
        (determinantLineMap e₁)
        (determinantLineMap e₃)
        (x₁ ⊗ₜ[R] x₃)) =
      x₁ ⊗ₜ[R] x₃ := by
  -- Proof comment: this is the generic tensor roundtrip lemma applied to the determinant-line
  -- equivalences induced by `e₁` and `e₃`.
  exact tensorproduct_congr_symm_apply_tmul (R := R)
    (e₁ := determinantLineMap e₁)
    (e₂ := determinantLineMap e₃)
    (x := x₁) (y := x₃)

/-- Helper for Lemma 15.119.3: transport the right square of a short-complex isomorphism to the
exterior algebra on a chosen element. -/
theorem transport_g_square_apply
    (hS : S.ShortExact) (e : S ≅ T)
    (y₃ : ExteriorAlgebra R T.X₂) :
    ExteriorAlgebra.map S.g.hom
      (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃) =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (ExteriorAlgebra.map T.g.hom y₃) := by
  let _ := (inferInstance : Module.Finite R S.X₁)
  let _ := (inferInstance : Module.Projective R S.X₁)
  let _ := (inferInstance : Module.Finite R S.X₂)
  let _ := (inferInstance : Module.Projective R S.X₂)
  let _ := (inferInstance : Module.Finite R S.X₃)
  let _ := (inferInstance : Module.Projective R S.X₃)
  let _ := (inferInstance : Module.Finite R T.X₁)
  let _ := (inferInstance : Module.Projective R T.X₁)
  let _ := (inferInstance : Module.Finite R T.X₂)
  let _ := (inferInstance : Module.Projective R T.X₂)
  let _ := (inferInstance : Module.Finite R T.X₃)
  let _ := (inferInstance : Module.Projective R T.X₃)
  have _ := hS
  -- Proof comment: rewrite the inverse `g`-square of `e` as an equality of linear maps and then
  -- evaluate the induced exterior-algebra map on `y₃`.
  have hcomm :
      S.g.hom.comp (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) =
        (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.g.hom := by
    simpa using congrArg ModuleCat.Hom.hom e.inv.comm₂₃
  have hleft :
      ExteriorAlgebra.map S.g.hom
        (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃) =
      ExteriorAlgebra.map
        (S.g.hom.comp (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)) y₃ := by
    simpa using
      congrArg
        (fun ψ : ExteriorAlgebra R T.X₂ →ₐ[R] ExteriorAlgebra R S.X₃ ↦ ψ y₃)
        (ExteriorAlgebra.map_comp_map
          (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) S.g.hom)
  have hright :
      ExteriorAlgebra.map
        ((((π₃.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.g.hom) y₃ =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (ExteriorAlgebra.map T.g.hom y₃) := by
    simpa using
      congrArg
        (fun ψ : ExteriorAlgebra R T.X₂ →ₐ[R] ExteriorAlgebra R S.X₃ ↦ ψ y₃)
        (ExteriorAlgebra.map_comp_map
          T.g.hom (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)).symm
  -- Proof comment: evaluate the equality of composite linear maps on `y₃` and then rewrite both
  -- composite exterior-algebra maps into nested form.
  calc
    ExteriorAlgebra.map S.g.hom
        (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃) =
      ExteriorAlgebra.map
        (S.g.hom.comp (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)) y₃ := hleft
    _ =
      ExteriorAlgebra.map
        ((((π₃.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.g.hom) y₃ := by
        exact congrArg
          (fun φ : T.X₂ →ₗ[R] S.X₃ ↦ ExteriorAlgebra.map φ y₃)
          hcomm
    _ =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (ExteriorAlgebra.map T.g.hom y₃) := hright

/-- Helper for Lemma 15.119.3: transport the left wedge factor across the left square of a
short-complex isomorphism. -/
theorem transport_left_factor_apply
    (hS : S.ShortExact) (e : S ≅ T)
    (x₁ : Module.det R T.X₁) :
    ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
      (ExteriorAlgebra.map S.f.hom
        (ExteriorAlgebra.map (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap)
          (x₁ : ExteriorAlgebra R T.X₁))) =
      ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) := by
  let _ := (inferInstance : Module.Finite R S.X₁)
  let _ := (inferInstance : Module.Projective R S.X₁)
  let _ := (inferInstance : Module.Finite R S.X₂)
  let _ := (inferInstance : Module.Projective R S.X₂)
  let _ := (inferInstance : Module.Finite R S.X₃)
  let _ := (inferInstance : Module.Projective R S.X₃)
  let _ := (inferInstance : Module.Finite R T.X₁)
  let _ := (inferInstance : Module.Projective R T.X₁)
  let _ := (inferInstance : Module.Finite R T.X₂)
  let _ := (inferInstance : Module.Projective R T.X₂)
  let _ := (inferInstance : Module.Finite R T.X₃)
  let _ := (inferInstance : Module.Projective R T.X₃)
  have _ := hS
  -- Proof comment: rewrite the inverse `f`-square of `e`, then cancel the adjacent `π₂.mapIso`
  -- transport before applying `ExteriorAlgebra.map`.
  have hcomm :
      S.f.hom.comp (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap) =
        (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.f.hom := by
    simpa using congrArg ModuleCat.Hom.hom e.inv.comm₁₂
  have htransport :
      ExteriorAlgebra.map S.f.hom
        (ExteriorAlgebra.map (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap)
          (x₁ : ExteriorAlgebra R T.X₁)) =
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)
        (ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁)) := by
    -- Proof comment: as with the right square, evaluate the equality of composite linear maps on
    -- the chosen left determinant element and rewrite to nested exterior-algebra maps.
    have hleft :
        ExteriorAlgebra.map S.f.hom
          (ExteriorAlgebra.map (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap)
            (x₁ : ExteriorAlgebra R T.X₁)) =
        ExteriorAlgebra.map
          (S.f.hom.comp (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap))
          (x₁ : ExteriorAlgebra R T.X₁) := by
      simpa using
        congrArg
          (fun ψ : ExteriorAlgebra R T.X₁ →ₐ[R] ExteriorAlgebra R S.X₂ ↦
            ψ (x₁ : ExteriorAlgebra R T.X₁))
          (ExteriorAlgebra.map_comp_map
            (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap) S.f.hom)
    have hright :
        ExteriorAlgebra.map
          ((((π₂.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.f.hom)
          (x₁ : ExteriorAlgebra R T.X₁) =
        ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)
          (ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁)) := by
      simpa using
        congrArg
          (fun ψ : ExteriorAlgebra R T.X₁ →ₐ[R] ExteriorAlgebra R S.X₂ ↦
            ψ (x₁ : ExteriorAlgebra R T.X₁))
          (ExteriorAlgebra.map_comp_map
            T.f.hom (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)).symm
    calc
      ExteriorAlgebra.map S.f.hom
          (ExteriorAlgebra.map (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap)
            (x₁ : ExteriorAlgebra R T.X₁)) =
        ExteriorAlgebra.map
          (S.f.hom.comp (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap))
          (x₁ : ExteriorAlgebra R T.X₁) := hleft
      _ =
        ExteriorAlgebra.map
          ((((π₂.mapIso e).toLinearEquiv).symm.toLinearMap).comp T.f.hom)
          (x₁ : ExteriorAlgebra R T.X₁) := by
          exact congrArg
            (fun φ : T.X₁ →ₗ[R] S.X₂ ↦
              ExteriorAlgebra.map φ (x₁ : ExteriorAlgebra R T.X₁))
            hcomm
      _ =
        ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)
          (ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁)) := hright
  calc
    ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        (ExteriorAlgebra.map S.f.hom
          (ExteriorAlgebra.map (((π₁.mapIso e).toLinearEquiv).symm.toLinearMap)
            (x₁ : ExteriorAlgebra R T.X₁))) =
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap)
          (ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁))) := by
        rw [htransport]
    _ = ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) := by
        simpa using
          LinearMap.congr_fun
            (exteriorAlgebraLinearEquiv_right_inv (R := R) ((π₂.mapIso e).toLinearEquiv))
            (ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁))

/-- Helper for Lemma 15.119.3: pulling a lift of the right determinant factor back along a
short-complex isomorphism preserves the defining lift condition for the owner-level determinant
comparison map. -/
theorem transport_lift_condition_apply
    (hS : S.ShortExact) (e : S ≅ T)
    (x₃ : Module.det R T.X₃) (y₃ : ExteriorAlgebra R T.X₂)
    (hy₃ : ExteriorAlgebra.map T.g.hom y₃ = (x₃ : ExteriorAlgebra R T.X₃)) :
    ExteriorAlgebra.map S.g.hom
      (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃) =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (x₃ : ExteriorAlgebra R T.X₃) := by
  -- Proof comment: first move `y₃` across the inverse `g`-square, then rewrite by the chosen lift
  -- equation `hy₃`.
  calc
    ExteriorAlgebra.map S.g.hom
        (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃) =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (ExteriorAlgebra.map T.g.hom y₃) := by
        simpa using transport_g_square_apply (R := R) (hS := hS) (e := e) y₃
    _ =
      ExteriorAlgebra.map (((π₃.mapIso e).toLinearEquiv).symm.toLinearMap)
        (x₃ : ExteriorAlgebra R T.X₃) := by rw [hy₃]

/-- Helper for Lemma 15.119.3: transporting the owner-level determinant comparison map along a
short-complex isomorphism preserves the wedge characterization. -/
noncomputable abbrev transportedDeterminantTensorIso
    (hS : S.ShortExact) (e : S ≅ T) :
    Module.det R T.X₁ ⊗[R] Module.det R T.X₃ ≃ₗ[R] Module.det R T.X₂ :=
  (TensorProduct.congr
      (determinantLineMap (((π₁.mapIso e).toLinearEquiv).symm))
      (determinantLineMap (((π₃.mapIso e).toLinearEquiv).symm))).trans
    (hS.determinantTensorIso.trans
      (determinantLineMap ((π₂.mapIso e).toLinearEquiv)))

/-- Helper for Lemma 15.119.3: transporting the owner-level determinant comparison map along a
short-complex isomorphism preserves the wedge characterization. -/
theorem determinantTensorIso_transport_spec
    (hS : S.ShortExact) (e : S ≅ T)
    (x₁ : Module.det R T.X₁) (x₃ : Module.det R T.X₃) (y₃ : ExteriorAlgebra R T.X₂)
    (hy₃ : ExteriorAlgebra.map T.g.hom y₃ = (x₃ : ExteriorAlgebra R T.X₃)) :
    (((transportedDeterminantTensorIso (R := R) hS e).toLinearMap
        (x₁ ⊗ₜ[R] x₃) : Module.det R T.X₂) : ExteriorAlgebra R T.X₂) =
      ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) * y₃ := by
  let x₁S : Module.det R S.X₁ :=
    determinantLineMap (((π₁.mapIso e).toLinearEquiv).symm) x₁
  let x₃S : Module.det R S.X₃ :=
    determinantLineMap (((π₃.mapIso e).toLinearEquiv).symm) x₃
  let y₃S : ExteriorAlgebra R S.X₂ :=
    ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).symm.toLinearMap) y₃
  have hy₃S :
      ExteriorAlgebra.map S.g.hom y₃S = (x₃S : ExteriorAlgebra R S.X₃) := by
    simpa [x₃S, y₃S, determinantLineMap_apply] using
      transport_lift_condition_apply (R := R) (hS := hS) (e := e) x₃ y₃ hy₃
  have hspec :=
    determinantTensorIso_spec (R := R) (hS := hS) x₁S x₃S y₃S hy₃S
  have hspec' :
      ((hS.determinantTensorIso (x₁S ⊗ₜ[R] x₃S) :
          Module.det R S.X₂) : ExteriorAlgebra R S.X₂) =
        ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁) * y₃S := by
    simpa [x₁S, x₃S, y₃S, determinantLineMap_apply] using hspec
  have hy₃_roundtrip :
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        y₃S = y₃ := by
    simpa using
      LinearMap.congr_fun
        (exteriorAlgebraLinearEquiv_right_inv (R := R) ((π₂.mapIso e).toLinearEquiv))
        y₃
  have hpush_forward :
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        (ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁) * y₃S) =
      ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) * y₃ := by
    have hleft :
        ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
          (ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁)) =
        ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) := by
      simpa [x₁S, determinantLineMap_apply] using
        transport_left_factor_apply (R := R) (hS := hS) (e := e) x₁
    calc
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
          (ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁) * y₃S) =
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
          (ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁)) *
        ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap) y₃S := by
          exact (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)).map_mul _ _
      _ = ExteriorAlgebra.map T.f.hom (x₁ : ExteriorAlgebra R T.X₁) * y₃ := by
          exact congrArg₂ HMul.hMul hleft hy₃_roundtrip
  -- Proof comment: apply the source-row wedge formula after pulling the right lift back across
  -- the short-complex isomorphism, then push the resulting identity forward along `π₂.mapIso e`.
  have htransport :
      (((transportedDeterminantTensorIso (R := R) hS e).toLinearMap
            (x₁ ⊗ₜ[R] x₃) : Module.det R T.X₂) : ExteriorAlgebra R T.X₂) =
          ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
            ((hS.determinantTensorIso (x₁S ⊗ₜ[R] x₃S) : Module.det R S.X₂) :
              ExteriorAlgebra R S.X₂) := by
    rfl
  have hmapped_spec :
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        ((hS.determinantTensorIso (x₁S ⊗ₜ[R] x₃S) : Module.det R S.X₂) :
          ExteriorAlgebra R S.X₂) =
      ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)
        (ExteriorAlgebra.map S.f.hom (x₁S : ExteriorAlgebra R S.X₁) * y₃S) := by
    exact congrArg (ExteriorAlgebra.map (((π₂.mapIso e).toLinearEquiv).toLinearMap)) hspec'
  exact htransport.trans (hmapped_spec.trans hpush_forward)

/-- Helper for Lemma 15.119.3: the transported owner candidate is the canonical target
determinant comparison map by uniqueness. -/
theorem determinantTensorIso_transport_eq_owner
    (hS : S.ShortExact) (e : S ≅ T) :
    transportedDeterminantTensorIso (R := R) hS e =
      (shortExact_of_iso e hS).determinantTensorIso := by
  obtain ⟨_, huniq⟩ :=
    Classical.choose_spec (existsUnique_determinantTensorIso (shortExact_of_iso e hS))
  -- Proof comment: uniqueness for the target short exact sequence identifies the transported
  -- candidate with the canonical determinant comparison map once the wedge formula is verified.
  apply huniq
  intro x₁ x₃ y₃ hy₃
  exact determinantTensorIso_transport_spec
    (R := R) (hS := hS) (e := e) x₁ x₃ y₃ hy₃

/-- Core/canonical: an isomorphism of short exact sequences of finite projective `R`-modules
intertwines the owner-level determinant-line comparison maps. -/
theorem determinantTensorIso_naturality
    (hS : S.ShortExact) (e : S ≅ T) :
    CommSq
      (ModuleCat.ofHom <| hS.determinantTensorIso.toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
          (determinantLineMap ((π₃.mapIso e).toLinearEquiv))).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap ((π₂.mapIso e).toLinearEquiv)).toLinearMap)
      (ModuleCat.ofHom <| (shortExact_of_iso e hS).determinantTensorIso.toLinearMap) := by
  -- Proof comment: prove the commutative square on the underlying linear maps, then repackage it
  -- as a square in `ModuleCat`.
  refine CommSq.mk ?_
  have hlin :
      (determinantLineMap ((π₂.mapIso e).toLinearEquiv)).toLinearMap.comp
          hS.determinantTensorIso.toLinearMap =
        (shortExact_of_iso e hS).determinantTensorIso.toLinearMap.comp
          (TensorProduct.congr
            (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
            (determinantLineMap ((π₃.mapIso e).toLinearEquiv))).toLinearMap := by
    apply TensorProduct.ext'
    intro x₁ x₃
    -- Proof comment: after reducing the composed `ModuleCat` morphisms to their underlying
    -- linear maps on the pure tensor, the goal is exactly the transported-owner equality.
    change
      (determinantLineMap ((π₂.mapIso e).toLinearEquiv))
          (hS.determinantTensorIso (x₁ ⊗ₜ[R] x₃)) =
        (shortExact_of_iso e hS).determinantTensorIso
          ((TensorProduct.congr
            (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
            (determinantLineMap ((π₃.mapIso e).toLinearEquiv)))
            (x₁ ⊗ₜ[R] x₃))
    have htransport :=
      congrArg
        (fun ψ : Module.det R T.X₁ ⊗[R] Module.det R T.X₃ ≃ₗ[R] Module.det R T.X₂ ↦
          ψ (TensorProduct.congr
            (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
            (determinantLineMap ((π₃.mapIso e).toLinearEquiv))
            (x₁ ⊗ₜ[R] x₃)))
        (determinantTensorIso_transport_eq_owner (R := R) (hS := hS) (e := e))
    have hroundtrip :
        transportedDeterminantTensorIso (R := R) hS e
          ((TensorProduct.congr
            (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
            (determinantLineMap ((π₃.mapIso e).toLinearEquiv)))
            (x₁ ⊗ₜ[R] x₃)) =
          (determinantLineMap ((π₂.mapIso e).toLinearEquiv))
            (hS.determinantTensorIso (x₁ ⊗ₜ[R] x₃)) := by
      -- Proof comment: unfold the transported map and cancel the forward-then-backward tensor
      -- transport on the domain.
      exact congrArg
        (fun z : Module.det R S.X₁ ⊗[R] Module.det R S.X₃ ↦
          (determinantLineMap ((π₂.mapIso e).toLinearEquiv))
            (hS.determinantTensorIso z))
        (tensorproduct_congr_determinantLineMap_roundtrip_apply
          (R := R)
          (S := S)
          (T := T)
          ((π₁.mapIso e).toLinearEquiv)
          ((π₃.mapIso e).toLinearEquiv)
          x₁
          x₃)
    exact hroundtrip.symm.trans htransport
  exact congrArg ModuleCat.ofHom hlin

end Naturality
end ShortExact
end CategoryTheory.ShortComplex

section Naturality

variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M'' : Type v} [AddCommGroup M''] [Module R M'']
variable {K' : Type v} [AddCommGroup K'] [Module R K']
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {K'' : Type v} [AddCommGroup K''] [Module R K'']

private theorem injective_of_commSq
    {f : M' →ₗ[R] M} {fK : K' →ₗ[R] K}
    (hf : Function.Injective f) (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap) :
    Function.Injective fK := by
  intro x y hxy
  have hx : v (f (u.symm x)) = fK x := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm x)) huv
  have hy : v (f (u.symm y)) = fK y := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm y)) huv
  have hxy' : u.symm x = u.symm y := hf <| v.injective <| hx.trans (hxy.trans hy.symm)
  exact u.symm.injective hxy'

private theorem surjective_of_commSq
    {g : M →ₗ[R] M''} {gK : K →ₗ[R] K''}
    (hg : Function.Surjective g) (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Surjective gK := by
  intro z
  obtain ⟨y, hy⟩ := hg (w.symm z)
  refine ⟨v y, ?_⟩
  have hy' : w (g y) = gK (v y) := by
    simpa using congrArg (fun φ : M →ₗ[R] K'' ↦ φ y) hvw
  calc
    gK (v y) = w (g y) := by simpa using hy'.symm
    _ = z := by simpa [hy]

private theorem exact_of_commSq
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Exact fK gK := by
  exact Function.Exact.of_ladder_linearEquiv_of_exact huv.symm hvw.symm hexact

variable [Module.Finite R M'] [Module.Projective R M']
variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R M''] [Module.Projective R M'']
variable [Module.Finite R K'] [Module.Projective R K']
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R K''] [Module.Projective R K'']

/-- Helper for Lemma 15.119.3: a linear equivalence induces the corresponding equivalence between
the universe-lifted module presentations used in `shortComplexOfShortExact`. -/
private abbrev uliftLinearEquiv
    {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) :
    ULift.{v, v} A ≃ₗ[R] ULift.{v, v} B :=
  (ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A).trans
    (e.trans (ULift.moduleEquiv : ULift.{v, v} B ≃ₗ[R] B).symm)

/-- Helper for Lemma 15.119.3: the left square of the `ULift`-transported ladder commutes. -/
private theorem shortComplexOfShortExact_iso_of_ladder_comm₁₂
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g) (hexactK : Function.Exact fK gK)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (_hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    (uliftLinearEquiv (R := R) u).toModuleIso.hom ≫
        (shortComplexOfShortExact fK gK hexactK).f =
      (shortComplexOfShortExact f g hexact).f ≫
        (uliftLinearEquiv (R := R) v).toModuleIso.hom := by
  let _ := (inferInstance : Module.Finite R M')
  let _ := (inferInstance : Module.Projective R M')
  let _ := (inferInstance : Module.Finite R M)
  let _ := (inferInstance : Module.Projective R M)
  let _ := (inferInstance : Module.Finite R M'')
  let _ := (inferInstance : Module.Projective R M'')
  let _ := (inferInstance : Module.Finite R K')
  let _ := (inferInstance : Module.Projective R K')
  let _ := (inferInstance : Module.Finite R K)
  let _ := (inferInstance : Module.Projective R K)
  let _ := (inferInstance : Module.Finite R K'')
  let _ := (inferInstance : Module.Projective R K'')
  -- Proof comment: this is the transported equality `fK ∘ u = v ∘ f` written on `ULift`.
  ext x
  change ULift.up (fK (u x.down)) = ULift.up (v (f x.down))
  apply ULift.ext
  exact (congrArg (fun φ : M' →ₗ[R] K ↦ φ x.down) huv).symm

/-- Helper for Lemma 15.119.3: the right square of the `ULift`-transported ladder commutes. -/
private theorem shortComplexOfShortExact_iso_of_ladder_comm₂₃
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g) (hexactK : Function.Exact fK gK)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (_huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    (uliftLinearEquiv (R := R) v).toModuleIso.hom ≫
        (shortComplexOfShortExact fK gK hexactK).g =
      (shortComplexOfShortExact f g hexact).g ≫
        (uliftLinearEquiv (R := R) w).toModuleIso.hom := by
  let _ := (inferInstance : Module.Finite R M')
  let _ := (inferInstance : Module.Projective R M')
  let _ := (inferInstance : Module.Finite R M)
  let _ := (inferInstance : Module.Projective R M)
  let _ := (inferInstance : Module.Finite R M'')
  let _ := (inferInstance : Module.Projective R M'')
  let _ := (inferInstance : Module.Finite R K')
  let _ := (inferInstance : Module.Projective R K')
  let _ := (inferInstance : Module.Finite R K)
  let _ := (inferInstance : Module.Projective R K)
  let _ := (inferInstance : Module.Finite R K'')
  let _ := (inferInstance : Module.Projective R K'')
  -- Proof comment: this is the transported equality `gK ∘ v = w ∘ g` written on `ULift`.
  ext x
  change ULift.up (gK (v x.down)) = ULift.up (w (g x.down))
  apply ULift.ext
  exact (congrArg (fun φ : M →ₗ[R] K'' ↦ φ x.down) hvw).symm

/-- Helper for Lemma 15.119.3: a commutative ladder between presented short exact rows induces an
isomorphism between the associated short complexes. -/
private noncomputable abbrev shortComplexOfShortExact_iso_of_ladder
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g) (hexactK : Function.Exact fK gK)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    shortComplexOfShortExact f g hexact ≅ shortComplexOfShortExact fK gK hexactK :=
  ShortComplex.isoMk
    (uliftLinearEquiv (R := R) u).toModuleIso
    (uliftLinearEquiv (R := R) v).toModuleIso
    (uliftLinearEquiv (R := R) w).toModuleIso
    (shortComplexOfShortExact_iso_of_ladder_comm₁₂
      (R := R) (hexact := hexact) (hexactK := hexactK) u v w huv hvw)
    (shortComplexOfShortExact_iso_of_ladder_comm₂₃
      (R := R) (hexact := hexact) (hexactK := hexactK) u v w huv hvw)

/-- Helper for Lemma 15.119.3: the determinant-line map of `uliftLinearEquiv` is the expected
two-sided `ULift` bridge around the determinant-line map of the original equivalence. -/
private theorem determinantLineMap_uliftLinearEquiv
    {A B : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₗ[R] B) :
    determinantLineMap (uliftLinearEquiv (R := R) e) =
      (determinantLineMap (ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A)).trans
        ((determinantLineMap e).trans
          (determinantLineMap (ULift.moduleEquiv : ULift.{v, v} B ≃ₗ[R] B).symm)) := by
  -- Proof comment: `uliftLinearEquiv` is literally the composite `ULift ≃ A ≃ B ≃ ULift`.
  let _ : Module.Projective R (ULift.{v, v} A) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A).symm)
  let _ : Module.Projective R (ULift.{v, v} B) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} B ≃ₗ[R] B).symm)
  rw [uliftLinearEquiv]
  rw [CategoryTheory.ShortComplex.ShortExact.determinantLineMap_trans]
  rw [CategoryTheory.ShortComplex.ShortExact.determinantLineMap_trans]

/-- Helper for Lemma 15.119.3: the determinant-line maps induced by `ULift.moduleEquiv` and its
inverse cancel pointwise on determinant-line elements. -/
private theorem determinantLineMap_ulift_roundtrip_apply
    {A : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    (x : Module.det R A) :
    determinantLineMap (ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A)
      (determinantLineMap (ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A).symm x) = x := by
  let _ : Module.Projective R (ULift.{v, v} A) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A).symm)
  -- Proof comment: specialize the generic determinant-line cancellation lemma to the `ULift`
  -- equivalence.
  simpa using
    CategoryTheory.ShortComplex.ShortExact.determinantLineMap_symm_apply_apply
      (R := R) (e := (ULift.moduleEquiv : ULift.{v, v} A ≃ₗ[R] A)) x

/-- Helper for Lemma 15.119.3: the tensor-domain `ULift` bridge converts the owner vertical map
into the source-facing vertical map. -/
private theorem determinantTensorIsoOfShortExact_ulift_domain_pure_tensor
    (u : M' ≃ₗ[R] K') (w : M'' ≃ₗ[R] K'')
    (x : Module.det R M') (y : Module.det R M'') :
    ((((TensorProduct.congr
        (determinantLineMap (uliftLinearEquiv (R := R) u))
        (determinantLineMap (uliftLinearEquiv (R := R) w))).toLinearMap).comp
        ((TensorProduct.congr
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} M' ≃ₗ[R] M').symm)
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} M'' ≃ₗ[R] M'').symm)).toLinearMap))
      (x ⊗ₜ[R] y) =
      (((TensorProduct.congr
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} K' ≃ₗ[R] K').symm)
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} K'' ≃ₗ[R] K'').symm)).toLinearMap).comp
          ((TensorProduct.congr
            (determinantLineMap u)
            (determinantLineMap w)).toLinearMap))
        (x ⊗ₜ[R] y)) := by
  let _ : Module.Projective R (ULift.{v, v} M') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M' ≃ₗ[R] M').symm)
  let _ : Module.Projective R (ULift.{v, v} M'') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M'' ≃ₗ[R] M'').symm)
  let _ : Module.Projective R (ULift.{v, v} K') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K' ≃ₗ[R] K').symm)
  let _ : Module.Projective R (ULift.{v, v} K'') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K'' ≃ₗ[R] K'').symm)
  -- Proof comment: unfold the two `ULift` determinant transports on the pure tensor and cancel
  -- the adjacent `ULift.moduleEquiv` round trips factorwise.
  simp [LinearMap.comp_apply, LinearEquiv.trans_apply,
    determinantLineMap_uliftLinearEquiv, determinantLineMap_ulift_roundtrip_apply]

/-- Helper for Lemma 15.119.3: the tensor-domain `ULift` bridge converts the owner vertical map
into the source-facing vertical map. -/
private theorem determinantTensorIsoOfShortExact_ulift_domain_comm
    (u : M' ≃ₗ[R] K') (w : M'' ≃ₗ[R] K'') :
    CommSq
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} M' ≃ₗ[R] M').symm)
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} M'' ≃ₗ[R] M'').symm)).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr (determinantLineMap u) (determinantLineMap w)).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap (uliftLinearEquiv (R := R) u))
          (determinantLineMap (uliftLinearEquiv (R := R) w))).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} K' ≃ₗ[R] K').symm)
          (determinantLineMap
            (ULift.moduleEquiv : ULift.{v, v} K'' ≃ₗ[R] K'').symm)).toLinearMap) := by
  let _ : Module.Projective R (ULift.{v, v} M') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M' ≃ₗ[R] M').symm)
  let _ : Module.Projective R (ULift.{v, v} M'') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M'' ≃ₗ[R] M'').symm)
  let _ : Module.Projective R (ULift.{v, v} K') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K' ≃ₗ[R] K').symm)
  let _ : Module.Projective R (ULift.{v, v} K'') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K'' ≃ₗ[R] K'').symm)
  -- Proof comment: the pure-tensor normalization extends to all tensors by one induction on the
  -- tensor product.
  refine CommSq.mk ?_
  ext x y
  simpa [LinearMap.comp_apply] using
    determinantTensorIsoOfShortExact_ulift_domain_pure_tensor
      (R := R) (u := u) (w := w) x y

/-- Helper for Lemma 15.119.3: the middle-term `ULift` bridge converts the owner vertical map
into the source-facing determinant-line map. -/
private theorem determinantTensorIsoOfShortExact_ulift_codomain_comm
    (v : M ≃ₗ[R] K) :
    CommSq
      (ModuleCat.ofHom <|
        (determinantLineMap (ULift.moduleEquiv : ULift.{v, v} M ≃ₗ[R] M)).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap (uliftLinearEquiv (R := R) v)).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap v).toLinearMap)
      (ModuleCat.ofHom <|
        (determinantLineMap (ULift.moduleEquiv : ULift.{v, v} K ≃ₗ[R] K)).toLinearMap) := by
  let _ : Module.Projective R (ULift.{v, v} M) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M ≃ₗ[R] M).symm)
  let _ : Module.Projective R (ULift.{v, v} K) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K ≃ₗ[R] K).symm)
  -- Proof comment: after expanding `determinantLineMap (uliftLinearEquiv v)`, the adjacent
  -- `ULift.moduleEquiv` determinant transports cancel pointwise.
  refine CommSq.mk ?_
  ext x
  simp [LinearEquiv.trans_apply, determinantLineMap_uliftLinearEquiv,
    determinantLineMap_ulift_roundtrip_apply]

/-- Lemma 15.119.3: an isomorphism of presented short exact sequences of finite projective
`R`-modules intertwines the determinant-line comparison maps from Lemma `15.119.2`. The target-row
injectivity, surjectivity, and exactness hypotheses are derived internally by transport along the
given linear equivalences, and the underlying owner-level comparison is still the short-complex
determinant isomorphism `determinantTensorIso`. -/
@[stacks 0FJC]
theorem determinantTensorIsoOfShortExact_naturality
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (fK : K' →ₗ[R] K) (gK : K →ₗ[R] K'') (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    let hfK : Function.Injective fK := injective_of_commSq hf u v huv
    let hgK : Function.Surjective gK := surjective_of_commSq hg v w hvw
    let hexactK : Function.Exact fK gK := exact_of_commSq hexact u v w huv hvw
    CommSq
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact f g hf hg hexact).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr (determinantLineMap u) (determinantLineMap w)).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap v).toLinearMap)
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact fK gK hfK hgK hexactK).toLinearMap) :=
  by
  -- Proof comment: after transporting the two rows to short complexes, the result is exactly the
  -- owner-level naturality square rewritten through the `ULift` bridge from Lemma 15.119.2.
  dsimp
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₁ := by
    change Module.Finite R (ULift.{v, v} M')
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₂ := by
    change Module.Finite R (ULift.{v, v} M)
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₃ := by
    change Module.Finite R (ULift.{v, v} M'')
    infer_instance
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₁ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M' ≃ₗ[R] M').symm)
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₂ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M ≃ₗ[R] M).symm)
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₃ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} M'' ≃ₗ[R] M'').symm)
  let _ : Module.Finite R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₁ := by
    change Module.Finite R (ULift.{v, v} K')
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₂ := by
    change Module.Finite R (ULift.{v, v} K)
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₃ := by
    change Module.Finite R (ULift.{v, v} K'')
    infer_instance
  let _ : Module.Projective R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₁ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K' ≃ₗ[R] K').symm)
  let _ : Module.Projective R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₂ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K ≃ₗ[R] K).symm)
  let _ : Module.Projective R (shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw)).X₃ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{v, v} K'' ≃ₗ[R] K'').symm)
  let eSc :
      shortComplexOfShortExact f g hexact ≅
        shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw) :=
    shortComplexOfShortExact_iso_of_ladder
      (R := R) (hexact := hexact) (hexactK := exact_of_commSq hexact u v w huv hvw)
      u v w huv hvw
  have hNat :=
    CategoryTheory.ShortComplex.ShortExact.determinantTensorIso_naturality
      (R := R)
      (S := shortComplexOfShortExact f g hexact)
      (T := shortComplexOfShortExact fK gK (exact_of_commSq hexact u v w huv hvw))
      (shortComplexOfShortExact_shortExact f g hf hg hexact)
      eSc
  have hShortExact :
      ShortComplex.shortExact_of_iso eSc (shortComplexOfShortExact_shortExact f g hf hg hexact) =
        shortComplexOfShortExact_shortExact fK gK
          (injective_of_commSq hf u v huv)
          (surjective_of_commSq hg v w hvw)
          (exact_of_commSq hexact u v w huv hvw) := by
    -- Proof comment: short exactness on a fixed short complex is a proposition.
    apply Subsingleton.elim
  let hDomain :=
    determinantTensorIsoOfShortExact_ulift_domain_comm (R := R) (u := u) (w := w)
  let hCodomain :=
    determinantTensorIsoOfShortExact_ulift_codomain_comm (R := R) (v := v)
  -- Proof comment: the displayed map on each row is exactly the horizontal composite of the
  -- source `ULift` bridge, the owner naturality square, and the target `ULift` bridge.
  simpa only [determinantTensorIsoOfShortExact, hShortExact] using
    CommSq.horiz_comp (CommSq.horiz_comp hDomain hNat) hCodomain

end Naturality
