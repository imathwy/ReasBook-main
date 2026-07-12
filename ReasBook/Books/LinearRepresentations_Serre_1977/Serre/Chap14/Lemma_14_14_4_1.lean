import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.TensorProduct.Basis

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra TensorProduct BigOperators

universe u v w

noncomputable section

variable {Λ : Type u} [CommRing Λ]
variable {G : Type v} [Group G] [Fintype G]
variable {P : Type w} [AddCommGroup P] [Module Λ P] [Module Λ[G] P]
variable [IsScalarTower Λ Λ[G] P]

/-
Domain-style sampling:
* Primary domain: projectivity of modules over the finite group algebra `Λ[G]`.
* Core/canonical owners: `Module.Projective` for projectivity, `Module.End Λ P` for
  endomorphisms of the underlying `Λ`-module, and mathlib's `LinearMap.sumOfConjugates` for the
  Maschke averaging operator.
* Source-facing layer: the present lemma, which packages the textbook criterion as a projectivity
  equivalence for a `Λ[G]`-module.
* Bridge/view layer: restriction of scalars from `Λ[G]` to `Λ` and the averaging operator on
  underlying `Λ`-linear endomorphisms.
-/

/-- Helper for Lemma 14-14.4-1: the group-algebra action commutes with scalars from `Λ`. -/
lemma action_right_smul (c : Λ) (a : Λ[G]) (x : P) : a • (c • x) = c • (a • x) := by
  -- The coefficient-ring action is central inside the group algebra.
  rw [smul_comm c a x]

/-- Helper for Lemma 14-14.4-1: the canonical bilinear action map
`Λ[G] × P → P`. -/
noncomputable def groupAlgebra_action_bilinear : Λ[G] →ₗ[Λ[G]] P →ₗ[Λ] P :=
  LinearMap.mk₂' (R := Λ[G]) (S := Λ) (fun a x => a • x)
    (fun a b x => add_smul a b x)
    (fun a b x => mul_smul a b x)
    (fun a x y => smul_add a x y)
    action_right_smul

/-- Helper for Lemma 14-14.4-1: the canonical `Λ[G]`-linear map
`Λ[G] ⊗[Λ] P → P` induced by the module action. -/
noncomputable def groupAlgebra_tensor_action : Λ[G] ⊗[Λ] P →ₗ[Λ[G]] P :=
  TensorProduct.AlgebraTensorModule.lift groupAlgebra_action_bilinear

/-- Helper for Lemma 14-14.4-1: the induced-module action map is surjective. -/
lemma groupAlgebra_tensor_action_surjective :
    Function.Surjective (groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)) := by
  -- The simple tensor `1 ⊗ x` maps back to `x`.
  intro x
  refine ⟨(1 : Λ[G]) ⊗ₜ[Λ] x, ?_⟩
  simp [groupAlgebra_tensor_action, groupAlgebra_action_bilinear]

/-- Helper for Lemma 14-14.4-1: the seed map `x ↦ 1 ⊗ u x`. -/
noncomputable def groupAlgebra_seed (u : Module.End Λ P) : P →ₗ[Λ] Λ[G] ⊗[Λ] P :=
  (TensorProduct.mk Λ (Λ[G]) P (1 : Λ[G])).comp u

/-- Helper for Lemma 14-14.4-1: applying the canonical action map to the seed recovers `u`. -/
lemma tensor_action_comp_seed_endomorphism (u : Module.End Λ P) :
    ((groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)).restrictScalars Λ).comp
      (groupAlgebra_seed (Λ := Λ) (G := G) (P := P) u) = u := by
  -- Evaluate on `1 ⊗ u x` and use the defining tensor-action formula.
  ext x
  simp [groupAlgebra_seed, groupAlgebra_tensor_action, groupAlgebra_action_bilinear]

/-- Helper for Lemma 14-14.4-1: an equivariant map commutes with summing conjugates. -/
lemma equivariant_comp_sumOfConjugates {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module Λ[G] Q]
    [IsScalarTower Λ Λ[G] Q] (f : Q →ₗ[Λ[G]] P) (π : P →ₗ[Λ] Q) :
    ((f.restrictScalars Λ).comp π).sumOfConjugates G =
      (f.restrictScalars Λ).comp (π.sumOfConjugates G) := by
  -- Expand both conjugation sums pointwise and use equivariance of `f`.
  ext x
  simp [LinearMap.sumOfConjugates_apply, LinearMap.conjugate_apply]

/-- Helper for Lemma 14-14.4-1: an endomorphism whose averaged conjugates are the identity
produces an equivariant section of `Λ[G] ⊗[Λ] P → P`. -/
lemma averaging_endomorphism_yields_section (u : Module.End Λ P)
    (hu : u.sumOfConjugates G = LinearMap.id) :
    ∃ v : P →ₗ[Λ[G]] Λ[G] ⊗[Λ] P,
      (groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)).comp v = LinearMap.id := by
  -- Average the seed map and then push the action map through the sum of conjugates.
  refine ⟨(groupAlgebra_seed (Λ := Λ) (G := G) (P := P) u).sumOfConjugatesEquivariant G, ?_⟩
  apply LinearMap.restrictScalars_injective Λ
  rw [LinearMap.restrictScalars_comp, LinearMap.restrictScalars_id,
    show
        ((LinearMap.sumOfConjugatesEquivariant G
            (groupAlgebra_seed (Λ := Λ) (G := G) (P := P) u)).restrictScalars Λ) =
          (groupAlgebra_seed (Λ := Λ) (G := G) (P := P) u).sumOfConjugates G by
      rfl,
    ← equivariant_comp_sumOfConjugates (G := G)
      (f := groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P))
      (π := groupAlgebra_seed (Λ := Λ) (G := G) (P := P) u)]
  -- The remaining composition is exactly the seed-action endomorphism, hence equal to `u`.
  have hseed := tensor_action_comp_seed_endomorphism (Λ := Λ) (G := G) (P := P) u
  simpa [hseed] using hu

/-- Helper for Lemma 14-14.4-1: restricting scalars carries a projective `Λ[G]`-module to a
projective `Λ`-module because `Λ[G]` is `Λ`-free. -/
lemma projective_restrictScalars_of_projective_groupAlgebra
    (hP : Module.Projective Λ[G] P) : Module.Projective Λ P := by
  -- Split `P` off a free `Λ[G]`-module and then restrict that splitting to `Λ`.
  obtain ⟨M, _instAddCommGroup, _instModule, _instFree, i, s, hs⟩ :=
    Module.Projective.iff_split.mp hP
  let _ : Module Λ M := Module.compHom M (algebraMap Λ Λ[G])
  let _ : IsScalarTower Λ Λ[G] M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Module.Free Λ M :=
    Module.Free.of_basis
      ((MonoidAlgebra.basis G Λ).smulTower (Module.Free.chooseBasis (Λ[G]) M))
  exact Module.Projective.of_split (i.restrictScalars Λ) (s.restrictScalars Λ) <| by
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Lemma 14-14.4-1: the coefficients of `Λ[G] ⊗[Λ] P` along the standard basis of
`Λ[G]`. -/
noncomputable def tensor_left_coeffs [DecidableEq G] : Λ[G] ⊗[Λ] P →ₗ[Λ] G →₀ P :=
  (TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis G Λ)).toLinearMap

/-- Helper for Lemma 14-14.4-1: the coefficient of `1 ∈ G` in the left tensor factor. -/
noncomputable def tensor_left_coeffOne [DecidableEq G] : Λ[G] ⊗[Λ] P →ₗ[Λ] P :=
  (Finsupp.lapply (1 : G)).comp tensor_left_coeffs

/-- Helper for Lemma 14-14.4-1: the coefficient of a pure tensor is the expected scalar multiple
of the right factor. -/
lemma coeff_tmul [DecidableEq G] (a : Λ[G]) (x : P) (g : G) :
    tensor_left_coeffs (Λ := Λ) (G := G) (P := P) (a ⊗ₜ[Λ] x) g = a g • x := by
  -- Rewrite the tensor in the basis expansion of the left factor.
  have h' :
      tensor_left_coeffs (Λ := Λ) (G := G) (P := P) (a ⊗ₜ[Λ] x) g =
        ((MonoidAlgebra.basis G Λ).repr a) g • x := by
    simpa [tensor_left_coeffs] using
      (TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
        (ℬ := MonoidAlgebra.basis G Λ) (m := a) (n := x) (i := g))
  simpa using h'

/-- Helper for Lemma 14-14.4-1: the action map evaluates a tensor by summing its basis
coefficients against the group action. -/
lemma groupAlgebra_tensor_action_apply_eq_sum_coeffs [DecidableEq G] (y : Λ[G] ⊗[Λ] P) :
    groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P) y =
      ∑ g : G,
        MonoidAlgebra.single g (1 : Λ) •
          tensor_left_coeffs (Λ := Λ) (G := G) (P := P) y g := by
  -- Expand `y` in the standard basis of `Λ[G]` and evaluate on each basis tensor.
  have hy := congrArg (groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P))
    ((TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis G Λ)).symm_apply_apply y)
  rw [show (TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis G Λ)) y =
      tensor_left_coeffs (Λ := Λ) (G := G) (P := P) y by
    rfl] at hy
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at hy
  symm at hy
  rw [hy]
  rw [map_finsuppSum]
  rw [Finsupp.sum_fintype (tensor_left_coeffs (Λ := Λ) (G := G) (P := P) y)
    (fun g x =>
      groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)
        ((MonoidAlgebra.basis G Λ) g ⊗ₜ[Λ] x))
    (fun _ => by simp)]
  simp [groupAlgebra_tensor_action, groupAlgebra_action_bilinear, MonoidAlgebra.basis_apply]

/-- Helper for Lemma 14-14.4-1: multiplying the left tensor factor by `g⁻¹` shifts the coefficient
at `1` to the coefficient at `g`. -/
lemma tensor_left_coeffs_smul_apply_one [DecidableEq G] (g : G) (y : Λ[G] ⊗[Λ] P) :
    tensor_left_coeffs (Λ := Λ) (G := G) (P := P)
        (MonoidAlgebra.single g⁻¹ (1 : Λ) • y) 1 =
      tensor_left_coeffs (Λ := Λ) (G := G) (P := P) y g := by
  -- Reduce to pure tensors and compute with `single_mul_apply`.
  induction y using TensorProduct.induction_on with
  | zero => simp [tensor_left_coeffs]
  | tmul a x =>
      rw [show MonoidAlgebra.single g⁻¹ (1 : Λ) • (a ⊗ₜ[Λ] x) =
          (MonoidAlgebra.single g⁻¹ (1 : Λ) * a) ⊗ₜ[Λ] x by
        rfl]
      rw [coeff_tmul, coeff_tmul]
      simp [MonoidAlgebra.single_mul_apply]
  | add y z hy hz => simp [hy, hz]

/-- Helper for Lemma 14-14.4-1: an equivariant map is determined by its coefficient at `1`. -/
lemma tensor_left_coeff_apply_of_equivariant [DecidableEq G]
    (v : P →ₗ[Λ[G]] Λ[G] ⊗[Λ] P) (x : P) (g : G) :
    tensor_left_coeffs (Λ := Λ) (G := G) (P := P) (v x) g =
      tensor_left_coeffOne (Λ := Λ) (G := G) (P := P)
        (v (MonoidAlgebra.single g⁻¹ (1 : Λ) • x)) := by
  -- Equivariance converts the `g`-coefficient of `v x` into the `1`-coefficient after shifting by
  -- `g⁻¹`.
  rw [tensor_left_coeffOne]
  rw [show v (MonoidAlgebra.single g⁻¹ (1 : Λ) • x) =
      MonoidAlgebra.single g⁻¹ (1 : Λ) • v x by
    simp]
  exact
    (tensor_left_coeffs_smul_apply_one
      (Λ := Λ) (G := G) (P := P) (g := g) (y := v x)).symm

/-- Helper for Lemma 14-14.4-1: the textbook averaging formula is the same as mathlib's
`sumOfConjugates`. -/
lemma textbook_average_eq_sumOfConjugates [DecidableEq G] (u : Module.End Λ P) (x : P) :
    (∑ g : G, MonoidAlgebra.single g (1 : Λ) •
        u (MonoidAlgebra.single g⁻¹ (1 : Λ) • x)) =
      u.sumOfConjugates G x := by
  -- Reindex the conjugation sum by inversion to match the textbook formula.
  rw [LinearMap.sumOfConjugates_apply]
  symm
  refine Fintype.sum_bijective (fun g : G => g⁻¹) inv_bijective
    (fun g => u.conjugate g x)
    (fun g =>
      MonoidAlgebra.single g (1 : Λ) • u (MonoidAlgebra.single g⁻¹ (1 : Λ) • x)) ?_
  intro g
  simp [LinearMap.conjugate_apply]

/-- Helper for Lemma 14-14.4-1: for an equivariant section `v`, composing with the action map
gives the averaged endomorphism extracted from the coefficient at `1`. -/
lemma tensor_action_comp_equivariant_eq_sumOfConjugates [DecidableEq G]
    (v : P →ₗ[Λ[G]] Λ[G] ⊗[Λ] P) :
    let u : Module.End Λ P :=
      tensor_left_coeffOne (Λ := Λ) (G := G) (P := P).comp (v.restrictScalars Λ)
    ((groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)).restrictScalars Λ).comp
      (v.restrictScalars Λ) = u.sumOfConjugates G := by
  -- First rewrite the action map as a coefficient sum, then identify those coefficients through
  -- equivariance with the extracted endomorphism.
  ext x
  let u : Module.End Λ P :=
    tensor_left_coeffOne (Λ := Λ) (G := G) (P := P).comp (v.restrictScalars Λ)
  change
    groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P) (v x) =
      u.sumOfConjugates G x
  rw [groupAlgebra_tensor_action_apply_eq_sum_coeffs]
  calc
    ∑ g : G,
        MonoidAlgebra.single g (1 : Λ) •
          tensor_left_coeffs (Λ := Λ) (G := G) (P := P) (v x) g
      = ∑ g : G,
          MonoidAlgebra.single g (1 : Λ) •
            u (MonoidAlgebra.single g⁻¹ (1 : Λ) • x) := by
          simp [u, tensor_left_coeff_apply_of_equivariant]
    _ = u.sumOfConjugates G x := textbook_average_eq_sumOfConjugates (u := u) (x := x)

-- Proof sketch: for the forward direction, restrict scalars from `Λ[G]` to `Λ` and use the usual
-- splitting characterization of projective modules. For the reverse direction, compare `P` with
-- the induced module `Λ[G] ⊗[Λ] P`; a `Λ`-linear endomorphism satisfying the displayed averaging
-- identity provides a `Λ[G]`-linear splitting of the canonical surjection onto `P`.
/-- Lemma 14-14.4-1: a `Λ[G]`-module `P` is projective over the group algebra exactly when its
underlying `Λ`-module is projective and there exists a `Λ`-linear endomorphism whose group-average
is the identity on `P`; mathlib expresses this averaged conjugation operator as the canonical
linear map `LinearMap.sumOfConjugates`. -/
theorem projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism :
    Module.Projective Λ[G] P ↔
      Module.Projective Λ P ∧
        ∃ u : Module.End Λ P, u.sumOfConjugates G = .id := by
  constructor
  · intro hP
    -- Start from a `Λ[G]`-splitting, restrict scalars to get `Λ`-projectivity, and then recover
    -- the averaging endomorphism from the coefficient of an induced-module section.
    have hPΛ : Module.Projective Λ P :=
      projective_restrictScalars_of_projective_groupAlgebra
        (Λ := Λ) (G := G) (P := P) hP
    let _ : Module.Projective Λ P := hPΛ
    let _ : Module.Projective Λ[G] (Λ[G] ⊗[Λ] P) := by
      infer_instance
    obtain ⟨v, hv⟩ :=
      (Module.Projective.iff_split_of_projective
        (s := groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P))
        (groupAlgebra_tensor_action_surjective (Λ := Λ) (G := G) (P := P))).mp hP
    classical
    let u : Module.End Λ P :=
      tensor_left_coeffOne (Λ := Λ) (G := G) (P := P).comp (v.restrictScalars Λ)
    have hcomp :
        ((groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)).restrictScalars Λ).comp
          (v.restrictScalars Λ) = u.sumOfConjugates G := by
      simpa [u] using
        tensor_action_comp_equivariant_eq_sumOfConjugates
          (Λ := Λ) (G := G) (P := P) (v := v)
    have hv' :
        ((groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)).restrictScalars Λ).comp
          (v.restrictScalars Λ) = LinearMap.id := by
      simpa using congrArg (LinearMap.restrictScalars Λ) hv
    refine ⟨hPΛ, u, ?_⟩
    exact hcomp.symm.trans hv'
  · rintro ⟨hP, u, hu⟩
    -- Use the given averaging endomorphism to build an equivariant section of the induced-module
    -- surjection, then split off `P` from a projective induced module.
    let _ : Module.Projective Λ P := hP
    let _ : Module.Projective Λ[G] (Λ[G] ⊗[Λ] P) := by
      infer_instance
    obtain ⟨v, hv⟩ :=
      averaging_endomorphism_yields_section (Λ := Λ) (G := G) (P := P) u hu
    exact
      Module.Projective.of_split v
        (groupAlgebra_tensor_action (Λ := Λ) (G := G) (P := P)) hv

end
