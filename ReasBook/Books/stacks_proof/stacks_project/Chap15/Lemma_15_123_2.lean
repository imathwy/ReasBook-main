import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_119_6
import stacks_proof.stacks_project.Chap15.Lemma_15_123_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.2:
- primary domain: determinant maps of admissible morphisms between bounded finite-projective
  two-term cochain complexes, and invariance of those maps under chain homotopy;
- sampled owner declarations of the same kind:
  `_root_.Homotopy`,
  `_root_.Homotopy.dNext_eq`,
  `determinantMap`,
  `determinantIso`;
- best owner abstraction:
  `core/canonical`: the homotopy datum should be owned by `_root_.Homotopy a b`, and the
    determinant comparison should be stated using the chapter owner `determinantMap`;
  `source-facing`: the Stacks statement that chain-homotopic admissible perturbations induce the
    same determinant map;
  `bridge/view`: in these degrees a homotopy is equivalently determined by its degree-`0`
    component `K.X 0 ⟶ L.X (-1)`, while `determinantMap` is the contravariant view of
    `determinantIso`.
- primitive data: the two morphisms `a`, `b`, their admissibility witnesses, and a chain homotopy
  `_root_.Homotopy a b`;
- derived API: the degree `-1/0` perturbation formulas and the expanded inverse linear map
  `(determinantIso _ _).symm.toLinearMap`, so those should not remain primitive public input or
  output data here.
-/

-- Proof sketch: locally on `Spec R`, the homotopy perturbation is given by conjugating the short
-- exact kernel rows by automorphisms of the middle terms. Lemma `15.119.6` then identifies the
-- determinant contributions of `a` and `b`.
/-- Helper for Lemma 15.123.2: after reversing the homotopy, the only nonzero component is the
degree-`0 → -1` map, so the endpoint maps differ by the expected Stacks perturbation formulas. -/
private theorem homotopy_reverse_component_formulas
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    (b.f (-1)).hom = (a.f (-1)).hom + h.comp (K.d (-1) 0).hom ∧
      (b.f 0).hom = (a.f 0).hom + (L.d (-1) 0).hom.comp h := by
  dsimp
  have hhom_one : H.symm.hom 1 0 = 0 := by
    -- Proof comment: the source complex has no degree-`1` term, so this homotopy component
    -- vanishes.
    exact (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_src _ _
  have hhom_negTwo : H.symm.hom (-1) (-2) = 0 := by
    -- Proof comment: the target complex starts in degree `-1`, so no homotopy component can land
    -- in degree `-2`.
    exact (L.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_tgt _ _
  have hhom_one_hom : (H.hom 1 0).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom hhom_one
  have hhom_negTwo_hom : (H.hom (-1) (-2)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom hhom_negTwo
  have hcomm_negOne := H.symm.comm (-1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp)] at hcomm_negOne
  have hcomm_zero := H.symm.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hcomm_zero
  refine ⟨?_, ?_⟩
  · -- Proof comment: in degree `-1`, the vanished `(-1,-2)` component leaves only `h ∘ d`.
    simpa [hhom_negTwo_hom, add_assoc, add_left_comm, add_comm] using
      congrArg (fun f : K.X (-1) ⟶ L.X (-1) ↦ f.hom) hcomm_negOne
  · -- Proof comment: in degree `0`, the vanished `(1,0)` component leaves only `d ∘ h`.
    simpa [hhom_one_hom, add_assoc, add_left_comm, add_comm] using
      congrArg (fun f : K.X 0 ⟶ L.X 0 ↦ f.hom) hcomm_zero

/-- Helper for Lemma 15.123.2: choosing a section of `a^{-1}` packages the reversed homotopy
perturbation into endomorphisms of the source complex in degrees `-1` and `0`. -/
private theorem section_perturbation_component_formulas
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    (a.f (-1)).hom.comp uNeg = (b.f (-1)).hom ∧
      (a.f 0).hom.comp uZero = (b.f 0).hom ∧
      uZero.comp (K.d (-1) 0).hom = (K.d (-1) 0).hom.comp uNeg := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  obtain ⟨hneg, hzero⟩ := homotopy_reverse_component_formulas (H := H)
  dsimp [h, t, uNeg, uZero] at hneg hzero ⊢
  have hσ_apply (x : L.X (-1)) : (a.f (-1)).hom (σ x) = x := by
    -- Proof comment: evaluate the chosen section identity pointwise.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ x
  have ha_comm_apply (x : K.X (-1)) :
      (a.f 0).hom ((K.d (-1) 0).hom x) = (L.d (-1) 0).hom ((a.f (-1)).hom x) := by
    -- Proof comment: evaluate the degree `-1/0` chain-map square for `a` at the chosen vector.
    simpa only [LinearMap.comp_apply] using
      congrArg (fun f : K.X (-1) ⟶ L.X 0 ↦ f.hom x) (a.comm (-1) 0).symm
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the section turns the additive correction `h ∘ d` into right composition
    -- by the source endomorphism `uNeg`.
    ext x
    calc
      ((a.f (-1)).hom.comp (1 + (σ.comp h).comp (K.d (-1) 0).hom)) x
          = (a.f (-1)).hom x + (a.f (-1)).hom (σ (h ((K.d (-1) 0).hom x))) := by
              simp [LinearMap.comp_apply]
      _ = (a.f (-1)).hom x + h ((K.d (-1) 0).hom x) := by
            rw [hσ_apply]
      _ = (b.f (-1)).hom x := by
            simpa [LinearMap.add_apply, LinearMap.comp_apply] using
              (LinearMap.congr_fun hneg x).symm
  · -- Proof comment: the degree-`0` factorization uses the chain-map square for `a` to move the
    -- differential across the chosen section.
    ext x
    calc
      ((a.f 0).hom.comp (1 + (K.d (-1) 0).hom.comp (σ.comp h))) x
          = (a.f 0).hom x + (a.f 0).hom ((K.d (-1) 0).hom (σ (h x))) := by
              simp [LinearMap.comp_apply]
      _ = (a.f 0).hom x + (L.d (-1) 0).hom ((a.f (-1)).hom (σ (h x))) := by
            rw [ha_comm_apply]
      _ = (a.f 0).hom x + (L.d (-1) 0).hom (h x) := by
            rw [hσ_apply]
      _ = (b.f 0).hom x := by
            change
              (a.f 0).hom x + (L.d (-1) 0).hom (-(H.hom 0 (-1)).hom x) =
                (b.f 0).hom x
            simpa [LinearMap.add_apply, LinearMap.comp_apply] using
              (LinearMap.congr_fun hzero x).symm
  · -- Proof comment: both composites expand to `d + d ∘ t ∘ d`.
    ext x
    simp [LinearMap.comp_apply]

/-- Helper for Lemma 15.123.2: the source perturbation endomorphisms restrict to a commutative
ladder between the two kernel rows attached to `a` and `b`. -/
private theorem section_perturbation_projectiveDet_eq
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1)) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    LinearMap.projectiveDet uNeg = LinearMap.projectiveDet uZero := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  -- Proof comment: the perturbation endomorphisms are exactly `1 + t ∘ d` and `1 + d ∘ t`, so
  -- Lemma `15.119.6` applies directly to the pair `(d, t)`.
  simpa [h, t, uNeg, uZero] using
    (LinearMap.det_id_add_a_comp_b_eq_det_id_add_b_comp_a
      (R := R) (a := (K.d (-1) 0).hom) (b := t)).symm

/-- Helper for Lemma 15.123.2: the source perturbation endomorphisms restrict to a commutative
ladder between the two kernel rows attached to `a` and `b`. -/
private theorem section_perturbation_kernel_maps
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    ∃ κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom,
      ∃ κZero : LinearMap.ker (b.f 0).hom →ₗ[R] LinearMap.ker (a.f 0).hom,
        (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
            uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype ∧
          (LinearMap.ker (a.f 0).hom).subtype.comp κZero =
            uZero.comp (LinearMap.ker (b.f 0).hom).subtype ∧
          (kernelDifferential a).comp κNeg = κZero.comp (kernelDifferential b) := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  obtain ⟨hneg, hzero, hcomm⟩ := section_perturbation_component_formulas (H := H) σ hσ
  have hκNeg_mem :
      ∀ x : LinearMap.ker (b.f (-1)).hom,
        (uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype) x ∈
          LinearMap.ker (a.f (-1)).hom := by
    intro x
    -- Proof comment: the degree `-1` perturbation identity sends a `b^{-1}`-kernel vector to the
    -- corresponding `a^{-1}`-kernel vector.
    rw [LinearMap.mem_ker]
    change (a.f (-1)).hom (uNeg x) = 0
    calc
      (a.f (-1)).hom (uNeg x) = (b.f (-1)).hom x := by
        simpa [uNeg, t, h, LinearMap.comp_apply] using
          congrArg (fun f : K.X (-1) →ₗ[R] L.X (-1) ↦ f x) hneg
      _ = 0 := x.2
  have hκZero_mem :
      ∀ x : LinearMap.ker (b.f 0).hom,
        (uZero.comp (LinearMap.ker (b.f 0).hom).subtype) x ∈
          LinearMap.ker (a.f 0).hom := by
    intro x
    -- Proof comment: the same argument in degree `0` restricts `uZero` to the `0`-kernels.
    rw [LinearMap.mem_ker]
    change (a.f 0).hom (uZero x) = 0
    calc
      (a.f 0).hom (uZero x) = (b.f 0).hom x := by
        simpa [uZero, t, h, LinearMap.comp_apply] using
          congrArg (fun f : K.X 0 →ₗ[R] L.X 0 ↦ f x) hzero
      _ = 0 := x.2
  let κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom :=
    LinearMap.codRestrict
      (LinearMap.ker (a.f (-1)).hom)
      (uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype)
      hκNeg_mem
  let κZero : LinearMap.ker (b.f 0).hom →ₗ[R] LinearMap.ker (a.f 0).hom :=
    LinearMap.codRestrict
      (LinearMap.ker (a.f 0).hom)
      (uZero.comp (LinearMap.ker (b.f 0).hom).subtype)
      hκZero_mem
  have hκNeg_subtype :
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
        uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype := by
    -- Proof comment: `κNeg` is the codomain restriction of `uNeg`, so forgetting the subtype
    -- recovers the original map.
    ext x
    rfl
  have hκZero_subtype :
      (LinearMap.ker (a.f 0).hom).subtype.comp κZero =
        uZero.comp (LinearMap.ker (b.f 0).hom).subtype := by
    -- Proof comment: the same codomain-restriction computation identifies `κZero`.
    ext x
    rfl
  have hκSquare :
      (kernelDifferential a).comp κNeg = κZero.comp (kernelDifferential b) := by
    -- Proof comment: after forgetting the subtype proofs, the kernel differential square is just
    -- the commutation relation `uZero ∘ d = d ∘ uNeg`.
    ext x
    change ((K.d (-1) 0).hom.comp uNeg) x = (uZero.comp (K.d (-1) 0).hom) x
    simpa [uNeg, uZero, t, h, LinearMap.comp_apply] using
      congrArg (fun f : K.X (-1) →ₗ[R] K.X 0 ↦ f x) hcomm.symm
  exact ⟨κNeg, κZero, hκNeg_subtype, hκZero_subtype, hκSquare⟩

/-- Helper for Lemma 15.123.2: on `ker(b⁻¹)`, the restricted perturbation map is the split
projection `x ↦ x - σ(a⁻¹ x)`. -/
private theorem section_perturbation_kernel_projection_formula
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    {κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom}
    (hκNeg :
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
        (((LinearMap.id : K.X (-1) →ₗ[R] K.X (-1)) +
            ((σ.comp (-(H.hom 0 (-1)).hom)).comp (K.d (-1) 0).hom))).comp
          (LinearMap.ker (b.f (-1)).hom).subtype) :
    ∀ x : LinearMap.ker (b.f (-1)).hom,
      ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) =
        x - σ ((a.f (-1)).hom x) := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  obtain ⟨hneg, -⟩ := homotopy_reverse_component_formulas (H := H)
  dsimp [h, t, uNeg] at hneg ⊢
  intro x
  have hκNeg_apply :
      ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) =
        x + (σ.comp (-(H.hom 0 (-1)).hom)) ((K.d (-1) 0).hom x) := by
    -- Proof comment: forgetting the codomain restriction identifies `κNeg` with `uNeg`.
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] K.X (-1) ↦ f x)
        hκNeg
  have hsum :
      (a.f (-1)).hom x + (-(H.hom 0 (-1)).hom) ((K.d (-1) 0).hom x) = 0 := by
    -- Proof comment: evaluating the degree `-1` perturbation identity on `x ∈ ker(b⁻¹)` leaves
    -- exactly the cancellation relation needed for the split projection formula.
    have hneg_apply :
        (b.f (-1)).hom x =
          (a.f (-1)).hom x + (-(H.hom 0 (-1)).hom) ((K.d (-1) 0).hom x) := by
      simpa [LinearMap.add_apply, LinearMap.comp_apply] using
        congrArg
          (fun f : K.X (-1) →ₗ[R] L.X (-1) ↦ f x)
          hneg
    calc
      (a.f (-1)).hom x + (-(H.hom 0 (-1)).hom) ((K.d (-1) 0).hom x) = (b.f (-1)).hom x := by
        rw [hneg_apply]
      _ = 0 := x.2
  have hsplit :
      (-(H.hom 0 (-1)).hom) ((K.d (-1) 0).hom x) = -((a.f (-1)).hom x) := by
    -- Proof comment: subtracting the `a⁻¹ x` term isolates the perturbation correction.
    have := congrArg (fun z : L.X (-1) ↦ z - (a.f (-1)).hom x) hsum
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  calc
    ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) =
        x + (σ.comp (-(H.hom 0 (-1)).hom)) ((K.d (-1) 0).hom x) := hκNeg_apply
    _ = x + σ ((-(H.hom 0 (-1)).hom) ((K.d (-1) 0).hom x)) := by
          simp [LinearMap.comp_apply]
    _ = x - σ ((a.f (-1)).hom x) := by
          rw [hsplit, LinearMap.map_neg]
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.123.2: if the chosen section also makes `b⁻¹ ∘ σ` surjective, then every
`y ∈ ker(a⁻¹)` comes from a split preimage `x = y + σ ℓ ∈ ker(b⁻¹)` under the restricted
perturbation map `κNeg`. -/
private theorem section_perturbation_split_preimage
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    (hbσ : Function.Surjective ((b.f (-1)).hom.comp σ))
    {κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom}
    (hκNeg :
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
        (((LinearMap.id : K.X (-1) →ₗ[R] K.X (-1)) +
            ((σ.comp (-(H.hom 0 (-1)).hom)).comp (K.d (-1) 0).hom))).comp
          (LinearMap.ker (b.f (-1)).hom).subtype)
    (y : LinearMap.ker (a.f (-1)).hom) :
    ∃ x : LinearMap.ker (b.f (-1)).hom,
      ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) = y := by
  -- Route correction: the source proof does not introduce a fresh abstract surjectivity bridge
  -- here. It fixes `y ∈ ker(a⁻¹)`, writes the desired preimage as `x = y + σ ℓ`, and uses the
  -- split projection formula to reduce the goal to the residual equation `b⁻¹ (y + σ ℓ) = 0`.
  have hprojection :
      ∀ x : LinearMap.ker (b.f (-1)).hom,
        ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) =
          x - σ ((a.f (-1)).hom x) :=
    section_perturbation_kernel_projection_formula (H := H) σ hσ hκNeg
  have hσ_apply (z : L.X (-1)) : (a.f (-1)).hom (σ z) = z := by
    -- Proof comment: the chosen section is a right inverse to `a⁻¹`, so it evaluates pointwise.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ z
  obtain ⟨ℓ, hℓ⟩ := hbσ (- (b.f (-1)).hom y)
  let xVal : K.X (-1) := y + σ ℓ
  have hxker : (b.f (-1)).hom xVal = 0 := by
    -- Proof comment: the extra surjectivity hypothesis on `b⁻¹ ∘ σ` solves the residual split
    -- equation from the source proof.
    calc
      (b.f (-1)).hom xVal =
          (b.f (-1)).hom y + (((b.f (-1)).hom.comp σ) ℓ) := by
            simp [xVal, LinearMap.comp_apply]
      _ = (b.f (-1)).hom y + (-(b.f (-1)).hom y) := by rw [hℓ]
      _ = 0 := by simp
  let x : LinearMap.ker (b.f (-1)).hom := ⟨xVal, hxker⟩
  have hx_a : (a.f (-1)).hom x = ℓ := by
    -- Proof comment: the `a⁻¹`-image of `x = y + σ ℓ` is exactly `ℓ` because `y ∈ ker(a⁻¹)`.
    change (a.f (-1)).hom xVal = ℓ
    calc
      (a.f (-1)).hom xVal = (a.f (-1)).hom y + (a.f (-1)).hom (σ ℓ) := by
        simp [xVal]
      _ = 0 + ℓ := by rw [y.2, hσ_apply]
      _ = ℓ := by simp
  refine ⟨x, ?_⟩
  calc
    ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) = x - σ ((a.f (-1)).hom x) := hprojection x
    _ = y := by
      -- Proof comment: the split projection formula collapses to `y` once we rewrite `a⁻¹ x = ℓ`
      -- and expand `x = y + σ ℓ`.
      change xVal - σ ℓ = y
      simp [xVal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.123.2: surjectivity of the degree-`-1` kernel restriction is exactly the
pointwise split-preimage statement. -/
private theorem section_perturbation_kernel_surjective
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    (hbσ : Function.Surjective ((b.f (-1)).hom.comp σ))
    {κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom}
    (hκNeg :
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
        (((LinearMap.id : K.X (-1) →ₗ[R] K.X (-1)) +
            ((σ.comp (-(H.hom 0 (-1)).hom)).comp (K.d (-1) 0).hom))).comp
          (LinearMap.ker (b.f (-1)).hom).subtype) :
    Function.Surjective κNeg := by
  intro y
  obtain ⟨x, hx⟩ := section_perturbation_split_preimage (H := H) σ hσ hbσ hκNeg y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simpa using hx

/-- Helper for Lemma 15.123.2: in each degree, surjectivity of the perturbation endomorphism is
equivalent to surjectivity of its restriction to the corresponding kernel row. -/
private theorem section_perturbation_surjective_equivalences
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    ∀ (κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom)
      (κZero : LinearMap.ker (b.f 0).hom →ₗ[R] LinearMap.ker (a.f 0).hom),
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
          uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype →
        (LinearMap.ker (a.f 0).hom).subtype.comp κZero =
          uZero.comp (LinearMap.ker (b.f 0).hom).subtype →
        (Function.Surjective uNeg ↔ Function.Surjective κNeg) ∧
          (Function.Surjective uZero ↔ Function.Surjective κZero) := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  obtain ⟨hneg, hzero, -⟩ := section_perturbation_component_formulas (H := H) σ hσ
  dsimp [h, t, uNeg, uZero] at hneg hzero ⊢
  intro κNeg κZero hκNeg hκZero
  have hneg_apply (x : K.X (-1)) :
      (a.f (-1)).hom (uNeg x) = (b.f (-1)).hom x := by
    -- Proof comment: evaluate the degree `-1` perturbation identity on the chosen source vector.
    simpa [h, t, uNeg, LinearMap.comp_apply] using
      congrArg (fun f : K.X (-1) →ₗ[R] L.X (-1) ↦ f x) hneg
  have hzero_apply (x : K.X 0) :
      (a.f 0).hom (uZero x) = (b.f 0).hom x := by
    -- Proof comment: the same evaluation in degree `0` rewrites `a⁰ ∘ uZero` as `b⁰`.
    simpa [h, t, uZero, LinearMap.comp_apply] using
      congrArg (fun f : K.X 0 →ₗ[R] L.X 0 ↦ f x) hzero
  constructor
  · constructor
    · intro hsurjU y
      obtain ⟨x, hx⟩ := hsurjU y
      have hxker : (b.f (-1)).hom x = 0 := by
        -- Proof comment: if `uNeg x = y` lands in `ker(a⁻¹)`, then `x` already lies in
        -- `ker(b⁻¹)` because `a⁻¹ ∘ uNeg = b⁻¹`.
        calc
          (b.f (-1)).hom x = (a.f (-1)).hom (uNeg x) := by rw [hneg_apply]
          _ = (a.f (-1)).hom y := by rw [hx]
          _ = 0 := y.2
      refine ⟨⟨x, hxker⟩, ?_⟩
      apply Subtype.ext
      -- Proof comment: forgetting the subtype, `κNeg` is exactly the restriction of `uNeg`.
      calc
        ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg ⟨x, hxker⟩)) = uNeg x := by
          simpa [h, t, uNeg, LinearMap.comp_apply] using
            congrArg
              (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] K.X (-1) ↦ f ⟨x, hxker⟩)
              hκNeg
        _ = y := hx
    · intro hsurjκ y
      obtain ⟨x, hx⟩ := hb.mapNegOne_surjective ((a.f (-1)).hom y)
      have hy_mem : y - uNeg x ∈ LinearMap.ker (a.f (-1)).hom := by
        -- Proof comment: matching the `L⁻¹`-image of `y` with a `b⁻¹`-preimage leaves a residual
        -- term in `ker(a⁻¹)`.
        rw [LinearMap.mem_ker]
        calc
          (a.f (-1)).hom (y - uNeg x) =
              (a.f (-1)).hom y - (a.f (-1)).hom (uNeg x) := by
                simp
          _ = (a.f (-1)).hom y - (b.f (-1)).hom x := by rw [hneg_apply]
          _ = 0 := by simp [hx]
      obtain ⟨z, hz⟩ := hsurjκ ⟨y - uNeg x, hy_mem⟩
      refine ⟨x + z, ?_⟩
      have hz_val :
          ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg z)) = y - uNeg x :=
        congrArg (fun w : LinearMap.ker (a.f (-1)).hom ↦ (w : K.X (-1))) hz
      have hκNeg_apply :
          ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg z)) = uNeg z := by
        -- Proof comment: evaluate the restricted-map identity on the chosen kernel vector `z`.
        simpa [h, t, uNeg, LinearMap.comp_apply] using
          congrArg
            (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] K.X (-1) ↦ f z)
            hκNeg
      -- Proof comment: the kernel correction `z` cancels the residual term, so `x + z` is a
      -- genuine preimage of `y`.
      calc
        uNeg (x + z) = uNeg x + uNeg z := by simp
        _ = uNeg x + (y - uNeg x) := by rw [← hκNeg_apply, hz_val]
        _ = y := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · constructor
    · intro hsurjU y
      obtain ⟨x, hx⟩ := hsurjU y
      have hxker : (b.f 0).hom x = 0 := by
        -- Proof comment: the degree-`0` kernel restriction is detected by `a⁰ ∘ uZero = b⁰`.
        calc
          (b.f 0).hom x = (a.f 0).hom (uZero x) := by rw [hzero_apply]
          _ = (a.f 0).hom y := by rw [hx]
          _ = 0 := y.2
      refine ⟨⟨x, hxker⟩, ?_⟩
      apply Subtype.ext
      -- Proof comment: forgetting the subtype identifies `κZero` with the restricted `uZero`.
      calc
        ((LinearMap.ker (a.f 0).hom).subtype (κZero ⟨x, hxker⟩)) = uZero x := by
          simpa [h, t, uZero, LinearMap.comp_apply] using
            congrArg
              (fun f : LinearMap.ker (b.f 0).hom →ₗ[R] K.X 0 ↦ f ⟨x, hxker⟩)
              hκZero
        _ = y := hx
    · intro hsurjκ y
      obtain ⟨x, hx⟩ := hb.mapZero_surjective ((a.f 0).hom y)
      have hy_mem : y - uZero x ∈ LinearMap.ker (a.f 0).hom := by
        -- Proof comment: the same degree-`0` diagram chase produces a residual kernel element.
        rw [LinearMap.mem_ker]
        calc
          (a.f 0).hom (y - uZero x) =
              (a.f 0).hom y - (a.f 0).hom (uZero x) := by
                simp
          _ = (a.f 0).hom y - (b.f 0).hom x := by rw [hzero_apply]
          _ = 0 := by simp [hx]
      obtain ⟨z, hz⟩ := hsurjκ ⟨y - uZero x, hy_mem⟩
      refine ⟨x + z, ?_⟩
      have hz_val :
          ((LinearMap.ker (a.f 0).hom).subtype (κZero z)) = y - uZero x :=
        congrArg (fun w : LinearMap.ker (a.f 0).hom ↦ (w : K.X 0)) hz
      have hκZero_apply :
          ((LinearMap.ker (a.f 0).hom).subtype (κZero z)) = uZero z := by
        -- Proof comment: this is the degree-`0` restriction identity evaluated at `z`.
        simpa [h, t, uZero, LinearMap.comp_apply] using
          congrArg
            (fun f : LinearMap.ker (b.f 0).hom →ₗ[R] K.X 0 ↦ f z)
            hκZero
      -- Proof comment: adding the kernel correction again produces an actual preimage of `y`.
      calc
        uZero (x + z) = uZero x + uZero z := by simp
        _ = uZero x + (y - uZero x) := by rw [← hκZero_apply, hz_val]
        _ = y := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.123.2: the two kernel restrictions are simultaneously surjective because
the admissible kernel differentials identify them up to conjugation. -/
private theorem section_perturbation_kernel_surjective_equiv
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    {κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom}
    {κZero : LinearMap.ker (b.f 0).hom →ₗ[R] LinearMap.ker (a.f 0).hom}
    (hκSquare : (kernelDifferential a).comp κNeg = κZero.comp (kernelDifferential b)) :
    Function.Surjective κNeg ↔ Function.Surjective κZero := by
  constructor
  · intro hsurjNeg y
    obtain ⟨x, hx⟩ := ha.kernelDifferential_bijective.2 y
    obtain ⟨z, hz⟩ := hsurjNeg x
    refine ⟨(kernelDifferential b) z, ?_⟩
    -- Proof comment: surjectivity in degree `-1` transports across the commutative square by
    -- first lifting `y` through the bijective kernel differential of `a`.
    calc
      κZero ((kernelDifferential b) z) = (kernelDifferential a) (κNeg z) := by
        simpa [LinearMap.comp_apply] using
          (congrArg
            (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f 0).hom ↦ f z)
            hκSquare).symm
      _ = (kernelDifferential a) x := by rw [hz]
      _ = y := hx
  · intro hsurjZero y
    obtain ⟨z, hz⟩ := hsurjZero ((kernelDifferential a) y)
    obtain ⟨x, hx⟩ := hb.kernelDifferential_bijective.2 z
    -- Proof comment: after lifting the degree-`0` preimage back through `kernelDifferential b`,
    -- injectivity of `kernelDifferential a` recovers the required degree-`-1` preimage.
    refine ⟨x, ?_⟩
    apply ha.kernelDifferential_bijective.1
    calc
      (kernelDifferential a) (κNeg x) = κZero ((kernelDifferential b) x) := by
        simpa [LinearMap.comp_apply] using
          congrArg
            (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f 0).hom ↦ f x)
            hκSquare
      _ = κZero z := by rw [hx]
      _ = (kernelDifferential a) y := hz

/-- Helper for Lemma 15.123.2: once the degree `-1` kernel restriction is surjective, the rest of
the perturbation ladder becomes surjective, and the middle endomorphisms are automorphisms by the
finite-module endomorphism criterion. -/
private theorem section_perturbation_middle_bijective_of_kernel_surjective
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    ∀ {κNeg : LinearMap.ker (b.f (-1)).hom →ₗ[R] LinearMap.ker (a.f (-1)).hom}
      {κZero : LinearMap.ker (b.f 0).hom →ₗ[R] LinearMap.ker (a.f 0).hom},
      (LinearMap.ker (a.f (-1)).hom).subtype.comp κNeg =
          uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype →
        (LinearMap.ker (a.f 0).hom).subtype.comp κZero =
          uZero.comp (LinearMap.ker (b.f 0).hom).subtype →
        (kernelDifferential a).comp κNeg = κZero.comp (kernelDifferential b) →
        Function.Surjective κNeg →
        Function.Surjective κZero ∧
          Function.Bijective uNeg ∧
          Function.Bijective uZero := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  intro κNeg κZero hκNeg hκZero hκSquare hsurjκNeg
  have hsurjκZero : Function.Surjective κZero :=
    (section_perturbation_kernel_surjective_equiv (ha := ha) (hb := hb) hκSquare).1 hsurjκNeg
  obtain ⟨huNeg, huZero⟩ :=
    section_perturbation_surjective_equivalences (ha := ha) (hb := hb) (H := H) σ hσ κNeg κZero
      hκNeg hκZero
  have hsurjUNeg : Function.Surjective uNeg := huNeg.2 hsurjκNeg
  have hsurjUZero : Function.Surjective uZero := huZero.2 hsurjκZero
  have hbijUNeg : Function.Bijective uNeg :=
    OrzechProperty.bijective_of_surjective_endomorphism uNeg hsurjUNeg
  have hbijUZero : Function.Bijective uZero :=
    OrzechProperty.bijective_of_surjective_endomorphism uZero hsurjUZero
  exact ⟨hsurjκZero, hbijUNeg, hbijUZero⟩

/-- Helper for Lemma 15.123.2: a section `σ` with `a⁻¹ ∘ σ = id` and surjective `b⁻¹ ∘ σ`
already supplies the full source-faithful perturbation package: the degree `-1` kernel map is
surjective, hence the middle perturbation endomorphisms are automorphisms. -/
private theorem section_perturbation_middle_bijective_of_surjective_b_section
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    (hbσ : Function.Surjective ((b.f (-1)).hom.comp σ)) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    Function.Bijective uNeg ∧ Function.Bijective uZero := by
  obtain ⟨κNeg, κZero, hκNeg, hκZero, hκSquare⟩ :=
    section_perturbation_kernel_maps (H := H) σ hσ
  have hsurjκNeg : Function.Surjective κNeg :=
    -- Proof comment: the repaired split-preimage lemma turns the extra surjectivity of `b⁻¹ ∘ σ`
    -- into surjectivity of the degree `-1` kernel restriction.
    section_perturbation_kernel_surjective (H := H) σ hσ hbσ hκNeg
  obtain ⟨-, hbijUNeg, hbijUZero⟩ :=
    -- Proof comment: once the degree `-1` kernel restriction is surjective, the kernel ladder and
    -- admissibility propagate surjectivity through degree `0`, and finite-projective endomorphism
    -- surjectivity upgrades to bijectivity.
    section_perturbation_middle_bijective_of_kernel_surjective
      (ha := ha) (hb := hb) (H := H) σ hσ hκNeg hκZero hκSquare hsurjκNeg
  exact ⟨hbijUNeg, hbijUZero⟩

/-- Helper for Lemma 15.123.2: under the source-faithful section hypothesis, the restricted
kernel maps are actual linear equivalences compatible with both short exact kernel rows. -/
private theorem section_perturbation_kernel_equivalences_of_surjective_b_section
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    (hbσ : Function.Surjective ((b.f (-1)).hom.comp σ)) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    ∃ eNeg : LinearMap.ker (b.f (-1)).hom ≃ₗ[R] LinearMap.ker (a.f (-1)).hom,
      ∃ eZero : LinearMap.ker (b.f 0).hom ≃ₗ[R] LinearMap.ker (a.f 0).hom,
        (LinearMap.ker (a.f (-1)).hom).subtype.comp eNeg.toLinearMap =
            uNeg.comp (LinearMap.ker (b.f (-1)).hom).subtype ∧
          (LinearMap.ker (a.f 0).hom).subtype.comp eZero.toLinearMap =
            uZero.comp (LinearMap.ker (b.f 0).hom).subtype ∧
          (kernelDifferential a).comp eNeg.toLinearMap =
            eZero.toLinearMap.comp (kernelDifferential b) := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  obtain ⟨κNeg, κZero, hκNeg, hκZero, hκSquare⟩ :=
    section_perturbation_kernel_maps (H := H) σ hσ
  have hsurjκNeg : Function.Surjective κNeg :=
    -- Proof comment: the source's split-preimage argument already upgrades the degree `-1`
    -- kernel restriction to a surjection.
    section_perturbation_kernel_surjective (H := H) σ hσ hbσ hκNeg
  have hsurjκZero : Function.Surjective κZero :=
    -- Proof comment: admissibility transports this surjectivity across the kernel-differential
    -- square.
    (section_perturbation_kernel_surjective_equiv (ha := ha) (hb := hb) hκSquare).1 hsurjκNeg
  obtain ⟨hbijUNeg, hbijUZero⟩ :=
    section_perturbation_middle_bijective_of_surjective_b_section
      (ha := ha) (hb := hb) (H := H) σ hσ hbσ
  dsimp [h, t, uNeg, uZero] at hκNeg hκZero hκSquare ⊢
  have hκNeg_apply (x : LinearMap.ker (b.f (-1)).hom) :
      ((LinearMap.ker (a.f (-1)).hom).subtype (κNeg x)) = uNeg x := by
    -- Proof comment: forgetting the codomain restriction identifies `κNeg` with the restricted
    -- middle perturbation endomorphism.
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun f : LinearMap.ker (b.f (-1)).hom →ₗ[R] K.X (-1) ↦ f x)
        hκNeg
  have hκZero_apply (x : LinearMap.ker (b.f 0).hom) :
      ((LinearMap.ker (a.f 0).hom).subtype (κZero x)) = uZero x := by
    -- Proof comment: the same identification holds in degree `0`.
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun f : LinearMap.ker (b.f 0).hom →ₗ[R] K.X 0 ↦ f x)
        hκZero
  have hκNeg_inj : Function.Injective κNeg := by
    intro x y hxy
    apply Subtype.ext
    -- Proof comment: after identifying both restricted maps with `uNeg`, injectivity of `uNeg`
    -- forces equality in the kernel.
    apply hbijUNeg.1
    rw [← hκNeg_apply x, hxy, hκNeg_apply y]
  have hκZero_inj : Function.Injective κZero := by
    intro x y hxy
    apply Subtype.ext
    -- Proof comment: the degree-`0` kernel restriction is injective for the same reason.
    apply hbijUZero.1
    rw [← hκZero_apply x, hxy, hκZero_apply y]
  let eNeg : LinearMap.ker (b.f (-1)).hom ≃ₗ[R] LinearMap.ker (a.f (-1)).hom :=
    LinearEquiv.ofBijective κNeg ⟨hκNeg_inj, hsurjκNeg⟩
  let eZero : LinearMap.ker (b.f 0).hom ≃ₗ[R] LinearMap.ker (a.f 0).hom :=
    LinearEquiv.ofBijective κZero ⟨hκZero_inj, hsurjκZero⟩
  refine ⟨eNeg, eZero, ?_, ?_, ?_⟩
  · -- Proof comment: after packaging `κNeg` as an equivalence, the degree `-1` ladder identity
    -- is unchanged.
    simpa [eNeg] using hκNeg
  · -- Proof comment: likewise for the degree `0` row.
    simpa [eZero] using hκZero
  · -- Proof comment: the kernel differential square is the same equality after replacing the raw
    -- restricted maps by their packaged equivalences.
    simpa [eNeg, eZero] using hκSquare

/-- Helper for Lemma 15.123.2: under the source-faithful section hypothesis, the middle
perturbation endomorphisms can be packaged as genuine linear equivalences. -/
private theorem section_perturbation_middle_linearEquivs_of_surjective_b_section
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (σ : L.X (-1) →ₗ[R] K.X (-1))
    (hσ : (a.f (-1)).hom.comp σ = LinearMap.id)
    (hbσ : Function.Surjective ((b.f (-1)).hom.comp σ)) :
    let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
    let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
    let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
    let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
    ∃ eNeg : K.X (-1) ≃ₗ[R] K.X (-1),
      ∃ eZero : K.X 0 ≃ₗ[R] K.X 0,
        eNeg.toLinearMap = uNeg ∧ eZero.toLinearMap = uZero := by
  let h : K.X 0 →ₗ[R] L.X (-1) := -(H.hom 0 (-1)).hom
  let t : K.X 0 →ₗ[R] K.X (-1) := σ.comp h
  let uNeg : K.X (-1) →ₗ[R] K.X (-1) := 1 + t.comp (K.d (-1) 0).hom
  let uZero : K.X 0 →ₗ[R] K.X 0 := 1 + (K.d (-1) 0).hom.comp t
  obtain ⟨hbijUNeg, hbijUZero⟩ :=
    section_perturbation_middle_bijective_of_surjective_b_section
      (ha := ha) (hb := hb) (H := H) σ hσ hbσ
  -- Proof comment: the previous surjectivity-to-bijectivity step already proves that the two
  -- middle perturbation endomorphisms are bijections, so they can be repackaged as linear
  -- equivalences without changing their underlying maps.
  refine ⟨LinearEquiv.ofBijective uNeg hbijUNeg, LinearEquiv.ofBijective uZero hbijUZero, ?_, ?_⟩
  · rfl
  · rfl

/-- Helper for Lemma 15.123.2: a linear map between finite modules is zero once all of its
maximal localizations have zero range. -/
private theorem linearMap_eq_of_localized_zero_range_at_maximals
    {X Y : Type*}
    [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y]
    (f : X →ₗ[R] Y)
    (hzero : ∀ (m : Ideal R) [m.IsMaximal], LocalizedModule.map m.primeCompl f = 0) :
    f = 0 := by
  apply LinearMap.range_eq_bot.mp
  refine Submodule.eq_of_localization_maximal
    (Rₚ := fun m => Localization.AtPrime m)
    (Mₚ := fun m => LocalizedModule.AtPrime m Y)
    (f := fun m => LocalizedModule.mkLinearMap m.primeCompl Y)
    ?_
  intro m hm
  have hlocalized_range :
      Submodule.localized₀ m.primeCompl
          (LocalizedModule.mkLinearMap m.primeCompl Y)
          (LinearMap.range f) =
        LinearMap.range (LocalizedModule.map m.primeCompl f) := by
    -- Proof comment: the localized image owner agrees with the range of the localized map.
    symm
    simpa using
      (LinearMap.range_localizedMap_eq_localized₀_range
        (p := m.primeCompl)
        (f := LocalizedModule.mkLinearMap m.primeCompl X)
        (f' := LocalizedModule.mkLinearMap m.primeCompl Y)
        (g := f))
  -- Proof comment: after identifying the localized range, the zero-localization hypothesis forces
  -- the localized submodule to be trivial at every maximal ideal.
  ext x
  change
    x ∈ Submodule.localized₀ m.primeCompl
        (LocalizedModule.mkLinearMap m.primeCompl Y)
        (LinearMap.range f) ↔
      x ∈ (⊥ : Submodule R (LocalizedModule.AtPrime m Y))
  rw [hlocalized_range]
  simpa [hzero m]

/-- Helper for Lemma 15.123.2: after localizing at a maximal ideal, the determinant-map
difference vanishes once the source-faithful common-section construction is inserted in degree
`-1`. -/
private theorem localized_determinantMap_difference_zero_at_maximal
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a b : K ⟶ L) (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b)
    (m : Ideal R) [m.IsMaximal] :
    LocalizedModule.map m.primeCompl (determinantMap b hb - determinantMap a ha) = 0 := by
  -- Route correction: the global perturbation ladder is already in place. What remains is the
  -- maximal-local source proof route: construct a localized degree-`-1` common section `σ_m`,
  -- apply `section_perturbation_kernel_equivalences_of_surjective_b_section` over
  -- `Localization.AtPrime m`, compare the localized short exact kernel rows through
  -- `determinantTensorIsoOfShortExact_naturality`, and then transport that localized determinant
  -- equality back to `LocalizedModule.map m.primeCompl (determinantMap _ _ - determinantMap _ _)`.
  sorry

/-- Lemma 15.123.2: if `a^•, b^• : K^• → L^•` are chain-homotopic, both satisfy the
determinant-complex hypotheses, and the degree maps are surjective, then the attached determinant
maps `det(L^•) → det(K^•)` agree. For two-term complexes concentrated in degrees `-1` and `0`,
this homotopy is equivalently determined by its single component `K^0 → L^{-1}`. -/
@[stacks 0FJK]
theorem determinantMap_eq_of_chainHomotopic_surjective_perturbation
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a b : K ⟶ L) (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b) :
    determinantMap b hb = determinantMap a ha := by
  -- Route correction: the proof is now reduced to the source-faithful local step. Once the
  -- determinant-map difference vanishes after every maximal localization, the standard
  -- localization criterion kills its global range.
  let Δ : det(L^•) →ₗ[R] det(K^•) := determinantMap b hb - determinantMap a ha
  have hΔloc : ∀ (m : Ideal R) [m.IsMaximal], LocalizedModule.map m.primeCompl Δ = 0 := by
    intro m hm
    -- Proof comment: this is exactly the localized common-section comparison isolated above.
    simpa [Δ] using
      localized_determinantMap_difference_zero_at_maximal
        (a := a) (b := b) (ha := ha) (hb := hb) (H := H) (m := m)
  have hΔ : Δ = 0 :=
    linearMap_eq_of_localized_zero_range_at_maximals (f := Δ) hΔloc
  exact sub_eq_zero.mp hΔ

end CochainComplex

end
