import Mathlib
import StacksProject_2024.Chap10.Lemma_10_46_11
import StacksProject_2024.Chap15.Lemma_15_111_4

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial PrimeSpectrum RingHom
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Lemma 15.111.7:
- primary domain: invariant theory for the canonical fixed-points map on the base-changed tensor
  product `A ⊗[R^G] R`
- sampled owner declarations:
  `FixedPoints.subalgebra`,
  `Algebra.TensorProduct.includeLeft`,
  `RingHom.ShiftPowerPolynomialImageGenerating`,
  `RingHom.isIntegral_of_shiftPowerPolynomialImageGenerating`
- best owner abstraction: the source-facing owner is the canonical map
  `A → (A ⊗[R^G] R)^G`; the Chapter 10 owner abstraction governing its spectral consequences is the
  shift-power generation predicate `RingHom.ShiftPowerPolynomialImageGenerating`
- primitive data: the fixed subalgebra `FixedPoints.subalgebra RFix (A ⊗[RFix] R) G` and the
  canonical map into it induced by `Algebra.TensorProduct.includeLeft`
- derived API: the flat isomorphism, the shift-power bridge theorem, integrality, purely
  inseparable residue-field extensions, and the homeomorphism on spectra

Layer triage:
- `source-facing`: the canonical fixed-points map and the four source statements of Lemma 15.111.7
- `core/canonical`: `FixedPoints.subalgebra`, `Algebra.TensorProduct.includeLeft`, and the Chapter
  10 owner predicate `RingHom.ShiftPowerPolynomialImageGenerating`
- `bridge/view`: the proof that the canonical fixed-points map satisfies the shift-power
  generation hypothesis, allowing the Chapter 10 owner theorems to supply the spectral
  consequences directly

The file should keep the source-facing fixed-points map, but its spectral consequences should be
derived through the Chapter 10 owner abstraction rather than via parallel local wrappers.
-/

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G

/-- Helper for Lemma 15.111.7: fixed scalars from `R^G` commute with the given `G`-action on
`R`. -/
instance fixedPointsSubring_smulCommClass :
    SMulCommClass G RFix R where
  smul_comm g x r := by
    -- Rewrite the scalar from `R^G` to `R` and use that it is fixed by every group element.
    change (MulSemiringAction.toRingHom G R g) ((x : R) * r) = (x : R) * (g • r)
    rw [map_mul]
    simpa using congrArg (fun t : R => t * (g • r)) (x.2 g)

/-- Helper for Lemma 15.111.7: the right-factor tensor action attached to a group element. -/
private noncomputable abbrev tensorBaseChangeRightAlgHom (g : G) :
    BaseChange →ₐ[RFix] BaseChange :=
  Algebra.TensorProduct.map (AlgHom.id RFix A) (MulSemiringAction.toAlgHom RFix R g)

/-- Helper for Lemma 15.111.7: the monoid hom describing the induced right-factor action on
`A ⊗[R^G] R`. -/
private noncomputable def tensorBaseChangeRightAction :
    G →* (BaseChange →+* BaseChange) where
  toFun g := (tensorBaseChangeRightAlgHom g).toRingHom
  map_one' := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom]
  map_mul' g h := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom, mul_smul]

/-- The induced `G`-action on `A ⊗[R^G] R`, acting on the right tensor factor and trivially on
`A`. -/
noncomputable instance tensorBaseChangeRightMulSemiringAction :
    MulSemiringAction G BaseChange :=
  MulSemiringAction.compHom BaseChange
    (tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange))

/-- Helper for Lemma 15.111.7: the induced right-factor action sends `a ⊗ r` to `a ⊗ g • r`. -/
@[simp] theorem tensorBaseChangeRight_smul_tmul (g : G) (a : A) (r : R) :
    g • ((a ⊗ₜ[RFix] r : BaseChange)) = a ⊗ₜ[RFix] (g • r) := by
  change
    ((tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange)) g) (a ⊗ₜ[RFix] r) =
      a ⊗ₜ[RFix] (g • r)
  rfl

-- Proof sketch: the induced endomorphism on `A ⊗[R^G] R` acts trivially on the left tensor factor,
-- so it fixes every element coming from `A` through `includeLeft`.
/-- The canonical map `A → A ⊗[R^G] R` lands in the fixed part of the base-changed tensor
product. -/
theorem tensorBaseChange_includeLeft_mem_fixedPoints (a : A) :
    (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a ∈ BaseChangeFixed := by
  -- Rewrite `includeLeft a` as `a ⊗ₜ 1` and use that the right-factor action fixes `1`.
  intro g
  simpa [Algebra.TensorProduct.includeLeft_apply] using
    (tensorBaseChangeRight_smul_tmul (R := R) (G := G) (A := A) g a (1 : R))

/-- The canonical `RFix`-algebra map `A → (A ⊗[R^G] R)^G`. -/
noncomputable def tensorBaseChangeFixedPointsMap :
    A →ₐ[RFix] BaseChangeFixed :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).codRestrict BaseChangeFixed
    tensorBaseChange_includeLeft_mem_fixedPoints

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G
local notation "f" =>
  ((tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) : A →+* BaseChangeFixed)

/-- Helper for Lemma 15.111.7: a fixed tensor satisfies an orbit-polynomial identity over the
source ring `A`. -/
theorem exists_monic_polynomial_over_baseChange_eq_X_sub_C_pow_of_fixed
    (b : BaseChangeFixed) :
    ∃ P : Polynomial A,
      P.Monic ∧
        P.map (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) =
          (X - C (b : BaseChange)) ^ Nat.card G := by
  sorry

/-- Helper for Lemma 15.111.7: a kernel element of the ordinary base-change map satisfies the
orbit-polynomial identity `(X - C a)^|G| = X^|G|`. -/
theorem kernelElement_X_sub_pow_eq_X_pow_of_baseChange
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := by
  sorry

/-- Helper for Lemma 15.111.7: forgetting the fixed-point subtype turns the canonical map back
into the usual left tensor inclusion. -/
@[simp] private theorem tensorBaseChangeFixedPointsMap_val_apply (a : A) :
    ((tensorBaseChangeFixedPointsMap (R := R) (G := G) (A := A) a : BaseChangeFixed) :
      BaseChange) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a := rfl

/-- Helper for Lemma 15.111.7: on underlying ring homomorphisms, the fixed-points map followed by
the subtype inclusion is exactly `includeLeft`. -/
private theorem tensorBaseChangeFixedPointsMap_val_comp :
    (show BaseChangeFixed →+* BaseChange from BaseChangeFixed.val).comp
        (show A →+* BaseChangeFixed from tensorBaseChangeFixedPointsMap) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).toRingHom := by
  -- Both routes evaluate to the same tensor after forgetting the fixed-point witness.
  ext a
  simp

-- Proof sketch: tensor the equalizer sequence
-- `0 → R^G → R → ∏_{g ∈ G} R` with the flat `R^G`-algebra `A`; exactness identifies the equalizer
-- with the fixed elements of `A ⊗[R^G] R`, so the canonical map from `A` is an isomorphism.
/-- The canonical map `A → (A ⊗[R^G] R)^G` is bijective when `R^G → A` is flat. -/
private theorem tensorBaseChangeFixedPointsMap_bijective_of_flat_aux [Module.Flat RFix A] :
    Function.Bijective (tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) := by
  classical
  cases nonempty_fintype G
  let ι : RFix →ₗ[RFix] R :=
    { toFun := fun r ↦ r
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c r
        rfl }
  let δ : R →ₗ[RFix] G → R :=
    { toFun := fun r g ↦ g • r - r
      map_add' := by
        intro x y
        ext g
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro c r
        ext g
        change g • ((c : R) * r) - (c : R) * r = (c : R) * (g • r - r)
        rw [show g • ((c : R) * r) = (c : R) * (g • r) by
          change (MulSemiringAction.toRingHom G R g) ((c : R) * r) = (c : R) * (g • r)
          rw [map_mul]
          simpa using congrArg (fun t : R ↦ t * (g • r)) (c.2 g), mul_sub] }
  let Δ : BaseChange →ₗ[RFix] G → BaseChange :=
    { toFun := fun z g ↦ g • z - z
      map_add' := by
        intro x y
        ext g
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro c z
        ext g
        change g • (c • z) - c • z = c • (g • z - z)
        rw [smul_comm g c z, smul_sub] }
  let e : A ⊗[RFix] (G → R) ≃ₗ[RFix] G → BaseChange :=
    TensorProduct.piRight RFix RFix A fun _ : G ↦ R
  have hδ_exact : Function.Exact ι δ := by
    -- The kernel of the action-difference map is exactly the fixed subring.
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext x g
      simp [δ]
    · intro r hr
      refine ⟨⟨r, ?_⟩, rfl⟩
      intro g
      have hg := congrArg (fun v : G → R ↦ v g) hr
      exact sub_eq_zero.mp hg
  have hTensorExact : Function.Exact (ι.lTensor A) (δ.lTensor A) := by
    -- Flatness preserves the exact equalizer sequence after tensoring on the left by `A`.
    simpa [ι, δ] using Module.Flat.lTensor_exact (R := RFix) A hδ_exact
  have hιTensor
      (z : A ⊗[RFix] RFix) :
      (ι.lTensor A) z =
        (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
          ((TensorProduct.rid RFix A) z) := by
    -- The tensorized fixed-subring inclusion is the usual `includeLeft` map after collapsing
    -- the right `RFix`-factor.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a r
      simp [ι, Algebra.TensorProduct.includeLeft_apply, TensorProduct.rid_tmul,
        TensorProduct.tmul_smul]
    · intro x y hx hy
      simp [hx, hy]
  constructor
  · intro x y hxy
    have hxy_base :
        (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) x =
          (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) y := by
      exact congrArg (fun z : BaseChangeFixed ↦ (z : BaseChange)) hxy
    -- Forget the codomain restriction and use injectivity of the tensor inclusion.
    exact (Algebra.TensorProduct.includeLeft_injective
      (R := RFix) (S := A) (A := A) (B := R) (show Function.Injective (algebraMap RFix R) from
        Subtype.val_injective)) hxy_base
  · intro b
    have hbKer : (b : BaseChange) ∈ LinearMap.ker (δ.lTensor A) := by
      rw [LinearMap.mem_ker]
      apply e.injective
      ext g
      -- After the finite-product comparison, the tensorized difference map is the fixed-points
      -- difference map on `A ⊗[R^G] R`.
      refine TensorProduct.induction_on (b : BaseChange) ?_ ?_ ?_
      · simp [δ, Δ, e]
      · intro a r
        simp [δ, Δ, e, tensorBaseChangeRight_smul_tmul, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc]
      · intro x y hx hy
        simp [hx, hy]
    have hbRange :
        (b : BaseChange) ∈ LinearMap.range (ι.lTensor A) := by
      rw [(LinearMap.exact_iff.1 hTensorExact)] at hbKer
      exact hbKer
    rcases hbRange with ⟨z, hz⟩
    refine ⟨(TensorProduct.rid RFix A) z, ?_⟩
    -- Transport the tensor-side preimage back to the canonical fixed-points map.
    apply Subtype.ext
    simpa [tensorBaseChangeFixedPointsMap] using (hιTensor z).symm.trans hz

/-- Lemma 15.111.7 (1): if `R^G → A` is flat, then the canonical map
`A → (A ⊗[R^G] R)^G` is an isomorphism of `R^G`-algebras. -/
noncomputable def tensorBaseChangeFixedPointsEquivOfFlat [Module.Flat RFix A] :
    A ≃ₐ[RFix] BaseChangeFixed :=
  AlgEquiv.ofBijective tensorBaseChangeFixedPointsMap
    tensorBaseChangeFixedPointsMap_bijective_of_flat_aux

/-- The canonical isomorphism of Lemma 15.111.7 (1) acts by the canonical map
`A → (A ⊗[R^G] R)^G`. -/
@[simp] theorem tensorBaseChangeFixedPointsEquivOfFlat_apply [Module.Flat RFix A] (a : A) :
    (tensorBaseChangeFixedPointsEquivOfFlat : A ≃ₐ[RFix] BaseChangeFixed) a =
      tensorBaseChangeFixedPointsMap a := rfl

/-- The canonical map `A → (A ⊗[R^G] R)^G` is bijective when `R^G → A` is flat. -/
theorem tensorBaseChangeFixedPointsMap_bijective_of_flat [Module.Flat RFix A] :
    Function.Bijective (tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) :=
  tensorBaseChangeFixedPointsEquivOfFlat.bijective

-- Proof sketch: every element of `BaseChangeFixed` is fixed by definition, so Lemma `15.111.6`
-- supplies the required polynomial identity with exponent `|G|`; since this holds for every
-- element of the codomain, the Chapter 10 shift-power generation owner predicate follows
-- directly.
/-- The canonical map `A → (A ⊗[R^G] R)^G` satisfies the shift-power generation hypothesis from
Lemma `10.46.11`. -/
theorem tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating :
    (f).ShiftPowerPolynomialImageGenerating := by
  let f0 : A →+* BaseChangeFixed := tensorBaseChangeFixedPointsMap
  let _ : Algebra A BaseChangeFixed := f0.toAlgebra
  -- Every fixed tensor already satisfies the orbit-polynomial identity from Lemma `15.111.6`.
  apply top_unique
  intro b _
  obtain ⟨P, -, hPmap⟩ :=
    exists_monic_polynomial_over_baseChange_eq_X_sub_C_pow_of_fixed
      (R := R) (G := G) (A := A) b
  refine Algebra.subset_adjoin ⟨Nat.card G, Nat.card_pos, P, ?_⟩
  apply (Polynomial.map_injective (show BaseChangeFixed →+* BaseChange from BaseChangeFixed.val)
    Subtype.val_injective)
  calc
    Polynomial.map (show BaseChangeFixed →+* BaseChange from BaseChangeFixed.val)
        (Polynomial.map f0 P) =
      Polynomial.map
        ((show BaseChangeFixed →+* BaseChange from BaseChangeFixed.val).comp f0) P := by
          rw [Polynomial.map_map]
    _ =
        Polynomial.map ((Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).toRingHom) P :=
          by
            -- Route correction: rewrite the codomain restriction through the subtype inclusion
            -- before using the polynomial identity from Lemma `15.111.6`.
            rw [tensorBaseChangeFixedPointsMap_val_comp (R := R) (G := G) (A := A)]
    _ = (X - C (b : BaseChange)) ^ Nat.card G := by
          simpa using hPmap
    _ = Polynomial.map (show BaseChangeFixed →+* BaseChange from BaseChangeFixed.val)
          ((X - C b) ^ Nat.card G) := by
          simp

-- Proof sketch: apply Lemma `15.111.6 (2)` to any kernel element of
-- `A → (A ⊗[R^G] R)^G`; the resulting identity `(X - C a)^|G| = X^|G|` forces `a^|G| = 0`, so
-- every kernel element is nilpotent.
theorem tensorBaseChangeFixedPointsMap_ker_isLocallyNilpotent :
    (ker f).IsLocallyNilpotent := by
  rw [Ideal.isLocallyNilpotent_iff]
  intro a ha
  have ha_zero :
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a = 0 := by
    -- Forget the codomain restriction to read the kernel condition in `A ⊗[R^G] R`.
    simpa [tensorBaseChangeFixedPointsMap] using
      congrArg (fun z : BaseChangeFixed ↦ (z : BaseChange)) ha
  have hpow :=
    kernelElement_X_sub_pow_eq_X_pow_of_baseChange
      (R := R) (G := G) (A := A) ⟨a, ha_zero⟩
  -- Evaluate at `0` to read off the nilpotent power of `a`.
  have heval := congrArg (fun p : Polynomial A ↦ p.eval 0) hpow
  have hneg_nil : IsNilpotent (-a) := by
    have hneg_pow : (-a) ^ Nat.card G = 0 ^ Nat.card G := by
      simpa [sub_eq_add_neg] using heval
    have hzero_pow : (0 : A) ^ Nat.card G = 0 := by
      exact zero_pow (Nat.card_pos.ne')
    exact ⟨Nat.card G, hneg_pow.trans hzero_pow⟩
  exact isNilpotent_neg_iff.mp hneg_nil

-- Proof sketch: for an invariant element of `A ⊗[R^G] R`, Lemma `15.111.6` supplies a monic
-- polynomial over `A` annihilating it, so every element of `(A ⊗[R^G] R)^G` is integral over `A`.
/-- Lemma 15.111.7 (2): the canonical map `A → (A ⊗[R^G] R)^G` is integral. -/
theorem tensorBaseChangeFixedPointsMap_isIntegral :
    (f).IsIntegral := by
  exact isIntegral_of_shiftPowerPolynomialImageGenerating f
    tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating

-- Proof sketch: the same orbit-polynomial argument gives the shift-power generation hypothesis,
-- and the positive-power bridge from Lemma `10.46.11`; together with local nilpotence of the
-- kernel, the canonical owner theorem `PrimeSpectrum.isHomeomorph_comap` applies directly.
/-- Lemma 15.111.7 (3): the induced map
`Spec((A ⊗[R^G] R)^G) → Spec(A)` is a homeomorphism. -/
theorem tensorBaseChangeFixedPointsMap_isHomeomorph_comap :
    IsHomeomorph (comap f) := by
  exact isHomeomorph_comap f
    (exists_pow_mem_range_of_shiftPowerPolynomialImageGenerating f
      tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating)
    tensorBaseChangeFixedPointsMap_ker_isLocallyNilpotent

-- Proof sketch: this is the residue-field clause of the Chapter 10 owner theorem applied to the
-- shift-power bridge above.
/-- Lemma 15.111.7 (4): the canonical map `A → (A ⊗[R^G] R)^G` induces purely inseparable
extensions on residue fields. -/
theorem tensorBaseChangeFixedPointsMap_hasPurelyInseparableResidueFieldExtensions :
    (f).HasPurelyInseparableResidueFieldExtensions := by
  exact hasPurelyInseparableResidueFieldExtensions_of_shiftPowerPolynomialImageGenerating f
    tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating

end
