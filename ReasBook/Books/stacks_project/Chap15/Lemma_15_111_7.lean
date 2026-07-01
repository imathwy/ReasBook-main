import Mathlib
import stacks_project.Chap10.Lemma_10_46_11
import stacks_project.Chap15.Lemma_15_111_6

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum RingHom
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

-- Proof sketch: the induced endomorphism on `A ⊗[R^G] R` acts trivially on the left tensor factor,
-- so it fixes every element coming from `A` through `includeLeft`.
/-- The canonical map `A → A ⊗[R^G] R` lands in the fixed part of the base-changed tensor
product. -/
theorem tensorBaseChange_includeLeft_mem_fixedPoints (a : A) :
    (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a ∈ BaseChangeFixed := sorry

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

-- Proof sketch: tensor the equalizer sequence
-- `0 → R^G → R → ∏_{g ∈ G} R` with the flat `R^G`-algebra `A`; exactness identifies the equalizer
-- with the fixed elements of `A ⊗[R^G] R`, so the canonical map from `A` is an isomorphism.
/-- The canonical map `A → (A ⊗[R^G] R)^G` is bijective when `R^G → A` is flat. -/
private theorem tensorBaseChangeFixedPointsMap_bijective_of_flat_aux [Module.Flat RFix A] :
    Function.Bijective (tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) := sorry

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
    (f).ShiftPowerPolynomialImageGenerating := sorry

-- Proof sketch: apply Lemma `15.111.6 (2)` to any kernel element of
-- `A → (A ⊗[R^G] R)^G`; the resulting identity `(X - C a)^|G| = X^|G|` forces `a^|G| = 0`, so
-- every kernel element is nilpotent.
theorem tensorBaseChangeFixedPointsMap_ker_isLocallyNilpotent :
    (ker f).IsLocallyNilpotent := sorry

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
