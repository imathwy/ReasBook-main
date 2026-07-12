import Mathlib
import StacksProject_2024.Chap15.Lemma_15_90_3
import StacksProject_2024.Chap15.«15_91_9_1»
import StacksProject_2024.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped IdealPowerTorsion

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo module glueability, expressed through the module Cech short
  complex and the canonical tensor base-change map on `(f)^∞`-torsion;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `TensorProduct.comm`,
  `IsBeauvilleLaszloGlueingPairAlong`;
- best owner abstraction: the primitive comparison map is the chapter owner
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`, i.e. the canonical tensor
  base-change unit restricted to the primary component for `(f)`;
- primitive data vs derived API: the primitive data are the module Cech short complex and the
  canonical primary-component base-change map; the injectivity, surjectivity, and glueability
  criteria are derived API.

Source/core/bridge triage:
- `source-facing`: the Beauville-Laszlo exactness criteria for modules;
- `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact` and
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`;
- `bridge/view`: the textbook right-tensor order `M ⊗[R] R'`, related by tensor symmetry to the
  canonical owner `R' ⊗[R] M`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: tensor the right exact ring sequence `R → R' → R'_f` with `M`. Right exactness of
-- `M ⊗[R] -` turns the surjectivity statement from Lemma `15.91.6` into surjectivity of the
-- module-side right map.
/-- The module Beauville-Laszlo sequence is exact on the right under the quotient-isomorphism
hypothesis. -/
theorem beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Surjective ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
  -- First tensor the ring-side surjectivity statement with `M`.
  have hring :
      Function.Surjective ((beauvilleLaszloCechSequence (algebraMap R R') f).g.hom) := by
    simpa [beauvilleLaszloCechSequence] using
      (beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
        (φ := algebraMap R R') (f := f) hquot)
  have htensor :
      Function.Surjective ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
    simpa [beauvilleLaszloModuleCechTensorImage] using
      (LinearMap.rTensor_surjective M
        (g := (beauvilleLaszloCechSequence (algebraMap R R') f).g.hom)
        hring)
  -- Then transport surjectivity across the displayed middle isomorphism.
  change Function.Surjective (beauvilleLaszloModuleCechBeta R' M f)
  intro z
  rcases htensor z with ⟨y, rfl⟩
  refine ⟨(beauvilleLaszloModuleCechMiddleIso R' M f).hom y, ?_⟩
  -- The transported right map is the tensor-image right map after undoing the middle isomorphism.
  simp [beauvilleLaszloModuleCechBeta]

/-- Helper for Lemma 15.91.10: for any module over a commutative ring, the kernel of the
localization map away from `a` is exactly the `a^∞`-torsion submodule. -/
theorem mem_fPowerTorsion_iff_localizedAway_eq_zero
    {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N]
    (a : A) (x : N) :
    x ∈ (N[a^∞] : Submodule A N) ↔
      (LocalizedModule.mkLinearMap (Submonoid.powers a) N) x = 0 := by
  -- Identify `N[a^∞]` with the torsion submodule cut out by powers of `a`.
  rw [Submodule.mem_torsion'_iff (Submonoid.powers a) x]
  constructor
  · rintro ⟨s, hsx⟩
    -- A torsion relation gives a localization-kernel witness with denominator `s`.
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers a) N).ker
    exact (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers a) (m := x)).2 ⟨s, s.2, hsx⟩
  · intro hx
    -- Conversely, vanishing in the localization comes from some power of `a` killing `x`.
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers a) N).ker at hx
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers a) (m := x)).1 hx with ⟨s, hs, hsx⟩
    exact ⟨⟨s, hs⟩, hsx⟩

/-- Helper for Lemma 15.91.10: under the standard identification
`M ⊗[R] Localization.Away f ≃ LocalizedModule.Away f M`, the pure tensor `x ⊗ 1`
is the localized generator of `x`. -/
theorem tensor_localizationAway_eq_mkLinearMap
    (f : R) (x : M) :
    let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
      (TensorProduct.comm R M (Localization.Away f)).trans
        ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
    e (x ⊗ₜ[R] (1 : Localization.Away f)) =
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x := by
  -- Rewrite the right-ordered pure tensor through tensor symmetry and the standard
  -- localization/tensor equivalence.
  change (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
      (Localization.mk (1 : R) (1 : Submonoid.powers f) ⊗ₜ[R] x) =
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x
  simpa [LocalizedModule.mkLinearMap_apply] using
    (LocalizedModule.equivTensorProduct_symm_apply_tmul
      (S := Submonoid.powers f)
      (M := M)
      (x := x)
      (r := (1 : R))
      (s := (1 : Submonoid.powers f)))

-- Proof sketch: the generic localization-kernel lemma above identifies `M[f^∞]` with the kernel
-- of `M → M_f`, and the tensor/localization equivalence rewrites the localization image of `x`
-- as the pure tensor `x ⊗ 1`.
/-- Helper for Lemma 15.91.10: an element of `M` is `f`-power torsion exactly when its canonical
pure tensor `x ⊗ 1` vanishes in `M ⊗[R] Localization.Away f`. -/
theorem mem_fPowerTorsion_iff_tensor_localization_eq_zero
    (f : R) (x : M) :
    x ∈ (M[f^∞] : Submodule R M) ↔
      x ⊗ₜ[R] (1 : Localization.Away f) = 0 := by
  let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
    (TensorProduct.comm R M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
  constructor
  · intro hx
    -- Transport torsion to localization and then back through the tensor/localization equivalence.
    apply e.injective
    rw [tensor_localizationAway_eq_mkLinearMap (R := R) (M := M) (f := f) (x := x)]
    exact (mem_fPowerTorsion_iff_localizedAway_eq_zero (a := f) (x := x)).1 hx
  · intro hx
    -- Vanishing of `x ⊗ 1` forces the localization image of `x` to vanish, hence `x` is torsion.
    have hloc :
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x = 0 := by
      rw [← tensor_localizationAway_eq_mkLinearMap (R := R) (M := M) (f := f) (x := x)]
      exact congrArg e hx
    exact (mem_fPowerTorsion_iff_localizedAway_eq_zero (a := f) (x := x)).2 hloc

/-- Helper for Lemma 15.91.10: every element of `M ⊗[R] Localization.Away f` is represented by a
single power denominator in the canonical `LocalizedModule` model. -/
theorem tensor_localizationAway_exists_power_denominator
    (f : R) (z : M ⊗[R] Localization.Away f) :
    let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
      (TensorProduct.comm R M (Localization.Away f)).trans
        ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
    ∃ n : ℕ, ∃ m : M,
      e z = LocalizedModule.mk m ⟨f ^ n, by exact ⟨n, rfl⟩⟩ := by
  let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
    (TensorProduct.comm R M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
  -- Use surjectivity of the localization map to choose one denominator in the canonical model.
  rcases IsLocalizedModule.surj (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) (e z) with ⟨⟨m, s⟩, hs⟩
  rcases s.2 with ⟨n, hn⟩
  refine ⟨n, m, ?_⟩
  -- Rewrite the chosen denominator as an actual power of `f`, then package it as `mk m / f^n`.
  rw [IsLocalizedModule.mk_eq_mk']
  symm
  apply (IsLocalizedModule.mk'_eq_iff).2
  simpa [LocalizedModule.mkLinearMap_apply, hn] using hs.symm

/-- Helper for Lemma 15.91.10: the first component of the displayed left Beauville-Laszlo map is
the canonical pure tensor in `M ⊗[R] R'`. -/
theorem moduleCechAlpha_fst_eq_tensor_baseChange_unit
    (f : R) (x : M) :
    Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x) = x ⊗ₜ[R] (1 : R') := by
  -- Route correction: first expose the two coordinates of `beauvilleLaszloModuleCechAlpha`
  -- explicitly, and only then compare them with the canonical torsion map.
  simp [beauvilleLaszloModuleCechAlpha, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechLeftIso, beauvilleLaszloModuleCechMiddleIso,
    beauvilleLaszloModuleCechCanonicalMiddleIso, beauvilleLaszloModuleCechMiddleTensorIso,
    beauvilleLaszloModuleCechMiddleTensor_eq, beauvilleLaszloCechLeftMap,
    tensorLeft_obj_tensorProductIso]

/-- Helper for Lemma 15.91.10: the second component of the displayed left Beauville-Laszlo map is
the canonical localization tensor `x ⊗ 1`. -/
theorem moduleCechAlpha_snd_eq_tensor_localization_unit
    (f : R) (x : M) :
    Prod.snd (beauvilleLaszloModuleCechAlpha R' M f x) =
      x ⊗ₜ[R] (1 : Localization.Away f) := by
  -- Read off the localization factor from the explicit transported tensor-image map.
  simp [beauvilleLaszloModuleCechAlpha, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechLeftIso, beauvilleLaszloModuleCechMiddleIso,
    beauvilleLaszloModuleCechCanonicalMiddleIso, beauvilleLaszloModuleCechMiddleTensorIso,
    beauvilleLaszloModuleCechMiddleTensor_eq, beauvilleLaszloCechLeftMap,
    tensorLeft_obj_tensorProductIso]

/-- Helper for Lemma 15.91.10: on the principal-primary component, the canonical restricted
base-change map agrees with the first Beauville-Laszlo Cech component after tensor symmetry. -/
theorem tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
    (f : R) (x : (M[(principalIdeal f)^∞] : Submodule R M)) :
    (TensorProduct.comm R R' M)
        ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M x : R' ⊗[R] M)) =
      Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x) := by
  -- The restricted base-change map is still the pure tensor `1 ⊗ x`; `TensorProduct.comm`
  -- rewrites it to the first displayed Cech coordinate.
  simpa [tensorBaseChangeUnitPrimaryComponent,
    moduleCechAlpha_fst_eq_tensor_baseChange_unit]

-- Proof sketch: the kernel of `M → M ⊗[R] Localization.Away f` is `M[f^∞]`. Therefore the left
-- Cech map is injective exactly when the comparison map from `M[f^∞]` to the `f^∞`-torsion of
-- `R' ⊗[R] M` is injective; via tensor symmetry this is the usual map to `(M ⊗[R] R')[f^∞]`.
-- TODO: prove the module analogue of Lemma `15.91.6` on the left by identifying
-- `ker (M → M ⊗[R] Localization.Away f)` with `M[f^∞]` and transporting the target torsion
-- submodule across `TensorProduct.comm`.
/-- The module Beauville-Laszlo sequence is exact on the left exactly when the canonical
base-change map on `(f)^∞`-torsion is injective. -/
theorem beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
    (f : R) :
    Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := by
  constructor
  · intro hleft
    intro x y hxy
    apply Subtype.ext
    apply hleft
    ext
    · -- Compare the first coordinates through the canonical restricted base-change map.
      have hxy_val :
          ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M x : R' ⊗[R] M)) =
            (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M y : R' ⊗[R] M) :=
        congrArg Subtype.val hxy
      calc
        Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x)
            =
              (TensorProduct.comm R R' M)
                ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M x :
                  R' ⊗[R] M)) := by
                  symm
                  exact
                    tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
                      (R := R) (R' := R') (M := M) f x
        _ =
              (TensorProduct.comm R R' M)
                ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M y :
                  R' ⊗[R] M)) := by
                  simpa using congrArg (TensorProduct.comm R R' M) hxy_val
        _ = Prod.fst (beauvilleLaszloModuleCechAlpha R' M f y) := by
              exact
                tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
                  (R := R) (R' := R') (M := M) f y
    · -- Both torsion inputs have zero localization coordinate.
      have hxmem : (x : M) ∈ (M[f^∞] : Submodule R M) := by
        simpa [Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := M) f] using x.2
      have hymem : (y : M) ∈ (M[f^∞] : Submodule R M) := by
        simpa [Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := M) f] using y.2
      have hx0 :
          Prod.snd (beauvilleLaszloModuleCechAlpha R' M f x) = 0 := by
        rw [moduleCechAlpha_snd_eq_tensor_localization_unit]
        exact (mem_fPowerTorsion_iff_tensor_localization_eq_zero (R := R) (M := M) f x).1 hxmem
      have hy0 :
          Prod.snd (beauvilleLaszloModuleCechAlpha R' M f y) = 0 := by
        rw [moduleCechAlpha_snd_eq_tensor_localization_unit]
        exact (mem_fPowerTorsion_iff_tensor_localization_eq_zero (R := R) (M := M) f y).1 hymem
      exact hx0.trans hy0.symm
  · intro htors
    intro x y hxy
    -- Use the localization coordinate to place `x - y` in the principal-primary component.
    have hsnd_eq :
        x ⊗ₜ[R] (1 : Localization.Away f) = y ⊗ₜ[R] (1 : Localization.Away f) := by
      simpa [moduleCechAlpha_snd_eq_tensor_localization_unit] using congrArg Prod.snd hxy
    have htors_mem : x - y ∈ (M[f^∞] : Submodule R M) := by
      apply
        (mem_fPowerTorsion_iff_tensor_localization_eq_zero (R := R) (M := M) f (x - y)).2
      simpa [sub_tmul] using
        (sub_eq_zero.mpr hsnd_eq :
          x ⊗ₜ[R] (1 : Localization.Away f) -
              y ⊗ₜ[R] (1 : Localization.Away f) =
            0)
    have hprimary : x - y ∈ (M[(principalIdeal f)^∞] : Submodule R M) := by
      simpa [Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := M) f] using htors_mem
    let z : (M[(principalIdeal f)^∞] : Submodule R M) := ⟨x - y, hprimary⟩
    -- Then the first coordinate shows that the torsion comparison kills `x - y`.
    have hfst_eq :
        Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x) =
          Prod.fst (beauvilleLaszloModuleCechAlpha R' M f y) := by
      simpa using congrArg Prod.fst hxy
    have hfst_zero :
        Prod.fst (beauvilleLaszloModuleCechAlpha R' M f (x - y)) = 0 := by
      simpa [map_sub] using
        (sub_eq_zero.mpr hfst_eq :
          Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x) -
              Prod.fst (beauvilleLaszloModuleCechAlpha R' M f y) =
            0)
    have hz_zero :
        tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M z = 0 := by
      apply Subtype.ext
      apply (TensorProduct.comm R R' M).injective
      calc
        (TensorProduct.comm R R' M)
            ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M z : R' ⊗[R] M))
            =
              Prod.fst (beauvilleLaszloModuleCechAlpha R' M f (x - y)) := by
                exact
                  tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
                    (R := R) (R' := R') (M := M) f z
        _ = 0 := hfst_zero
    have hz : z = 0 := htors hz_zero
    exact sub_eq_zero.mp <| congrArg Subtype.val hz

-- Proof sketch: if the sequence is exact in the middle, then an `f^∞`-torsion element of
-- `R' ⊗[R] M` yields a kernel element of the right map and so comes from `M`. Conversely,
-- surjectivity on `f^∞`-torsion lets one lift the torsion correction needed to express a kernel
-- element of the right map as the image of an element of `M`.
/-- Helper for Lemma 15.91.10: the displayed right Beauville-Laszlo map is the difference between
the two canonical overlap maps on the `R'`- and `R_f`-coordinates. -/
theorem moduleCechBeta_apply_explicit
    (f : R) (y : M ⊗[R] R') (z : M ⊗[R] Localization.Away f) :
    beauvilleLaszloModuleCechBeta R' M f (y, z) =
      (TensorProduct.map
          (LinearMap.id : M →ₗ[R] M)
          ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R)) y -
        (TensorProduct.map
          (LinearMap.id : M →ₗ[R] M)
          ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap)) z := by
  -- Route correction: normalize `beauvilleLaszloModuleCechBeta` once to the concrete
  -- tensor-image right map, and then read off the two product coordinates.
  simp [beauvilleLaszloModuleCechBeta, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechMiddleIso, beauvilleLaszloModuleCechCanonicalMiddleIso,
    beauvilleLaszloModuleCechMiddleTensorIso, beauvilleLaszloModuleCechMiddleTensor_eq,
    beauvilleLaszloCechRightMap, tensorLeft_obj_tensorProductIso]

/-- Helper for Lemma 15.91.10: after clearing any chosen power denominator in the localization
coordinate, the kernel relation for `(y, z)` becomes an overlap-vanishing statement for the
corrected first coordinate. -/
theorem kernel_first_coordinate_error_overlap_eq_zero_of_moduleCechBeta_eq_zero
    (f : R) {y : M ⊗[R] R'} {z : M ⊗[R] Localization.Away f} {n : ℕ} {m : M}
    (hker : beauvilleLaszloModuleCechBeta R' M f (y, z) = 0)
    (hden : ((f ^ n : R) • z) = m ⊗ₜ[R] (1 : Localization.Away f)) :
    (TensorProduct.map
        (LinearMap.id : M →ₗ[R] M)
        ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R))
      (((f ^ n : R) • y) -
        Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) = 0 := by
  let overlapFromBaseChange :
      M ⊗[R] R' →ₗ[R] M ⊗[R] Localization.Away (algebraMap R R' f) :=
    TensorProduct.map
      (LinearMap.id : M →ₗ[R] M)
      ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R)
  let overlapFromLocalization :
      M ⊗[R] Localization.Away f →ₗ[R] M ⊗[R] Localization.Away (algebraMap R R' f) :=
    TensorProduct.map
      (LinearMap.id : M →ₗ[R] M)
      ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap)
  have hker_eq : overlapFromBaseChange y = overlapFromLocalization z := by
    -- Read the kernel equation as equality of the two overlap coordinates.
    rw [moduleCechBeta_apply_explicit (R := R) (R' := R') (M := M) (f := f) y z] at hker
    exact sub_eq_zero.mp hker
  -- Proof comment: multiply the kernel equality by `f^n`, substitute the cleared
  -- denominator expression for `z`, and compare with the explicit first Cech coordinate.
  calc
    overlapFromBaseChange
        (((f ^ n : R) • y) -
          Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) =
      (f ^ n : R) • overlapFromBaseChange y -
        overlapFromBaseChange
          (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) := by
            simp [overlapFromBaseChange]
    _ =
      (f ^ n : R) • overlapFromLocalization z -
        overlapFromBaseChange
          (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) := by
            rw [hker_eq]
    _ =
      overlapFromLocalization (((f ^ n : R) • z)) -
        overlapFromBaseChange
          (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) := by
            simp [overlapFromLocalization]
    _ =
      overlapFromLocalization (m ⊗ₜ[R] (1 : Localization.Away f)) -
        overlapFromBaseChange
          (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f m)) := by
            rw [hden]
    _ = 0 := by
      rw [moduleCechAlpha_fst_eq_tensor_baseChange_unit (R := R) (R' := R') (M := M)
        (f := f) (x := m)]
      simp [overlapFromBaseChange, overlapFromLocalization]

/-- Helper for Lemma 15.91.10: quotient-bijectivity modulo `f^n` lifts any first Cech coordinate
up to an `f^n`-multiple remainder. -/
theorem exists_preimage_mod_fpow_first_component
    (f : R) (n : ℕ+)
    (hbij : Function.Bijective (principalPowerIdealImageQuotientMap (algebraMap R R') f n))
    (y : M ⊗[R] R') :
    ∃ x : M, ∃ r : M ⊗[R] R',
      y = Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x) + (f ^ (n : ℕ) : R) • r := by
  -- Follow the source proof: first lift pure tensors modulo `f^n`, then extend by tensor
  -- additivity to arbitrary elements of `M ⊗[R] R'`.
  induction y using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, 0, ?_⟩
      -- The zero tensor is already the first coordinate of the zero preimage.
      simp [moduleCechAlpha_fst_eq_tensor_baseChange_unit]
  | tmul m a =>
      rcases exists_lift_remainder_of_principalPowerQuotient_surjective
          (φ := algebraMap R R') (f := f) (n := n) a hbij with ⟨x, z, hz⟩
      refine ⟨x • m, m ⊗ₜ[R] z, ?_⟩
      -- Rewrite the scalar coefficient modulo `f^n`, then move the scalar to the first tensor
      -- factor to match the explicit first Cech coordinate.
      calc
        m ⊗ₜ[R] a =
            m ⊗ₜ[R] (algebraMap R R' x + (algebraMap R R' f) ^ (n : ℕ) * z) := by
              rw [hz]
        _ = m ⊗ₜ[R] (algebraMap R R' x) +
              m ⊗ₜ[R] ((algebraMap R R' f) ^ (n : ℕ) * z) := by
              rw [TensorProduct.tmul_add]
        _ = Prod.fst (beauvilleLaszloModuleCechAlpha R' M f (x • m)) +
              (f ^ (n : ℕ) : R) • (m ⊗ₜ[R] z) := by
              rw [moduleCechAlpha_fst_eq_tensor_baseChange_unit]
              congr 1
              · calc
                  m ⊗ₜ[R] (algebraMap R R' x) = m ⊗ₜ[R] (x • (1 : R')) := by
                    simp [Algebra.smul_def]
                  _ = x • (m ⊗ₜ[R] (1 : R')) := by
                    simpa using
                      (TensorProduct.tmul_smul (R := R) (r := x) (x := m) (y := (1 : R')))
                  _ = (x • m) ⊗ₜ[R] (1 : R') := by
                    simpa using
                      (TensorProduct.smul_tmul' (R := R) (r := x) (m := m) (n := (1 : R')))
              · calc
                  m ⊗ₜ[R] ((algebraMap R R' f) ^ (n : ℕ) * z) =
                      m ⊗ₜ[R] ((f ^ (n : ℕ) : R) • z) := by
                        simp [Algebra.smul_def, map_pow]
                  _ = (f ^ (n : ℕ) : R) • (m ⊗ₜ[R] z) := by
                        rw [TensorProduct.tmul_smul]
  | add y₁ y₂ hy₁ hy₂ =>
      rcases hy₁ with ⟨x₁, r₁, hr₁⟩
      rcases hy₂ with ⟨x₂, r₂, hr₂⟩
      refine ⟨x₁ + x₂, r₁ + r₂, ?_⟩
      -- Combine the two already-lifted summands and use linearity of the first Cech coordinate.
      calc
        y₁ + y₂ =
            (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x₁) + (f ^ (n : ℕ) : R) • r₁) +
              (Prod.fst (beauvilleLaszloModuleCechAlpha R' M f x₂) +
                (f ^ (n : ℕ) : R) • r₂) := by
                  rw [hr₁, hr₂]
        _ = Prod.fst (beauvilleLaszloModuleCechAlpha R' M f (x₁ + x₂)) +
              (f ^ (n : ℕ) : R) • (r₁ + r₂) := by
                simp [map_add, add_assoc, add_left_comm, add_comm, smul_add]

/-- Helper for Lemma 15.91.10: the overlap image of an `f^∞`-torsion element in `M ⊗[R] R'`
vanishes after localizing away from `f`. -/
theorem tensor_overlap_map_eq_zero_of_mem_fPowerTorsion
    (f : R) {y : M ⊗[R] R'}
    (hy : y ∈ ((M ⊗[R] R')[f^∞] : Submodule R (M ⊗[R] R'))) :
    (TensorProduct.map
        (LinearMap.id : M →ₗ[R] M)
        ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R)) y = 0 := by
  -- Expand the torsion witness and cancel the resulting invertible power of `f` in the overlap.
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f) y] at hy
  rcases hy with ⟨a, ha⟩
  rcases a.2 with ⟨n, rfl⟩
  let overlapMap :
      M ⊗[R] R' →ₗ[R] M ⊗[R] Localization.Away (algebraMap R R' f) :=
    TensorProduct.map
      (LinearMap.id : M →ₗ[R] M)
      ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R)
  have hsmul :
      (f ^ n : R) • overlapMap y = 0 := by
    -- Map the torsion relation into the overlap tensor product.
    simpa [overlapMap] using congrArg overlapMap ha
  have hsmul' :
      (algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n)) • overlapMap y = 0 := by
    -- Rewrite the `R`-scalar action in the codomain through the overlap ring.
    simpa [Algebra.smul_def] using hsmul
  have hunit :
      IsUnit (algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n)) := by
    -- Every power of `f` becomes a unit after passing to the overlap localization.
    have hunit' :
        IsUnit
          (algebraMap R' (Localization.Away (algebraMap R R' f))
            ((algebraMap R R' f) ^ n)) := by
      have hpow : (algebraMap R R' f) ^ n ∈ Submonoid.powers (algebraMap R R' f) := ⟨n, rfl⟩
      simpa using
        (IsLocalization.map_units (Localization.Away (algebraMap R R' f))
          ⟨(algebraMap R R' f) ^ n, hpow⟩)
    simpa [map_pow] using hunit'
  rcases hunit with ⟨u, hu⟩
  -- Multiply by the inverse unit to cancel the overlap scalar.
  calc
    overlapMap y = (1 : Localization.Away (algebraMap R R' f)) • overlapMap y := by simp
    _ = (u * algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n)) • overlapMap y := by
      rw [hu, one_smul]
    _ = u • ((algebraMap R (Localization.Away (algebraMap R R' f)) (f ^ n)) • overlapMap y) := by
      rw [mul_smul]
    _ = 0 := by simp [hsmul']

/-- Helper for Lemma 15.91.10: tensor symmetry carries `f^∞`-torsion in `R' ⊗[R] M` to
`f^∞`-torsion in `M ⊗[R] R'`. -/
theorem tensorProduct_comm_mem_fPowerTorsion
    (f : R) {y : R' ⊗[R] M}
    (hy :
      y ∈ ((((R' ⊗[R] M)[((principalIdeal f).map (algebraMap R R'))^∞] :
        Submodule R' (R' ⊗[R] M)).restrictScalars R))) :
    (TensorProduct.comm R R' M y) ∈
      ((M ⊗[R] R')[f^∞] : Submodule R (M ⊗[R] R')) := by
  -- Rewrite the target primary component as `((algebraMap f)^∞)`-torsion and transport the
  -- witness across tensor symmetry.
  have hy' :
      y ∈ (((R' ⊗[R] M)[(algebraMap R R' f)^∞] :
        Submodule R' (R' ⊗[R] M)).restrictScalars R) := by
    simpa [principalIdeal, Ideal.map_span, Set.image_singleton,
      Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := R' ⊗[R] M)
        (f := algebraMap R R' f)] using hy
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f), Submodule.mem_torsion'_iff
    (Submonoid.powers (algebraMap R R' f))] at hy' ⊢
  rcases hy' with ⟨a, ha⟩
  rcases a.2 with ⟨n, rfl⟩
  refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
  -- Apply tensor symmetry to the `((algebraMap f)^n)`-torsion relation.
  have hcomm := congrArg (TensorProduct.comm R R' M) ha
  simpa [map_smul, Algebra.smul_def, map_pow] using hcomm

/-- Helper for Lemma 15.91.10: tensor symmetry carries `f^∞`-torsion in `M ⊗[R] R'` back to the
principal-primary component in `R' ⊗[R] M`. -/
theorem tensorProduct_comm_symm_mem_primaryComponent_of_mem_fPowerTorsion
    (f : R) {y : M ⊗[R] R'}
    (hy : y ∈ ((M ⊗[R] R')[f^∞] : Submodule R (M ⊗[R] R'))) :
    (TensorProduct.comm R R' M).symm y ∈
      ((((R' ⊗[R] M)[((principalIdeal f).map (algebraMap R R'))^∞] :
        Submodule R' (R' ⊗[R] M)).restrictScalars R)) := by
  -- Rewrite the target primary component as `((algebraMap f)^∞)`-torsion and transport the
  -- witness back through tensor symmetry.
  have hy' :
      y ∈ (((M ⊗[R] R')[(algebraMap R R' f)^∞] :
        Submodule R' (M ⊗[R] R')).restrictScalars R) := by
    simpa [Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := M ⊗[R] R')
      (f := algebraMap R R' f)] using hy
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f),
    Submodule.mem_torsion'_iff (Submonoid.powers (algebraMap R R' f))] at hy' ⊢
  rcases hy' with ⟨a, ha⟩
  rcases a.2 with ⟨n, rfl⟩
  refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
  -- Apply tensor symmetry in the reverse direction to the transported torsion relation.
  have hcomm := congrArg (TensorProduct.comm R R' M).symm ha
  simpa [map_smul, Algebra.smul_def, map_pow, principalIdeal, Ideal.map_span, Set.image_singleton,
    Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := R' ⊗[R] M)
      (f := algebraMap R R' f)] using hcomm

/-- Helper for Lemma 15.91.10: middle exactness of the module Beauville-Laszlo sequence forces
surjectivity of the canonical base-change map on `(f)^∞`-torsion. -/
theorem fPowerTorsionToTensor_surjective_of_beauvilleLaszloModuleCech_exact
    (f : R)
    (hexact :
      Function.Exact
        ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
        ((beauvilleLaszloModuleCechSequence R' M f).g.hom)) :
    Function.Surjective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := by
  intro y
  let ycomm : M ⊗[R] R' := (TensorProduct.comm R R' M) (y : R' ⊗[R] M)
  have hycomm_tors :
      ycomm ∈ ((M ⊗[R] R')[f^∞] : Submodule R (M ⊗[R] R')) := by
    -- Move the given target torsion class to the first Cech coordinate.
    exact tensorProduct_comm_mem_fPowerTorsion (R := R) (R' := R') (M := M) f y.2
  have hkernel :
      (beauvilleLaszloModuleCechSequence R' M f).g.hom (ycomm, 0) = 0 := by
    -- The localization coordinate is zero, and the first coordinate dies in the overlap because
    -- it is `f^∞`-torsion.
    rw [show (beauvilleLaszloModuleCechSequence R' M f).g.hom =
        beauvilleLaszloModuleCechBeta R' M f from rfl]
    rw [moduleCechBeta_apply_explicit (R := R) (R' := R') (M := M) (f := f) ycomm 0]
    simp [tensor_overlap_map_eq_zero_of_mem_fPowerTorsion (R := R) (R' := R') (M := M) f
      hycomm_tors]
  rcases hexact (ycomm, 0) hkernel with ⟨x, hx⟩
  have hx_tors :
      x ∈ (M[f^∞] : Submodule R M) := by
    -- The second Cech coordinate of the chosen preimage is zero, so `x` is torsion.
    have hsnd :
        Prod.snd (beauvilleLaszloModuleCechAlpha R' M f x) = 0 := by
      simpa using congrArg Prod.snd hx
    rw [moduleCechAlpha_snd_eq_tensor_localization_unit] at hsnd
    exact (mem_fPowerTorsion_iff_tensor_localization_eq_zero (R := R) (M := M) f x).2 hsnd
  let xtors : (M[(principalIdeal f)^∞] : Submodule R M) := by
    refine ⟨x, ?_⟩
    simpa [Module.primaryComponent_principalIdeal_eq_fPowerTorsion (M := M) f] using hx_tors
  refine ⟨xtors, ?_⟩
  apply Subtype.ext
  apply (TensorProduct.comm R R' M).injective
  -- Compare the first Cech coordinate of the exactness preimage with the prescribed torsion class.
  calc
    (TensorProduct.comm R R' M)
        ((tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M xtors : R' ⊗[R] M)) =
      Prod.fst (beauvilleLaszloModuleCechAlpha R' M f xtors) := by
        exact
          tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
            (R := R) (R' := R') (M := M) f xtors
    _ = ycomm := by
      simpa using congrArg Prod.fst hx
    _ = (TensorProduct.comm R R' M) (y : R' ⊗[R] M) := rfl

/-- Helper for Lemma 15.91.10: rewrite the principal-power quotient comparison into the generic
`Ideal.quotientMap` form needed by the ideal-power-torsion tensor base-change theorem. -/
theorem principal_power_quotientMap_bijective
    (f : R) (n : ℕ+)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Bijective
      (Ideal.quotientMap
        (((principalIdeal f) ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map) := by
  let I : Ideal R := principalIdeal f
  let σ : R →+* R' := algebraMap R R'
  have hmap :
      Ideal.map σ (I ^ (n : ℕ)) = principalPowerIdeal (σ f) n := by
    simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have htransport :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map) := by
    -- Proof comment: both quotient maps agree on generators of `R ⧸ I^n`, so the displayed
    -- `principalPowerIdeal` presentation is just the generic quotient map conjugated by the
    -- canonical quotient equivalence.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
    simpa [I, σ] using
      (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
  have hcomp :
      Function.Bijective
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map)) := by
    -- Proof comment: transport the given bijectivity hypothesis through the quotient equivalence.
    have hcomp0 : Function.Bijective (principalPowerIdealImageQuotientMap σ f n) := by
      simpa [σ] using hquot n
    rw [htransport] at hcomp0
    exact hcomp0
  constructor
  · intro x y hxy
    have hxy0 :
        (Ideal.quotientMap
          (Ideal.map σ (I ^ (n : ℕ)))
          σ
          Ideal.le_comap_map) x =
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map) y := by
      simpa [I, σ] using hxy
    have hxy' :
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map)) x =
          ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map)) y := by
      exact congrArg (Ideal.quotientEquivAlgOfEq R hmap) hxy0
    exact hcomp.1 hxy'
  · intro z
    obtain ⟨x, hx⟩ :=
      hcomp.2 ((Ideal.quotientEquivAlgOfEq R hmap) z)
    refine ⟨x, ?_⟩
    have hx' := hx
    have hx0 :
        (Ideal.quotientMap
          (Ideal.map σ (I ^ (n : ℕ)))
          σ
          Ideal.le_comap_map) x = z :=
      (Ideal.quotientEquivAlgOfEq R hmap).injective hx'
    simpa [I, σ] using hx0

/-- Helper for Lemma 15.91.10: surjectivity on `(f)^∞`-torsion should reconstruct a preimage of
any kernel pair by clearing a denominator in the localization coordinate and correcting the first
coordinate by a torsion lift. -/
theorem beauvilleLaszloModuleCech_exact_of_fPowerTorsionToTensor_surjective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n))
    (hsurj : Function.Surjective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M)) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
  -- Route correction: the denominator-clearing step and the modulo-`f^n` first-coordinate lift
  -- are now isolated in `tensor_localizationAway_exists_power_denominator`,
  -- `kernel_first_coordinate_error_overlap_eq_zero_of_moduleCechBeta_eq_zero`, and
  -- `tensorProduct_comm_symm_mem_primaryComponent_of_mem_fPowerTorsion`. The quotient-map
  -- transport needed for the quotient-module descent is now available in
  -- `principal_power_quotientMap_bijective`. The remaining blocker is the quotient/tensor descent
  -- step turning a first-coordinate identity `m ⊗ 1 = f^n • y` into an actual divisibility
  -- statement `m = f^n • m₀` in `M`, followed by the final denominator-splitting preimage
  -- assembly.
  -- TODO: package that descent as the missing module analogue of
  -- `preimage_principalPowerIdeal_of_quotient_injective`, then finish the source-faithful
  -- denominator-clearing reconstruction under `hsurj`.
  let _ := hquot
  let _ := hsurj
  sorry
/-- Under the quotient-isomorphism hypothesis, the module Beauville-Laszlo sequence is exact in the
middle exactly when the canonical base-change map on `(f)^∞`-torsion is surjective. -/
theorem beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) ↔
    Function.Surjective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := by
  constructor
  · intro hexact
    -- Exactness tests the kernel element `(y, 0)` and so yields surjectivity on torsion.
    exact
      fPowerTorsionToTensor_surjective_of_beauvilleLaszloModuleCech_exact
        (R := R) (R' := R') (M := M) f hexact
  · intro hsurj
    -- The converse is the denominator-clearing reconstruction from a kernel pair.
    exact
      beauvilleLaszloModuleCech_exact_of_fPowerTorsionToTensor_surjective
        (R := R) (R' := R') (M := M) f hquot hsurj

/-- Helper for Lemma 15.91.10: tensoring the ring-level Beauville-Laszlo exact sequence with `M`
and transporting across the displayed middle isomorphism gives middle exactness of the module
sequence for a glueing pair. -/
theorem beauvilleLaszloModuleCech_exact_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
  have hringExact :
      Function.Exact
        ((beauvilleLaszloCechSequence (algebraMap R R') f).f.hom)
        ((beauvilleLaszloCechSequence (algebraMap R R') f).g.hom) := by
    -- Extract the function-level exactness from the ring-side short exact sequence.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (beauvilleLaszloCechSequence (algebraMap R R') f)).1 hpair.shortExact.exact
  have hringSurj :
      Function.Surjective ((beauvilleLaszloCechSequence (algebraMap R R') f).g.hom) := by
    exact hpair.shortExact.moduleCat_surjective_g
  have htensorExact :
      Function.Exact
        ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom)
        ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
    -- Right exactness of `M ⊗[R] -` preserves the exact ring sequence.
    simpa [beauvilleLaszloModuleCechTensorImage] using
      (rTensor_exact M hringExact hringSurj)
  change Function.Exact
    (beauvilleLaszloModuleCechAlpha R' M f)
    (beauvilleLaszloModuleCechBeta R' M f)
  -- Route correction: prove exactness directly from the tensor-image exactness, rather than
  -- forcing repeated rewrites through the displayed short-complex packaging.
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · -- The displayed module Cech maps already form a complex.
    simpa [beauvilleLaszloModuleCechSequence] using
      (beauvilleLaszloModuleCech_comp_eq_zero R' M f)
  · intro x hx
    let middleIso := beauvilleLaszloModuleCechMiddleIso R' M f
    let leftIso := beauvilleLaszloModuleCechLeftIso R' M f
    have hxTensor :
        (beauvilleLaszloModuleCechTensorImage R' M f).g.hom (middleIso.inv.hom x) = 0 := by
      -- Rewrite the displayed kernel condition back to the tensor-image middle object.
      simpa [beauvilleLaszloModuleCechBeta, middleIso] using hx
    have hxRange :
        middleIso.inv.hom x ∈
          LinearMap.range ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom) := by
      have hxKer :
          middleIso.inv.hom x ∈
            LinearMap.ker ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
        simpa [LinearMap.mem_ker] using hxTensor
      rw [(LinearMap.exact_iff.1 htensorExact)] at hxKer
      exact hxKer
    rcases hxRange with ⟨y, hy⟩
    refine ⟨leftIso.hom y, ?_⟩
    -- Transport the tensor-image preimage back to the displayed module sequence.
    apply middleIso.inv.injective
    simpa [beauvilleLaszloModuleCechAlpha, leftIso, middleIso] using hy

-- Proof sketch: combine right exactness with the previous injectivity and surjectivity criteria.
-- Glueability is injectivity on the left, exactness in the middle, and surjectivity on the right,
-- so under the quotient-isomorphism hypothesis it is equivalent to bijectivity on `f^∞`-torsion.
/-- Lemma 15.91.10: if `R → R'` induces isomorphisms `R / f^n R → R' / f^n R'` for all positive
integers `n`, then `M` is glueable for `(R → R', f)` if and only if the induced map
on `(f)^∞`-torsion is bijective. -/
@[stacks 0BNW]
theorem isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Bijective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := by
  constructor
  · intro hshortExact
    constructor
    · -- Left exactness identifies injectivity with injectivity on `f^∞`-torsion.
      have hmono :
          Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) := by
        exact (ModuleCat.mono_iff_injective _).1 hshortExact.mono_f
      exact
        (beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
          (R := R) (R' := R') (M := M) f).1 hmono
    · -- Middle exactness identifies surjectivity with surjectivity on `f^∞`-torsion.
      have hexact :
          Function.Exact
            ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
            ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
        exact
          (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
            (beauvilleLaszloModuleCechSequence R' M f)).1 hshortExact.exact
      exact
        (beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
          (R := R) (R' := R') (M := M) f hquot).1 hexact
  · rintro ⟨hinj, hsurj⟩
    -- Assemble short exactness from the exactness, injectivity, and surjectivity criteria.
    refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModuleCechSequence R' M f) ?_ ?_ ?_
    · exact
        (beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
          (R := R) (R' := R') (M := M) f hquot).2 hsurj
    · exact
        (beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
          (R := R) (R' := R') (M := M) f).2 hinj
    · exact
        beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
          (R := R) (R' := R') (M := M) f hquot

-- Proof sketch: if `(R → R', f)` is a glueing pair, the ring-level Beauville-Laszlo sequence is
-- exact, and tensoring that exact sequence with `M` gives exactness in the middle for the
-- module-side sequence. The main criterion then reduces glueability to injectivity on
-- the canonical base-change map on `(f)^∞`-torsion.
/-- For a Beauville-Laszlo glueing pair `(R → R', f)`, module glueability is equivalent to
injectivity on `f^∞`-torsion. -/
theorem isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := by
  constructor
  · intro hshortExact
    -- Left exactness alone gives the forward implication.
    have hmono :
        Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) := by
      exact (ModuleCat.mono_iff_injective _).1 hshortExact.mono_f
    exact
      (beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
        (R := R) (R' := R') (M := M) f).1 hmono
  · intro hinj
    -- For a glueing pair, middle exactness is automatic after tensoring the ring sequence.
    refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModuleCechSequence R' M f) ?_ ?_ ?_
    · exact beauvilleLaszloModuleCech_exact_of_glueingPair (R := R) (R' := R') (M := M) f hpair
    · exact
        (beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
          (R := R) (R' := R') (M := M) f).2 hinj
    · exact
        beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
          (R := R) (R' := R') (M := M) f hpair.quotientMapBijective

end

section

variable {R : Type u} [CommRing R]

variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: specialize the previous theorem to `R' = R^∧`. For a Beauville-Laszlo glueing
-- pair `(R, f)`, the completion pair is exact in the middle for every `M`, so only injectivity of
-- the canonical base-change map on `(f)^∞`-torsion remains.
/-- If `(R, f)` is a Beauville-Laszlo glueing pair, then `M` is glueable along the completion map
if and only if the canonical base-change map on `(f)^∞`-torsion is injective. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f))
      f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective
        (tensorBaseChangeUnitPrimaryComponent
          (principalAdicCompletion f)
          (principalIdeal f)
          M) := by
  -- This is the completion specialization of the glueing-pair criterion proved above.
  simpa using
    (isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair
      (R := R) (R' := principalAdicCompletion f) (M := M) f hpair)

end
