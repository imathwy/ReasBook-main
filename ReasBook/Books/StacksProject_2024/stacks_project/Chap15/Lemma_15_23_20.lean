import Mathlib
import StacksProject_2024.Chap10.Lemma_10_38_6
import StacksProject_2024.Chap10.Lemma_10_157_6
import StacksProject_2024.Chap15.Lemma_15_23_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped nonZeroDivisors
open Module

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
variable [Module.Finite A (integralClosure A L)]
local notation "K" => FractionRing A
local notation "B" => integralClosure A L

/-- Helper for Lemma 15.23.20: the canonical map `A → L` is injective because it factors through
the fraction field of `A`. -/
lemma algebraMap_injective_to_field_extension :
    Function.Injective (algebraMap A L) := by
  -- Injectivity over `A` follows by passing through `FractionRing A`.
  intro x y hxy
  apply IsFractionRing.injective A K
  apply RingHom.injective (algebraMap K L)
  simpa [IsScalarTower.algebraMap_apply A K L] using hxy

/-- Helper for Lemma 15.23.20: if a scalar from `A` acts on the ambient field `L` by a nonzero
element, then its induced `A`-linear endomorphism of `L` is invertible. -/
lemma scalar_action_isUnit_of_algebraMap_ne_zero (a : A) (ha : algebraMap A L a ≠ 0) :
    IsUnit (algebraMap A (Module.End A L) a) := by
  -- Multiplication by a nonzero scalar is bijective on a field.
  rw [Module.End.isUnit_iff]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply_fun fun z : L ↦ (algebraMap A L a)⁻¹ * z at hxy
    simpa [Algebra.smul_def, ha, mul_assoc] using hxy
  · intro x
    refine ⟨(algebraMap A L a)⁻¹ * x, ?_⟩
    simpa [Algebra.smul_def, ha, mul_assoc]

/-- Helper for Lemma 15.23.20: every nonzero element of `A` acts invertibly on the ambient field
`L`. -/
lemma nonZeroDivisor_action_isUnit_on_field (s : A⁰) :
    IsUnit (algebraMap A (Module.End A L) s.1) :=
  scalar_action_isUnit_of_algebraMap_ne_zero (A := A) (L := L) s.1 <|
    fun hzero ↦ nonZeroDivisors.ne_zero s.2 <|
      (algebraMap_injective_to_field_extension (A := A) (L := L)) <| by
        simpa using hzero

/-- Helper for Lemma 15.23.20: every element outside a prime ideal acts invertibly on the ambient
field `L`. -/
lemma prime_compl_action_isUnit_on_field (I : Ideal A) [I.IsPrime] (s : I.primeCompl) :
    IsUnit (algebraMap A (Module.End A L) s.1) :=
  scalar_action_isUnit_of_algebraMap_ne_zero (A := A) (L := L) s.1 <|
    fun hzero ↦ s.2 <| by
      have hs0 : s.1 = 0 :=
        (algebraMap_injective_to_field_extension (A := A) (L := L)) <| by
          simpa using hzero
      simpa [hs0] using (show (0 : A) ∈ I from Ideal.zero_mem I)

/-- Helper for Lemma 15.23.20: the generic localization of the integral closure maps to the
ambient field `L`. -/
noncomputable def integralClosure_genericLocalization_to_field :
    LocalizedModule A⁰ B →ₗ[A] L :=
  IsLocalizedModule.lift A⁰ (LocalizedModule.mkLinearMap A⁰ B)
    (LinearMap.restrictScalars A (Algebra.linearMap B L))
    (nonZeroDivisor_action_isUnit_on_field (A := A) (L := L))

/-- Helper for Lemma 15.23.20: the localization at a prime complement maps to the ambient field
`L`. -/
noncomputable def integralClosure_primeLocalization_to_field (I : Ideal A) [I.IsPrime] :
    LocalizedModule I.primeCompl B →ₗ[A] L :=
  IsLocalizedModule.lift I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl B)
    (LinearMap.restrictScalars A (Algebra.linearMap B L))
    (prime_compl_action_isUnit_on_field (A := A) (L := L) I)

/-- Helper for Lemma 15.23.20: the generic-localization map agrees with the ambient inclusion on
integral elements. -/
@[simp] lemma integralClosure_genericLocalization_to_field_mkLinearMap (b : B) :
    integralClosure_genericLocalization_to_field (A := A) (L := L)
        (LocalizedModule.mkLinearMap A⁰ B b) =
      algebraMap B L b := by
  -- This is the defining property of the localization lift.
  simpa [integralClosure_genericLocalization_to_field] using
    (IsLocalizedModule.lift_apply A⁰ (LocalizedModule.mkLinearMap A⁰ B)
      (LinearMap.restrictScalars A (Algebra.linearMap B L))
      (nonZeroDivisor_action_isUnit_on_field (A := A) (L := L)) b)

/-- Helper for Lemma 15.23.20: the prime-localization map agrees with the ambient inclusion on
integral elements. -/
@[simp] lemma integralClosure_primeLocalization_to_field_mkLinearMap
    (I : Ideal A) [I.IsPrime] (b : B) :
    integralClosure_primeLocalization_to_field (A := A) (L := L) I
        (LocalizedModule.mkLinearMap I.primeCompl B b) =
      algebraMap B L b := by
  -- This is again the universal-property equation for the localization lift.
  simpa [integralClosure_primeLocalization_to_field] using
    (IsLocalizedModule.lift_apply I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl B)
      (LinearMap.restrictScalars A (Algebra.linearMap B L))
      (prime_compl_action_isUnit_on_field (A := A) (L := L) I) b)

/-- Helper for Lemma 15.23.20: both localization-to-field maps coincide after restricting the
prime-localized module to the generic localization. -/
lemma integralClosure_genericLocalization_to_field_comp_liftOfLE
    (I : Ideal A) [I.IsPrime] :
    (integralClosure_genericLocalization_to_field (A := A) (L := L)).comp
        (LocalizedModule.liftOfLE I.primeCompl A⁰
          (Ideal.primeCompl_le_nonZeroDivisors I)) =
      integralClosure_primeLocalization_to_field (A := A) (L := L) I := by
  -- Both maps are the unique localization lifts extending the ambient map `B → L`.
  symm
  apply IsLocalizedModule.lift_unique I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl B)
    (LinearMap.restrictScalars A (Algebra.linearMap B L))
    (prime_compl_action_isUnit_on_field (A := A) (L := L) I)
  ext b
  -- Compare both extensions on the numerator copy of `B`.
  rw [LinearMap.comp_assoc, IsLocalizedModule.liftOfLE_comp]
  simpa using integralClosure_genericLocalization_to_field_mkLinearMap (A := A) (L := L) b

/-- Helper for Lemma 15.23.20: the generic-localization map into the ambient field is injective,
because it is already injective on the image of `B`. -/
lemma integralClosure_genericLocalization_to_field_injective :
    Function.Injective (integralClosure_genericLocalization_to_field (A := A) (L := L)) := by
  -- Reduce injectivity on the localization to injectivity on the numerator copy of `B`.
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  refine IsLocalizedModule.injective_of_map_eq A⁰ (LocalizedModule.mkLinearMap A⁰ B) ?_
  intro x y hxy
  have hxy' : algebraMap B L x = algebraMap B L y := by
    rw [integralClosure_genericLocalization_to_field_mkLinearMap (A := A) (L := L) x,
      integralClosure_genericLocalization_to_field_mkLinearMap (A := A) (L := L) y] at hxy
    exact hxy
  simpa using congrArg (LocalizedModule.mkLinearMap A⁰ B)
    ((FaithfulSMul.algebraMap_injective B L) hxy')

/-- Helper for Lemma 15.23.20: a height-one branch witness maps to the same ambient-field element
as its generic-localization image. -/
lemma heightOne_branch_maps_to_generic_field_element
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    {x : LocalizedModule A⁰ B}
    {y : LocalizedModule p.1.asIdeal.primeCompl B}
    (hy :
      LocalizedModule.liftOfLE p.1.asIdeal.primeCompl A⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) y = x) :
    integralClosure_primeLocalization_to_field (A := A) (L := L) p.1.asIdeal y =
      integralClosure_genericLocalization_to_field (A := A) (L := L) x := by
  -- Evaluate the comparison of localization maps on the chosen branch element `y`.
  calc
    integralClosure_primeLocalization_to_field (A := A) (L := L) p.1.asIdeal y =
        integralClosure_genericLocalization_to_field (A := A) (L := L)
          (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl A⁰
            (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) y) := by
          symm
          exact congrArg
            (fun f : LocalizedModule p.1.asIdeal.primeCompl B →ₗ[A] L => f y)
            (integralClosure_genericLocalization_to_field_comp_liftOfLE
              (A := A) (L := L) p.1.asIdeal)
    _ = integralClosure_genericLocalization_to_field (A := A) (L := L) x := by rw [hy]

/-- Helper for Lemma 15.23.20: every element outside a prime ideal becomes a unit in the ambient
field `L`. -/
lemma prime_compl_isUnit_in_field (I : Ideal A) [I.IsPrime] (s : I.primeCompl) :
    IsUnit (algebraMap A L s.1) := by
  -- Elements of `I.primeCompl` stay nonzero in the fraction-field extension `L`.
  refine isUnit_iff_ne_zero.mpr fun hs ↦ s.2 ?_
  have hs0 : s.1 = 0 :=
    algebraMap_injective_to_field_extension (A := A) (L := L) <| by
      simpa using hs
  simpa [hs0] using (show (0 : A) ∈ I from Ideal.zero_mem I)

/-- Helper for Lemma 15.23.20: the canonical map from the localization `A_I` to the ambient field
`L` is obtained from the universal property of localization. -/
noncomputable def primeLocalization_algebraTo_field (I : Ideal A) [I.IsPrime] :
    Localization.AtPrime I →+* L :=
  IsLocalization.lift (S := Localization.AtPrime I) (g := algebraMap A L)
    (fun s ↦ prime_compl_isUnit_in_field (A := A) (L := L) I s)

/-- Helper for Lemma 15.23.20: the prime localization `A_I` carries its canonical algebra
structure over `L` induced by the universal localization map. -/
noncomputable instance primeLocalization_to_field_algebra (I : Ideal A) [I.IsPrime] :
    Algebra (Localization.AtPrime I) L :=
  RingHom.toAlgebra (primeLocalization_algebraTo_field (A := A) (L := L) I)

/-- Helper for Lemma 15.23.20: the localization-to-field map extends the original map `A → L`. -/
@[simp] lemma primeLocalization_algebraTo_field_commutes
    (I : Ideal A) [I.IsPrime] (a : A) :
    primeLocalization_algebraTo_field (A := A) (L := L) I
        (algebraMap A (Localization.AtPrime I) a) =
      algebraMap A L a := by
  -- This is the defining compatibility of the localization lift.
  simpa [primeLocalization_algebraTo_field] using
    (IsLocalization.lift_eq (S := Localization.AtPrime I) (g := algebraMap A L)
      (fun s ↦ prime_compl_isUnit_in_field (A := A) (L := L) I s) a)

/-- Helper for Lemma 15.23.20: the localized `A`-algebra structure on `L` is compatible with the
original scalar tower `A → K → L`. -/
instance primeLocalization_to_field_isScalarTower (I : Ideal A) [I.IsPrime] :
    IsScalarTower A (Localization.AtPrime I) L := by
  -- The localization map was defined to agree with the original `A → L` map.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro a
  change (algebraMap A L) a =
    primeLocalization_algebraTo_field (A := A) (L := L) I
      (algebraMap A (Localization.AtPrime I) a)
  symm
  exact primeLocalization_algebraTo_field_commutes (A := A) (L := L) I a

/-- Helper for Lemma 15.23.20: the localized map `A_I → L` factors through the fraction field
`K = FractionRing A`. -/
lemma primeLocalization_to_fractionRing_to_field_comp
    (I : Ideal A) [I.IsPrime] :
    (algebraMap K L).comp (algebraMap (Localization.AtPrime I) K) =
      algebraMap (Localization.AtPrime I) L := by
  -- Both ring maps out of `A_I` agree on the image of `A`, hence they are equal by localization.
  apply IsLocalization.ringHom_ext I.primeCompl
  ext a
  have hAK :
      (algebraMap A K) a =
        (algebraMap (Localization.AtPrime I) K)
          ((algebraMap A (Localization.AtPrime I)) a) := by
    simpa using congrArg (fun f : A →+* K => f a)
      (IsScalarTower.algebraMap_eq A (Localization.AtPrime I) K)
  have hAL :
      (algebraMap A L) a =
        (algebraMap (Localization.AtPrime I) L)
          ((algebraMap A (Localization.AtPrime I)) a) := by
    simpa using congrArg (fun f : A →+* L => f a)
      (IsScalarTower.algebraMap_eq A (Localization.AtPrime I) L)
  calc
    (algebraMap K L) ((algebraMap (Localization.AtPrime I) K)
        ((algebraMap A (Localization.AtPrime I)) a)) =
        (algebraMap K L) ((algebraMap A K) a) := by rw [hAK]
    _ = algebraMap A L a := by
          simpa using (congrArg (fun f : A →+* L => f a)
            (IsScalarTower.algebraMap_eq A K L)).symm
    _ = (algebraMap (Localization.AtPrime I) L)
          ((algebraMap A (Localization.AtPrime I)) a) := hAL

/-- Helper for Lemma 15.23.20: the localized fraction-field map gives the expected scalar tower
`A_I → K → L`. -/
instance primeLocalization_to_fractionRing_to_field_isScalarTower
    (I : Ideal A) [I.IsPrime] :
    IsScalarTower (Localization.AtPrime I) K L := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro z
  exact congrArg
    (fun f : Localization.AtPrime I →+* L => f z)
    (primeLocalization_to_fractionRing_to_field_comp (A := A) (L := L) I).symm

/-- Helper for Lemma 15.23.20: every element coming from the localization of the integral closure
at a prime is integral over the localized base ring. -/
lemma primeLocalization_to_field_isIntegral
    (I : Ideal A) [I.IsPrime]
    (y : LocalizedModule I.primeCompl B) :
    IsIntegral (Localization.AtPrime I)
      (integralClosure_primeLocalization_to_field (A := A) (L := L) I y) := by
  obtain ⟨⟨b, s⟩, hs⟩ :=
    IsLocalizedModule.surj I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl B) y
  have hs_map :
      algebraMap A L s.1 *
          integralClosure_primeLocalization_to_field (A := A) (L := L) I y =
        algebraMap B L b := by
    -- Applying the localization map clears the chosen denominator `s`.
    calc
      algebraMap A L s.1 *
          integralClosure_primeLocalization_to_field (A := A) (L := L) I y =
          s.1 • integralClosure_primeLocalization_to_field (A := A) (L := L) I y := by
            simp [Algebra.smul_def]
      _ =
          integralClosure_primeLocalization_to_field (A := A) (L := L) I (s.1 • y) := by
            rw [LinearMap.map_smul]
      _ =
          integralClosure_primeLocalization_to_field (A := A) (L := L) I
            ((LocalizedModule.mkLinearMap I.primeCompl B) b) := by
              exact congrArg
                (integralClosure_primeLocalization_to_field (A := A) (L := L) I) hs
      _ = algebraMap B L b := by
            simpa [LocalizedModule.mkLinearMap_apply] using
              integralClosure_primeLocalization_to_field_mkLinearMap
                (A := A) (L := L) I b
  have hs_ne_zero : algebraMap A L s.1 ≠ 0 := by
    -- The chosen denominator comes from the prime complement, so it stays nonzero in `L`.
    exact (isUnit_iff_ne_zero.mp <|
      prime_compl_isUnit_in_field (A := A) (L := L) I s)
  have hs_inv_integral :
      IsIntegral (Localization.AtPrime I) ((algebraMap A L s.1)⁻¹) := by
    -- The inverse denominator is the image of a unit from `A_I`.
    let u : Units (Localization.AtPrime I) :=
      (IsLocalization.map_units (Localization.AtPrime I) s).unit
    have hu :
        (algebraMap A L s.1)⁻¹ =
          algebraMap (Localization.AtPrime I) L ↑u⁻¹ := by
      have hcomm :
          algebraMap A L s.1 =
            algebraMap (Localization.AtPrime I) L
              (algebraMap A (Localization.AtPrime I) s.1) := by
        simpa using congrArg (fun f : A →+* L => f s.1)
          (IsScalarTower.algebraMap_eq A (Localization.AtPrime I) L)
      rw [hcomm]
      simp [u]
    rw [hu]
    simpa using
      (show IsIntegral (Localization.AtPrime I)
        (algebraMap (Localization.AtPrime I) L ↑(u⁻¹)) from isIntegral_algebraMap)
  have hu_inv_integral :
      IsIntegral (Localization.AtPrime I) ((algebraMap A L s.1)⁻¹) :=
    hs_inv_integral
  have hb_integral :
      IsIntegral (Localization.AtPrime I) (algebraMap B L b) := by
    -- Integral elements over `A` stay integral after passing to the localization `A_I`.
    exact IsIntegral.tower_top (A := Localization.AtPrime I) <| by
      simpa using (show IsIntegral A (b : L) from b.2)
  have hy_eq :
      integralClosure_primeLocalization_to_field (A := A) (L := L) I y =
        (algebraMap A L s.1)⁻¹ * algebraMap B L b := by
    -- Solve the denominator equation inside the field `L`.
    exact (eq_inv_mul_iff_mul_eq₀ hs_ne_zero).2 hs_map
  -- Rewrite the branch value as a product of two integral elements over `A_I`.
  rw [hy_eq]
  exact IsIntegral.mul hu_inv_integral hb_integral

/-- Helper for Lemma 15.23.20: if an element of `L` is integral over a height-one localization of
`A`, then every coefficient of its minimal polynomial over `K` comes from that localization. -/
lemma coeff_minpoly_mem_range_localizationAtPrime_of_isIntegral
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (z : L) (hz : IsIntegral (Localization.AtPrime p.1.asIdeal) z) (n : ℕ) :
    (minpoly K z).coeff n ∈ (algebraMap (Localization.AtPrime p.1.asIdeal) K).range := by
  let _ : IsFractionRing (Localization.AtPrime p.1.asIdeal) K :=
    IsFractionRing.isFractionRing_of_isLocalization p.1.asIdeal.primeCompl
      (Localization.AtPrime p.1.asIdeal) K p.1.asIdeal.primeCompl_le_nonZeroDivisors
  -- Compare the minimal polynomial over `K` with the localized minimal polynomial over `A_p`.
  refine ⟨(minpoly (Localization.AtPrime p.1.asIdeal) z).coeff n, ?_⟩
  symm
  simpa [Polynomial.coeff_map] using
    congrArg (fun q : Polynomial K => q.coeff n)
      (minpoly.isIntegrallyClosed_eq_field_fractions' K hz)

/-- Helper for Lemma 15.23.20: coefficients of the minimal polynomial of an element in the
height-one-localization intersection lie in every height-one localization of `A`. -/
lemma coeff_minpoly_mem_localizationAtPrime_of_mem_heightOneLocalizationIntersection
    (x : LocalizedModule A⁰ B)
    (hx : x ∈ moduleHeightOneLocalizationIntersection A B)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (n : ℕ) :
    let xL : L := integralClosure_genericLocalization_to_field (A := A) (L := L) x
    (minpoly K xL).coeff n ∈ (algebraMap (Localization.AtPrime p.1.asIdeal) K).range := by
  dsimp
  rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf] at hx
  rcases hx p with ⟨y, hy⟩
  have hy_field :
      integralClosure_primeLocalization_to_field (A := A) (L := L) p.1.asIdeal y =
        integralClosure_genericLocalization_to_field (A := A) (L := L) x :=
    heightOne_branch_maps_to_generic_field_element (A := A) (L := L) p hy
  have hz :
      IsIntegral (Localization.AtPrime p.1.asIdeal)
        (integralClosure_genericLocalization_to_field (A := A) (L := L) x) := by
    -- Transport local integrality along the branch/generic comparison.
    rw [← hy_field]
    exact primeLocalization_to_field_isIntegral (A := A) (L := L) p.1.asIdeal y
  exact coeff_minpoly_mem_range_localizationAtPrime_of_isIntegral (A := A) (L := L) p
    (integralClosure_genericLocalization_to_field (A := A) (L := L) x) hz n

/-
Domain-style sampling:
- primary domain: finite integral closures over Noetherian normal domains, viewed as finite
  modules over the base domain and analyzed via the chapter's reflexivity criterion;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.IsTorsionFree`,
  `IsIntegralClosure.isTorsionFree`,
  `reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner of the conclusion, and Lemma `15.23.18` is the
  chapter bridge/view that turns the height-one-localization-intersection criterion into that
  owner instance;
- source/core/bridge triage:
  `source-facing`: this lemma asserting that the finite integral closure is reflexive;
  `core/canonical`: `Module.IsReflexive`;
  `bridge/view`: the proof route through torsion-freeness and the height-one localization
    intersection inside the ambient field.

Primitive data are only the normal domain `A`, the finite extension `L / FractionRing A`, and the
finiteness of `integralClosure A L` over `A`. Torsion-freeness of the integral closure and the
final reflexivity claim are derived API from the owner abstractions above, so the public surface
should be a single named owner instance rather than a theorem duplicated by a second wrapper
instance.
-/

-- Proof sketch: by Lemma `15.23.18`, it is enough to show that `integralClosure A L` agrees with
-- the intersection of its height-one localizations inside `L`. For an element of that
-- intersection, Lemma `10.38.6` shows that the coefficients of its minimal polynomial over
-- `FractionRing A` lie in every height-one localization of `A`, and Lemma `10.157.6` then forces
-- those coefficients to lie in `A`, proving integrality over `A`.
/-- Lemma 15.23.20: if `A` is a Noetherian normal domain and `L / FractionRing A` is a finite
extension such that the integral closure of `A` in `L` is finite over `A`, then
`integralClosure A L` is reflexive as an `A`-module. -/
instance integralClosure_isReflexive_of_finite :
    IsReflexive A B := by
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let _ : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  let _ : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  -- Apply the height-one intersection criterion from Lemma `15.23.18`.
  refine
    ((reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection
      (R := A) (M := B)).out 2 0).mp ?_
  refine ⟨inferInstance, le_antisymm ?_ ?_⟩
  · -- Every global integral element belongs to each height-one localization branch.
    intro x hx
    rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf]
    intro p
    rcases hx with ⟨b, rfl⟩
    refine ⟨LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl B b, ?_⟩
    simpa using LinearMap.congr_fun
      (IsLocalizedModule.liftOfLE_comp p.1.asIdeal.primeCompl A⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)
        (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl B)
        (LocalizedModule.mkLinearMap A⁰ B)) b
  · intro x hxIntersection
    let xL : L := integralClosure_genericLocalization_to_field (A := A) (L := L) x
    -- Route correction: keep the textbook minimal-polynomial route in the ambient field `L`,
    -- rather than switching to a local-global reflexivity criterion unrelated to the source proof.
    have hxcoeff :
        ∀ n : ℕ, (minpoly K xL).coeff n ∈ (algebraMap A K).range := by
      intro n
      rw [mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one]
      intro p
      -- Use the height-one branch witness for `x` to obtain local integrality of `xL`.
      simpa [xL] using
        coeff_minpoly_mem_localizationAtPrime_of_mem_heightOneLocalizationIntersection
          (A := A) (L := L) x hxIntersection p n
    have hxcoeff_integral : ∀ n : ℕ, IsIntegral A ((minpoly K xL).coeff n) := by
      intro n
      rcases hxcoeff n with ⟨a, ha⟩
      simpa [ha] using (show IsIntegral A (algebraMap A K a) from isIntegral_algebraMap)
    have hxIntegral : IsIntegral A xL := by
      let q : Polynomial L := (minpoly K xL).map (algebraMap K L)
      have hqcoeff : ∀ n : ℕ, IsIntegral A (q.coeff n) := by
        intro n
        simpa [q, Polynomial.coeff_map] using
          (hxcoeff_integral n).map (IsScalarTower.toAlgHom A K L)
      have hqeval : Polynomial.eval xL q = 0 := by
        -- Evaluating the mapped minimal polynomial in `L` is the same as evaluating the original
        -- minimal polynomial over `K`.
        simpa [q] using (minpoly.aeval K xL)
      have hqdeg : q.natDegree ≠ 0 := by
        simpa [q] using
          (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral xL)).ne'
      refine IsIntegral.of_aeval_monic_of_isIntegral_coeff
        (x := xL) (p := q)
        ((minpoly.monic (Algebra.IsIntegral.isIntegral xL)).map _)
        hqdeg
        (by simpa [hqeval] using isIntegral_zero)
        hqcoeff
    obtain ⟨b, hb⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := B) (R := A) (x := xL)).mp hxIntegral
    refine ⟨b, ?_⟩
    apply integralClosure_genericLocalization_to_field_injective (A := A) (L := L)
    rw [integralClosure_genericLocalization_to_field_mkLinearMap (A := A) (L := L) b]
    simpa [xL] using hb

end
