import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_43_1 (from Chap15) -/
universe u

open IsLocalRing

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
* primary domain: local commutative algebra of maximal-ideal adic completion and Krull dimension.
* sampled owner declarations:
  `Ideal.Fiber`,
  `ringKrullDim`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown`,
  `adicCompletion_isNoetherianRing`,
  `AdicCompletion.isAdicComplete`,
  `IsAdicComplete.map_algebraMap_iff`,
  `completionIdeal_pow_eq_ker_evalₐ`,
  `IsCompleteLocalRing`.
* owner abstraction: the canonical completion owner `AdicCompletion (maximalIdeal A) A`, together
  with the Chapter 10 faithful-flat completion map and localization/closed-fiber dimension
  formulas.
* primitive data: the Noetherian local ring `A`.
* derived API: the completion is a complete local ring, the completion map is local, the extended
  maximal ideal is the maximal ideal of the completion, and the closed fiber at the maximal ideal
  has Krull dimension `0`.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

private theorem completionMap_maximalIdeal_isMaximal :
    Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : Field (A ⧸ (maximalIdeal A) ^ 1) := by
    let e : A ⧸ (maximalIdeal A) ^ 1 ≃+* A ⧸ maximalIdeal A :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal A))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1) : Ideal.IsMaximal
        (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1)))

private theorem completion_isLocalRing :
    IsLocalRing ACompletion := by
  let hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completionMap_maximalIdeal_isMaximal A
  letI : Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := hmax
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2
  letI : IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    hcomplete
  exact @isLocalRing_of_isAdicComplete_maximal ACompletion _
    (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) hmax hcomplete

local instance : IsLocalRing ACompletion := completion_isLocalRing A

private theorem completionMap_maximalIdeal_eq_maximalIdeal :
    Ideal.map (algebraMap A ACompletion) (maximalIdeal A) = maximalIdeal ACompletion := by
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completionMap_maximalIdeal_isMaximal A
  exact IsLocalRing.eq_maximalIdeal inferInstance

omit [IsNoetherianRing A] in
instance : IsLocalHom (algebraMap A ACompletion) := by
  let φ : ACompletion →+* A ⧸ maximalIdeal A :=
    (AdicCompletion.evalOneₐ (maximalIdeal A)).toRingHom
  have hcomp : φ.comp (algebraMap A ACompletion) = Ideal.Quotient.mk (maximalIdeal A) := by
    ext x
    simp [φ]
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap A ACompletion)) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap A ACompletion) φ

private theorem completion_isAdicComplete_maximalIdeal :
    IsAdicComplete (maximalIdeal ACompletion) ACompletion := by
  haveI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  haveI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  simpa [completionMap_maximalIdeal_eq_maximalIdeal A] using
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2

instance : IsCompleteLocalRing ACompletion := by
  exact
    { toIsLocalRing := completion_isLocalRing A
      toIsAdicComplete := completion_isAdicComplete_maximalIdeal A }

private noncomputable def closedFiberQuotRingEquiv :
    ClosedFiber ≃+* ACompletion ⧸ maximalIdeal ACompletion :=
  let e :
      ClosedFiber ≃+*
        ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A) :=
    ((Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))) .refl).toRingEquiv).trans <|
      ((Algebra.TensorProduct.comm _ _ _).toRingEquiv.trans <|
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.toRingEquiv)
  e.trans <| Ideal.quotEquivOfEq (completionMap_maximalIdeal_eq_maximalIdeal A)

/- The canonical closed fiber of the maximal-ideal adic completion map is a field. -/
instance : Field ClosedFiber := by
  letI : Field (ACompletion ⧸ maximalIdeal ACompletion) :=
    Ideal.Quotient.field (maximalIdeal ACompletion)
  exact IsField.toField <|
    (closedFiberQuotRingEquiv A).toMulEquiv.isField (Field.toIsField _)

-- Proof sketch: Lemma `10.97.4` identifies the quotients by powers of the maximal ideal of `A`
-- and of `AdicCompletion (maximalIdeal A) A`. Lemma `10.52.12` then gives equality of their
-- lengths, so the dimension formula of Proposition `10.60.9` yields equality of Krull
-- dimensions; alternatively one can appeal to the dimension formula in Lemma `10.112.7`.
/-- Lemma 15.43.1: a Noetherian local ring and its maximal-ideal adic completion have the same
Krull dimension. -/
theorem ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion :
    ringKrullDim A = ringKrullDim ACompletion := by
  letI : RingHom.FaithfullyFlat (algebraMap A ACompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  let q : Ideal ACompletion := maximalIdeal ACompletion
  have hlocalA :
      ringKrullDim (Localization.AtPrime (maximalIdeal A)) = ringKrullDim A := by
    calc
      ringKrullDim (Localization.AtPrime (maximalIdeal A)) = (maximalIdeal A).height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal A) _
      _ = ringKrullDim A := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hlocalCompletion :
      ringKrullDim (Localization.AtPrime q) = ringKrullDim ACompletion := by
    calc
      ringKrullDim (Localization.AtPrime q) = q.height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height q _
      _ = ringKrullDim ACompletion := by
        change (maximalIdeal ACompletion).height = ringKrullDim ACompletion
        exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hq : q.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    simpa [q, Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap A ACompletion)).symm
  have hclosedFiber :
      ringKrullDim
        ((Localization.AtPrime q) ⧸
          Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A)) = 0 := by
    have hmap :
        Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A) =
          maximalIdeal (Localization.AtPrime q) := by
      calc
        Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A) =
            Ideal.map (algebraMap ACompletion (Localization.AtPrime q))
              (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
              rw [show algebraMap A (Localization.AtPrime q) =
                  (algebraMap ACompletion (Localization.AtPrime q)).comp (algebraMap A ACompletion) by
                    ext x
                    rfl, Ideal.map_map]
        _ = Ideal.map (algebraMap ACompletion (Localization.AtPrime q)) q := by
              simpa [q] using
                congrArg (Ideal.map (algebraMap ACompletion (Localization.AtPrime q)))
                  (completionMap_maximalIdeal_eq_maximalIdeal A)
        _ = maximalIdeal (Localization.AtPrime q) := by
              simpa [q] using
        (IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q))
    rw [hmap]
    letI : Field (Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q)) :=
      Ideal.Quotient.field (maximalIdeal (Localization.AtPrime q))
    have hfield : IsField (Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q)) := by
      exact Field.toIsField _
    exact ringKrullDim_eq_zero_of_isField hfield
  calc
    ringKrullDim A = ringKrullDim (Localization.AtPrime (maximalIdeal A)) := hlocalA.symm
    _ = ringKrullDim (Localization.AtPrime q) := by
      have hdim :=
        ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown
          (maximalIdeal A) q hq
      rw [hclosedFiber, add_zero] at hdim
      exact hdim.symm
    _ = ringKrullDim ACompletion := hlocalCompletion

end

/-! ### Lemma_15_43_2 (from Chap15) -/
open IsLocalRing

universe u

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

-- Domain-style sampling:
-- * primary domain: local commutative algebra of depth and maximal-ideal adic completion.
-- * sampled owner declarations:
--   `moduleDepth`,
--   `depth_target_eq_depth_source_add_depth_closed_fiber`,
--   `moduleDepth_self_eq_zero_of_field`,
--   `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
--   the canonical instance `Field ClosedFiber`.
-- * owner abstraction: the local-depth owner `moduleDepth` together with the canonical closed
--   fiber owner `ClosedFiber`; the completion-specific local and flat
--   structure and the depth-zero field input are derived from the completion-map and closed-fiber
--   instances supplied by Lemma `15.43.1`.
-- * primitive data: the local Noetherian ring `A`.
-- * derived API: locality of the completion map, faithful flatness of the completion algebra, and
--   the identification of the closed fiber with the residue-field quotient.
--
-- Source/core/bridge triage:
-- * source-facing: equality of the depth of a Noetherian local ring and the depth of its
--   maximal-ideal adic completion;
-- * core/canonical: `moduleDepth` and the closed-fiber owner `ClosedFiber`;
-- * bridge/view: the completion map `A → ACompletion` together with the field identification of
--   its closed fiber.

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

local instance : Module.Finite ACompletion ACompletion :=
  Module.Finite.self ACompletion

private theorem closedFiber_moduleDepth_eq_zero :
    moduleDepth ClosedFiber ClosedFiber = 0 := by
  letI : Ring.KrullDimLE 0 ClosedFiber :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <|
      ringKrullDim_eq_zero_of_isField (Field.toIsField ClosedFiber)
  let hCM : Module.CohenMacaulay ClosedFiber ClosedFiber :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiber
  have hdepth :
      ringKrullDim ClosedFiber = .some (moduleDepth ClosedFiber ClosedFiber) :=
    (Module.supportDim_self_eq_ringKrullDim ClosedFiber).symm.trans hCM.supportDim_eq_moduleDepth
  rw [ringKrullDim_eq_zero_of_isField (Field.toIsField ClosedFiber)] at hdepth
  simpa using hdepth.symm

-- Proof sketch: apply the flat local-homomorphism depth formula
-- `depth_target_eq_depth_source_add_depth_closed_fiber` to the completion map
-- `A → AdicCompletion (maximalIdeal A) A`. The closed fiber is canonically isomorphic to the
-- residue-field quotient by the extended maximal ideal, hence is a field and has depth `0`.
/-- Lemma 15.43.2: a Noetherian local ring and its maximal-ideal adic completion have the same
depth. -/
theorem moduleDepth_eq_moduleDepth_maximalIdeal_adicCompletion :
    moduleDepth A A = moduleDepth ACompletion ACompletion := by
  let _ : Module.Flat A ACompletion :=
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A).flat
  have hdepth :
      moduleDepth ACompletion ACompletion =
        moduleDepth A A + moduleDepth ClosedFiber ClosedFiber :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [closedFiber_moduleDepth_eq_zero A] using hdepth.symm

end

/-! ### Lemma_15_43_3 (from Chap15) -/
universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
* primary domain: Cohen-Macaulay local rings under maximal-ideal adic completion.
* sampled owner declarations:
  `Module.CohenMacaulay`,
  `cohenMacaulayRing_iff_source_and_closedFiber`,
  `Ideal.Fiber`,
  `self_cohenMacaulay_of_krullDimLE_zero`.
* owner abstraction: the core owner is `Module.CohenMacaulay` on the self-module; this lemma is
  the `bridge/view` specialization of the flat-local closed-fiber equivalence to the canonical
  completion map `A → AdicCompletion (maximalIdeal A) A`.
* primitive data: the Noetherian local ring `A`.
* derived API: the completion map and target local structure from Lemma `15.43.1`, and the
  Cohen-Macaulayness of the completion closed fiber derived from its canonical field structure.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

private theorem closedFiber_cohenMacaulay :
    Module.CohenMacaulay ClosedFiber ClosedFiber := by
  let _ : Ring.KrullDimLE 0 ClosedFiber :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <|
      ringKrullDim_eq_zero_of_field ClosedFiber
  exact self_cohenMacaulay_of_krullDimLE_zero ClosedFiber

-- Proof sketch: specialize the flat-local closed-fiber criterion of Lemma `10.163.3` to the
-- canonical completion map `A → ACompletion`. Lemma `15.43.1` supplies the required completion
-- map structure and identifies the closed fiber as a field, hence Cohen-Macaulay.
/-- Lemma 15.43.3: a Noetherian local ring is Cohen-Macaulay if and only if its maximal-ideal
adic completion is Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_maximalIdeal_adicCompletion :
    Module.CohenMacaulay A A ↔ Module.CohenMacaulay ACompletion ACompletion := by
  have hiff :
      Module.CohenMacaulay ACompletion ACompletion ↔
        Module.CohenMacaulay A A ∧ Module.CohenMacaulay ClosedFiber ClosedFiber :=
    cohenMacaulayRing_iff_source_and_closedFiber
  constructor
  · intro hA
    exact hiff.2 ⟨hA, closedFiber_cohenMacaulay A⟩
  · intro hCompletion
    exact (hiff.1 hCompletion).1

end

/-! ### Lemma_15_43_4 (from Chap15) -/
universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling:
* primary domain: regular local rings and maximal-ideal adic completion in local commutative
  algebra;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  the canonical instance `Field (Ideal.Fiber (maximalIdeal A) ACompletion)`.
* owner abstraction: the canonical regular-local owner `IsRegularLocalRing` on `A` and on its
  maximal-ideal completion `AdicCompletion (maximalIdeal A) A`;
* primitive data: the Noetherian local ring `A`;
* derived API: Noetherianity and locality of the completion, the completion-map local-hom
  instance from Lemma `15.43.1`, and regularity of the closed fiber.

Source/core/bridge triage:
* source-facing: the textbook equivalence between regularity of `A` and of its maximal-ideal
  completion;
* core/canonical: the owner predicate `IsRegularLocalRing`;
* bridge/view: the completion map `A → A^∧` and the closed fiber
  `Ideal.Fiber (maximalIdeal A) A^∧`.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

-- Proof sketch: apply the flat local ascent lemma
-- `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber` to the completion map
-- `A → AdicCompletion (maximalIdeal A) A`; its closed fiber is the residue field of `A`, hence
-- regular. For the converse, use the flat local descent lemma
-- `isRegularLocalRing_of_flat_localHom_of_regularTarget`.
/-- Lemma 15.43.4: a Noetherian local ring is regular if and only if its maximal-ideal adic
completion is regular. -/
theorem isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion :
    IsRegularLocalRing A ↔ IsRegularLocalRing ACompletion := by
  have hclosedFiber : IsRegularLocalRing ClosedFiber := inferInstance
  constructor
  · intro hA
    let _ : IsRegularLocalRing A := hA
    exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber
  · intro hCompletion
    let _ : IsRegularLocalRing ACompletion := hCompletion
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget ACompletion

end

/-! ### Lemma_15_43_5 (from Chap15) -/
universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling:
* primary domain: local commutative algebra of discrete valuation rings, regular local rings, and
  maximal-ideal adic completion;
* sampled owner declarations:
  `IsDiscreteValuationRing`,
  `discreteValuationRing_tfae`,
  `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion`,
  `ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion`;
* owner abstraction: the canonical owner `IsDiscreteValuationRing`, used on arbitrary commutative
  rings through the source-facing existential bridge
  `∃ (_ : IsDomain A), IsDiscreteValuationRing A`;
* primitive data: the Noetherian local ring `A`;
* derived API: the regular-local and dimension-one bridge
  `discreteValuationRing_iff_regularLocalRing_dim_one`, plus preservation of regularity
  and Krull dimension under maximal-ideal completion.

Source/core/bridge triage:
* source-facing: the textbook equivalence between `A` being a DVR and its maximal-ideal completion
  being a DVR;
* core/canonical: the owner predicate `IsDiscreteValuationRing`;
* bridge/view: the regular-local-dimension-one bridge
  `discreteValuationRing_iff_regularLocalRing_dim_one` together with the completion
  comparison theorems for regularity and Krull dimension.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

-- Proof sketch: use Lemma `10.119.7` to characterize discrete valuation rings among Noetherian
-- local rings as the one-dimensional regular local rings. Then apply Lemma `15.43.4` for the
-- regular-local condition and Lemma `15.43.1` for preservation of Krull dimension under maximal-
-- ideal adic completion.
/-- Lemma 15.43.5: a Noetherian local ring `A` is a discrete valuation ring if and only if its
maximal-ideal adic completion is a discrete valuation ring. -/
theorem isDiscreteValuationRing_iff_isDiscreteValuationRing_maximalIdeal_adicCompletion :
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
      ∃ (_ : IsDomain ACompletion), IsDiscreteValuationRing ACompletion := by
  calc
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
        IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
      discreteValuationRing_iff_regularLocalRing_dim_one
    _ ↔ IsRegularLocalRing ACompletion ∧ ringKrullDim A = 1 := by
      exact and_congr
        (isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion A) Iff.rfl
    _ ↔ IsRegularLocalRing ACompletion ∧ ringKrullDim ACompletion = 1 := by
      simp [ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion A]
    _ ↔ ∃ (_ : IsDomain ACompletion), IsDiscreteValuationRing ACompletion :=
      discreteValuationRing_iff_regularLocalRing_dim_one.symm

end

/-! ### Lemma_15_43_6 (from Chap15) -/
universe u

open IsLocalRing

/-
Domain triage:
- primary domain: Noetherian local rings, maximal-ideal completions, and analytic unramifiedness;
- sampled owner declarations: `IsAnalyticallyUnramified`,
  `isReduced_of_isAnalyticallyUnramified`,
  and `isAnalyticallyUnramified_of_isReduced_of_minimalPrimes`;
- core/canonical owner: `IsAnalyticallyUnramified` for the completion-reducedness owner and its
  reducedness consequences;
- source-facing bridge: reducedness of `AdicCompletion (maximalIdeal A) A` is the completion view
  of `IsAnalyticallyUnramified A`, while the Chapter 15 statements themselves remain phrased in the
  source completion language.

Primitive vs derived:
- the owner-level datum for completion-reducedness is `IsAnalyticallyUnramified`;
- reducedness of `A` and of minimal-prime quotients are derived owner API, so this file should
  reuse those chapter owners instead of rebuilding a parallel completion-descent argument.
-/

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

section

variable [IsNoetherianRing A]

-- Proof sketch: reducedness of the maximal-ideal completion is exactly the owner hypothesis
-- `IsAnalyticallyUnramified A`, so the result is the Chapter `10.162.10 (1)` theorem reused in the
-- source completion language.
/-- Lemma 15.43.6 (1): if the maximal-ideal adic completion of a Noetherian local ring `A` is
reduced, then `A` is reduced. -/
theorem isReduced_of_maximalIdealAdicCompletion_isReduced
    [IsReduced ACompletion] : IsReduced A := by
  letI : IsAnalyticallyUnramified A := (isAnalyticallyUnramified_iff A).2 inferInstance
  exact isReduced_of_isAnalyticallyUnramified A

end

-- Proof sketch: Example `10.119.5` constructs a one-dimensional Noetherian local domain whose
-- maximal-ideal adic completion is not reduced. Taking that explicit example yields a reduced
-- Noetherian local ring for which the converse of part `(1)` fails.
/-- Lemma 15.43.6 (2): in general, there exists a reduced Noetherian local ring whose
maximal-ideal adic completion is not reduced. -/
theorem exists_reduced_noetherian_local_ring_with_nonreduced_completion :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A),
      IsReduced A ∧ ¬ IsReduced (AdicCompletion (maximalIdeal A) A) := by
  obtain ⟨A, _, _, _, _, _, _, hA, _⟩ :=
    exists_charZero_nonstabilizing_finite_semilocal_domain_overring_sequence
  refine ⟨A, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  simpa [isAnalyticallyUnramified_iff A] using hA

section

variable [NagataRing A]

local instance (p : minimalPrimes A) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

local instance (p : minimalPrimes A) : IsLocalRing (A ⧸ p.1) :=
  primeSpectrum_quotient_isLocalRing ⟨p.1, inferInstance⟩

local instance (p : minimalPrimes A) : NagataRing (A ⧸ p.1) :=
  nagataRing_of_finiteType A

/-- Lemma 15.43.6 (3): for a Nagata local ring `A`, reducedness is equivalent to reducedness of
its maximal-ideal adic completion. -/
theorem nagataRing_isReduced_iff_maximalIdealAdicCompletion_isReduced :
    IsReduced A ↔ IsReduced ACompletion := by
  constructor
  · intro hA
    letI : IsReduced A := hA
    letI : IsAnalyticallyUnramified A :=
      isAnalyticallyUnramified_of_isReduced_of_minimalPrimes A (fun _ ↦ inferInstance)
    exact inferInstance
  · intro hCompletion
    letI : IsReduced ACompletion := hCompletion
    exact isReduced_of_maximalIdealAdicCompletion_isReduced

end

end

/-! ### Lemma_15_43_7 (from Chap15) -/
open IsLocalRing

universe u

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: local commutative algebra of normality and maximal-ideal adic completion;
- sampled owner declarations:
  `IsNormalRing`,
  `isNormalRing_of_faithfullyFlat`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`;
- `source-facing`: the source theorem that normality of the maximal-ideal completion descends to
  `A`;
- `core/canonical`: `IsNormalRing`;
- `bridge/view`: faithful flatness of the canonical completion map `A → ACompletion`;
- primitive data: the Noetherian local ring `A`.
-/

-- Proof sketch: the canonical map `A → AdicCompletion (maximalIdeal A) A` is faithfully flat by
-- `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`. Apply the faithfully flat descent
-- statement `isNormalRing_of_faithfullyFlat` to this map.
/-- Lemma 15.43.7: if the maximal-ideal adic completion of a Noetherian local ring `A` is normal,
then `A` is normal. -/
theorem isNormalRing_of_maximalIdealAdicCompletion_isNormal
    [IsNormalRing ACompletion] :
    IsNormalRing A :=
  isNormalRing_of_faithfullyFlat
    (algebraMap A ACompletion)
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A)

end

/-! ### Lemma_15_43_8 (from Chap15) -/
noncomputable section

open IsLocalRing Algebra.TensorProduct
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B

/- Domain triage:
* `source-facing`: Lemma `15.43.8` compares flatness of a local map of Noetherian local rings
  with flatness of the induced map on maximal-ideal completions.
* `core/canonical` owners: `maximalIdealCompletionMap` for the induced completed map and
  `RingHom.Flat` for the flatness property of ring homomorphisms.
* `bridge/view`: faithful flatness of the completion maps from Lemma `10.97.3`, the descent owner
  `algebraMap_flat_of_flat_of_faithfullyFlat` from Lemma `10.39.10`, and the canonical
  base-change owner `Module.Flat.baseChange`.
* sampled declarations in the same domain:
  `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_comp`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`,
  `Module.Flat.baseChange`,
  `Algebra.TensorProduct.lidOfCompatibleSMul`.

Primitive data are the local ring map `f : A →+* B` and the Noetherian local hypotheses on `A`
and `B`. The completed comparison map and the faithfully-flat base-change/descent infrastructure
are derived from the owner declarations above, so this file keeps only the source-facing theorem. -/

-- Proof sketch: if the induced map `A^∧ → B^∧` is flat, compose it with the faithfully flat map
-- `A → A^∧` to obtain flatness of `A → B^∧`, then apply the owner descent theorem
-- `algebraMap_flat_of_flat_of_faithfullyFlat` to the faithfully flat map `B → B^∧`. Conversely,
-- if `A → B` is flat, then `A → B^∧` is flat because `B → B^∧` is flat; faithful flatness of
-- `A → A^∧` upgrades this by base change to flatness of `A^∧ ⊗[A] B^∧` over `A^∧`, and the
-- canonical tensor-action equivalence
-- `A^∧ ⊗[A] B^∧ ≃ B^∧` yields flatness of `A^∧ → B^∧`.
/-- Lemma 15.43.8: for a local homomorphism `f : A →+* B` of Noetherian local rings, the induced
map on maximal-ideal completions is flat if and only if `f` is flat. -/
theorem flat_iff_flat_maximalIdealCompletionMap (f : A →+* B) [IsLocalHom f] :
    (maximalIdealCompletionMap f).Flat ↔ f.Flat := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B BCompletion := (algebraMap B BCompletion).toAlgebra
  letI : Algebra A BCompletion := ((algebraMap B BCompletion).comp f).toAlgebra
  letI : Algebra ACompletion BCompletion := (maximalIdealCompletionMap f).toAlgebra
  letI : IsScalarTower A ACompletion BCompletion :=
    IsScalarTower.of_algebraMap_eq' <| by
      simpa [RingHom.algebraMap_toAlgebra] using (maximalIdealCompletionMap_comp f).symm
  have hACompletion_ff : (algebraMap A ACompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  have hBCompletion_ff : (algebraMap B BCompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat B
  letI : Module.FaithfullyFlat A ACompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hACompletion_ff
  letI : Module.FaithfullyFlat B BCompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hBCompletion_ff
  constructor
  · intro hCompletion
    have hABCompletion_comp : ((algebraMap B BCompletion).comp f).Flat := by
      simpa [maximalIdealCompletionMap_comp f] using
        RingHom.Flat.comp hACompletion_ff.flat hCompletion
    have hABCompletion : (algebraMap A BCompletion).Flat := by
      simpa [RingHom.algebraMap_toAlgebra] using hABCompletion_comp
    letI : Module.Flat A BCompletion := RingHom.flat_algebraMap_iff.mp hABCompletion
    letI : Module.Flat A (RestrictScalars A B BCompletion) := by
      change Module.Flat A BCompletion
      infer_instance
    simpa [RingHom.algebraMap_toAlgebra] using
      (algebraMap_flat_of_flat_of_faithfullyFlat BCompletion : (algebraMap A B).Flat)
  · intro hf
    sorry

end

/-! ### Lemma_15_43_9 (from Chap15) -/
noncomputable section

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]

/- The comparison map on maximal-ideal completions is the owner theorem
`maximalIdealCompletionMap_comp` from Lemma `10.97.7`, specialized to `algebraMap A B`. -/
recall maximalIdealCompletionMap_comp

-- Proof sketch: apply Lemma `10.97.7` to identify `B^∧` with the completion of `B` along
-- `maximalIdeal A`, use Lemma `15.27.5` to deduce flatness of `B^∧` over `A^∧`, then invoke
-- `Module.free_of_flat_of_isLocalRing` from Lemma `10.78.5`. The residue-field bijectivity
-- hypothesis shows that the closed fiber has dimension one over the residue field, so the free
-- module has rank `1`, forcing the canonical completion map to be bijective.
/-- Lemma 15.43.9: if `A → B` is a flat local homomorphism of Noetherian local rings, the
maximal ideal of `B` is the extension of the maximal ideal of `A`, and the induced map on residue
fields is bijective, then the induced map `A^∧ → B^∧` on maximal-ideal completions is
bijective. -/
theorem maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (maximalIdealCompletionMap (algebraMap A B)) := sorry

end
