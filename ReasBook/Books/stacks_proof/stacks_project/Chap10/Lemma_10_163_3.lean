import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_104_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_3
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_163_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-
Domain-style sampling pass:
* primary domain: local commutative algebra of Cohen-Macaulay local rings under flat local
  homomorphisms, with the closed fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Module.CohenMacaulay`,
  `Ideal.Fiber`,
  `depth_target_eq_depth_source_add_depth_closed_fiber`,
  `Module.supportDim_self_eq_ringKrullDim`;
* best owner abstraction: the Cohen-Macaulay conditions should stay on the owner
  `Module.CohenMacaulay`, and the closed fiber should be expressed by the canonical ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`; the quotient `S ⧸ 𝔪S` is only a bridge/view.

Primitive data vs. derived API:
* primitive data: only the flat local algebra map `R → S`;
* derived API: the quotient presentation `S ⧸ 𝔪S` of the closed fiber and the induced local and
  Noetherian instances used to formulate the owner statement on `ClosedFiber`.

Source/core/bridge triage:
* `source-facing`: the Stacks equivalence saying that `S` is Cohen-Macaulay iff both `R` and the
  closed fiber are Cohen-Macaulay;
* `core/canonical`: `Module.CohenMacaulay` and `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`;
* `bridge/view`: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.
-/

private noncomputable def closedFiberQuotEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

attribute [local instance] closedFiber_isLocalRing closedFiber_isNoetherianRing

-- Proof sketch: combine Lemma `10.163.2`, which gives the additivity formula for the depth of
-- `S`, with Lemma `10.112.7`, which gives the corresponding dimension formula for the canonical
-- closed fiber `ClosedFiber`. Then rewrite the Cohen-Macaulay condition on `R`, `S`, and
-- `ClosedFiber` as the equality between depth and Krull dimension, using the quotient view only
-- internally, and compare the two formulas.
/-- Helper for Lemma 10.163.3: the depth additivity theorem from Lemma `10.163.1`, specialized to
the self-modules `R` and `S`, identifies the target depth with the source depth plus the depth of
the canonical closed fiber. -/
private theorem moduleDepth_target_eq_moduleDepth_source_add_moduleDepth_closedFiber :
    moduleDepth S S = moduleDepth R R + moduleDepth ClosedFiber ClosedFiber := by
  -- The tensor terms in Lemma `10.163.1` collapse to the underlying rings by the right-unit
  -- tensor equivalences.
  rw [← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid R S S).toLinearEquiv,
    ← moduleDepth_eq_of_equiv (Algebra.TensorProduct.rid S ClosedFiber ClosedFiber).toLinearEquiv]
  simpa using
    (depth_tensorProduct_eq_depth_add_depth_closedFiber :
      moduleDepth S (S ⊗[R] R) =
        moduleDepth R R + moduleDepth ClosedFiber (ClosedFiber ⊗[S] S))

/-- Helper for Lemma 10.163.3: specializing Lemma `10.112.7` at the closed point yields the
dimension formula for the source, target, and canonical closed fiber. -/
private theorem ringKrullDim_target_eq_ringKrullDim_source_add_ringKrullDim_closedFiber :
    ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber := by
  let q : PrimeSpectrum S := ⟨maximalIdeal S, inferInstance⟩
  let h_unitsR : (maximalIdeal R).primeCompl ≤ IsUnit.submonoid R := by
    intro r hr
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hr
  let h_unitsS : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := by
    intro s hs
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hs
  let pUnder : Ideal R := Ideal.under R (maximalIdeal S)
  letI : pUnder.IsPrime := by
    dsimp [pUnder]
    infer_instance
  have hpUnder : pUnder = maximalIdeal R := by
    simpa [pUnder, Ideal.under_def] using
      IsLocalRing.maximalIdeal_comap (algebraMap R S)
  let h_unitsP : pUnder.primeCompl ≤ IsUnit.submonoid R := by
    intro r hr
    have hr' : r ∉ maximalIdeal R := by
      simpa [pUnder, hpUnder] using hr
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hr'
  letI : IsLocalization pUnder.primeCompl R := IsLocalization.self h_unitsP
  letI : IsLocalization (maximalIdeal S).primeCompl S := IsLocalization.self h_unitsS
  let eP : Localization.AtPrime pUnder ≃ₐ[R] R :=
    IsLocalization.algEquiv pUnder.primeCompl (Localization.AtPrime pUnder) R
  let eS : Localization.AtPrime (maximalIdeal S) ≃ₐ[S] S :=
    IsLocalization.algEquiv (maximalIdeal S).primeCompl
      (Localization.AtPrime (maximalIdeal S)) S
  let Iunder : Ideal (Localization.AtPrime (maximalIdeal S)) :=
    Ideal.map (algebraMap R (Localization.AtPrime (maximalIdeal S))) pUnder
  have hIunder_map : Ideal.map eS.toRingHom Iunder = 𝔪S := by
    -- Rewriting the localized source ideal through the local equivalence recovers `𝔪_R S`.
    calc
      Ideal.map eS.toRingHom Iunder =
          Ideal.map
            (eS.toRingHom.comp (algebraMap R (Localization.AtPrime (maximalIdeal S))))
            pUnder := by
              simpa [Iunder] using
                (Ideal.map_map (I := pUnder)
                  (algebraMap R (Localization.AtPrime (maximalIdeal S))) eS.toRingHom)
      _ = Ideal.map (algebraMap R S) pUnder := by
        congr 1
        ext r
        simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime (maximalIdeal S))] using
          (eS.commutes (algebraMap R S r))
      _ = Ideal.map (algebraMap R S) (maximalIdeal R) := by
        rw [hpUnder]
      _ = 𝔪S := rfl
  have hIunder_comap : Ideal.comap eS.toRingHom 𝔪S = Iunder := by
    rw [← hIunder_map, Ideal.comap_map_of_surjective eS.toRingHom eS.surjective,
      Ideal.comap_bot_of_injective (f := eS.toRingHom) eS.injective, sup_eq_left]
    exact bot_le
  let φ : Localization.AtPrime (maximalIdeal S) →+* S ⧸ 𝔪S :=
    (Ideal.Quotient.mk 𝔪S).comp eS.toRingHom
  have hφ_surj : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp eS.surjective
  have hker_aux :
      RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) =
        Ideal.comap eS.toRingHom 𝔪S := by
    ext z
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hkerφ : RingHom.ker φ = Iunder := by
    change RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) = Iunder
    rw [hker_aux, hIunder_comap]
  let eQ : (Localization.AtPrime (maximalIdeal S)) ⧸ Iunder ≃+* S ⧸ 𝔪S :=
    (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφ_surj)
  have hdimLoc :
      ringKrullDim (Localization.AtPrime (maximalIdeal S)) =
        ringKrullDim (Localization.AtPrime pUnder) +
          ringKrullDim ((Localization.AtPrime (maximalIdeal S)) ⧸ Iunder) := by
    -- This is exactly Lemma `10.112.7` at the maximal ideal of `S`.
    change
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime pUnder) +
          ringKrullDim
            ((Localization.AtPrime q.asIdeal) ⧸
              Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) pUnder)
    simpa [q, pUnder, Iunder] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
        (R := R) (S := S) q
  -- Move the localized dimension identity back to the original local rings and the owner closed
  -- fiber `ClosedFiber`.
  calc
    ringKrullDim S = ringKrullDim (Localization.AtPrime (maximalIdeal S)) := by
      symm
      exact ringKrullDim_eq_of_ringEquiv eS.toRingEquiv
    _ = ringKrullDim (Localization.AtPrime pUnder) +
          ringKrullDim ((Localization.AtPrime (maximalIdeal S)) ⧸ Iunder) := by
      exact hdimLoc
    _ = ringKrullDim R + ringKrullDim (S ⧸ 𝔪S) := by
      rw [ringKrullDim_eq_of_ringEquiv eP.toRingEquiv, ringKrullDim_eq_of_ringEquiv eQ]
    _ = ringKrullDim R + ringKrullDim ClosedFiber := by
      congr 1
      exact ringKrullDim_eq_of_ringEquiv closedFiberQuotEquiv.toRingEquiv.symm

/-- Helper for Lemma 10.163.3: Cohen-Macaulayness of the source and closed fiber implies
Cohen-Macaulayness of the target. -/
private theorem cohenMacaulay_target_of_source_and_closedFiber
    (hR : Module.CohenMacaulay R R) (hF : Module.CohenMacaulay ClosedFiber ClosedFiber) :
    Module.CohenMacaulay S S := by
  refine Module.CohenMacaulay.mk ?_
  have hRdim :
      ringKrullDim R = WithBot.some (moduleDepth R R : ℕ∞) := by
    simpa [Module.supportDim_self_eq_ringKrullDim] using hR.supportDim_eq_moduleDepth
  have hFdim :
      ringKrullDim ClosedFiber = WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
    simpa [Module.supportDim_self_eq_ringKrullDim] using hF.supportDim_eq_moduleDepth
  -- Match the depth formula from Lemma `10.163.2` with the dimension formula proved above.
  calc
    Module.supportDim S S = ringKrullDim S := by
      rw [Module.supportDim_self_eq_ringKrullDim]
    _ = ringKrullDim R + ringKrullDim ClosedFiber :=
      ringKrullDim_target_eq_ringKrullDim_source_add_ringKrullDim_closedFiber
    _ = WithBot.some (moduleDepth R R : ℕ∞) +
          WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
      rw [hRdim, hFdim]
    _ = WithBot.some (moduleDepth R R + moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
      simp
    _ = WithBot.some (moduleDepth S S : ℕ∞) := by
      simpa using
        congrArg (fun d : ℕ∞ ↦ WithBot.some d)
          (moduleDepth_target_eq_moduleDepth_source_add_moduleDepth_closedFiber
            (R := R) (S := S)).symm

/-- Helper for Lemma 10.163.3: Cohen-Macaulayness of the target forces both the source and the
canonical closed fiber to be Cohen-Macaulay. -/
private theorem cohenMacaulay_source_and_closedFiber_of_target
    (hS : Module.CohenMacaulay S S) :
    Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiber ClosedFiber := by
  have hR_le :
      WithBot.some (moduleDepth R R : ℕ∞) ≤ ringKrullDim R := by
    simpa [Module.supportDim_self_eq_ringKrullDim] using
      (depth_le_supportDim (R := R) (M := R))
  have hF_le :
      WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) ≤ ringKrullDim ClosedFiber := by
    simpa [Module.supportDim_self_eq_ringKrullDim] using
      (depth_le_supportDim (R := ClosedFiber) (M := ClosedFiber))
  have hsum :
      ringKrullDim R + ringKrullDim ClosedFiber =
        WithBot.some (moduleDepth R R : ℕ∞) +
          WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
    -- Rewriting the target Cohen-Macaulay equality through the two additivity formulas yields one
    -- equality of sums.
    calc
      ringKrullDim R + ringKrullDim ClosedFiber = ringKrullDim S := by
        simpa using ringKrullDim_target_eq_ringKrullDim_source_add_ringKrullDim_closedFiber.symm
      _ = WithBot.some (moduleDepth S S : ℕ∞) := by
        simpa [Module.supportDim_self_eq_ringKrullDim] using hS.supportDim_eq_moduleDepth
      _ = WithBot.some (moduleDepth R R + moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
        simpa using
          congrArg (fun d : ℕ∞ ↦ WithBot.some d)
            (moduleDepth_target_eq_moduleDepth_source_add_moduleDepth_closedFiber
              (R := R) (S := S))
      _ = WithBot.some (moduleDepth R R : ℕ∞) +
            WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
        simp
  have hR_depth_ne_top :
      WithBot.some (moduleDepth R R : ℕ∞) ≠ ⊤ := by
    exact (lt_of_le_of_lt hR_le (ringKrullDim_lt_top (R := R))).ne
  have hF_depth_ne_top :
      WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) ≠ ⊤ := by
    exact (lt_of_le_of_lt hF_le (ringKrullDim_lt_top (R := ClosedFiber))).ne
  have hR_ge :
      ringKrullDim R ≤ WithBot.some (moduleDepth R R : ℕ∞) := by
    have haux :
        ringKrullDim R + WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) ≤
          WithBot.some (moduleDepth R R : ℕ∞) +
            WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
      calc
        ringKrullDim R + WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) ≤
            ringKrullDim R + ringKrullDim ClosedFiber := by
              gcongr
        _ = WithBot.some (moduleDepth R R : ℕ∞) +
              WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := hsum
    exact
      (WithBot.add_le_add_iff_right'
        (c := WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞))
        (by simp) hF_depth_ne_top).mp haux
  have hF_ge :
      ringKrullDim ClosedFiber ≤ WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := by
    have haux :
        ringKrullDim ClosedFiber + WithBot.some (moduleDepth R R : ℕ∞) ≤
          WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) +
            WithBot.some (moduleDepth R R : ℕ∞) := by
      calc
        ringKrullDim ClosedFiber + WithBot.some (moduleDepth R R : ℕ∞) ≤
            ringKrullDim ClosedFiber + ringKrullDim R := by
              gcongr
        _ = ringKrullDim R + ringKrullDim ClosedFiber := by
          rw [add_comm]
        _ = WithBot.some (moduleDepth R R : ℕ∞) +
              WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) := hsum
        _ = WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) +
              WithBot.some (moduleDepth R R : ℕ∞) := by
          rw [add_comm]
    exact
      (WithBot.add_le_add_iff_right'
        (c := WithBot.some (moduleDepth R R : ℕ∞))
        (by simp) hR_depth_ne_top).mp haux
  have hR_eq :
      ringKrullDim R = WithBot.some (moduleDepth R R : ℕ∞) :=
    le_antisymm hR_ge hR_le
  have hF_eq :
      ringKrullDim ClosedFiber = WithBot.some (moduleDepth ClosedFiber ClosedFiber : ℕ∞) :=
    le_antisymm hF_ge hF_le
  refine ⟨Module.CohenMacaulay.mk ?_, Module.CohenMacaulay.mk ?_⟩
  · -- The source ring satisfies depth equals dimension because the total equality forces
    -- equality in the source summand.
    simpa [Module.supportDim_self_eq_ringKrullDim] using hR_eq
  · -- The same cancellation argument identifies depth and dimension on the closed fiber.
    simpa [Module.supportDim_self_eq_ringKrullDim] using hF_eq

/-- Lemma 10.163.3: for a flat local homomorphism `R → S` of local Noetherian rings, `S` is
Cohen-Macaulay if and only if both `R` and the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently `S / 𝔪_R S`, are Cohen-Macaulay. -/
@[stacks 045J]
theorem cohenMacaulayRing_iff_source_and_closedFiber :
    Module.CohenMacaulay S S ↔
      Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiber ClosedFiber := by
  -- Proof comment: the source-faithful route is exactly the textbook one: pair the depth formula
  -- from Lemma `10.163.2` with the closed-point dimension formula from Lemma `10.112.7`.
  constructor
  · exact cohenMacaulay_source_and_closedFiber_of_target
  · rintro ⟨hR, hF⟩
    exact cohenMacaulay_target_of_source_and_closedFiber hR hF

end
