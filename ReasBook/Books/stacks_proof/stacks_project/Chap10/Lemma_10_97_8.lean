import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Ideal AdicCompletion
open scoped TensorProduct

universe u v

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable (p : PrimeSpectrum R)

local notation "Rₚ" => Localization.AtPrime p.asIdeal
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
local notation "mₚ" => maximalIdeal Rₚ
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) mₚ
local notation "Rₚ^" => AdicCompletion mₚ Rₚ

/- Domain triage:
* primary domain: semilocal localization of a finite algebra over a prime, and completion along
  the induced maximal ideal;
* source-facing layer: the product decomposition of the completed semilocal localization into the
  completed local rings at the primes lying over `p`;
* core/canonical owners sampled for this refinement:
  `Ideal.primesOver`,
  `PrimeSpectrum.primesOverOrderIsoFiber`,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`,
  `MaximalSpectrum.toPiLocalizationEquiv`,
  `AdicCompletion.piEquivOfFintype`;
* bridge/view role here: the source theorem is phrased on the fiber of `Spec(S) → Spec(R)`,
  while the owner object for the indexing set is `p.asIdeal.primesOver S`; the bridge is
  `PrimeSpectrum.primesOverOrderIsoFiber`.

Primitive data are `R`, `S`, the prime `p`, and the finite set `p.asIdeal.primesOver S`. The
public output is the source-facing tensor term `Rₚ^ ⊗[R] S`, its canonical bridge to the
localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ`, and the comparison map from the completed semilocal
localization to the product of completed local rings indexed by that owner set; bijectivity then
packages the latter as the canonical equivalence. -/

/- Companion owners used below:
`PrimeSpectrum.primesOverOrderIsoFiber` identifies the textbook fiber with the owner set
`p.asIdeal.primesOver S`, and
`Localization.tensorRightAlgEquiv p.asIdeal.primeCompl S` is the localization/base-change
identification `Rₚ ⊗[R] S ≃ₐ[Rₚ] Sₚ`, while
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` is the specialized
tensor-product/completion comparison after localizing at `p`. -/

/-- Lemma 10.97.8, source-facing bridge: the textbook left-hand tensor term `Rₚ^ ⊗[R] S`
canonically identifies with the localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ`. Composing this bridge
with `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` recovers the tensor/completion
comparison in the localized owner form. -/
@[stacks 07N9]
noncomputable def completion_tensorProductOverBase_algEquiv_localizedTensorProduct :
    Rₚ^ ⊗[R] S ≃ₐ[Rₚ^] Rₚ^ ⊗[Rₚ] Sₚ := by
  letI : Algebra Rₚ^ (Rₚ^ ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra Rₚ^ (Rₚ^ ⊗[Rₚ] Sₚ) := Algebra.TensorProduct.leftAlgebra
  exact
    (Algebra.TensorProduct.cancelBaseChange R Rₚ Rₚ^ Rₚ^ S).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Rₚ^ ≃ₐ[Rₚ^] Rₚ^)
        (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl S))

/-- Bridge/view for Lemma 10.97.8: the localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ` canonically
identifies, as an `Rₚ`-algebra, with the `mₚ`-adic completion of the semilocal localization
`Sₚ`. This upgrades the canonical tensor/completion comparison
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` from its linear owner form to the
ring-level comparison used in the source statement. -/
private noncomputable def completionBaseQuotientMap (n : ℕ) : Rₚ^ →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ n :=
  (Ideal.quotientMapₐ (pSₚ ^ n) (Algebra.ofId Rₚ Sₚ)
    ((Ideal.pow_right_mono (Ideal.le_comap_map : mₚ ≤ Ideal.comap (algebraMap Rₚ Sₚ) pSₚ) n).trans
      (Ideal.le_comap_pow (algebraMap Rₚ Sₚ) n))).comp
    (AdicCompletion.evalₐ mₚ n)

private theorem completionBaseQuotientMap_compatible {m n : ℕ} (h : m ≤ n) :
    ((Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h) :
      Sₚ ⧸ pSₚ ^ n →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ m)).comp (completionBaseQuotientMap p n) =
      completionBaseQuotientMap p m := by
  ext x
  let P : Rₚ^ → Prop := fun y ↦
    ((Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h) :
      Sₚ ⧸ pSₚ ^ n →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ m)).comp (completionBaseQuotientMap p n) y =
      completionBaseQuotientMap p m y
  -- Compare both quotient maps on a concrete representative of the completion element.
  change P x
  refine AdicCompletion.induction_on (I := mₚ) (M := Rₚ) x ?_
  intro r
  -- On representatives, the target equality is exactly the stage-`m` quotient compatibility,
  -- pushed forward along `Rₚ → Sₚ`; proving it directly on quotient classes avoids the slow
  -- algebra-quotient instance search at this stage.
  dsimp [P]
  simp only [completionBaseQuotientMap, AlgHom.comp_apply, AdicCompletion.evalₐ_mk,
    Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hrsub : r n - r m ∈ mₚ ^ m := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact AdicCompletion.Ideal.mk_eq_mk (I := mₚ) (m := m) (n := n) h r
  simpa [Ideal.map_pow, map_sub] using Ideal.mem_map_of_mem (algebraMap Rₚ Sₚ) hrsub

private noncomputable def completionBaseAlgHom : Rₚ^ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  AdicCompletion.liftAlgHom pSₚ (completionBaseQuotientMap p)
    (completionBaseQuotientMap_compatible p)

/-- Helper for Lemma 10.97.8: evaluating the completed base map at stage `n` recovers the
defining quotient map from the base completion. -/
private theorem completionBaseAlgHom_eval_a (n : ℕ) (x : Rₚ^) :
    AdicCompletion.evalₐ pSₚ n ((completionBaseAlgHom (S := S) p) x) =
      completionBaseQuotientMap (S := S) p n x := by
  -- This is the quotientwise evaluation formula for the algebraic completion lift.
  simpa [completionBaseAlgHom] using
    (AdicCompletion.evalₐ_liftAlgHom pSₚ
      (completionBaseQuotientMap (S := S) p)
      (completionBaseQuotientMap_compatible (S := S) p) n x)

/-- Helper for Lemma 10.97.8: the completed base map sends the canonical image of `r : Rₚ`
to the canonical image of its image in `Sₚ`. -/
private theorem completionBaseAlgHom_of (r : Rₚ) :
    ((completionBaseAlgHom p).toRingHom) (AdicCompletion.of mₚ Rₚ r) =
      AdicCompletion.of pSₚ Sₚ (algebraMap Rₚ Sₚ r) := by
  -- Compare both completed base maps after every stage evaluation.
  apply AdicCompletion.ext_evalₐ
  intro n
  simpa [completionBaseQuotientMap] using
    completionBaseAlgHom_eval_a (p := p) (S := S) n (AdicCompletion.of mₚ Rₚ r)

private noncomputable def localizedTensorProduct_to_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  Algebra.TensorProduct.productMap (completionBaseAlgHom p)
    ((Algebra.ofId Sₚ (AdicCompletion pSₚ Sₚ)).restrictScalars Rₚ)

/-- Helper for Lemma 10.97.8: on a pure tensor from the dense image of `Rₚ`, the localized
tensor/completion map is the canonical completed product in `Sₚ`. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrime_of_tmul
    (r : Rₚ) (s : Sₚ) :
    ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
        (AdicCompletion.of mₚ Rₚ r ⊗ₜ[Rₚ] s) =
      AdicCompletion.of pSₚ Sₚ (algebraMap Rₚ Sₚ r * s) := by
  -- Route correction: normalize the product-map application all the way down to the two
  -- canonical `of` terms before using multiplicativity of `AdicCompletion.of`.
  simp only [localizedTensorProduct_to_completion_localizationAtPrime,
    Algebra.TensorProduct.productMap_apply_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.restrictScalars_apply, Algebra.ofId_apply]
  simpa [AdicCompletion.algebraMap_apply] using
    (map_mul (algebraMap Sₚ (AdicCompletion pSₚ Sₚ)) (algebraMap Rₚ Sₚ r) s).symm

section

variable [IsNoetherianRing R] [Module.Finite R S]

/-- Helper for Lemma 10.97.8: the `mₚ`-power submodules on `Sₚ` are exactly the powers of the
extended ideal `pSₚ`. This is the quotient-level bridge between the module completion over `Rₚ`
and the ring completion over `Sₚ`. -/
private theorem localized_stage_smul_top_eq_stage_map (n : ℕ) :
    (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) =
      Submodule.restrictScalars Rₚ ((pSₚ ^ n : Ideal Sₚ) : Submodule Sₚ Sₚ) := by
  -- Rewrite the scalar-power submodule as the mapped ideal, then use `pSₚ = mₚ Sₚ`.
  simpa [Ideal.map_pow] using
    (Ideal.smul_top_eq_map (R := Rₚ) (S := Sₚ) (I := mₚ ^ n))

/-- Helper for Lemma 10.97.8: the semilocal ring completion is also complete for the `mₚ`-adic
`Rₚ`-module topology. This is the completeness input needed to compare the two completion models.
-/
private theorem completion_localizationAtPrime_isAdicComplete_as_module :
    IsAdicComplete mₚ (AdicCompletion pSₚ Sₚ) := by
  have hm_fg : (mₚ : Ideal Rₚ).FG := Ideal.FG.of_isNoetherianRing mₚ
  have hp_fg : (Ideal.map (algebraMap Rₚ Sₚ) mₚ : Ideal Sₚ).FG := by
    simpa using Ideal.FG.map hm_fg (algebraMap Rₚ Sₚ)
  have hcomplete_pS :
      IsAdicComplete (Ideal.map (algebraMap Rₚ Sₚ) mₚ)
        (AdicCompletion (Ideal.map (algebraMap Rₚ Sₚ) mₚ) Sₚ) :=
    AdicCompletion.isAdicComplete hp_fg
  -- Transport completeness across the algebra map `Rₚ → Sₚ`.
  exact (IsAdicComplete.map_algebraMap_iff (I := mₚ) (S := Sₚ)
    (M := AdicCompletion pSₚ Sₚ)).mp <| by
      exact hcomplete_pS

/-- Helper for Lemma 10.97.8: after restricting scalars to `Rₚ`, the stage-`n` quotient of the
`pSₚ`-adic ring completion is the same quotient of `Sₚ` used by the `mₚ`-adic module completion.
-/
private theorem localized_ring_stage_restrictScalars_eq_module_stage (n : ℕ) :
    ((pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ)).restrictScalars Rₚ : Submodule Rₚ Sₚ) =
      (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) := by
  -- Rewrite the `Sₚ`-linear stage as the extended ideal stage, then use the quotient bridge.
  calc
    ((pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ)).restrictScalars Rₚ : Submodule Rₚ Sₚ) =
        (Submodule.restrictScalars Rₚ ((pSₚ ^ n : Ideal Sₚ) : Submodule Sₚ Sₚ)) := by
          ext x
          simp
    _ = (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) := by
          symm
          exact localized_stage_smul_top_eq_stage_map (p := p) (S := S) n

/-- Helper for Chap10 Lemma 10 97 8: the stage quotient of the `pSₚ`-adic ring completion,
viewed as an `Rₚ`-module quotient, is canonically the stage quotient of the `mₚ`-adic module
completion. -/
private noncomputable def ringCompletionStageLinearEquivModuleStage (n : ℕ) :
    (Sₚ ⧸ (pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ))) ≃ₗ[Rₚ]
      Sₚ ⧸ (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) :=
  ((Submodule.Quotient.restrictScalarsEquiv Rₚ
      (pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ))).symm).trans
    (Submodule.quotEquivOfEq _ _
      (localized_ring_stage_restrictScalars_eq_module_stage (p := p) (S := S) n))

/-- Helper for Chap10 Lemma 10 97 8: the stage comparison between the two completion models sends
the class of `s : Sₚ` to the same residue class in the `mₚ`-adic module quotient. -/
private theorem ringCompletionStageLinearEquivModuleStage_mk (n : ℕ) (s : Sₚ) :
    ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk s := by
  -- Both quotient comparisons are defined by the identity on representatives.
  rfl

private noncomputable def localizedModuleCompletion_to_ringCompletion :
    AdicCompletion mₚ Sₚ →ₗ[Rₚ] AdicCompletion pSₚ Sₚ :=
  letI : IsAdicComplete mₚ (AdicCompletion pSₚ Sₚ) :=
    completion_localizationAtPrime_isAdicComplete_as_module (p := p) (S := S)
  let completionInclusion : Sₚ →ₗ[Rₚ] AdicCompletion pSₚ Sₚ :=
    ((Algebra.ofId Sₚ (AdicCompletion pSₚ Sₚ)).toLinearMap).restrictScalars Rₚ
  let completionMap :
      AdicCompletion mₚ Sₚ →ₗ[Rₚ]
        AdicCompletion mₚ (AdicCompletion pSₚ Sₚ) :=
    AdicCompletion.map mₚ completionInclusion
  (AdicCompletion.ofLinearEquiv mₚ (AdicCompletion pSₚ Sₚ)).symm.toLinearMap.comp completionMap

/-- Helper for Lemma 10.97.8: the comparison map from the `mₚ`-adic module completion to the
ring completion sends the canonical image of `s : Sₚ` to the same completed element. -/
private theorem localizedModuleCompletion_to_ringCompletion_of (s : Sₚ) :
    localizedModuleCompletion_to_ringCompletion (p := p) (S := S) (AdicCompletion.of mₚ Sₚ s) =
      AdicCompletion.of pSₚ Sₚ s := by
  -- Compute the induced map on the dense image of `Sₚ` using functoriality of completion.
  letI : IsAdicComplete mₚ (AdicCompletion pSₚ Sₚ) :=
    completion_localizationAtPrime_isAdicComplete_as_module (p := p) (S := S)
  simpa [localizedModuleCompletion_to_ringCompletion] using
    congrArg
      ((AdicCompletion.ofLinearEquiv mₚ (AdicCompletion pSₚ Sₚ)).symm :
        AdicCompletion mₚ (AdicCompletion pSₚ Sₚ) → AdicCompletion pSₚ Sₚ)
      (AdicCompletion.map_of mₚ
        (((Algebra.ofId Sₚ (AdicCompletion pSₚ Sₚ)).toLinearMap).restrictScalars Rₚ) s)

/-- Helper for Chap10 Lemma 10 97 8: the reverse comparison family evaluates an element of the
`pSₚ`-adic ring completion at stage `n` and then rewrites that quotient into the corresponding
`mₚ`-adic module quotient. -/
private noncomputable def ringCompletionToLocalizedModuleCompletionFamily (n : ℕ) :
    AdicCompletion pSₚ Sₚ →ₗ[Rₚ] Sₚ ⧸ (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) :=
  (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).toLinearMap.comp
    ((AdicCompletion.eval pSₚ Sₚ n).restrictScalars Rₚ)

/-- Helper for Chap10 Lemma 10 97 8: the reverse comparison family is compatible with the
transition maps in the inverse system defining the `mₚ`-adic module completion. -/
private theorem ringCompletionStageLinearEquivModuleStage_factor {m n : ℕ} (h : m ≤ n)
    (z : Sₚ ⧸ (pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ))) :
    AdicCompletion.transitionMap mₚ Sₚ h
        (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n z) =
      ringCompletionStageLinearEquivModuleStage (p := p) (S := S) m
        (AdicCompletion.transitionMap pSₚ Sₚ h z) := by
  -- Check transition-map naturality on quotient representatives, where both quotient bridges are
  -- induced by the identity map on `Sₚ`.
  refine Quotient.inductionOn' z ?_
  intro s
  rfl

/-- Helper for Chap10 Lemma 10 97 8: the inverse finite-stage comparison also sends quotient
representatives to the same representative. -/
private theorem ringCompletionStageLinearEquivModuleStage_symm_mk
    (n : ℕ) (s : Sₚ) :
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
        (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk s := by
  -- Apply the forward stage comparison so the inverse computation reduces to the representative
  -- formula already proved for the forward comparison.
  apply (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).injective
  rw [LinearEquiv.apply_symm_apply,
    ringCompletionStageLinearEquivModuleStage_mk]

/-- Helper for Chap10 Lemma 10 97 8: the inverse finite-stage comparison commutes with
transition maps. -/
private theorem ringCompletionStageLinearEquivModuleStage_symm_factor {m n : ℕ} (h : m ≤ n)
    (z : Sₚ ⧸ (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ))) :
    AdicCompletion.transitionMap pSₚ Sₚ h
        ((ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm z) =
      (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) m).symm
        (AdicCompletion.transitionMap mₚ Sₚ h z) := by
  -- Naturality of the inverse bridge is again checked on quotient representatives, where all
  -- maps are induced by the identity on `Sₚ`.
  refine Quotient.inductionOn' z ?_
  intro s
  rfl

/-- Helper for Chap10 Lemma 10 97 8: applying the inverse finite-stage comparison to all
coordinates of an `mₚ`-adic completion point gives a compatible `pSₚ`-adic point. -/
private theorem moduleCompletionToRingCompletionByStagesFun_compatible
    (x : AdicCompletion mₚ Sₚ) :
    ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap pSₚ Sₚ h
          ((ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
            (x.val n)) =
        (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) m).symm
          (x.val m) := by
  -- Move transition maps through the inverse stage comparison and then use the compatibility
  -- relation stored in the completion element `x`.
  intro m n h
  rw [ringCompletionStageLinearEquivModuleStage_symm_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise forward comparison from the module
completion model to the ring completion model. -/
private noncomputable def moduleCompletionToRingCompletionByStagesFun :
    AdicCompletion mₚ Sₚ → AdicCompletion pSₚ Sₚ :=
  fun x ↦
    ⟨fun n ↦
        (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
          (x.val n),
      moduleCompletionToRingCompletionByStagesFun_compatible (p := p) (S := S) x⟩

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise forward comparison sends completed
source elements to the same completed element in the ring completion model. -/
private theorem moduleCompletionToRingCompletionByStages_of (s : Sₚ) :
    moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        (AdicCompletion.of mₚ Sₚ s) =
      AdicCompletion.of pSₚ Sₚ s := by
  -- The dense-element computation is exactly the inverse finite-stage representative formula at
  -- every coordinate.
  ext n
  change
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
        (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk s
  exact ringCompletionStageLinearEquivModuleStage_symm_mk (p := p) (S := S) n s

/-- Helper for Chap10 Lemma 10 97 8: the reverse comparison family is compatible with the
transition maps in the inverse system defining the `mₚ`-adic module completion. -/
private theorem ringCompletionToLocalizedModuleCompletionFamily_compatible {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap mₚ Sₚ h ∘ₗ
        ringCompletionToLocalizedModuleCompletionFamily (p := p) (S := S) n =
      ringCompletionToLocalizedModuleCompletionFamily (p := p) (S := S) m := by
  apply LinearMap.ext
  intro x
  -- Evaluate the stagewise bridge on the `n`th quotient coordinate of `x`.
  rw [ringCompletionToLocalizedModuleCompletionFamily]
  rw [ringCompletionToLocalizedModuleCompletionFamily]
  change
    AdicCompletion.transitionMap mₚ Sₚ h
        (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n (x.val n)) =
      ringCompletionStageLinearEquivModuleStage (p := p) (S := S) m (x.val m)
  rw [ringCompletionStageLinearEquivModuleStage_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 97 8: lifting the compatible stagewise quotient comparison gives a
canonical map from the `pSₚ`-adic ring completion back to the `mₚ`-adic module completion. -/
private noncomputable def ringCompletion_to_localizedModuleCompletion :
    AdicCompletion pSₚ Sₚ →ₗ[Rₚ] AdicCompletion mₚ Sₚ :=
  AdicCompletion.lift mₚ
    (ringCompletionToLocalizedModuleCompletionFamily (p := p) (S := S))
    (fun {m n} h =>
      ringCompletionToLocalizedModuleCompletionFamily_compatible (p := p) (S := S) h)

/-- Helper for Lemma 10.97.8: the reverse comparison from the ring completion to the module
completion sends the canonical image of `s : Sₚ` to the same completed element. -/
private theorem ringCompletion_to_localizedModuleCompletion_of (s : Sₚ) :
    ringCompletion_to_localizedModuleCompletion (p := p) (S := S) (AdicCompletion.of pSₚ Sₚ s) =
      AdicCompletion.of mₚ Sₚ s := by
  -- Evaluate the lifted map stagewise, where it is defined by the quotient bridge.
  ext n
  rw [ringCompletion_to_localizedModuleCompletion, AdicCompletion.eval_lift_apply]
  simpa [ringCompletionToLocalizedModuleCompletionFamily] using
    (ringCompletionStageLinearEquivModuleStage_mk (p := p) (S := S) n s)

/-- Helper for Lemma 10.97.8: the two completion comparison maps already compose to the identity
on the dense image of `Sₚ` inside the `mₚ`-adic module completion. -/
private theorem localizedCompletionComparison_left_on_of (s : Sₚ) :
    ringCompletion_to_localizedModuleCompletion (p := p) (S := S)
        (localizedModuleCompletion_to_ringCompletion (p := p) (S := S)
          (AdicCompletion.of mₚ Sₚ s)) =
      AdicCompletion.of mₚ Sₚ s := by
  -- First move from the module completion to the ring completion, then immediately come back.
  rw [localizedModuleCompletion_to_ringCompletion_of, ringCompletion_to_localizedModuleCompletion_of]

/-- Helper for Lemma 10.97.8: the two completion comparison maps already compose to the identity
on the dense image of `Sₚ` inside the `pSₚ`-adic ring completion. -/
private theorem localizedCompletionComparison_right_on_of (s : Sₚ) :
    localizedModuleCompletion_to_ringCompletion (p := p) (S := S)
        (ringCompletion_to_localizedModuleCompletion (p := p) (S := S)
          (AdicCompletion.of pSₚ Sₚ s)) =
      AdicCompletion.of pSₚ Sₚ s := by
  -- The reverse comparison fixes `of s`, so the forward comparison does as well.
  rw [ringCompletion_to_localizedModuleCompletion_of, localizedModuleCompletion_to_ringCompletion_of]

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise forward comparison and the lifted
reverse comparison are inverse on the `mₚ`-adic module completion. -/
private theorem moduleCompletionByStages_left_inv :
    Function.LeftInverse
      (ringCompletion_to_localizedModuleCompletion (p := p) (S := S))
      (moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)) := by
  -- After evaluating at stage `n`, the composite is `Eₙ (Eₙ.symm _)`.
  intro x
  ext n
  rw [ringCompletion_to_localizedModuleCompletion]
  change
    ringCompletionToLocalizedModuleCompletionFamily (p := p) (S := S) n
        (moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) x) =
      x.val n
  rw [ringCompletionToLocalizedModuleCompletionFamily,
    moduleCompletionToRingCompletionByStagesFun]
  change
    ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n
        ((ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
          (x.val n)) =
      x.val n
  exact
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).apply_symm_apply
      (x.val n)

/-- Helper for Chap10 Lemma 10 97 8: the lifted reverse comparison and the coordinatewise
forward comparison are inverse on the `pSₚ`-adic ring completion. -/
private theorem moduleCompletionByStages_right_inv :
    Function.RightInverse
      (ringCompletion_to_localizedModuleCompletion (p := p) (S := S))
      (moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)) := by
  -- The other composite has coordinate `Eₙ.symm (Eₙ _)`, hence is also the identity.
  intro y
  ext n
  change
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
        ((ringCompletion_to_localizedModuleCompletion (p := p) (S := S) y).val n) =
      y.val n
  rw [ringCompletion_to_localizedModuleCompletion]
  change
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
        (ringCompletionToLocalizedModuleCompletionFamily (p := p) (S := S) n y) =
      y.val n
  rw [ringCompletionToLocalizedModuleCompletionFamily]
  exact
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm_apply_apply
      (y.val n)

/-- Helper for Chap10 Lemma 10 97 8: the module-completion model and ring-completion model of
`Sₚ` are equivalent by the coordinatewise stage comparison. -/
private noncomputable def moduleCompletion_ringCompletionByStages_equiv :
    AdicCompletion mₚ Sₚ ≃ AdicCompletion pSₚ Sₚ :=
  { toFun := moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
    invFun := ringCompletion_to_localizedModuleCompletion (p := p) (S := S)
    left_inv := moduleCompletionByStages_left_inv (p := p) (S := S)
    right_inv := moduleCompletionByStages_right_inv (p := p) (S := S) }

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise module-to-ring completion comparison is
bijective. -/
private theorem moduleCompletionToRingCompletionByStagesFun_bijective :
    Function.Bijective
      (moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) :
        AdicCompletion mₚ Sₚ → AdicCompletion pSₚ Sₚ) := by
  -- The comparison was packaged as an equivalence, so bijectivity is immediate.
  exact (moduleCompletion_ringCompletionByStages_equiv (p := p) (S := S)).bijective

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise module-to-ring completion comparison
sends zero to zero. -/
private theorem moduleCompletionToRingCompletionByStagesFun_zero :
    moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) (0 : AdicCompletion mₚ Sₚ) =
      0 := by
  -- At every finite stage, the inverse linear equivalence sends zero to zero.
  ext n
  exact (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm.map_zero

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise module-to-ring completion comparison is
additive. -/
private theorem moduleCompletionToRingCompletionByStagesFun_add
    (x y : AdicCompletion mₚ Sₚ) :
    moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) (x + y) =
      moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) x +
        moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) y := by
  -- Additivity is checked coordinatewise through the finite-stage linear equivalences.
  ext n
  simp [moduleCompletionToRingCompletionByStagesFun]

/-- Helper for Chap10 Lemma 10 97 8: the inverse finite-stage comparison sends a scalar quotient
multiple of a representative to the matching representative in the ring-stage quotient. -/
private theorem ringCompletionStageLinearEquivModuleStage_symm_smul_mk
    (n : ℕ) (r : Rₚ) (s : Sₚ) :
    (ringCompletionStageLinearEquivModuleStage (p := p) (S := S) n).symm
        (Submodule.Quotient.mk (r • s : Sₚ)) =
      Submodule.Quotient.mk (algebraMap Rₚ Sₚ r * s) := by
  -- The inverse stage bridge is identity on representatives; scalar multiplication in `Sₚ`
  -- is multiplication by the algebra-map image.
  simpa [Algebra.smul_def] using
    ringCompletionStageLinearEquivModuleStage_symm_mk (p := p) (S := S) n
      (algebraMap Rₚ Sₚ r * s)

/-- Helper for Chap10 Lemma 10 97 8: the staged module-to-ring comparison sends a Cauchy
representative scalar multiple to the expected quotient representative at every finite stage. -/
private theorem moduleCompletionToRingCompletionByStagesFun_smul_mk_val
    (n : ℕ) (r : AdicCauchySequence mₚ Rₚ) (s : Sₚ) :
    (moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        ((AdicCompletion.mk mₚ Rₚ r) • AdicCompletion.of mₚ Sₚ s)).val n =
      Submodule.Quotient.mk (algebraMap Rₚ Sₚ (r.val n) * s) := by
  -- Evaluate the scalar action stagewise, then use the inverse quotient bridge on representatives.
  simpa [AdicCompletion.smul_eval, Algebra.smul_def] using
    ringCompletionStageLinearEquivModuleStage_symm_smul_mk (p := p) (S := S) n
      (r.val n) s

/-- Helper for Chap10 Lemma 10 97 8: evaluating the completed base algebra map on a Cauchy
representative gives the image of the same representative in the localized quotient. -/
private theorem completionBaseAlgHom_mk_eval_a
    (n : ℕ) (r : AdicCauchySequence mₚ Rₚ) :
    AdicCompletion.evalₐ pSₚ n
        ((completionBaseAlgHom (S := S) p) (AdicCompletion.mk mₚ Rₚ r)) =
      Ideal.Quotient.mk (pSₚ ^ n) (algebraMap Rₚ Sₚ (r.val n)) := by
  -- Unfold only the base quotient map; this avoids normalizing the whole tensor comparison.
  simpa [completionBaseQuotientMap, Ideal.Quotient.mkₐ_eq_mk] using
    completionBaseAlgHom_eval_a (p := p) (S := S) n (AdicCompletion.mk mₚ Rₚ r)

/-- Helper for Chap10 Lemma 10 97 8: the ideal stage `pSₚ^n` maps to the corresponding
submodule stage used by the underlying coordinate of `AdicCompletion pSₚ Sₚ`. -/
private theorem stageIdeal_le_smulTop (n : ℕ) :
    pSₚ ^ n ≤ pSₚ ^ n • (⊤ : Submodule Sₚ Sₚ) := by
  -- In the ring-as-module case, multiplying the stage ideal by the top submodule is the same
  -- ideal, so the bridge inclusion is equality.
  simpa using
    (Ideal.smul_top_eq_map (R := Sₚ) (S := Sₚ) (I := pSₚ ^ n)).symm.le

/-- Helper for Chap10 Lemma 10 97 8: factoring an algebraic stage evaluation through the
underlying submodule quotient recovers the raw `val n` coordinate. -/
private theorem evalAlgHom_factor_eq_val
    (n : ℕ) (z : AdicCompletion pSₚ Sₚ) :
    Ideal.Quotient.factor (stageIdeal_le_smulTop (p := p) (S := S) n)
        (AdicCompletion.evalₐ pSₚ n z) =
      z.val n := by
  -- Cross from the algebra quotient coordinate to the underlying completion coordinate using the
  -- canonical adic-completion bridge, then unfold `eval`.
  simpa [AdicCompletion.eval_apply] using
    (AdicCompletion.factor_evalₐ_eq_eval (I := pSₚ) (n := n) z
      (stageIdeal_le_smulTop (p := p) (S := S) n))

/-- Helper for Chap10 Lemma 10 97 8: evaluating the localized tensor/completion map on a Cauchy
pure tensor gives the expected finite-stage algebra quotient representative. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrime_mk_tmul_eval_a
    (n : ℕ) (r : AdicCauchySequence mₚ Rₚ) (s : Sₚ) :
    AdicCompletion.evalₐ pSₚ n
        (((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
          (AdicCompletion.mk mₚ Rₚ r ⊗ₜ[Rₚ] s)) =
      Ideal.Quotient.mk (pSₚ ^ n) (algebraMap Rₚ Sₚ (r.val n) * s) := by
  -- First compute the tensor product map as a product in the completion.
  simp only [localizedTensorProduct_to_completion_localizationAtPrime,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.productMap_apply_tmul,
    AlgHom.restrictScalars_apply, Algebra.ofId_apply]
  -- Then evaluate both factors in the finite quotient and multiply there.
  rw [map_mul, completionBaseAlgHom_mk_eval_a]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

/-- Helper for Chap10 Lemma 10 97 8: the localized tensor/completion map has the same stage
coordinate on Cauchy pure tensors as the staged module-to-ring comparison. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrime_mk_tmul_val
    (n : ℕ) (r : AdicCauchySequence mₚ Rₚ) (s : Sₚ) :
    (((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
        (AdicCompletion.mk mₚ Rₚ r ⊗ₜ[Rₚ] s)).val n =
      Submodule.Quotient.mk (algebraMap Rₚ Sₚ (r.val n) * s) := by
  -- Convert the raw completion coordinate to an algebra quotient coordinate, compute there, and
  -- factor back to the underlying quotient.
  rw [← evalAlgHom_factor_eq_val (p := p) (S := S) n
    (((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
      (AdicCompletion.mk mₚ Rₚ r ⊗ₜ[Rₚ] s))]
  rw [localizedTensorProduct_to_completion_localizationAtPrime_mk_tmul_eval_a]
  rw [Ideal.Quotient.factor_mk]
  rfl

/-- Helper for Chap10 Lemma 10 97 8: the coordinatewise module-to-ring comparison, viewed as an
additive map, records additivity once for tensor-product induction. -/
private noncomputable def moduleCompletionToRingCompletionByStagesAddMonoidHom :
    AdicCompletion mₚ Sₚ →+ AdicCompletion pSₚ Sₚ :=
  { toFun := moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
    map_zero' := moduleCompletionToRingCompletionByStagesFun_zero (p := p) (S := S)
    map_add' := moduleCompletionToRingCompletionByStagesFun_add (p := p) (S := S) }

/-- Helper for Chap10 Lemma 10 97 8: the additive-map wrapper applies as the underlying
coordinatewise module-to-ring comparison. -/
private theorem moduleCompletionToRingCompletionByStagesAddMonoidHom_apply
    (x : AdicCompletion mₚ Sₚ) :
    moduleCompletionToRingCompletionByStagesAddMonoidHom (p := p) (S := S) x =
      moduleCompletionToRingCompletionByStagesFun (p := p) (S := S) x := by
  -- The wrapper was introduced only to cache the additive structure.
  rfl

/-- Helper for Chap10 Lemma 10 97 8: the localized tensor/completion algebra map viewed only as
an additive homomorphism. -/
private noncomputable def localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom :
    Rₚ^ ⊗[Rₚ] Sₚ →+ AdicCompletion pSₚ Sₚ :=
  ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom).toAddMonoidHom

/-- Helper for Chap10 Lemma 10 97 8: the staged comparison after the canonical tensor-to-module
completion map viewed as an additive homomorphism. -/
private noncomputable def moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom :
    Rₚ^ ⊗[Rₚ] Sₚ →+ AdicCompletion pSₚ Sₚ :=
  (moduleCompletionToRingCompletionByStagesAddMonoidHom (p := p) (S := S)).comp
    (AdicCompletion.ofTensorProduct mₚ Sₚ).toAddMonoidHom

/-- Helper for Chap10 Lemma 10 97 8: the additive localized tensor/completion map applies as the
underlying algebra map. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom_apply
    (x : Rₚ^ ⊗[Rₚ] Sₚ) :
    localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom (p := p) x =
      ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom) x := by
  -- The additive wrapper is just the additive part of the algebra map.
  rfl

/-- Helper for Chap10 Lemma 10 97 8: the additive staged tensor comparison applies as the staged
map after `AdicCompletion.ofTensorProduct`. -/
private theorem moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom_apply
    (x : Rₚ^ ⊗[Rₚ] Sₚ) :
    moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom (p := p) (S := S) x =
      moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        (AdicCompletion.ofTensorProduct mₚ Sₚ x) := by
  -- The composed additive wrapper first applies the tensor-to-completion map, then the staged map.
  rfl

/-- Helper for Chap10 Lemma 10 97 8: after applying the canonical tensor-to-module-completion
map to a pure tensor, the coordinatewise module-to-ring completion comparison agrees with the
localized tensor/completion algebra map. -/
private theorem moduleCompletionToRingCompletionByStages_ofTensorProduct_tmul
    (rhat : Rₚ^) (s : Sₚ) :
    moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        (AdicCompletion.ofTensorProduct mₚ Sₚ (rhat ⊗ₜ[Rₚ] s)) =
      ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
        (rhat ⊗ₜ[Rₚ] s) := by
  let P : Rₚ^ → Prop := fun y ↦
    moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        (AdicCompletion.ofTensorProduct mₚ Sₚ (y ⊗ₜ[Rₚ] s)) =
      ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
        (y ⊗ₜ[Rₚ] s)
  -- Reduce the completed scalar to a Cauchy representative; on dense elements both sides are
  -- the canonical completed product in `Sₚ`.
  change P rhat
  refine AdicCompletion.induction_on (I := mₚ) (M := Rₚ) rhat ?_
  intro r
  dsimp [P]
  rw [AdicCompletion.ofTensorProduct_tmul]
  -- Evaluate at every finite stage. Both sides reduce to the same quotient representative
  -- `algebraMap Rₚ Sₚ (r.val n) * s`.
  ext n
  rw [moduleCompletionToRingCompletionByStagesFun_smul_mk_val]
  exact (localizedTensorProduct_to_completion_localizationAtPrime_mk_tmul_val
    (p := p) (S := S) n r s).symm

/-- Helper for Chap10 Lemma 10 97 8: the two cached additive homomorphisms from the localized
tensor product agree. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom_eq :
    localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom (p := p) =
      moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom (p := p) (S := S) := by
  -- Additive-hom equality is proved by tensor induction. The pure tensor case is the completed
  -- coordinate comparison; the additive branch uses only the cached `map_add` fields.
  apply AddMonoidHom.ext
  intro x
  let F := localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom (p := p) (S := S)
  let G := moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom (p := p) (S := S)
  change F x = G x
  refine TensorProduct.induction_on x ?zero ?tmul ?add
  · rw [F.map_zero, G.map_zero]
  · intro rhat s
    change
      ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom)
          (rhat ⊗ₜ[Rₚ] s) =
        moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
          (AdicCompletion.ofTensorProduct mₚ Sₚ (rhat ⊗ₜ[Rₚ] s))
    exact (moduleCompletionToRingCompletionByStages_ofTensorProduct_tmul
      (p := p) (S := S) rhat s).symm
  · intro x y hx hy
    rw [F.map_add, G.map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 97 8: the localized tensor/completion algebra map is the staged
module-completion comparison after `AdicCompletion.ofTensorProduct`. -/
private theorem localizedTensorProduct_to_completion_localizationAtPrime_eq_byStages_comp_ofTensorProduct
    (x : Rₚ^ ⊗[Rₚ] Sₚ) :
    ((localizedTensorProduct_to_completion_localizationAtPrime p).toRingHom) x =
      moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
        (AdicCompletion.ofTensorProduct mₚ Sₚ x) := by
  -- Read the pointwise statement off the equality of cached additive homomorphisms.
  have happ :=
    congrArg
      (fun f : Rₚ^ ⊗[Rₚ] Sₚ →+ AdicCompletion pSₚ Sₚ ↦ f x)
      (localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom_eq
        (p := p) (S := S))
  simpa [localizedTensorProduct_to_completion_localizationAtPrimeAddMonoidHom_apply,
    moduleCompletionToRingCompletionByStagesOfTensorProductAddMonoidHom_apply] using happ

private theorem localizedTensorProduct_to_completion_localizationAtPrime_bijective :
    Function.Bijective
      ((localizedTensorProduct_to_completion_localizationAtPrime p :
        Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ) :
        Rₚ^ ⊗[Rₚ] Sₚ → AdicCompletion pSₚ Sₚ) := by
  -- Route correction: the reverse completion map is now packaged as
  -- `ringCompletion_to_localizedModuleCompletion`, and the coordinatewise forward map
  -- `moduleCompletionToRingCompletionByStagesFun` is now globally bijective. The remaining
  -- adapter is to identify this staged forward map after `AdicCompletion.ofTensorProduct mₚ Sₚ`
  -- with the algebra map `localizedTensorProduct_to_completion_localizationAtPrime`.
  have hof :
      Function.Bijective (AdicCompletion.ofTensorProduct mₚ Sₚ :
        Rₚ^ ⊗[Rₚ] Sₚ → AdicCompletion mₚ Sₚ) := by
    letI : IsNoetherianRing Rₚ :=
      IsLocalization.isNoetherianRing p.asIdeal.primeCompl Rₚ inferInstance
    letI : Module.Finite Rₚ Sₚ :=
      Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
    exact AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian mₚ Sₚ
  have hcomp :
      Function.Bijective
        (fun x : Rₚ^ ⊗[Rₚ] Sₚ ↦
          moduleCompletionToRingCompletionByStagesFun (p := p) (S := S)
            (AdicCompletion.ofTensorProduct mₚ Sₚ x)) :=
    Function.Bijective.comp
      (moduleCompletionToRingCompletionByStagesFun_bijective (p := p) (S := S)) hof
  -- Transfer bijectivity across the pointwise equality between the two comparison maps.
  constructor
  · intro x y hxy
    apply hcomp.1
    exact
      (localizedTensorProduct_to_completion_localizationAtPrime_eq_byStages_comp_ofTensorProduct
        (p := p) (S := S) x).symm.trans <|
        hxy.trans
          (localizedTensorProduct_to_completion_localizationAtPrime_eq_byStages_comp_ofTensorProduct
            (p := p) (S := S) y)
  · intro z
    rcases hcomp.2 z with ⟨x, hx⟩
    exact
      ⟨x,
        (localizedTensorProduct_to_completion_localizationAtPrime_eq_byStages_comp_ofTensorProduct
          (p := p) (S := S) x).trans hx⟩

noncomputable def localizedTensorProduct_algEquiv_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ ≃ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  AlgEquiv.ofBijective (localizedTensorProduct_to_completion_localizationAtPrime p)
    (localizedTensorProduct_to_completion_localizationAtPrime_bijective p)

/-- Lemma 10.97.8, first equality: the textbook tensor term `Rₚ^ ⊗[R] S` canonically identifies,
as a ring, with the completion of the semilocal localization `Sₚ`. This is the source-facing
first comparison `Rₚ^ ⊗[R] S = (Sₚ)^∧`, before passing to the product decomposition. -/
@[stacks 07N9]
noncomputable def completion_tensorProductOverBase_ringEquiv_completion_localizationAtPrime :
    Rₚ^ ⊗[R] S ≃+* AdicCompletion pSₚ Sₚ :=
  ((completion_tensorProductOverBase_algEquiv_localizedTensorProduct p).toRingEquiv).trans
    (localizedTensorProduct_algEquiv_completion_localizationAtPrime p).toRingEquiv

end

-- The factor map from the semilocal localization `Sₚ` to the local ring at a prime `q` over `p`.
private lemma localizedFactorSubmonoid_le_primeCompl (q : p.asIdeal.primesOver S) :
    Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl ≤
      Submonoid.comap (RingHom.id S) q.1.primeCompl := by
  intro y hy
  have hy' : y ∈ Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl := hy
  rw [Submonoid.mem_comap]
  have hy'' : ∃ x ∉ p.asIdeal, algebraMap R S x = y := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hy'
  rcases hy'' with ⟨x, hx, rfl⟩
  have hxq : algebraMap R S x ∉ q.1 := by
    intro hmem
    have hqover : p.asIdeal = Ideal.comap (algebraMap R S) q.1 := Ideal.LiesOver.over
    have hxmem : x ∈ p.asIdeal := by
      simpa [hqover, Ideal.mem_comap] using hmem
    exact hx hxmem
  exact show (RingHom.id S) (algebraMap R S x) ∈ q.1.primeCompl by
    simpa using hxq

private noncomputable def localizedFactorRingHom (q : p.asIdeal.primesOver S) :
    Sₚ →+* Localization.AtPrime q.1 :=
  IsLocalization.map (Localization.AtPrime q.1) (RingHom.id S)
    (localizedFactorSubmonoid_le_primeCompl p q)

private lemma localizedFactorRingHom_comp (q : p.asIdeal.primesOver S) :
    (localizedFactorRingHom p q).comp (algebraMap Rₚ Sₚ) =
      Localization.localRingHom p.asIdeal q.1 (algebraMap R S) Ideal.LiesOver.over := by
  have hsub :
      p.asIdeal.primeCompl ≤
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl).comap (algebraMap R S) := by
    simpa [Algebra.algebraMapSubmonoid] using
      (Submonoid.le_comap_map p.asIdeal.primeCompl :
        p.asIdeal.primeCompl ≤
          (Submonoid.map (algebraMap R S) p.asIdeal.primeCompl).comap (algebraMap R S))
  have hmap :
      algebraMap Rₚ Sₚ =
        IsLocalization.map Sₚ (algebraMap R S) hsub := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [hmap]
  symm
  apply Localization.localRingHom_unique p.asIdeal q.1 (algebraMap R S) Ideal.LiesOver.over
  intro y
  have hcomp :
      (localizedFactorRingHom p q).comp (algebraMap S Sₚ) =
        (algebraMap S (Localization.AtPrime q.1)).comp (RingHom.id S) := by
    ext y
    simp [localizedFactorRingHom]
  have h :=
    congrArg (fun g : S →+* Localization.AtPrime q.1 ↦ g ((algebraMap R S) y))
      hcomp
  convert h using 1
  · simp [localizedFactorRingHom, RingHom.comp_apply]

private noncomputable def localizedFactorAlgHom (q : p.asIdeal.primesOver S) :
    Sₚ →ₐ[Rₚ] Localization.AtPrime q.1 :=
  { toRingHom := localizedFactorRingHom p q
    commutes' := by
      intro x
      simpa [RingHom.algebraMap_toAlgebra] using
        congrArg (fun g : Rₚ →+* Localization.AtPrime q.1 ↦ g x)
          (localizedFactorRingHom_comp p q) }

/-- Helper for Chap10 Lemma 10 97 8: the algebra-valued localized factor has the expected
underlying ring homomorphism. -/
private theorem localizedFactorAlgHom_toRingHom (q : p.asIdeal.primesOver S) :
    (localizedFactorAlgHom p q).toRingHom = localizedFactorRingHom p q := by
  -- This keeps later quotient-map comparisons in the stable `AlgHom` spelling while allowing
  -- direct access to the underlying localization map.
  rfl

private lemma localizedFactorAlgHom_map_pSₚ_le (q : p.asIdeal.primesOver S) :
    Ideal.map (localizedFactorAlgHom p q).toRingHom pSₚ ≤ maximalIdeal (Localization.AtPrime q.1) := by
  have hcomp :
      (localizedFactorAlgHom p q).toRingHom.comp (algebraMap Rₚ Sₚ) =
        Localization.localRingHom p.asIdeal q.1 (algebraMap R S)
          Ideal.LiesOver.over :=
    localizedFactorRingHom_comp p q
  rw [show pSₚ = Ideal.map (algebraMap Rₚ Sₚ) mₚ by rfl, Ideal.map_map]
  rw [hcomp]
  simpa using IsLocalRing.map_maximalIdeal_le
    (Localization.localRingHom p.asIdeal q.1 (algebraMap R S)
      Ideal.LiesOver.over)

/-- Helper for Chap10 Lemma 10 97 8: the ideal on the local factor induced by the semilocal
stage ideal `pSₚ`. This is the corrected finite-stage normal form for the product decomposition.
-/
private noncomputable def localizedFactorIdeal (q : p.asIdeal.primesOver S) :
    Ideal (Localization.AtPrime q.1) :=
  Ideal.map (localizedFactorAlgHom p q).toRingHom pSₚ

/-- Helper for Chap10 Lemma 10 97 8: the localized factor ideal is the image of the maximal
ideal of `Rₚ` under the canonical algebra map to the local factor. -/
private theorem localizedFactorIdeal_eq_map_maximalIdeal (q : p.asIdeal.primesOver S) :
    localizedFactorIdeal p q =
      Ideal.map (algebraMap Rₚ (Localization.AtPrime q.1)) mₚ := by
  -- Rewrite `pSₚ` as the image of `mₚ`, then use the `Rₚ`-linearity of the local factor map.
  have hcomp :
      (localizedFactorAlgHom p q).toRingHom.comp (algebraMap Rₚ Sₚ) =
        algebraMap Rₚ (Localization.AtPrime q.1) := by
    ext x
    exact (localizedFactorAlgHom p q).commutes x
  calc
    localizedFactorIdeal p q =
        Ideal.map ((localizedFactorAlgHom p q).toRingHom.comp (algebraMap Rₚ Sₚ)) mₚ := by
          simp [localizedFactorIdeal, Ideal.map_map]
    _ = Ideal.map (algebraMap Rₚ (Localization.AtPrime q.1)) mₚ := by
          rw [hcomp]

/-- Helper for Chap10 Lemma 10 97 8: the localized image of `pSₚ` lies in the maximal ideal of
the local factor. -/
private theorem localizedFactorIdeal_le_maximal (q : p.asIdeal.primesOver S) :
    localizedFactorIdeal p q ≤ maximalIdeal (Localization.AtPrime q.1) := by
  -- This is the same containment as the existing map-to-maximal lemma, repackaged under the
  -- `J_q` name used for the corrected finite-stage route.
  exact localizedFactorAlgHom_map_pSₚ_le p q

/-- Helper for Chap10 Lemma 10 97 8: powers of the semilocal stage ideal map into the
corresponding powers of the localized factor ideal. -/
private theorem localizedFactorIdealPow_le_comap (q : p.asIdeal.primesOver S) (n : ℕ) :
    pSₚ ^ n ≤ Ideal.comap (localizedFactorAlgHom p q).toRingHom
      (localizedFactorIdeal p q ^ n) := by
  -- Map the source-stage power into the target and rewrite the mapped power as `J_q ^ n`.
  exact
    (Ideal.map_le_iff_le_comap).mp <| by
      simpa [localizedFactorIdeal, Ideal.map_pow]

/-- Helper for Chap10 Lemma 10 97 8: powers of the localized factor ideal are exactly the images
of the corresponding powers of the semilocal stage ideal. -/
private theorem localizedFactorIdeal_pow_eq_map_pow (q : p.asIdeal.primesOver S) (n : ℕ) :
    localizedFactorIdeal p q ^ n =
      Ideal.map (localizedFactorAlgHom p q).toRingHom (pSₚ ^ n) := by
  -- This is the directed rewrite from the `J_q` normal form to the quotient-localization normal
  -- form expected by mathlib's quotient localization instance.
  simp [localizedFactorIdeal, Ideal.map_pow]

/-- Helper for Chap10 Lemma 10 97 8: powers of the localized factor ideal lie in the matching
powers of the local maximal ideal. -/
private theorem localizedFactorIdeal_pow_le_maximal_pow (q : p.asIdeal.primesOver S) (n : ℕ) :
    localizedFactorIdeal p q ^ n ≤ maximalIdeal (Localization.AtPrime q.1) ^ n := by
  -- The containment `J_q ≤ maximalIdeal` propagates to every power.
  exact Ideal.pow_right_mono (localizedFactorIdeal_le_maximal p q) n

private lemma localizedFactorPow_le_comap (q : p.asIdeal.primesOver S) (n : ℕ) :
    pSₚ ^ n ≤ Ideal.comap (localizedFactorAlgHom p q).toRingHom
      (maximalIdeal (Localization.AtPrime q.1) ^ n) := by
  exact
    (Ideal.map_le_iff_le_comap).mp <| by
      simpa [Ideal.map_pow] using
        Ideal.pow_right_mono (localizedFactorAlgHom_map_pSₚ_le p q) n

/-- Helper for Chap10 Lemma 10 97 8: the stage-`n` quotient map from the completed semilocal
localization to the `J_q`-adic quotient of the local factor. -/
private noncomputable def completionFactorPadicQuotientMap
    (q : p.asIdeal.primesOver S) (n : ℕ) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n :=
  (Ideal.quotientMapₐ _ (localizedFactorAlgHom p q)
    (localizedFactorIdealPow_le_comap p q n)).comp
    ((AdicCompletion.evalₐ pSₚ n).restrictScalars Rₚ)

/-- Helper for Chap10 Lemma 10 97 8: the `J_q`-adic stage quotient maps commute with transition
maps. -/
private theorem completionFactorPadicQuotientMap_compatible
    (q : p.asIdeal.primesOver S) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
        (completionFactorPadicQuotientMap p q n) =
      completionFactorPadicQuotientMap p q m := by
  ext x
  let P : AdicCompletion pSₚ Sₚ → Prop := fun y ↦
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
        (completionFactorPadicQuotientMap p q n) y =
      completionFactorPadicQuotientMap p q m y
  -- Check compatibility on dense representatives, where both sides are the same residue class in
  -- the `J_q ^ m` quotient.
  change P x
  refine AdicCompletion.induction_on (I := pSₚ) (M := Sₚ) x ?_
  intro s
  dsimp [P]
  simpa [completionFactorPadicQuotientMap, AdicCompletion.evalₐ_mk,
    Ideal.Quotient.factorₐ_comp] using
    congrArg
      (Ideal.quotientMapₐ (localizedFactorIdeal p q ^ m)
        (localizedFactorAlgHom p q) (localizedFactorIdealPow_le_comap p q m))
      (AdicCompletion.Ideal.mk_eq_mk (I := pSₚ) (m := m) (n := n) h s)

/-- Helper for Chap10 Lemma 10 97 8: the `J_q`-adic completion coordinate map induced by the
canonical local factor map `Sₚ → S_q`. -/
private noncomputable def completionFactorPadicAlgHom (q : p.asIdeal.primesOver S) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1) :=
  AdicCompletion.liftAlgHom (localizedFactorIdeal p q)
    (completionFactorPadicQuotientMap p q)
    (completionFactorPadicQuotientMap_compatible p q)

/-- Helper for Chap10 Lemma 10 97 8: evaluating the `J_q`-adic coordinate map gives its defining
finite-stage quotient map. -/
private theorem completionFactorPadicAlgHom_eval_a
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    AdicCompletion.evalₐ (localizedFactorIdeal p q) n
        (completionFactorPadicAlgHom p q x) =
      completionFactorPadicQuotientMap p q n x := by
  -- This is the quotientwise evaluation formula for the lifted `J_q`-adic coordinate map.
  simpa [completionFactorPadicAlgHom] using
    (AdicCompletion.evalₐ_liftAlgHom
      (localizedFactorIdeal p q)
      (completionFactorPadicQuotientMap p q)
      (completionFactorPadicQuotientMap_compatible p q) n x)

/-- Helper for Lemma 10.97.8: the stage-`n` quotient map from the completed semilocal
localization to the `q`-factor quotient is induced by the canonical map `Sₚ → S_q`. -/
private noncomputable def completionFactorQuotientMap (q : p.asIdeal.primesOver S) (n : ℕ) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      Localization.AtPrime q.1 ⧸ maximalIdeal (Localization.AtPrime q.1) ^ n :=
  (Ideal.quotientMapₐ _ (localizedFactorAlgHom p q)
    (localizedFactorPow_le_comap p q n)).comp
    ((AdicCompletion.evalₐ pSₚ n).restrictScalars Rₚ)

/-- Helper for Chap10 Lemma 10 97 8: the existing maximal-ideal stage coordinate is obtained
from the `J_q`-adic stage coordinate by quotienting `J_q ^ n ≤ maximalIdeal ^ n`. -/
private theorem completionFactorQuotientMap_eq_factor_padic
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    completionFactorQuotientMap p q n x =
      (Ideal.Quotient.factorₐ Rₚ
        (localizedFactorIdeal_pow_le_maximal_pow p q n))
        (completionFactorPadicQuotientMap p q n x) := by
  let P : AdicCompletion pSₚ Sₚ → Prop := fun y ↦
    completionFactorQuotientMap p q n y =
      (Ideal.Quotient.factorₐ Rₚ
        (localizedFactorIdeal_pow_le_maximal_pow p q n))
        (completionFactorPadicQuotientMap p q n y)
  -- Reduce to a dense semilocal representative, where both constructions are the same local
  -- residue class followed by the quotient map `J_q ^ n → maximalIdeal ^ n`.
  change P x
  refine AdicCompletion.induction_on (I := pSₚ) (M := Sₚ) x ?_
  intro s
  dsimp [P]
  simp [completionFactorQuotientMap, completionFactorPadicQuotientMap,
    AdicCompletion.evalₐ_mk]

/-- Helper for Lemma 10.97.8: the stage quotient maps to a fixed local factor commute with the
transition maps of the inverse system. -/
private theorem completionFactorQuotientMap_compatible
    (q : p.asIdeal.primesOver S) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
        (completionFactorQuotientMap p q n) =
      completionFactorQuotientMap p q m := by
  ext x
  let P : AdicCompletion pSₚ Sₚ → Prop := fun y ↦
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
        (completionFactorQuotientMap p q n) y =
      completionFactorQuotientMap p q m y
  -- Compare both factor maps on a concrete representative of the semilocal completion.
  change P x
  refine AdicCompletion.induction_on (I := pSₚ) (M := Sₚ) x ?_
  intro s
  -- On representatives, both sides are the same stage-`m` residue class in the local factor.
  dsimp [P]
  simpa [completionFactorQuotientMap, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp] using
    congrArg
      (Ideal.quotientMapₐ (maximalIdeal (Localization.AtPrime q.1) ^ m)
        (localizedFactorAlgHom p q) (localizedFactorPow_le_comap p q m))
      (AdicCompletion.Ideal.mk_eq_mk (I := pSₚ) (m := m) (n := n) h s)

private noncomputable def completionFactorAlgHom (q : p.asIdeal.primesOver S) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  AdicCompletion.liftAlgHom (maximalIdeal (Localization.AtPrime q.1))
    (completionFactorQuotientMap p q)
    (completionFactorQuotientMap_compatible p q)

/-- Helper for Lemma 10.97.8: evaluating the `q`-factor completion map at stage `n` recovers the
defining quotient map from the completed semilocal localization. -/
private theorem completionFactorAlgHom_eval_a
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q.1)) n
        (completionFactorAlgHom p q x) =
      completionFactorQuotientMap p q n x := by
  -- This is the owner evaluation formula for `liftAlgHom`.
  simpa [completionFactorAlgHom] using
    (AdicCompletion.evalₐ_liftAlgHom
      (maximalIdeal (Localization.AtPrime q.1))
      (completionFactorQuotientMap p q)
      (completionFactorQuotientMap_compatible p q) n x)

variable (S) in
/-- The canonical comparison map from the completion of the semilocal localization `Sₚ` to the
product of the completed local rings indexed by the owner set `p.asIdeal.primesOver S`. -/
noncomputable def completion_localizationAtPrime_toPiLocalRingCompletion :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  Pi.algHom Rₚ
    (fun q : p.asIdeal.primesOver S ↦
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1))
    (fun q ↦ completionFactorAlgHom p q)

section

variable [IsNoetherianRing R] [Module.Finite R S]

variable (S) in
/-- Helper for Lemma 10.97.8: the maximal ideals of the semilocal localization `Sₚ` are exactly
the primes of `S` lying over `p`. This fixes the source owner set once and for all before passing
to the Artinian quotient stages. -/
private noncomputable def semilocal_maximalSpectrum_equiv_primesOver :
    MaximalSpectrum Sₚ ≃ p.asIdeal.primesOver S where
  toFun M := by
    letI : Module.Finite Rₚ Sₚ := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
    letI : Algebra.IsIntegral Rₚ Sₚ := Algebra.IsIntegral.of_finite (R := Rₚ) (B := Sₚ)
    have hM_comap_maximal : (Ideal.comap (algebraMap Rₚ Sₚ) M.asIdeal).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (R := Rₚ) (S := Sₚ) M.asIdeal
    have hM_comap_eq :
        maximalIdeal Rₚ = Ideal.comap (algebraMap Rₚ Sₚ) M.asIdeal :=
      (IsLocalRing.eq_maximalIdeal hM_comap_maximal).symm
    letI : M.asIdeal.LiesOver (maximalIdeal Rₚ) := ⟨hM_comap_eq⟩
    letI : (Ideal.comap (algebraMap S Sₚ) M.asIdeal).IsPrime := Ideal.IsPrime.under S M.asIdeal
    letI : (Ideal.comap (algebraMap S Sₚ) M.asIdeal).LiesOver p.asIdeal :=
      ⟨by
        -- Push the localization maximal ideal back to `R`, then use the scalar-tower comap formula.
        calc
          p.asIdeal = Ideal.comap (algebraMap R Rₚ) (maximalIdeal Rₚ) := by
            simpa using (IsLocalization.AtPrime.comap_maximalIdeal Rₚ p.asIdeal).symm
          _ =
              Ideal.comap (algebraMap R Rₚ)
                (Ideal.comap (algebraMap Rₚ Sₚ) M.asIdeal) := by rw [hM_comap_eq]
          _ = Ideal.comap (algebraMap R Sₚ) M.asIdeal := by
            rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq R Rₚ Sₚ]
          _ =
              Ideal.comap (algebraMap R S) (Ideal.comap (algebraMap S Sₚ) M.asIdeal) := by
            rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq R S Sₚ]⟩
    -- Pull the maximal ideal of `Sₚ` back along the localization map `S → Sₚ`.
    refine ⟨Ideal.comap (algebraMap S Sₚ) M.asIdeal, ?_⟩
    exact ⟨inferInstance, inferInstance⟩
  invFun q := by
    letI : Module.Finite Rₚ Sₚ := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
    letI : Algebra.IsIntegral Rₚ Sₚ := Algebra.IsIntegral.of_finite (R := Rₚ) (B := Sₚ)
    let Q : Ideal Sₚ := Ideal.map (algebraMap S Sₚ) q.1
    have hq_disjoint :
        Disjoint ((Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) : Set S) (q.1 : Set S) :=
      Ideal.disjoint_primeCompl_of_liesOver q.1 p.asIdeal
    have hQ_prime : Q.IsPrime := by
      -- The prime `q` stays prime after localizing away from `p`.
      simpa [Q] using
        (IsLocalization.isPrime_of_isPrime_disjoint
          (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Sₚ q.1 q.2.1 hq_disjoint)
    have hq_over : Ideal.comap (algebraMap R S) q.1 = p.asIdeal := by
      simpa [Ideal.under_def] using (Ideal.over_def q.1 p.asIdeal).symm
    letI : Q.IsPrime := hQ_prime
    have hQ_comap_eq :
        Ideal.comap (algebraMap Rₚ Sₚ) Q =
          Ideal.map (algebraMap R Rₚ) (Ideal.comap (algebraMap R S) q.1) := by
      -- The source owner `q` lies over `p`, so extension to `Rₚ` commutes with localization.
      simpa [Q, Ideal.under_def] using
        (Ideal.under_map_eq_map_under
          (A := R) (B := S) (C := Rₚ) (D := Sₚ) (P := q.1)
          (by
            rw [Ideal.under_def, hq_over, IsLocalization.AtPrime.map_eq_maximalIdeal]
            exact maximalIdeal.isMaximal Rₚ)
          (by simpa [Q] using hQ_prime.ne_top))
    have hQ_comap_maximal : IsMaximal (Ideal.comap (algebraMap Rₚ Sₚ) Q) := by
      -- Route correction: use the fixed owner set in `Sₚ`; maximality comes from integrality over
      -- the local ring `Rₚ`, not from rebuilding a quotient-stage owner equivalence.
      rw [hQ_comap_eq, hq_over, IsLocalization.AtPrime.map_eq_maximalIdeal]
      exact maximalIdeal.isMaximal Rₚ
    have hQ_maximal : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (R := Rₚ) (S := Sₚ) Q hQ_comap_maximal
    -- Push the prime-over-`p` ideal forward to the corresponding maximal ideal of `Sₚ`.
    exact ⟨Q, hQ_maximal⟩
  left_inv M := by
    -- Mapping a maximal ideal of the localization back to `S` and forward again recovers it.
    exact MaximalSpectrum.ext <|
      IsLocalization.map_comap (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Sₚ M.asIdeal
  right_inv q := by
    have hq_disjoint :
        Disjoint ((Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) : Set S) (q.1 : Set S) :=
      Ideal.disjoint_primeCompl_of_liesOver q.1 p.asIdeal
    -- A prime over `p` is disjoint from the localization submonoid, so comap/map returns it.
    exact SetCoe.ext <|
      IsLocalization.comap_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Sₚ q.2.1 hq_disjoint

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the semilocal maximal ideal associated to a prime over `p`
contracts along `S → Sₚ` to that prime. -/
private theorem semilocalOwner_comap_eq_primesOver
    (q : p.asIdeal.primesOver S) :
    Ideal.comap (algebraMap S Sₚ)
        ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q).asIdeal =
      q.1 := by
  -- This is exactly the right inverse property of the owner equivalence, read on ideal carriers.
  exact congrArg Subtype.val
    ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).right_inv q)

private noncomputable instance primesOverFintype :
    Fintype (p.asIdeal.primesOver S) :=
  Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p.asIdeal)

/-- Helper for Lemma 10.97.8: each positive quotient of the local ring `Rₚ` by a power of its
maximal ideal is Artinian. This is the source proof's base stage before passing to the finite
`Rₚ`-algebra `Sₚ`. -/
private theorem local_power_quotient_isArtinian (n : ℕ) :
    IsArtinianRing (Rₚ ⧸ mₚ ^ (n + 1)) := by
  letI : IsNoetherianRing Rₚ :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl Rₚ inferInstance
  let Q : Type u := Rₚ ⧸ mₚ ^ (n + 1)
  letI : CommRing Q := by infer_instance
  have hm_pow_ne_top : mₚ ^ (n + 1) ≠ (⊤ : Ideal Rₚ) := by
    intro htop
    rcases Ideal.pow_eq_top_iff.mp htop with hm_top | hn
    · exact (maximalIdeal.isMaximal Rₚ).ne_top hm_top
    · exact Nat.succ_ne_zero n hn
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hm_pow_ne_top
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (mₚ ^ (n + 1))) Ideal.Quotient.mk_surjective
  have hmap :
      Ideal.map (Ideal.Quotient.mk (mₚ ^ (n + 1))) mₚ = maximalIdeal Q := by
    -- The quotient of a local ring is still local, with maximal ideal the image of `mₚ`.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (mₚ ^ (n + 1)))
      Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (maximalIdeal Q) := by
    -- The image of `mₚ` in the quotient is nilpotent because `(mₚ ^ (n + 1))` is killed there.
    refine ⟨n + 1, ?_⟩
    rw [← hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal Q).mpr hnil

/-- Helper for Lemma 10.97.8: each positive quotient `Sₚ ⧸ pSₚ^(n + 1)` is Artinian. This is the
stagewise Artinian input needed for the source-faithful product decomposition of the completion. -/
private theorem stageQuotient_isArtinian (n : ℕ) :
    IsArtinianRing (Sₚ ⧸ pSₚ ^ (n + 1)) := by
  let I : Ideal Rₚ := (pSₚ ^ (n + 1)).under Rₚ
  have hm_pow_le : mₚ ^ (n + 1) ≤ I := by
    -- The stage quotient kills at least the `(n + 1)`-st power of the base maximal ideal.
    change mₚ ^ (n + 1) ≤ Ideal.comap (algebraMap Rₚ Sₚ) (pSₚ ^ (n + 1))
    simpa [Ideal.under_def, Ideal.map_pow] using
      (Ideal.le_comap_map : mₚ ^ (n + 1) ≤
        Ideal.comap (algebraMap Rₚ Sₚ) (Ideal.map (algebraMap Rₚ Sₚ) (mₚ ^ (n + 1))))
  letI : IsArtinianRing (Rₚ ⧸ I) := by
    letI : IsArtinianRing (Rₚ ⧸ mₚ ^ (n + 1)) := local_power_quotient_isArtinian p n
    -- Surjective quotient maps preserve Artinianness on the base stage.
    exact
      Function.Surjective.isArtinianRing
        (f := Ideal.Quotient.factor hm_pow_le)
        (Ideal.Quotient.factor_surjective hm_pow_le)
  letI : Module.Finite Rₚ Sₚ := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
  letI : (pSₚ ^ (n + 1)).LiesOver I := by
    change (pSₚ ^ (n + 1)).LiesOver ((pSₚ ^ (n + 1)).under Rₚ)
    infer_instance
  letI : Algebra (Rₚ ⧸ I) (Sₚ ⧸ pSₚ ^ (n + 1)) :=
    Ideal.Quotient.algebraQuotientOfLEComap (show
      I ≤ Ideal.comap (algebraMap Rₚ Sₚ) (pSₚ ^ (n + 1)) by
        rfl)
  letI : Module (Rₚ ⧸ I) (Sₚ ⧸ pSₚ ^ (n + 1)) := Algebra.toModule
  letI : Module.Finite Rₚ (Sₚ ⧸ pSₚ ^ (n + 1)) := inferInstance
  letI : Module.Finite (Rₚ ⧸ I) (Sₚ ⧸ pSₚ ^ (n + 1)) :=
    Module.Finite.of_restrictScalars_finite Rₚ (Rₚ ⧸ I) (Sₚ ⧸ pSₚ ^ (n + 1))
  -- The finite quotient of `Sₚ` over the Artinian base quotient is again Artinian.
  exact IsArtinianRing.of_finite (R := Rₚ ⧸ I) (S := Sₚ ⧸ pSₚ ^ (n + 1))

/-- Helper for Lemma 10.97.8: every maximal ideal of the semilocal localization contains the
positive stage ideal `pSₚ^(n + 1)`. This is the source proof's fixed-owner input for passing from
`Sₚ` to its Artinian quotient stages. -/
private theorem stage_ideal_le_maximal (n : ℕ) (M : MaximalSpectrum Sₚ) :
    pSₚ ^ (n + 1) ≤ M.asIdeal := by
  letI : Module.Finite Rₚ Sₚ := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
  letI : Algebra.IsIntegral Rₚ Sₚ := Algebra.IsIntegral.of_finite (R := Rₚ) (B := Sₚ)
  have hM_comap_maximal : (Ideal.comap (algebraMap Rₚ Sₚ) M.asIdeal).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (R := Rₚ) (S := Sₚ) M.asIdeal
  have hM_comap_eq :
      maximalIdeal Rₚ = Ideal.comap (algebraMap Rₚ Sₚ) M.asIdeal :=
    (IsLocalRing.eq_maximalIdeal hM_comap_maximal).symm
  have hpSₚ_le : pSₚ ≤ M.asIdeal := by
    -- First show that the base maximal ideal maps into every maximal ideal of `Sₚ`.
    rw [show pSₚ = Ideal.map (algebraMap Rₚ Sₚ) mₚ by rfl]
    exact Ideal.map_le_iff_le_comap.mpr <| by
      simpa [hM_comap_eq]
  -- Then pass to powers and use that every positive power of a maximal ideal lies inside it.
  exact (Ideal.pow_right_mono hpSₚ_le (n + 1)).trans (Ideal.pow_le_self (Nat.succ_ne_zero n))

variable (S) in
/-- Helper for Lemma 10.97.8: the maximal spectrum of each positive stage quotient
`Sₚ ⧸ pSₚ^(n + 1)` is canonically the same owner set as the maximal spectrum of `Sₚ`. This is the
fixed-owner step in the source proof before applying the Artinian product decomposition. -/
private noncomputable def stage_maximalSpectrum_equiv_semilocal (n : ℕ) :
    MaximalSpectrum (Sₚ ⧸ pSₚ ^ (n + 1)) ≃ MaximalSpectrum Sₚ where
  toFun N := by
    -- Pull a maximal ideal of the stage quotient back along the quotient map.
    refine
      ⟨Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1))) N.asIdeal, ?_⟩
    exact
      Ideal.comap_isMaximal_of_surjective
        (f := Ideal.Quotient.mk (pSₚ ^ (n + 1))) Ideal.Quotient.mk_surjective (K := N.asIdeal)
  invFun M := by
    -- Push a maximal ideal of `Sₚ` down to the quotient; the stage ideal lies inside `M`.
    refine
      ⟨Ideal.map (Ideal.Quotient.mk (pSₚ ^ (n + 1))) M.asIdeal, ?_⟩
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (pSₚ ^ (n + 1))) Ideal.Quotient.mk_surjective <| by
        simpa [Ideal.mk_ker] using stage_ideal_le_maximal (p := p) (S := S) n M
  left_inv N := by
    -- Mapping down and then pulling back along a surjective quotient map fixes the stage ideal.
    apply MaximalSpectrum.ext
    simpa using
      (Ideal.map_comap_of_surjective
        (Ideal.Quotient.mk (pSₚ ^ (n + 1))) Ideal.Quotient.mk_surjective N.asIdeal)
  right_inv M := by
    -- Pulling back the pushed-forward ideal adds the kernel, which is already inside `M`.
    apply MaximalSpectrum.ext
    calc
      Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1)))
          (Ideal.map (Ideal.Quotient.mk (pSₚ ^ (n + 1))) M.asIdeal) =
          M.asIdeal ⊔ RingHom.ker (Ideal.Quotient.mk (pSₚ ^ (n + 1))) := by
            rw [Ideal.comap_map_of_surjective
              (Ideal.Quotient.mk (pSₚ ^ (n + 1))) Ideal.Quotient.mk_surjective,
              RingHom.ker_eq_comap_bot]
      _ = M.asIdeal ⊔ pSₚ ^ (n + 1) := by rw [Ideal.mk_ker]
      _ = M.asIdeal := by
            rw [sup_eq_left.mpr (stage_ideal_le_maximal (p := p) (S := S) n M)]

variable (S) in
/-- Helper for Lemma 10.97.8: the inverse owner map from the semilocal maximal spectrum to the
stage quotient is given by pushing the maximal ideal forward along the quotient map. This is the
rewrite needed when reindexing the Artinian stage decomposition back to the fixed owner set. -/
private theorem stage_maximalSpectrum_equiv_semilocal_symm_asIdeal
    (n : ℕ) (M : MaximalSpectrum Sₚ) :
    ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M).asIdeal =
      Ideal.map (Ideal.Quotient.mk (pSₚ ^ (n + 1))) M.asIdeal := by
  rfl

variable (S) in
/-- Helper for Lemma 10.97.8: the forward owner map from the stage quotient back to `Sₚ` is given
by pulling the stage maximal ideal back along the quotient map. This is the companion rewrite for
the fixed-owner Artinian stage comparison. -/
private theorem stage_maximalSpectrum_equiv_semilocal_apply_asIdeal
    (n : ℕ) (N : MaximalSpectrum (Sₚ ⧸ pSₚ ^ (n + 1))) :
    (stage_maximalSpectrum_equiv_semilocal (S := S) p n N).asIdeal =
      Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1))) N.asIdeal := by
  rfl

variable (S) in
/-- Helper for Lemma 10.97.8: each Artinian stage quotient is indexed by the same owner set
`p.asIdeal.primesOver S` as the semilocal localization itself. -/
private noncomputable def stage_maximalSpectrum_equiv_primesOver (n : ℕ) :
    MaximalSpectrum (Sₚ ⧸ pSₚ ^ (n + 1)) ≃ p.asIdeal.primesOver S :=
  (stage_maximalSpectrum_equiv_semilocal (S := S) p n).trans
    (semilocal_maximalSpectrum_equiv_primesOver (S := S) p)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the stage maximal ideal associated to `q` pulls back to the
same semilocal maximal ideal associated to `q`. -/
private theorem stageOwner_comap_eq_semilocalOwner
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1)))
        ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal =
      ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q).asIdeal := by
  -- Apply the right inverse of the quotient-stage owner equivalence and read it on ideals.
  let M := (semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q
  have happly :
      (stage_maximalSpectrum_equiv_semilocal (S := S) p n
          ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M)).asIdeal =
        Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1)))
          (((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M).asIdeal) :=
    stage_maximalSpectrum_equiv_semilocal_apply_asIdeal (S := S) p n
      ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M)
  have hright :
      (stage_maximalSpectrum_equiv_semilocal (S := S) p n
          ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M)).asIdeal =
        M.asIdeal :=
    congrArg (fun M : MaximalSpectrum Sₚ ↦ M.asIdeal)
      ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).right_inv
        M)
  calc
    Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1)))
        ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal =
        (stage_maximalSpectrum_equiv_semilocal (S := S) p n
          ((stage_maximalSpectrum_equiv_semilocal (S := S) p n).symm M)).asIdeal := by
          simpa [stage_maximalSpectrum_equiv_primesOver, M] using happly.symm
    _ = M.asIdeal := hright
    _ = ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q).asIdeal := rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: after passing to the positive stage quotient, the image of
the semilocal owner prime complement is exactly the stage owner prime complement. This is the
owner normalization needed before applying the localization uniqueness equivalence. -/
private theorem stageOwnerPrimeCompl_eq_algebraMapSubmonoid_semilocalOwner
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
    Algebra.algebraMapSubmonoid (Sₚ ⧸ pSₚ ^ (n + 1)) M.asIdeal.primeCompl =
      N.asIdeal.primeCompl := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Proof comment: read non-membership in the stage owner through contraction along the stage
    -- quotient map, then rewrite that contraction to the fixed semilocal owner.
    change Ideal.Quotient.mk (pSₚ ^ (n + 1)) y ∉ N.asIdeal
    change y ∉ Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1))) N.asIdeal
    simpa [M, N, stageOwner_comap_eq_semilocalOwner (S := S) p n q] using hy
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨y, ?_, rfl⟩
    -- Proof comment: any quotient representative outside the stage owner was already outside the
    -- semilocal owner before quotienting.
    change Ideal.Quotient.mk (pSₚ ^ (n + 1)) y ∉ N.asIdeal at hx
    change y ∉ Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1))) N.asIdeal at hx
    simpa [M, N, stageOwner_comap_eq_semilocalOwner (S := S) p n q] using hx

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: localizing the positive stage quotient at the stage owner
identified by `q` is the same as first localizing `Sₚ` at the matching semilocal owner and then
quotienting by the stage ideal. -/
private noncomputable def stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
    Localization.AtPrime N.asIdeal ≃ₐ[Rₚ]
      ((Localization.AtPrime M.asIdeal) ⧸
        Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1))) := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
  let U : Submonoid (Sₚ ⧸ pSₚ ^ (n + 1)) :=
    Algebra.algebraMapSubmonoid (Sₚ ⧸ pSₚ ^ (n + 1)) M.asIdeal.primeCompl
  let Qloc :
      Type u :=
    (Localization.AtPrime M.asIdeal) ⧸
      Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1))
  have hU : U = N.asIdeal.primeCompl := by
    -- Proof comment: the previous prime-complement lemma is exactly the owner rewrite needed to
    -- make the stage localization and the localized quotient localize the same stage ring.
    simpa [U, M, N] using
      stageOwnerPrimeCompl_eq_algebraMapSubmonoid_semilocalOwner (S := S) p n q
  letI : IsLocalization U (Localization.AtPrime N.asIdeal) := by
    simpa [U, hU] using
      (inferInstance : IsLocalization N.asIdeal.primeCompl (Localization.AtPrime N.asIdeal))
  letI : CommRing Qloc := by
    dsimp [Qloc]
    infer_instance
  letI : Algebra Rₚ Qloc := by
    dsimp [Qloc]
    infer_instance
  letI : IsLocalization U Qloc := by
    dsimp [U, Qloc]
    infer_instance
  let eStage :
      Localization U ≃ₐ[Sₚ ⧸ pSₚ ^ (n + 1)] Localization.AtPrime N.asIdeal :=
    Localization.algEquiv U (Localization.AtPrime N.asIdeal)
  let eQuot :
      Localization U ≃ₐ[Sₚ ⧸ pSₚ ^ (n + 1)] Qloc :=
    Localization.algEquiv U Qloc
  -- Proof comment: both targets are now the localization of the same stage quotient at the same
  -- owner submonoid, so uniqueness of localization supplies the comparison.
  exact (eStage.symm.trans eQuot).restrictScalars Rₚ

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the semilocal owner picked out by `q` localizes further to
the genuine local factor `S_q`. This is the second owner transport in the positive-stage route. -/
private noncomputable def semilocalOwnerLocalizationAlgEquiv_localizedFactor
    (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    Localization.AtPrime M.asIdeal ≃ₐ[Rₚ] Localization.AtPrime q.1 := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  let eS :
      Localization.AtPrime q.1 ≃ₐ[S] Localization.AtPrime M.asIdeal := by
    -- Proof comment: rewrite the contracted semilocal owner back to the prime `q`, then invoke
    -- the canonical iterated-localization equivalence.
    simpa [M, semilocalOwner_comap_eq_primesOver (S := S) p q] using
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M.asIdeal)
  let eRing : Localization.AtPrime M.asIdeal ≃+* Localization.AtPrime q.1 :=
    eS.symm.toRingEquiv
  have hcomp :
      eRing.toRingHom.comp (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) =
        localizedFactorRingHom p q := by
    -- Proof comment: both maps are localizations of `Sₚ` away from the same source submonoid, so
    -- it suffices to compare them on elements coming from `S`.
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    intro s
    change eRing
        (algebraMap Sₚ (Localization.AtPrime M.asIdeal) (algebraMap S Sₚ s)) =
      localizedFactorRingHom p q (algebraMap S Sₚ s)
    simpa [eRing, localizedFactorRingHom, IsScalarTower.algebraMap_eq S Sₚ
      (Localization.AtPrime M.asIdeal)] using (eS.symm.commutes s)
  exact
    AlgEquiv.ofRingEquiv (f := eRing) <| by
      intro x
      -- Proof comment: evaluate the comparison of the two `Sₚ`-maps on `x ∈ Rₚ`, then use the
      -- canonical description of the `Rₚ`-algebra structure on the local factor.
      have hx :=
        congrArg (fun g : Sₚ →+* Localization.AtPrime q.1 ↦ g (algebraMap Rₚ Sₚ x)) hcomp
      have hx' :=
        congrArg (fun g : Rₚ →+* Localization.AtPrime q.1 ↦ g x)
          (localizedFactorRingHom_comp (S := S) p q)
      calc
        eRing (algebraMap Rₚ (Localization.AtPrime M.asIdeal) x) =
            eRing ((algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (algebraMap Rₚ Sₚ x)) := by
              simp [IsScalarTower.algebraMap_eq Rₚ Sₚ (Localization.AtPrime M.asIdeal)]
        _ = localizedFactorRingHom p q (algebraMap Rₚ Sₚ x) := by
              simpa [RingHom.comp_apply] using hx
        _ = algebraMap Rₚ (Localization.AtPrime q.1) x := by
              simpa [RingHom.comp_apply] using hx'

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: after identifying the semilocal owner localization with the
local factor, the localization map from `Sₚ` becomes the previously fixed local-factor map. -/
private theorem semilocalOwnerLocalizationAlgEquiv_localizedFactor_comp_algebraMap
    (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    ((semilocalOwnerLocalizationAlgEquiv_localizedFactor (S := S) p q).toRingHom).comp
        (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) =
      localizedFactorRingHom p q := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  -- Proof comment: unfold the comparison equivalence and reuse the localization-uniqueness
  -- comparison established in its construction.
  dsimp [semilocalOwnerLocalizationAlgEquiv_localizedFactor]
  let eS :
      Localization.AtPrime q.1 ≃ₐ[S] Localization.AtPrime M.asIdeal :=
    by
      simpa [M, semilocalOwner_comap_eq_primesOver (S := S) p q] using
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M.asIdeal)
  let eRing : Localization.AtPrime M.asIdeal ≃+* Localization.AtPrime q.1 :=
    eS.symm.toRingEquiv
  change eRing.toRingHom.comp (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) =
    localizedFactorRingHom p q
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  intro s
  change eRing
      (algebraMap Sₚ (Localization.AtPrime M.asIdeal) (algebraMap S Sₚ s)) =
    localizedFactorRingHom p q (algebraMap S Sₚ s)
  simpa [eRing, localizedFactorRingHom, IsScalarTower.algebraMap_eq S Sₚ
    (Localization.AtPrime M.asIdeal)] using (eS.symm.commutes s)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: transporting the stage ideal through the semilocal-to-local
equivalence yields the corrected power `J_q^(n + 1)` on the local factor. -/
private theorem semilocalOwnerLocalizationAlgEquiv_localizedFactor_map_stageIdeal
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    Ideal.map
        (semilocalOwnerLocalizationAlgEquiv_localizedFactor (S := S) p q).toRingHom
        (Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1))) =
      localizedFactorIdeal p q ^ (n + 1) := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  -- Proof comment: compose the two quotient-side algebra maps and then rewrite the resulting
  -- image ideal into the stable `J_q` notation.
  rw [Ideal.map_map]
  simpa [M, semilocalOwnerLocalizationAlgEquiv_localizedFactor_comp_algebraMap (S := S) p q] using
    (localizedFactorIdeal_pow_eq_map_pow (p := p) q (n + 1)).symm

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: quotienting the semilocal owner localization by the stage
ideal matches quotienting the true local factor by `J_q^(n + 1)`. -/
private noncomputable def semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    ((Localization.AtPrime M.asIdeal) ⧸
        Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1))) ≃ₐ[Rₚ]
      (Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ (n + 1)) := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  -- Proof comment: first identify the two localizations, then transport the quotient ideal along
  -- that equivalence using the directed ideal rewrite proved above.
  exact
    Ideal.quotientEquivAlg
      (Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1)))
      (localizedFactorIdeal p q ^ (n + 1))
      (semilocalOwnerLocalizationAlgEquiv_localizedFactor (S := S) p q)
      (semilocalOwnerLocalizationAlgEquiv_localizedFactor_map_stageIdeal
        (S := S) p n q)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the first quotient-localization transport sends the stage
class of `s` to the quotient class of the same element inside the semilocal owner localization. -/
private theorem stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient_apply_mk
    (n : ℕ) (s : Sₚ) (q : p.asIdeal.primesOver S) :
    let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
    let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
    stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q
        (algebraMap (Sₚ ⧸ pSₚ ^ (n + 1)) (Localization.AtPrime N.asIdeal)
          (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1)))
        (algebraMap Sₚ (Localization.AtPrime M.asIdeal) s) := by
  let M := ((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q)
  let N := ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)
  let U : Submonoid (Sₚ ⧸ pSₚ ^ (n + 1)) :=
    Algebra.algebraMapSubmonoid (Sₚ ⧸ pSₚ ^ (n + 1)) M.asIdeal.primeCompl
  let Qloc :
      Type u :=
    (Localization.AtPrime M.asIdeal) ⧸
      Ideal.map (algebraMap Sₚ (Localization.AtPrime M.asIdeal)) (pSₚ ^ (n + 1))
  have hU : U = N.asIdeal.primeCompl := by
    simpa [U, M, N] using
      stageOwnerPrimeCompl_eq_algebraMapSubmonoid_semilocalOwner (S := S) p n q
  letI : IsLocalization U (Localization.AtPrime N.asIdeal) := by
    simpa [U, hU] using
      (inferInstance : IsLocalization N.asIdeal.primeCompl (Localization.AtPrime N.asIdeal))
  letI : CommRing Qloc := by
    dsimp [Qloc]
    infer_instance
  letI : Algebra Rₚ Qloc := by
    dsimp [Qloc]
    infer_instance
  letI : IsLocalization U Qloc := by
    dsimp [U, Qloc]
    infer_instance
  -- Proof comment: both localization equivalences fix the stage quotient generators, so their
  -- composite sends the canonical localized stage class to the quotient class of `s`.
  simp [stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient, U, Qloc, M, N, hU,
    IsScalarTower.algebraMap_eq (Sₚ ⧸ pSₚ ^ (n + 1)) (Localization U)
      (Localization.AtPrime N.asIdeal)]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the second quotient transport sends a semilocal quotient
class to the corresponding quotient class in the true local factor. -/
private theorem semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient_apply_mk
    (n : ℕ) (q : p.asIdeal.primesOver S)
    (x : Localization.AtPrime
      (((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q).asIdeal)) :
    semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q
        (Ideal.Quotient.mk
          (Ideal.map
            (algebraMap Sₚ
              (Localization.AtPrime
                (((semilocal_maximalSpectrum_equiv_primesOver (S := S) p).symm q).asIdeal)))
            (pSₚ ^ (n + 1)))
          x) =
      Ideal.Quotient.mk (localizedFactorIdeal p q ^ (n + 1))
        ((semilocalOwnerLocalizationAlgEquiv_localizedFactor (S := S) p q) x) := by
  -- Proof comment: this is the quotient transport formula for `Ideal.quotientEquivAlg`.
  simp [semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: after composing the two coordinate transports, the reindexed
Artinian-stage product map becomes the corrected stage map to `J_q^(n + 1)`-quotients. -/
private theorem stagePadicProductMap_succ_apply_mk_via_stageQuotient
    (n : ℕ) (s : Sₚ) (q : p.asIdeal.primesOver S) :
    let eCoord :=
      (stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
        (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q)
    eCoord
        (MaximalSpectrum.toPiLocalization (Sₚ ⧸ pSₚ ^ (n + 1))
          (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s)
          ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)) =
      stagePadicProductMap S p (n + 1)
        (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s) q := by
  let eCoord :=
    (stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
      (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q)
  -- Proof comment: first rewrite the Artinian-stage coordinate as the canonical localization of
  -- the quotient class, then apply the two quotient transports in turn.
  rw [stageQuotient_toPiLocalization_apply_mk_primesOver (S := S) p n s q,
    stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient_apply_mk (S := S) p n s q,
    semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient_apply_mk (S := S) p n q,
    stagePadicProductMap_apply_mk (S := S) p (n + 1) s q]
  rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: every positive Artinian stage of the corrected product map
is bijective, obtained by transporting the canonical stage decomposition through the two owner
equivalences above. -/
private theorem stagePadicProductMap_succ_bijective (n : ℕ) :
    Function.Bijective (stagePadicProductMap S p (n + 1)) := by
  let eIndex := stage_maximalSpectrum_equiv_primesOver (S := S) p n
  let f₀ := MaximalSpectrum.toPiLocalization (Sₚ ⧸ pSₚ ^ (n + 1))
  let f₁ :
      (∀ M : MaximalSpectrum (Sₚ ⧸ pSₚ ^ (n + 1)), Localization.AtPrime M.asIdeal) →
        ∀ q : p.asIdeal.primesOver S,
          Localization.AtPrime (eIndex.symm q).asIdeal :=
    fun y q ↦ y (eIndex.symm q)
  let f₂ :
      (∀ q : p.asIdeal.primesOver S,
          Localization.AtPrime (eIndex.symm q).asIdeal) →
        ∀ q : p.asIdeal.primesOver S,
          Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ (n + 1) :=
    fun y q ↦
      ((stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
        (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q))
        (y q)
  have hf₀ : Function.Bijective f₀ :=
    stageQuotient_toPiLocalization_bijective (S := S) p n
  have hf₁ : Function.Bijective f₁ := by
    constructor
    · intro y₁ y₂ h
      funext M
      have hM := congrArg (fun f ↦ f (eIndex M)) h
      simpa using hM
    · intro z
      refine ⟨fun M ↦ z (eIndex M), ?_⟩
      funext q
      simp [f₁]
  have hf₂ : Function.Bijective f₂ := by
    constructor
    · intro y₁ y₂ h
      funext q
      exact ((stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
        (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q)).injective
          (congrArg (fun f ↦ f q) h)
    · intro z
      refine ⟨fun q ↦
        (((stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
          (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q)).symm
          (z q)), ?_⟩
      funext q
      exact ((stageOwnerLocalizationAlgEquiv_semilocalOwnerQuotient (S := S) p n q).trans
        (semilocalOwnerQuotientAlgEquiv_localizedFactorPowQuotient (S := S) p n q)).apply_symm_apply
          (z q)
  have htransport : Function.Bijective (fun x ↦ f₂ (f₁ (f₀ x))) := by
    constructor
    · intro x y hxy
      apply hf₀.1
      apply hf₁.1
      exact hf₂.1 hxy
    · intro z
      rcases hf₂.2 z with ⟨z₂, rfl⟩
      rcases hf₁.2 z₂ with ⟨z₁, rfl⟩
      rcases hf₀.2 z₁ with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hEq :
      (fun x : Sₚ ⧸ pSₚ ^ (n + 1) ↦ f₂ (f₁ (f₀ x))) = stagePadicProductMap S p (n + 1) := by
    funext x
    refine Quotient.inductionOn' x ?_
    intro s
    funext q
    simpa [f₀, f₁, f₂] using
      stagePadicProductMap_succ_apply_mk_via_stageQuotient (S := S) p n s q
  -- Proof comment: once the transported stage map is identified with `stagePadicProductMap`, the
  -- Artinian-stage bijectivity carries over directly.
  rw [← hEq]
  exact htransport

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the stage maximal ideal associated to `q` contracts all the
way back along `S → Sₚ ⧸ pSₚ^(n + 1)` to the prime `q`. -/
private theorem stageOwner_comap_eq_primesOver
    (n : ℕ) (q : p.asIdeal.primesOver S) :
    Ideal.comap (algebraMap S (Sₚ ⧸ pSₚ ^ (n + 1)))
        ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal =
      q.1 := by
  -- First pull the stage owner back to `Sₚ`, then use the semilocal owner contraction.
  have hcomp :
      algebraMap S (Sₚ ⧸ pSₚ ^ (n + 1)) =
        (Ideal.Quotient.mk (pSₚ ^ (n + 1))).comp (algebraMap S Sₚ) := by
    ext x
    rfl
  calc
    Ideal.comap (algebraMap S (Sₚ ⧸ pSₚ ^ (n + 1)))
        ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal =
        Ideal.comap (algebraMap S Sₚ)
          (Ideal.comap (Ideal.Quotient.mk (pSₚ ^ (n + 1)))
            ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal) := by
          rw [hcomp, Ideal.comap_comap]
    _ = q.1 := by
          rw [stageOwner_comap_eq_semilocalOwner (S := S) p n q,
            semilocalOwner_comap_eq_primesOver (S := S) p q]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the prime spectrum of a positive finite stage is finite. -/
private theorem stageQuotient_primeSpectrum_finite (n : ℕ) :
    Finite (PrimeSpectrum (Sₚ ⧸ pSₚ ^ (n + 1))) := by
  letI : IsArtinianRing (Sₚ ⧸ pSₚ ^ (n + 1)) := stageQuotient_isArtinian (S := S) p n
  -- Artinian rings have only finitely many prime ideals.
  infer_instance

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: a positive finite stage has Krull dimension zero. -/
private theorem stageQuotient_krullDimLE_zero (n : ℕ) :
    Ring.KrullDimLE 0 (Sₚ ⧸ pSₚ ^ (n + 1)) := by
  -- The Artinian stage theorem packages Noetherianity and dimension zero at once.
  exact
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp
      (stageQuotient_isArtinian (S := S) p n)).2

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: each positive finite stage has discrete prime spectrum, so
the Artinian product decomposition can be applied uniformly at that stage. -/
private theorem stageQuotient_primeSpectrum_discreteTopology (n : ℕ) :
    DiscreteTopology (PrimeSpectrum (Sₚ ⧸ pSₚ ^ (n + 1))) := by
  -- Artinian rings are Noetherian of Krull dimension zero, hence have discrete spectrum.
  exact
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr
      ⟨stageQuotient_primeSpectrum_finite (S := S) p n,
        stageQuotient_krullDimLE_zero (S := S) p n⟩

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the canonical Artinian-stage map from
`Sₚ ⧸ pSₚ^(n + 1)` to the product of its localizations at maximal ideals is bijective. -/
private theorem stageQuotient_toPiLocalization_bijective (n : ℕ) :
    Function.Bijective
      (MaximalSpectrum.toPiLocalization (Sₚ ⧸ pSₚ ^ (n + 1))) := by
  letI : DiscreteTopology (PrimeSpectrum (Sₚ ⧸ pSₚ ^ (n + 1))) :=
    stageQuotient_primeSpectrum_discreteTopology (S := S) p n
  -- The source proof uses the Artinian product decomposition; in mathlib this is the bijective
  -- statement that the canonical map to the product of localizations is both injective and
  -- surjective.
  exact
    ⟨MaximalSpectrum.toPiLocalization_injective (Sₚ ⧸ pSₚ ^ (n + 1)),
      PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology
        (Sₚ ⧸ pSₚ ^ (n + 1))⟩

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: on quotient representatives, the Artinian-stage product
map is the ordinary localization map in each maximal-ideal coordinate. -/
private theorem stageQuotient_toPiLocalization_apply_mk
    (n : ℕ) (s : Sₚ) (M : MaximalSpectrum (Sₚ ⧸ pSₚ ^ (n + 1))) :
    MaximalSpectrum.toPiLocalization (Sₚ ⧸ pSₚ ^ (n + 1))
        (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s) M =
      algebraMap (Sₚ ⧸ pSₚ ^ (n + 1)) (Localization.AtPrime M.asIdeal)
        (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s) := by
  -- The product map is coordinatewise the canonical localization map.
  exact MaximalSpectrum.toPiLocalization_apply_apply (R := Sₚ ⧸ pSₚ ^ (n + 1))

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: after reindexing a positive Artinian stage by primes over
`p`, the product decomposition still evaluates quotient representatives by the canonical
localization map in the selected coordinate. -/
private theorem stageQuotient_toPiLocalization_apply_mk_primesOver
    (n : ℕ) (s : Sₚ) (q : p.asIdeal.primesOver S) :
    MaximalSpectrum.toPiLocalization (Sₚ ⧸ pSₚ ^ (n + 1))
        (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s)
        ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q) =
      algebraMap (Sₚ ⧸ pSₚ ^ (n + 1))
        (Localization.AtPrime
          (((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q).asIdeal))
        (Ideal.Quotient.mk (pSₚ ^ (n + 1)) s) := by
  -- This is just the coordinate formula for the canonical product map, specialized to the
  -- fixed owner `p.asIdeal.primesOver S`.
  exact stageQuotient_toPiLocalization_apply_mk (S := S) p n s
    ((stage_maximalSpectrum_equiv_primesOver (S := S) p n).symm q)

variable (S) in
/-- Helper for Lemma 10.97.8: the product comparison evaluates coordinatewise to the previously
defined local completion maps. -/
private theorem completion_localizationAtPrime_toPiLocalRingCompletion_apply
    (q : p.asIdeal.primesOver S) (x : AdicCompletion pSₚ Sₚ) :
    completion_localizationAtPrime_toPiLocalRingCompletion S p x q =
      completionFactorAlgHom p q x := by
  -- The product comparison is defined by packaging the coordinate maps into `Pi.algHom`.
  rfl

variable (S) in
/-- Helper for Lemma 10.97.8: after evaluating a coordinate of the product comparison at stage
`n`, one obtains the corresponding stage quotient map to the local factor. -/
private theorem completion_localizationAtPrime_toPiLocalRingCompletion_eval_a
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q.1)) n
        (completion_localizationAtPrime_toPiLocalRingCompletion S p x q) =
      completionFactorQuotientMap p q n x := by
  -- First read off the `q`-coordinate, then use the evaluation formula for that coordinate map.
  rw [completion_localizationAtPrime_toPiLocalRingCompletion_apply (S := S)]
  exact completionFactorAlgHom_eval_a p q n x

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the corrected finite-stage product comparison uses the
mapped ideal `J_q = localizedFactorIdeal p q` in each local factor. This is the stage normal form
where quotienting commutes directly with the localized factor maps. -/
private noncomputable def stagePadicProductMap (n : ℕ) :
    Sₚ ⧸ pSₚ ^ n →ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n :=
  Pi.algHom Rₚ
    (fun q : p.asIdeal.primesOver S ↦
      Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n)
    (fun q ↦
      Ideal.quotientMapₐ (localizedFactorIdeal p q ^ n) (localizedFactorAlgHom p q)
        (localizedFactorIdealPow_le_comap p q n))

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the corrected finite-stage product map sends a semilocal
quotient representative to the corresponding quotient representative in every `J_q` coordinate. -/
private theorem stagePadicProductMap_apply_mk
    (n : ℕ) (s : Sₚ) (q : p.asIdeal.primesOver S) :
    stagePadicProductMap S p n (Ideal.Quotient.mk (pSₚ ^ n) s) q =
      Ideal.Quotient.mk (localizedFactorIdeal p q ^ n) ((localizedFactorAlgHom p q) s) := by
  -- The product map is assembled coordinatewise from the quotient maps induced by
  -- `localizedFactorAlgHom`.
  rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the corrected finite-stage product maps commute with the
source and target quotient transition maps. This is the compatibility needed by the inverse-limit
assembly once the stage maps are known to be bijective. -/
private theorem stagePadicProductMap_transition {m n : ℕ} (h : m ≤ n)
    (x : Sₚ ⧸ pSₚ ^ n) (q : p.asIdeal.primesOver S) :
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h) :
        Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n →ₐ[Rₚ]
          Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ m)
        (stagePadicProductMap S p n x q) =
      stagePadicProductMap S p m
        ((Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h) :
          Sₚ ⧸ pSₚ ^ n →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ m) x) q := by
  -- Check the equality on semilocal quotient representatives and then in every product coordinate.
  refine Quotient.inductionOn' x ?_
  intro s
  -- On representatives both sides are the same quotient class in the lower `J_q ^ m` stage.
  rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the zero stage of the corrected finite-stage product map is
bijective, since all source and target quotients are quotients by the top ideal. -/
private theorem stagePadicProductMap_zero_bijective :
    Function.Bijective (stagePadicProductMap S p 0) := by
  -- Both the semilocal source quotient and each local target quotient are subsingletons at stage
  -- zero, so any map between them is automatically bijective.
  have hsource : Subsingleton (Sₚ ⧸ pSₚ ^ 0) := by
    simpa using (inferInstance : Subsingleton (Sₚ ⧸ (⊤ : Ideal Sₚ)))
  constructor
  · intro x y _
    exact @Subsingleton.elim _ hsource x y
  · intro y
    refine ⟨0, ?_⟩
    funext q
    have htarget :
        Subsingleton (Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ 0) := by
      simpa using
        (inferInstance :
          Subsingleton (Localization.AtPrime q.1 ⧸ (⊤ : Ideal (Localization.AtPrime q.1))))
    exact @Subsingleton.elim _ htarget _ (y q)

/-- Helper for Chap10 Lemma 10 97 8: the canonical map from `Rₚ` to each local factor
`S_q` is a local homomorphism. -/
private theorem localizedFactor_base_isLocalHom (q : p.asIdeal.primesOver S) :
    IsLocalHom (algebraMap Rₚ (Localization.AtPrime q.1)) := by
  -- The algebra structure on the target local factor is the canonical local homomorphism between
  -- localizations at lying-over prime ideals.
  change IsLocalHom
    (Localization.localRingHom p.asIdeal q.1 (algebraMap R S) Ideal.LiesOver.over)
  exact Localization.isLocalHom_localRingHom p.asIdeal q.1 (algebraMap R S)
    Ideal.LiesOver.over

/-- Helper for Chap10 Lemma 10 97 8: the maximal ideal of the localized base ring `Rₚ` is
finitely generated. -/
private theorem localizedBase_maximalIdeal_fg :
    (mₚ : Ideal Rₚ).FG := by
  -- Noetherianity localizes, and every ideal in a Noetherian ring is finitely generated.
  letI : IsNoetherianRing Rₚ :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl Rₚ inferInstance
  exact Ideal.FG.of_isNoetherianRing mₚ

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the product comparison from the semilocal completion to the
product of the `J_q`-adic local completions. This is the corrected completion-level target before
the final comparison with maximal-ideal completions. -/
private noncomputable def completion_localizationAtPrime_toPiPadicCompletion :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1) :=
  Pi.algHom Rₚ
    (fun q : p.asIdeal.primesOver S ↦
      AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1))
    (fun q ↦ completionFactorPadicAlgHom p q)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the `J_q`-adic product comparison evaluates coordinatewise to
the local factor completion maps. -/
private theorem completion_localizationAtPrime_toPiPadicCompletion_apply
    (q : p.asIdeal.primesOver S) (x : AdicCompletion pSₚ Sₚ) :
    completion_localizationAtPrime_toPiPadicCompletion S p x q =
      completionFactorPadicAlgHom p q x := by
  -- The product comparison is defined by packaging the `J_q`-adic coordinate maps into `Pi.algHom`.
  rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: evaluating a coordinate of the corrected `J_q`-adic product
comparison at stage `n` gives the quotient map induced by `Sₚ → S_q`. -/
private theorem completion_localizationAtPrime_toPiPadicCompletion_eval_a
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    AdicCompletion.evalₐ (localizedFactorIdeal p q) n
        (completion_localizationAtPrime_toPiPadicCompletion S p x q) =
      completionFactorPadicQuotientMap p q n x := by
  -- Read off the coordinate and use the evaluation formula for the lifted `J_q`-adic factor map.
  rw [completion_localizationAtPrime_toPiPadicCompletion_apply (S := S)]
  exact completionFactorPadicAlgHom_eval_a p q n x

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: every maximal-ideal coordinate of the original product
comparison is obtained from the corrected `J_q`-adic coordinate by the finite-stage quotient map
`J_q^n ≤ maximalIdeal^n`. -/
private theorem completion_localizationAtPrime_toPiLocalRingCompletion_eval_a_eq_factor_padic
    (q : p.asIdeal.primesOver S) (n : ℕ) (x : AdicCompletion pSₚ Sₚ) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q.1)) n
        (completion_localizationAtPrime_toPiLocalRingCompletion S p x q) =
      (Ideal.Quotient.factorₐ Rₚ (localizedFactorIdeal_pow_le_maximal_pow p q n))
        (AdicCompletion.evalₐ (localizedFactorIdeal p q) n
          (completion_localizationAtPrime_toPiPadicCompletion S p x q)) := by
  -- Normalize both completion coordinates to their defining quotient maps, then use the finite-stage
  -- bridge from the `J_q` quotient to the maximal-ideal quotient.
  rw [completion_localizationAtPrime_toPiLocalRingCompletion_eval_a (S := S),
    completion_localizationAtPrime_toPiPadicCompletion_eval_a (S := S),
    completionFactorQuotientMap_eq_factor_padic]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: each local factor `S_q` remains finite over the localized
base `Rₚ`. -/
private theorem localizedFactor_moduleFinite
    (q : p.asIdeal.primesOver S) :
    Module.Finite Rₚ (Localization.AtPrime q.1) := by
  letI : Module.Finite S (Localization.AtPrime q.1) :=
    Module.Finite.of_restrictScalars_finite S (Localization.AtPrime q.1)
      (Localization.AtPrime q.1)
  letI : Module.Finite R (Localization.AtPrime q.1) :=
    Module.Finite.trans R S (Localization.AtPrime q.1)
  have hcomp : (algebraMap R (Localization.AtPrime q.1)).Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  have hmap :
      (algebraMap Rₚ (Localization.AtPrime q.1)).comp (algebraMap R Rₚ) =
        algebraMap R (Localization.AtPrime q.1) := by
    ext x
    simp [IsScalarTower.algebraMap_eq R Rₚ (Localization.AtPrime q.1)]
  -- The local factor is already finite over `R`, so finiteness descends to the localization map
  -- `R → Rₚ`.
  exact RingHom.finite_algebraMap.mp <| hmap ▸ RingHom.Finite.of_comp_finite hcomp

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the stage-one residue quotient of each local factor is
finite over the residue ring of the localized base. -/
private theorem localizedFactor_residue_moduleFinite
    (q : p.asIdeal.primesOver S) :
    Module.Finite (Rₚ ⧸ mₚ) (Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q) := by
  letI : Module.Finite Rₚ (Localization.AtPrime q.1) :=
    localizedFactor_moduleFinite (S := S) p q
  have hquot :
      Module.Finite (Rₚ ⧸ mₚ)
        (Localization.AtPrime q.1 ⧸
          Ideal.map (algebraMap Rₚ (Localization.AtPrime q.1)) mₚ) := by
    infer_instance
  -- Rewrite the mapped base ideal in the stable `J_q` notation used by the corrected route.
  simpa [localizedFactorIdeal_eq_map_maximalIdeal (p := p) q] using hquot

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: for each `q | p`, Lemma 10.97.7 compares the `J_q`-adic
completion of the local factor with its maximal-ideal completion. -/
private noncomputable def completionFactorPadicAlgEquiv_localRingCompletion
    (q : p.asIdeal.primesOver S) :
    AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1) ≃ₐ[Rₚ]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) := by
  letI : IsLocalHom (algebraMap Rₚ (Localization.AtPrime q.1)) :=
    localizedFactor_base_isLocalHom (p := p) q
  let hmR : (maximalIdeal Rₚ).FG := localizedBase_maximalIdeal_fg (p := p) (S := S)
  letI : Module.Finite Rₚ (Localization.AtPrime q.1) :=
    localizedFactor_moduleFinite (S := S) p q
  let hfinite_quotient :
      Module.Finite (Rₚ ⧸ mₚ) (Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q) :=
    localizedFactor_residue_moduleFinite (S := S) p q
  -- Route correction: compare the two completions coordinatewise first, then compose this stable
  -- owner-level bridge with the product map only after the `J_q`-adic inverse-limit bijection is
  -- available.
  simpa [localizedFactorIdeal_eq_map_maximalIdeal (p := p) q] using
    (((maximalIdealCompletionAlgEquivMadicCompletion
        (R := Rₚ) (S := Localization.AtPrime q.1) hmR hfinite_quotient).symm).restrictScalars Rₚ)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the coordinate comparison fixes dense images of local-factor
elements. -/
private theorem completionFactorPadicAlgEquiv_localRingCompletion_of
    (q : p.asIdeal.primesOver S) (y : Localization.AtPrime q.1) :
    completionFactorPadicAlgEquiv_localRingCompletion (S := S) p q
        (AdicCompletion.of (localizedFactorIdeal p q) (Localization.AtPrime q.1) y) =
      AdicCompletion.of
        (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) y := by
  letI : IsLocalHom (algebraMap Rₚ (Localization.AtPrime q.1)) :=
    localizedFactor_base_isLocalHom (p := p) q
  let hmR : (maximalIdeal Rₚ).FG := localizedBase_maximalIdeal_fg (p := p) (S := S)
  letI : Module.Finite Rₚ (Localization.AtPrime q.1) :=
    localizedFactor_moduleFinite (S := S) p q
  let hfinite_quotient :
      Module.Finite (Rₚ ⧸ mₚ) (Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q) :=
    localizedFactor_residue_moduleFinite (S := S) p q
  -- Read the coordinate bridge as the inverse of Lemma 10.97.7 and evaluate it on `of`.
  simpa [completionFactorPadicAlgEquiv_localRingCompletion, localizedFactorIdeal_eq_map_maximalIdeal
      (p := p) q] using
    (maximalIdealCompletionAlgEquivMadicCompletion_of
      (R := Rₚ) (S := Localization.AtPrime q.1) hmR hfinite_quotient y).symm

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the `J_q`-adic coordinate map sends dense semilocal elements
to the dense image of their localized value. -/
private theorem completionFactorPadicAlgHom_of
    (q : p.asIdeal.primesOver S) (s : Sₚ) :
    completionFactorPadicAlgHom p q (AdicCompletion.of pSₚ Sₚ s) =
      AdicCompletion.of (localizedFactorIdeal p q) (Localization.AtPrime q.1)
        ((localizedFactorAlgHom p q) s) := by
  -- Compare both completion elements stagewise, where both sides are the same quotient class.
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionFactorPadicAlgHom_eval_a]
  simp [completionFactorPadicQuotientMap, AdicCompletion.evalₐ_of]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the maximal-ideal coordinate map also sends dense semilocal
elements to the dense image of their localized value. -/
private theorem completionFactorAlgHom_of
    (q : p.asIdeal.primesOver S) (s : Sₚ) :
    completionFactorAlgHom p q (AdicCompletion.of pSₚ Sₚ s) =
      AdicCompletion.of
        (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)
        ((localizedFactorAlgHom p q) s) := by
  -- Compare both completion elements stagewise, where both sides are the same quotient class.
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionFactorAlgHom_eval_a]
  simp [completionFactorQuotientMap, AdicCompletion.evalₐ_of]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: every maximal-ideal coordinate is obtained by applying the
coordinate comparison equivalence to the corrected `J_q`-adic coordinate. -/
private theorem completion_localizationAtPrime_toPiLocalRingCompletion_apply_via_padic
    (x : AdicCompletion pSₚ Sₚ) (q : p.asIdeal.primesOver S) :
    completion_localizationAtPrime_toPiLocalRingCompletion S p x q =
      completionFactorPadicAlgEquiv_localRingCompletion (S := S) p q
        (completion_localizationAtPrime_toPiPadicCompletion S p x q) := by
  -- Both coordinate maps are determined by their values on dense semilocal elements.
  refine AdicCompletion.induction_on (I := pSₚ) (M := Sₚ) x ?_
  intro s
  rw [completion_localizationAtPrime_toPiLocalRingCompletion_apply (S := S),
    completion_localizationAtPrime_toPiPadicCompletion_apply (S := S),
    completionFactorAlgHom_of (S := S), completionFactorPadicAlgHom_of (S := S),
    completionFactorPadicAlgEquiv_localRingCompletion_of (S := S)]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: evaluating the corrected stage product map on the stage
quotient of a semilocal completion element recovers the defining `J_q`-adic stage quotient map. -/
private theorem stagePadicProductMap_evalₐ
    (n : ℕ) (x : AdicCompletion pSₚ Sₚ) (q : p.asIdeal.primesOver S) :
    stagePadicProductMap S p n (AdicCompletion.evalₐ pSₚ n x) q =
      completionFactorPadicQuotientMap p q n x := by
  -- Both sides are definitionally the same quotient map followed by stage evaluation.
  rfl

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: package the stagewise bijectivity of the corrected finite
product maps into a single owner-level equivalence for stage `n`. -/
private noncomputable def stagePadicProductEquiv
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) (n : ℕ) :
    Sₚ ⧸ pSₚ ^ n ≃ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n :=
  AlgEquiv.ofBijective (stagePadicProductMap S p n) (hstage n)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: under stagewise bijectivity, the `n`th quotient of the
semilocal completion is recovered by inverting the stage product map on the family of coordinate
stage evaluations. -/
private noncomputable def piPadicCompletionToStageQuotient
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) (n : ℕ) :
    (∀ q : p.asIdeal.primesOver S,
        AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) →ₐ[Rₚ]
      Sₚ ⧸ pSₚ ^ n :=
  ((stagePadicProductEquiv (S := S) p hstage n).symm.toAlgHom).comp
    (Pi.algHom Rₚ
      (fun q : p.asIdeal.primesOver S ↦
        Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n)
      (fun q ↦ AdicCompletion.evalₐ (localizedFactorIdeal p q) n))

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: after inverting the `n`th finite-stage product map, applying
that product map again recovers the original family of stage evaluations. -/
private theorem stagePadicProductEquiv_piPadicCompletionToStageQuotient
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n))
    (n : ℕ)
    (y : ∀ q : p.asIdeal.primesOver S,
      AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) :
    stagePadicProductMap S p n
        (piPadicCompletionToStageQuotient (S := S) p hstage n y) =
      fun q : p.asIdeal.primesOver S ↦
        AdicCompletion.evalₐ (localizedFactorIdeal p q) n (y q) := by
  let e := stagePadicProductEquiv (S := S) p hstage n
  -- Proof comment: the stage inverse was defined by composing the family of evaluations with
  -- `e.symm`, so reapplying `e` is just `apply_symm_apply`.
  change
    e
        (((e.symm.toAlgHom).comp
            (Pi.algHom Rₚ
              (fun q : p.asIdeal.primesOver S ↦
                Localization.AtPrime q.1 ⧸ localizedFactorIdeal p q ^ n)
              (fun q ↦ AdicCompletion.evalₐ (localizedFactorIdeal p q) n))) y) =
      fun q : p.asIdeal.primesOver S ↦
        AdicCompletion.evalₐ (localizedFactorIdeal p q) n (y q)
  simp [piPadicCompletionToStageQuotient, e]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the stagewise inverse maps are compatible with the source
completion transition maps once the corrected finite-stage product maps are bijective. -/
private theorem piPadicCompletionToStageQuotient_compatible
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n))
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
        (piPadicCompletionToStageQuotient (S := S) p hstage n) =
      piPadicCompletionToStageQuotient (S := S) p hstage m := by
  ext y
  apply (hstage m).1
  ext q
  -- Proof comment: compare both candidate stage-`m` preimages after reapplying the stage-`m`
  -- product map; compatibility then reduces to the completion transition formula on each
  -- coordinate.
  rw [stagePadicProductMap_transition (S := S) (p := p) h,
    stagePadicProductEquiv_piPadicCompletionToStageQuotient (S := S) p hstage n y,
    stagePadicProductEquiv_piPadicCompletionToStageQuotient (S := S) p hstage m y]
  exact AdicCompletion.transitionMap_comp_eval_apply h (y q)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: stagewise bijectivity of the corrected finite-stage product
maps lifts to an inverse algebra hom from the product of `J_q`-adic completions back to the
semilocal completion. -/
private noncomputable def piPadicCompletionTo_completion_localizationAtPrime
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) :
    (∀ q : p.asIdeal.primesOver S,
        AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) →ₐ[Rₚ]
      AdicCompletion pSₚ Sₚ :=
  AdicCompletion.liftAlgHom pSₚ
    (piPadicCompletionToStageQuotient (S := S) p hstage)
    (fun {m n} h =>
      piPadicCompletionToStageQuotient_compatible (S := S) p hstage h)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: evaluating the inverse completion map at stage `n` recovers
the chosen stagewise inverse. -/
private theorem piPadicCompletionTo_completion_localizationAtPrime_evalₐ
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n))
    (n : ℕ)
    (y : ∀ q : p.asIdeal.primesOver S,
      AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) :
    AdicCompletion.evalₐ pSₚ n
        (piPadicCompletionTo_completion_localizationAtPrime (S := S) p hstage y) =
      piPadicCompletionToStageQuotient (S := S) p hstage n y := by
  -- Proof comment: this is the standard stage-evaluation formula for `liftAlgHom`.
  simpa [piPadicCompletionTo_completion_localizationAtPrime] using
    (AdicCompletion.evalₐ_liftAlgHom pSₚ
      (piPadicCompletionToStageQuotient (S := S) p hstage)
      (fun {m n} h =>
        piPadicCompletionToStageQuotient_compatible (S := S) p hstage h) n y)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: once every corrected finite-stage product map is bijective,
the induced map on `J_q`-adic completions is injective and has the explicit stagewise inverse
constructed above. -/
private theorem piPadicCompletionTo_completion_localizationAtPrime_leftInverse
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) :
    Function.LeftInverse
      (piPadicCompletionTo_completion_localizationAtPrime (S := S) p hstage)
      (completion_localizationAtPrime_toPiPadicCompletion S p) := by
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [piPadicCompletionTo_completion_localizationAtPrime_evalₐ (S := S) p hstage]
  apply (hstage n).1
  ext q
  -- Proof comment: after reapplying the stage product map, both sides become the same coordinate
  -- `J_q`-adic stage evaluation of `x`.
  rw [stagePadicProductEquiv_piPadicCompletionToStageQuotient (S := S) p hstage]
  rw [stagePadicProductMap_evalₐ (S := S) p n x q,
    completion_localizationAtPrime_toPiPadicCompletion_eval_a (S := S) p q n x]

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: the explicit inverse map on `J_q`-adic completions is also a
right inverse once the corrected finite-stage product maps are bijective. -/
private theorem piPadicCompletionTo_completion_localizationAtPrime_rightInverse
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) :
    Function.RightInverse
      (piPadicCompletionTo_completion_localizationAtPrime (S := S) p hstage)
      (completion_localizationAtPrime_toPiPadicCompletion S p) := by
  intro y
  ext q
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completion_localizationAtPrime_toPiPadicCompletion_eval_a (S := S) p q n]
  rw [← stagePadicProductMap_evalₐ (S := S) p n
      (piPadicCompletionTo_completion_localizationAtPrime (S := S) p hstage y) q]
  rw [piPadicCompletionTo_completion_localizationAtPrime_evalₐ (S := S) p hstage]
  exact congrArg (fun f ↦ f q)
    (stagePadicProductEquiv_piPadicCompletionToStageQuotient (S := S) p hstage n y)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: stagewise bijectivity of the corrected finite-stage product
maps lifts to bijectivity of the product map on `J_q`-adic completions. -/
private theorem completion_localizationAtPrime_toPiPadicCompletion_bijective_of_stageBijective
    (hstage : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)) :
    Function.Bijective
      (completion_localizationAtPrime_toPiPadicCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) := by
  let g := piPadicCompletionTo_completion_localizationAtPrime (S := S) p hstage
  have hleft :
      Function.LeftInverse g (completion_localizationAtPrime_toPiPadicCompletion S p) :=
    piPadicCompletionTo_completion_localizationAtPrime_leftInverse (S := S) p hstage
  have hright :
      Function.RightInverse g (completion_localizationAtPrime_toPiPadicCompletion S p) :=
    piPadicCompletionTo_completion_localizationAtPrime_rightInverse (S := S) p hstage
  -- Proof comment: the explicit inverse gives injectivity from the left-inverse identity and
  -- surjectivity from the right-inverse identity.
  exact ⟨hleft.injective, hright.surjective⟩

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: separating the zero stage from the positive stages suffices
to recover bijectivity for all corrected finite-stage product maps. -/
private theorem stagePadicProductMap_bijective_of_zero_succ
    (hsucc : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p (n + 1))) :
    ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p n)
  | 0 => stagePadicProductMap_zero_bijective (S := S) p
  | n + 1 => hsucc n

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: positive-stage bijectivity of the corrected finite-stage
product maps is exactly the remaining input needed to deduce bijectivity on `J_q`-adic
completions. -/
private theorem completion_localizationAtPrime_toPiPadicCompletion_bijective_of_stageSuccBijective
    (hsucc : ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p (n + 1))) :
    Function.Bijective
      (completion_localizationAtPrime_toPiPadicCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) := by
  -- Proof comment: the zero stage was handled separately, so only the positive-stage Artinian
  -- comparison remains as a genuine new premise.
  exact completion_localizationAtPrime_toPiPadicCompletion_bijective_of_stageBijective
    (S := S) p (stagePadicProductMap_bijective_of_zero_succ (S := S) p hsucc)

variable (S) in
/-- Helper for Chap10 Lemma 10 97 8: once the corrected `J_q`-adic product map is bijective, the
public product map to maximal-ideal completions is bijective by composing with the coordinatewise
comparison equivalences from Lemma 10.97.7. -/
private theorem completion_localizationAtPrime_toPiLocalRingCompletion_bijective_of_padic
    (hpadic :
      Function.Bijective
        (completion_localizationAtPrime_toPiPadicCompletion S p :
          AdicCompletion pSₚ Sₚ →
            ∀ q : p.asIdeal.primesOver S,
              AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1))) :
    Function.Bijective
      (completion_localizationAtPrime_toPiLocalRingCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) := by
  constructor
  · intro x y hxy
    apply hpadic.1
    ext q
    -- Proof comment: pull each coordinate back through the fixed comparison equivalence from
    -- `J_q`-adic completion to maximal-ideal completion.
    have hxyq := congrArg (fun f ↦ f q) hxy
    exact
      (completionFactorPadicAlgEquiv_localRingCompletion (S := S) p q).injective <|
        by
          rw [completion_localizationAtPrime_toPiLocalRingCompletion_apply_via_padic (S := S) p x q,
            completion_localizationAtPrime_toPiLocalRingCompletion_apply_via_padic (S := S) p y q]
          exact hxyq
  · intro y
    let yPadic :
        ∀ q : p.asIdeal.primesOver S,
          AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1) :=
      fun q ↦
        (completionFactorPadicAlgEquiv_localRingCompletion (S := S) p q).symm (y q)
    rcases hpadic.2 yPadic with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext q
    -- Proof comment: the chosen preimage has the prescribed `J_q`-adic coordinate, so applying
    -- the coordinate comparison equivalence gives the required maximal-ideal coordinate.
    have hxq := congrArg (fun f ↦ f q) hx
    rw [completion_localizationAtPrime_toPiLocalRingCompletion_apply_via_padic (S := S) p x q]
    simpa [yPadic] using
      congrArg (completionFactorPadicAlgEquiv_localRingCompletion (S := S) p q) hxq

variable (S) in
/-- Lemma 10.97.8, product side: the canonical comparison map from the completed semilocal
localization `Sₚ` to the product of the completed local rings at the primes of `S` lying over `p`
is bijective. -/
@[stacks 07N9]
theorem completion_localizationAtPrime_toPiLocalRingCompletion_bijective :
    Function.Bijective
      (completion_localizationAtPrime_toPiLocalRingCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) := by
  -- Route correction: the public theorem now factors through the generic inverse-limit lemma
  -- `completion_localizationAtPrime_toPiPadicCompletion_bijective_of_stageSuccBijective`, so the
  -- only remaining blocker is the positive-stage Artinian comparison for `stagePadicProductMap`.
  have hpadic :
      Function.Bijective
        (completion_localizationAtPrime_toPiPadicCompletion S p :
          AdicCompletion pSₚ Sₚ →
            ∀ q : p.asIdeal.primesOver S,
              AdicCompletion (localizedFactorIdeal p q) (Localization.AtPrime q.1)) := by
    have hsucc :
        ∀ n : ℕ, Function.Bijective (stagePadicProductMap S p (n + 1)) := by
      intro n
      -- Proof comment: reuse the positive-stage Artinian product decomposition after transporting
      -- each coordinate through the semilocal-owner and local-factor quotient equivalences.
      exact stagePadicProductMap_succ_bijective (S := S) p n
    exact
      completion_localizationAtPrime_toPiPadicCompletion_bijective_of_stageSuccBijective
        (S := S) p hsucc
  -- Proof comment: once the corrected `J_q`-adic product map is bijective, the public theorem is
  -- the coordinatewise completion comparison from Lemma 10.97.7.
  exact
    completion_localizationAtPrime_toPiLocalRingCompletion_bijective_of_padic
      (S := S) p hpadic

variable (S) in
/-- Lemma 10.97.8: the completion of the semilocal localization `Sₚ` along the ideal induced by
`p` is canonically identified, as an `Rₚ`-algebra, with the product of the completed local rings
at the primes of `S` lying over `p`. This is the product-side companion used to obtain the direct
source-facing tensor decomposition below. -/
@[stacks 07N9]
noncomputable def completion_localizationAtPrime_algEquiv_pi_localRingCompletion :
    AdicCompletion pSₚ Sₚ ≃ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  AlgEquiv.ofBijective (completion_localizationAtPrime_toPiLocalRingCompletion S p)
    (completion_localizationAtPrime_toPiLocalRingCompletion_bijective S p)

variable (S) in
/-- Lemma 10.97.8: the completed tensor product `Rₚ^ ⊗[R] S` is canonically identified, as a
ring, with the product of the completed local rings `∏_{q | p} S_q^∧`, indexed by the canonical
owner set `p.asIdeal.primesOver S`. This is the direct source-facing composite of the two
textbook equalities `Rₚ^ ⊗[R] S = (Sₚ)^∧ = ∏_{q | p} S_q^∧`. -/
@[stacks 07N9]
noncomputable def completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion :
    Rₚ^ ⊗[R] S ≃+*
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  (completion_tensorProductOverBase_ringEquiv_completion_localizationAtPrime p).trans
    (completion_localizationAtPrime_algEquiv_pi_localRingCompletion S p).toRingEquiv

end

end
