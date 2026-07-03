import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_97_8 (from Chap10) -/
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

private noncomputable def localizedTensorProduct_to_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  Algebra.TensorProduct.productMap (completionBaseAlgHom p)
    ((Algebra.ofId Sₚ (AdicCompletion pSₚ Sₚ)).restrictScalars Rₚ)

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
          simp [Ideal.smul_eq_mul]
    _ = (mₚ ^ n • (⊤ : Submodule Rₚ Sₚ)) := by
          symm
          exact localized_stage_smul_top_eq_stage_map (p := p) (S := S) n

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

private theorem localizedTensorProduct_to_completion_localizationAtPrime_bijective :
    Function.Bijective
      ((localizedTensorProduct_to_completion_localizationAtPrime p :
        Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ) :
        Rₚ^ ⊗[Rₚ] Sₚ → AdicCompletion pSₚ Sₚ) := by
  -- Route correction: this comparison is the owner tensor/completion map after localizing at `p`.
  -- TODO: compare this map with the Noetherian tensor/product comparison for the `mₚ`-adic module
  -- completion by upgrading `localizedModuleCompletion_to_ringCompletion` to the relevant
  -- `Rₚ^`-linear statement, and then identify
  -- `localizedTensorProduct_to_completion_localizationAtPrime p` with the composite of
  -- `localizedModuleCompletion_to_ringCompletion` and
  -- `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ`.
  sorry

noncomputable def localizedTensorProduct_algEquiv_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ ≃ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  AlgEquiv.ofBijective (localizedTensorProduct_to_completion_localizationAtPrime p)
    (localizedTensorProduct_to_completion_localizationAtPrime_bijective p)

/-- Lemma 10.97.8, first equality: the textbook tensor term `Rₚ^ ⊗[R] S` canonically identifies,
as a ring, with the completion of the semilocal localization `Sₚ`. This is the source-facing
first comparison `Rₚ^ ⊗[R] S = (Sₚ)^∧`, before passing to the product decomposition. -/
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

private lemma localizedFactorPow_le_comap (q : p.asIdeal.primesOver S) (n : ℕ) :
    pSₚ ^ n ≤ Ideal.comap (localizedFactorAlgHom p q).toRingHom
      (maximalIdeal (Localization.AtPrime q.1) ^ n) := by
  exact
    (Ideal.map_le_iff_le_comap).mp <| by
      simpa [Ideal.map_pow] using
        Ideal.pow_right_mono (localizedFactorAlgHom_map_pSₚ_le p q) n

/-- Helper for Lemma 10.97.8: the stage-`n` quotient map from the completed semilocal
localization to the `q`-factor quotient is induced by the canonical map `Sₚ → S_q`. -/
private noncomputable def completionFactorQuotientMap (q : p.asIdeal.primesOver S) (n : ℕ) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      Localization.AtPrime q.1 ⧸ maximalIdeal (Localization.AtPrime q.1) ^ n :=
  (Ideal.quotientMapₐ _ (localizedFactorAlgHom p q)
    (localizedFactorPow_le_comap p q n)).comp
    ((AdicCompletion.evalₐ pSₚ n).restrictScalars Rₚ)

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
/-- Lemma 10.97.8, product side: the canonical comparison map from the completed semilocal
localization `Sₚ` to the product of the completed local rings at the primes of `S` lying over `p`
is bijective. -/
theorem completion_localizationAtPrime_toPiLocalRingCompletion_bijective :
    Function.Bijective
      (completion_localizationAtPrime_toPiLocalRingCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) := by
  -- Route correction: the Artinian stage input is now explicit through
  -- `stageQuotient_isArtinian`; the remaining source-faithful work is the stagewise product
  -- decomposition and the compatibility needed to lift its inverse to completions.
  -- TODO: the fixed owner set is now
  -- `semilocal_maximalSpectrum_equiv_primesOver (S := S) p : MaximalSpectrum Sₚ ≃ p.asIdeal.primesOver S`.
  -- The remaining source-faithful step is to show that each positive stage quotient
  -- `Sₚ ⧸ pSₚ^(n + 1)` has the same maximal-spectrum owners as `Sₚ`, apply the Artinian product
  -- decomposition there, rewrite each factor to
  -- `Localization.AtPrime q.1 ⧸ maximalIdeal (Localization.AtPrime q.1)^(n + 1)`, and then lift
  -- the compatible stagewise inverses to the adic completion.
  sorry

variable (S) in
/-- Lemma 10.97.8: the completion of the semilocal localization `Sₚ` along the ideal induced by
`p` is canonically identified, as an `Rₚ`-algebra, with the product of the completed local rings
at the primes of `S` lying over `p`. This is the product-side companion used to obtain the direct
source-facing tensor decomposition below. -/
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
noncomputable def completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion :
    Rₚ^ ⊗[R] S ≃+*
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  (completion_tensorProductOverBase_ringEquiv_completion_localizationAtPrime p).trans
    (completion_localizationAtPrime_algEquiv_pi_localRingCompletion S p).toRingEquiv

end

end
