import Mathlib
import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap10.Lemma_10_96_9
import StacksProject_2024.Chap10.Lemma_10_96_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing Ideal AdicCompletion

universe u v

section maximalIdealCompletionComparison

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B

/-- Under a local homomorphism, every power of the source maximal ideal maps into the corresponding
power of the target maximal ideal. -/
theorem pow_maximalIdeal_le_comap_pow_maximalIdeal (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap f := by
  -- Map the source maximal ideal into the target maximal ideal, then pass to powers.
  exact
    (Ideal.map_le_iff_le_comap).mp <| by
      simpa [Ideal.map_pow] using
        Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) n

private def maximalIdealCompletionQuotientMap (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    ACompletion →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap (maximalIdeal B ^ n) f (pow_maximalIdeal_le_comap_pow_maximalIdeal f n)).comp
    (AdicCompletion.evalₐ (maximalIdeal A) n)

/-- The quotient maps defining the canonical map on maximal-ideal completions are compatible with
the transition maps in the inverse system for the target completion. -/
private theorem maximalIdealCompletionQuotientMap_compatible (f : A →+* B) [IsLocalHom f]
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp
        (maximalIdealCompletionQuotientMap f n) =
      maximalIdealCompletionQuotientMap f m := by
  ext x
  let p : ACompletion → Prop := fun y ↦
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp
        (maximalIdealCompletionQuotientMap f n) y =
      maximalIdealCompletionQuotientMap f m y
  -- Compare both maps on a Cauchy representative of the completion element.
  change p x
  refine AdicCompletion.induction_on (I := maximalIdeal A) (M := A) x ?_
  intro r
  -- After evaluating at the representative, the target equality is exactly the Cauchy
  -- compatibility at level `m`, pushed forward along the quotient map induced by `f`.
  simpa [maximalIdealCompletionQuotientMap] using
    congrArg
      (Ideal.quotientMap (maximalIdeal B ^ m) f
        (pow_maximalIdeal_le_comap_pow_maximalIdeal f m))
      (AdicCompletion.Ideal.mk_eq_mk (I := maximalIdeal A) (m := m) (n := n) h r)

/-- The canonical map on maximal-ideal completions induced by a local homomorphism of local rings.
-/
noncomputable def maximalIdealCompletionMap (f : A →+* B) [IsLocalHom f] :
    ACompletion →+* BCompletion :=
  AdicCompletion.liftRingHom (maximalIdeal B) (maximalIdealCompletionQuotientMap f)
    (maximalIdealCompletionQuotientMap_compatible f)

/-- The canonical map on maximal-ideal completions extends the original local homomorphism. -/
theorem maximalIdealCompletionMap_comp (f : A →+* B) [IsLocalHom f] :
    (maximalIdealCompletionMap f).comp (algebraMap A ACompletion) =
      RingHom.comp (algebraMap B BCompletion) f := by
  apply RingHom.ext
  intro x
  -- Compare the two completion maps on every quotient stage of the target completion.
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [maximalIdealCompletionMap, maximalIdealCompletionQuotientMap]

end maximalIdealCompletionComparison

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- Helper for Lemma 10.97.7: after restricting scalars to the source ring, the kernel of the
stage-one algebra evaluation is the kernel of the underlying linear evaluation at level one. -/
private theorem ker_evalOneₐ_restrictScalars_eq_ker_eval :
    (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I A)) :
        Submodule (AdicCompletion I A) (AdicCompletion I A)).restrictScalars A) =
      (AdicCompletion.eval I A 1).ker := by
  have hle₁ : I ^ 1 ≤ I ^ 1 • (⊤ : Submodule A A) := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I).symm
  have hle₂ : I ^ 1 • (⊤ : Submodule A A) ≤ I ^ 1 := by
    simpa [pow_one, Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top I)
  -- Compare the two kernels by transporting vanishing across the stage-one quotient factor.
  ext x
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    have hfactor :
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) = 0 := by
      calc
        Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) =
            (AdicCompletion.evalOneₐ I) x := AdicCompletion.factorₐ_evalₐ_one (I := I) x
        _ = 0 := hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      have hf :
          Function.Injective
            (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) : A ⧸ I ^ 1 →+* A ⧸ I) := by
        let e : (A ⧸ I ^ 1) ≃+* (A ⧸ I) := (Ideal.quotientEquivAlgOfEq A (by simp)).toRingEquiv
        simpa [e, pow_one] using e.injective
      exact hf hfactor
    calc
      (AdicCompletion.eval I A 1) x =
          Ideal.Quotient.factor hle₁ ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := 1) x hle₁
      _ = 0 := by simpa [hx']
  · intro hx
    have hx' : (AdicCompletion.evalₐ I 1) x = 0 := by
      calc
        (AdicCompletion.evalₐ I 1) x =
            Submodule.factor hle₂ ((AdicCompletion.eval I A 1) x) := by
              symm
              exact AdicCompletion.factor_eval_eq_evalₐ (I := I) (n := 1) x hle₂
        _ = 0 := by simpa [hx]
    calc
      (AdicCompletion.evalOneₐ I) x =
          Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) ((AdicCompletion.evalₐ I 1) x) := by
            symm
            exact AdicCompletion.factorₐ_evalₐ_one (I := I) x
      _ = 0 := by simpa [hx']

/-- Helper for Lemma 10.97.7: the extended ideal on the stage-one completion is the kernel of the
canonical stage-one evaluation map. -/
private theorem completion_ideal_eq_ker_evalOneA (hI : I.FG) :
    Ideal.map (algebraMap A (AdicCompletion I A)) I =
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
  -- Restrict scalars so the goal matches the module-side kernel statement from Lemma `10.96.3`.
  apply Submodule.restrictScalars_injective A (AdicCompletion I A) (AdicCompletion I A)
  calc
    (((Ideal.map (algebraMap A (AdicCompletion I A)) I : Ideal (AdicCompletion I A)) :
        Submodule (AdicCompletion I A) (AdicCompletion I A)).restrictScalars A) =
        I • (⊤ : Submodule A (AdicCompletion I A)) := by
          simpa [Ideal.smul_top_eq_map]
    _ = (AdicCompletion.eval I A 1).ker := by
      -- Finite generation identifies the first kernel with the image ideal.
      simpa using (AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := A) (n := 1) hI)
    _ =
        (((RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom : Ideal (AdicCompletion I A)) :
          Submodule (AdicCompletion I A) (AdicCompletion I A)).restrictScalars A) := by
      -- The algebra-valued and linear stage-one evaluation maps have the same kernel.
      symm
      exact ker_evalOneₐ_restrictScalars_eq_ker_eval (I := I)

/-- Helper for Lemma 10.97.7: the adic completion is complete for the adic topology of the
extended ideal. -/
private theorem completion_ideal_isAdicComplete (hI : I.FG) :
    IsAdicComplete (Ideal.map (algebraMap A (AdicCompletion I A)) I) (AdicCompletion I A) := by
  -- Transport owner completeness for `AdicCompletion I A` across the standard map-ideal rewrite.
  have hmap :
      IsAdicComplete (Ideal.map (algebraMap A (AdicCompletion I A)) I) (AdicCompletion I A) ↔
        IsAdicComplete I (AdicCompletion I A) :=
    IsAdicComplete.map_algebraMap_iff (R := A) (S := AdicCompletion I A)
      (M := AdicCompletion I A) (I := I)
  exact hmap.2 (AdicCompletion.isAdicComplete hI)

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-
Domain-style sampling:
* primary domain: adic completions of local rings along the maximal ideal and its extension.
* source-facing layer: the maximal-ideal completion `S^∧` of `S` and its finiteness over `R^∧`.
* core/canonical owner: `AdicCompletion`, especially `adicCompletionLinearEquivOfPowLe` from
  Lemma `10.96.9` and `moduleFinite_of_finite_quotient_of_isHausdorff` from Lemma `10.96.12`.
* sampled upstream declarations:
  `maximalIdealCompletionMap`,
  `adicCompletionLinearEquivOfPowLe`,
  `adicCompletionLinearEquivOfPowLe_of`,
  `isAdicComplete_iff_of_pow_le`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`.
* primitive data: the local rings `R`, `S`, the ideals `maximalIdeal R`, `maximalIdeal S`,
  `Ideal.map (algebraMap R S) (maximalIdeal R)`, and the quotient-finiteness hypothesis.
* derived API: the canonical completion map `R^∧ → S^∧`, the comparison between the two
  completions of `S`, and the finiteness bridge through the `mR S`-adic completion.
-/
local notation "mR" => maximalIdeal R
local notation "mS" => maximalIdeal S
local notation "mRS" => Ideal.map (algebraMap R S) mR
local notation "RCompletion" => AdicCompletion mR R
local notation "SCompletion" => AdicCompletion mS S
local notation "SmCompletion" => AdicCompletion mRS S
local notation "mRC" => Ideal.map (algebraMap R RCompletion) mR

noncomputable instance maximalIdealCompletionAlgebra : Algebra RCompletion SCompletion :=
  (maximalIdealCompletionMap (algebraMap R S)).toAlgebra

/-- The quotient-level maps from `R^∧` to the quotients `S / (m_R S)^n` induced by `R → S`. -/
private def completionBaseQuotientMap (n : ℕ) : RCompletion →ₐ[R] S ⧸ mRS ^ n :=
  (Ideal.quotientMapₐ (mRS ^ n) (Algebra.ofId R S)
    ((Ideal.pow_right_mono (Ideal.le_comap_map : mR ≤ Ideal.comap (algebraMap R S) mRS) n).trans
      (Ideal.le_comap_pow (algebraMap R S) n))).comp
    (AdicCompletion.evalₐ mR n)

-- Proof sketch: reduce to a Cauchy sequence representative `f`; on the `m`-th quotient, the
-- compatibility condition is exactly the statement that `f n` and `f m` become equal modulo
-- `mR ^ m`, and mapping along `R → S` sends this congruence to one modulo `(mR S) ^ m`.
-- The quotient-level maps from `R^∧` to the quotients `S / (mR S)^n` are compatible with the
-- transition maps in the inverse system.
omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- The quotient-level maps `R^∧ → S / (m_R S)^n` are compatible with the transition maps of the
inverse system defining the `m_R S`-adic completion of `S`. -/
private theorem completionBaseQuotientMap_compatible {m n : ℕ} (h : m ≤ n) :
    ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) :
      S ⧸ mRS ^ n →ₐ[R] S ⧸ mRS ^ m)).comp (completionBaseQuotientMap n) =
      completionBaseQuotientMap m := by
  ext x
  let p : RCompletion → Prop := fun y ↦
    ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) :
      S ⧸ mRS ^ n →ₐ[R] S ⧸ mRS ^ m)).comp (completionBaseQuotientMap n) y =
      completionBaseQuotientMap m y
  -- Compare both algebra maps on a Cauchy representative of `x : R^∧`.
  change p x
  refine AdicCompletion.induction_on (I := mR) (M := R) x ?_
  intro r
  -- Route correction: the stable proof is quotientwise at level `m`; broad normalization of the
  -- completion term is unnecessary and was the source of earlier `whnf` pressure.
  simpa [completionBaseQuotientMap] using
    congrArg
      (Ideal.quotientMapₐ (mRS ^ m) (Algebra.ofId R S)
        ((Ideal.pow_right_mono (Ideal.le_comap_map : mR ≤ Ideal.comap (algebraMap R S) mRS) m).trans
          (Ideal.le_comap_pow (algebraMap R S) m)))
      (AdicCompletion.Ideal.mk_eq_mk (I := mR) (m := m) (n := n) h r)

-- The canonical algebra morphism from `R^∧` to the `mR S`-adic completion of `S`.
/-- The canonical algebra morphism from `R^∧` to the `m_R S`-adic completion of `S`. -/
private def completionBaseAlgHom : RCompletion →ₐ[R] SmCompletion :=
  AdicCompletion.liftAlgHom mRS completionBaseQuotientMap completionBaseQuotientMap_compatible

private noncomputable instance completionBaseAlgebra : Algebra RCompletion SmCompletion :=
  completionBaseAlgHom.toAlgebra

/-- Evaluating `completionBaseAlgHom` modulo `(m_R S)^n` recovers the quotient map used to define
it. -/
private theorem completionBaseAlgHom_evalₐ (n : ℕ) (x : RCompletion) :
    AdicCompletion.evalₐ mRS n (completionBaseAlgHom x) = completionBaseQuotientMap n x := by
  simp [completionBaseAlgHom]

/-- The canonical algebra morphism from `R^∧` to the `m_R S`-adic completion of `S` extends the
original map `R → S`. -/
private theorem completionBaseAlgHom_comp :
    completionBaseAlgHom.toRingHom.comp (algebraMap R RCompletion) =
      RingHom.comp (algebraMap S SmCompletion) (algebraMap R S) := by
  apply RingHom.ext
  intro x
  -- Compare both ring maps on every quotient stage of the `m_R S`-adic completion.
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [completionBaseAlgHom]

/-- Mapping the extended maximal ideal of `R` into `SmCompletion` agrees with mapping `m_R S`
into the `m_R S`-adic completion of `S`. -/
private theorem completionBase_map_maximalIdeal :
    Ideal.map (algebraMap RCompletion SmCompletion) mRC =
      Ideal.map (algebraMap S SmCompletion) mRS := by
  -- Route correction: compare the two ideal maps through the canonical extension theorem above
  -- instead of unfolding both algebra structures inside the quotient proof.
  simpa [Ideal.map_map] using
    congrArg
      (fun g : R →+* SmCompletion => Ideal.map g mR)
      completionBaseAlgHom_comp

-- Proof sketch: the finite residue-fibre hypothesis makes the maximal ideal of
-- `S / mR S` nilpotent, hence some power of `maximalIdeal S` lies in `mR S`.
omit [IsLocalHom (algebraMap R S)] in
/-- Under the hypotheses of Lemma `10.97.7`, some positive power of `maximalIdeal S` is contained
in the extended maximal ideal `mR S`. This is the bridge needed to compare the two adic
filtrations on `S`. -/
theorem exists_pow_maximalIdeal_le_map_maximalIdeal
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    ∃ n : ℕ, 0 < n ∧ mS ^ n ≤ mRS := by
  let _hmR : (maximalIdeal R).FG := hmR
  letI : Field (R ⧸ mR) := Ideal.Quotient.field mR
  letI : IsArtinianRing (S ⧸ mRS) := IsArtinianRing.of_finite (R ⧸ mR) (S ⧸ mRS)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (R := S) mRS
  cases n with
  | zero =>
      -- If the quotient ideal is already the whole ring, the first power works automatically.
      have hmRS_top : mRS = ⊤ := by
        simpa using hn
      refine ⟨1, Nat.one_pos, ?_⟩
      simpa [pow_one, hmRS_top]
  | succ n =>
      exact ⟨n + 1, Nat.succ_pos _, hn⟩

private noncomputable def maximalIdealCompletionExponent
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) : ℕ := by
  classical
  exact
    Nat.find
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)

private theorem maximalIdealCompletionExponent_pos
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    0 < maximalIdealCompletionExponent hmR hfinite_quotient := by
  classical
  exact
    (Nat.find_spec
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)).1

private theorem maximalIdealCompletionExponent_pow_le
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    mS ^ maximalIdealCompletionExponent hmR hfinite_quotient ≤ mRS := by
  classical
  exact
    (Nat.find_spec
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)).2

/-- Helper for Lemma 10.97.7: a power containment `mS ^ k ≤ m_R S` propagates to
`mS ^ (k * n) ≤ (m_R S) ^ n`. -/
private theorem maximalIdealCompletion_pow_mul_le_pow
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) :
    mS ^ (maximalIdealCompletionExponent hmR hfinite_quotient * n) ≤ mRS ^ n := by
  -- Rewrite the left-hand side as `(mS ^ k) ^ n`, then use monotonicity of ideal powers.
  rw [pow_mul]
  exact Ideal.pow_right_mono (maximalIdealCompletionExponent_pow_le hmR hfinite_quotient) n

/-- Helper for Lemma 10.97.7: the extended maximal ideal `m_R S` lies in the maximal ideal of
`S`. -/
private theorem map_maximalIdeal_le_target_maximalIdeal :
    mRS ≤ mS := by
  -- A local homomorphism sends the source maximal ideal into the target maximal ideal.
  exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)

/-- Helper for Lemma 10.97.7: positivity of the comparison exponent gives `n ≤ k * n` for every
stage `n`. -/
private theorem le_completionExponent_mul
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) :
    n ≤ maximalIdealCompletionExponent hmR hfinite_quotient * n := by
  -- Multiply the obvious inequality `1 ≤ k` on the right by `n`.
  simpa [one_mul] using
    Nat.mul_le_mul_right n
      (Nat.succ_le_of_lt (maximalIdealCompletionExponent_pos hmR hfinite_quotient))

/-- Helper for Lemma 10.97.7: the quotient family defining the comparison
`S^∧ → completion_{m_R S}(S)`. -/
private noncomputable def maximalIdealCompletionComparisonRightFamily
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) :
    SCompletion →ₐ[S] S ⧸ mRS ^ n :=
  (Ideal.Quotient.factorₐ S (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient n)).comp
    (AdicCompletion.evalₐ mS (maximalIdealCompletionExponent hmR hfinite_quotient * n))

/-- Helper for Lemma 10.97.7: the quotient family defining the inverse comparison
`completion_{m_R S}(S) → S^∧`. -/
private noncomputable def maximalIdealCompletionComparisonLeftFamily (n : ℕ) :
    SmCompletion →ₐ[S] S ⧸ mS ^ n :=
  (Ideal.Quotient.factorₐ S
      (Ideal.pow_right_mono
        (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S)) n)).comp
    (AdicCompletion.evalₐ mRS n)

/-- Helper for Lemma 10.97.7: composing the right comparison quotient map with the quotient
`S / (m_R S)^n → S / m_S^n` recovers the native stage-`n` projection of `S^∧`. -/
private theorem comparison_right_transition_eval
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (z : SCompletion) :
    Ideal.Quotient.factorₐ S
        (Ideal.pow_right_mono
          (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S)) n)
        ((Ideal.Quotient.factorₐ S
            (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient n))
          (AdicCompletion.evalₐ mS
            (maximalIdealCompletionExponent hmR hfinite_quotient * n) z)) =
      AdicCompletion.evalₐ mS n z := by
  let p : SCompletion → Prop := fun w ↦
    Ideal.Quotient.factorₐ S
        (Ideal.pow_right_mono
          (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S)) n)
        ((Ideal.Quotient.factorₐ S
            (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient n))
          (AdicCompletion.evalₐ mS
            (maximalIdealCompletionExponent hmR hfinite_quotient * n) w)) =
      AdicCompletion.evalₐ mS n w
  change p z
  refine AdicCompletion.induction_on (I := mS) (M := S) z ?_
  intro s
  -- On a concrete Cauchy representative, both sides read off the same `n`th residue class.
  dsimp [p]
  simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp] using
    AdicCompletion.Ideal.mk_eq_mk (I := mS) (m := n)
      (n := maximalIdealCompletionExponent hmR hfinite_quotient * n)
      (le_completionExponent_mul hmR hfinite_quotient n) s

/-- Helper for Lemma 10.97.7: composing the left comparison quotient map with the quotient
`S / m_S^(k n) → S / (m_R S)^n` recovers the native stage-`n` projection of the
`m_R S`-adic completion. -/
private theorem comparison_left_transition_eval
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (z : SmCompletion) :
    Ideal.Quotient.factorₐ S
        (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient n)
        ((Ideal.Quotient.factorₐ S
            (Ideal.pow_right_mono
              (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S))
              (maximalIdealCompletionExponent hmR hfinite_quotient * n)))
          (AdicCompletion.evalₐ mRS
            (maximalIdealCompletionExponent hmR hfinite_quotient * n) z)) =
      AdicCompletion.evalₐ mRS n z := by
  let p : SmCompletion → Prop := fun w ↦
    Ideal.Quotient.factorₐ S
        (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient n)
        ((Ideal.Quotient.factorₐ S
            (Ideal.pow_right_mono
              (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S))
              (maximalIdealCompletionExponent hmR hfinite_quotient * n)))
          (AdicCompletion.evalₐ mRS
            (maximalIdealCompletionExponent hmR hfinite_quotient * n) w)) =
      AdicCompletion.evalₐ mRS n w
  change p z
  refine AdicCompletion.induction_on (I := mRS) (M := S) z ?_
  intro s
  -- On a concrete Cauchy representative, both sides read off the same `n`th residue class.
  dsimp [p]
  simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp] using
    AdicCompletion.Ideal.mk_eq_mk (I := mRS) (m := n)
      (n := maximalIdealCompletionExponent hmR hfinite_quotient * n)
      (le_completionExponent_mul hmR hfinite_quotient n) s

/-- Helper for Lemma 10.97.7: the right comparison family is compatible with the transition maps
of the `m_R S`-adic completion. -/
private theorem maximalIdealCompletionComparisonRightFamily_compatible
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hmn)).comp
        (maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient n) =
      maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient m := by
  ext z
  let p : SCompletion → Prop := fun w ↦
    (Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hmn)).comp
        (maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient n) w =
      maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient m w
  change p z
  refine AdicCompletion.induction_on (I := mS) (M := S) z ?_
  intro s
  -- On a concrete Cauchy representative, both sides read off the same `m`th residue class.
  dsimp [p]
  have hs :
      Ideal.Quotient.mk (mS ^ (maximalIdealCompletionExponent hmR hfinite_quotient * m))
          (s (maximalIdealCompletionExponent hmR hfinite_quotient * n)) =
        Ideal.Quotient.mk (mS ^ (maximalIdealCompletionExponent hmR hfinite_quotient * m))
          (s (maximalIdealCompletionExponent hmR hfinite_quotient * m)) := by
    exact AdicCompletion.Ideal.mk_eq_mk (I := mS)
      (m := maximalIdealCompletionExponent hmR hfinite_quotient * m)
      (n := maximalIdealCompletionExponent hmR hfinite_quotient * n)
      (Nat.mul_le_mul_left _ hmn) s
  simpa [AdicCompletion.evalₐ_mk, maximalIdealCompletionComparisonRightFamily,
    Ideal.Quotient.factorₐ_comp] using
    congrArg
      (Ideal.Quotient.factorₐ S (maximalIdealCompletion_pow_mul_le_pow hmR hfinite_quotient m))
      hs

/-- Helper for Lemma 10.97.7: the left comparison family is compatible with the transition maps
of the maximal-ideal completion of `S`. -/
private theorem maximalIdealCompletionComparisonLeftFamily_compatible
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hmn)).comp
        (maximalIdealCompletionComparisonLeftFamily (R := R) (S := S) n) =
      maximalIdealCompletionComparisonLeftFamily (R := R) (S := S) m := by
  ext z
  let p : SmCompletion → Prop := fun w ↦
    (Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hmn)).comp
        (maximalIdealCompletionComparisonLeftFamily (R := R) (S := S) n) w =
      maximalIdealCompletionComparisonLeftFamily (R := R) (S := S) m w
  change p z
  refine AdicCompletion.induction_on (I := mRS) (M := S) z ?_
  intro s
  -- On a concrete Cauchy representative, both sides read off the same `m`th residue class.
  dsimp [p]
  have hs :
      Ideal.Quotient.mk (mRS ^ m) (s n) =
        Ideal.Quotient.mk (mRS ^ m) (s m) := by
    exact AdicCompletion.Ideal.mk_eq_mk (I := mRS) (m := m) (n := n) hmn s
  simpa [AdicCompletion.evalₐ_mk, maximalIdealCompletionComparisonLeftFamily,
    Ideal.Quotient.factorₐ_comp] using
    congrArg
      (Ideal.Quotient.factorₐ S
        (Ideal.pow_right_mono
          (map_maximalIdeal_le_target_maximalIdeal (R := R) (S := S)) m))
      hs

/-- Helper for Lemma 10.97.7: the right comparison map from the maximal-ideal completion of `S`
to the `m_R S`-adic completion of `S`. -/
private noncomputable def maximalIdealCompletionComparisonRightAlgHom
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion →ₐ[S] SmCompletion :=
  AdicCompletion.liftAlgHom mRS
    (maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient)
    (maximalIdealCompletionComparisonRightFamily_compatible (R := R) (S := S) hmR
      hfinite_quotient)

/-- Helper for Lemma 10.97.7: the inverse comparison map from the `m_R S`-adic completion of `S`
to the maximal-ideal completion of `S`. -/
private noncomputable def maximalIdealCompletionComparisonLeftAlgHom :
    SmCompletion →ₐ[S] SCompletion :=
  AdicCompletion.liftAlgHom mS
    (maximalIdealCompletionComparisonLeftFamily (R := R) (S := S))
    (maximalIdealCompletionComparisonLeftFamily_compatible (R := R) (S := S))

/-- Helper for Lemma 10.97.7: evaluating the right comparison map at stage `n` yields the
defining quotient map from stage `k * n`. -/
private theorem maximalIdealCompletionComparisonRightAlgHom_eval_a
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (z : SCompletion) :
    AdicCompletion.evalₐ mRS n
        (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient z) =
      maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient n z := by
  -- This is the quotientwise evaluation formula from `liftAlgHom`.
  simpa [maximalIdealCompletionComparisonRightAlgHom] using
    (AdicCompletion.evalₐ_liftAlgHom mRS
      (maximalIdealCompletionComparisonRightFamily hmR hfinite_quotient)
      (maximalIdealCompletionComparisonRightFamily_compatible (R := R) (S := S) hmR
        hfinite_quotient) n z)

/-- Helper for Lemma 10.97.7: evaluating the left comparison map at stage `n` yields the
defining quotient map from the `m_R S`-adic completion. -/
private theorem maximalIdealCompletionComparisonLeftAlgHom_eval_a
    (n : ℕ) (z : SmCompletion) :
    AdicCompletion.evalₐ mS n
        (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S) z) =
      maximalIdealCompletionComparisonLeftFamily (R := R) (S := S) n z := by
  -- This is the quotientwise evaluation formula from `liftAlgHom`.
  simpa [maximalIdealCompletionComparisonLeftAlgHom] using
    (AdicCompletion.evalₐ_liftAlgHom mS
      (maximalIdealCompletionComparisonLeftFamily (R := R) (S := S))
      (maximalIdealCompletionComparisonLeftFamily_compatible (R := R) (S := S)) n z)

/-- Helper for Lemma 10.97.7: the two comparison maps are inverse on the maximal-ideal
completion. -/
private theorem maximalIdealCompletionComparisonLeft_right
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S)).toLinearMap.comp
        (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S)
      (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient z) = z
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Evaluate the composite at stage `n` and collapse the quotient composite to the native
  -- `mS`-adic transition.
  rw [maximalIdealCompletionComparisonLeftAlgHom_eval_a, maximalIdealCompletionComparisonLeftFamily,
    AlgHom.comp_apply, maximalIdealCompletionComparisonRightAlgHom_eval_a]
  simpa [maximalIdealCompletionComparisonRightFamily]
    using comparison_right_transition_eval (R := R) (S := S) hmR hfinite_quotient n z

/-- Helper for Lemma 10.97.7: the two comparison maps are inverse on the `m_R S`-adic
completion. -/
private theorem maximalIdealCompletionComparisonRight_left
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient).toLinearMap.comp
        (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S)).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient
      (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S) z) = z
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Evaluate the composite at stage `n` and collapse the quotient composite to the native
  -- `(m_R S)`-adic transition.
  rw [maximalIdealCompletionComparisonRightAlgHom_eval_a,
    maximalIdealCompletionComparisonRightFamily, AlgHom.comp_apply,
    maximalIdealCompletionComparisonLeftAlgHom_eval_a]
  simpa [maximalIdealCompletionComparisonLeftFamily]
    using comparison_left_transition_eval (R := R) (S := S) hmR hfinite_quotient n z

/-- Helper for Lemma 10.97.7: the two comparison algebra maps compose to the identity on
`SmCompletion`. -/
private theorem maximalIdealCompletionComparisonRight_left_algHom
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient).comp
        (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S)) =
      AlgHom.id S SmCompletion := by
  apply AlgHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Evaluate the composite at stage `n` and collapse the quotient composite to the native
  -- `(m_R S)`-adic transition.
  rw [AlgHom.id_apply, AlgHom.comp_apply, maximalIdealCompletionComparisonRightAlgHom_eval_a,
    maximalIdealCompletionComparisonRightFamily, AlgHom.comp_apply,
    maximalIdealCompletionComparisonLeftAlgHom_eval_a]
  simpa [maximalIdealCompletionComparisonLeftFamily]
    using comparison_left_transition_eval (R := R) (S := S) hmR hfinite_quotient n z

/-- Helper for Lemma 10.97.7: the two comparison algebra maps compose to the identity on
`SCompletion`. -/
private theorem maximalIdealCompletionComparisonLeft_right_algHom
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S)).comp
        (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient) =
      AlgHom.id S SCompletion := by
  apply AlgHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Evaluate the composite at stage `n` and collapse the quotient composite to the native
  -- `mS`-adic transition.
  rw [AlgHom.id_apply, AlgHom.comp_apply, maximalIdealCompletionComparisonLeftAlgHom_eval_a,
    maximalIdealCompletionComparisonLeftFamily, AlgHom.comp_apply,
    maximalIdealCompletionComparisonRightAlgHom_eval_a]
  simpa [maximalIdealCompletionComparisonRightFamily]
    using comparison_right_transition_eval (R := R) (S := S) hmR hfinite_quotient n z

/-- Helper for Lemma 10.97.7: the local comparison between the two completions of `S` is an
`S`-algebra equivalence. -/
private noncomputable def maximalIdealCompletionComparisonAlgEquiv
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₐ[S] SmCompletion :=
  AlgEquiv.ofAlgHom
    (maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient)
    (maximalIdealCompletionComparisonLeftAlgHom (R := R) (S := S))
    (maximalIdealCompletionComparisonRight_left_algHom (R := R) (S := S) hmR
      hfinite_quotient)
    (maximalIdealCompletionComparisonLeft_right_algHom (R := R) (S := S) hmR
      hfinite_quotient)

/-- Helper for Lemma 10.97.7: the comparison algebra equivalence preserves the canonical image of
`S` inside the two completions. -/
private theorem maximalIdealCompletionComparisonAlgEquiv_of
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (x : S) :
    maximalIdealCompletionComparisonAlgEquiv hmR hfinite_quotient (of mS S x) =
      of mRS S x := by
  -- The packaged algebra equivalence uses the right comparison `AlgHom` as its forward map.
  change maximalIdealCompletionComparisonRightAlgHom hmR hfinite_quotient (of mS S x) =
    of mRS S x
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Compute the `n`th quotient coordinate directly from the defining family.
  rw [maximalIdealCompletionComparisonRightAlgHom_eval_a]
  simp [maximalIdealCompletionComparisonRightFamily]

/-- Helper for Lemma 10.97.7: the canonical linear comparison between the maximal-ideal
completion of `S` and the completion of `S` for the extended ideal `m_R S`. -/
private noncomputable def maximalIdealCompletionComparisonLinearEquiv
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₗ[S] SmCompletion :=
  (maximalIdealCompletionComparisonAlgEquiv hmR hfinite_quotient).toLinearEquiv

/-- Helper for Lemma 10.97.7: the residue ring of `R^∧` modulo the extended maximal ideal is
canonically the residue ring `R / m_R`. -/
private noncomputable def completion_residue_algEquiv
    (hmR : (maximalIdeal R).FG) :
    (RCompletion ⧸ mRC) ≃+* (R ⧸ mR) :=
  (Ideal.quotientEquivAlgOfEq RCompletion
      (completion_ideal_eq_ker_evalOneA (A := R) (I := mR) hmR)).toRingEquiv.trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalOneₐ mR) (AdicCompletion.evalOneₐ_surjective mR)).toRingEquiv

/-- Helper for Lemma 10.97.7: after restricting scalars along the residue-ring identification,
`R^∧ / m_R R^∧` is linearly equivalent to `R / m_R`. -/
private noncomputable def completion_residue_linear_equiv
    (hmR : (maximalIdeal R).FG) :
    let A := RCompletion ⧸ mRC
    let _ : Algebra A (R ⧸ mR) := (completion_residue_algEquiv hmR).toRingHom.toAlgebra
    let _ : Module A (R ⧸ mR) :=
      Module.compHom (R := R ⧸ mR) (S := A) (R ⧸ mR) (completion_residue_algEquiv hmR).toRingHom
    A ≃ₗ[A] (R ⧸ mR) := by
  dsimp
  let _ : Algebra (RCompletion ⧸ mRC) (R ⧸ mR) :=
    (completion_residue_algEquiv hmR).toRingHom.toAlgebra
  let eA : (RCompletion ⧸ mRC) ≃ₐ[RCompletion ⧸ mRC] (R ⧸ mR) :=
    { __ := completion_residue_algEquiv hmR
      commutes' := fun a => rfl }
  -- The residue comparison is already algebra-linear for the transported scalar structure.
  exact eA.toLinearEquiv

/-- Helper for Lemma 10.97.7: the residue quotient `R^∧ / m_R R^∧` is finite over `R^∧`. -/
private theorem completion_residue_finite :
    Module.Finite RCompletion (RCompletion ⧸ mRC) := by
  -- The residue quotient is a quotient of the rank-one regular module `R^∧`.
  exact Module.Finite.of_surjective (Submodule.mkQ mRC) (Submodule.mkQ_surjective mRC)

/-- Helper for Lemma 10.97.7: the stage-one quotient map induced from `R^∧` to `S / m_R S`. -/
private noncomputable def completionBaseEvalOneAlgHom : RCompletion →ₐ[R] S ⧸ mRS :=
  (Ideal.Quotient.factorₐ R (by simp)).comp (completionBaseQuotientMap 1)

private noncomputable instance completionBaseEvalOneAlgebra : Algebra RCompletion (S ⧸ mRS) :=
  completionBaseEvalOneAlgHom.toAlgebra

/-- Helper for Lemma 10.97.7: evaluating the base completion map modulo `m_R S` recovers the
stage-one quotient map from `R^∧`. -/
private theorem completionBase_evalOne_base (c : RCompletion) :
    AdicCompletion.evalOneₐ mRS (completionBaseAlgHom c) = completionBaseEvalOneAlgHom c := by
  -- Both maps are defined by evaluating the `m_R S`-adic completion at level one.
  change Ideal.Quotient.factorₐ R (by simp)
      (AdicCompletion.evalₐ mRS 1 (completionBaseAlgHom c)) =
    Ideal.Quotient.factorₐ R (by simp) (completionBaseQuotientMap 1 c)
  rw [completionBaseAlgHom_evalₐ]

/-- Helper for Lemma 10.97.7: the stage-one base map from `R^∧` to `S / m_R S` factors through
the residue ring `R^∧ / m_R R^∧`. -/
private theorem completion_residue_algEquiv_mk
    (hmR : (maximalIdeal R).FG) (c : RCompletion) :
    completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c) = AdicCompletion.evalOneₐ mR c := by
  -- Evaluate the two quotient identifications directly on the class of `c`.
  rw [completion_residue_algEquiv, RingEquiv.trans_apply]
  change
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalOneₐ mR) (AdicCompletion.evalOneₐ_surjective mR))
      (Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ mR).toRingHom) c) =
    AdicCompletion.evalOneₐ mR c
  exact
    Ideal.quotientKerAlgEquivOfSurjective_mk
      (f := AdicCompletion.evalOneₐ mR) (AdicCompletion.evalOneₐ_surjective mR) c

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Lemma 10.97.7: on a concrete Cauchy representative, the stage-one base map is the
first quotient coordinate mapped along `R → S`. -/
private theorem completionBaseEvalOneAlgHom_mk
    (f : AdicCompletion.AdicCauchySequence mR R) :
    completionBaseEvalOneAlgHom (AdicCompletion.mk mR R f) =
      algebraMap (R ⧸ mR) (S ⧸ mRS) (Ideal.Quotient.mk mR (f 1)) := by
  -- Unfold the defining quotient map at stage one and evaluate the completion on the
  -- representative itself.
  -- At level one, the defining composition reduces directly to the residue-ring algebra map.
  simpa [completionBaseEvalOneAlgHom, completionBaseQuotientMap, AdicCompletion.evalₐ_mk, pow_one]

/-- Helper for Lemma 10.97.7: the stage-one base map from `R^∧` to `S / m_R S` factors through
the residue ring `R^∧ / m_R R^∧`. -/
private theorem completionBaseEvalOneAlgHom_eq_residue_map
    (hmR : (maximalIdeal R).FG) (c : RCompletion) :
    completionBaseEvalOneAlgHom c =
        algebraMap (R ⧸ mR) (S ⧸ mRS)
        (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c)) := by
  let p : RCompletion → Prop := fun x ↦
    completionBaseEvalOneAlgHom x =
      algebraMap (R ⧸ mR) (S ⧸ mRS)
        (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC x))
  -- Reduce to a concrete Cauchy representative so both sides become the explicit stage-one maps.
  change p c
  refine AdicCompletion.induction_on (I := mR) (M := R) c ?_
  intro f
  change
    completionBaseEvalOneAlgHom (AdicCompletion.mk mR R f) =
      algebraMap (R ⧸ mR) (S ⧸ mRS)
        (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC (AdicCompletion.mk mR R f)))
  rw [completion_residue_algEquiv_mk]
  -- Compare both sides with the first quotient coordinate of the representative.
  calc
    completionBaseEvalOneAlgHom (AdicCompletion.mk mR R f)
        = algebraMap (R ⧸ mR) (S ⧸ mRS) (Ideal.Quotient.mk mR (f 1)) :=
          completionBaseEvalOneAlgHom_mk (R := R) (S := S) f
    _ = algebraMap (R ⧸ mR) (S ⧸ mRS) (AdicCompletion.evalOneₐ mR (AdicCompletion.mk mR R f)) := by
          -- The stage-one evaluation of a representative is its first residue class.
          simpa [AdicCompletion.evalₐ_mk, pow_one] using
            congrArg (algebraMap (R ⧸ mR) (S ⧸ mRS))
              ((AdicCompletion.factorₐ_evalₐ_one (I := mR) (AdicCompletion.mk mR R f)).symm)

/-- Helper for Lemma 10.97.7: the `R^∧`-action on `S / m_R S` evaluates pointwise through the
residue quotient `R^∧ / m_R R^∧ ≃ R / m_R`. -/
private theorem completionBase_evalOne_residue_algebraMap_apply
    (hmR : (maximalIdeal R).FG) (c : RCompletion) :
    algebraMap RCompletion (S ⧸ mRS) c =
      algebraMap (R ⧸ mR) (S ⧸ mRS)
        (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c)) := by
  -- The stage-one base map already computes the `R^∧`-action on `S / m_R S`.
  change completionBaseEvalOneAlgHom c =
    algebraMap (R ⧸ mR) (S ⧸ mRS)
      (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c))
  exact completionBaseEvalOneAlgHom_eq_residue_map (R := R) (S := S) hmR c

/-- Helper for Lemma 10.97.7: the stage-one evaluation on `SmCompletion` is linear over `R^∧`. -/
private theorem completionBase_evalOne_smul (c : RCompletion) (x : SmCompletion) :
    AdicCompletion.evalOneₐ mRS (c • x) = c • AdicCompletion.evalOneₐ mRS x := by
  -- Rewrite both scalar actions as multiplication by the corresponding algebra maps.
  change
    AdicCompletion.evalOneₐ mRS ((algebraMap RCompletion SmCompletion c) * x) =
      (algebraMap RCompletion (S ⧸ mRS) c) * AdicCompletion.evalOneₐ mRS x
  rw [map_mul]
  congr 1
  exact completionBase_evalOne_base c

/-- Helper for Lemma 10.97.7: the stage-one evaluation on `SmCompletion` packaged as an
`R^∧`-linear map. -/
private noncomputable def completionBase_evalOne_linear : SmCompletion →ₗ[RCompletion] S ⧸ mRS :=
  { toFun := AdicCompletion.evalOneₐ mRS
    map_add' := map_add (AdicCompletion.evalOneₐ mRS)
    map_smul' := completionBase_evalOne_smul }

/-- Helper for Lemma 10.97.7: the kernel of the stage-one `R^∧`-linear evaluation is exactly the
submodule generated by the extended maximal ideal of `R^∧`. -/
private theorem completionBase_evalOne_linear_ker
    (hmR : (maximalIdeal R).FG) :
    LinearMap.ker completionBase_evalOne_linear = mRC • (⊤ : Submodule RCompletion SmCompletion) := by
  have hmRS : (Ideal.map (algebraMap R S) mR).FG := by
    -- Finite generation of `m_R` propagates across `R → S`.
    simpa using Ideal.FG.map hmR (algebraMap R S)
  calc
    LinearMap.ker completionBase_evalOne_linear =
        (((RingHom.ker (AdicCompletion.evalOneₐ mRS).toRingHom : Ideal SmCompletion) :
          Submodule SmCompletion SmCompletion).restrictScalars RCompletion) := by
          -- The linear and ring kernels are definitionally the same subset.
          ext x
          rfl
    _ =
        (((Ideal.map (algebraMap S SmCompletion) mRS : Ideal SmCompletion) :
          Submodule SmCompletion SmCompletion).restrictScalars RCompletion) := by
          -- Identify the kernel with the extended ideal via the stage-one evaluation theorem.
          simpa [completion_ideal_eq_ker_evalOneA (A := S) (I := mRS) hmRS]
    _ =
        (((Ideal.map (algebraMap RCompletion SmCompletion) mRC : Ideal SmCompletion) :
          Submodule SmCompletion SmCompletion).restrictScalars RCompletion) := by
          -- The two extended ideals agree by functoriality of the completion base map.
          simpa using
            congrArg
              (fun J : Ideal SmCompletion ↦
                (((J : Ideal SmCompletion) : Submodule SmCompletion SmCompletion).restrictScalars
                  RCompletion))
              (completionBase_map_maximalIdeal (R := R) (S := S)).symm
    _ = mRC • (⊤ : Submodule RCompletion SmCompletion) := by
          -- Turn the image ideal back into the standard `I • ⊤` module expression.
          simpa [Ideal.smul_top_eq_map]

/-- Helper for Lemma 10.97.7: the stage-one `R^∧`-linear evaluation is surjective. -/
private theorem completionBase_evalOne_linear_surjective :
    Function.Surjective (completionBase_evalOne_linear (R := R) (S := S)) := by
  -- This is the same underlying function as the canonical stage-one algebra evaluation.
  intro x
  obtain ⟨y, hy⟩ := AdicCompletion.evalOneₐ_surjective mRS x
  exact ⟨y, hy⟩

/-- Helper for Lemma 10.97.7: quotienting `SmCompletion` by `m_R R^∧` identifies with the stage-one
quotient `S / m_R S`. -/
private noncomputable def completionBase_stageOne_quotient_linearEquiv
    (hmR : (maximalIdeal R).FG) :
    (SmCompletion ⧸ (mRC • (⊤ : Submodule RCompletion SmCompletion))) ≃ₗ[RCompletion] (S ⧸ mRS) :=
  (Submodule.quotEquivOfEq _ _
      (completionBase_evalOne_linear_ker (R := R) (S := S) hmR).symm).trans
    (LinearMap.quotKerEquivOfSurjective (f := completionBase_evalOne_linear (R := R) (S := S))
      (completionBase_evalOne_linear_surjective (R := R) (S := S)))

/-- Helper for Lemma 10.97.7: the `R^∧`-action on `S / m_R S` factors through the residue ring
`R^∧ / m_R R^∧` identified with `R / m_R`. -/
private theorem completionBase_evalOne_residue_smul
    (hmR : (maximalIdeal R).FG) (c : RCompletion) (x : S ⧸ mRS) :
    let _ : Algebra (RCompletion ⧸ mRC) (R ⧸ mR) :=
      (completion_residue_algEquiv hmR).toRingHom.toAlgebra
    let _ : Module (RCompletion ⧸ mRC) (S ⧸ mRS) :=
      Module.compHom (R := R ⧸ mR) (S := RCompletion ⧸ mRC) (S ⧸ mRS)
      (completion_residue_algEquiv hmR).toRingHom
    c • x = (Ideal.Quotient.mk mRC c : RCompletion ⧸ mRC) • x := by
  let _ : Algebra (RCompletion ⧸ mRC) (R ⧸ mR) :=
    (completion_residue_algEquiv hmR).toRingHom.toAlgebra
  let _ : Module (RCompletion ⧸ mRC) (S ⧸ mRS) :=
    Module.compHom (R := R ⧸ mR) (S := RCompletion ⧸ mRC) (S ⧸ mRS)
      (completion_residue_algEquiv hmR).toRingHom
  -- Rewrite the left scalar action through the stage-one base map, then compare residue classes.
  change completionBaseEvalOneAlgHom c * x =
    (Ideal.Quotient.mk mRC c : RCompletion ⧸ mRC) • x
  rw [completionBaseEvalOneAlgHom_eq_residue_map (R := R) (S := S) hmR c]
  change
    algebraMap (R ⧸ mR) (S ⧸ mRS)
        (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c)) * x =
      (completion_residue_algEquiv hmR (Ideal.Quotient.mk mRC c) : R ⧸ mR) • x
  simpa [Algebra.smul_def]

/-- Helper for Lemma 10.97.7: the stage-one residue action factors through the canonical tower
`R^∧ → R / m_R → S / m_R S`. -/
private theorem completionBase_evalOne_stageOne_isScalarTower
    (hmR : (maximalIdeal R).FG) :
    let _ : Algebra RCompletion (R ⧸ mR) := (AdicCompletion.evalOneₐ mR).toRingHom.toAlgebra
    IsScalarTower RCompletion (R ⧸ mR) (S ⧸ mRS) := by
  let _ : Algebra RCompletion (R ⧸ mR) := (AdicCompletion.evalOneₐ mR).toRingHom.toAlgebra
  -- Route correction: use the simpler stage-one tower `R^∧ → R / m_R → S / m_R S`
  -- instead of introducing an extra residue-quotient action on `S / m_R S`.
  refine IsScalarTower.of_algebraMap_smul fun c x ↦ ?_
  -- Compare the two scalar actions through the explicit stage-one residue formula.
  rw [Algebra.smul_def, Algebra.smul_def]
  rw [completionBase_evalOne_residue_algebraMap_apply (R := R) (S := S) hmR c]
  rw [completion_residue_algEquiv_mk (R := R) (hmR := hmR) c]
  rfl

/-- Helper for Lemma 10.97.7: the stage-one quotient of the `m_R S`-adic completion is already
finite over `R^∧`. -/
private theorem completionBase_stageOne_quotient_finite_over_completion
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    Module.Finite RCompletion
      (SmCompletion ⧸ (mRC • (⊤ : Submodule RCompletion SmCompletion))) := by
  let _ : Algebra RCompletion (R ⧸ mR) := (AdicCompletion.evalOneₐ mR).toRingHom.toAlgebra
  let _ : IsScalarTower RCompletion (R ⧸ mR) (S ⧸ mRS) :=
    completionBase_evalOne_stageOne_isScalarTower (R := R) (S := S) hmR
  have hfg_top :
      ((⊤ : Submodule (R ⧸ mR) (S ⧸ mRS)).restrictScalars RCompletion).FG := by
    -- Restrict the finite residue module along the surjective stage-one map `R^∧ → R / m_R`.
    exact Submodule.FG.restrictScalars_of_surjective
      (R := RCompletion) (A := R ⧸ mR) (M := S ⧸ mRS) (S := ⊤)
      (Module.Finite.fg_top (R := R ⧸ mR) (M := S ⧸ mRS))
      (AdicCompletion.evalOneₐ_surjective mR)
  letI : Module.Finite RCompletion (S ⧸ mRS) := by
    exact ⟨by simpa using hfg_top⟩
  -- Transport the finite residue quotient across the stage-one linear equivalence.
  exact Module.Finite.equiv (completionBase_stageOne_quotient_linearEquiv (R := R) (S := S) hmR).symm

/-- Helper for Lemma 10.97.7: the comparison equivalence fixes the ring unit. -/
private theorem maximalIdealCompletionComparisonLinearEquiv_map_one
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient (1 : SCompletion) = 1 := by
  -- The linear comparison is the underlying map of an `AlgEquiv`, so it preserves `1`.
  simpa [maximalIdealCompletionComparisonLinearEquiv] using
    (maximalIdealCompletionComparisonAlgEquiv hmR hfinite_quotient).map_one

/-- Helper for Lemma 10.97.7: the `n`th quotient coordinate of the comparison equivalence is
obtained by evaluating at stage `k * n` in the maximal-ideal completion and then quotienting to
`S / (m_R S)^n`. -/
private theorem maximalIdealCompletionComparisonLinearEquiv_eval_a
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (z : SCompletion) :
    AdicCompletion.evalₐ mRS n
        (maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient z) =
      Ideal.Quotient.factorₐ S
        (show mS ^ (maximalIdealCompletionExponent hmR hfinite_quotient * n) ≤ mRS ^ n by
          rw [pow_mul]
          exact Ideal.pow_right_mono
            (maximalIdealCompletionExponent_pow_le hmR hfinite_quotient) n)
        (AdicCompletion.evalₐ mS (maximalIdealCompletionExponent hmR hfinite_quotient * n) z) := by
  -- The forward map of the algebra equivalence is exactly the right comparison `AlgHom`.
  simpa [maximalIdealCompletionComparisonLinearEquiv, maximalIdealCompletionComparisonRightFamily]
    using maximalIdealCompletionComparisonRightAlgHom_eval_a (R := R) (S := S) hmR
      hfinite_quotient n z

/-- Helper for Lemma 10.97.7: the comparison equivalence preserves multiplication. -/
private theorem maximalIdealCompletionComparisonLinearEquiv_map_mul
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (x y : SCompletion) :
    maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient (x * y) =
      maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient x *
        maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient y := by
  -- The linear comparison is the underlying map of an `AlgEquiv`, so multiplication is preserved.
  simpa [maximalIdealCompletionComparisonLinearEquiv] using
    (maximalIdealCompletionComparisonAlgEquiv hmR hfinite_quotient).map_mul x y

/-- Lemma 10.97.7 comparison map: under the usual finiteness hypotheses, the maximal-ideal
completion `S^∧ = AdicCompletion (maximalIdeal S) S` is canonically identified, as an `S`-algebra,
with the `mR S`-adic completion of `S`. This keeps the source-facing completion comparison public,
while realizing it through the chapter's completion-comparison API from Lemma `10.96.9`. -/
noncomputable def maximalIdealCompletionAlgEquivMadicCompletion
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₐ[S] SmCompletion :=
  maximalIdealCompletionComparisonAlgEquiv hmR hfinite_quotient

@[simp]
theorem maximalIdealCompletionAlgEquivMadicCompletion_of
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (x : S) :
    maximalIdealCompletionAlgEquivMadicCompletion hmR hfinite_quotient (of mS S x) =
      of mRS S x := by
  -- The algebra equivalence is built from the comparison linear equivalence, which fixes `of`.
  simpa [maximalIdealCompletionAlgEquivMadicCompletion] using
    maximalIdealCompletionComparisonAlgEquiv_of (R := R) (S := S) hmR hfinite_quotient x

/-- Helper for Lemma 10.97.7: after comparing the two completions of `S`, the image of
`R^∧ → S^∧` at stage `n` agrees with the canonical stage-`n` base quotient map
`R^∧ → S / (m_R S)^n`. -/
private theorem maximalIdealCompletionComparison_comp_base_eval_a
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (n : ℕ) (c : RCompletion) :
    AdicCompletion.evalₐ mRS n
        (maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient
          ((maximalIdealCompletionMap (algebraMap R S)) c)) =
      completionBaseQuotientMap n c := by
  let p : RCompletion → Prop := fun x ↦
    AdicCompletion.evalₐ mRS n
        (maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient
          ((maximalIdealCompletionMap (algebraMap R S)) x)) =
      completionBaseQuotientMap n x
  change p c
  refine AdicCompletion.induction_on (I := mR) (M := R) c ?_
  intro r
  let k := maximalIdealCompletionExponent hmR hfinite_quotient
  -- Compare both sides on the concrete quotient coordinates of the Cauchy representative `r`.
  calc
    AdicCompletion.evalₐ mRS n
        (maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient
          ((maximalIdealCompletionMap (algebraMap R S)) (AdicCompletion.mk mR R r))) =
      Ideal.Quotient.mk (mRS ^ n) (algebraMap R S (r (k * n))) := by
        rw [maximalIdealCompletionComparisonLinearEquiv_eval_a]
        simp [k, maximalIdealCompletionMap, maximalIdealCompletionQuotientMap,
          AdicCompletion.evalₐ_mk]
    _ = Ideal.Quotient.mk (mRS ^ n) (algebraMap R S (r n)) := by
        exact
          congrArg
            (Ideal.quotientMapₐ (mRS ^ n) (Algebra.ofId R S)
              ((Ideal.pow_right_mono (Ideal.le_comap_map : mR ≤ Ideal.comap (algebraMap R S) mRS)
                  n).trans
                (Ideal.le_comap_pow (algebraMap R S) n)))
            (AdicCompletion.Ideal.mk_eq_mk (I := mR) (m := n) (n := k * n)
              (le_completionExponent_mul hmR hfinite_quotient n) r)
    _ = completionBaseQuotientMap n (AdicCompletion.mk mR R r) := by
        simp [completionBaseQuotientMap, AdicCompletion.evalₐ_mk]

/-- Helper for Lemma 10.97.7: the comparison algebra equivalence intertwines the two canonical
base maps from `R^∧` into the two completions of `S`. -/
private theorem maximalIdealCompletionAlgEquivMadicCompletion_comp_base
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    (((maximalIdealCompletionAlgEquivMadicCompletion hmR hfinite_quotient).toAlgHom :
        SCompletion →ₐ[S] SmCompletion).toRingHom).comp
        (maximalIdealCompletionMap (algebraMap R S)) =
      completionBaseAlgHom.toRingHom := by
  -- Compare the two maps on each quotient stage of the `m_R S`-adic completion.
  apply RingHom.ext
  intro c
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [RingHom.comp_apply]
  calc
    AdicCompletion.evalₐ mRS n
        (((maximalIdealCompletionAlgEquivMadicCompletion hmR hfinite_quotient).toAlgHom :
          SCompletion →ₐ[S] SmCompletion) ((maximalIdealCompletionMap (algebraMap R S)) c)) =
      completionBaseQuotientMap n c := by
        simpa using
          maximalIdealCompletionComparison_comp_base_eval_a (R := R) (S := S) hmR
            hfinite_quotient n c
    _ = AdicCompletion.evalₐ mRS n (completionBaseAlgHom c) := by
        symm
        simpa using completionBaseAlgHom_evalₐ (R := R) (S := S) n c

-- Proof sketch: `R^∧` is complete for `mR`, and by construction `SmCompletion` is complete for
-- `mR S`. The quotient modulo `mR` identifies with `S / mR S`, which is finite over `R / mR`.
-- Apply the owner-facing finite-generation criterion from Lemma `10.96.12`.
/-- Bridge companion for Lemma `10.97.7`: the `mR S`-adic completion of `S` is finite over
`R^∧`. -/
theorem madicCompletion_finite
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    Module.Finite RCompletion SmCompletion := by
  have hmRS : (mRS : Ideal S).FG := by
    -- Finite generation of `m_R` propagates across the local homomorphism.
    simpa using Ideal.FG.map hmR (algebraMap R S)
  have hcompleteR : IsAdicComplete mRC RCompletion := by
    -- This is the completion-side adic completeness from Lemma `10.97.5`.
    simpa using completion_ideal_isAdicComplete (A := R) (I := mR) hmR
  letI : IsAdicComplete mRC RCompletion := hcompleteR
  have hcompleteSm_map :
      IsAdicComplete (Ideal.map (algebraMap S SmCompletion) mRS) SmCompletion := by
    -- The `m_R S`-adic completion is complete for the image of `m_R S`.
    simpa using completion_ideal_isAdicComplete (A := S) (I := mRS) hmRS
  have hcompleteSm : IsAdicComplete mRC SmCompletion := by
    -- Rewrite the mapped ideal and then transport completeness across the algebra map.
    have hmap :
        Ideal.map (algebraMap RCompletion SmCompletion) mRC =
          Ideal.map (algebraMap S SmCompletion) mRS :=
      completionBase_map_maximalIdeal (R := R) (S := S)
    letI : IsScalarTower RCompletion SmCompletion SmCompletion :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact (IsAdicComplete.map_algebraMap_iff
      (R := RCompletion) (S := SmCompletion) (M := SmCompletion) (I := mRC)).1 <|
      by simpa [hmap] using hcompleteSm_map
  letI : IsAdicComplete mRC SmCompletion := hcompleteSm
  letI : IsHausdorff mRC SmCompletion := hcompleteSm.toIsHausdorff
  have hfinite_stage_one :
      Module.Finite RCompletion
        (SmCompletion ⧸ (mRC • (⊤ : Submodule RCompletion SmCompletion))) :=
    completionBase_stageOne_quotient_finite_over_completion (R := R) (S := S) hmR
      hfinite_quotient
  letI :
      Module.Finite (RCompletion ⧸ mRC)
        (SmCompletion ⧸ (mRC • (⊤ : Submodule RCompletion SmCompletion))) :=
    Module.Finite.of_restrictScalars_finite RCompletion (RCompletion ⧸ mRC)
      (SmCompletion ⧸ (mRC • (⊤ : Submodule RCompletion SmCompletion)))
  -- Apply Lemma `10.96.12` to the `mRC`-adic module `SmCompletion` over `RCompletion`.
  exact
    @moduleFinite_of_finite_quotient_of_isHausdorff RCompletion _ mRC SmCompletion _ _
      hcompleteR inferInstance inferInstance

/-- Lemma 10.97.7: for a local homomorphism `R → S` of local rings, if `mR` is finitely generated
and `S / mR S` is finite over `R / mR`, then the maximal-ideal completion `S^∧` is finite over
the maximal-ideal completion `R^∧`. -/
theorem maximalIdealCompletion_finite
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    Module.Finite RCompletion SCompletion := by
  let eS := maximalIdealCompletionComparisonLinearEquiv hmR hfinite_quotient
  let e : SCompletion ≃ₗ[RCompletion] SmCompletion :=
    { toFun := eS
      invFun := eS.symm
      map_add' := eS.map_add
      map_smul' := by
        intro c x
        -- Route correction: rewrite both scalar actions as multiplication and use the
        -- intertwining identity between the two base maps from `R^∧`.
        change
          eS ((maximalIdealCompletionMap (algebraMap R S) c) * x) =
            completionBaseAlgHom c * eS x
        rw [maximalIdealCompletionComparisonLinearEquiv_map_mul hmR hfinite_quotient]
        congr 1
        exact DFunLike.congr_fun
          (maximalIdealCompletionAlgEquivMadicCompletion_comp_base hmR hfinite_quotient) c
      left_inv := eS.left_inv
      right_inv := eS.right_inv }
  letI : Module.Finite RCompletion SmCompletion :=
    madicCompletion_finite hmR hfinite_quotient
  exact Module.Finite.equiv e.symm

end
