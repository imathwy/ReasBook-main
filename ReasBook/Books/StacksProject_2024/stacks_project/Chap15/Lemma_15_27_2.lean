import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_91_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open AdicCompletion
open CategoryTheory
open CategoryTheory.ShortComplex
open LinearMap

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: flatness of adic completions of free modules over a Noetherian ring;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `AdicCompletion.flat_of_isNoetherian`,
  `adicCompletionDirectSumToPi_universallyInjective`,
  `adicCompletion_isNoetherian_and_flat_of_flat_mod_ideal_and_tor_one_vanishing`;
- primitive data: the ideal `I`, the index type `A`, and the free `R`-module `⨁ a : A, R`;
- derived API: the universally injective comparison with the product module from
  Lemma `15.27.1`, and the more general completion-flatness criterion later packaged in
  Lemma `15.27.5`.

Source/core/bridge triage:
- `source-facing`: the flatness statement for the completed direct sum from the Stacks lemma;
- `core/canonical`: the owner predicate `Module.Flat`;
- `bridge/view`: the canonical comparison map from the completed direct sum to the product module.
-/

-- Proof sketch: combine the universally injective comparison map from Lemma `15.27.1` with the
-- flatness of the product module over a Noetherian ring and the flat completion map
-- `R → AdicCompletion I R`. The public statement should remain on the canonical owner
-- `Module.Flat R (AdicCompletion I (⨁ a, R))`; the comparison map and any quotient/tensor bridges
-- belong to the proof route rather than the theorem surface.
/-- Helper for Lemma 15.27.2: over the completed ring `R^`, the completed direct sum maps
universally exactly into the product module, so flatness of the product implies flatness of the
completed direct sum. -/
lemma completed_directSum_flat_over_completed_ring (I : Ideal R) (A : Type v) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    Module.Flat Rhat (AdicCompletion J (⨁ _ : A, Rhat)) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  letI : IsNoetherianRing Rhat :=
    (adicCompletion_isNoetherian_and_isAdicComplete (I := I) I.fg_of_isNoetherianRing).1
  letI : IsAdicComplete J Rhat :=
    (adicCompletion_isNoetherian_and_isAdicComplete (I := I) I.fg_of_isNoetherianRing).2
  let cmp :
      AdicCompletion J (⨁ _ : A, Rhat) →ₗ[Rhat] A → Rhat :=
    adicCompletionDirectSumToPi (R := Rhat) (I := J) A
  have hPiFlat : Module.Flat Rhat (A → Rhat) :=
    (Module.noetherian_pi_flat_and_mittagLeffler : _
      ∧ Module.MittagLeffler Rhat (A → Rhat)).1
  have hCmpInjective :
      Function.Injective cmp := by
    -- Reduce ordinary injectivity to injectivity of the induced map on the quotient by `0`.
    have hq :
        Function.Injective (cmp.quotientMapByIdeal (⊥ : Ideal Rhat)) :=
      injective_quotientMapByIdeal_of_universallyInjective
        cmp
        (adicCompletionDirectSumToPi_universallyInjective
          (R := Rhat) (I := J) (A := A))
        (⊥ : Ideal Rhat)
    intro x y hxy
    have hmkQ :
        ((⊥ • (⊤ : Submodule Rhat (AdicCompletion J (⨁ _ : A, Rhat)))).mkQ x) =
          ((⊥ • (⊤ : Submodule Rhat (AdicCompletion J (⨁ _ : A, Rhat)))).mkQ y) := by
      apply hq
      simpa [LinearMap.quotientMapByIdeal, hxy]
    exact sub_eq_zero.mp <|
      (Submodule.Quotient.eq
        (⊥ : Submodule Rhat (AdicCompletion J (⨁ _ : A, Rhat)))).mp <| by
          simpa using hmkQ
  let S :
      ShortComplex (ModuleCat Rhat) :=
    ShortComplex.moduleCatMk cmp cmp.range.mkQ (by ext x <;> rfl)
  have hShortExact : S.ShortExact := by
    -- The quotient by the range is always surjective, and exactness is the kernel-range identity.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, LinearMap.exact_iff]
      simp
    · exact (ModuleCat.mono_iff_injective _).2 hCmpInjective
    · exact (ModuleCat.epi_iff_surjective _).2 cmp.range.mkQ_surjective
  have hUniversallyExact : S.UniversallyExact := by
    -- Lemma 15.27.1 provides the universal injectivity of the comparison map in the complete case.
    exact ⟨hShortExact,
      adicCompletionDirectSumToPi_universallyInjective
        (R := Rhat) (I := J) (A := A)⟩
  -- Apply the owner theorem for universally exact short complexes with flat middle term.
  exact UniversallyExact.flat_X₁ hUniversallyExact

/-- Helper for Lemma 15.27.2: the original completion `AdicCompletion I (⨁ a, R)` is complete for
the extended ideal on the completed base ring `R^`. -/
private theorem original_completion_isAdicComplete
    (I : Ideal R) (A : Type v) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I (⨁ _ : A, R)) := by
  -- Move completeness across the flat completion map using the owner equivalence
  -- `IsAdicComplete.map_algebraMap_iff`.
  have hcomplete :
      IsAdicComplete I (AdicCompletion I (⨁ _ : A, R)) :=
    AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing
  exact (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I (⨁ _ : A, R))).2 hcomplete

/-- Helper for Lemma 15.27.2: the completed direct sum over `R^` is still `I`-adically complete
after restricting scalars along `R → R^`. -/
private theorem completed_directSum_isAdicComplete_restrictScalars
    (I : Ideal R) (A : Type v) :
    IsAdicComplete I
      (AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
        (⨁ _ : A, AdicCompletion I R)) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  letI : IsNoetherianRing Rhat :=
    (adicCompletion_isNoetherian_and_isAdicComplete (I := I) I.fg_of_isNoetherianRing).1
  have hcompleteJ :
      IsAdicComplete J (AdicCompletion J (⨁ _ : A, Rhat)) :=
    AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  exact (IsAdicComplete.map_algebraMap_iff I (AdicCompletion J (⨁ _ : A, Rhat))).1 hcompleteJ

/-- Helper for Lemma 15.27.2: the raw direct sum over `R` maps into the completed direct sum over
`R^` by sending each summand through `R → R^` and then into the `J`-adic completion. -/
private noncomputable def original_completion_to_completed_directSum_raw
    (I : Ideal R) (A : Type v) :
    (⨁ _ : A, R) →ₗ[R]
      AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
        (⨁ _ : A, AdicCompletion I R) :=
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  ((AdicCompletion.of J (⨁ _ : A, Rhat)).restrictScalars R).comp
    (DirectSum.lmap fun _ : A ↦ AdicCompletion.of I R)

/-- Helper for Lemma 15.27.2: the completion over `R^` maps back to the original completion by the
canonical direct-sum map from the completed coordinates. -/
private noncomputable def completed_directSum_to_original_completion_over_completion
    (I : Ideal R) (A : Type v) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    AdicCompletion J (⨁ _ : A, AdicCompletion I R) →ₗ[AdicCompletion I R]
      AdicCompletion I (⨁ _ : A, R) :=
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  letI : IsAdicComplete J (AdicCompletion I (⨁ _ : A, R)) :=
    original_completion_isAdicComplete (R := R) I A
  AdicCompletion.mapToComplete J (AdicCompletion.sum I (fun _ : A ↦ R))

/-- Helper for Lemma 15.27.2: the completion over `R^` maps back to the original completion by the
canonical direct-sum map from the completed coordinates, viewed after restricting scalars to `R`.
-/
private noncomputable def completed_directSum_to_original_completion
    (I : Ideal R) (A : Type v) :
    AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
      (⨁ _ : A, AdicCompletion I R) →ₗ[R]
        AdicCompletion I (⨁ _ : A, R) :=
  (completed_directSum_to_original_completion_over_completion (R := R) I A).restrictScalars R

/-- Helper for Lemma 15.27.2: the original completion maps to the completion over `R^` by
extending the coordinatewise inclusion of the raw direct sum. -/
private noncomputable def original_completion_to_completed_directSum
    (I : Ideal R) (A : Type v) :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R]
      AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
        (⨁ _ : A, AdicCompletion I R) :=
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  letI :
      IsAdicComplete I (AdicCompletion J (⨁ _ : A, Rhat)) :=
    completed_directSum_isAdicComplete_restrictScalars (R := R) I A
  AdicCompletion.mapToComplete I (original_completion_to_completed_directSum_raw (R := R) I A)

/-- Helper for Lemma 15.27.2: summing the completed coordinates after inserting each raw summand
through `R → R^` recovers the canonical dense map into the original completion. -/
private theorem completed_directSum_to_original_completion_raw
    (I : Ideal R) (A : Type v) :
    (((AdicCompletion.sum I (fun _ : A ↦ R)).restrictScalars R).comp
      (DirectSum.lmap fun _ : A ↦ AdicCompletion.of I R)) =
        AdicCompletion.of I (⨁ _ : A, R) := by
  -- Compare the two direct-sum maps by induction on the finitely supported input.
  ext x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro a r
    -- On one summand, `sum` is defined by the corresponding completed inclusion.
    simp [AdicCompletion.sum, LinearMap.comp_apply, DirectSum.toModule_lof]
  · intro y z hy hz
    -- Both maps are linear, so additivity closes the induction.
    simp [hy, hz]

/-- Helper for Lemma 15.27.2: on one raw basis vector, the coordinatewise inclusion agrees with
first completing the coefficient and then inserting it into the matching `R^`-summand. -/
private theorem original_completion_to_completed_directSum_raw_comp_lof
    (I : Ideal R) (A : Type v) (a : A) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    (original_completion_to_completed_directSum_raw (R := R) I A).comp
      (DirectSum.lof R A (fun _ : A ↦ R) a) =
        (((AdicCompletion.of J (⨁ _ : A, Rhat)).restrictScalars R).comp
          (((DirectSum.lof Rhat A (fun _ : A ↦ Rhat) a).restrictScalars R).comp
            (AdicCompletion.of I R))) := by
  -- Unfold the coordinatewise inclusion and evaluate on one basis vector.
  ext r
  simp [original_completion_to_completed_directSum_raw, LinearMap.comp_apply]

/-- Helper for Lemma 15.27.2: after moving one completed coordinate into the original completion,
the reverse comparison map sends it back to the matching basis vector in the completed direct sum
over `R^`. -/
private theorem original_completion_to_completed_directSum_map_lof
    (I : Ideal R) (A : Type v) (a : A) (xhat : AdicCompletion I R) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    original_completion_to_completed_directSum (R := R) I A
        (AdicCompletion.map I (DirectSum.lof R A (fun _ : A ↦ R) a) xhat) =
      AdicCompletion.of J (⨁ _ : A, Rhat)
        (DirectSum.of (fun _ : A ↦ Rhat) a xhat) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  let N := ⨁ _ : A, Rhat
  let Nhat := AdicCompletion J N
  letI : IsAdicComplete I Nhat :=
    completed_directSum_isAdicComplete_restrictScalars (R := R) I A
  -- Apply `ofLinearEquiv` so the goal becomes a calculation with `AdicCompletion.map`.
  apply (AdicCompletion.ofLinearEquiv I Nhat).injective
  change (AdicCompletion.map I (original_completion_to_completed_directSum_raw (R := R) I A))
      (AdicCompletion.map I (DirectSum.lof R A (fun _ : A ↦ R) a) xhat) =
    AdicCompletion.of I Nhat
      (AdicCompletion.of J N (DirectSum.of (fun _ : A ↦ Rhat) a xhat))
  -- Rewrite the completed map through the raw basis-vector factorization.
  rw [← AdicCompletion.map_comp]
  rw [original_completion_to_completed_directSum_raw_comp_lof (R := R) (I := I) (A := A) a]
  rw [← AdicCompletion.map_comp, ← AdicCompletion.map_comp]
  simp [LinearMap.comp_apply]

/-- Helper for Lemma 15.27.2: the forward and backward comparison maps already agree with the
identity on the dense image of the original direct sum. -/
private theorem completed_original_comparison_comp_of
    (I : Ideal R) (A : Type v) (x : ⨁ _ : A, R) :
    completed_directSum_to_original_completion (R := R) I A
      (original_completion_to_completed_directSum (R := R) I A
        (AdicCompletion.of I (⨁ _ : A, R) x)) =
      AdicCompletion.of I (⨁ _ : A, R) x := by
  -- Unfold both extensions and reduce to the raw direct-sum identity proved above.
  simp [completed_directSum_to_original_completion, original_completion_to_completed_directSum,
    original_completion_to_completed_directSum_raw, LinearMap.comp_apply,
    completed_directSum_to_original_completion_raw]

/-- Helper for Lemma 15.27.2: the comparison maps also agree with the identity on the dense image
of the completed direct sum over `R^`. -/
private theorem original_completed_comparison_comp_of
    (I : Ideal R) (A : Type v)
    (x : ⨁ _ : A, AdicCompletion I R) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    original_completion_to_completed_directSum (R := R) I A
      (completed_directSum_to_original_completion (R := R) I A
        (AdicCompletion.of J (⨁ _ : A, Rhat) x)) =
      AdicCompletion.of J (⨁ _ : A, Rhat) x := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  -- Reduce to the one-summand calculation and then close by direct-sum induction.
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp [completed_directSum_to_original_completion, original_completion_to_completed_directSum]
  · intro a xhat
    simpa [completed_directSum_to_original_completion, LinearMap.comp_apply,
      AdicCompletion.sum, DirectSum.toModule_lof] using
      original_completion_to_completed_directSum_map_lof (R := R) (I := I) (A := A) a xhat
  · intro y z hy hz
    simp [hy, hz]

/-- Helper for Lemma 15.27.2: a linear map out of an adic completion into an adically complete
target is determined by its composite with the canonical dense map `AdicCompletion.of`. -/
private theorem complete_linearMap_ext_of
    {S : Type u} [CommRing S] {K : Ideal S}
    {N Q : Type v} [AddCommGroup N] [Module S N] [AddCommGroup Q] [Module S Q]
    [IsAdicComplete K Q]
    {f g : AdicCompletion K N →ₗ[S] Q}
    (hfg : f.comp (AdicCompletion.of K N) = g.comp (AdicCompletion.of K N)) :
    f = g := by
  -- Compare both maps after re-embedding the complete target into its completion.
  have hcomp :
      (AdicCompletion.of K Q).comp f = (AdicCompletion.of K Q).comp g := by
    -- `map_ext''` reduces equality on the completion to equality on the dense image.
    apply AdicCompletion.map_ext''
    simpa [LinearMap.comp_assoc, LinearMap.comp_apply] using
      congrArg (fun u ↦ (AdicCompletion.of K Q).comp u) hfg
  -- The re-embedding `Q → Q^` is injective because `Q` is already complete.
  ext x
  exact ((AdicCompletion.ofLinearEquiv K Q).symm.injective
    (LinearMap.congr_fun hcomp x))

/-- Helper for Lemma 15.27.2: if the target is annihilated by a power of the ideal, agreement on
the dense image of `AdicCompletion.of` still determines a map out of the completion. -/
private theorem completion_map_to_pow_torsion_ext_of
    {S : Type u} [CommRing S] {K : Ideal S}
    {N Q : Type v} [AddCommGroup N] [Module S N] [AddCommGroup Q] [Module S Q]
    {c : ℕ} (hc : K ^ c • (⊤ : Submodule S Q) = ⊥)
    {f g : AdicCompletion K N →ₗ[S] Q}
    (hfg : f.comp (AdicCompletion.of K N) = g.comp (AdicCompletion.of K N)) :
    f = g := by
  -- A `K^c`-torsion target is already `K`-adically complete, so the dense-image extensionality
  -- lemma applies without further transport.
  letI : IsAdicComplete K Q := isAdicComplete_of_pow_smul_top_eq_bot (I := K) c hc
  exact complete_linearMap_ext_of (K := K) hfg

/-- Helper for Lemma 15.27.2: if two endomorphisms of the completed direct sum agree after every
finite-stage evaluation map `evalₐ`, then they agree everywhere. -/
private theorem completion_endomorphism_eq_of_eval
    (I : Ideal R) (A : Type v)
    {f g :
      AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
          (⨁ _ : A, AdicCompletion I R) →ₗ[R]
        AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
          (⨁ _ : A, AdicCompletion I R)}
    (hfg :
      ∀ n : ℕ,
        ((AdicCompletion.evalₐ
            (I.map (algebraMap R (AdicCompletion I R))) n).toLinearMap).comp f =
          ((AdicCompletion.evalₐ
            (I.map (algebraMap R (AdicCompletion I R))) n).toLinearMap).comp g) :
    f = g := by
  ext x
  -- Route correction: the completed-side identity is reconstructed from all quotient stages,
  -- rather than from a missing global `R^`-linear extensionality principle.
  apply AdicCompletion.ext_evalₐ (I := I.map (algebraMap R (AdicCompletion I R)))
  intro n
  -- Evaluate the assumed equality of stagewise composites at the chosen completion point.
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun (hfg n) x

/-- Helper for Lemma 15.27.2: the comparison from the original completion to the completed direct
sum over `R^` and back is the identity. -/
private theorem completed_original_comparison_eq_id
    (I : Ideal R) (A : Type v) :
    (completed_directSum_to_original_completion (R := R) I A).comp
        (original_completion_to_completed_directSum (R := R) I A) =
      LinearMap.id := by
  -- Both endomorphisms agree on the dense image of the raw direct sum.
  apply complete_linearMap_ext_of (K := I)
  ext x
  simpa [LinearMap.comp_assoc, LinearMap.comp_apply] using
    completed_original_comparison_comp_of (R := R) (I := I) (A := A) x

/-- Helper for Lemma 15.27.2: on the completed-base-ring side, the reverse comparison followed by
the forward comparison is also the identity. -/
private theorem original_completed_comparison_eval_stage_of
    (I : Ideal R) (A : Type v) (n : ℕ)
    (x : ⨁ _ : A, AdicCompletion I R) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    let N := ⨁ _ : A, Rhat
    let φ :
        AdicCompletion J N →ₗ[R] AdicCompletion J N :=
      (original_completion_to_completed_directSum (R := R) I A).comp
        (completed_directSum_to_original_completion (R := R) I A)
    AdicCompletion.evalₐ J n (φ (AdicCompletion.of J N x)) =
      AdicCompletion.evalₐ J n (AdicCompletion.of J N x) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  let N := ⨁ _ : A, Rhat
  let φ :
      AdicCompletion J N →ₗ[R] AdicCompletion J N :=
    (original_completion_to_completed_directSum (R := R) I A).comp
      (completed_directSum_to_original_completion (R := R) I A)
  -- Package the dense-image identity into the exact finite-stage quotient equality.
  simpa [φ] using
    congrArg (AdicCompletion.evalₐ J n)
      (original_completed_comparison_comp_of (R := R) (I := I) (A := A) x)

/-- Helper for Lemma 15.27.2: the same stagewise identity holds on arbitrary Cauchy-sequence
representatives of the completed direct sum over `R^`. -/
private theorem original_completed_comparison_eval_stage_mk_to_of_stage
    (I : Ideal R) (A : Type v) (n : ℕ)
    (f :
      AdicCompletion.AdicCauchySequence
        (I.map (algebraMap R (AdicCompletion I R)))
        (⨁ _ : A, AdicCompletion I R)) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    let N := ⨁ _ : A, Rhat
    let φ :
        AdicCompletion J N →ₗ[R] AdicCompletion J N :=
      (original_completion_to_completed_directSum (R := R) I A).comp
        (completed_directSum_to_original_completion (R := R) I A)
    AdicCompletion.evalₐ J n (φ (AdicCompletion.mk J N f)) =
      AdicCompletion.evalₐ J n (φ (AdicCompletion.of J N (f n))) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  let N := ⨁ _ : A, Rhat
  let φ :
      AdicCompletion J N →ₗ[R] AdicCompletion J N :=
    (original_completion_to_completed_directSum (R := R) I A).comp
      (completed_directSum_to_original_completion (R := R) I A)
  -- Unfold both completion extensions and normalize the stage-`n` value on the representative.
  -- After `map_mk` and `evalₐ_mk`, both sides become the same quotient class of `f n`.
  simp only [φ, original_completion_to_completed_directSum,
    completed_directSum_to_original_completion, completed_directSum_to_original_completion_over_completion,
    AdicCompletion.mapToComplete, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AdicCompletion.map_mk, AdicCompletion.map_of, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_of]

/-- Helper for Lemma 15.27.2: the same stagewise identity holds on arbitrary Cauchy-sequence
representatives of the completed direct sum over `R^`. -/
private theorem original_completed_comparison_eval_stage_mk
    (I : Ideal R) (A : Type v) (n : ℕ)
    (f :
      AdicCompletion.AdicCauchySequence
        (I.map (algebraMap R (AdicCompletion I R)))
        (⨁ _ : A, AdicCompletion I R)) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    let N := ⨁ _ : A, Rhat
    let φ :
        AdicCompletion J N →ₗ[R] AdicCompletion J N :=
      (original_completion_to_completed_directSum (R := R) I A).comp
        (completed_directSum_to_original_completion (R := R) I A)
    AdicCompletion.evalₐ J n (φ (AdicCompletion.mk J N f)) =
      AdicCompletion.evalₐ J n (AdicCompletion.mk J N f) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  let N := ⨁ _ : A, Rhat
  let φ :
      AdicCompletion J N →ₗ[R] AdicCompletion J N :=
    (original_completion_to_completed_directSum (R := R) I A).comp
      (completed_directSum_to_original_completion (R := R) I A)
  -- First reduce the representative-stage computation to the dense image point `of (f n)`.
  calc
    AdicCompletion.evalₐ J n (φ (AdicCompletion.mk J N f)) =
        AdicCompletion.evalₐ J n (φ (AdicCompletion.of J N (f n))) := by
          simpa [Rhat, J, N, φ] using
            original_completed_comparison_eval_stage_mk_to_of_stage
              (R := R) (I := I) (A := A) n f
    _ = AdicCompletion.evalₐ J n (AdicCompletion.of J N (f n)) := by
          simpa [Rhat, J, N, φ] using
            original_completed_comparison_eval_stage_of
              (R := R) (I := I) (A := A) n (f n)
    _ = AdicCompletion.evalₐ J n (AdicCompletion.mk J N f) := by
          simp [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_of]

private theorem original_completed_comparison_eq_id
    (I : Ideal R) (A : Type v) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    (original_completion_to_completed_directSum (R := R) I A).comp
        (completed_directSum_to_original_completion (R := R) I A) =
      (LinearMap.id :
        AdicCompletion J (⨁ _ : A, Rhat) →ₗ[R] AdicCompletion J (⨁ _ : A, Rhat)) :=
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  let N := ⨁ _ : A, Rhat
  let φ :
      AdicCompletion J N →ₗ[R] AdicCompletion J N :=
    (original_completion_to_completed_directSum (R := R) I A).comp
      (completed_directSum_to_original_completion (R := R) I A)
  -- Route correction: instead of a missing abstract uniqueness theorem, compare the composite
  -- with the identity after every finite-stage evaluation map `evalₐ`.
  suffices hφ :
      φ = (LinearMap.id : AdicCompletion J N →ₗ[R] AdicCompletion J N) by
    simpa [Rhat, J, N, φ] using hφ
  apply completion_endomorphism_eq_of_eval (R := R) (I := I) (A := A)
  intro n
  ext x
  let p : AdicCompletion J N → Prop := fun y =>
    AdicCompletion.evalₐ J n (φ y) = AdicCompletion.evalₐ J n y
  change p x
  -- Check the stagewise equality on Cauchy representatives and descend by completion induction.
  refine AdicCompletion.induction_on (I := J) (M := N) x ?_
  intro f
  simpa [p] using
    original_completed_comparison_eval_stage_mk (R := R) (I := I) (A := A) n f

/-- Helper for Lemma 15.27.2: the completion of the original direct sum is canonically identified
with the completion of the direct sum after base change to the completed ring `R^`. -/
private noncomputable def adicCompletion_directSum_baseChange_equiv
    (I : Ideal R) (A : Type v) :
    let Rhat := AdicCompletion I R
    let J : Ideal Rhat := I.map (algebraMap R Rhat)
    AdicCompletion I (⨁ _ : A, R) ≃ₗ[R]
      AdicCompletion J (⨁ _ : A, Rhat) :=
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  LinearEquiv.ofLinear
    (original_completion_to_completed_directSum (R := R) I A)
    (completed_directSum_to_original_completion (R := R) I A)
    (original_completed_comparison_eq_id (R := R) I A)
    (completed_original_comparison_eq_id (R := R) I A)

/-- Lemma 15.27.2: for a Noetherian ring `R`, ideal `I`, and set `A`, the `I`-adic completion of
the direct sum `⨁ a : A, R` is a flat `R`-module. -/
theorem adicCompletion_directSum_flat (I : Ideal R) (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := by
  let Rhat := AdicCompletion I R
  let J : Ideal Rhat := I.map (algebraMap R Rhat)
  -- First prove flatness after replacing `R` by its completion, as in the source argument.
  have hcompleted : Module.Flat Rhat (AdicCompletion J (⨁ _ : A, Rhat)) := by
    simpa [Rhat, J] using completed_directSum_flat_over_completed_ring (R := R) I A
  have hflat_alg : (algebraMap R Rhat).Flat :=
    adicCompletion_algebraMap_flat (R := R) I
  let _ : Module.Flat R Rhat := RingHom.flat_algebraMap_iff.mp hflat_alg
  let _ : Module.Flat Rhat (AdicCompletion J (⨁ _ : A, Rhat)) := hcompleted
  have hbase : Module.Flat R (AdicCompletion J (⨁ _ : A, Rhat)) := by
    -- Flatness over `R` descends from the flat completion map `R → R^`.
    simpa [Rhat, J] using Module.Flat.trans R Rhat (AdicCompletion J (⨁ _ : A, Rhat))
  let _ : Module.Flat R (AdicCompletion J (⨁ _ : A, Rhat)) := hbase
  -- Transport flatness back along the explicit comparison equivalence
  -- `AdicCompletion I (⨁ a, R) ≃ AdicCompletion J (⨁ a, R^)`.
  exact Module.Flat.of_linearEquiv (adicCompletion_directSum_baseChange_equiv (R := R) I A)

end
