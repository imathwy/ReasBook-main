import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_91_3
import StacksProject_2024.Chap10.Lemma_10_96_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open AdicCompletion
open LinearMap

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (A : Type v)

/- Domain triage:
- primary domain: adic completion functoriality and universal injectivity of linear maps;
- sampled owner declarations of the same kind:
  `mapToComplete` and `mapToComplete_comp_of` from the completion bridge API,
  `AdicCompletion.Families.pi` and `LinearEquiv.piCongrRight` for the canonical product
  comparison,
  the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  and the owner flatness theorem `Module.noetherian_pi_flat_and_mittagLeffler`;
- primitive data: the ideal `I`, the index type `A`, and the direct-sum inclusion
  `DirectSum.coeFnLinearMap R`;
- source/core/bridge triage:
  `source-facing`: the universally injective comparison map from the completed direct sum to the
  product `A → R`;
  `core/canonical`: the owner predicate `LinearMap.UniversallyInjective`;
  `bridge/view`: the canonical comparison is the composite of
  `AdicCompletion.map I (DirectSum.coeFnLinearMap R)`,
  `AdicCompletion.Families.pi I (fun _ : A ↦ R)`,
  and the pointwise completion equivalence
  `LinearEquiv.piCongrRight (fun _ : A ↦ (AdicCompletion.ofLinearEquiv I R).symm)`.
-/
variable [IsAdicComplete I R]

/-- The canonical map from the completed direct sum `AdicCompletion I (⨁ a, R)` to the product
`A → R`, obtained by functoriality of completion followed by the coordinatewise identification of
the completion of a product with the product of the completed coordinates. -/
noncomputable abbrev adicCompletionDirectSumToPi :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] A → R :=
  ((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
    (((AdicCompletion.pi I (fun _ : A ↦ R)).restrictScalars R).comp
      ((map I (DirectSum.coeFnLinearMap R)).restrictScalars R))

@[simp]
theorem adicCompletionDirectSumToPi_of (x : ⨁ _ : A, R) :
    adicCompletionDirectSumToPi I A (of I (⨁ _ : A, R) x) = DirectSum.coeFnLinearMap R x := by
  ext a
  change (ofLinearEquiv I R).symm
      (map I (LinearMap.proj a) ((map I (DirectSum.coeFnLinearMap R)) (of I (⨁ _ : A, R) x))) =
    x a
  rw [map_of, map_of, ofLinearEquiv_symm_of]
  rfl

@[simp]
theorem adicCompletionDirectSumToPi_comp_of :
    (adicCompletionDirectSumToPi I A).comp (of I (⨁ _ : A, R)) = DirectSum.coeFnLinearMap R := by
  ext x a
  rw [LinearMap.comp_apply, adicCompletionDirectSumToPi_of]

variable [IsNoetherianRing R]

-- Proof sketch: the product module `A → R` is flat by `Module.noetherian_pi_flat_and_mittagLeffler`,
-- so the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal` reduces
-- the goal to injectivity modulo finitely generated ideals. For such an ideal, test after
-- tensoring with the finite quotient module, use completion exactness together with Artin-Rees to
-- control lifts through the completed direct sum, and identify the resulting comparison map with
-- the coordinatewise inclusion via the canonical computation
-- `adicCompletionDirectSumToPi_comp_of I A`.
/-- Lemma 15.27.1: if `R` is Noetherian and `I`-adically complete, then the canonical map from the
`I`-adic completion of `⨁ a, R` to the product `∀ a, R` is universally injective. -/
theorem adicCompletionDirectSumToPi_universallyInjective :
    (adicCompletionDirectSumToPi I A).UniversallyInjective := by
  letI : Module.Flat R (A → R) :=
    (Module.noetherian_pi_flat_and_mittagLeffler : _
      ∧ Module.MittagLeffler R (A → R)).1
  refine (universallyInjective_iff_injective_mod_finite_ideal
    (adicCompletionDirectSumToPi I A)).2 ?_
  intro J hJ
  sorry

end
