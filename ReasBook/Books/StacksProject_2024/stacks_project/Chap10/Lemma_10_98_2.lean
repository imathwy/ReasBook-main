import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A

/- Domain triage:
* `source-facing`: Lemma `10.98.2` studies a sequential inverse system of `A`-modules whose
  transition kernels are exactly the ideal-power submodules `I ^ n M_{n + 1}`, and concludes that
  each canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` identifies with `M_n`.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its stages `M_.obj (OrderDual.toDual n)`, the canonical projections `limit.π`, the quotient
  equivalence API `LinearMap.quotKerEquivOfSurjective` and `Submodule.quotEquivOfEq`, and the
  owner predicate `IsAdicComplete`.
* `bridge/view`: the lower-level surjectivity and kernel calculation for the canonical projection
  `lim M_ → M_n` are companion ingredients used only to build the canonical quotient equivalence.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.Limits.limit.π`
* `IsAdicComplete`
* `isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot`
* the inverse-limit comparison pattern in `Lemma_10_98_4`

Primitive data are only the inverse system `M_` and the source hypotheses on its transition maps.
The stages, limit module, and limit projections are canonical derived API from that owner, so the
public statement keeps the stagewise surjectivity and kernel-identification hypotheses explicit
instead of packaging them into a second owner predicate. -/

private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

private abbrev stageMap (M_ : ModuleInverseSystem) (n : ℕ+) :
    M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  (M_.map (homOfLE (pnat_le_succ n))).hom

private abbrev limitProjection (M_ : ModuleInverseSystem) (n : ℕ+) :
    (limit M_ : ModuleCat A) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  (limit.π M_ (OrderDual.toDual n)).hom

-- Proof sketch: apply Lemma `10.98.1` to get that the inverse limit is `I`-adically complete,
-- use the surjective transition maps to obtain surjective limit projections, and compare the
-- kernels of `M → M_n` with `I^n M` via the inverse system of short exact sequences from the
-- textbook argument.
private theorem inverseLimitProjection_surjective_and_ker_eq_pow_smul_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    ∀ n : ℕ+,
      Function.Surjective (limitProjection M_ n) ∧
        LinearMap.ker (limitProjection M_ n) =
          I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)) := sorry

/-- Lemma 10.98.2: if a sequential inverse system of `A`-modules has transition maps
`M_{n + 1} → M_n` that are surjective with kernel `I^n M_{n + 1}`, then for every `n` the
canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` is linearly equivalent to the `n`th
stage. -/
abbrev inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ((limit M_ : ModuleCat A) ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))) ≃ₗ[A]
      M_.obj (OrderDual.toDual n) :=
  let hπ :=
    inverseLimitProjection_surjective_and_ker_eq_pow_smul_of_successive_ideal_power_quotients
      I hI M_ hSurj hKer n
  (Submodule.quotEquivOfEq
      (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))
      (LinearMap.ker (limitProjection M_ n))
      hπ.2.symm).trans
    ((limitProjection M_ n).quotKerEquivOfSurjective hπ.1)

-- Proof sketch: unfold the quotient equivalence into the kernel-identification equivalence followed
-- by the first isomorphism theorem for the surjective projection `lim M_ → M_n`, then apply the
-- corresponding `quotKerEquivOfSurjective_apply_mk` computation rule.
/-- The quotient equivalence of Lemma `10.98.2` sends the class of an inverse-limit element to its
`n`th stage projection. -/
theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_apply_mk
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) (x : (limit M_ : ModuleCat A)) :
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer n (Submodule.Quotient.mk x) =
      limitProjection M_ n x := sorry

-- Proof sketch: the kernel computation implies `I^n M_n = 0` for every stage, so Lemma `10.98.1`
-- applies directly to the inverse system `M_`.
/-- The inverse limit of a sequential system with successive quotients `M_n = M_{n + 1} / I^n
M_{n + 1}` is `I`-adically complete. -/
theorem isAdicComplete_inverseLimit_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    IsAdicComplete I (limit M_ : ModuleCat A) := sorry

end
