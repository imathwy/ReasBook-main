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
* `source-facing`: Lemma `10.98.1` says that a sequential inverse system of `A`-modules whose
  `n`th stage is annihilated by `I ^ n` has `I`-adically complete inverse limit.
* `core/canonical` owners: the inverse system owner `OrderDual ℕ+ ⥤ ModuleCat A`, the inverse
  limit owner `limit M_`, the canonical projections `limit.π`, and the adic-completeness owner
  `IsAdicComplete` together with `AdicCompletion.isAdicComplete`.
* `bridge/view`: the factorization of each projection `limit M_ → M_n` through
  `(limit M_) ⧸ I ^ n (limit M_)`, then the induced retraction
  `AdicCompletion I (limit M_) → limit M_`.

Relevant owner declarations sampled for this refinement:
* `IsAdicComplete`
* `AdicCompletion.of_bijective_iff`
* `AdicCompletion.isAdicComplete`
* `CategoryTheory.Limits.limit.π`

Primitive data are only the inverse system `M_` and the stagewise annihilation hypothesis `I^n M_n
= 0`; the inverse limit module and its projections are canonical derived API from `limit M_`. -/

-- Proof sketch: for each positive integer `n`, the projection `M := lim M_n → M_n` factors through
-- `M ⧸ I ^ n M` because `I ^ n M_n = 0`. Passing to the inverse limit of these factorizations gives
-- a retraction `AdicCompletion I M → M` of the canonical map `M → AdicCompletion I M`. Since
-- `AdicCompletion I M` is `I`-adically complete by Lemma `10.96.3`, the retract `M` is also
-- `I`-adically complete.
/-- Lemma 10.98.1: if `I` is a finitely generated ideal and `(M_n)` is an inverse system of
`A`-modules over `ℕ+` with `I ^ n M_n = 0` for every stage `n`, then the inverse limit
`\varprojlim M_n` is `I`-adically complete. -/
theorem isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    IsAdicComplete I (limit M_ : ModuleCat A) := sorry

end
