import Mathlib
import stacks_project.Chap10.Lemma_10_69_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory
open Ideal

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- 
Domain triage:
* primary domain: quasi-regular sequences and quotients by the `J`-adic intersection in
  commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`,
  `Ideal.iInf_pow_eq_bot_of_isLocalRing`,
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`;
* core/canonical owner abstractions: `IsQuasiRegular` for the source-facing sequence predicate and
  the raw infimum expressions `⨅ n, J ^ n` and `⨅ n, J ^ n • ⊤` for the `J`-adic intersection;
* primitive vs derived split: the ideal `⨅ n, J ^ n` and submodule `⨅ n, J ^ n • ⊤` are primitive
  canonical data, while the quotient module structure and the quotient invariance statement are
  derived API.
-/

/-- The quotient module by `⋂ n, J^n M` carries the canonical action of the quotient ring by
`⋂ n, J^n`. -/
private instance (J : Ideal R) :
    Module (R ⧸ (⨅ n : ℕ, (J ^ n : Ideal R)))
      (M ⧸ (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M))) := by
  let K : Ideal R := ⨅ n : ℕ, J ^ n
  have hK :
      Module.IsTorsionBySet R
        (M ⧸ (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M)))
        (K : Set R) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x r hr
    change r ∈ (⨅ n : ℕ, (J ^ n : Ideal R)) at hr
    rw [Submodule.mem_iInf]
    intro n
    exact Submodule.smul_mem_smul ((iInf_le (fun n : ℕ ↦ J ^ n) n) hr) (by simp)
  change Module (R ⧸ K) (M ⧸ (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M)))
  exact Module.IsTorsionBySet.module hK

-- Proof sketch: compare the homogeneous-coefficient definition of quasi-regularity before and
-- after passing to the quotients by `⋂ n, J ^ n` and `⋂ n, J ^ n M`. The graded pieces are
-- unchanged because for every `n` there is a canonical isomorphism
-- `J ^ n • ⊤ / J ^ (n + 1) • ⊤ ≃ₗ[R] (J̄ ^ n • ⊤) / (J̄ ^ (n + 1) • ⊤)`, so the coefficient
-- criterion is equivalent on the two sides.
/-- Lemma 10.69.9: a finite sequence in a commutative ring is `M`-quasi-regular if and only if
its image in the quotient ring by `⋂ n, J ^ n`, where `J = Ideal.ofList rs`, is
quasi-regular on the corresponding quotient module. -/
theorem isQuasiRegular_iff_quotient_iInf_pow {rs : List R} :
    IsQuasiRegular M rs ↔
      IsQuasiRegular
        (M ⧸ (⨅ n : ℕ, (ofList rs) ^ n • (⊤ : Submodule R M)))
        (rs.map (Ideal.Quotient.mk (⨅ n : ℕ, ((ofList rs) ^ n : Ideal R)))) :=
  sorry

end RingTheory.Sequence
