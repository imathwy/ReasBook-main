import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_111_10

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

/-- Any maximal ideal of the integral closure of the local ring `A` lies over `maximalIdeal A`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal B) [m.IsMaximal] : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/- Domain-style sampling for Lemma 15.113.1:
- primary domain: Galois conjugacy of prime and maximal ideals in the integral closure of a local
  integrally closed domain;
- sampled owner declarations:
  `exists_gal_smul_eq_of_liesOver`,
  `MulAction.stabilizer`,
  `Ideal.LiesOver`,
  `residueField_normal_of_liesOver`;
- best owner abstraction: the chapter owner theorem `exists_gal_smul_eq_of_liesOver`, whose
  maximal-ideal specialization is exactly the source-facing local-ring statement here;
- primitive data: the integral closure `B = integralClosure A L`, two maximal ideals `m, m' : Ideal B`,
  and the canonical `LiesOver (maximalIdeal A)` facts supplied by locality;
- derived API: conjugacy of maximal ideals and the downstream residue-field transport statements in
  later files.

Source/core/bridge triage:
- `source-facing`: the local-ring maximal-ideal transitivity statement in Lemma 15.113.1;
- `core/canonical`: `exists_gal_smul_eq_of_liesOver`;
- `bridge/view`: the canonical specialization from maximal ideals of `B` to primes lying over
  `maximalIdeal A`. -/

-- Proof sketch: maximal ideals of `B` lie over `maximalIdeal A`, so this is the
-- `p = maximalIdeal A` specialization of Lemma `15.111.10 (1)`.
/-- Lemma 15.113.1: for `B = integralClosure A L`, the canonical action of `Gal(L/K)` on `B`
is transitive on the maximal ideals of `B`. -/
@[stacks 09EA]
theorem exists_gal_smul_eq_of_isMaximal
    (m m' : Ideal B) (hm : m.IsMaximal) (hm' : m'.IsMaximal) :
    ∃ σ : Gal(L/K), σ • m = m' := by
  letI : m.IsMaximal := hm
  letI : m'.IsMaximal := hm'
  exact exists_gal_smul_eq_of_liesOver p m m'

end
