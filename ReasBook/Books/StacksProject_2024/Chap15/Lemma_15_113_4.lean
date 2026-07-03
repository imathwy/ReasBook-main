import Mathlib
import stacks_project.Chap15.Lemma_15_111_10

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
local notation "κA" => Ideal.ResidueField p

/-- The Galois group acts on the integral closure through the induced automorphisms of the ambient
field. -/
private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

/- Domain-style sampling for Lemma 15.113.4:
- primary domain: residue-field extensions and decomposition groups for maximal ideals of the
  integral closure in a Galois extension of fraction fields;
- sampled owner declarations:
  `Ideal.LiesOver`,
  `Ideal.ResidueField.map`,
  `residueField_normal_of_liesOver`,
  `stabilizerHom_surjective_of_liesOver`,
  `IsFractionRing.stabilizerHom`;
- best owner abstraction: the canonical owner map `IsFractionRing.stabilizerHom`, with the
  source-facing prime-ideal surjectivity theorem `stabilizerHom_surjective_of_liesOver`
  supplying its maximal-ideal specialization once the local integral-closure residue-field bridge
  is in place at the weaker local integrally closed-domain layer;
- primitive data: a maximal ideal `m : Ideal B`;
- derived API: the induced residue-field extension `κ(m) / κA`, its normality, and the canonical
  decomposition-group action on the residue field. -/

/- Source/core/bridge triage:
- `source-facing`: the five clauses of Lemma 15.113.4 for maximal ideals of `B`;
- `core/canonical`: `Ideal.LiesOver`, `residueField_normal_of_liesOver`, and
  `IsFractionRing.stabilizerHom` together with the prime-ideal surjectivity theorem from
  Lemma `15.111.10` and its maximal-ideal specialization;
- `bridge/view`: the maximal-ideal specialization of the residue-field bridge instances and
  source-facing theorems from Lemma `15.111.10`. -/

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {L : Type v} [Field L] [Algebra A L]

/- Any maximal ideal of the integral closure of the local ring `A` lies over `maximalIdeal A`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

end

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "ρ" => IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField

-- Proof sketch: this is the `p = maximalIdeal A`, `q = m` specialization of the prime-ideal
-- normality theorem from Lemma `15.111.10`.
/- Lemma 15.113.4 (1): for a maximal ideal `m` of `integralClosure A L`, the residue field
extension `κ(m) / κA` is normal. This is exactly the `p = maximalIdeal A`, `q = m`
specialization of `residueField_normal_of_liesOver`. -/
#check (residueField_normal_of_liesOver p m : Normal κA m.ResidueField)

/- Lemma 15.113.4 (2): the decomposition group `D = stabilizer Gal(L / K) m` surjects onto
`Aut(κ(m) / κA)`. This is exactly the `p = maximalIdeal A`, `q = m` specialization of the
source-facing prime-ideal surjectivity theorem from Lemma `15.111.10`. -/
#check (IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField :
  D →* (m.ResidueField ≃ₐ[κA] m.ResidueField))
#check (stabilizerHom_surjective_of_liesOver p m : Function.Surjective ρ)

-- Proof sketch: maximal ideals of `B` are conjugate by Lemma `15.113.1`; transport the residue
-- field extension along the induced algebra equivalence and use invariance of separability under
-- base-field algebra equivalence.
/-- Lemma 15.113.4 (3): for any two maximal ideals `m` and `m'` of `integralClosure A L`, the
residue field extensions over `κA` are simultaneously separable. This is the formalized
`some (equivalently all)` clause. -/
theorem residueField_separable_iff_of_isMaximal
    (m' : Ideal (integralClosure A L)) [m'.IsMaximal] :
    Algebra.IsSeparable κA m.ResidueField ↔ Algebra.IsSeparable κA m'.ResidueField := sorry

-- Proof sketch: combine `residueField_normal_of_liesOver p m` with the assumed separability of
-- `κ(m) / κA`; the canonical field-theoretic owner `isGalois_iff` packages exactly this
-- conjunction.
/-- Lemma 15.113.4 (4): if `κ(m) / κA` is separable, then it is Galois. -/
theorem residueField_isGalois_of_separable
    (hsep : Algebra.IsSeparable κA m.ResidueField) :
    IsGalois κA m.ResidueField := by
  exact isGalois_iff.mpr ⟨hsep, residueField_normal_of_liesOver p m⟩

/- Lemma 15.113.4 (5): after clause `(4)`, the target group may be read as
`Gal(κ(m) / κA)`, but the canonical map and its surjectivity statement are exactly those of
clause `(2)`. -/
#check (IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField :
  D →* Gal(m.ResidueField/κA))
#check (stabilizerHom_surjective_of_liesOver p m : Function.Surjective ρ)

end
