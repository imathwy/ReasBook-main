import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]

local notation "B" => integralClosure A L

/- Domain-style sampling for Lemma 15.111.10:
- primary domain: Galois actions on the integral closure of an integrally closed domain and the
  induced decomposition-group action on residue fields
- sampled owner declarations:
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `Algebra.isInvariant_of_isGalois`,
  `IsFractionRing.stabilizerHom`,
  `FixedPoints.toAlgAut_surjective`
- best owner abstraction: the invariant-extension owner
  `Algebra.IsInvariant A (integralClosure A L) Gal(L/K)` together with the residue-field owner
  `IsFractionRing.stabilizerHom`
- primitive data: `B = integralClosure A L`, a prime `p : Ideal A`, and primes of `B` lying over
  `p`
- derived API: transitivity on primes above `p`, normality of the residue-field extension, and the
  decomposition-group action on `Aut(κ(q) / κ(p))`

Layer triage:
- `source-facing`: the three textbook clauses for `B = integralClosure A L`
- `core/canonical`: `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `IsFractionRing.stabilizerHom`, and the profinite/fixed-field surjectivity owner behind the
  induced residue-field action
- `bridge/view`: the quotient-to-residue-field algebra and scalar-tower instances identifying the
  integral-closure situation with those owner theorems

The decomposition-group homomorphism itself is an exact owner specialization, so the refined file
should reuse that directly rather than keep a parallel local definition. Clauses `(1)` and `(3)`
remain source-facing theorems because the finite-group owner theorems in mathlib live under
stronger assumptions than the current statement header.
-/

/-- The Galois group `Gal(L / K)` acts on `B = integralClosure A L`. -/
private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

variable (p : Ideal A) [p.IsPrime]
variable (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p]

local notation "κp" => p.ResidueField
local notation "κq" => q.ResidueField

-- The canonical map `(A ⧸ p) → κ(q)` agrees with the composite `(A ⧸ p) → B ⧸ q → κ(q)`.
-- Proof sketch: both maps are induced by the same ring map `A → integralClosure A L`; compare them
-- on quotient classes represented by elements of `A`.
private theorem integralClosureResidueFieldMap_comp_quotient :
    (Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p)).comp
        (algebraMap (A ⧸ p) κp) =
      (algebraMap (B ⧸ q) κq).comp (algebraMap (A ⧸ p) (B ⧸ q)) := sorry

/-- The residue field `κ(q)` is an `(A ⧸ p)`-algebra via the composite
`(A ⧸ p) → κ(p) → κ(q)`. -/
private noncomputable instance integralClosureQuotientResidueFieldAlgebra :
    Algebra (A ⧸ p) κq :=
  ((Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p)).comp
    (algebraMap (A ⧸ p) κp)).toAlgebra

/-- The canonical maps `(A ⧸ p) → κ(p) → κ(q)` form a scalar tower. -/
private noncomputable instance integralClosureResidueField_isScalarTower :
    IsScalarTower (A ⧸ p) κp κq :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical maps `(A ⧸ p) → (integralClosure A L) ⧸ q → κ(q)` form a scalar tower. -/
private noncomputable instance integralClosureQuotientResidueField_isScalarTower :
    IsScalarTower (A ⧸ p) (B ⧸ q) κq :=
  IsScalarTower.of_algebraMap_eq' (integralClosureResidueFieldMap_comp_quotient p q)

variable (q' : Ideal (integralClosure A L)) [q'.IsPrime] [q'.LiesOver p]

-- Proof sketch: apply the profinite invariant-theory transitivity theorem to the invariant
-- extension `A ⊆ integralClosure A L`; the hypotheses that `q` and `q'` both lie over `p`
-- identify their contractions to `A`.
/- Lemma 15.111.10 (1): if two prime ideals of the integral closure `B = integralClosure A L`
lie over the same prime ideal `p` of `A`, then some `σ ∈ Gal(L / K)` sends one to the other.
The finite-group owner theorem `Algebra.IsInvariant.exists_smul_of_under_eq` is not used as the
main entry here because the current statement header is broader. -/
theorem exists_gal_smul_eq_of_liesOver
    (p : Ideal A) (q q' : Ideal B)
    [p.IsPrime] [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] :
    ∃ σ : Gal(L/K), σ • q = q' := sorry

-- Proof sketch: apply the residue-field normality statement for invariant extensions to the
-- invariant extension `A ⊆ integralClosure A L` and the prime `q` above `p`.
/-- Lemma 15.111.10 (2): if `q` is a prime of `B = integralClosure A L` lying over the prime
`p` of `A`, then the residue field extension `κ(q) / κ(p)` is normal. -/
theorem residueField_normal_of_liesOver :
    Normal κp κq := sorry

-- Proof sketch: use the profinite invariant-theory surjectivity theorem for the stabilizer of
-- `q`, then identify the resulting map on fraction fields with the canonical owner map from the
-- decomposition group to `Aut(κ(q) / κ(p))`.
/- Lemma 15.111.10 (3): if `q` is a prime of `B = integralClosure A L` lying over the prime
`p` of `A`, then the decomposition group of `q` surjects onto `Aut(κ(q) / κ(p))`. The public
surface should stay source-facing at this generality; the finite theorem
`IsFractionRing.stabilizerHom_surjective` is only a stronger companion specialization. -/
theorem stabilizerHom_surjective_of_liesOver :
    Function.Surjective (IsFractionRing.stabilizerHom Gal(L/K) p q κp κq) := by
  sorry

end
