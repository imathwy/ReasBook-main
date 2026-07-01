import Mathlib
import stacks_project.Chap15.Lemma_15_111_1
import stacks_project.Chap15.Lemma_15_111_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Lemma 15.111.9:
- primary domain: invariant-theoretic actions of decomposition/stabilizer groups on quotient and
  residue fields
- sampled owner declarations:
  `Algebra.IsInvariant`,
  `Ideal.Quotient.normal`,
  `Ideal.Quotient.stabilizerHom`,
  `IsFractionRing.stabilizerHom`,
  `IsFractionRing.stabilizerHom_surjective`
- best owner abstractions: the quotient-level normality theorem `Ideal.Quotient.normal` for clause
  `(1)`, and the stabilizer owner `IsFractionRing.stabilizerHom` with its canonical surjectivity
  theorem `IsFractionRing.stabilizerHom_surjective` for clause `(2)`
- primitive data: the invariant fixed-subring extension `RFix ⊆ R` together with primes
  `p ⊆ RFix`, `q ⊆ R` and the lying-over hypothesis `q.LiesOver p`
- derived API: normality of the residue-field extension and surjectivity of the decomposition-group
  action on `Aut(κ(q) / κ(p))`

Layer triage:
- `source-facing`: the textbook residue-field statement for the decomposition group over `p` and
  `q`
- `core/canonical`: `Ideal.Quotient.normal`, `IsFractionRing.stabilizerHom`, and
  `IsFractionRing.stabilizerHom_surjective`
- `bridge/view`: the fixed-subring/residue-field instances in this file realizing the source
  situation as an instance of the canonical owner theorem

The surjectivity clause is derived API from the owner theorem, so it should be expressed by direct
canonical reuse rather than by a parallel local wrapper theorem.
-/

attribute [local instance] fixedPointsSubring_smulCommClass

variable (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
variable (q : Ideal R) [q.IsPrime] [q.LiesOver p]

local notation "κp" => p.ResidueField
local notation "κq" => q.ResidueField

private noncomputable instance fixedPointsResidueFieldAlgebra :
    Algebra (RFix ⧸ p) κq :=
  ((Ideal.ResidueField.map p q (algebraMap RFix R) (Ideal.over_def q p)).comp
    (algebraMap (RFix ⧸ p) κp)).toAlgebra

-- Proof sketch: both ring homomorphisms are induced by the same inclusion `R^G ↪ R`; compare them
-- on quotient classes represented by elements of `R^G`.
private theorem fixedPointsResidueField_comp_quotient :
    algebraMap (RFix ⧸ p) κq =
      (algebraMap (R ⧸ q) κq).comp (algebraMap (RFix ⧸ p) (R ⧸ q)) := sorry

private noncomputable instance fixedPointsResidueFieldTower :
    IsScalarTower (RFix ⧸ p) κp κq :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable instance fixedPointsQuotientResidueFieldTower :
    IsScalarTower (RFix ⧸ p) (R ⧸ q) κq :=
  IsScalarTower.of_algebraMap_eq' (fixedPointsResidueField_comp_quotient p q)

-- Proof sketch: the invariant extension `R^G ⊆ R` is integral, so the induced residue field
-- extension is algebraic; normality follows from the orbit polynomial over `R^G` whose roots are
-- the conjugates `σ(a)` and whose reduction mod `q` splits in `κ(q)`.
/-- Lemma 15.111.9 (1): if `q` is a prime of `R` lying over a prime `p` of the fixed subring
`R^G`, then the residue field extension `κ(q) / κ(p)` is algebraic and normal. -/
theorem residueField_normal_of_liesOver_fixedPoints :
    Normal κp κq := sorry

-- Proof sketch: the stabilizer of `q` acts on `R / q` over `(R^G) / p`, hence on
-- `Frac(R / q) = κ(q)` over `Frac((R^G) / p) = κ(p)`. The invariant-theory surjectivity theorem for
-- stabilizers then gives every automorphism of `κ(q) / κ(p)`.
/- Lemma 15.111.9 (2): the decomposition group
`D = {σ ∈ G | σ(q) = q}` surjects onto `Aut(κ(q) / κ(p))`. In this fixed-subring setting, this is
exactly the canonical invariant-theory owner theorem
`IsFractionRing.stabilizerHom_surjective`, specialized to `A = R^G`, `B = R`, `P = p`, and
`Q = q`. -/
#check (IsFractionRing.stabilizerHom_surjective G p q κp κq :
  Function.Surjective (IsFractionRing.stabilizerHom G p q κp κq))

end
