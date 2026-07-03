import Mathlib
import stacks_project.Chap15.Lemma_15_113_5
import stacks_project.Chap15.Lemma_15_113_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open Ideal IsLocalRing Algebra IntermediateField

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

/-- The Galois group acts on the integral closure through the induced automorphisms of the ambient
field. -/
private instance integralClosureMulSemiringActionRemark :
    MulSemiringAction G B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass G A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B G := sorry

attribute [local instance] integralClosure_isInvariant

/- Domain-style sampling for Remark 15.113.9:
- primary domain: fixed subalgebras and fixed fields attached to the wild inertia, inertia, and
  decomposition subgroups of a maximal ideal in a finite Galois extension of fraction fields of a
  discrete valuation ring, together with the contracted primes and their residue-field /
  ramification behavior;
- sampled owner declarations:
  `FixedPoints.subalgebra`,
  `IntermediateField.fixedField`,
  `wildInertiaSubgroup`,
  `tameInertiaQuotient`,
  `fixedSubalgebra_isIntegralClosure`,
  `inertiaFixedSubalgebra_isEtaleAt_under`,
  `Ideal.ResidueField.map`,
  `Ideal.ramificationIdx`;
- best owner abstraction: the fixed-object owners `FixedPoints.subalgebra A B H` and
  `IntermediateField.fixedField H` for `H = P, I, D`; the tower maps between the fixed subalgebras
  and fixed fields are derived from subgroup inclusions `P ≤ I ≤ D`, not primitive data;
- primitive data: the subgroup owners `P`, `I`, `D`, their fixed subalgebras `B^P`, `B^I`, `B^D`,
  and their fixed fields `L^P`, `L^I`, `L^D`;
- derived API: the inclusion algebras along the tower, the contracted ideals
  `m^P`, `m^I`, `m^D`, the induced residue-field maps, and the local étale / ramification /
  separability conclusions.

Layer triage:
- `source-facing`: the fifteen clauses of the Stacks remark about the full chain
  `P ⊂ I ⊂ D`, especially the `B^P` unique-prime and residue-field / ramification statements;
- `core/canonical`: `FixedPoints.subalgebra`, `IntermediateField.fixedField`,
  `wildInertiaSubgroup`, `tameInertiaQuotient`, `Ideal.under`, `Ideal.ResidueField.map`, and
  `Ideal.ramificationIdx`;
- `bridge/view`: the canonical inclusions `B^D ⊆ B^I ⊆ B^P ⊆ B` and the corresponding residue
  field maps.

Primitive-vs-derived split:
- primitive public data in this file: none beyond the source-facing subgroup/fixed-object owners
  already established earlier in the chapter;
- derived public API in this file: the source-facing consequences for the tower
  `B^D ⊆ B^I ⊆ B^P ⊆ B`, keeping exact-interface recall when an upstream chapter theorem already
  has the desired statement. -/

private theorem fixedSubalgebra_le_of_le {H H' : Subgroup G} (h : H ≤ H') :
    FixedPoints.subalgebra A B H' ≤ FixedPoints.subalgebra A B H := by
  intro x hx g
  exact hx ⟨g.1, h g.2⟩

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer G m
local notation "I" => m.inertia G
local notation "P" => wildInertiaSubgroup K m
local notation "I_t" => tameInertiaQuotient K m

local notation "B[D]" => FixedPoints.subalgebra A B D
local notation "B[I]" => FixedPoints.subalgebra A B I
local notation "B[P]" => FixedPoints.subalgebra A B P

local notation "L[D]" => IntermediateField.fixedField D
local notation "L[I]" => IntermediateField.fixedField I
local notation "L[P]" => IntermediateField.fixedField P

local notation "mD" => m.under B[D]
local notation "mI" => m.under B[I]
local notation "mP" => m.under B[P]

local notation "κD" => Ideal.ResidueField mD
local notation "κI" => Ideal.ResidueField mI
local notation "κP" => Ideal.ResidueField mP

local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

noncomputable instance decompositionToInertiaFixedSubalgebraAlgebra :
    Algebra B[D] B[I] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedSubalgebraAlgebra :
    Algebra B[I] B[P] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedSubalgebraAlgebra :
    Algebra B[D] B[P] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

noncomputable instance decompositionToInertiaFixedFieldAlgebra :
    Algebra L[D] L[I] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedFieldAlgebra :
    Algebra L[I] L[P] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedFieldAlgebra :
    Algebra L[D] L[P] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

theorem under_decomposition_over_base :
    p = Ideal.comap (algebraMap A B[D]) mD := by
  change p = Ideal.comap ((algebraMap B[D] B).comp (algebraMap A B[D])) m
  simpa using (Ideal.over_def m p)

omit [m.IsMaximal] in
theorem under_inertia_over_decomposition :
    mD = Ideal.comap (algebraMap B[D] B[I]) mI := by
  change Ideal.comap (algebraMap B[D] B) m =
    Ideal.comap ((algebraMap B[I] B).comp (algebraMap B[D] B[I])) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_inertia :
    mI = Ideal.comap (algebraMap B[I] B[P]) mP := by
  change Ideal.comap (algebraMap B[I] B) m =
    Ideal.comap ((algebraMap B[P] B).comp (algebraMap B[I] B[P])) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_decomposition :
    mD = Ideal.comap (algebraMap B[D] B[P]) mP := by
  change Ideal.comap (algebraMap B[D] B) m =
    Ideal.comap ((algebraMap B[P] B).comp (algebraMap B[D] B[P])) m
  rfl

theorem under_wildInertia_over_base :
    p = Ideal.comap (algebraMap A B[P]) mP := by
  change p = Ideal.comap ((algebraMap B[P] B).comp (algebraMap A B[P])) m
  simpa using (Ideal.over_def m p)

noncomputable instance baseToDecompositionResidueFieldAlgebra :
    Algebra κA κD :=
  (Ideal.ResidueField.map p mD (algebraMap A B[D]) (under_decomposition_over_base m)).toAlgebra

noncomputable instance decompositionToInertiaResidueFieldAlgebra :
    Algebra κD κI :=
  (Ideal.ResidueField.map mD mI (algebraMap B[D] B[I])
      (under_inertia_over_decomposition m)).toAlgebra

noncomputable instance inertiaToWildInertiaResidueFieldAlgebra :
    Algebra κI κP :=
  (Ideal.ResidueField.map mI mP (algebraMap B[I] B[P])
      (under_wildInertia_over_inertia m)).toAlgebra

noncomputable instance decompositionToWildInertiaResidueFieldAlgebra :
    Algebra κD κP :=
  (Ideal.ResidueField.map mD mP (algebraMap B[D] B[P])
      (under_wildInertia_over_decomposition m)).toAlgebra

noncomputable instance baseToWildInertiaResidueFieldAlgebra :
    Algebra κA κP :=
  (Ideal.ResidueField.map p mP (algebraMap A B[P]) (under_wildInertia_over_base m)).toAlgebra

omit [m.IsMaximal] in
private instance inertiaContractedIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver mI mD :=
  ⟨(under_inertia_over_decomposition m).symm⟩

omit [m.IsMaximal] in
private instance wildInertiaContractedIdeal_liesOver_inertiaContractedIdeal :
    Ideal.LiesOver mP mI :=
  ⟨(under_wildInertia_over_inertia m).symm⟩

omit [m.IsMaximal] in
private instance wildInertiaContractedIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver mP mD :=
  ⟨(under_wildInertia_over_decomposition m).symm⟩

private instance integralClosure_maximalIdeal_liesOver_wildInertiaContractedIdeal :
    Ideal.LiesOver m mP := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[P]))

private instance integralClosure_maximalIdeal_liesOver_inertiaContractedIdeal :
    Ideal.LiesOver m mI := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[I]))

private instance integralClosure_maximalIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver m mD := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[D]))

/- The inertia fixed subalgebra `B^I` is the integral closure of `A` in `L^I`. -/
recall inertiaFixedSubalgebra_isIntegralClosure

-- Proof sketch: this is the first Galois-theoretic clause of the remark, viewing `L^I / L^D`
-- through the canonical fixed-field tower attached to `I ≤ D`.
/-- Remark 15.113.9 (1): the fixed-field extension `L^I / L^D` is Galois. -/
theorem inertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[I] := sorry

-- Proof sketch: the Galois group in `(1)` is the quotient `D / I`.
/-- Companion cardinal statement for Remark 15.113.9 (1): the Galois group of `L^I / L^D` has the
same cardinality as the quotient `D / I`. -/
theorem card_gal_inertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[I] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf I D) := sorry

-- Proof sketch: clause `(2)` is the wild-inertia step in the fixed-field tower.
/-- Remark 15.113.9 (2): the fixed-field extension `L^P / L^I` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_inertiaFixedField :
    IsGalois L[I] L[P] := sorry

-- Proof sketch: the Galois group in `(2)` is the tame inertia quotient `I_t = I / P`.
/-- Companion cardinal statement for Remark 15.113.9 (2): the Galois group of `L^P / L^I` has the
same cardinality as `I_t = I / P`. -/
theorem card_gal_wildInertiaFixedField_over_inertiaFixedField :
    Nat.card (Gal(L[P] / L[I])) = Nat.card I_t := sorry

-- Proof sketch: clause `(3)` is the composite Galois step `L^P / L^D`.
/-- Remark 15.113.9 (3): the fixed-field extension `L^P / L^D` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[P] := sorry

-- Proof sketch: the Galois group in `(3)` is the quotient `D / P`.
/-- Companion cardinal statement for Remark 15.113.9 (3): the Galois group of `L^P / L^D` has the
same cardinality as the quotient `D / P`. -/
theorem card_gal_wildInertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[P] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf P D) := sorry

-- Proof sketch: `m^I` is the unique prime of `B^I` above `m^D`.
/-- Remark 15.113.9 (4): the contracted ideal `m^I` is the unique prime of `B^I` lying over
`m^D`. -/
theorem inertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B[I]) :
    q.1 = mI := sorry

-- Proof sketch: `m^P` is the unique prime of `B^P` above `m^I`.
/-- Remark 15.113.9 (5): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^I`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_inertiaContractedIdeal
    (q : Ideal.primesOver mI B[P]) :
    q.1 = mP := sorry

-- Proof sketch: `m` is the unique prime of `B` above `m^P`.
/-- Remark 15.113.9 (6): the maximal ideal `m` is the unique prime of `B` lying over `m^P`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_wildInertiaContractedIdeal
    (q : Ideal.primesOver mP B) :
    q.1 = m := sorry

-- Proof sketch: combine `(4)` and `(5)` to descend uniqueness from `B^P` to `B^D`.
/-- Remark 15.113.9 (7): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^D`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B[P]) :
    q.1 = mP := sorry

-- Proof sketch: combine `(5)` and `(6)` to ascend uniqueness from `B^I` to `B`.
/-- Remark 15.113.9 (8): the maximal ideal `m` is the unique prime of `B` lying over `m^I`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_inertiaContractedIdeal
    (q : Ideal.primesOver mI B) :
    q.1 = m := sorry

-- Proof sketch: combine `(7)` and `(6)` to ascend uniqueness from `B^D` to `B`.
/-- Remark 15.113.9 (9): the maximal ideal `m` is the unique prime of `B` lying over `m^D`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B) :
    q.1 = m := sorry

-- Proof sketch: `B^D_{m^D}` is the unramified-local branch over `A`.
/-- Remark 15.113.9 (10): `A → B^D` is étale at the contracted ideal `m^D`. -/
theorem decompositionFixedSubalgebra_isEtaleAt_under :
    IsEtaleAt A mD := sorry

-- Proof sketch: clause `(10)` also says the induced residue-field extension is trivial.
/-- Remark 15.113.9 (10): the induced residue-field map `κA → κ(m^D)` is bijective. -/
theorem baseToDecompositionResidueField_bijective :
    Function.Bijective (algebraMap κA κD) := sorry

-- Proof sketch: the relative step `B^D_{m^D} → B^I_{m^I}` is the étale residue-field Galois step
-- with group `D / I`.
/-- Remark 15.113.9 (11): `B^D → B^I` is étale at the contracted ideal `m^I`. -/
theorem decompositionToInertiaFixedSubalgebra_isEtaleAt_under :
    IsEtaleAt B[D] mI := sorry

-- Proof sketch: the residue-field extension in `(11)` is Galois.
/-- Remark 15.113.9 (11): the induced residue-field extension `κ(m^I) / κ(m^D)` is Galois. -/
theorem decompositionToInertiaResidueField_isGalois :
    IsGalois κD κI := sorry

-- Proof sketch: the Galois group of the residue-field extension in `(11)` has cardinality
-- `|D / I|`.
/-- Companion cardinal statement for Remark 15.113.9 (11): the residue-field Galois group has the
same cardinality as `D / I`. -/
theorem card_gal_decompositionToInertiaResidueField :
    Nat.card (Gal(κI / κD)) = Nat.card (D ⧸ Subgroup.subgroupOf I D) := sorry

/- Remark 15.113.9 (12): `A → B^I` is étale at the contracted ideal `m^I`. -/
recall inertiaFixedSubalgebra_isEtaleAt_under

-- Proof sketch: clause `(13)` is the tame local branch over `B^I`, with ramification index
-- `|I_t|` and trivial residue field extension.
/-- Remark 15.113.9 (13): the ramification index of the branch `B^I ⊂ B^P` at
`m^I ⊂ m^P` is `|I_t|`. -/
theorem inertiaToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx mI mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(13)` is trivial.
/-- Remark 15.113.9 (13): the induced residue-field map `κ(m^I) → κ(m^P)` is bijective. -/
theorem inertiaToWildInertiaResidueField_bijective :
    Function.Bijective (algebraMap κI κP) := sorry

-- Proof sketch: the ramification index in `(13)` is prime to the residue characteristic of
-- `κ(m^I)`.
/-- Remark 15.113.9 (13): the ramification index `|I_t|` is prime to the residue characteristic of
`κ(m^I)`. -/
theorem inertiaToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κI q] :
    Nat.Coprime (Ideal.ramificationIdx mI mP) q := sorry

-- Proof sketch: clause `(14)` is the composite branch `B^D ⊂ B^P`.
/-- Remark 15.113.9 (14): the ramification index of the branch `B^D ⊂ B^P` at
`m^D ⊂ m^P` is `|I_t|`. -/
theorem decompositionToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx mD mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(14)` is separable.
/-- Remark 15.113.9 (14): the induced residue-field extension `κ(m^P) / κ(m^D)` is separable. -/
theorem decompositionToWildInertiaResidueField_isSeparable :
    Algebra.IsSeparable κD κP := sorry

-- Proof sketch: the ramification index in `(14)` is prime to the residue characteristic of
-- `κ(m^D)`.
/-- Remark 15.113.9 (14): the ramification index `|I_t|` is prime to the residue characteristic of
`κ(m^D)`. -/
theorem decompositionToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κD q] :
    Nat.Coprime (Ideal.ramificationIdx mD mP) q := sorry

-- Proof sketch: clause `(15)` is the total branch `A ⊂ B^P`.
/-- Remark 15.113.9 (15): the ramification index of the branch `A ⊂ B^P` at `p ⊂ m^P`
is `|I_t|`. -/
theorem baseToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx p mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(15)` is separable.
/-- Remark 15.113.9 (15): the induced residue-field extension `κ(m^P) / κA` is separable. -/
theorem baseToWildInertiaResidueField_isSeparable :
    Algebra.IsSeparable κA κP := sorry

-- Proof sketch: the ramification index in `(15)` is prime to the residue characteristic of
-- `κA`.
/-- Remark 15.113.9 (15): the ramification index `|I_t|` is prime to the residue characteristic of
`κA`. -/
theorem baseToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κA q] :
    Nat.Coprime (Ideal.ramificationIdx p mP) q := sorry

end
