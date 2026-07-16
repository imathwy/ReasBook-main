import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_111_2
import stacks_proof.stacks_project.Chap15.Lemma_15_113_5

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
    SMulCommClass G A B := by
  -- The restricted action fixes `A`-scalars because `galRestrict` is an `A`-algebra equivalence.
  refine ⟨fun g a b ↦ ?_⟩
  have hfix : (galRestrict A K L B g) (algebraMap A B a) = algebraMap A B a := by
    simpa using (galRestrict A K L B g).commutes a
  rw [Algebra.smul_def, Algebra.smul_def]
  change
    (galRestrict A K L B g) ((algebraMap A B a : B) * b) =
      (algebraMap A B a : B) * (galRestrict A K L B g b)
  rw [map_mul, hfix]

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B G := by
  -- The integral closure inherits the invariant-ring structure from the ambient Galois action.
  simpa using Algebra.isInvariant_of_isGalois (A := A) (B := B) (G := G)

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

/-- Helper for Remark 15.113.9: a subgroup inclusion `H ≤ H'` induces the canonical algebra
structure `B^H' → B^H` on fixed subalgebras. -/
private noncomputable def fixedSubalgebraAlgebraOfLe
    {H H' : Subgroup G} (h : H ≤ H') :
    Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
  ((Subalgebra.inclusion (fixedSubalgebra_le_of_le (A := A) (K := K) (L := L) h)).toRingHom).toAlgebra

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

private local instance integralClosure_ideal_mulAction :
    MulAction G (Ideal B) :=
  Ideal.pointwiseDistribMulAction.toMulAction

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

/-- Helper for Remark 15.113.9: fixed scalars from `B^H` commute with the restricted `H`-action on
the ambient integral closure `B`. -/
private instance fixedSubalgebra_smulCommClass (H : Subgroup G) :
    SMulCommClass H (FixedPoints.subalgebra A B H) B where
  smul_comm g x r := by
    -- A fixed scalar is pointwise invariant under the subgroup action, so it can be moved past
    -- the action on `B`.
    change (((g : H) : G) • ((x : B) * r)) = (x : B) * (((g : H) : G) • r)
    rw [smul_mul']
    simpa using congrArg (fun t : B ↦ t * (((g : H) : G) • r)) (x.2 g)

/-- Helper for Remark 15.113.9: `B` is invariant over each fixed subalgebra `B^H`. -/
private instance fixedSubalgebra_isInvariant (H : Subgroup G) :
    Algebra.IsInvariant (FixedPoints.subalgebra A B H) B H where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- Helper for Remark 15.113.9: every fixed subalgebra `B^H` is integral over the base discrete
valuation ring `A`. -/
private theorem fixedSubalgebra_isIntegral (H : Subgroup G) :
    Algebra.IsIntegral A (FixedPoints.subalgebra A B H) := by
  -- Restrict integrality from the ambient integral closure `B` to the fixed subalgebra `B^H`.
  rw [Subalgebra.isIntegral_iff]
  intro x hx
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  exact Algebra.IsIntegral.isIntegral x

/-- Helper for Remark 15.113.9: the contraction of `m` to any fixed subalgebra `B^H` is a maximal
ideal. -/
private theorem fixedSubalgebra_contractedIdeal_isMaximal (H : Subgroup G) :
    (m.under (FixedPoints.subalgebra A B H) : Ideal (FixedPoints.subalgebra A B H)).IsMaximal := by
  letI : Algebra.IsIntegral A (FixedPoints.subalgebra A B H) :=
    fixedSubalgebra_isIntegral (H := H)
  letI : (m.under (FixedPoints.subalgebra A B H) :
      Ideal (FixedPoints.subalgebra A B H)).IsPrime := by
    -- The contracted ideal is prime because it is the comap of the maximal ideal `m`.
    simpa [Ideal.under_def] using
      (Ideal.comap_isPrime (algebraMap (FixedPoints.subalgebra A B H) B) m :
        (Ideal.comap (algebraMap (FixedPoints.subalgebra A B H) B) m).IsPrime)
  have hcomap_max :
      (Ideal.comap (algebraMap A (FixedPoints.subalgebra A B H))
        (m.under (FixedPoints.subalgebra A B H) :
          Ideal (FixedPoints.subalgebra A B H))).IsMaximal := by
    -- Rewrite the double contraction to the already-known maximal contraction of `m` to `A`.
    change (Ideal.comap (algebraMap A (FixedPoints.subalgebra A B H))
      (Ideal.comap (algebraMap (FixedPoints.subalgebra A B H) B) m)).IsMaximal
    simpa [Ideal.under_def, RingHom.comp_assoc] using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m :
        (Ideal.comap (algebraMap A B) m).IsMaximal)
  -- Integral extensions preserve maximality along contraction once the source contraction is
  -- maximal.
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (m.under (FixedPoints.subalgebra A B H)) hcomap_max

/-- Helper for Remark 15.113.9: the quotient of `B^H` by the contracted branch ideal maps
bijectively to its residue field. -/
private theorem fixedSubalgebra_quotient_residueField_bijective (H : Subgroup G) :
    Function.Bijective
      (algebraMap
        ((FixedPoints.subalgebra A B H) ⧸
          (m.under (FixedPoints.subalgebra A B H) : Ideal (FixedPoints.subalgebra A B H)))
        (Ideal.ResidueField
          (m.under (FixedPoints.subalgebra A B H) : Ideal (FixedPoints.subalgebra A B H)))) := by
  letI : (m.under (FixedPoints.subalgebra A B H) :
      Ideal (FixedPoints.subalgebra A B H)).IsMaximal :=
    fixedSubalgebra_contractedIdeal_isMaximal (m := m) (H := H)
  -- For a maximal ideal, the quotient-to-residue-field map is the canonical bijection.
  simpa using
    (Ideal.bijective_algebraMap_quotient_residueField
      (m.under (FixedPoints.subalgebra A B H) : Ideal (FixedPoints.subalgebra A B H)))

local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

noncomputable instance decompositionToInertiaFixedSubalgebraAlgebra :
    Algebra (B[D]) (B[I]) :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedSubalgebraAlgebra :
    Algebra (B[I]) (B[P]) :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedSubalgebraAlgebra :
    Algebra (B[D]) (B[P]) :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

noncomputable instance decompositionToInertiaFixedFieldAlgebra :
    Algebra (L[D]) (L[I]) :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedFieldAlgebra :
    Algebra (L[I]) (L[P]) :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedFieldAlgebra :
    Algebra (L[D]) (L[P]) :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

theorem under_decomposition_over_base :
    p = Ideal.comap (algebraMap A (B[D])) mD := by
  change p = Ideal.comap ((algebraMap (B[D]) B).comp (algebraMap A (B[D]))) m
  simpa using (Ideal.over_def m p)

omit [m.IsMaximal] in
theorem under_inertia_over_decomposition :
    mD = Ideal.comap (algebraMap (B[D]) (B[I])) mI := by
  change Ideal.comap (algebraMap (B[D]) B) m =
    Ideal.comap ((algebraMap (B[I]) B).comp (algebraMap (B[D]) (B[I]))) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_inertia :
    mI = Ideal.comap (algebraMap (B[I]) (B[P])) mP := by
  change Ideal.comap (algebraMap (B[I]) B) m =
    Ideal.comap ((algebraMap (B[P]) B).comp (algebraMap (B[I]) (B[P]))) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_decomposition :
    mD = Ideal.comap (algebraMap (B[D]) (B[P])) mP := by
  change Ideal.comap (algebraMap (B[D]) B) m =
    Ideal.comap ((algebraMap (B[P]) B).comp (algebraMap (B[D]) (B[P]))) m
  rfl

theorem under_wildInertia_over_base :
    p = Ideal.comap (algebraMap A (B[P])) mP := by
  change p = Ideal.comap ((algebraMap (B[P]) B).comp (algebraMap A (B[P]))) m
  simpa using (Ideal.over_def m p)

noncomputable instance baseToDecompositionResidueFieldAlgebra :
    Algebra κA κD :=
  (Ideal.ResidueField.map p mD (algebraMap A (B[D])) (under_decomposition_over_base m)).toAlgebra

noncomputable instance decompositionToInertiaResidueFieldAlgebra :
    Algebra κD κI :=
  (Ideal.ResidueField.map mD mI (algebraMap (B[D]) (B[I]))
      (under_inertia_over_decomposition m)).toAlgebra

noncomputable instance inertiaToWildInertiaResidueFieldAlgebra :
    Algebra κI κP :=
  (Ideal.ResidueField.map mI mP (algebraMap (B[I]) (B[P]))
      (under_wildInertia_over_inertia m)).toAlgebra

noncomputable instance decompositionToWildInertiaResidueFieldAlgebra :
    Algebra κD κP :=
  (Ideal.ResidueField.map mD mP (algebraMap (B[D]) (B[P]))
      (under_wildInertia_over_decomposition m)).toAlgebra

noncomputable instance baseToWildInertiaResidueFieldAlgebra :
    Algebra κA κP :=
  (Ideal.ResidueField.map p mP (algebraMap A (B[P])) (under_wildInertia_over_base m)).toAlgebra

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

/-- Helper for Remark 15.113.9: conjugating an inertia element by a decomposition-group element
stays in the inertia subgroup. -/
private theorem inertia_conj_mem_of_decomposition
    (τ : D) (σ : I) :
    τ.1 * σ.1 * τ.1⁻¹ ∈ I := by
  -- Transport the defining inertia congruence along the decomposition-group action on `B`.
  rw [ideal_inertia_mem_iff (A := A) (K := K) (L := L) (J := m)]
  intro x
  have hσ :
      σ.1 • (τ.1⁻¹ • x) - τ.1⁻¹ • x ∈ m := by
    exact (ideal_inertia_mem_iff (A := A) (K := K) (L := L) (J := m) σ.1).mp σ.2
      (τ.1⁻¹ • x)
  have htransport :
      τ.1 • (σ.1 • (τ.1⁻¹ • x) - τ.1⁻¹ • x) ∈ τ.1 • m := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.mem_map_of_mem (MulSemiringAction.toRingHom G B τ.1) hσ
  have hfix : τ.1 • m = m := MulAction.mem_stabilizer_iff.mp τ.2
  simpa [hfix, smul_sub, smul_smul, mul_assoc] using htransport

/-- Helper for Remark 15.113.9: the inertia subgroup is normal inside the decomposition group. -/
private theorem inertiaSubgroup_normal_in_decompositionGroup :
    Subgroup.Normal (Subgroup.subgroupOf I D) := by
  -- Route correction: clause `(1)` must run over the relative extension `L / L^D`, so we first
  -- isolate the source conjugation statement showing that `I` is stable under `D`.
  have hID : I ≤ D := Ideal.inertia_le_stabilizer m
  rw [Subgroup.normal_subgroupOf_iff hID]
  intro σ τ hσ hτ
  exact inertia_conj_mem_of_decomposition (m := m) ⟨τ, hτ⟩ ⟨σ, hσ⟩

/-- Helper for Remark 15.113.9: wild inertia is normal inside the inertia group. -/
private theorem wildInertiaSubgroup_normal_in_inertiaGroup :
    Subgroup.Normal (Subgroup.subgroupOf P I) := by
  -- This is exactly the normality owner already packaged when defining the tame inertia quotient.
  infer_instance

/-- Helper for Remark 15.113.9: wild inertia is normal inside the decomposition group. -/
private theorem wildInertiaSubgroup_normal_in_decompositionGroup' :
    Subgroup.Normal (Subgroup.subgroupOf P D) := by
  -- Clause `(3)` uses the larger normality statement already proved in Lemma `15.113.5`.
  simpa [P] using
    (wildInertiaSubgroup_normal_in_decompositionGroup (K := K) (m := m))

/- The inertia fixed subalgebra `B^I` is the integral closure of `A` in `L^I`. -/
recall inertiaFixedSubalgebra_isIntegralClosure

/-- Helper for Remark 15.113.9: the subgroup-to-relative-Galois equivalence acts by the ambient
automorphism on `L`. -/
private theorem subgroupEquivAlgEquiv_apply {H : Subgroup G} (σ : H) (x : L) :
    IntermediateField.subgroupEquivAlgEquiv H σ x = σ x := by
  -- Unfold the canonical equivalence from the subgroup owner to the relative Galois owner.
  rfl

/-- Helper for Remark 15.113.9: the inverse subgroup-to-relative-Galois equivalence restricts to
the same automorphism on `L`. -/
private theorem subgroupEquivAlgEquiv_symm_apply {H : Subgroup G}
    (σ : Gal(L / IntermediateField.fixedField H)) (x : L) :
    (((IntermediateField.subgroupEquivAlgEquiv H).symm σ : H) : G) x = σ x := by
  -- Evaluate the forward equivalence on the inverse image of `σ`, then simplify by the inverse
  -- relation of the equivalence.
  simpa using
    (subgroupEquivAlgEquiv_apply (H := H)
      ((IntermediateField.subgroupEquivAlgEquiv H).symm σ) x).symm

/-- Helper for Remark 15.113.9: transporting `H ≤ H'` into the relative Galois group over `L^H'`
cuts out exactly the relative copy of `L^H`. -/
private theorem relative_fixedField_subgroupOf_eq_extendScalars
    {H H' : Subgroup G} (hHH' : H ≤ H') :
    IntermediateField.fixedField
        ((Subgroup.subgroupOf H H').map (IntermediateField.subgroupEquivAlgEquiv H')) =
      (IntermediateField.fixedField H).extendScalars (IntermediateField.fixedField_le hHH') := by
  -- Identify the relative fixed field by computing the relative fixing subgroup of `L^H`.
  apply (IsGalois.fixedField_eq_iff_fixingSubgroup_eq
      (F := IntermediateField.fixedField H') (E := L)
      (K := (IntermediateField.fixedField H).extendScalars
        (IntermediateField.fixedField_le hHH'))).2
  ext φ
  constructor
  · intro hφ
    rw [Subgroup.mem_map]
    refine ⟨(IntermediateField.subgroupEquivAlgEquiv H').symm φ, ?_, ?_⟩
    · -- Pull the relative fixedness of `φ` back to the ambient subgroup owner `H`.
      rw [Subgroup.mem_subgroupOf, ← IntermediateField.fixingSubgroup_fixedField H,
        IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hfixx : φ x = x := by
        exact hφ x (show x ∈ (IntermediateField.fixedField H).extendScalars
          (IntermediateField.fixedField_le hHH') from hx)
      simpa [subgroupEquivAlgEquiv_symm_apply] using hfixx
    · -- The chosen witness is the inverse image of `φ` under the subgroup equivalence.
      exact (IntermediateField.subgroupEquivAlgEquiv H').apply_symm_apply φ
  · rintro ⟨σ, hσ, rfl⟩
    -- Transport the ambient `H`-fixedness of `σ` to the corresponding relative automorphism.
    rw [Subgroup.mem_subgroupOf, ← IntermediateField.fixingSubgroup_fixedField H,
      IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hfixx : ((σ : H') : G) x = x := by
      exact hσ x (show x ∈ IntermediateField.fixedField H from hx)
    simpa [subgroupEquivAlgEquiv_apply] using hfixx

/-- Helper for Remark 15.113.9: a normal transported subgroup yields the expected relative Galois
subextension over `L^H'`. -/
private theorem relative_fixedField_subgroupOf_isGalois
    {H H' : Subgroup G} (hHH' : H ≤ H')
    (hNormal : Subgroup.Normal (Subgroup.subgroupOf H H')) :
    IsGalois (IntermediateField.fixedField H')
      ((IntermediateField.fixedField H).extendScalars (IntermediateField.fixedField_le hHH')) := by
  let Hrel : Subgroup (Gal(L / IntermediateField.fixedField H')) :=
    (Subgroup.subgroupOf H H').map (IntermediateField.subgroupEquivAlgEquiv H')
  have hnormal : Subgroup.Normal Hrel := by
    -- Mapping a normal subgroup across the subgroup-to-relative-Galois equivalence preserves
    -- normality.
    exact Subgroup.Normal.map hNormal _ (IntermediateField.subgroupEquivAlgEquiv H').surjective
  letI : Subgroup.Normal Hrel := hnormal
  -- Apply the relative fixed-field criterion after identifying the transported fixed field.
  simpa [Hrel, relative_fixedField_subgroupOf_eq_extendScalars (H := H) (H' := H') hHH'] using
    (inferInstance :
      IsGalois (IntermediateField.fixedField H') (IntermediateField.fixedField Hrel))

/-- Helper for Remark 15.113.9: the relative Galois group of `L^H / L^H'` has the expected
quotient cardinality `|H' / H|`. -/
private theorem relative_fixedField_subgroupOf_card_gal
    {H H' : Subgroup G} (hHH' : H ≤ H')
    (hNormal : Subgroup.Normal (Subgroup.subgroupOf H H')) :
    Nat.card
        (Gal(((IntermediateField.fixedField H).extendScalars (IntermediateField.fixedField_le hHH')) /
          IntermediateField.fixedField H')) =
      Nat.card (H' ⧸ Subgroup.subgroupOf H H') := by
  let e : H' ≃* Gal(L / IntermediateField.fixedField H') :=
    IntermediateField.subgroupEquivAlgEquiv H'
  let Hrel : Subgroup (Gal(L / IntermediateField.fixedField H')) :=
    (Subgroup.subgroupOf H H').map e
  have hnormal : Subgroup.Normal Hrel := by
    -- The transported subgroup remains normal in the relative Galois group.
    exact Subgroup.Normal.map hNormal _ e.surjective
  letI : Subgroup.Normal Hrel := hnormal
  -- Compute the relative Galois group as a quotient and then transport that quotient back to `H'`.
  calc
    Nat.card
        (Gal(((IntermediateField.fixedField H).extendScalars (IntermediateField.fixedField_le hHH')) /
          IntermediateField.fixedField H')) =
        Nat.card (Gal(IntermediateField.fixedField Hrel / IntermediateField.fixedField H')) := by
          rw [← relative_fixedField_subgroupOf_eq_extendScalars (H := H) (H' := H') hHH']
    _ = Nat.card ((Gal(L / IntermediateField.fixedField H')) ⧸ Hrel) := by
          exact (Nat.card_congr (IsGalois.normalAutEquivQuotient Hrel).toEquiv).symm
    _ = Nat.card (H' ⧸ Subgroup.subgroupOf H H') := by
          exact (Nat.card_congr
            (QuotientGroup.congr (Subgroup.subgroupOf H H') Hrel e rfl).toEquiv).symm

/-- Remark 15.113.9 (1): the fixed-field extension `L^I / L^D` is Galois. -/
theorem inertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[I] := by
  -- Route correction: run the source proof in the relative extension `L / L^D`, then rewrite the
  -- resulting relative fixed field back to `L^I`.
  simpa using
    (relative_fixedField_subgroupOf_isGalois (H := I) (H' := D)
      (Ideal.inertia_le_stabilizer m) inertiaSubgroup_normal_in_decompositionGroup)

-- Proof sketch: the Galois group in `(1)` is the quotient `D / I`.
/-- Companion cardinal statement for Remark 15.113.9 (1): the Galois group of `L^I / L^D` has the
same cardinality as the quotient `D / I`. -/
theorem card_gal_inertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[I] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf I D) := by
  -- The relative quotient-cardinality theorem specializes directly to the inertia subgroup.
  simpa using
    (relative_fixedField_subgroupOf_card_gal (H := I) (H' := D)
      (Ideal.inertia_le_stabilizer m) inertiaSubgroup_normal_in_decompositionGroup)

-- Proof sketch: clause `(2)` is the wild-inertia step in the fixed-field tower.
/-- Remark 15.113.9 (2): the fixed-field extension `L^P / L^I` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_inertiaFixedField :
    IsGalois L[I] L[P] := by
  -- Apply the same relative fixed-field argument to the wild inertia subgroup inside inertia.
  simpa using
    (relative_fixedField_subgroupOf_isGalois (H := P) (H' := I)
      (wildInertiaSubgroup_le_inertia (K := K) m)
      wildInertiaSubgroup_normal_in_inertiaGroup)

-- Proof sketch: the Galois group in `(2)` is the tame inertia quotient `I_t = I / P`.
/-- Companion cardinal statement for Remark 15.113.9 (2): the Galois group of `L^P / L^I` has the
same cardinality as `I_t = I / P`. -/
theorem card_gal_wildInertiaFixedField_over_inertiaFixedField :
    Nat.card (Gal(L[P] / L[I])) = Nat.card I_t := by
  -- First identify the relative Galois group with `I / P`, then unfold the tame inertia quotient.
  simpa [I_t] using
    (relative_fixedField_subgroupOf_card_gal (H := P) (H' := I)
      (wildInertiaSubgroup_le_inertia (K := K) m)
      wildInertiaSubgroup_normal_in_inertiaGroup)

-- Proof sketch: clause `(3)` is the composite Galois step `L^P / L^D`.
/-- Remark 15.113.9 (3): the fixed-field extension `L^P / L^D` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[P] := by
  -- The same relative argument also handles the composite wild-inertia-over-decomposition step.
  simpa using
    (relative_fixedField_subgroupOf_isGalois (H := P) (H' := D)
      (wildInertiaSubgroup_le_decompositionGroup (K := K) m)
      wildInertiaSubgroup_normal_in_decompositionGroup')

-- Proof sketch: the Galois group in `(3)` is the quotient `D / P`.
/-- Companion cardinal statement for Remark 15.113.9 (3): the Galois group of `L^P / L^D` has the
same cardinality as the quotient `D / P`. -/
theorem card_gal_wildInertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[P] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf P D) := by
  -- Specialize the relative quotient-cardinality statement to `P ≤ D`.
  simpa using
    (relative_fixedField_subgroupOf_card_gal (H := P) (H' := D)
      (wildInertiaSubgroup_le_decompositionGroup (K := K) m)
      wildInertiaSubgroup_normal_in_decompositionGroup')

-- Proof sketch: `m^I` is the unique prime of `B^I` above `m^D`.
/-- Helper for Remark 15.113.9: uniqueness of the branch above `m ∩ B^H'` in a smaller fixed
subalgebra `B^H` follows by lifting to `B`, using the ambient uniqueness theorem there, and
contracting back. -/
private theorem contracted_prime_unique_between_fixed_subalgebras
    {H H' : Subgroup G} (hHH' : H ≤ H') (hH'D : H' ≤ D)
    (q : @Ideal.primesOver ↥(FixedPoints.subalgebra A B H') ↥(FixedPoints.subalgebra A B H) _ _
      (fixedSubalgebraAlgebraOfLe (A := A) (K := K) (L := L) hHH')
      (m.under (FixedPoints.subalgebra A B H'))) :
    q.1 = m.under (FixedPoints.subalgebra A B H) := by
  let _ : q.1.IsPrime := q.2.1
  letI : Algebra.IsIntegral (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) := by
    -- Restrict the integrality of `B` over `B^H'` to the intermediate fixed subalgebra `B^H`.
    rw [Subalgebra.isIntegral_iff]
    intro x hx
    letI : Algebra.IsIntegral (FixedPoints.subalgebra A B H') B :=
      Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B H') B H'
    exact Algebra.IsIntegral.isIntegral x
  have hqmax : q.1.IsMaximal := by
    -- A prime of `B^H` above the maximal branch of `B^H'` is maximal by integrality.
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.1 <| by
      simpa [q.1.over_def (m.under (FixedPoints.subalgebra A B H'))] using
        fixedSubalgebra_contractedIdeal_isMaximal (m := m) (H := H')
  letI : Algebra.IsIntegral (FixedPoints.subalgebra A B H) B :=
    Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B H) B H
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) q.1
  letI : Q.IsMaximal := hQmax
  have hQover' : Q.LiesOver (m.under (FixedPoints.subalgebra A B H')) := by
    -- Compose the branch `Q` over `q.1` with the given branch `q.1` over `m ∩ B^H'`.
    rw [Ideal.liesOver_iff]
    calc
      Ideal.comap (algebraMap (FixedPoints.subalgebra A B H') B) Q =
          Ideal.comap
            (algebraMap (FixedPoints.subalgebra A B H')
              (FixedPoints.subalgebra A B H))
            (Ideal.comap (algebraMap (FixedPoints.subalgebra A B H) B) Q) := by
              rfl
      _ = Ideal.comap
            (algebraMap (FixedPoints.subalgebra A B H')
              (FixedPoints.subalgebra A B H))
            q.1 := by
              rw [(Ideal.liesOver_iff _ _).mp hQover]
      _ = m.under (FixedPoints.subalgebra A B H') := by
              exact (Ideal.liesOver_iff _ _).mp q.2.2
  let qB : Ideal.primesOver (m.under (FixedPoints.subalgebra A B H')) B :=
    Ideal.primesOver.mk (m.under (FixedPoints.subalgebra A B H')) Q
  have hQeq : Q = m :=
    integralClosure_maximalIdeal_unique_prime_over_fixed_contracted_ideal
      (m := m) (H := H') hH'D qB
  -- Contract the ambient identification `Q = m` back to the smaller fixed subalgebra `B^H`.
  calc
    q.1 = Ideal.comap (algebraMap (FixedPoints.subalgebra A B H) B) Q := by
      exact (Ideal.liesOver_iff _ _).mp hQover
    _ = m.under (FixedPoints.subalgebra A B H) := by
      simpa [Ideal.under_def, hQeq]

/-- Remark 15.113.9 (4): the contracted ideal `m^I` is the unique prime of `B^I` lying over
`m^D`. -/
theorem inertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : @Ideal.primesOver ↥(B[D]) ↥(B[I]) _ _
      (inferInstance : Algebra ↥(B[D]) ↥(B[I])) mD) :
    q.1 = mI := by
  -- Contract the unique ambient branch above `m^D` from `B` down to the intermediate
  -- fixed-subalgebra tower `B^D ⊆ B^I`.
  simpa using
    (contracted_prime_unique_between_fixed_subalgebras
      (m := m) (H := I) (H' := D)
      (Ideal.inertia_le_stabilizer m) (show D ≤ D from fun _ h ↦ h) q)

-- Proof sketch: `m^P` is the unique prime of `B^P` above `m^I`.
/-- Remark 15.113.9 (5): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^I`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_inertiaContractedIdeal
    (q : @Ideal.primesOver ↥(B[I]) ↥(B[P]) _ _
      (inferInstance : Algebra ↥(B[I]) ↥(B[P])) mI) :
    q.1 = mP := by
  -- The same contraction argument applied to the tower `B^I ⊆ B^P` gives the unique branch
  -- above `m^I`.
  simpa using
    (contracted_prime_unique_between_fixed_subalgebras
      (m := m) (H := P) (H' := I)
      (wildInertiaSubgroup_le_inertia (K := K) m)
      (Ideal.inertia_le_stabilizer m) q)

/-- Helper for Remark 15.113.9: any prime of `B` above the contraction to a fixed subalgebra
`B^H` with `H ≤ D` is forced back to the chosen maximal ideal `m`. -/
private theorem integralClosure_maximalIdeal_unique_prime_over_fixed_contracted_ideal
    {H : Subgroup G} (hHD : H ≤ D)
    (q : Ideal.primesOver (m.under (FixedPoints.subalgebra A B H)) B) :
    q.1 = m := by
  have hunder :
      (q : Ideal B).under (FixedPoints.subalgebra A B H) =
        m.under (FixedPoints.subalgebra A B H) := by
    -- Both branches contract to the same ideal in the fixed subalgebra `B^H`.
    exact
      q.2.2.over.symm.trans
        (Ideal.over_def m (m.under (FixedPoints.subalgebra A B H)))
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subalgebra A B H) B H (q : Ideal B) m hunder
  have hfix_inv : ((((σ : H) : G)⁻¹) • m : Ideal B) = m := by
    -- The inverse of an element of `H ≤ D` still lies in the decomposition group, so it fixes
    -- the chosen maximal branch `m`.
    exact MulAction.mem_stabilizer_iff.mp ((hHD σ.2.inv))
  have hq : (q : Ideal B) = (((σ⁻¹ : H) : G) • m : Ideal B) := by
    -- Rewrite `q` by undoing the `σ`-transport supplied by invariant-theoretic transitivity.
    calc
      (q : Ideal B) = ((((σ : H) : G)⁻¹ * ((σ : H) : G)) • (q : Ideal B)) := by
        rw [show ((((σ : H) : G)⁻¹ * ((σ : H) : G)) : G) = 1 by simp, one_smul]
      _ = (((σ⁻¹ : H) : G) • ((((σ : H) : G) • (q : Ideal B) : Ideal B))) := by
        simp [smul_smul]
      _ = (((σ⁻¹ : H) : G) • m : Ideal B) := by
        exact congrArg (fun J : Ideal B ↦ (((σ⁻¹ : H) : G) • J : Ideal B)) hσ.symm
  simpa [hfix_inv] using hq

/-- Remark 15.113.9 (6): the maximal ideal `m` is the unique prime of `B` lying over `m^P`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_wildInertiaContractedIdeal
    (q : Ideal.primesOver mP B) :
    q.1 = m := by
  -- Specialize the ambient uniqueness theorem to the wild inertia fixed subalgebra `B^P`.
  simpa using
    (integralClosure_maximalIdeal_unique_prime_over_fixed_contracted_ideal
      (m := m) (H := P)
      (wildInertiaSubgroup_le_decompositionGroup (K := K) m) q)

-- Proof sketch: combine `(4)` and `(5)` to descend uniqueness from `B^P` to `B^D`.
/-- Remark 15.113.9 (7): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^D`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : @Ideal.primesOver ↥(B[D]) ↥(B[P]) _ _
      (inferInstance : Algebra ↥(B[D]) ↥(B[P])) mD) :
    q.1 = mP := by
  -- Contract the unique ambient branch above `m^D` through the tower `B^D ⊆ B^P`.
  simpa using
    (contracted_prime_unique_between_fixed_subalgebras
      (m := m) (H := P) (H' := D)
      (wildInertiaSubgroup_le_decompositionGroup (K := K) m)
      (show D ≤ D from fun _ h ↦ h) q)

-- Proof sketch: combine `(5)` and `(6)` to ascend uniqueness from `B^I` to `B`.
/-- Remark 15.113.9 (8): the maximal ideal `m` is the unique prime of `B` lying over `m^I`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_inertiaContractedIdeal
    (q : Ideal.primesOver mI B) :
    q.1 = m := by
  -- Specialize the ambient uniqueness theorem to the inertia fixed subalgebra `B^I`.
  simpa using
    (integralClosure_maximalIdeal_unique_prime_over_fixed_contracted_ideal
      (m := m) (H := I) (Ideal.inertia_le_stabilizer m) q)

-- Proof sketch: combine `(7)` and `(6)` to ascend uniqueness from `B^D` to `B`.
/-- Remark 15.113.9 (9): the maximal ideal `m` is the unique prime of `B` lying over `m^D`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B) :
    q.1 = m := by
  -- Specialize the ambient uniqueness theorem to the decomposition fixed subalgebra `B^D`.
  simpa using
    (integralClosure_maximalIdeal_unique_prime_over_fixed_contracted_ideal
      (m := m) (H := D) (show D ≤ D from fun _ h ↦ h) q)

/-- Helper for Remark 15.113.9: each inertia element stabilizes the chosen maximal ideal `m`. -/
private theorem inertia_ideal_stable
    (g : I) :
    (((g : I) : G) • m : Ideal B) = m := by
  -- This is the defining stabilizer property built into the inertia subgroup.
  exact MulAction.mem_stabilizer_iff.mp ((Ideal.inertia_le_stabilizer m) g.2)

/-- Helper for Remark 15.113.9: the quotient `B / m` carries the induced inertia action because
every inertia element stabilizes `m`. -/
private noncomputable abbrev inertiaQuotientAction :
    MulSemiringAction I (B ⧸ m) :=
  @quotientMulSemiringAction B I inferInstance inferInstance inferInstance m
    (fun h ↦ inertia_ideal_stable (m := m) h)

/-- Helper for Remark 15.113.9: the quotient of the inertia fixed subalgebra by `m^I` identifies
with the residue field `κ(m^I)`. -/
private noncomputable abbrev inertiaContractedIdeal_quotient_equiv_residueField :
    B[I] ⧸ mI ≃+* κI :=
  RingEquiv.ofBijective
    (algebraMap (B[I] ⧸ mI) κI)
    (fixedSubalgebra_quotient_residueField_bijective (m := m) I)

/-- Helper for Remark 15.113.9: the residue-field extension `κ(m) / κ(m^I)` is purely
inseparable. -/
private theorem inertia_to_integralClosure_residueField_isPurelyInseparable :
    IsPurelyInseparable κI m.ResidueField := by
  -- TODO for Remark 15.113.9: complete the quotient-to-residue-field transport from
  -- `B^I / m^I → B / m`, using `fixedPointsQuotient_hasPurelyInseparableResidueFieldExtensions`
  -- for the inertia action on `B ⧸ m` and the quotient/residue-field identifications recorded
  -- above. The broken import of `Lemma_15_113_8` forced this bridge to be rebuilt locally.
  sorry

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

/- Remark 15.113.9 (12): `A → B^I` is étale at the contracted ideal `m^I`.
   Source dependency note: the canonical owner theorem lives in `Lemma_15_113_8`, but that file is
   currently broken in this workspace, so this remark no longer imports it directly. -/

-- Proof sketch: clause `(13)` is the tame local branch over `B^I`, with ramification index
-- `|I_t|` and trivial residue field extension.
/-- Remark 15.113.9 (13): the ramification index of the branch `B^I ⊂ B^P` at
`m^I ⊂ m^P` is `|I_t|`. -/
theorem inertiaToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    @Ideal.ramificationIdx (B[I]) (B[P]) _ _
        (inertiaToWildInertiaFixedSubalgebraAlgebra (m := m)) mI mP =
      Nat.card I_t := sorry

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
    Nat.Coprime
      (@Ideal.ramificationIdx (B[I]) (B[P]) _ _
        (inertiaToWildInertiaFixedSubalgebraAlgebra (m := m)) mI mP) q := sorry

-- Proof sketch: clause `(14)` is the composite branch `B^D ⊂ B^P`.
/-- Remark 15.113.9 (14): the ramification index of the branch `B^D ⊂ B^P` at
`m^D ⊂ m^P` is `|I_t|`. -/
theorem decompositionToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    @Ideal.ramificationIdx (B[D]) (B[P]) _ _
        (decompositionToWildInertiaFixedSubalgebraAlgebra (m := m)) mD mP =
      Nat.card I_t := sorry

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
    Nat.Coprime
      (@Ideal.ramificationIdx (B[D]) (B[P]) _ _
        (decompositionToWildInertiaFixedSubalgebraAlgebra (m := m)) mD mP) q := sorry

-- Proof sketch: clause `(15)` is the total branch `A ⊂ B^P`.
/-- Remark 15.113.9 (15): the ramification index of the branch `A ⊂ B^P` at `p ⊂ m^P`
is `|I_t|`. -/
theorem baseToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    @Ideal.ramificationIdx A (B[P]) _ _ (inferInstance : Algebra A (B[P])) p mP =
      Nat.card I_t := sorry

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
    Nat.Coprime
      (@Ideal.ramificationIdx A (B[P]) _ _ (inferInstance : Algebra A (B[P])) p mP) q := sorry

end
