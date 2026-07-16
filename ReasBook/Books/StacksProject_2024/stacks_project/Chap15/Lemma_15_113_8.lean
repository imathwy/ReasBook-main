import Mathlib
import StacksProject_2024.stacks_project.Chap09.Lemma_9_15_9
import StacksProject_2024.stacks_project.Chap09.Lemma_9_21_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_111_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open Ideal IsLocalRing
open IntermediateField
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L

/-- Helper for Lemma 15.113.8: the Galois action on the integral closure is `A`-linear. -/
private local instance integralClosure_smulCommClass :
    SMulCommClass G A B := by
  infer_instance

local notation "B[" H "]" => FixedPoints.subalgebra A B H
local notation "L[" H "]" => IntermediateField.fixedField H

/- Domain-style sampling for Lemma 15.113.8:
- primary domain: integral closures and fixed objects for subgroup actions of `Gal(L / K)` on the
  integral closure `B = integralClosure A L`;
- sampled owner declarations:
  `Ideal.inertia`,
  `FixedPoints.subalgebra`,
  `IntermediateField.fixedField`,
  `algebraMap_galRestrict_apply`;
- best owner abstraction: for a subgroup `H : Subgroup Gal(L / K)`, the fixed `A`-subalgebra
  `FixedPoints.subalgebra A B H` of the integral closure and the fixed field
  `IntermediateField.fixedField H`;
- primitive data: the canonical fixed-subalgebra owner `FixedPoints.subalgebra A B H`;
- derived API: the canonical map `B^H → L^H` and the source-facing inertia specialization obtained
  by setting `H = m.inertia G`.

Layer triage:
- `source-facing`: the inertia specialization saying `B^I` is the integral closure of `A` in
  `L^I`, together with the later local étale statement;
- `core/canonical`: the owner pair `FixedPoints.subalgebra A B H` /
  `IntermediateField.fixedField H`;
- `bridge/view`: the canonical map from the fixed subalgebra to the fixed field.

The bridge layer therefore belongs at the general subgroup level. Only the final étale statement
should remain in the local inertia/maximal-ideal section. -/

variable (H : Subgroup Gal(L/K))

-- Proof sketch: an element of the fixed subalgebra is fixed in `L` by every element of `H`, so
-- its image lies in the fixed field `L^H`.
private theorem fixedSubalgebra_mem_fixedField (x : B[H]) :
    algebraMap B L x ∈ L[H] := by
  -- Unpack the fixed-subalgebra condition and transport it through the inclusion `B ↪ L`.
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  simpa using congrArg (algebraMap B L) (x.2 ⟨g, hg⟩)

private noncomputable abbrev fixedSubalgebraToFixedField : B[H] →ₐ[A] L[H] :=
  show B[H] →ₐ[A] L[H] from
    AlgHom.codRestrict
      ((IsScalarTower.toAlgHom A B L).comp (B[H]).val)
      (((L[H]).toSubalgebra : Subalgebra K L).restrictScalars A)
      (fixedSubalgebra_mem_fixedField H)

private noncomputable instance fixedSubalgebraToFixedFieldAlgebra :
    Algebra B[H] L[H] :=
  (fixedSubalgebraToFixedField H).toRingHom.toAlgebra

/-- Helper for Lemma 15.113.8: the canonical map `B^H → L^H` is injective because it is induced by
the inclusion `B ↪ L`. -/
private theorem fixedSubalgebraToFixedField_injective :
    Function.Injective (algebraMap B[H] L[H]) := by
  -- Compare in `L`, where injectivity of `B ↪ L` is immediate from faithful scalar action.
  intro x y hxy
  apply Subtype.ext
  exact FaithfulSMul.algebraMap_injective B L <|
    congrArg (fun z : L[H] ↦ (z : L)) hxy

/-- Helper for Lemma 15.113.8: an element of the fixed field integral over `A` comes from the
fixed subalgebra of the ambient integral closure. -/
private theorem fixedSubalgebra_exists_of_isIntegral
    (x : L[H]) (hx : IsIntegral A x) :
    ∃ y : B[H], algebraMap B[H] L[H] y = x := by
  let f : L[H] →ₐ[A] L := (((L[H]).toSubalgebra : Subalgebra K L).restrictScalars A).val
  have hxL : IsIntegral A (x : L) := IsIntegral.map f hx
  have hIntegralClosure :
      IsIntegral A (x : L) ↔ ∃ y : B, algebraMap B L y = (x : L) := by
    simpa using
      (IsIntegralClosure.isIntegral_iff (A := integralClosure A L) (R := A) (x := (x : L)))
  obtain ⟨y, hy⟩ := hIntegralClosure.mp hxL
  refine ⟨⟨y, ?_⟩, ?_⟩
  · -- The fixed-field element `x` gives the needed `H`-fixedness of its lift `y`.
    intro g
    apply FaithfulSMul.algebraMap_injective B L
    calc
      algebraMap B L (g • y) = g • algebraMap B L y := by simp
      _ = g • (x : L) := by rw [hy]
      _ = (x : L) := x.2 g
      _ = algebraMap B L y := by rw [hy]
  · -- The chosen lift maps back to `x` by construction.
    apply Subtype.ext
    change algebraMap B L y = x
    simpa using hy

/-- Helper for Lemma 15.113.8: every element of the fixed subalgebra `B^H` is integral over the
base ring `A` because `B` is the integral closure of `A` in `L`. -/
private theorem fixedSubalgebra_isIntegral :
    Algebra.IsIntegral A B[H] := by
  -- Reduce integrality of the fixed subalgebra to integrality inside the ambient integral closure.
  rw [Subalgebra.isIntegral_iff]
  intro x hx
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  exact Algebra.IsIntegral.isIntegral x

-- Proof sketch: an element of `L^H` integral over `A` already lies in the ambient integral
-- closure `B`, and the fixed-field condition forces it to land in the fixed subalgebra `B^H`.
/-- Companion bridge theorem: for any subgroup `H ≤ Gal(L / K)`, the fixed subalgebra `B^H` of
the integral closure `B` is the integral closure of `A` in the fixed field `L^H`. -/
theorem fixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[H] A L[H] := by
  -- Use the canonical map `B^H → L^H` and characterize integrality by lifting to `B`.
  refine IsIntegralClosure.mk (fixedSubalgebraToFixedField_injective (A := A) (K := K) (L := L) H) ?_
  intro x
  constructor
  · intro hx
    exact fixedSubalgebra_exists_of_isIntegral (A := A) (K := K) (L := L) H x hx
  · rintro ⟨y, rfl⟩
    have hyIntegralB : IsIntegral A (algebraMap B[H] B y) := by
      exact
        (Subalgebra.isIntegral_iff (S := B[H])).mp
          (fixedSubalgebra_isIntegral (A := A) (K := K) (L := L) H)
          y y.2
    have hyIntegralFixed : IsIntegral A y := by
      exact IsIntegral.tower_bot (FaithfulSMul.algebraMap_injective B[H] B) hyIntegralB
    -- Map integrality of `y ∈ B^H` along the canonical inclusion into `L^H`.
    simpa using IsIntegral.map (fixedSubalgebraToFixedField H) hyIntegralFixed

variable (m : Ideal (integralClosure A L))

local notation "I" => m.inertia Gal(L / K)

/-- Lemma 15.113.8 (1): the inertia fixed subalgebra `B^I` is the integral closure of `A` in the
inertia fixed field `L^I`. -/
theorem inertiaFixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[I] A L[I] :=
  fixedSubalgebra_isIntegralClosure I

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L

/-- Helper for Lemma 15.113.8: the Galois group acts on the integral closure through the ambient
field action. -/
private local instance integralClosure_mulSemiringAction :
    MulSemiringAction G B :=
  IsIntegralClosure.MulSemiringAction A K L B

/-- Helper for Lemma 15.113.8: the ambient Galois action on the integral closure is `A`-linear. -/
private local instance integralClosure_smulCommClass_dvr :
    SMulCommClass G A B where
  smul_comm g a b := by
    -- The restricted action fixes `A`-scalars because `galRestrict` is an `A`-algebra equivalence.
    have hfix : (galRestrict A K L B g) (algebraMap A B a) = algebraMap A B a := by
      simpa using (galRestrict A K L B g).commutes a
    rw [Algebra.smul_def, Algebra.smul_def]
    change
      (galRestrict A K L B g) ((algebraMap A B a : B) * b) =
        (algebraMap A B a : B) * (galRestrict A K L B g b)
    rw [map_mul, hfix]

local notation "B[" H "]" => FixedPoints.subalgebra A B H

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "I" => m.inertia G
local notation "mI" => m.under B[I]

/-- Helper for Lemma 15.113.8: the induced action on ideals of the integral closure is the
pointwise action coming from the Galois action on `B`. -/
private local instance integralClosure_ideal_mulAction :
    MulAction G (Ideal B) :=
  inferInstance

/-- Helper for Lemma 15.113.8: the restricted inertia action still commutes with the `A`-scalar
action on the integral closure. -/
private local instance inertia_smulCommClass :
    SMulCommClass I A B where
  smul_comm g a b := by
    -- This is the ambient `G`-linearity specialized to the subgroup `I`.
    exact smul_comm (((g : I) : G)) a b

/-- Helper for Lemma 15.113.8: the inertia action on the integral closure is `B^I`-linear. -/
private instance inertiaFixedSubalgebra_smulCommClass :
    SMulCommClass I B[I] B where
  smul_comm g x r := by
    -- Fixed scalars from `B^I` commute with the restricted inertia action on `B`.
    change (((g : I) : G) • ((x : B) * r)) = (x : B) * (((g : I) : G) • r)
    rw [smul_mul']
    simpa using congrArg (fun t : B ↦ t * (((g : I) : G) • r)) (x.2 g)

/-- Helper for Lemma 15.113.8: the integral closure is invariant over the inertia fixed
subalgebra. -/
private instance inertiaFixedSubalgebra_isInvariant :
    Algebra.IsInvariant B[I] B I where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- Helper for Lemma 15.113.8: every maximal ideal of the integral closure lies over the maximal
ideal of the base discrete valuation ring. -/
private instance liesOver_maximalIdeal_of_isMaximal :
    m.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/-- Helper for Lemma 15.113.8: the contracted inertia ideal lies over the maximal ideal of the
base discrete valuation ring. -/
private instance inertiaContractedIdeal_liesOver_maximalIdeal :
    Ideal.LiesOver mI (maximalIdeal A) :=
  ⟨by
    -- Compare the contraction to `A` through the inclusion `B[I] ↪ B`.
    change maximalIdeal A = Ideal.comap ((algebraMap B[I] B).comp (algebraMap A B[I])) m
    simpa using (Ideal.over_def m (maximalIdeal A))⟩

/-- Helper for Lemma 15.113.8: the maximal ideal `m` is the unique prime of `B` lying over its
inertia contraction `m ∩ B^I`. -/
private theorem integralClosure_maximalIdeal_unique_prime_over_inertia_contracted_ideal
    (q : Ideal.primesOver mI B) :
    (q : Ideal B) = m := by
  -- Use invariant-theoretic prime transitivity over the fixed subalgebra `B^I`.
  have hm_lies : m.LiesOver mI := by
    simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[I]))
  have hunder : (q : Ideal B).under B[I] = m.under B[I] := by
    exact
      (Ideal.over_def (P := (q : Ideal B)) (p := mI)).symm.trans
        (Ideal.over_def (P := m) (p := mI))
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq B[I] B I (q : Ideal B) m hunder
  have hfix_inv : ((((σ : I) : G)⁻¹) • m : Ideal B) = m := by
    exact MulAction.mem_stabilizer_iff.mp ((Ideal.inertia_le_stabilizer m) (σ⁻¹).2)
  -- Route correction: rewrite `q` as `σ⁻¹ • (σ • q)` and then use the transitivity equality.
  have hq : (q : Ideal B) = (((σ⁻¹ : I) : G) • m : Ideal B) := by
    calc
      (q : Ideal B) = ((((σ : I) : G)⁻¹ * ((σ : I) : G)) • (q : Ideal B)) := by
        rw [show ((((σ : I) : G)⁻¹ * ((σ : I) : G)) : G) = 1 by simp, one_smul]
      _ = (((σ⁻¹ : I) : G) • ((((σ : I) : G) • (q : Ideal B) : Ideal B))) := by
        simp [smul_smul]
      _ = (((σ⁻¹ : I) : G) • m : Ideal B) := by
        exact congrArg (fun J : Ideal B ↦ (((σ⁻¹ : I) : G) • J : Ideal B)) hσ.symm
  simpa [hfix_inv] using hq

/-- Helper for Lemma 15.113.8: each inertia element stabilizes the chosen maximal ideal `m`. -/
private theorem inertia_ideal_stable
    (g : I) :
    (((g : I) : G) • m : Ideal B) = m := by
  -- This is the defining stabilizer property built into the inertia subgroup.
  exact MulAction.mem_stabilizer_iff.mp ((Ideal.inertia_le_stabilizer m) g.2)

/-- Helper for Lemma 15.113.8: membership in an inertia group is the pointwise congruence
criterion modulo the chosen ideal. -/
private theorem mem_inertia_iff_sub_mem
    (J : Ideal B) (σ : G) :
    σ ∈ Ideal.inertia G J ↔ ∀ x : B, σ • x - x ∈ J := by
  -- This is just the defining shape of the owner `Ideal.inertia`.
  rfl

/-- Helper for Lemma 15.113.8: the quotient `B / m` carries the induced inertia action because
every inertia element stabilizes `m`. -/
private noncomputable abbrev inertiaQuotientAction :
    MulSemiringAction I (B ⧸ m) := by
  let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
  exact @quotientMulSemiringAction B I inferInstance inferInstance inferInstance m hstable

/-- Helper for Lemma 15.113.8: the induced inertia action on `B ⧸ m` is available as a section
instance. -/
private local instance inertia_quotient_mulSemiringAction :
    MulSemiringAction I (B ⧸ m) :=
  inertiaQuotientAction (m := m)

/-- Helper for Lemma 15.113.8: the inertia fixed subalgebra `B^I` is integral over `A` because it
is a subalgebra of the ambient integral closure. -/
private theorem inertiaFixedSubalgebra_isIntegral :
    Algebra.IsIntegral A B[I] := by
  -- Restrict integrality from the ambient integral closure `B` to its fixed subalgebra `B^I`.
  rw [Subalgebra.isIntegral_iff]
  intro x hx
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  exact Algebra.IsIntegral.isIntegral x

/-- Helper for Lemma 15.113.8: the contracted ideal `mI = m ∩ B^I` is maximal because `B^I` is
integral over the base discrete valuation ring `A`. -/
private theorem inertiaContractedIdeal_isMaximal :
    (mI : Ideal B[I]).IsMaximal := by
  letI : Algebra.IsIntegral A B[I] :=
    inertiaFixedSubalgebra_isIntegral (A := A) (K := K) (L := L) (m := m)
  letI : (mI : Ideal B[I]).IsPrime := by
    -- The contracted ideal is prime because it is the comap of the maximal ideal `m`.
    simpa [Ideal.under_def] using
      (Ideal.comap_isPrime (algebraMap B[I] B) m :
        (Ideal.comap (algebraMap B[I] B) m).IsPrime)
  have hcomap_max :
      (Ideal.comap (algebraMap A B[I]) (mI : Ideal B[I])).IsMaximal := by
    -- Rewrite the double contraction to the already-known maximal contraction of `m` to `A`.
    change (Ideal.comap (algebraMap A B[I]) (Ideal.comap (algebraMap B[I] B) m)).IsMaximal
    simpa [Ideal.under_def, RingHom.comp_assoc] using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m :
        (Ideal.comap (algebraMap A B) m).IsMaximal)
  exact
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (mI : Ideal B[I]) hcomap_max

/-- Helper for Lemma 15.113.8: the quotient of the inertia fixed subalgebra by
`m ∩ B^I = mI` maps bijectively to the residue field `κ(mI)`. -/
private noncomputable abbrev inertiaContractedIdeal_quotient_equiv_residueField :
    B[I] ⧸ mI ≃+* Ideal.ResidueField mI := by
  -- Install the maximality of `mI = m ∩ B^I` through the source integral-closure statement.
  letI : (mI : Ideal B[I]).IsMaximal := inertiaContractedIdeal_isMaximal (A := A) (K := K) (L := L) (m := m)
  exact
    RingEquiv.ofBijective
      (algebraMap (B[I] ⧸ mI) (Ideal.ResidueField mI))
      (Ideal.bijective_algebraMap_quotient_residueField mI)

/-- Helper for Lemma 15.113.8: the canonical fixed-points quotient map for the inertia action
already has purely inseparable residue-field extensions before identifying the codomain with
`B / m`. -/
private theorem inertia_fixed_points_quotient_has_purely_inseparable_residue_field_extensions :
    let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
    letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
    (@fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
      hstable).HasPurelyInseparableResidueFieldExtensions :=
  by
  -- This is the source Step 2 owner theorem specialized to the inertia action on `B`.
  let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
  letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
  exact
    @fixedPointsQuotient_hasPurelyInseparableResidueFieldExtensions B I
      inferInstance inferInstance inferInstance inferInstance m hstable

/-- Helper for Lemma 15.113.8: every inertia element defines a stabilizer element for the
restricted `I`-action on the maximal ideal `m`. -/
private def inertia_stabilizer
    (σ : I) : MulAction.stabilizer I m :=
  ⟨σ, by
    -- Inertia stabilizes the chosen maximal ideal by definition.
    exact inertia_ideal_stable (m := m) σ⟩

/-- Helper for Lemma 15.113.8: the restricted inertia action on the quotient `B ⧸ m` is trivial.
-/
private theorem inertia_quotient_action_trivial
    (σ : I) :
    Ideal.Quotient.stabilizerHom m mI I (inertia_stabilizer (m := m) σ) = 1 := by
  -- After the `#print` probe, the quotient-level owner is explicit: it is enough to compare both
  -- sides on quotient classes and use the defining congruence condition for inertia.
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk m (((σ : I) : G) • a) = Ideal.Quotient.mk m a
  rw [Ideal.Quotient.eq]
  exact (mem_inertia_iff_sub_mem (A := A) (K := K) (L := L) (J := m) ((σ : I) : G)).mp σ.2 a

/-- Helper for Lemma 15.113.8: for the restricted `I`-action, every stabilizer element of `m`
comes from the underlying inertia element. -/
private theorem inertia_stabilizer_eq
    (σ : MulAction.stabilizer I m) :
    σ = inertia_stabilizer (m := m) σ.1 := by
  -- The restricted action already fixes `m`, so the stabilizer subtype is propositionally the
  -- same data as `I`.
  ext
  rfl

/-- Helper for Lemma 15.113.8: after restricting from `G` to `I`, the induced stabilizer action on
the quotient field `B ⧸ m` is still trivial. -/
private theorem inertia_quotient_stabilizer_action_trivial
    (σ : MulAction.stabilizer I m) :
    Ideal.Quotient.stabilizerHom m mI I σ = 1 := by
  -- Replace the stabilizer element by its underlying inertia element and reuse quotient triviality.
  rw [inertia_stabilizer_eq (m := m) σ]
  exact inertia_quotient_action_trivial (A := A) (K := K) (L := L) (m := m) σ.1

/-- Helper for Lemma 15.113.8: because inertia acts trivially on `B ⧸ m`, the fixed subring of
the quotient identifies with the whole quotient ring. -/
private noncomputable abbrev inertia_quotient_fixed_subring_equiv :
    FixedPoints.subring (B ⧸ m) I ≃+* (B ⧸ m) := by
  -- The inclusion is bijective: injectivity is by subtype, and surjectivity uses the pointwise
  -- triviality of the inertia action on quotient classes.
  refine RingEquiv.ofBijective (FixedPoints.subring (B ⧸ m) I).subtype ?_
  constructor
  · intro x y hxy
    exact Subtype.ext hxy
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro σ
    -- Reduce to quotient classes represented by elements of `B`, then use the defining inertia
    -- congruence modulo `m`.
    refine Quotient.inductionOn' x (fun a ↦ ?_)
    change Ideal.Quotient.mk m (((σ : I) : G) • a) = Ideal.Quotient.mk m a
    rw [Ideal.Quotient.eq]
    exact (mem_inertia_iff_sub_mem (A := A) (K := K) (L := L) (J := m) ((σ : I) : G)).mp σ.2 a

/-- Helper for Lemma 15.113.8: the fixed subring of `B ⧸ m` is a domain because it identifies
with the residue field `B ⧸ m`. -/
private local instance inertia_quotient_fixed_subring_isDomain :
    IsDomain (FixedPoints.subring (B ⧸ m) I) :=
  Function.Injective.isDomain
    (inertia_quotient_fixed_subring_equiv (m := m))
    (EquivLike.injective _)

/-- Helper for Lemma 15.113.8: the residue field at the zero prime of a field is canonically the
field itself. -/
private noncomputable abbrev bot_residueField_ringEquiv
    (F : Type*) [Field F] :
    Ideal.ResidueField (⊥ : Ideal F) ≃+* (F ⧸ (⊥ : Ideal F)) :=
  (RingEquiv.ofBijective
    (algebraMap (F ⧸ (⊥ : Ideal F)) (Ideal.ResidueField (⊥ : Ideal F)))
    (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal F))).symm

/-- Helper for Lemma 15.113.8: the zero-prime residue field of a field is canonically the field
itself as an algebra over that field. -/
private noncomputable abbrev bot_residueField_algEquiv
    (F : Type*) [Field F] :
    F ≃ₐ[F] Ideal.ResidueField (⊥ : Ideal F) := by
  -- First identify `F` with the quotient `F / (0)`, then use the quotient-to-residue-field
  -- equivalence at the zero ideal.
  let eQuot : F ≃ₐ[F] (F ⧸ (⊥ : Ideal F)) :=
    (AlgEquiv.quotientBot F F).symm
  let eResidue : (F ⧸ (⊥ : Ideal F)) ≃ₐ[F] Ideal.ResidueField (⊥ : Ideal F) :=
    AlgEquiv.ofRingEquiv (f := (bot_residueField_ringEquiv F).symm) (by
      intro x
      rfl)
  exact eQuot.trans eResidue

/-- Helper for Lemma 15.113.8: for any domain, the quotient by the zero ideal identifies with the
residue field at `⊥`. -/
private noncomputable abbrev bot_quotient_equiv_residueField
    (R : Type*) [CommRing R] [IsDomain R] :
    R ⧸ (⊥ : Ideal R) ≃+* Ideal.ResidueField (⊥ : Ideal R) := by
  exact
    RingEquiv.ofBijective
      (algebraMap (R ⧸ (⊥ : Ideal R)) (Ideal.ResidueField (⊥ : Ideal R)))
      (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal R))

/-- Helper for Lemma 15.113.8: for any domain, the zero-prime residue field is canonically the
domain itself. -/
private noncomputable abbrev bot_domain_algEquiv_residueField
    (R : Type*) [CommRing R] [IsDomain R] :
    R ≃ₐ[R] Ideal.ResidueField (⊥ : Ideal R) := by
  let eQuot : R ≃ₐ[R] (R ⧸ (⊥ : Ideal R)) :=
    (AlgEquiv.quotientBot R R).symm
  let eResidue : (R ⧸ (⊥ : Ideal R)) ≃ₐ[R] Ideal.ResidueField (⊥ : Ideal R) :=
    AlgEquiv.ofRingEquiv (f := bot_quotient_equiv_residueField R) (by
      intro x
      rfl)
  exact eQuot.trans eResidue

/-- Helper for Lemma 15.113.8: the quotient `B / m` maps bijectively to the residue field
`κ(m)`. -/
private noncomputable abbrev integralClosure_maximalIdeal_quotient_equiv_residueField :
    B ⧸ m ≃+* m.ResidueField := by
  -- Maximality of `m` identifies the quotient ring with the corresponding residue field.
  exact
    RingEquiv.ofBijective
      (algebraMap (B ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)

/-- Helper for Lemma 15.113.8: after identifying the fixed quotient with `B ⧸ m`, the fixed-points
quotient map is the canonical quotient algebra map. -/
private theorem fixedPointsQuotient_comp_eq_algebraMap :
    let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
    letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
    let f : B[I] ⧸ mI →+* FixedPoints.subring (B ⧸ m) I :=
      @fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
        hstable
    (inertia_quotient_fixed_subring_equiv (m := m)).toRingHom.comp f =
      algebraMap (B[I] ⧸ mI) (B ⧸ m) := by
  let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
  letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
  let f : B[I] ⧸ mI →+* FixedPoints.subring (B ⧸ m) I :=
    @fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
      hstable
  -- Compare both quotient maps on representatives from `B^I`.
  apply Ideal.Quotient.ringHom_ext
  ext x
  change ((f (Ideal.Quotient.mk mI x) : FixedPoints.subring (B ⧸ m) I) : B ⧸ m) =
      Ideal.Quotient.mk m x
  rw [fixedPointsQuotientToQuotientFixedPoints_mk]
  rfl

/-- Helper for Lemma 15.113.8: after identifying the bottom residue fields with the corresponding
zero quotients and forgetting the fixed-subring structure on the codomain, the specialized
residue-field map is the canonical quotient map `B^I / mI → B / m`. -/
private theorem bottom_residueField_map_eq_canonical_quotient_map :
    let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
    letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
    let Fix := FixedPoints.subring (B ⧸ m) I
    let f : B[I] ⧸ mI →+* Fix :=
      @fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
        hstable
    let hp : Ideal.comap f (⊥ : Ideal Fix) = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot]
      simpa [f] using
        (fixedPointsQuotient_ker_eq_bot (R := B) (G := I) (I := m) hstable)
    let fκ :
        Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)) →+*
          Ideal.ResidueField (⊥ : Ideal Fix) :=
      Ideal.ResidueField.map (⊥ : Ideal (B[I] ⧸ mI)) (⊥ : Ideal Fix) f hp
    (((inertia_quotient_fixed_subring_equiv (m := m)).toRingHom).comp
        ((bot_domain_algEquiv_residueField Fix).symm.toRingHom)).comp fκ =
      (algebraMap (B[I] ⧸ mI) (B ⧸ m)).comp
        ((bot_domain_algEquiv_residueField (B[I] ⧸ mI)).symm.toRingHom) := by
  let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
  letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
  let Fix := FixedPoints.subring (B ⧸ m) I
  let f : B[I] ⧸ mI →+* Fix :=
    @fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
      hstable
  let hp : Ideal.comap f (⊥ : Ideal Fix) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    simpa [f] using
      (fixedPointsQuotient_ker_eq_bot (R := B) (G := I) (I := m) hstable)
  let fκ :
      Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)) →+*
        Ideal.ResidueField (⊥ : Ideal Fix) :=
    Ideal.ResidueField.map (⊥ : Ideal (B[I] ⧸ mI)) (⊥ : Ideal Fix) f hp
  -- Compare the two residue-field maps on scalars from `B^I / mI`.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  rw [RingHom.comp_assoc, RingHom.comp_assoc, Ideal.ResidueField.map_algebraMap]
  simp [bot_domain_algEquiv_residueField, bot_quotient_equiv_residueField,
    fixedPointsQuotient_comp_eq_algebraMap (A := A) (K := K) (L := L) (m := m), f]

/-- Helper for Lemma 15.113.8: the canonical quotient map `B^I / mI → B / m` and the canonical
residue-field map `κ(mI) → κ(m)` agree after the standard quotient-to-residue-field
identifications. -/
private theorem quotient_residueField_transport_commutes :
    (integralClosure_maximalIdeal_quotient_equiv_residueField (m := m)).toRingHom.comp
        (algebraMap (B[I] ⧸ mI) (B ⧸ m)) =
      (Ideal.ResidueField.map mI m (algebraMap B[I] B) (Ideal.over_def m mI)).comp
        (inertiaContractedIdeal_quotient_equiv_residueField (m := m)).toRingHom := by
  -- Compare both maps on representatives coming from `B^I`.
  apply Ideal.Quotient.ringHom_ext
  ext x
  rw [RingHom.comp_assoc, Ideal.ResidueField.map_algebraMap]
  rfl

/-- Helper for Lemma 15.113.8: the quotient-field extension `(B^I / mI) → (B / m)` is purely
inseparable. This is the invariant-theory Step 2 route before transporting from quotients to the
residue-field models. -/
private theorem inertia_fixed_subalgebra_quotient_isPurelyInseparable :
    let F := B[I] ⧸ mI
    let E := B ⧸ m
    IsPurelyInseparable F E := by
  let hstable : ∀ g : I, g • m = m := fun h ↦ inertia_ideal_stable (m := m) h
  letI : MulSemiringAction I (B ⧸ m) := inertiaQuotientAction (m := m)
  let Fix := FixedPoints.subring (B ⧸ m) I
  let f : B[I] ⧸ mI →+* Fix :=
    @fixedPointsQuotientToQuotientFixedPoints B I inferInstance inferInstance inferInstance m
      hstable
  let hp : Ideal.comap f (⊥ : Ideal Fix) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    simpa [f] using
      (fixedPointsQuotient_ker_eq_bot (R := B) (G := I) (I := m) hstable)
  let fκ :
      Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)) →+*
        Ideal.ResidueField (⊥ : Ideal Fix) :=
    Ideal.ResidueField.map (⊥ : Ideal (B[I] ⧸ mI)) (⊥ : Ideal Fix) f hp
  have hpiResidue :
      IsPurelyInseparable
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)))
        (Ideal.ResidueField (⊥ : Ideal Fix)) := by
    -- Source Step 2: specialize the owner theorem at the bottom prime of the fixed quotient.
    let hpure :=
      inertia_fixed_points_quotient_has_purely_inseparable_residue_field_extensions
        (A := A) (K := K) (L := L) (m := m)
    simpa [Fix, f, hp, fκ] using (hpure (q := (⊥ : PrimeSpectrum Fix)))
  let g :
      Ideal.ResidueField (⊥ : Ideal Fix) →+* (B ⧸ m) :=
    ((inertia_quotient_fixed_subring_equiv (m := m)).toRingHom).comp
      ((bot_domain_algEquiv_residueField Fix).symm.toRingHom)
  letI :
      Algebra (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI))) (B ⧸ m) :=
    (g.comp fκ).toAlgebra
  let eTop : (B ⧸ m) ≃ₐ[Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI))]
      Ideal.ResidueField (⊥ : Ideal Fix) :=
    AlgEquiv.ofRingEquiv
      (f := ((inertia_quotient_fixed_subring_equiv (m := m)).symm.toRingEquiv).trans
        (bot_domain_algEquiv_residueField Fix).toRingEquiv)
      (by
        ext x
        simp [g])
  have hpiBottom :
      IsPurelyInseparable
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)))
        (B ⧸ m) :=
    (eTop.isPurelyInseparable_iff).2 hpiResidue
  letI :
      Algebra (B[I] ⧸ mI)
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI))) :=
    ((bot_domain_algEquiv_residueField (B[I] ⧸ mI)).toRingHom).toAlgebra
  letI : Algebra (B[I] ⧸ mI) (B ⧸ m) :=
    (algebraMap (B[I] ⧸ mI) (B ⧸ m)).toAlgebra
  letI :
      IsScalarTower (B[I] ⧸ mI)
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)))
        (B ⧸ m) :=
    IsScalarTower.of_algebraMap_eq' <|
      bottom_residueField_map_eq_canonical_quotient_map
        (A := A) (K := K) (L := L) (m := m)
  have hpiSource :
      IsPurelyInseparable
        (B[I] ⧸ mI)
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI))) := by
    -- The bottom residue field of `B^I / mI` is canonically the field itself.
    exact AlgEquiv.isPurelyInseparable (bot_domain_algEquiv_residueField (B[I] ⧸ mI))
  letI :
      IsPurelyInseparable
        (B[I] ⧸ mI)
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI))) :=
    hpiSource
  letI :
      IsPurelyInseparable
        (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)))
        (B ⧸ m) :=
    hpiBottom
  -- Source Step 2 concludes by composing the trivial bottom-residue identification with the
  -- purely inseparable fixed-points quotient map.
  exact IsPurelyInseparable.trans
    (B[I] ⧸ mI)
    (Ideal.ResidueField (⊥ : Ideal (B[I] ⧸ mI)))
    (B ⧸ m)

/-- Helper for Lemma 15.113.8: the residue-field extension `κ(m) / κ(m ∩ B^I)` is purely
inseparable. -/
private theorem inertia_fixed_subalgebra_residueField_isPurelyInseparable :
    let κI := Ideal.ResidueField mI
    let κm := m.ResidueField
    IsPurelyInseparable κI κm := by
  have hquot :
      IsPurelyInseparable (B[I] ⧸ mI) (B ⧸ m) :=
    inertia_fixed_subalgebra_quotient_isPurelyInseparable
      (A := A) (K := K) (L := L) (m := m)
  let κI := Ideal.ResidueField mI
  let κm := m.ResidueField
  let eI : (B[I] ⧸ mI) ≃+* κI :=
    inertiaContractedIdeal_quotient_equiv_residueField (m := m)
  let eM : (B ⧸ m) ≃+* κm :=
    integralClosure_maximalIdeal_quotient_equiv_residueField (m := m)
  letI : Algebra κI (B[I] ⧸ mI) := eI.symm.toRingHom.toAlgebra
  let eSource : (B[I] ⧸ mI) ≃ₐ[κI] κI :=
    AlgEquiv.ofRingEquiv
      (f := eI)
      (by
        ext x
        simp)
  have hpiSource :
      IsPurelyInseparable κI (B[I] ⧸ mI) :=
    (eSource.isPurelyInseparable_iff).2 inferInstance
  letI : Algebra (B[I] ⧸ mI) (B ⧸ m) :=
    (algebraMap (B[I] ⧸ mI) (B ⧸ m)).toAlgebra
  letI : Algebra κI (B ⧸ m) :=
    ((algebraMap (B[I] ⧸ mI) (B ⧸ m)).comp eI.symm.toRingHom).toAlgebra
  letI :
      IsScalarTower κI (B[I] ⧸ mI) (B ⧸ m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsPurelyInseparable κI (B[I] ⧸ mI) := hpiSource
  letI : IsPurelyInseparable (B[I] ⧸ mI) (B ⧸ m) := hquot
  have hpiMiddle :
      IsPurelyInseparable κI (B ⧸ m) :=
    IsPurelyInseparable.trans κI (B[I] ⧸ mI) (B ⧸ m)
  letI : Algebra κI κm :=
    (Ideal.ResidueField.map mI m (algebraMap B[I] B) (Ideal.over_def m mI)).toAlgebra
  let eTarget : (B ⧸ m) ≃ₐ[κI] κm :=
    AlgEquiv.ofRingEquiv
      (f := eM)
      (by
        rw [RingHom.comp_assoc, quotient_residueField_transport_commutes (A := A) (K := K)
          (L := L) (m := m)]
        simp)
  -- Transport the quotient-level purely inseparable extension across the residue-field
  -- identifications for `mI` and `m`.
  exact (eTarget.isPurelyInseparable_iff).1 hpiMiddle

-- Proof sketch: let `m' = B^I ∩ m`. Show that the extension of discrete valuation rings
-- `A → (B^I)_{m'}` is weakly unramified and has separable residue-field extension, then apply the
-- étale criterion of Lemma `10.143.7`.
/-- Lemma 15.113.8 (2): if `m' = B^I ∩ m`, then `A → (B^I)_{m'}` is étale, expressed as the
statement that `A → B^I` is étale at the prime `m'`. -/
theorem inertiaFixedSubalgebra_isEtaleAt_under
    : IsEtaleAt A (m.under B[I]) := by
  -- TODO for Lemma 15.113.8: finish the source-faithful valuation-counting endgame after the new
  -- quotient-field pivot. The stabilized frontier is now:
  -- 1. the canonical quotient purity `(B^I / mI) → (B / m)`,
  -- 2. the concrete residue-field purity `κ(mI) → κ(m)`, and
  -- 3. the unique-prime statement over `mI = m ∩ B^I`.
  -- The remaining work is the source valuation-counting endgame: construct the faithful `D / I`
  -- action on `κ(mI)`, combine it with the localized branch formulas to force ramification index
  -- `1`, deduce separability of `κ(mI) / κ(A)`, and then apply Lemma `10.143.7`.
  sorry

end
