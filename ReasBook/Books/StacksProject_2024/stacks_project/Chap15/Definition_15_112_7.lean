import Mathlib
import Mathlib.NumberTheory.RamificationInertia.Ramification
import StacksProject_2024.stacks_project.Chap10.Lemma_10_120_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing

section

/-- A natural number is prime to the residue characteristic of a local ring `A` if it is coprime
to every prime realizing the characteristic of the residue field of `A`. -/
def PrimeToResidueCharacteristic
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p], Nat.Coprime n p

end

section

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]

local instance (P : Ideal (integralClosure A L)) [P.IsMaximal] : P.IsPrime :=
  Ideal.IsMaximal.isPrime inferInstance

/-
Domain-style sampling for Definition 15.112.7:
- primary domain: ramification theory for finite separable extensions of the fraction field of a
  discrete valuation ring, measured on maximal ideals of the integral closure;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Ideal.ramificationIdx`,
  `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`;
- best owner abstraction: the integral-closure branches above `maximalIdeal A`, with the canonical
  branchwise owner `Algebra.IsUnramifiedAt A P` supplying the primitive local unramified data once
  the branch algebra is known to be essentially of finite type over `A`, and the ideal-theoretic
  ramification owner `Ideal.ramificationIdx` supplying the derived equality `ramificationIdx = 1`;
- primitive-vs-derived split: tame ramification carries the residue-separability and prime-to-
  residue-characteristic branch conditions, while unramified stores only the stronger canonical
  branchwise owner and derives those tame consequences from it; the ambient
  `A → FractionRing A → L` tower is primitive because the source definition is about extensions
  `L / FractionRing A`, while the finite separable fraction-field hypotheses belong to the
  downstream bridge that makes `integralClosure A L` essentially of finite type over `A`.

Source/core/bridge triage:
- `source-facing`: `IsUnramifiedWithRespectTo`, `IsTamelyRamifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`;
- `core/canonical`: `integralClosure A L`, `Algebra.IsUnramifiedAt`, `Ideal.ramificationIdx`, and
  the induced residue-field map;
- `bridge/view`: the finite-extension bridge furnishing `Module.Finite` and `EssFiniteType` on
  `integralClosure A L`.
-/

/-- Definition 15.112.7 (2): the finite separable extension `L / FractionRing A` is tamely
ramified with respect to the discrete valuation ring `A` if the residue-field extensions above
`maximalIdeal A` are separable and every ramification index is prime to the residue characteristic
of `A`; when `κA = Ideal.ResidueField (maximalIdeal A)` has characteristic `0`, the coprimality
condition is vacuous. -/
class IsTamelyRamifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
      let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
        ResidueField.instAlgebra
      Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) P.ResidueField
  ramificationIdx_coprime (q : ℕ) [_hq : Fact q.Prime]
      [CharP (Ideal.ResidueField (maximalIdeal A)) q]
      (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
      Nat.Coprime (ramificationIdx (maximalIdeal A) P) q

/-- Definition 15.112.7 (1): the finite separable extension `L / FractionRing A` is unramified
with respect to the discrete valuation ring `A` if for every maximal ideal of
`B = integralClosure A L` above `maximalIdeal A`, the ramification index is `1` and the induced
residue-field extension is separable. The bridge to the canonical owner
`Algebra.IsUnramifiedAt A P` is derived only under the finite-type hypotheses needed by that
owner. -/
class IsUnramifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
      let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
        ResidueField.instAlgebra
      Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) P.ResidueField
  ramificationIdx_eq_one (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      ramificationIdx (maximalIdeal A) P = 1

section FractionFieldExtension

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

omit [Algebra.IsSeparable (FractionRing A) L] in
instance integralClosure_moduleFinite : Module.Finite A (integralClosure A L) :=
  IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)

omit [Algebra.IsSeparable (FractionRing A) L] in
instance integralClosure_essFiniteType : Algebra.EssFiniteType A (integralClosure A L) := by
  infer_instance

namespace IsUnramifiedWithRespectTo

/-- Helper for Definition 15.112.7: a discrete valuation ring is not a field, so the Dedekind
package on its finite integral closure is available in the fraction-field extension section. -/
private theorem not_isField_base : ¬ IsField A := by
  -- The source route needs the nonfield hypothesis to install the Dedekind owner on the
  -- integral closure.
  intro hA
  exact IsDiscreteValuationRing.not_a_field A
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hA)

/-- The source-facing unramified branch data recover the canonical owner
`Algebra.IsUnramifiedAt A P` once the finite/separable fraction-field hypotheses put the integral
closure in the Dedekind setting used by the ramification theorem. -/
theorem isUnramifiedAt (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] [h : _root_.IsUnramifiedWithRespectTo A L] :
    Algebra.IsUnramifiedAt A P := by
  let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
    ResidueField.instAlgebra
  letI : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing A) L
  letI : IsDedekindDomain (integralClosure A L) :=
    integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
      (IsPrincipalIdealRing.ringKrullDim_eq_one A not_isField_base)
  letI : Module.IsTorsionFree A L := .trans_faithfulSMul A (FractionRing A) L
  letI : Module.IsTorsionFree A (integralClosure A L) := IsIntegralClosure.isTorsionFree A L
  -- Route correction: use the source proof's Dedekind-domain bridge from `e = 1` to the
  -- localized maximal-ideal equality, instead of the earlier over-generalized finite-type route.
  refine (Algebra.isUnramifiedAt_iff_map_eq A (maximalIdeal A) P).2 ⟨?_, ?_⟩
  · -- The residue-field separability hypothesis is already part of the source-facing data.
    simpa using h.residueField_separable P
  · -- The ramification-index hypothesis becomes the localized maximal-ideal equality in the
    -- Dedekind owner package.
    have hP_ne_bot : P ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) P
    have hmap_le : (maximalIdeal A).map (algebraMap A (integralClosure A L)) ≤ P := by
      refine Ideal.map_le_iff_le_comap.mpr ?_
      simpa [P.over_def (maximalIdeal A)]
    exact
      (Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff
        (p := maximalIdeal A) (P := P) hP_ne_bot hmap_le).mp
        (h.ramificationIdx_eq_one P)

/-- Under the finite/separable fraction-field bridge, the source-facing unramified predicate is
equivalent to the branchwise canonical owner `Algebra.IsUnramifiedAt`. -/
theorem iff_isUnramifiedAt :
    _root_.IsUnramifiedWithRespectTo A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt A P := by
  constructor
  · intro h P _ _
    -- The forward implication is the branchwise bridge just proved in the Dedekind section.
    letI : _root_.IsUnramifiedWithRespectTo A L := h
    exact isUnramifiedAt (A := A) (L := L) P
  · intro h
    -- The reverse implication reads the source-facing branch conditions off the canonical owner.
    refine
      { residueField_separable := ?_
        ramificationIdx_eq_one := ?_ }
    · intro P _ _
      let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
        ResidueField.instAlgebra
      exact (Algebra.isUnramifiedAt_iff_map_eq A (maximalIdeal A) P).mp (h P) |>.1
    · intro P _ _
      letI : Algebra.IsUnramifiedAt A P := h P
      letI : Module.IsTorsionFree A L := .trans_faithfulSMul A (FractionRing A) L
      letI : Module.IsTorsionFree A (integralClosure A L) := IsIntegralClosure.isTorsionFree A L
      have hP_ne_bot : P ≠ ⊥ :=
        Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) P
      simpa [P.over_def (maximalIdeal A)] using
        (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
          (R := A) (S := integralClosure A L) (p := P) hP_ne_bot)

end IsUnramifiedWithRespectTo

instance [h : IsUnramifiedWithRespectTo A L] : IsTamelyRamifiedWithRespectTo A L := by
  refine
    { residueField_separable := ?_
      ramificationIdx_coprime := ?_ }
  · intro P _ _
    letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
    letI : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
      ResidueField.instAlgebra
    simpa using h.residueField_separable P
  · intro p _ _ P _ _
    have hramification : ramificationIdx (maximalIdeal A) P = 1 := h.ramificationIdx_eq_one P
    simpa [hramification]

end FractionFieldExtension

/-- Definition 15.112.7 (3): the finite separable extension `L / FractionRing A` is totally
ramified with respect to the discrete valuation ring `A` if there is a unique maximal ideal of
`B = integralClosure A L` above `maximalIdeal A` and the induced residue-field extension over
`κA = Ideal.ResidueField (maximalIdeal A)` is trivial; existence of a maximal ideal above
`maximalIdeal A` is ambiently supplied by lying-over for `integralClosure A L`. -/
class IsTotallyRamifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  unique_maximalIdeal (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)] :
      P = Q
  residueField_bijective (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
          (P.over_def (maximalIdeal A)))

/-- Helper for Definition 15.112.7: the integral closure of a discrete valuation ring inside its
own fraction field is the bottom subalgebra. -/
@[simp] lemma integralClosure_fractionRing_eq_bot :
    integralClosure A (FractionRing A) = ⊥ := by
  -- A discrete valuation ring is integrally closed, so the integral closure collapses to the
  -- base copy inside the fraction field.
  simpa using
    (IsIntegrallyClosed.integralClosure_eq_bot A (FractionRing A) :
      integralClosure A (FractionRing A) = ⊥)

/-- Helper for Definition 15.112.7: after collapsing the integral closure of `A` in its own
fraction field, one obtains a canonical `A`-algebra equivalence back to `A`. -/
noncomputable def integralClosure_fractionRing_equiv :
    integralClosure A (FractionRing A) ≃ₐ[A] A :=
  (Subalgebra.equivOfEq (integralClosure A (FractionRing A)) ⊥
      (integralClosure_fractionRing_eq_bot (A := A))).trans
    (Algebra.botEquivOfInjective (IsFractionRing.injective A (FractionRing A)))

/-- Helper for Definition 15.112.7: the canonical collapse of the integral closure fixes the base
copy of `A`. -/
lemma integralClosure_fractionRing_equiv_apply_algebraMap (a : A) :
    integralClosure_fractionRing_equiv (A := A)
        (algebraMap A (integralClosure A (FractionRing A)) a) =
      a := by
  -- The algebra equivalence is defined over `A`, so it commutes with the structure map.
  simpa using (integralClosure_fractionRing_equiv (A := A)).commutes a

/-- Helper for Definition 15.112.7: the integral closure of `A` in its own fraction field is local,
because it is ring-equivalent to the local ring `A`. -/
lemma isLocalRing_integralClosure_fractionRing :
    IsLocalRing (integralClosure A (FractionRing A)) := by
  let e : integralClosure A (FractionRing A) ≃ₐ[A] A :=
    integralClosure_fractionRing_equiv (A := A)
  exact e.symm.toRingEquiv.isLocalRing

/-- Helper for Definition 15.112.7: in the trivial fraction-field extension, every maximal branch
above `maximalIdeal A` is the unique maximal ideal of the collapsed integral closure. -/
lemma fractionRing_branch_eq_maximalIdeal
    [IsLocalRing (integralClosure A (FractionRing A))]
    (P : Ideal (integralClosure A (FractionRing A))) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    P = maximalIdeal (integralClosure A (FractionRing A)) := by
  -- After transport to the local base ring, maximal ideals are forced to be the unique maximal
  -- ideal.
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Definition 15.112.7: the ideal residue field at the maximal ideal of a local ring
identifies with the canonical local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Definition 15.112.7: the maximal-ideal residue-field identification sends residue
classes of elements to the canonical local residue classes. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a) =
      residue R a := by
  -- Compare both sides through the inverse equivalence coming from the quotient/residue-field map.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a) by rfl]
  change
    maximalIdeal_residueField_equiv R
        ((maximalIdeal_residueField_equiv R).symm (residue R a)) =
      residue R a
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply (residue R a)

/-- Helper for Definition 15.112.7: after identifying ideal residue fields with local residue
fields, the ideal-level residue-field map becomes the canonical local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv S).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_equiv R).toRingHom := by
  -- It suffices to check the comparison on residue classes of elements of `R`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv S
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap R (maximalIdeal R).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Definition 15.112.7: a surjective local map induces a bijection on residue
fields. -/
private theorem residueField_map_bijective_of_surjective_localHom
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  let hField : Field (IsLocalRing.ResidueField S) := inferInstance
  let _ : Nontrivial (IsLocalRing.ResidueField S) := hField.toNontrivial
  constructor
  · -- The source residue field is a field, so the canonical map into a nontrivial ring is
    -- injective.
    exact RingHom.injective (IsLocalRing.ResidueField.map f)
  · -- Lift a target residue class to `S`, lift that element further to `R`, and compare residues.
    intro z
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    rcases hf s with ⟨r, rfl⟩
    refine ⟨IsLocalRing.residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

/-- Helper for Definition 15.112.7: the collapse equivalence shows that the structure map
`A → integralClosure A (FractionRing A)` is surjective. -/
private theorem integralClosure_fractionRing_algebraMap_surjective :
    Function.Surjective (algebraMap A (integralClosure A (FractionRing A))) := by
  intro b
  refine ⟨integralClosure_fractionRing_equiv (A := A) b, ?_⟩
  -- Apply the collapse equivalence to reduce to its `A`-linearity on the structure map.
  apply (integralClosure_fractionRing_equiv (A := A)).injective
  simpa using
    integralClosure_fractionRing_equiv_apply_algebraMap
      (A := A) (a := integralClosure_fractionRing_equiv (A := A) b)

/-- Helper for Definition 15.112.7: in the trivial fraction-field extension, the residue-field map
at any branch above `maximalIdeal A` is bijective. -/
lemma fractionRing_residueField_map_bijective
    (P : Ideal (integralClosure A (FractionRing A))) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) P
        (algebraMap A (integralClosure A (FractionRing A))) (P.over_def (maximalIdeal A))) := by
  let B := integralClosure A (FractionRing A)
  letI : IsLocalRing B := isLocalRing_integralClosure_fractionRing (A := A)
  letI : IsLocalHom (algebraMap A B) :=
    Function.Surjective.isLocalHom (algebraMap A B)
      (integralClosure_fractionRing_algebraMap_surjective (A := A))
  -- Route correction: normalize the branch to the unique maximal ideal first, then compare the
  -- ideal residue-field map with the canonical local residue-field map.
  have hP : P = maximalIdeal B := fractionRing_branch_eq_maximalIdeal (A := A) P
  subst P
  have hres :
      Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_bijective_of_surjective_localHom (algebraMap A B)
      (integralClosure_fractionRing_algebraMap_surjective (A := A))
  have hcomp :
      (maximalIdeal_residueField_equiv B).toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
            ((maximalIdeal B).over_def (maximalIdeal A))) =
        (IsLocalRing.ResidueField.map (algebraMap A B)).comp
          (maximalIdeal_residueField_equiv A).toRingHom := by
    simpa using
      maximalIdeal_residueField_equiv_comp_residueFieldMap (f := algebraMap A B)
  constructor
  · intro x y hxy
    -- Compare `x` and `y` after transporting to the canonical local residue fields.
    have hx :
        (maximalIdeal_residueField_equiv B)
            (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
              ((maximalIdeal B).over_def (maximalIdeal A)) x) =
          (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A) x) := by
      simpa [RingHom.comp_apply] using
        congrArg (fun g : (maximalIdeal A).ResidueField →+* ResidueField B ↦ g x) hcomp
    have hy :
        (maximalIdeal_residueField_equiv B)
            (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
              ((maximalIdeal B).over_def (maximalIdeal A)) y) =
          (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A) y) := by
      simpa [RingHom.comp_apply] using
        congrArg (fun g : (maximalIdeal A).ResidueField →+* ResidueField B ↦ g y) hcomp
    have hxy' :
        (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A) x) =
          (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A) y) := by
      calc
        (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A) x) =
            (maximalIdeal_residueField_equiv B)
              (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
                ((maximalIdeal B).over_def (maximalIdeal A)) x) := hx.symm
        _ =
            (maximalIdeal_residueField_equiv B)
              (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
                ((maximalIdeal B).over_def (maximalIdeal A)) y) := by simpa [hxy]
        _ =
            (IsLocalRing.ResidueField.map (algebraMap A B))
              ((maximalIdeal_residueField_equiv A) y) := hy
    exact (maximalIdeal_residueField_equiv A).injective (hres.1 hxy')
  · intro z
    -- Pull `z` across the target equivalence and then lift it through the local residue-field map.
    obtain ⟨w, hw⟩ := hres.2 ((maximalIdeal_residueField_equiv B) z)
    refine ⟨(maximalIdeal_residueField_equiv A).symm w, ?_⟩
    apply (maximalIdeal_residueField_equiv B).injective
    calc
      (maximalIdeal_residueField_equiv B)
          (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
            ((maximalIdeal B).over_def (maximalIdeal A))
            ((maximalIdeal_residueField_equiv A).symm w)) =
          (IsLocalRing.ResidueField.map (algebraMap A B))
            ((maximalIdeal_residueField_equiv A)
              ((maximalIdeal_residueField_equiv A).symm w)) := by
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun g : (maximalIdeal A).ResidueField →+* ResidueField B ↦
                    g ((maximalIdeal_residueField_equiv A).symm w))
                  hcomp
      _ = (IsLocalRing.ResidueField.map (algebraMap A B)) w := by simp
      _ = (maximalIdeal_residueField_equiv B) z := hw

/-- Helper for Definition 15.112.7: after normalizing a branch in the trivial fraction-field
extension to the unique maximal ideal of the integral closure, the localized image of
`maximalIdeal A` is the maximal ideal of the branch localization. -/
lemma fractionRing_localized_branch_map_eq_maximalIdeal
    (P : Ideal (integralClosure A (FractionRing A))) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (maximalIdeal A) =
      maximalIdeal (Localization.AtPrime P) := by
  let B := integralClosure A (FractionRing A)
  letI : IsLocalRing B := isLocalRing_integralClosure_fractionRing (A := A)
  -- Route correction: first replace the branch by the unique maximal ideal of the collapsed
  -- integral closure, and only then push the maximal-ideal equality through localization.
  have hP : P = maximalIdeal B := fractionRing_branch_eq_maximalIdeal (A := A) P
  subst P
  have hunder : maximalIdeal A = (maximalIdeal B).under A :=
    (Ideal.liesOver_iff (maximalIdeal B) (maximalIdeal A)).1 inferInstance
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
    -- Use the lies-over equality to rewrite the source maximal ideal as a comap, then push it
    -- forward through the surjective collapse map.
    calc
      Ideal.map (algebraMap A B) (maximalIdeal A) =
          Ideal.map (algebraMap A B) ((maximalIdeal B).under A) := by
            rw [hunder]
      _ = maximalIdeal B := by
            simpa [Ideal.under_def] using
              (Ideal.map_comap_of_surjective (algebraMap A B)
                (integralClosure_fractionRing_algebraMap_surjective (A := A)) (maximalIdeal B))
  -- Rewrite the localization map as the composite `A → B → B_(max)` and apply the canonical
  -- maximal-ideal description for localization at a prime.
  have hcomp :
      Ideal.map (algebraMap A (Localization.AtPrime (maximalIdeal B))) (maximalIdeal A) =
        Ideal.map (algebraMap B (Localization.AtPrime (maximalIdeal B)))
          (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    simpa [IsScalarTower.algebraMap_eq A B (Localization.AtPrime (maximalIdeal B))] using
      (Ideal.map_map (I := maximalIdeal A) (f := algebraMap A B)
        (g := algebraMap B (Localization.AtPrime (maximalIdeal B)))).symm
  calc
    Ideal.map (algebraMap A (Localization.AtPrime (maximalIdeal B))) (maximalIdeal A) =
        Ideal.map (algebraMap B (Localization.AtPrime (maximalIdeal B)))
          (Ideal.map (algebraMap A B) (maximalIdeal A)) := hcomp
    _ =
        Ideal.map (algebraMap B (Localization.AtPrime (maximalIdeal B))) (maximalIdeal B) := by
          rw [hmap]
    _ = maximalIdeal (Localization.AtPrime (maximalIdeal B)) := by
          simpa using
            (IsLocalization.AtPrime.map_eq_maximalIdeal (maximalIdeal B)
              (Localization.AtPrime (maximalIdeal B)))

/-- Helper for Definition 15.112.7: the branch residue field in the trivial fraction-field
extension is separable over the base residue field because the canonical residue-field map is a
bijective algebra map. -/
lemma fractionRing_branch_residueField_separable
    (P : Ideal (integralClosure A (FractionRing A))) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
    let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
      ResidueField.instAlgebra
    Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) P.ResidueField := by
  let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
    ResidueField.instAlgebra
  let e : Ideal.ResidueField (maximalIdeal A) ≃+* P.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map (maximalIdeal A) P
        (algebraMap A (integralClosure A (FractionRing A))) (P.over_def (maximalIdeal A)))
      (fractionRing_residueField_map_bijective (A := A) P)
  have hcomm :
      RingHom.comp (algebraMap (Ideal.ResidueField (maximalIdeal A)) P.ResidueField)
          (RingEquiv.refl (Ideal.ResidueField (maximalIdeal A))).toRingHom =
        RingHom.comp e.toRingHom
          (algebraMap (Ideal.ResidueField (maximalIdeal A))
            (Ideal.ResidueField (maximalIdeal A))) := by
    -- The equivalence `e` was built from the algebra map itself, so the comparison diagram is
    -- definitionally the identity on residue classes.
    ext x
    rfl
  -- Transport self-separability of the base residue field across the residue-field equivalence.
  simpa using
    (Algebra.IsSeparable.of_equiv_equiv
      (RingEquiv.refl (Ideal.ResidueField (maximalIdeal A))) e hcomm)

/-- The trivial extension of the fraction field of a discrete valuation ring is unramified with
respect to the base ring. -/
instance fractionRing_isUnramifiedWithRespectTo :
    IsUnramifiedWithRespectTo A (FractionRing A) := by
  -- Route correction: normalize each branch to the unique maximal ideal of the collapsed
  -- integral closure, prove the required localized maximal-ideal equality there, and pair it
  -- with the already-established residue-field equivalence.
  refine (IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A) (L := FractionRing A)).2 ?_
  intro P _ _
  let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
    ResidueField.instAlgebra
  -- The canonical owner `Algebra.IsUnramifiedAt` asks exactly for the branchwise separability and
  -- localized maximal-ideal equality just isolated in the two helpers above.
  exact (Algebra.isUnramifiedAt_iff_map_eq A (maximalIdeal A) P).2
    ⟨fractionRing_branch_residueField_separable (A := A) P,
      fractionRing_localized_branch_map_eq_maximalIdeal (A := A) P⟩

/-- The trivial extension of the fraction field of a discrete valuation ring is totally ramified
with respect to the base ring. -/
instance fractionRing_isTotallyRamifiedWithRespectTo :
    IsTotallyRamifiedWithRespectTo A (FractionRing A) := by
  let B := integralClosure A (FractionRing A)
  letI : IsLocalRing B := isLocalRing_integralClosure_fractionRing (A := A)
  refine
    { unique_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · intro P Q _ _ _ _
    -- Both branches are forced to be the unique maximal ideal of the local target.
    calc
      P = maximalIdeal (integralClosure A (FractionRing A)) :=
        fractionRing_branch_eq_maximalIdeal (A := A) P
      _ = Q :=
        (fractionRing_branch_eq_maximalIdeal (A := A) Q).symm
  · intro P _ _
    -- The residue-field extension is exactly the bijective map established above.
    exact fractionRing_residueField_map_bijective (A := A) P

end
