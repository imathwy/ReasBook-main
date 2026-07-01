import Mathlib
import Mathlib.NumberTheory.RamificationInertia.Ramification

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

namespace IsUnramifiedWithRespectTo

variable [Algebra.EssFiniteType A (integralClosure A L)]

/-- The source-facing unramified branch data recover the canonical owner
`Algebra.IsUnramifiedAt A P` under the finite-type hypotheses required by that owner. -/
theorem isUnramifiedAt (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] [h : _root_.IsUnramifiedWithRespectTo A L] :
    Algebra.IsUnramifiedAt A P := sorry

/-- Under the finite-type bridge, the source-facing unramified predicate is equivalent to the
branchwise canonical owner `Algebra.IsUnramifiedAt`. -/
theorem iff_isUnramifiedAt :
    _root_.IsUnramifiedWithRespectTo A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt A P := sorry

end IsUnramifiedWithRespectTo

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

/-- The trivial extension of the fraction field of a discrete valuation ring is unramified with
respect to the base ring. -/
instance fractionRing_isUnramifiedWithRespectTo :
    IsUnramifiedWithRespectTo A (FractionRing A) := by
  sorry

/-- The trivial extension of the fraction field of a discrete valuation ring is totally ramified
with respect to the base ring. -/
instance fractionRing_isTotallyRamifiedWithRespectTo :
    IsTotallyRamifiedWithRespectTo A (FractionRing A) := sorry

end
