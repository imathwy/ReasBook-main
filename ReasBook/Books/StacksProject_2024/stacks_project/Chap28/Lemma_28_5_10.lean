import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `Scheme.fromSpecStalk`, `Scheme.fromSpecResidueField`, `Scheme.SpecToEquivOfField`,
-- `IsLocalRing.closedPoint`, and `CommSq` for the generic-point factorization square.

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.5.10 (1): if `x' ⤳ x` is a specialization in a locally Noetherian scheme `X`, then
there exists a discrete valuation ring whose spectrum maps to `X`, sending the generic point to
`x'` and the closed point to `x`. -/
@[stacks 054F]
theorem exists_dvr_specialization_lift
    {x' x : X} (h : x' ⤳ x) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (CommRingCat.of R) ⟶ X),
      f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x := sorry

/-- Source-facing bridge for Lemma 28.5.10 (1): the generic-point condition can be expressed by a
commutative square over `X.fromSpecResidueField x'`. -/
theorem exists_dvr_specialization_lift_CommSq
    {x' x : X} (h : x' ⤳ x) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : Algebra (X.residueField x') (FractionRing R))
      (f : Spec (CommRingCat.of R) ⟶ X),
      f (IsLocalRing.closedPoint R) = x ∧
        CommSq
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') (FractionRing R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
          (X.fromSpecResidueField x') f := sorry

/-- Lemma 28.5.10 (2): if `x' ⤳ x` is a nontrivial specialization in a locally Noetherian scheme
`X` and `K / κ(x')` is a finitely generated field extension, then one can choose the discrete
valuation ring in part `(1)` so that `K` itself is the fraction field over `κ(x')`. The induced
extension is recorded by the canonical commutative square factoring the generic-point map through
`X.fromSpecResidueField x'`. -/
@[stacks 054F]
theorem exists_dvr_specialization_lift_with_prescribed_fractionField
    {x' x : X} (h : x' ⤳ x) (hneq : x ≠ x')
    (K : Type u) [Field K] [Algebra (X.residueField x') K]
    [Algebra.FiniteType (X.residueField x') K] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : Algebra R K) (_ : IsFractionRing R K)
      (f : Spec (CommRingCat.of R) ⟶ X),
      f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x ∧
        CommSq
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') K)))
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (X.fromSpecResidueField x') f := sorry

end

end AlgebraicGeometry.Scheme
