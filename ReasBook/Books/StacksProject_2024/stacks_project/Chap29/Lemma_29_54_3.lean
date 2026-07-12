import Mathlib
import StacksProject_2024.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Ideal.Quotient

local instance minimalPrimes_isPrime {A : Type*} [CommRing A] (q : minimalPrimes A) :
    q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

-- Semantic recall: `lean_leansearch` identified the canonical ingredients
-- `minimalPrimes`, `Scheme.Hom.fromNormalization_preimage`, `Scheme.Hom.ι_fromNormalization`,
-- and `IsAffineOpen.isoSpec`. The ring-theoretic clauses are stated directly on `Γ(X, U)` and
-- indexed by the canonical subtype `minimalPrimes _`, while the normalization clauses are
-- exposed through the affine-preimage notation and section-ring API.

/-- Lemma 29.54.3 (1): for an affine open `U = Spec A` of a reduced scheme `X` such that every
quasi-compact open of `X` has finitely many irreducible components, the ring `A = Γ(X, U)` has
finitely many minimal primes. -/
@[stacks 035P]
theorem affineOpen_sections_finite_minimalPrimes
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    let A := Γ(X, (U : X.Opens))
    (minimalPrimes A).Finite := sorry

/-- The canonical comparison from the total ring of fractions of `Γ(X, U)` to the product of the
fraction fields of the reduced irreducible-component quotients. -/
noncomputable def affineOpen_sections_totalRingOfFractionsToPi
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    let A := Γ(X, (U : X.Opens))
    Localization (nonZeroDivisors A) →+*
      ((q : minimalPrimes A) → FractionRing (A ⧸ q.1)) := by
  intro A
  classical
  refine Pi.ringHom fun q ↦ ?_
  let qQuot := A ⧸ q.1
  have hqMap :
      nonZeroDivisors A ≤ Submonoid.comap (Ideal.Quotient.mk q.1) (nonZeroDivisors qQuot) := by
    intro x hx
    have hx_not_mem_q : x ∉ q.1 := by
      intro hxq
      exact Set.disjoint_left.mp
        (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes q.2) hxq hx
    change Ideal.Quotient.mk q.1 x ∈ nonZeroDivisors qQuot
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hxq ↦ hx_not_mem_q (eq_zero_iff_mem.mp hxq)
  let qMap :
      Localization (nonZeroDivisors A) →+* FractionRing qQuot :=
    IsLocalization.map (FractionRing qQuot) (Ideal.Quotient.mk q.1) hqMap
  exact
    qMap

/-- Lemma 29.54.3 (2): for an affine open `U = Spec A` as above, the total ring of fractions of
`A` is the product of the fraction fields of the domain quotients by the minimal primes of `A`. -/
@[stacks 035P]
theorem affineOpen_sections_totalRingOfFractionsToPi_bijective
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    let A := Γ(X, (U : X.Opens))
    Function.Bijective (affineOpen_sections_totalRingOfFractionsToPi U : Localization
      (nonZeroDivisors A) → ((q : minimalPrimes A) → FractionRing (A ⧸ q.1))) := sorry

/-- The canonical comparison from the integral closure of `Γ(X, U)` in its total ring of
fractions to the product of the integral closures of the minimal-prime quotients in their fraction
fields. -/
noncomputable def affineOpen_sections_integralClosureToPi
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    let A := Γ(X, (U : X.Opens))
    integralClosure A (Localization (nonZeroDivisors A)) →+*
      ((q : minimalPrimes A) →
        integralClosure (A ⧸ q.1) (FractionRing (A ⧸ q.1))) := by
  intro A
  classical
  refine Pi.ringHom fun q ↦ ?_
  let qQuot := A ⧸ q.1
  let qFrac := FractionRing qQuot
  have hqMap :
      nonZeroDivisors A ≤ Submonoid.comap (Ideal.Quotient.mk q.1) (nonZeroDivisors qQuot) := by
    intro x hx
    have hx_not_mem_q : x ∉ q.1 := by
      intro hxq
      exact Set.disjoint_left.mp
        (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes q.2) hxq hx
    change Ideal.Quotient.mk q.1 x ∈ nonZeroDivisors qQuot
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hxq ↦ hx_not_mem_q (eq_zero_iff_mem.mp hxq)
  let qMapHom :
      Localization (nonZeroDivisors A) →+* qFrac :=
    IsLocalization.map qFrac (Ideal.Quotient.mk q.1) hqMap
  let qMap : Localization (nonZeroDivisors A) →ₐ[A] qFrac :=
    { toRingHom := qMapHom
      commutes' := fun a ↦ by
        have hmap :
            (IsLocalization.map qFrac (Ideal.Quotient.mk q.1) hqMap)
                (algebraMap A (Localization (nonZeroDivisors A)) a) =
              algebraMap qQuot qFrac (Ideal.Quotient.mk q.1 a) :=
          IsLocalization.map_eq hqMap a
        exact hmap }
  exact
    RingHom.codRestrict
      (qMap.toRingHom.comp (integralClosure A (Localization (nonZeroDivisors A))).val.toRingHom)
      (integralClosure qQuot qFrac).toSubring
      (fun x ↦ by
        change (_root_.IsIntegral qQuot
          (qMap ((integralClosure A (Localization (nonZeroDivisors A))).val x)))
        exact _root_.IsIntegral.tower_top (_root_.IsIntegral.map qMap x.2))

/-- Lemma 29.54.3 (3): for an affine open `U = Spec A` as above, the canonical integral-closure
comparison map is bijective. -/
@[stacks 035P]
theorem affineOpen_sections_integralClosureToPi_bijective
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    let A := Γ(X, (U : X.Opens))
    Function.Bijective (affineOpen_sections_integralClosureToPi U :
      integralClosure A (Localization (nonZeroDivisors A)) →
        ((q : minimalPrimes A) →
          integralClosure (A ⧸ q.1) (FractionRing (A ⧸ q.1)))) := sorry

/-- Lemma 29.54.3 (4): if `ν : X^ν ⟶ X` is the normalization morphism of a reduced scheme `X`
such that every quasi-compact open of `X` has finitely many irreducible components, then the
inverse image of an affine open `U ⊆ X` is affine. This is the affine half of the identification
`ν⁻¹(U) = Spec(A')`. -/
@[stacks 035P]
theorem normalization_preimage_isAffineOpen
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (U : X.affineOpens) :
    IsAffineOpen (X.normalizationTo ⁻¹ᵁ (U : X.Opens)) := sorry

/-- The normalization preimage sections inherit their `Γ(X, U)`-algebra structure from the
specialized normalization morphism `genericPointSpectrumCoproductTo X`. -/
noncomputable local instance normalization_preimage_sections_algebra
    {X : Scheme.{u}} [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (U : X.affineOpens) :
    Algebra Γ(X, (U : X.Opens))
      Γ((genericPointSpectrumCoproductTo X).normalization,
        (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X)) ⁻¹ᵁ (U : X.Opens)) :=
  ((Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X)).app (U : X.Opens)).hom.toAlgebra

/-- The generic-point coproduct sections over `U` inherit their `Γ(X, U)`-algebra structure from
the canonical coproduct map `genericPointSpectrumCoproductTo X`. -/
noncomputable local instance genericPointSpectrumCoproduct_preimage_sections_algebra
    {X : Scheme.{u}} (U : X.affineOpens) :
    Algebra Γ(X, (U : X.Opens))
      Γ(genericPointSpectrumCoproduct X, genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens)) :=
  ((genericPointSpectrumCoproductTo X).app (U : X.Opens)).hom.toAlgebra

/-- Lemma 29.54.3 (5): if `ν : X^ν ⟶ X` is the normalization morphism of a reduced scheme `X`
such that every quasi-compact open of `X` has finitely many irreducible components, then the
section ring of `ν⁻¹(U)` is the integral closure of `A = Γ(X, U)` in the generic-point
coproduct section ring over `U`. This is the canonical relative-normalization comparison
`Scheme.Hom.normalizationObjIso` specialized to `genericPointSpectrumCoproductTo X`; together
with the total-ring-of-fractions comparison from part `(2)`, it yields the source
identification `ν⁻¹(U) = Spec(A')`. -/
@[stacks 035P]
noncomputable def normalization_preimage_sections_algEquiv_integralClosure
    {X : Scheme.{u}} [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (U : X.affineOpens) :
    Γ((genericPointSpectrumCoproductTo X).normalization,
      (Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X)) ⁻¹ᵁ (U : X.Opens)) ≃ₐ[
        Γ(X, (U : X.Opens))]
      integralClosure Γ(X, (U : X.Opens))
        Γ(genericPointSpectrumCoproduct X, genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens)) :=
  { toRingEquiv :=
      ((genericPointSpectrumCoproductTo X).normalizationObjIso U.2).commRingCatIsoToRingEquiv
    commutes' := by
      have hcomm :
          (((genericPointSpectrumCoproductTo X).normalizationObjIso U.2).hom).hom.comp
              ((Scheme.Hom.fromNormalization (genericPointSpectrumCoproductTo X)).app
                (U : X.Opens)).hom =
            algebraMap Γ(X, (U : X.Opens))
              (integralClosure Γ(X, (U : X.Opens))
                Γ(genericPointSpectrumCoproduct X,
                  genericPointSpectrumCoproductTo X ⁻¹ᵁ (U : X.Opens))) := by
        rw [(genericPointSpectrumCoproductTo X).fromNormalization_app U.2]
        ext a
        simp
      intro a
      simpa using congrFun (congrArg DFunLike.coe hcomm) a }

end AlgebraicGeometry
