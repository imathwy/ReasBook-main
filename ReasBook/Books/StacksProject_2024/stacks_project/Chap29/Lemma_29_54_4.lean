import StacksProject_2024.Chap29.Definition_29_54_1
import StacksProject_2024.Chap29.HasFiniteIrreducibleComponentsOnCompactOpens

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled `TopCat.Presheaf.stalkPushforward`,
-- `RingedSpace.Hom.commRingSheafPushforwardMap`, and `StructureSheaf.toPushforwardStalk`. Local
-- Chapter 29 already packages the source-facing normalization owner as `Scheme.normalization`
-- and `Scheme.normalizationTo`, specialized to the generic-point residue-field coproduct
-- morphism `genericPointSpectrumCoproductTo X`, while Lemma `29.54.3` supplies the affine
-- integral-closure comparison that this file restates stalkwise.

namespace Scheme

variable (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]
variable (x : X)

local notation "A" => X.presheaf.stalk x
local abbrev normalizationPushforwardStalk :=
  ((((TopCat.Sheaf.pushforward CommRingCat X.normalizationTo.base).obj
      X.normalization.sheaf).presheaf).stalk x)
local abbrev reducedStalkFractionRing :=
  FractionRing (A ⧸ _root_.nilradical A)
local abbrev minimalPrimeResidueFields :=
  (q : minimalPrimes A) → q.1.ResidueField
local abbrev normalizationStalkIntegralClosure :=
  integralClosure A (reducedStalkFractionRing X x)
local abbrev minimalPrimeResidueFieldsIntegralClosure :=
  integralClosure A (minimalPrimeResidueFields X x)

local instance minimalPrimes_isPrime (q : minimalPrimes A) : q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

/-- The stalk of the pushed-forward normalization structure sheaf at `x` is an
`\mathcal O_{X, x}`-algebra through the canonical pushforward sheaf map. -/
noncomputable abbrev normalizationPushforwardStalkMap :
    A →+* normalizationPushforwardStalk X x :=
  (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (RingedSpace.Hom.commRingSheafPushforwardMap X.normalizationTo.toShHom).hom).hom)

/-- The total ring of fractions of the reduced local ring at `x` is an `\mathcal O_{X, x}`-algebra
via the reduction map `\mathcal O_{X, x} → (\mathcal O_{X, x})_{red}`. -/
noncomputable abbrev reducedStalkFractionRingMap :
    A →+* reducedStalkFractionRing X x :=
  ((algebraMap (A ⧸ _root_.nilradical A) (reducedStalkFractionRing X x)).comp
    (algebraMap A (A ⧸ _root_.nilradical A)))

noncomputable instance reducedStalkFractionRingAlgebra :
    Algebra A (reducedStalkFractionRing X x) :=
  (reducedStalkFractionRingMap X x).toAlgebra

/-- The product of the residue fields of the minimal primes of `\mathcal O_{X, x}` is an
`\mathcal O_{X, x}`-algebra, factorwise via the canonical residue maps. -/
noncomputable abbrev minimalPrimeResidueFieldsMap :
    A →+* minimalPrimeResidueFields X x :=
  Pi.ringHom fun q ↦ algebraMap A q.1.ResidueField

noncomputable instance minimalPrimeResidueFieldsAlgebra :
    Algebra A (minimalPrimeResidueFields X x) :=
  (minimalPrimeResidueFieldsMap X x).toAlgebra

/-- Lemma 29.54.4 (1): if every quasi-compact open of `X` has finitely many irreducible
components and `ν : X^ν ⟶ X` is the normalization morphism, then for `x : X` the stalk
`(\nu_* \mathcal O_{X^\nu})_x` is canonically isomorphic as an `\mathcal O_{X, x}`-algebra to
the integral closure of `\mathcal O_{X, x}` in the total ring of fractions of
`(\mathcal O_{X, x})_{red}`. -/
@[stacks 0C3B]
theorem normalizationPushforwardStalk_exists_ringEquiv_integralClosure_reducedFractionRing :
    ∃ e : normalizationPushforwardStalk X x ≃+* normalizationStalkIntegralClosure X x,
      e.toRingHom.comp (normalizationPushforwardStalkMap X x) =
        algebraMap A (normalizationStalkIntegralClosure X x) := by
  sorry

/-- Lemma 29.54.4 (2): the integral closure of `\mathcal O_{X, x}` in the total ring of fractions
of `(\mathcal O_{X, x})_{red}` is canonically isomorphic as an `\mathcal O_{X, x}`-algebra to the
integral closure of `\mathcal O_{X, x}` in the product of the residue fields of its minimal
primes. -/
@[stacks 0C3B]
theorem integralClosure_reducedFractionRing_exists_ringEquiv_integralClosure_minimalPrimeResidueFields :
    ∃ e : normalizationStalkIntegralClosure X x ≃+*
        minimalPrimeResidueFieldsIntegralClosure X x,
      e.toRingHom.comp (algebraMap A (normalizationStalkIntegralClosure X x)) =
        algebraMap A (minimalPrimeResidueFieldsIntegralClosure X x) := by
  sorry

/-- Lemma 29.54.4 (3): the local ring `\mathcal O_{X, x}` has only finitely many minimal primes,
so the product of their residue fields is indexed by a finite set. -/
@[stacks 0C3B]
theorem finite_minimalPrimeStalks :
    (minimalPrimes A).Finite := sorry

end Scheme

end AlgebraicGeometry
