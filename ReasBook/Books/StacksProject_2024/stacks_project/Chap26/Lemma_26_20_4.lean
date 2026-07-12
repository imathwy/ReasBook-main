import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.fromSpecStalk`,
-- `Scheme.range_fromSpecStalk`, and `Scheme.Hom.residueFieldMap`; local Chapter 29 precedent
-- uses `ValuationRing`, `IsFractionRing`, and `IsLocalRing.closedPoint` for valuation-ring
-- existence statements.

/-- Lemma 26.20.4: if `s'` specializes to `s` on a scheme `S`, then after any field extension
`κ(s') ⟶ K` there is a valuation ring `A` with fraction field `K` and a morphism
`Spec(A) ⟶ S` whose generic point maps to `s'`, whose closed point maps to `s`, and whose
induced residue-field extension at the generic point is the given one up to isomorphism. -/
@[stacks 01J8]
theorem exists_valuationRing_morphism_of_specialization_with_residueFieldExtension
    {S : Scheme.{u}} {s' s : S} (hsp : s' ⤳ s)
    (K : Type u) [Field K] (i : S.residueField s' ⟶ CommRingCat.of K) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (_ : Algebra A K) (_ : IsFractionRing A K)
      (f : Spec (CommRingCat.of A) ⟶ S),
        ∃ hη : f (⊥ : PrimeSpectrum A) = s',
          f (IsLocalRing.closedPoint A) = s ∧
            ∃ e : (Spec (CommRingCat.of A)).residueField (⊥ : PrimeSpectrum A) ≅
                CommRingCat.of K,
              Scheme.Hom.residueFieldMap f (⊥ : PrimeSpectrum A) ≫ e.hom = hη.symm ▸ i := sorry

end AlgebraicGeometry
