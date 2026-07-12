import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MorphismProperty
open CommRingCat

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `Spec.map` and
-- `Scheme.Hom.residueFieldMap`; local Chapter 29 defines universal homeomorphisms by
-- the generic bridge predicate `universally topologicallyIsHomeomorph`.

/-- Lemma 29.46.10 (1): if `x^3 = y^2`, then the map
`A → A[t]/(t^2 - x, t^3 - y)` induces bijections on residue fields. -/
@[stacks 0EUI]
theorem cuspQuotient_residueFieldMap_bijective_of_cube_eq_square
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
    ∀ z : Spec (.of B), Function.Bijective ((f.residueFieldMap z).hom :
      (Spec (.of A)).residueField (f z) → (Spec (.of B)).residueField z) := sorry

/-- Lemma 29.46.10 (2): if `x^3 = y^2`, then the map on spectra induced by
`A → A[t]/(t^2 - x, t^3 - y)` is a universal homeomorphism. -/
@[stacks 0EUI]
theorem cuspQuotient_universally_homeomorph_of_cube_eq_square
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    universally topologicallyIsHomeomorph (Spec.map (CommRingCat.ofHom φ)) := sorry

/-- Lemma 29.46.10 (3): if `p` is prime and `p^p x = y^p`, then the map on spectra
induced by `A → A[t]/(t^p - x, pt - y)` is a universal homeomorphism. -/
@[stacks 0EUI]
theorem primePowerQuotient_universally_homeomorph_of_natPrime_relation
    (A : Type u) [CommRing A] (x y : A) (p : ℕ) (hp : Nat.Prime p)
    (hxy : (p : A) ^ p * x = y ^ p) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    universally topologicallyIsHomeomorph (Spec.map (CommRingCat.ofHom φ)) := sorry

end

end AlgebraicGeometry
