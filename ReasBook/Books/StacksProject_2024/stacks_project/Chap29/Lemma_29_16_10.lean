import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap28.Lemma_28_6_4
import StacksProject_2024.Chap31.Lemma_31_16_1

open AlgebraicGeometry PrimeSpectrum IsLocalRing
open scoped AlgebraicGeometry

universe u

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-level theorem
  `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`;
- `Chap28/Lemma_28_6_4` and `Chap31/Lemma_31_16_1` provide the punctured-spectrum Jacobson base
  case together with the canonical open owner `puncturedSpectrumOpen`;
- the dimension-one Noetherian-domain clause is kept at the scheme level, with the ring-theoretic
  Jacobson criterion delegated to the supporting Chapter 10 development.
-/

section

/-- Lemma 29.16.10 (1): any scheme locally of finite type over a field is Jacobson. -/
@[stacks 02J6]
theorem jacobsonSpace_of_locallyOfFiniteType_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/-- Lemma 29.16.10 (2): any scheme locally of finite type over `Spec(ℤ)` is Jacobson. -/
@[stacks 02J6]
theorem jacobsonSpace_of_locallyOfFiniteType_over_specInt
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/-- Lemma 29.16.10 (3): any scheme locally of finite type over `Spec(R)` is Jacobson when `R` is a
1-dimensional Noetherian domain with infinitely many prime ideals. -/
@[stacks 02J6]
theorem jacobsonSpace_of_locallyOfFiniteType_over_spec_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Infinite (PrimeSpectrum R)]
    (hdim : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/- Supporting recall: for a Noetherian local ring `(A, 𝔪)`, the punctured spectrum
`Spec(A) \ {𝔪}` is Jacobson. This is exactly
`AlgebraicGeometry.jacobsonSpace_puncturedSpectrum_of_isNoetherianRing`. -/
recall AlgebraicGeometry.jacobsonSpace_puncturedSpectrum_of_isNoetherianRing

/-- Lemma 29.16.10 (4): any scheme locally of finite type over the punctured spectrum of a
Noetherian local ring is Jacobson. -/
@[stacks 02J6]
theorem jacobsonSpace_of_locallyOfFiniteType_over_puncturedSpectrum
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Scheme.Opens.toScheme
      (puncturedSpectrumOpen : (Spec (CommRingCat.of A)).Opens))
    [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

end
