import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

section RingHomPrimePowerRange

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]

namespace RingHom

/-- A ring map satisfies the prime-power image condition at `p` if every element `b` of the
target has some `p`-power multiple and the corresponding `p`-power power in the image. -/
def HasPrimePowerMultiplesAndPowersInRange (f : A →+* B) (p : ℕ) : Prop :=
  ∀ b : B, ∃ n : ℕ, p ^ n • b ∈ f.range ∧ b ^ (p ^ n) ∈ f.range

/-- Unfolding form of the prime-power image condition for a ring map. -/
theorem hasPrimePowerMultiplesAndPowersInRange_iff (f : A →+* B) (p : ℕ) :
    f.HasPrimePowerMultiplesAndPowersInRange p ↔
      ∀ b : B, ∃ n : ℕ, p ^ n • b ∈ f.range ∧ b ^ (p ^ n) ∈ f.range := sorry

end RingHom

end RingHomPrimePowerRange

namespace AlgebraicGeometry

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]

-- Semantic recall: `lean_leansearch` surfaced `Localization.awayMap` as the canonical induced map
-- `A[1/p] -> B[1/p]`; local Chapter 29 precedent supplies `UniversalHomeomorphism` for affine
-- spectra. The Stacks tag evidence is consistent: item tag `0CNF` agrees with the source URL
-- ending in `/tag/0CNF`.

/-- Lemma 29.46.9: let `p` be a prime number and let `f : A →+* B` be a ring map inducing an
isomorphism `A[1/p] → B[1/p]` through `Localization.awayMap f (p : A)`. Then
`Spec(B) → Spec(A)` is a universal homeomorphism if and only if `ker f` is locally nilpotent and
every `b : B` has a `p`-power `q` such that `q • b` and `b ^ q` lie in the image of `f`
(for example, the localization hypothesis holds when `p` is nilpotent in `A`). -/
@[stacks 0CNF]
theorem universalHomeomorphism_specMap_iff_ker_isLocallyNilpotent_and_primePowerMultiplesAndPowersInRange
    (p : ℕ) (hp : Nat.Prime p) (f : A →+* B)
    (hlocal : IsIso (CommRingCat.ofHom (Localization.awayMap f (p : A)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom f)) ↔
      (RingHom.ker f).IsLocallyNilpotent ∧
        f.HasPrimePowerMultiplesAndPowersInRange p := sorry

end

end AlgebraicGeometry
