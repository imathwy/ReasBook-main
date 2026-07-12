import StacksProject_2024.Chap28.Definition_28_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the affine-open owner `Scheme.affineOpens`; the
-- ring-side Japanese owner already present in the project is `IsN2Ring`. The remark's usable
-- replacement is therefore best formalized as a scheme property quantified over affine opens and
-- associated primes of their section rings, not as a stalkwise wrapper.

/-- Remark 28.13.2: a scheme `X` is Japanese if it is locally Noetherian and for every affine
open `U = Spec(A)` of `X` and every associated prime `p` of `A`, the quotient ring `A / p` is
Japanese, i.e. `N-2`. -/
@[stacks 033T]
class Japanese (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  /-- For every affine open `U` and every associated prime of its section ring, the quotient is
  Japanese. -/
  quotient_isN2Ring {U : X.affineOpens} (p : PrimeSpectrum (Γ(X, U)))
      (hp : IsAssociatedPrime p.asIdeal (Γ(X, U))) :
      IsN2Ring (Γ(X, U) ⧸ p.asIdeal)

/-- On an integral Japanese scheme, every nonempty affine open has `N-2` section ring. -/
theorem Japanese.affineOpenSectionsIsN2Ring (X : Scheme.{u}) [IsIntegral X] [Japanese X]
    (U : X.affineOpens) (hU : Nonempty U) :
    affineOpenSectionsIsN2Ring X U hU := sorry

/-- An integral Japanese scheme in the sense of Remark 28.13.2 is Japanese in the affine-open
sense of Definition 28.13.1. -/
@[stacks 033T]
instance instIsJapaneseOfJapanese (X : Scheme.{u}) [IsIntegral X] [Japanese X] :
    IsJapanese X := sorry

end AlgebraicGeometry.Scheme
