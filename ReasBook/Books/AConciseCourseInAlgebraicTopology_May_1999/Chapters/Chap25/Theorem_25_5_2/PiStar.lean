import Mathlib.Algebra.DirectSum.Module
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_3_3

open scoped DirectSum

noncomputable section

universe u w

namespace Prespectrum

/-- The nonnegative stable homotopy object `π_*(T)` of a prespectrum `T`, packaged as the direct
sum of the stable homotopy groups `π_n(T)` over `n : ℕ`. -/
abbrev piStar (T : Prespectrum.{u, w}) :=
  ⨁ n : ℕ, Additive (Prespectrum.stableHomotopyGroup T (n : ℤ))

/-- The canonical inclusion of the degree-`n` stable homotopy group into `π_*(T)`. -/
def piStarClass (T : Prespectrum.{u, w}) (n : ℕ)
    (x : Prespectrum.stableHomotopyGroup T (n : ℤ)) : piStar T :=
  DirectSum.lof ℤ ℕ
    (fun k ↦ Additive (Prespectrum.stableHomotopyGroup T (k : ℤ)))
    n
    (Additive.ofMul x)

/-- Equality of homogeneous classes in the same degree can be detected inside `π_*(T)`. -/
theorem piStarClass_injective (T : Prespectrum.{u, w}) (n : ℕ) :
    Function.Injective (T.piStarClass n) := by
  intro x y hxy
  have hcomponent :=
    congrArg
      (DirectSum.component ℤ ℕ
        (fun k ↦ Additive (Prespectrum.stableHomotopyGroup T (k : ℤ)))
        n)
      hxy
  simpa [Prespectrum.piStarClass] using hcomponent

end Prespectrum

namespace RingPrespectrum

/-- The nonnegative stable homotopy object `π_*(T)` for a ring prespectrum `T`. -/
abbrev piStar (T : RingPrespectrum.{u, w}) :=
  Prespectrum.piStar T.toPrespectrum

/-- The canonical inclusion of the degree-`n` stable homotopy group into `π_*(T)` for a ring
prespectrum `T`. -/
abbrev piStarClass (T : RingPrespectrum.{u, w}) (n : ℕ)
    (x : Prespectrum.stableHomotopyGroup T.toPrespectrum (n : ℤ)) :
    RingPrespectrum.piStar T :=
  Prespectrum.piStarClass T.toPrespectrum n x

/-- Equality of homogeneous classes in the same degree can be detected inside `π_*(T)` for a ring
prespectrum `T`. -/
theorem piStarClass_injective (T : RingPrespectrum.{u, w}) (n : ℕ) :
    Function.Injective (T.piStarClass n) :=
  Prespectrum.piStarClass_injective T.toPrespectrum n

end RingPrespectrum

namespace StableHomotopy

scoped notation "π_*(" T ")" => Prespectrum.piStar T

end StableHomotopy
