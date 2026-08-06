import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyInclusion

open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: `lean_leansearch` surfaced `ZerothHomotopy` as the canonical owner for `π₀`,
-- and Chapter 9 already formalizes pair-relative groups together with the inclusion-induced `π₀`
-- map. No built-in owner for `n`-connected pairs surfaced, so this item uses the source-faithful
-- class below.

/-- Definition 10.4.2: a pair `(X, A)` is `n`-connected when the inclusion-induced map
`π₀(A) → π₀(X)` is surjective and every positive relative homotopy group `π_q(X, A, a)` with
`q ≤ n` is trivial for each basepoint `a : A`. -/
@[mk_iff nConnectedPair_iff]
class NConnectedPair (n : ℕ) (A : Set X) : Prop where
  zerothHomotopy_surjective : Function.Surjective (zerothHomotopyInclusion A)
  subsingleton_relativeHomotopyGroup {q : ℕ+} (hq : (q : ℕ) ≤ n)
      (a : A) : Subsingleton (relativeHomotopyGroup q A a)

namespace NConnectedPair

variable {m n : ℕ} {A : Set X} {q : ℕ+}

/-- Lower connectivity follows formally from higher connectivity. -/
theorem of_le [hA : NConnectedPair n A] (hmn : m ≤ n) : NConnectedPair m A where
  zerothHomotopy_surjective := hA.zerothHomotopy_surjective
  subsingleton_relativeHomotopyGroup := fun {_} hq a ↦
    hA.subsingleton_relativeHomotopyGroup (Nat.le_trans hq hmn) a

/-- An `n`-connected pair has surjective inclusion on path components. -/
theorem zerothHomotopySurjective [hA : NConnectedPair n A] :
    Function.Surjective (zerothHomotopyInclusion A) :=
  hA.zerothHomotopy_surjective

/-- In an `n`-connected pair, every positive-degree relative homotopy group up to degree `n` is
subsingleton. -/
theorem subsingletonRelativeHomotopyGroup [hA : NConnectedPair n A]
    (hq : (q : ℕ) ≤ n) (a : A) : Subsingleton (relativeHomotopyGroup q A a) :=
  hA.subsingleton_relativeHomotopyGroup hq a

/-- When the degree itself is the connectivity bound, the corresponding relative homotopy group is
canonically subsingleton. -/
instance subsingletonRelativeHomotopyGroupSelf [hA : NConnectedPair (q : ℕ) A]
    (a : A) : Subsingleton (relativeHomotopyGroup q A a) :=
  hA.subsingleton_relativeHomotopyGroup le_rfl a

end NConnectedPair
