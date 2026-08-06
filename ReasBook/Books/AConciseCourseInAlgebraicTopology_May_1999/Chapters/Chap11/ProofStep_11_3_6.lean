import Mathlib.Topology.CWComplex.Classical.Finite
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.ProofStep_11_3_5

universe u v

-- Semantic recall via `lean_leansearch`: Chapter 11 already records the CW replacement data in
-- `WeakCWTriadApproximation`, so the cell-induction step should add only the genuinely new finite
-- and single-cell hypotheses on top of that canonical owner.

variable {X : Type u} [TopologicalSpace X]

namespace WeakCWTriadApproximation

/-- The source-facing special case `A = C ∪ D^m` and `B = C ∪ D^n` for a weak CW triad
approximation: `(A', C')` has exactly one relative `m`-cell and no others, while `(B', C')` has
exactly one relative `n`-cell and no others. -/
class IsOneCellPerSideSpecialCase
    {T : Triad X} {x : T.intersection} {m n : ℕ+}
    (approx : WeakCWTriadApproximation T x m n) : Prop where
  /-- The pair `(A', C')` has at most one relative `m`-cell. -/
  left_subsingleton : Subsingleton (approx.leftRelativeCells (m : ℕ))
  /-- The pair `(A', C')` has at least one relative `m`-cell. -/
  left_nonempty : Nonempty (approx.leftRelativeCells (m : ℕ))
  /-- The pair `(A', C')` has no relative cells outside degree `m`. -/
  left_isEmpty_of_ne : ∀ k : ℕ, k ≠ (m : ℕ) → IsEmpty (approx.leftRelativeCells k)
  /-- The pair `(B', C')` has at most one relative `n`-cell. -/
  right_subsingleton : Subsingleton (approx.rightRelativeCells (n : ℕ))
  /-- The pair `(B', C')` has at least one relative `n`-cell. -/
  right_nonempty : Nonempty (approx.rightRelativeCells (n : ℕ))
  /-- The pair `(B', C')` has no relative cells outside degree `n`. -/
  right_isEmpty_of_ne : ∀ k : ℕ, k ≠ (n : ℕ) → IsEmpty (approx.rightRelativeCells k)

/-- A weak CW triad approximation whose left and right relative CW structures are finite. -/
structure Finite (T : Triad X) (x : T.intersection) (m n : ℕ+)
    extends WeakCWTriadApproximation T x m n where
  /-- The relative CW structure on `(A', C')` is finite. -/
  left_finite :
    letI :
        Topology.RelCWComplex
          (toWeakCWTriadApproximation.cwTriad.subcomplexA : Set toWeakCWTriadApproximation.space)
          toWeakCWTriadApproximation.cwTriad.intersection :=
      toWeakCWTriadApproximation.leftRelCW
    Topology.RelCWComplex.Finite
      (toWeakCWTriadApproximation.cwTriad.subcomplexA : Set toWeakCWTriadApproximation.space)
  /-- The relative CW structure on `(B', C')` is finite. -/
  right_finite :
    letI :
        Topology.RelCWComplex
          (toWeakCWTriadApproximation.cwTriad.subcomplexB : Set toWeakCWTriadApproximation.space)
          toWeakCWTriadApproximation.cwTriad.intersection :=
      toWeakCWTriadApproximation.rightRelCW
    Topology.RelCWComplex.Finite
      (toWeakCWTriadApproximation.cwTriad.subcomplexB : Set toWeakCWTriadApproximation.space)

instance instCoeFiniteToWeakCWTriadApproximation
    {T : Triad X} {x : T.intersection} {m n : ℕ+} :
    Coe (Finite T x m n) (WeakCWTriadApproximation T x m n) where
  coe := Finite.toWeakCWTriadApproximation

namespace Finite

/-- The one-cell-per-side hypothesis for a finite weak CW triad approximation, viewed through its
inherited `WeakCWTriadApproximation` structure. -/
abbrev isOneCellPerSideSpecialCase
    {T : Triad X} {x : T.intersection} {m n : ℕ+} (approx : Finite T x m n) : Prop :=
  WeakCWTriadApproximation.IsOneCellPerSideSpecialCase
    (approx : WeakCWTriadApproximation T x m n)

end Finite

end WeakCWTriadApproximation

/-- Proof step 11.3.6. Induction over the relative cells reduces the vanishing theorem to the
special case `A = C ∪ D^m` and `B = C ∪ D^n`, expressed on a finite weak CW triad approximation by
`WeakCWTriadApproximation.IsOneCellPerSideSpecialCase`. The source hypotheses then supply both the
required finite approximation data and the induction principle reducing an arbitrary finite
approximation to this one-cell-per-side case. -/
theorem triadHomotopyGroup_subsingleton_of_cellInduction
    (specialCase :
      ∀ {Y : Type v} [TopologicalSpace Y]
        {T : Triad Y} {x : T.intersection} {m n : ℕ+}
        (approx : WeakCWTriadApproximation.Finite T x m n),
          approx.isOneCellPerSideSpecialCase →
            ∀ q : ℕ,
                ∀ hq₂ : 2 ≤ q,
                ∀ hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2,
                  Subsingleton (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint q hq₂))
    (cellInduction :
      ∀ {Y : Type v} [TopologicalSpace Y]
        {T : Triad Y} {x : T.intersection} {m n : ℕ+}
        (approx : WeakCWTriadApproximation.Finite T x m n),
          (∀ approx' : WeakCWTriadApproximation.Finite T x m n,
              approx'.isOneCellPerSideSpecialCase →
                ∀ q : ℕ,
                    ∀ hq₂ : 2 ≤ q,
                    ∀ hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2,
                      Subsingleton
                        (triadHomotopyGroup approx'.cwTriad.toTriad approx'.basepoint q hq₂)) →
            ∀ q : ℕ,
              ∀ hq₂ : 2 ≤ q,
              ∀ hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2,
                  Subsingleton (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint q hq₂))
    (finiteApproximation :
      ∀ {Y : Type v} [TopologicalSpace Y]
        (T : Triad Y) (x : T.intersection) (m n : ℕ+) (hExcisive : T.IsExcisive)
        (hA : NConnectedPair ((m : ℕ) - 1) T.leftIntersectionSubspace)
        (hB : NConnectedPair ((n : ℕ) - 1) T.rightIntersectionSubspace),
          Nonempty (WeakCWTriadApproximation.Finite T x m n))
    (T : Triad X) (x : T.intersection) (m n : ℕ+) (q : ℕ)
    (hq₂ : 2 ≤ q) (hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2)
    (hExcisive : T.IsExcisive)
    (hA : NConnectedPair ((m : ℕ) - 1) T.leftIntersectionSubspace)
    (hB : NConnectedPair ((n : ℕ) - 1) T.rightIntersectionSubspace) :
    Subsingleton (triadHomotopyGroup T x q hq₂) := sorry
