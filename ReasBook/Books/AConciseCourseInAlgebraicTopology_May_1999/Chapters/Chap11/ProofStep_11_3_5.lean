import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Refinement_10_7_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_3_2

open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: the current repository already fixes the CW-triad
-- approximation owners `CWTriad`, `IsCWTriadApproximation`, and the low-cell vanishing bridge
-- `Topology.RelCWComplex.NoCellsLEOf`. Accordingly, this proof step keeps
-- `WeakCWTriadApproximation` only as the source-facing bridge adding a chosen basepoint and the
-- two source clauses about relative cells below dimensions `m` and `n`.

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

open Triad

/-- A weak CW approximation of the based triad `(T, x)` with left/right relative CW skeleta
starting in dimensions `m` and `n`. -/
structure WeakCWTriadApproximation (T : Triad X) (x : T.intersection) (m n : ℕ+) where
  space : TopCat
  /-- The canonical Chapter 10 CW-triad approximation data on the ambient replacement space. -/
  cwTriad : CWTriad space
  /-- The chosen basepoint in the approximating intersection `C' = A' ∩ B'`. -/
  basepoint : cwTriad.intersection
  /-- The ambient comparison map from the approximating CW triad to the original triad. -/
  ambientMap : C(space, TopCat.of X)
  /-- The ambient comparison map respects the distinguished `A`- and `B`-subspaces. -/
  isTriadMap : cwTriad.toTriad.IsMap T ambientMap
  /-- The underlying Chapter 10 approximation is a weak equivalence on `X`, `A`, `B`, and
  `C = A ∩ B`. -/
  isApproximation : IsCWTriadApproximation cwTriad T ambientMap isTriadMap
  /-- The chosen approximating basepoint maps to the prescribed basepoint `x`. -/
  map_basepoint : cwTriad.toTriad.mapIntersection T ambientMap isTriadMap basepoint = x
  /-- The pair `(ΓA, ΓC)` carries the chosen relative CW structure from Refinement 10.7.5. -/
  leftRelCW : Topology.RelCWComplex cwTriad.subcomplexA cwTriad.intersection
  /-- The pair `(ΓA, ΓC)` has no relative `q`-cells for `q ≤ m - 1`, equivalently below `m`. -/
  leftNoCellsLE : leftRelCW.NoCellsLEOf ((m : ℕ) - 1)
  /-- The pair `(ΓB, ΓC)` carries the chosen relative CW structure from Refinement 10.7.5. -/
  rightRelCW : Topology.RelCWComplex cwTriad.subcomplexB cwTriad.intersection
  /-- The pair `(ΓB, ΓC)` has no relative `q`-cells for `q ≤ n - 1`, equivalently below `n`. -/
  rightNoCellsLE : rightRelCW.NoCellsLEOf ((n : ℕ) - 1)

namespace WeakCWTriadApproximation

variable {T : Triad X} {x : T.intersection} {m n : ℕ+}

instance instCWComplex (approx : WeakCWTriadApproximation T x m n) :
    Topology.CWComplex (Set.univ : Set approx.space) :=
  approx.cwTriad.cwComplex

instance instIsCWTriadApproximation (approx : WeakCWTriadApproximation T x m n) :
    IsCWTriadApproximation approx.cwTriad T approx.ambientMap approx.isTriadMap :=
  approx.isApproximation

/-- The pair `(ΓA, ΓC)` attached to a weak CW triad approximation carries its chosen relative CW
structure. -/
instance instRelCWComplexSubcomplexA (approx : WeakCWTriadApproximation T x m n) :
    Topology.RelCWComplex approx.cwTriad.subcomplexA approx.cwTriad.intersection :=
  approx.leftRelCW

/-- The pair `(ΓB, ΓC)` attached to a weak CW triad approximation carries its chosen relative CW
structure. -/
instance instRelCWComplexSubcomplexB (approx : WeakCWTriadApproximation T x m n) :
    Topology.RelCWComplex approx.cwTriad.subcomplexB approx.cwTriad.intersection :=
  approx.rightRelCW

/-- The relative `k`-cells of `(ΓA, ΓC)` in a weak CW triad approximation. -/
abbrev leftRelativeCells (approx : WeakCWTriadApproximation T x m n) (k : ℕ) : Type _ :=
  Topology.RelCWComplex.cell (approx.cwTriad.subcomplexA : Set approx.space) k

/-- The relative `k`-cells of `(ΓB, ΓC)` in a weak CW triad approximation. -/
abbrev rightRelativeCells (approx : WeakCWTriadApproximation T x m n) (k : ℕ) : Type _ :=
  Topology.RelCWComplex.cell (approx.cwTriad.subcomplexB : Set approx.space) k

@[simp] theorem mapIntersection_basepoint (approx : WeakCWTriadApproximation T x m n) :
    mapIntersection approx.cwTriad.toTriad T approx.ambientMap approx.isTriadMap
        approx.basepoint = x :=
  approx.map_basepoint

/-- The ambient comparison map of a weak CW triad approximation is a weak equivalence. -/
theorem isWeakEquivalence_ambientMap (approx : WeakCWTriadApproximation T x m n) :
    IsWeakEquivalence approx.ambientMap :=
  approx.isApproximation.isWeakEquivalence_toAmbient

/-- The induced map on the distinguished `A`-subspaces of a weak CW triad approximation is a weak
equivalence. -/
theorem isWeakEquivalence_mapSubspaceA (approx : WeakCWTriadApproximation T x m n) :
    IsWeakEquivalence (approx.cwTriad.mapSubspaceA T approx.ambientMap approx.isTriadMap) :=
  approx.isApproximation.isWeakEquivalence_subspaceA

/-- The induced map on the distinguished `B`-subspaces of a weak CW triad approximation is a weak
equivalence. -/
theorem isWeakEquivalence_mapSubspaceB (approx : WeakCWTriadApproximation T x m n) :
    IsWeakEquivalence (approx.cwTriad.mapSubspaceB T approx.ambientMap approx.isTriadMap) :=
  approx.isApproximation.isWeakEquivalence_subspaceB

/-- The induced map on the intersections `ΓC = ΓA ∩ ΓB` and `C = A ∩ B` of a weak CW triad
approximation is a weak equivalence. -/
theorem isWeakEquivalence_mapIntersection (approx : WeakCWTriadApproximation T x m n) :
    IsWeakEquivalence (approx.cwTriad.mapIntersection T approx.ambientMap approx.isTriadMap) :=
  approx.isApproximation.isWeakEquivalence_intersection

end WeakCWTriadApproximation

/-- A weak equivalence of modeled path-space pairs yields an equivalence of the degree-`2`
triad homotopy sets. -/
theorem triadHomotopyGroup_equiv_two_of_pathPairWeakEquivalence
    {T : Triad X} {x : T.intersection}
    {T' : Triad Y} {x' : T'.intersection}
    (e : triadHomotopyPathPair T' x' ⟶ triadHomotopyPathPair T x)
    (he : SpacePair.IsWeakEquivalence e) :
    Nonempty (triadHomotopyGroup T' x' 2 (by decide) ≃ triadHomotopyGroup T x 2 (by decide)) := by
  sorry

/-- A weak equivalence of modeled path-space pairs induces isomorphic triad homotopy groups in
each degree `q + 3`. -/
theorem triadHomotopyGroup_mulEquiv_of_pathPairWeakEquivalence
    {T : Triad X} {x : T.intersection}
    {T' : Triad Y} {x' : T'.intersection}
    (e : triadHomotopyPathPair T' x' ⟶ triadHomotopyPathPair T x)
    (he : SpacePair.IsWeakEquivalence e) (q : ℕ) :
    Nonempty
      (triadHomotopyGroup T' x' (q + 3) (triadHigherGroupDegree q) ≃*
        triadHomotopyGroup T x (q + 3) (triadHigherGroupDegree q)) := by
  sorry

/-- A weak CW triad approximation preserves the degree-`2` triad homotopy set up to
equivalence. -/
theorem triadHomotopyGroup_equiv_two_of_weakCWTriadApproximation
    {T : Triad X} {x : T.intersection} {m n : ℕ+}
    (approx : WeakCWTriadApproximation T x m n) :
    Nonempty
      (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint 2 (by decide) ≃
        triadHomotopyGroup T x 2 (by decide)) :=
  by
    sorry

/-- In higher degrees `q + 3`, the uniform weak-CW-approximation comparison upgrades to a group
isomorphism. -/
theorem triadHomotopyGroup_mulEquiv_of_weakCWTriadApproximation
    {T : Triad X} {x : T.intersection} {m n : ℕ+}
    (approx : WeakCWTriadApproximation T x m n) (q : ℕ) :
    Nonempty
      (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint (q + 3)
          (triadHigherGroupDegree q) ≃*
        triadHomotopyGroup T x (q + 3) (triadHigherGroupDegree q)) :=
  by
    sorry

/-- Proof step 11.3.5 (1): for every degree `q ≥ 2`, a weak CW triad approximation of `(T, x)`
does not change the triad homotopy groups. -/
theorem triadHomotopyGroup_equiv_of_weakCWTriadApproximation
    {T : Triad X} {x : T.intersection} {m n : ℕ+}
    (approx : WeakCWTriadApproximation T x m n) (q : ℕ) (hq : 2 ≤ q) :
    Nonempty (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint q hq ≃
      triadHomotopyGroup T x q hq) := by
  cases q with
  | zero =>
      exact False.elim (Nat.not_succ_le_zero 1 hq)
  | succ q =>
      cases q with
      | zero =>
          exact False.elim (Nat.not_succ_le_self 1 hq)
      | succ q =>
          cases q with
          | zero =>
              simpa using triadHomotopyGroup_equiv_two_of_weakCWTriadApproximation approx
          | succ q =>
              rcases triadHomotopyGroup_mulEquiv_of_weakCWTriadApproximation approx q with ⟨e⟩
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (show Nonempty
                  (triadHomotopyGroup approx.cwTriad.toTriad approx.basepoint (q + 3)
                      (triadHigherGroupDegree q) ≃
                    triadHomotopyGroup T x (q + 3) (triadHigherGroupDegree q)) from
                  ⟨e.toEquiv⟩)

/-- Proof step 11.3.5 (2): under the excision and connectivity hypotheses from homotopy excision,
one may replace a based triad by a weakly equivalent CW triad whose relative pairs `(ΓA, ΓC)` and
`(ΓB, ΓC)` have no relative cells in dimensions strictly below `m` and `n`, respectively. -/
theorem exists_weakCWTriadApproximation
    (T : Triad X) (x : T.intersection) (m n : ℕ+)
    (hExcisive : T.IsExcisive)
    (hA : NConnectedPair ((m : ℕ) - 1) T.leftIntersectionSubspace)
    (hB : NConnectedPair ((n : ℕ) - 1) T.rightIntersectionSubspace) :
    Nonempty (WeakCWTriadApproximation T x m n) := by
  sorry
