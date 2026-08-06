import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_4

open CategoryTheory.HomRel
open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: mathlib has Whitehead theorems in the abstract
-- model-category setting, notably `HomotopicalAlgebra.RightHomotopyClass.whitehead`. The source
-- item here is formalized directly with the local continuous-map owners `IsNEquivalence` and
-- `IsWeakEquivalence`, and with `ContinuousMap.HomotopyEquiv` as the canonical homotopy-
-- equivalence witness.

section

variable {Y Z : Type u}
variable [TopologicalSpace Y] [TopologicalSpace Z]

/-- A `TopCat` homotopy equivalence canonically yields a `ContinuousMap.HomotopyEquiv` with the
same underlying forward map. -/
theorem exists_homotopyEquiv_of_isHomotopyEquivalence (e : C(Y, Z))
    [IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e)] :
    ∃ h : Y ≃ₕ Z, h.toFun = e := by
  rcases
      (inferInstance : IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e)).exists_inverse with
    ⟨g, hgZ, hgY⟩
  refine ⟨{ toFun := e, invFun := g.hom, left_inv := ?_, right_inv := ?_ }, rfl⟩
  · simpa using hgY
  · simpa using hgZ

end

section

variable {Y Z : Type u}
variable [TopologicalSpace Y] [TopologicalSpace Z]

/-- Theorem 10.3.5 (1), proposition-level form: an `n`-equivalence between CW complexes whose
dimensions are both less than `n` is a homotopy equivalence in the quotient-by-homotopy category
of spaces. -/
theorem isHomotopyEquivalence_of_isNEquivalence_of_dimLE_lt
    [Topology.CWComplex (Set.univ : Set Y)] [Topology.CWComplex (Set.univ : Set Z)]
    (mY mZ n : ℕ) (h_dimY : Topology.RelCWComplex.dimLE (Set.univ : Set Y) mY) (hY_lt : mY < n)
    (h_dimZ : Topology.RelCWComplex.dimLE (Set.univ : Set Z) mZ) (hZ_lt : mZ < n) (e : C(Y, Z))
    [IsNEquivalence n e] :
    IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e) := by
  sorry

/-- Theorem 10.3.5 (1): an `n`-equivalence between CW complexes whose dimensions are both less
than `n` is a homotopy equivalence. Concretely, the given map is the forward map of a
`ContinuousMap.HomotopyEquiv`. -/
theorem exists_homotopyEquiv_of_isNEquivalence_of_dimLE_lt
    [Topology.CWComplex (Set.univ : Set Y)] [Topology.CWComplex (Set.univ : Set Z)]
    (mY mZ n : ℕ) (h_dimY : Topology.RelCWComplex.dimLE (Set.univ : Set Y) mY) (hY_lt : mY < n)
    (h_dimZ : Topology.RelCWComplex.dimLE (Set.univ : Set Z) mZ) (hZ_lt : mZ < n) (e : C(Y, Z))
    [IsNEquivalence n e] :
    ∃ h : Y ≃ₕ Z, h.toFun = e := by
  let _ : IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e) :=
    isHomotopyEquivalence_of_isNEquivalence_of_dimLE_lt mY mZ n h_dimY hY_lt h_dimZ hZ_lt e
  exact exists_homotopyEquiv_of_isHomotopyEquivalence e

/-- Theorem 10.3.5 (2), proposition-level form: a weak equivalence between CW complexes is a
homotopy equivalence in the quotient-by-homotopy category of spaces. -/
instance instIsHomotopyEquivalence_of_isWeakEquivalence
    [Topology.CWComplex (Set.univ : Set Y)] [Topology.CWComplex (Set.univ : Set Z)]
    (e : C(Y, Z)) [IsWeakEquivalence e] :
    IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e) := by
  sorry

/-- Theorem 10.3.5 (2): a weak equivalence between CW complexes is a homotopy equivalence.
Concretely, the given map is the forward map of a `ContinuousMap.HomotopyEquiv`. -/
theorem exists_homotopyEquiv_of_isWeakEquivalence
    [Topology.CWComplex (Set.univ : Set Y)] [Topology.CWComplex (Set.univ : Set Z)]
    (e : C(Y, Z)) [IsWeakEquivalence e] :
    ∃ h : Y ≃ₕ Z, h.toFun = e := by
  let _ : IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom e) := inferInstance
  exact exists_homotopyEquiv_of_isHomotopyEquivalence e

end
