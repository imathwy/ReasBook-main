import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_1

universe u

open Set Topology

-- `Topology.CWComplex.Subcomplex` from mathlib is the canonical owner for textbook subcomplexes of
-- a CW complex, so Definition 10.7.3 is refined as a source-facing triad owner built directly on
-- that API.

/-- Definition 10.7.3: a CW triad `(X; A, B)` is a triad on `X` together with a CW-complex
structure on `X`, chosen subcomplex presentations of `A` and `B`, and the covering condition
`A ∪ B = X`. -/
structure CWTriad (X : Type u) [TopologicalSpace X] extends Triad X where
  /-- The chosen CW-complex structure on the ambient space `X`. -/
  cwComplex : CWComplex (univ : Set X)
  /-- The distinguished subspace `A` is realized as a subcomplex of `X`. -/
  subcomplexA : letI := cwComplex; CWComplex.Subcomplex (univ : Set X)
  /-- The distinguished subspace `B` is realized as a subcomplex of `X`. -/
  subcomplexB : letI := cwComplex; CWComplex.Subcomplex (univ : Set X)
  /-- The inherited distinguished subspace `A` is the carrier of the chosen subcomplex. -/
  subspaceA_eq : letI := cwComplex; subspaceA = (subcomplexA : Set X)
  /-- The inherited distinguished subspace `B` is the carrier of the chosen subcomplex. -/
  subspaceB_eq : letI := cwComplex; subspaceB = (subcomplexB : Set X)
  /-- The distinguished subspaces cover the ambient space. -/
  union_eq_univ : subspaceA ∪ subspaceB = (univ : Set X)

variable {X : Type u} [TopologicalSpace X]

namespace CWTriad

instance instCWComplex (T : CWTriad X) : CWComplex (univ : Set X) := T.cwComplex

@[simp] theorem coe_subcomplexA (T : CWTriad X) : (T.subcomplexA : Set X) = T.subspaceA :=
  T.subspaceA_eq.symm

@[simp] theorem coe_subcomplexB (T : CWTriad X) : (T.subcomplexB : Set X) = T.subspaceB :=
  T.subspaceB_eq.symm

@[simp] theorem union_eq (T : CWTriad X) : T.union = (univ : Set X) :=
  T.union_eq_univ

/-- A CW triad presents its distinguished subspaces by subcomplexes whose carriers cover the
ambient space. -/
theorem spec (T : CWTriad X) :
    T.subspaceA = (T.subcomplexA : Set X) ∧
      T.subspaceB = (T.subcomplexB : Set X) ∧
      T.union = (univ : Set X) := by
  exact ⟨T.subspaceA_eq, T.subspaceB_eq, T.union_eq_univ⟩

end CWTriad
