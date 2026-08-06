import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWEulerCharacteristic

open scoped ContinuousMap
open scoped Topology.CWComplex
open Topology
open Topology.RelCWComplex

universe u

section

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
variable [CWComplex (Set.univ : Set X)] [CWComplex.Finite (Set.univ : Set X)]
variable (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
variable [CWComplex (Set.univ : Set Y)] [CWComplex.Finite (Set.univ : Set Y)]
variable (f : C(A, Y))
variable [CWComplex (Set.univ : Set (cellularPushout (A : Set X) f))]
variable [CWComplex.Finite (Set.univ : Set (cellularPushout (A : Set X) f))]

-- Semantic recall via `lean_leansearch`: no canonical mathlib Euler-characteristic theorem for a
-- cellular adjunction-space pushout surfaced in the current environment. The Chapter 10 owners
-- `cellularPushout`, `subcomplexMapPairHom`, and `cwEulerCharacteristic` therefore give the
-- source-faithful statement.

/-- Problem 10.8.4. For a finite cellular pushout `Y ∪_f X` with `A` a subcomplex of `X`, the
Euler characteristic satisfies the inclusion-exclusion formula
`χ(Y ∪_f X) = χ(Y) + χ(X) - χ(A)`. Here the pushout is formalized as
`cellularPushout (A : Set X) f`, and the Euler characteristic is the Chapter 10 owner
`cwEulerCharacteristic`. -/
theorem cwEulerCharacteristic_cellularPushout_eq
    (hf : IsCellularMap (subcomplexMapPairHom A f)) :
    χ((Set.univ : Set (cellularPushout (A : Set X) f))) =
      χ((Set.univ : Set Y)) + χ((Set.univ : Set X)) - χ((A : Set X)) := sorry

end
