import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_6

universe u w

-- Semantic recall: local Chapter 8/11 precedent already fixes `reducedSuspension`,
-- `suspensionPiMap`, and `suspensionHomomorphism` as the suspension owners used below.

/-- Definition 13.2.7. The provisional suspension map
`H'_n(X) → H'_(n + 1)(Σ X)` is represented by suspending maps `S^n → X`. In the current
formalization this means: degree `0` passes from `π_ 0` to the abelianization of `π_ 1(Σ X)`,
degree `1` factors the suspension homomorphism `π_ 1(X) → π_ 2(Σ X)` through abelianization, and
higher degrees use the usual suspension homomorphism on homotopy groups. -/
noncomputable def provisionalReducedGroupSuspensionMap
    (n : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroup n X →
      provisionalReducedGroup (n + 1) (Σ X) :=
  match n with
  | 0 => fun z ↦ Abelianization.of (suspensionPiMap 0 X (provisionalReducedGroupZeroEquivPi0 X z))
  | 1 => fun a ↦ Abelianization.lift (suspensionHomomorphism 1 X) a
  | m + 2 => suspensionHomomorphism (m + 2) X

/-- The degree-zero provisional suspension map is obtained from the `π_ 0` suspension class and
the canonical map to the abelianization of `π_ 1(Σ X)`. -/
@[simp] theorem provisionalReducedGroupSuspensionMap_zero
    (X : PointedCompactlyGenerated.{u, w}) (z : provisionalReducedGroup 0 X) :
    provisionalReducedGroupSuspensionMap 0 X z =
      Abelianization.of (suspensionPiMap 0 X (provisionalReducedGroupZeroEquivPi0 X z)) := rfl

/-- The degree-one provisional suspension map is the abelianization lift of
`suspensionHomomorphism 1 X`. -/
@[simp] theorem provisionalReducedGroupSuspensionMap_one
    (X : PointedCompactlyGenerated.{u, w}) (a : provisionalReducedGroup 1 X) :
    provisionalReducedGroupSuspensionMap 1 X a =
      Abelianization.lift (suspensionHomomorphism 1 X) a := rfl

/-- In degrees `m + 2`, the provisional suspension map agrees with the usual suspension
homomorphism on higher homotopy groups. -/
@[simp] theorem provisionalReducedGroupSuspensionMap_succ_succ
    (m : ℕ) (X : PointedCompactlyGenerated.{u, w})
    (a : provisionalReducedGroup (m + 2) X) :
    provisionalReducedGroupSuspensionMap (m + 2) X a =
      suspensionHomomorphism (m + 2) X a := rfl
