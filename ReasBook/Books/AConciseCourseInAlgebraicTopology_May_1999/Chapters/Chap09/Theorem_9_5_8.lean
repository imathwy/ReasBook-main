import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_5_7

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set X} {B : Set Y} {n : ℕ+}
variable
  (eA :
    ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
  (eB :
    ∀ b : B, relativeHomotopyGroup n B b ≃ basedDiskBoundaryPairMapHomotopyClass n B b)

-- Semantic recall via `lean_leansearch`: the closest canonical hit was the fundamental-group
-- basepoint-change API `FundamentalGroup.fundamentalGroupMulEquivOfPath`. Chapter 9 already fixes
-- `relativeHomotopyGroupMapOfPairMap` and `relativeHomotopyGroupEquivOfPathClass` as the public
-- owners for the relative induced map and its basepoint-change isomorphism, relative to explicit
-- disk-boundary model comparisons, so this item states the homotopy-compatibility theorem against
-- those existing owners.

/-- The endpoint pair-map condition for `f` is already encoded in a homotopy through maps of
pairs. -/
theorem ContinuousMap.HomotopyWith.mapsTo_zero
    {A : Set X} {B : Set Y} {f f' : C(X, Y)}
    (h : ContinuousMap.HomotopyWith f f' (Set.MapsTo · A B)) :
    Set.MapsTo f A B := by
  intro a ha
  simpa using h.prop 0 ha

/-- The endpoint pair-map condition for `f'` is already encoded in a homotopy through maps of
pairs. -/
theorem ContinuousMap.HomotopyWith.mapsTo_one
    {A : Set X} {B : Set Y} {f f' : C(X, Y)}
    (h : ContinuousMap.HomotopyWith f f' (Set.MapsTo · A B)) :
    Set.MapsTo f' A B := by
  intro a ha
  simpa using h.prop 1 ha

/-- A homotopy through maps of pairs determines the path `h(a)` in the target subspace `B`. -/
def homotopyOfPairsPath
    {A : Set X} {B : Set Y} {f f' : C(X, Y)}
    (h : ContinuousMap.HomotopyWith f f' (Set.MapsTo · A B)) (a : A) :
    Path (pairMapSubspace f h.mapsTo_zero a) (pairMapSubspace f' h.mapsTo_one a) :=
  { toFun := fun t ↦ ⟨h (t, a.1), h.prop t a.2⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ fun t ↦ h.prop t a.2
      continuity
    source' := by
      apply Subtype.ext
      simp [pairMapSubspace_apply]
    target' := by
      apply Subtype.ext
      simp [pairMapSubspace_apply] }

/-- Theorem 9.5.8. If `h : f ≃ f'` is a homotopy through maps of pairs `(X, A) → (Y, B)`, then
the induced maps on relative homotopy groups differ by the basepoint-change isomorphism along the
path `h(a)` in `B`, relative to the supplied disk-boundary model comparisons. -/
theorem relativeHomotopyGroupMap_homotopyWith_eq_basepointChange
    {f f' : C(X, Y)}
    (h : ContinuousMap.HomotopyWith f f' (Set.MapsTo · A B))
    (a : A) :
    relativeHomotopyGroupEquivOfPathClass eB
        ⟦homotopyOfPairsPath h a⟧ ∘
      relativeHomotopyGroupMapOfPairMap eA eB f h.mapsTo_zero a =
        relativeHomotopyGroupMapOfPairMap eA eB f' h.mapsTo_one a := sorry

/-- Applying Theorem 9.5.8 to an element gives the pointwise homotopy-compatibility of the
induced maps on relative homotopy groups. -/
theorem relativeHomotopyGroupMap_homotopyWith_eq_basepointChange_apply
    {f f' : C(X, Y)}
    (h : ContinuousMap.HomotopyWith f f' (Set.MapsTo · A B))
    (a : A) (x : relativeHomotopyGroup n A a) :
    relativeHomotopyGroupEquivOfPathClass eB ⟦homotopyOfPairsPath h a⟧
        (relativeHomotopyGroupMapOfPairMap eA eB f h.mapsTo_zero a x) =
      relativeHomotopyGroupMapOfPairMap eA eB f' h.mapsTo_one a x := by
  exact congrFun (relativeHomotopyGroupMap_homotopyWith_eq_basepointChange eA eB h a) x
