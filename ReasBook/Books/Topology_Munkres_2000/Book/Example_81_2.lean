module

public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Topology_Munkres_2000.Book.Lemma_60_5.Covering
import all Topology_Munkres_2000.Book.Definition_53_5.FigureEight
import all Topology_Munkres_2000.Book.Lemma_60_5.Covering

public section

open scoped CoveringTransformation

namespace FigureEightTangentCircleCover

/-- Helper for Example 81.2: the common vertex of the two coordinate axes in the total space. -/
private def origin : Total :=
  Quot.mk Gluing (xAxis 0)

/-- Helper for Example 81.2: the horizontal-axis inclusion into the glued total space is
continuous. -/
private lemma continuous_xAxisInclusion :
    Continuous (fun x : ℝ ↦ Quot.mk Gluing (xAxis x)) := by
  -- Compose the continuous summand inclusion with the quotient map.
  apply continuous_quot_mk.comp
  unfold xAxis
  fun_prop

/-- Helper for Example 81.2: the vertical-axis inclusion into the glued total space is
continuous. -/
private lemma continuous_yAxisInclusion :
    Continuous (fun y : ℝ ↦ Quot.mk Gluing (yAxis y)) := by
  -- Compose the continuous summand inclusion with the quotient map.
  apply continuous_quot_mk.comp
  unfold yAxis
  fun_prop

/-- Helper for Example 81.2: each circle tangent to the horizontal axis includes continuously
in the glued total space. -/
private lemma continuous_xCircleInclusion (n : NonzeroInt) :
    Continuous (fun z : Circle ↦ Quot.mk Gluing (xCircle n z)) := by
  -- Compose the continuous indexed-circle inclusion with the quotient map.
  apply continuous_quot_mk.comp
  unfold xCircle
  fun_prop

/-- Helper for Example 81.2: each circle tangent to the vertical axis includes continuously
in the glued total space. -/
private lemma continuous_yCircleInclusion (n : NonzeroInt) :
    Continuous (fun z : Circle ↦ Quot.mk Gluing (yCircle n z)) := by
  -- Compose the continuous indexed-circle inclusion with the quotient map.
  apply continuous_quot_mk.comp
  unfold yCircle
  fun_prop

/-- Helper for Example 81.2: the axes with all their tangent circles form a path-connected
space after the prescribed gluing. -/
private lemma totalPathConnectedSpace : PathConnectedSpace Total := by
  let toOrigin : ∀ e : Total, Joined e origin := by
    intro e
    induction e using Quot.inductionOn with
    | _ e =>
        rcases e with x | e
        · -- A horizontal-axis point moves to zero along that axis.
          have hreal : Joined x 0 := PathConnectedSpace.joined _ _
          exact ⟨hreal.somePath.map continuous_xAxisInclusion⟩
        · rcases e with y | e
          · -- A vertical-axis point moves to zero, which is glued to the chosen origin.
            have hreal : Joined y 0 := PathConnectedSpace.joined _ _
            have hmapped : Joined
                (Quot.mk Gluing (yAxis y)) (Quot.mk Gluing (yAxis 0)) :=
              ⟨hreal.somePath.map continuous_yAxisInclusion⟩
            have hpoint : Quot.mk Gluing (yAxis 0) = origin :=
              (Quot.sound Gluing.origin).symm
            rwa [hpoint] at hmapped
          · rcases e with e | e
            · rcases e with ⟨n, z⟩
              -- Move around the tangent circle to its attachment, then along the axis.
              have hcircle : Joined z (1 : Circle) := PathConnectedSpace.joined _ _
              have hmapped : Joined
                  (Quot.mk Gluing (xCircle n z)) (Quot.mk Gluing (xCircle n 1)) :=
                ⟨hcircle.somePath.map (continuous_xCircleInclusion n)⟩
              have hpoint : Quot.mk Gluing (xCircle n 1) = Quot.mk Gluing (xAxis n) :=
                Quot.sound (Gluing.xCircle_base n)
              have haxis : Joined (Quot.mk Gluing (xAxis n)) origin := by
                have hreal : Joined (n : ℝ) 0 := PathConnectedSpace.joined _ _
                exact ⟨hreal.somePath.map continuous_xAxisInclusion⟩
              rw [hpoint] at hmapped
              exact hmapped.trans haxis
            · rcases e with ⟨n, z⟩
              -- The vertical tangent-circle case is symmetric.
              have hcircle : Joined z (1 : Circle) := PathConnectedSpace.joined _ _
              have hmapped : Joined
                  (Quot.mk Gluing (yCircle n z)) (Quot.mk Gluing (yCircle n 1)) :=
                ⟨hcircle.somePath.map (continuous_yCircleInclusion n)⟩
              have hpoint : Quot.mk Gluing (yCircle n 1) = Quot.mk Gluing (yAxis n) :=
                Quot.sound (Gluing.yCircle_base n)
              have haxis : Joined (Quot.mk Gluing (yAxis n)) origin := by
                have hreal : Joined (n : ℝ) 0 := PathConnectedSpace.joined _ _
                have hmappedAxis : Joined
                    (Quot.mk Gluing (yAxis n)) (Quot.mk Gluing (yAxis 0)) :=
                  ⟨hreal.somePath.map continuous_yAxisInclusion⟩
                have horigin : Quot.mk Gluing (yAxis 0) = origin :=
                  (Quot.sound Gluing.origin).symm
                rwa [horigin] at hmappedAxis
              rw [hpoint] at hmapped
              exact hmapped.trans haxis
  refine ⟨⟨origin⟩, ?_⟩
  intro x y
  -- Join arbitrary points through the common origin.
  exact (toOrigin x).trans (toOrigin y).symm

/-- Helper for Example 81.2: the combinatorial vertices lying over the figure-eight
basepoint. -/
private inductive FiberVertex
  | origin
  | horizontal (n : NonzeroInt)
  | vertical (n : NonzeroInt)

/-- Helper for Example 81.2: the total-space point represented by a combinatorial fiber
vertex. -/
private def fiberPointValue : FiberVertex → Total
  | .origin => origin
  | .horizontal n => Quot.mk Gluing (xAxis n)
  | .vertical n => Quot.mk Gluing (yAxis n)

/-- Helper for Example 81.2: every displayed combinatorial vertex projects to the
figure-eight basepoint. -/
private lemma proj_fiberPointValue (v : FiberVertex) :
    proj (fiberPointValue v) = FigureEight.basepoint := by
  -- Each case is an integer point on one of the two wrapped axes.
  cases v with
  | origin =>
      apply Subtype.ext
      simp [fiberPointValue, origin, proj_xAxis, firstCircle, FigureEight.basepoint,
        Circle.turnExp_zero]
  | horizontal n =>
      apply Subtype.ext
      simp [fiberPointValue, proj_xAxis, firstCircle, FigureEight.basepoint,
        Circle.turnExp_int]
  | vertical n =>
      apply Subtype.ext
      simp [fiberPointValue, proj_yAxis, secondCircle, FigureEight.basepoint,
        Circle.turnExp_int]

/-- Helper for Example 81.2: a displayed combinatorial vertex belongs to the basepoint
fiber. -/
private lemma fiberPointValue_mem_fiber (v : FiberVertex) :
    fiberPointValue v ∈ proj ⁻¹' {FigureEight.basepoint} := by
  -- Membership in this singleton fiber is exactly the projection computation above.
  exact proj_fiberPointValue v

/-- Helper for Example 81.2: the canonical map from combinatorial vertices to the
basepoint fiber. -/
private def fiberPoint (v : FiberVertex) : proj ⁻¹' {FigureEight.basepoint} :=
  ⟨fiberPointValue v, fiberPointValue_mem_fiber v⟩

/-- Helper for Example 81.2: the horizontal coordinate is constant on every generating
gluing pair. -/
private def horizontalCoordinateRaw : Raw → ℝ
  | Sum.inl x => x
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl (n, _))) => n
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

/-- Helper for Example 81.2: the horizontal coordinate respects the gluing relation. -/
private lemma horizontalCoordinateRaw_eq {a b : Raw} (hab : Gluing a b) :
    horizontalCoordinateRaw a = horizontalCoordinateRaw b := by
  -- The only nontrivial attachment has the same integer coordinate on both sides.
  cases hab <;> rfl

/-- Helper for Example 81.2: the horizontal axis coordinate descends to the glued total
space. -/
private def horizontalCoordinate : Total → ℝ :=
  Quot.lift horizontalCoordinateRaw fun _ _ hab ↦ horizontalCoordinateRaw_eq hab

/-- Helper for Example 81.2: the raw horizontal coordinate is continuous on the disjoint
union of axes and tangent circles. -/
private lemma continuous_horizontalCoordinateRaw : Continuous horizontalCoordinateRaw := by
  -- Continuity is checked separately on the four coproduct summands.
  rw [continuous_sum_dom]
  constructor
  · change Continuous (fun x : ℝ ↦ x)
    exact continuous_id
  · rw [continuous_sum_dom]
    constructor
    · change Continuous (fun _ : ℝ ↦ (0 : ℝ))
      exact continuous_const
    · rw [continuous_sum_dom]
      constructor
      · change Continuous (fun p : TangentCircles ↦ (p.1 : ℝ))
        have hcast : Continuous (fun n : NonzeroInt ↦ (n : ℝ)) :=
          continuous_of_discreteTopology
        exact hcast.comp continuous_fst
      · change Continuous (fun _ : TangentCircles ↦ (0 : ℝ))
        exact continuous_const

/-- Helper for Example 81.2: the horizontal coordinate is continuous after gluing. -/
private lemma continuous_horizontalCoordinate : Continuous horizontalCoordinate := by
  -- The quotient universal property descends the continuous raw coordinate.
  exact continuous_quot_lift (fun _ _ hab ↦ horizontalCoordinateRaw_eq hab)
    continuous_horizontalCoordinateRaw

/-- Helper for Example 81.2: the vertical coordinate is constant on every generating
gluing pair. -/
private def verticalCoordinateRaw : Raw → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl y) => y
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr (n, _))) => n

/-- Helper for Example 81.2: the vertical coordinate respects the gluing relation. -/
private lemma verticalCoordinateRaw_eq {a b : Raw} (hab : Gluing a b) :
    verticalCoordinateRaw a = verticalCoordinateRaw b := by
  -- The only nontrivial attachment has the same integer coordinate on both sides.
  cases hab <;> rfl

/-- Helper for Example 81.2: the vertical axis coordinate descends to the glued total
space. -/
private def verticalCoordinate : Total → ℝ :=
  Quot.lift verticalCoordinateRaw fun _ _ hab ↦ verticalCoordinateRaw_eq hab

/-- Helper for Example 81.2: the raw vertical coordinate is continuous on the disjoint
union of axes and tangent circles. -/
private lemma continuous_verticalCoordinateRaw : Continuous verticalCoordinateRaw := by
  -- Continuity is checked separately on the four coproduct summands.
  rw [continuous_sum_dom]
  constructor
  · change Continuous (fun _ : ℝ ↦ (0 : ℝ))
    exact continuous_const
  · rw [continuous_sum_dom]
    constructor
    · change Continuous (fun y : ℝ ↦ y)
      exact continuous_id
    · rw [continuous_sum_dom]
      constructor
      · change Continuous (fun _ : TangentCircles ↦ (0 : ℝ))
        exact continuous_const
      · change Continuous (fun p : TangentCircles ↦ (p.1 : ℝ))
        have hcast : Continuous (fun n : NonzeroInt ↦ (n : ℝ)) :=
          continuous_of_discreteTopology
        exact hcast.comp continuous_fst

/-- Helper for Example 81.2: the vertical coordinate is continuous after gluing. -/
private lemma continuous_verticalCoordinate : Continuous verticalCoordinate := by
  -- The quotient universal property descends the continuous raw coordinate.
  exact continuous_quot_lift (fun _ _ hab ↦ verticalCoordinateRaw_eq hab)
    continuous_verticalCoordinateRaw

/-- Helper for Example 81.2: over the second circle, the horizontal coordinate is an
integer lift of the circle basepoint. -/
private lemma turnExp_horizontalCoordinate_of_proj_fst_eq_one (e : Total)
    (he : (proj e : Torus).1 = 1) :
    Circle.turnExp (horizontalCoordinate e) = 1 := by
  induction e using Quot.inductionOn with
  | _ e =>
      -- The four raw summands reduce to zero or an integer coordinate.
      rcases e with x | e
      · have hproj : proj (Quot.mk Gluing (Sum.inl x)) =
            firstCircle (Circle.turnExp x) := by
          simpa only [xAxis] using proj_xAxis x
        rw [hproj] at he
        simpa [horizontalCoordinate, horizontalCoordinateRaw, firstCircle] using he
      · rcases e with y | e
        · simp [horizontalCoordinate, horizontalCoordinateRaw, Circle.turnExp_zero]
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            simpa [horizontalCoordinate, horizontalCoordinateRaw] using Circle.turnExp_int n
          · rcases e with ⟨n, z⟩
            simp [horizontalCoordinate, horizontalCoordinateRaw, Circle.turnExp_zero]

/-- Helper for Example 81.2: over the first circle, the vertical coordinate is an
integer lift of the circle basepoint. -/
private lemma turnExp_verticalCoordinate_of_proj_snd_eq_one (e : Total)
    (he : (proj e : Torus).2 = 1) :
    Circle.turnExp (verticalCoordinate e) = 1 := by
  induction e using Quot.inductionOn with
  | _ e =>
      -- The four raw summands reduce to zero or an integer coordinate.
      rcases e with x | e
      · simp [verticalCoordinate, verticalCoordinateRaw, Circle.turnExp_zero]
      · rcases e with y | e
        · have hproj : proj (Quot.mk Gluing (Sum.inr (Sum.inl y))) =
              secondCircle (Circle.turnExp y) := by
            simpa only [yAxis] using proj_yAxis y
          rw [hproj] at he
          simpa [verticalCoordinate, verticalCoordinateRaw, secondCircle] using he
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            simp [verticalCoordinate, verticalCoordinateRaw, Circle.turnExp_zero]
          · rcases e with ⟨n, z⟩
            simpa [verticalCoordinate, verticalCoordinateRaw] using Circle.turnExp_int n

/-- Helper for Example 81.2: a continuous family lying over the second circle has constant
horizontal coordinate once that coordinate is fixed at one point. -/
private lemma horizontalCoordinate_eq_constant_of_proj_fst_eq_one
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F : X → Total) (hF : Continuous F) (x₀ : X) (c : ℝ)
    (hstart : horizontalCoordinate (F x₀) = c)
    (hproj : ∀ x, (proj (F x) : Torus).1 = 1) :
    ∀ x, horizontalCoordinate (F x) = c := by
  have hc : Circle.turnExp c = 1 := by
    rw [← hstart]
    exact turnExp_horizontalCoordinate_of_proj_fst_eq_one (F x₀) (hproj x₀)
  have hcomp : Circle.turnExp ∘ (horizontalCoordinate ∘ F) =
      Circle.turnExp ∘ (fun _ : X ↦ c) := by
    funext x
    -- Both sides are the basepoint because the family stays over the second circle.
    exact (turnExp_horizontalCoordinate_of_proj_fst_eq_one (F x) (hproj x)).trans hc.symm
  have hcoordinate := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    (continuous_horizontalCoordinate.comp hF) continuous_const hcomp x₀ hstart
  exact congrFun hcoordinate

/-- Helper for Example 81.2: a continuous family lying over the first circle has constant
vertical coordinate once that coordinate is fixed at one point. -/
private lemma verticalCoordinate_eq_constant_of_proj_snd_eq_one
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F : X → Total) (hF : Continuous F) (x₀ : X) (c : ℝ)
    (hstart : verticalCoordinate (F x₀) = c)
    (hproj : ∀ x, (proj (F x) : Torus).2 = 1) :
    ∀ x, verticalCoordinate (F x) = c := by
  have hc : Circle.turnExp c = 1 := by
    rw [← hstart]
    exact turnExp_verticalCoordinate_of_proj_snd_eq_one (F x₀) (hproj x₀)
  have hcomp : Circle.turnExp ∘ (verticalCoordinate ∘ F) =
      Circle.turnExp ∘ (fun _ : X ↦ c) := by
    funext x
    -- Both sides are the basepoint because the family stays over the first circle.
    exact (turnExp_verticalCoordinate_of_proj_snd_eq_one (F x) (hproj x)).trans hc.symm
  have hcoordinate := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    (continuous_verticalCoordinate.comp hF) continuous_const hcomp x₀ hstart
  exact congrFun hcoordinate

/-- Helper for Example 81.2: when the vertical coordinate vanishes, the first projection
coordinate is the exponential of the horizontal coordinate. -/
private lemma proj_fst_eq_turnExp_horizontal_of_vertical_eq_zero (e : Total)
    (hvertical : verticalCoordinate e = 0) :
    (proj e : Torus).1 = Circle.turnExp (horizontalCoordinate e) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · have hproj : proj (Quot.mk Gluing (Sum.inl x)) =
            firstCircle (Circle.turnExp x) := by
          simpa only [xAxis] using proj_xAxis x
        rw [hproj]
        rfl
      · rcases e with y | e
        · change y = 0 at hvertical
          subst y
          have hproj : proj (Quot.mk Gluing (Sum.inr (Sum.inl 0))) =
              secondCircle (Circle.turnExp 0) := by
            simpa only [yAxis] using proj_yAxis 0
          rw [hproj]
          simp [secondCircle, horizontalCoordinate, horizontalCoordinateRaw,
            Circle.turnExp_zero]
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            have hproj : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inl (n, z))))) = secondCircle z := by
              simpa only [xCircle] using proj_xCircle n z
            rw [hproj]
            simpa [secondCircle, horizontalCoordinate, horizontalCoordinateRaw] using
              (Circle.turnExp_int n).symm
          · rcases e with ⟨n, z⟩
            change (n : ℝ) = 0 at hvertical
            have hn : (n : ℤ) = 0 := by
              exact_mod_cast hvertical
            exact False.elim (n.property hn)

/-- Helper for Example 81.2: when the horizontal coordinate vanishes, the second projection
coordinate is the exponential of the vertical coordinate. -/
private lemma proj_snd_eq_turnExp_vertical_of_horizontal_eq_zero (e : Total)
    (hhorizontal : horizontalCoordinate e = 0) :
    (proj e : Torus).2 = Circle.turnExp (verticalCoordinate e) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · change x = 0 at hhorizontal
        subst x
        have hproj : proj (Quot.mk Gluing (Sum.inl 0)) =
            firstCircle (Circle.turnExp 0) := by
          simpa only [xAxis] using proj_xAxis 0
        rw [hproj]
        simp [firstCircle, verticalCoordinate, verticalCoordinateRaw, Circle.turnExp_zero]
      · rcases e with y | e
        · have hproj : proj (Quot.mk Gluing (Sum.inr (Sum.inl y))) =
              secondCircle (Circle.turnExp y) := by
            simpa only [yAxis] using proj_yAxis y
          rw [hproj]
          rfl
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            change (n : ℝ) = 0 at hhorizontal
            have hn : (n : ℤ) = 0 := by
              exact_mod_cast hhorizontal
            exact False.elim (n.property hn)
          · rcases e with ⟨n, z⟩
            have hproj : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inr (n, z))))) = firstCircle z := by
              simpa only [yCircle] using proj_yCircle n z
            rw [hproj]
            simpa [firstCircle, verticalCoordinate, verticalCoordinateRaw] using
              (Circle.turnExp_int n).symm

/-- Helper for Example 81.2: a nonzero horizontal coordinate forces the vertical coordinate
to vanish. -/
private lemma verticalCoordinate_eq_zero_of_horizontalCoordinate_ne_zero (e : Total)
    (h : horizontalCoordinate e ≠ 0) :
    verticalCoordinate e = 0 := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · rfl
      · rcases e with y | e
        · exact False.elim (h rfl)
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            rfl
          · rcases e with ⟨n, z⟩
            exact False.elim (h rfl)

/-- Helper for Example 81.2: a nonzero vertical coordinate forces the horizontal coordinate
to vanish. -/
private lemma horizontalCoordinate_eq_zero_of_verticalCoordinate_ne_zero (e : Total)
    (h : verticalCoordinate e ≠ 0) :
    horizontalCoordinate e = 0 := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · exact False.elim (h rfl)
      · rcases e with y | e
        · rfl
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            exact False.elim (h rfl)
          · rcases e with ⟨n, z⟩
            rfl

/-- Helper for Example 81.2: the two descended coordinates record a combinatorial fiber
vertex. -/
private def fiberVertexCoordinate : FiberVertex → ℝ × ℝ
  | .origin => (0, 0)
  | .horizontal n => (n, 0)
  | .vertical n => (0, n)

/-- Helper for Example 81.2: distinct combinatorial fiber vertices have distinct coordinate
pairs. -/
private lemma fiberVertexCoordinate_injective : Function.Injective fiberVertexCoordinate := by
  intro v w h
  cases v with
  | origin =>
      cases w with
      | origin => rfl
      | horizontal n =>
          have hnReal : (0 : ℝ) = n := congrArg Prod.fst h
          have hn : (0 : ℤ) = n := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn.symm)
      | vertical n =>
          have hnReal : (0 : ℝ) = n := congrArg Prod.snd h
          have hn : (0 : ℤ) = n := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn.symm)
  | horizontal n =>
      cases w with
      | origin =>
          have hnReal : (n : ℝ) = 0 := congrArg Prod.fst h
          have hn : (n : ℤ) = 0 := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn)
      | horizontal m =>
          have hnmReal : (n : ℝ) = m := congrArg Prod.fst h
          have hnm : (n : ℤ) = m := Int.cast_injective hnmReal
          exact congrArg FiberVertex.horizontal (Subtype.ext hnm)
      | vertical m =>
          have hnReal : (n : ℝ) = 0 := congrArg Prod.fst h
          have hn : (n : ℤ) = 0 := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn)
  | vertical n =>
      cases w with
      | origin =>
          have hnReal : (n : ℝ) = 0 := congrArg Prod.snd h
          have hn : (n : ℤ) = 0 := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn)
      | horizontal m =>
          have hnReal : (n : ℝ) = 0 := congrArg Prod.snd h
          have hn : (n : ℤ) = 0 := by
            exact_mod_cast hnReal
          exact False.elim (n.property hn)
      | vertical m =>
          have hnmReal : (n : ℝ) = m := congrArg Prod.snd h
          have hnm : (n : ℤ) = m := Int.cast_injective hnmReal
          exact congrArg FiberVertex.vertical (Subtype.ext hnm)

/-- Helper for Example 81.2: a fiber vertex with a prescribed nonzero horizontal coordinate
is the corresponding horizontal vertex. -/
private lemma fiberVertex_eq_horizontal_of_fst_eq (v : FiberVertex) (n : NonzeroInt)
    (h : (fiberVertexCoordinate v).1 = (n : ℝ)) :
    v = FiberVertex.horizontal n := by
  -- Origin and vertical vertices have zero first coordinate; horizontal coordinates are faithful.
  cases v with
  | origin =>
      have hnReal : (0 : ℝ) = n := h
      have hn : (0 : ℤ) = n := by
        exact_mod_cast hnReal
      exact False.elim (n.property hn.symm)
  | horizontal m =>
      have hmnReal : (m : ℝ) = n := h
      have hmn : (m : ℤ) = n := by
        exact_mod_cast hmnReal
      exact congrArg FiberVertex.horizontal (Subtype.ext hmn)
  | vertical m =>
      have hnReal : (0 : ℝ) = n := h
      have hn : (0 : ℤ) = n := by
        exact_mod_cast hnReal
      exact False.elim (n.property hn.symm)

/-- Helper for Example 81.2: a fiber vertex with a prescribed nonzero vertical coordinate
is the corresponding vertical vertex. -/
private lemma fiberVertex_eq_vertical_of_snd_eq (v : FiberVertex) (n : NonzeroInt)
    (h : (fiberVertexCoordinate v).2 = (n : ℝ)) :
    v = FiberVertex.vertical n := by
  -- Origin and horizontal vertices have zero second coordinate; vertical coordinates are faithful.
  cases v with
  | origin =>
      have hnReal : (0 : ℝ) = n := h
      have hn : (0 : ℤ) = n := by
        exact_mod_cast hnReal
      exact False.elim (n.property hn.symm)
  | horizontal m =>
      have hnReal : (0 : ℝ) = n := h
      have hn : (0 : ℤ) = n := by
        exact_mod_cast hnReal
      exact False.elim (n.property hn.symm)
  | vertical m =>
      have hmnReal : (m : ℝ) = n := h
      have hmn : (m : ℤ) = n := by
        exact_mod_cast hmnReal
      exact congrArg FiberVertex.vertical (Subtype.ext hmn)

/-- Helper for Example 81.2: the descended coordinates of a canonical fiber point are its
combinatorial coordinates. -/
private lemma fiberPoint_coordinates (v : FiberVertex) :
    (horizontalCoordinate (fiberPoint v), verticalCoordinate (fiberPoint v)) =
      fiberVertexCoordinate v := by
  -- Quotient evaluation computes directly on each chosen representative.
  cases v <;> rfl

/-- Helper for Example 81.2: the canonical enumeration of the basepoint fiber is injective. -/
private lemma fiberPoint_injective : Function.Injective fiberPoint := by
  intro v w h
  -- Push equality through the two quotient invariants and use their combinatorial injectivity.
  have hcoordinates := congrArg
    (fun e : proj ⁻¹' {FigureEight.basepoint} ↦
      (horizontalCoordinate e, verticalCoordinate e)) h
  rw [fiberPoint_coordinates v, fiberPoint_coordinates w] at hcoordinates
  exact fiberVertexCoordinate_injective hcoordinates

/-- Helper for Example 81.2: every point over the figure-eight basepoint is one of the
displayed combinatorial vertices. -/
private lemma fiberPoint_surjective : Function.Surjective fiberPoint := by
  rintro ⟨e, he⟩
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · -- A point of the horizontal axis lies over the basepoint exactly at an integer.
        have hxCircle : Circle.turnExp x = 1 := by
          have hproj : proj (Quot.mk Gluing (Sum.inl x)) = FigureEight.basepoint := he
          have hprojAxis :
              proj (Quot.mk Gluing (Sum.inl x)) = firstCircle (Circle.turnExp x) := by
            simpa only [xAxis] using proj_xAxis x
          rw [hprojAxis] at hproj
          have hx := congrArg (fun z : FigureEight ↦ (z : Torus).1) hproj
          simpa [firstCircle, FigureEight.basepoint] using hx
        obtain ⟨n, rfl⟩ := (Circle.turnExp_eq_one_iff x).mp hxCircle
        by_cases hn : n = 0
        · subst n
          refine ⟨FiberVertex.origin, ?_⟩
          apply Subtype.ext
          simp only [fiberPoint, fiberPointValue, origin, xAxis, Int.cast_zero]
        · let n' : NonzeroInt := ⟨n, hn⟩
          refine ⟨FiberVertex.horizontal n', ?_⟩
          apply Subtype.ext
          rfl
      · rcases e with y | e
        · -- The vertical-axis case is the symmetric integer classification.
          have hyCircle : Circle.turnExp y = 1 := by
            have hproj : proj (Quot.mk Gluing (Sum.inr (Sum.inl y))) =
                FigureEight.basepoint := he
            have hprojAxis :
                proj (Quot.mk Gluing (Sum.inr (Sum.inl y))) =
                  secondCircle (Circle.turnExp y) := by
              simpa only [yAxis] using proj_yAxis y
            rw [hprojAxis] at hproj
            have hy := congrArg (fun z : FigureEight ↦ (z : Torus).2) hproj
            simpa [secondCircle, FigureEight.basepoint] using hy
          obtain ⟨n, rfl⟩ := (Circle.turnExp_eq_one_iff y).mp hyCircle
          by_cases hn : n = 0
          · subst n
            refine ⟨FiberVertex.origin, ?_⟩
            apply Subtype.ext
            simpa only [fiberPoint, fiberPointValue, origin, yAxis, Int.cast_zero] using
              Quot.sound Gluing.origin
          · let n' : NonzeroInt := ⟨n, hn⟩
            refine ⟨FiberVertex.vertical n', ?_⟩
            apply Subtype.ext
            rfl
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            -- A point on a horizontal tangent circle is in the fiber only at its attachment.
            have hz : z = 1 := by
              have hproj : proj (Quot.mk Gluing
                  (Sum.inr (Sum.inr (Sum.inl (n, z))))) = FigureEight.basepoint := he
              have hprojCircle : proj (Quot.mk Gluing
                  (Sum.inr (Sum.inr (Sum.inl (n, z))))) = secondCircle z := by
                simpa only [xCircle] using proj_xCircle n z
              rw [hprojCircle] at hproj
              have hz' := congrArg (fun w : FigureEight ↦ (w : Torus).2) hproj
              simpa [secondCircle, FigureEight.basepoint] using hz'
            subst z
            refine ⟨FiberVertex.horizontal n, ?_⟩
            apply Subtype.ext
            simpa only [fiberPoint, fiberPointValue, xAxis, xCircle] using
              (Quot.sound (Gluing.xCircle_base n)).symm
          · rcases e with ⟨n, z⟩
            -- The vertical tangent circle similarly contributes its attachment vertex only.
            have hz : z = 1 := by
              have hproj : proj (Quot.mk Gluing
                  (Sum.inr (Sum.inr (Sum.inr (n, z))))) = FigureEight.basepoint := he
              have hprojCircle : proj (Quot.mk Gluing
                  (Sum.inr (Sum.inr (Sum.inr (n, z))))) = firstCircle z := by
                simpa only [yCircle] using proj_yCircle n z
              rw [hprojCircle] at hproj
              have hz' := congrArg (fun w : FigureEight ↦ (w : Torus).1) hproj
              simpa [firstCircle, FigureEight.basepoint] using hz'
            subst z
            refine ⟨FiberVertex.vertical n, ?_⟩
            apply Subtype.ext
            simpa only [fiberPoint, fiberPointValue, yAxis, yCircle] using
              (Quot.sound (Gluing.yCircle_base n)).symm

/-- Helper for Example 81.2: combinatorial vertices bijectively enumerate the basepoint
fiber. -/
private lemma fiberPoint_bijective : Function.Bijective fiberPoint := by
  -- Combine the quotient-coordinate separation with the representative classification.
  exact ⟨fiberPoint_injective, fiberPoint_surjective⟩

/-- Helper for Example 81.2: every covering transformation fixes the common axis vertex. -/
private lemma coveringTransformation_fix_origin
    (h : CoveringTransformation.group proj) :
    h origin = origin := by
  have hcover : proj ∘ (h : Total → Total) = proj :=
    (CoveringTransformation.mem_group proj h.1).mp h.property
  have horiginProj : proj (h origin) = FigureEight.basepoint := by
    calc
      proj (h origin) = proj origin := by
        exact congrFun hcover origin
      _ = FigureEight.basepoint := proj_fiberPointValue FiberVertex.origin
  let imageOrigin : proj ⁻¹' {FigureEight.basepoint} := ⟨h origin, horiginProj⟩
  obtain ⟨v, hv⟩ := fiberPoint_surjective imageOrigin
  have hvValue : fiberPointValue v = h origin := congrArg Subtype.val hv
  cases v with
  | origin =>
      -- The origin case is already the desired fixed-point equation.
      exact hvValue.symm
  | horizontal n =>
      -- Along the vertical generator, the image has the nonzero constant horizontal coordinate.
      let F : ℝ → Total := fun y ↦ h (Quot.mk Gluing (yAxis y))
      have hF : Continuous F := h.1.continuous.comp continuous_yAxisInclusion
      have hy0 : Quot.mk Gluing (yAxis 0) = origin := by
        exact (Quot.sound Gluing.origin).symm
      have hFzero : F 0 = fiberPointValue (FiberVertex.horizontal n) := by
        calc
          F 0 = h origin := congrArg h hy0
          _ = fiberPointValue (FiberVertex.horizontal n) := hvValue.symm
      have hstart : horizontalCoordinate (F 0) = (n : ℝ) := by
        rw [hFzero]
        rfl
      have hprojFirst (y : ℝ) : (proj (F y) : Torus).1 = 1 := by
        have hcover : proj (F y) = proj (Quot.mk Gluing (yAxis y)) := by
          exact congrFun hcover (Quot.mk Gluing (yAxis y))
        rw [hcover, proj_yAxis]
        rfl
      have hconstant := horizontalCoordinate_eq_constant_of_proj_fst_eq_one
        F hF 0 (n : ℝ) hstart hprojFirst
      have hFoneProj : proj (F 1) = FigureEight.basepoint := by
        calc
          proj (F 1) = proj (Quot.mk Gluing (yAxis 1)) := by
            exact congrFun hcover (Quot.mk Gluing (yAxis 1))
          _ = FigureEight.basepoint := by
            apply Subtype.ext
            simp [proj_yAxis, secondCircle, FigureEight.basepoint, Circle.turnExp_one]
      let imageOne : proj ⁻¹' {FigureEight.basepoint} := ⟨F 1, hFoneProj⟩
      obtain ⟨w, hw⟩ := fiberPoint_surjective imageOne
      have hwCoordinate : (fiberVertexCoordinate w).1 = (n : ℝ) := by
        calc
          (fiberVertexCoordinate w).1 = horizontalCoordinate (fiberPoint w) := by
            exact congrArg Prod.fst (fiberPoint_coordinates w).symm
          _ = horizontalCoordinate imageOne :=
            congrArg (fun e : proj ⁻¹' {FigureEight.basepoint} ↦ horizontalCoordinate e.1) hw
          _ = (n : ℝ) := hconstant 1
      have hwVertex := fiberVertex_eq_horizontal_of_fst_eq w n hwCoordinate
      have hwValue : fiberPointValue w = F 1 := congrArg Subtype.val hw
      have hFone : F 1 = fiberPointValue (FiberVertex.horizontal n) := by
        rw [hwVertex] at hwValue
        exact hwValue.symm
      have hyEndpoints : Quot.mk Gluing (yAxis 0) = Quot.mk Gluing (yAxis 1) := by
        apply h.1.injective
        exact hFzero.trans hFone.symm
      have hvertical := congrArg verticalCoordinate hyEndpoints
      norm_num [verticalCoordinate, verticalCoordinateRaw, yAxis] at hvertical
  | vertical n =>
      -- The horizontal generator gives the symmetric contradiction at a vertical vertex.
      let F : ℝ → Total := fun x ↦ h (Quot.mk Gluing (xAxis x))
      have hF : Continuous F := h.1.continuous.comp continuous_xAxisInclusion
      have hFzero : F 0 = fiberPointValue (FiberVertex.vertical n) := by
        calc
          F 0 = h origin := rfl
          _ = fiberPointValue (FiberVertex.vertical n) := hvValue.symm
      have hstart : verticalCoordinate (F 0) = (n : ℝ) := by
        rw [hFzero]
        rfl
      have hprojSecond (x : ℝ) : (proj (F x) : Torus).2 = 1 := by
        have hcover : proj (F x) = proj (Quot.mk Gluing (xAxis x)) := by
          exact congrFun hcover (Quot.mk Gluing (xAxis x))
        rw [hcover, proj_xAxis]
        rfl
      have hconstant := verticalCoordinate_eq_constant_of_proj_snd_eq_one
        F hF 0 (n : ℝ) hstart hprojSecond
      have hFoneProj : proj (F 1) = FigureEight.basepoint := by
        calc
          proj (F 1) = proj (Quot.mk Gluing (xAxis 1)) := by
            exact congrFun hcover (Quot.mk Gluing (xAxis 1))
          _ = FigureEight.basepoint := by
            apply Subtype.ext
            simp [proj_xAxis, firstCircle, FigureEight.basepoint, Circle.turnExp_one]
      let imageOne : proj ⁻¹' {FigureEight.basepoint} := ⟨F 1, hFoneProj⟩
      obtain ⟨w, hw⟩ := fiberPoint_surjective imageOne
      have hwCoordinate : (fiberVertexCoordinate w).2 = (n : ℝ) := by
        calc
          (fiberVertexCoordinate w).2 = verticalCoordinate (fiberPoint w) := by
            exact congrArg Prod.snd (fiberPoint_coordinates w).symm
          _ = verticalCoordinate imageOne :=
            congrArg (fun e : proj ⁻¹' {FigureEight.basepoint} ↦ verticalCoordinate e.1) hw
          _ = (n : ℝ) := hconstant 1
      have hwVertex := fiberVertex_eq_vertical_of_snd_eq w n hwCoordinate
      have hwValue : fiberPointValue w = F 1 := congrArg Subtype.val hw
      have hFone : F 1 = fiberPointValue (FiberVertex.vertical n) := by
        rw [hwVertex] at hwValue
        exact hwValue.symm
      have hxEndpoints : Quot.mk Gluing (xAxis 0) = Quot.mk Gluing (xAxis 1) := by
        apply h.1.injective
        exact hFzero.trans hFone.symm
      have hhorizontal := congrArg horizontalCoordinate hxEndpoints
      norm_num [horizontalCoordinate, horizontalCoordinateRaw, xAxis] at hhorizontal

/-- Helper for Example 81.2: projection and the two descended coordinates uniquely identify
a point of the horizontal axis. -/
private lemma eq_xAxis_of_coordinates (e : Total) (x : ℝ)
    (hhorizontal : horizontalCoordinate e = x)
    (hvertical : verticalCoordinate e = 0)
    (hproj : proj e = proj (Quot.mk Gluing (xAxis x))) :
    e = Quot.mk Gluing (xAxis x) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with y | e
      · -- The horizontal coordinate directly identifies another horizontal representative.
        change y = x at hhorizontal
        subst y
        rfl
      · rcases e with y | e
        · -- A vertical-axis representative with both coordinates zero is the glued origin.
          change y = 0 at hvertical
          subst y
          change (0 : ℝ) = x at hhorizontal
          subst x
          exact (Quot.sound Gluing.origin).symm
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            -- Equality of projections forces a tangent-circle point to be its attachment.
            change (n : ℝ) = x at hhorizontal
            have hleft : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inl (n, z))))) = secondCircle z := by
              simpa only [xCircle] using proj_xCircle n z
            have hright : proj (Quot.mk Gluing (xAxis x)) =
                firstCircle (Circle.turnExp x) := proj_xAxis x
            have hz := congrArg (fun w : FigureEight ↦ (w : Torus).2) hproj
            rw [hleft, hright] at hz
            have hzOne : z = 1 := by
              simpa [secondCircle, firstCircle] using hz
            subst z
            calc
              Quot.mk Gluing (xCircle n 1) = Quot.mk Gluing (xAxis (n : ℝ)) :=
                Quot.sound (Gluing.xCircle_base n)
              _ = Quot.mk Gluing (xAxis x) := congrArg (fun t ↦ Quot.mk Gluing (xAxis t))
                hhorizontal
          · rcases e with ⟨n, z⟩
            -- A nonzero vertical attachment cannot have vertical coordinate zero.
            change (n : ℝ) = 0 at hvertical
            have hn : (n : ℤ) = 0 := by
              exact_mod_cast hvertical
            exact False.elim (n.property hn)

/-- Helper for Example 81.2: projection and the two descended coordinates uniquely identify
a point of the vertical axis. -/
private lemma eq_yAxis_of_coordinates (e : Total) (y : ℝ)
    (hhorizontal : horizontalCoordinate e = 0)
    (hvertical : verticalCoordinate e = y)
    (hproj : proj e = proj (Quot.mk Gluing (yAxis y))) :
    e = Quot.mk Gluing (yAxis y) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · -- A horizontal-axis representative with both coordinates zero is the glued origin.
        change x = 0 at hhorizontal
        subst x
        change (0 : ℝ) = y at hvertical
        subst y
        exact Quot.sound Gluing.origin
      · rcases e with x | e
        · -- The vertical coordinate directly identifies another vertical representative.
          change x = y at hvertical
          subst x
          rfl
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            -- A nonzero horizontal attachment cannot have horizontal coordinate zero.
            change (n : ℝ) = 0 at hhorizontal
            have hn : (n : ℤ) = 0 := by
              exact_mod_cast hhorizontal
            exact False.elim (n.property hn)
          · rcases e with ⟨n, z⟩
            -- Equality of projections forces a tangent-circle point to be its attachment.
            change (n : ℝ) = y at hvertical
            have hleft : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inr (n, z))))) = firstCircle z := by
              simpa only [yCircle] using proj_yCircle n z
            have hright : proj (Quot.mk Gluing (yAxis y)) =
                secondCircle (Circle.turnExp y) := proj_yAxis y
            have hz := congrArg (fun w : FigureEight ↦ (w : Torus).1) hproj
            rw [hleft, hright] at hz
            have hzOne : z = 1 := by
              simpa [firstCircle, secondCircle] using hz
            subst z
            calc
              Quot.mk Gluing (yCircle n 1) = Quot.mk Gluing (yAxis (n : ℝ)) :=
                Quot.sound (Gluing.yCircle_base n)
              _ = Quot.mk Gluing (yAxis y) := congrArg (fun t ↦ Quot.mk Gluing (yAxis t))
                hvertical

/-- Helper for Example 81.2: projection and the descended coordinates uniquely identify a
point on a circle tangent to the horizontal axis. -/
private lemma eq_xCircle_of_coordinates (e : Total) (n : NonzeroInt) (z : Circle)
    (hhorizontal : horizontalCoordinate e = (n : ℝ))
    (hvertical : verticalCoordinate e = 0)
    (hproj : proj e = proj (Quot.mk Gluing (xCircle n z))) :
    e = Quot.mk Gluing (xCircle n z) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · -- An axis representative can match this circle only at the glued attachment.
        change x = (n : ℝ) at hhorizontal
        have hleft : proj (Quot.mk Gluing (Sum.inl x)) =
            firstCircle (Circle.turnExp x) := by
          simpa only [xAxis] using proj_xAxis x
        have hright : proj (Quot.mk Gluing (xCircle n z)) = secondCircle z :=
          proj_xCircle n z
        have hz := congrArg (fun w : FigureEight ↦ (w : Torus).2) hproj
        rw [hleft, hright] at hz
        have hzOne : z = 1 := by
          simpa [firstCircle, secondCircle] using hz.symm
        subst z
        calc
          Quot.mk Gluing (Sum.inl x) = Quot.mk Gluing (xAxis (n : ℝ)) := by
            exact congrArg (fun t ↦ Quot.mk Gluing (xAxis t)) hhorizontal
          _ = Quot.mk Gluing (xCircle n 1) :=
            (Quot.sound (Gluing.xCircle_base n)).symm
      · rcases e with y | e
        · -- A nonzero horizontal attachment cannot have horizontal coordinate zero.
          change (0 : ℝ) = n at hhorizontal
          have hn : (0 : ℤ) = n := by
            exact_mod_cast hhorizontal
          exact False.elim (n.property hn.symm)
        · rcases e with e | e
          · rcases e with ⟨m, w⟩
            -- Within the same circle family, the coordinate and projection recover both indices.
            change (m : ℝ) = n at hhorizontal
            have hmn : (m : ℤ) = n := by
              exact_mod_cast hhorizontal
            have hm : m = n := Subtype.ext hmn
            subst m
            have hleft : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inl (n, w))))) = secondCircle w := by
              simpa only [xCircle] using proj_xCircle n w
            have hright : proj (Quot.mk Gluing (xCircle n z)) = secondCircle z :=
              proj_xCircle n z
            have hw := congrArg (fun q : FigureEight ↦ (q : Torus).2) hproj
            rw [hleft, hright] at hw
            have hwz : w = z := by
              simpa [secondCircle] using hw
            subst w
            rfl
          · rcases e with ⟨m, w⟩
            -- The other circle family has horizontal coordinate zero.
            change (0 : ℝ) = n at hhorizontal
            have hn : (0 : ℤ) = n := by
              exact_mod_cast hhorizontal
            exact False.elim (n.property hn.symm)

/-- Helper for Example 81.2: projection and the descended coordinates uniquely identify a
point on a circle tangent to the vertical axis. -/
private lemma eq_yCircle_of_coordinates (e : Total) (n : NonzeroInt) (z : Circle)
    (hhorizontal : horizontalCoordinate e = 0)
    (hvertical : verticalCoordinate e = (n : ℝ))
    (hproj : proj e = proj (Quot.mk Gluing (yCircle n z))) :
    e = Quot.mk Gluing (yCircle n z) := by
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · -- A nonzero vertical attachment cannot have vertical coordinate zero.
        change (0 : ℝ) = n at hvertical
        have hn : (0 : ℤ) = n := by
          exact_mod_cast hvertical
        exact False.elim (n.property hn.symm)
      · rcases e with y | e
        · -- An axis representative can match this circle only at the glued attachment.
          change y = (n : ℝ) at hvertical
          have hleft : proj (Quot.mk Gluing (Sum.inr (Sum.inl y))) =
              secondCircle (Circle.turnExp y) := by
            simpa only [yAxis] using proj_yAxis y
          have hright : proj (Quot.mk Gluing (yCircle n z)) = firstCircle z :=
            proj_yCircle n z
          have hz := congrArg (fun w : FigureEight ↦ (w : Torus).1) hproj
          rw [hleft, hright] at hz
          have hzOne : z = 1 := by
            simpa [secondCircle, firstCircle] using hz.symm
          subst z
          calc
            Quot.mk Gluing (Sum.inr (Sum.inl y)) = Quot.mk Gluing (yAxis (n : ℝ)) := by
              exact congrArg (fun t ↦ Quot.mk Gluing (yAxis t)) hvertical
            _ = Quot.mk Gluing (yCircle n 1) :=
              (Quot.sound (Gluing.yCircle_base n)).symm
        · rcases e with e | e
          · rcases e with ⟨m, w⟩
            -- The other circle family has vertical coordinate zero.
            change (0 : ℝ) = n at hvertical
            have hn : (0 : ℤ) = n := by
              exact_mod_cast hvertical
            exact False.elim (n.property hn.symm)
          · rcases e with ⟨m, w⟩
            -- Within the same circle family, the coordinate and projection recover both indices.
            change (m : ℝ) = n at hvertical
            have hmn : (m : ℤ) = n := by
              exact_mod_cast hvertical
            have hm : m = n := Subtype.ext hmn
            subst m
            have hleft : proj (Quot.mk Gluing
                (Sum.inr (Sum.inr (Sum.inr (n, w))))) = firstCircle w := by
              simpa only [yCircle] using proj_yCircle n w
            have hright : proj (Quot.mk Gluing (yCircle n z)) = firstCircle z :=
              proj_yCircle n z
            have hw := congrArg (fun q : FigureEight ↦ (q : Torus).1) hproj
            rw [hleft, hright] at hw
            have hwz : w = z := by
              simpa [firstCircle] using hw
            subst w
            rfl

/-- Helper for Example 81.2: a covering transformation fixing the origin fixes the horizontal
axis pointwise. -/
private lemma coveringTransformation_fix_xAxis
    (h : CoveringTransformation.group proj) (horigin : h origin = origin) (x : ℝ) :
    h (Quot.mk Gluing (xAxis x)) = Quot.mk Gluing (xAxis x) := by
  have hcover : proj ∘ (h : Total → Total) = proj :=
    (CoveringTransformation.mem_group proj h.1).mp h.property
  let F : ℝ → Total := fun t ↦ h (Quot.mk Gluing (xAxis t))
  have hF : Continuous F := h.1.continuous.comp continuous_xAxisInclusion
  have hstartVertical : verticalCoordinate (F 0) = 0 := by
    have hFzero : F 0 = origin := by
      calc
        F 0 = h origin := rfl
        _ = origin := horigin
    rw [hFzero]
    rfl
  have hprojSecond (t : ℝ) : (proj (F t) : Torus).2 = 1 := by
    calc
      (proj (F t) : Torus).2 = (proj (Quot.mk Gluing (xAxis t)) : Torus).2 :=
        congrArg (fun w : FigureEight ↦ (w : Torus).2)
          (congrFun hcover (Quot.mk Gluing (xAxis t)))
      _ = 1 := by
        rw [proj_xAxis]
        rfl
  have hvertical := verticalCoordinate_eq_constant_of_proj_snd_eq_one
    F hF 0 0 hstartVertical hprojSecond
  have hturnExp (t : ℝ) :
      Circle.turnExp (horizontalCoordinate (F t)) = Circle.turnExp t := by
    calc
      Circle.turnExp (horizontalCoordinate (F t)) = (proj (F t) : Torus).1 :=
        (proj_fst_eq_turnExp_horizontal_of_vertical_eq_zero (F t) (hvertical t)).symm
      _ = (proj (Quot.mk Gluing (xAxis t)) : Torus).1 :=
        congrArg (fun w : FigureEight ↦ (w : Torus).1)
          (congrFun hcover (Quot.mk Gluing (xAxis t)))
      _ = Circle.turnExp t := by
        rw [proj_xAxis]
        rfl
  have hstartHorizontal : horizontalCoordinate (F 0) = 0 := by
    have hFzero : F 0 = origin := by
      calc
        F 0 = h origin := rfl
        _ = origin := horigin
    rw [hFzero]
    rfl
  have hcomp : Circle.turnExp ∘ (horizontalCoordinate ∘ F) =
      Circle.turnExp ∘ (fun t : ℝ ↦ t) := by
    funext t
    exact hturnExp t
  have hhorizontalFunction := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    (continuous_horizontalCoordinate.comp hF) continuous_id hcomp 0 hstartHorizontal
  have hhorizontal : horizontalCoordinate (F x) = x := congrFun hhorizontalFunction x
  have hproj : proj (F x) = proj (Quot.mk Gluing (xAxis x)) :=
    congrFun hcover (Quot.mk Gluing (xAxis x))
  -- The stable coordinate normal form now identifies the total-space point.
  exact eq_xAxis_of_coordinates (F x) x hhorizontal (hvertical x) hproj

/-- Helper for Example 81.2: a covering transformation fixing the origin fixes the vertical
axis pointwise. -/
private lemma coveringTransformation_fix_yAxis
    (h : CoveringTransformation.group proj) (horigin : h origin = origin) (y : ℝ) :
    h (Quot.mk Gluing (yAxis y)) = Quot.mk Gluing (yAxis y) := by
  have hcover : proj ∘ (h : Total → Total) = proj :=
    (CoveringTransformation.mem_group proj h.1).mp h.property
  let F : ℝ → Total := fun t ↦ h (Quot.mk Gluing (yAxis t))
  have hF : Continuous F := h.1.continuous.comp continuous_yAxisInclusion
  have hy0 : Quot.mk Gluing (yAxis 0) = origin := (Quot.sound Gluing.origin).symm
  have hstartHorizontal : horizontalCoordinate (F 0) = 0 := by
    have hFzero : F 0 = origin := by
      calc
        F 0 = h origin := congrArg h hy0
        _ = origin := horigin
    rw [hFzero]
    rfl
  have hprojFirst (t : ℝ) : (proj (F t) : Torus).1 = 1 := by
    calc
      (proj (F t) : Torus).1 = (proj (Quot.mk Gluing (yAxis t)) : Torus).1 :=
        congrArg (fun w : FigureEight ↦ (w : Torus).1)
          (congrFun hcover (Quot.mk Gluing (yAxis t)))
      _ = 1 := by
        rw [proj_yAxis]
        rfl
  have hhorizontal := horizontalCoordinate_eq_constant_of_proj_fst_eq_one
    F hF 0 0 hstartHorizontal hprojFirst
  have hturnExp (t : ℝ) :
      Circle.turnExp (verticalCoordinate (F t)) = Circle.turnExp t := by
    calc
      Circle.turnExp (verticalCoordinate (F t)) = (proj (F t) : Torus).2 :=
        (proj_snd_eq_turnExp_vertical_of_horizontal_eq_zero (F t) (hhorizontal t)).symm
      _ = (proj (Quot.mk Gluing (yAxis t)) : Torus).2 :=
        congrArg (fun w : FigureEight ↦ (w : Torus).2)
          (congrFun hcover (Quot.mk Gluing (yAxis t)))
      _ = Circle.turnExp t := by
        rw [proj_yAxis]
        rfl
  have hstartVertical : verticalCoordinate (F 0) = 0 := by
    have hFzero : F 0 = origin := by
      calc
        F 0 = h origin := congrArg h hy0
        _ = origin := horigin
    rw [hFzero]
    rfl
  have hcomp : Circle.turnExp ∘ (verticalCoordinate ∘ F) =
      Circle.turnExp ∘ (fun t : ℝ ↦ t) := by
    funext t
    exact hturnExp t
  have hverticalFunction := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    (continuous_verticalCoordinate.comp hF) continuous_id hcomp 0 hstartVertical
  have hvertical : verticalCoordinate (F y) = y := congrFun hverticalFunction y
  have hproj : proj (F y) = proj (Quot.mk Gluing (yAxis y)) :=
    congrFun hcover (Quot.mk Gluing (yAxis y))
  -- The symmetric coordinate normal form identifies the vertical-axis point.
  exact eq_yAxis_of_coordinates (F y) y (hhorizontal y) hvertical hproj

/-- Helper for Example 81.2: after the horizontal axis is fixed, every circle tangent to it
is fixed pointwise. -/
private lemma coveringTransformation_fix_xCircle
    (h : CoveringTransformation.group proj) (horigin : h origin = origin)
    (n : NonzeroInt) (z : Circle) :
    h (Quot.mk Gluing (xCircle n z)) = Quot.mk Gluing (xCircle n z) := by
  have hcover : proj ∘ (h : Total → Total) = proj :=
    (CoveringTransformation.mem_group proj h.1).mp h.property
  let F : Circle → Total := fun w ↦ h (Quot.mk Gluing (xCircle n w))
  have hF : Continuous F := h.1.continuous.comp (continuous_xCircleInclusion n)
  have hFone : F 1 = Quot.mk Gluing (xAxis (n : ℝ)) := by
    calc
      F 1 = h (Quot.mk Gluing (xAxis (n : ℝ))) :=
        congrArg h (Quot.sound (Gluing.xCircle_base n))
      _ = Quot.mk Gluing (xAxis (n : ℝ)) := coveringTransformation_fix_xAxis h horigin n
  have hstart : horizontalCoordinate (F 1) = (n : ℝ) := by
    rw [hFone]
    rfl
  have hprojFirst (w : Circle) : (proj (F w) : Torus).1 = 1 := by
    calc
      (proj (F w) : Torus).1 = (proj (Quot.mk Gluing (xCircle n w)) : Torus).1 :=
        congrArg (fun q : FigureEight ↦ (q : Torus).1)
          (congrFun hcover (Quot.mk Gluing (xCircle n w)))
      _ = 1 := by
        rw [proj_xCircle]
        rfl
  have hhorizontal := horizontalCoordinate_eq_constant_of_proj_fst_eq_one
    F hF 1 (n : ℝ) hstart hprojFirst
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.property
  have hhorizontalNe : horizontalCoordinate (F z) ≠ 0 := by
    rw [hhorizontal z]
    exact hnReal
  have hvertical : verticalCoordinate (F z) = 0 :=
    verticalCoordinate_eq_zero_of_horizontalCoordinate_ne_zero (F z) hhorizontalNe
  have hproj : proj (F z) = proj (Quot.mk Gluing (xCircle n z)) :=
    congrFun hcover (Quot.mk Gluing (xCircle n z))
  -- Nonzero attachment coordinate, zero transverse coordinate, and projection determine the point.
  exact eq_xCircle_of_coordinates (F z) n z (hhorizontal z) hvertical hproj

/-- Helper for Example 81.2: after the vertical axis is fixed, every circle tangent to it
is fixed pointwise. -/
private lemma coveringTransformation_fix_yCircle
    (h : CoveringTransformation.group proj) (horigin : h origin = origin)
    (n : NonzeroInt) (z : Circle) :
    h (Quot.mk Gluing (yCircle n z)) = Quot.mk Gluing (yCircle n z) := by
  have hcover : proj ∘ (h : Total → Total) = proj :=
    (CoveringTransformation.mem_group proj h.1).mp h.property
  let F : Circle → Total := fun w ↦ h (Quot.mk Gluing (yCircle n w))
  have hF : Continuous F := h.1.continuous.comp (continuous_yCircleInclusion n)
  have hFone : F 1 = Quot.mk Gluing (yAxis (n : ℝ)) := by
    calc
      F 1 = h (Quot.mk Gluing (yAxis (n : ℝ))) :=
        congrArg h (Quot.sound (Gluing.yCircle_base n))
      _ = Quot.mk Gluing (yAxis (n : ℝ)) := coveringTransformation_fix_yAxis h horigin n
  have hstart : verticalCoordinate (F 1) = (n : ℝ) := by
    rw [hFone]
    rfl
  have hprojSecond (w : Circle) : (proj (F w) : Torus).2 = 1 := by
    calc
      (proj (F w) : Torus).2 = (proj (Quot.mk Gluing (yCircle n w)) : Torus).2 :=
        congrArg (fun q : FigureEight ↦ (q : Torus).2)
          (congrFun hcover (Quot.mk Gluing (yCircle n w)))
      _ = 1 := by
        rw [proj_yCircle]
        rfl
  have hvertical := verticalCoordinate_eq_constant_of_proj_snd_eq_one
    F hF 1 (n : ℝ) hstart hprojSecond
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.property
  have hverticalNe : verticalCoordinate (F z) ≠ 0 := by
    rw [hvertical z]
    exact hnReal
  have hhorizontal : horizontalCoordinate (F z) = 0 :=
    horizontalCoordinate_eq_zero_of_verticalCoordinate_ne_zero (F z) hverticalNe
  have hproj : proj (F z) = proj (Quot.mk Gluing (yCircle n z)) :=
    congrFun hcover (Quot.mk Gluing (yCircle n z))
  -- The symmetric coordinate normal form determines the vertical tangent-circle point.
  exact eq_yCircle_of_coordinates (F z) n z hhorizontal (hvertical z) hproj

/-- Example 81.2. The covering-transformation group of the §60 figure-eight cover by
the coordinate axes with tangent circles at the nonzero integer points is trivial. -/
theorem group_eq_bot :
    𝒞(Total, proj, FigureEight) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro g hg
  let h : CoveringTransformation.group proj := ⟨g, hg⟩
  have horigin : h origin = origin := coveringTransformation_fix_origin h
  -- Once the common vertex is fixed, the axis and tangent-circle rigidity lemmas cover all
  -- representatives of the quotient total space.
  apply Homeomorph.ext
  intro e
  induction e using Quot.inductionOn with
  | _ e =>
      rcases e with x | e
      · simpa only [h, xAxis, Homeomorph.one_apply] using
          coveringTransformation_fix_xAxis h horigin x
      · rcases e with y | e
        · simpa only [h, yAxis, Homeomorph.one_apply] using
            coveringTransformation_fix_yAxis h horigin y
        · rcases e with e | e
          · rcases e with ⟨n, z⟩
            simpa only [h, xCircle, Homeomorph.one_apply] using
              coveringTransformation_fix_xCircle h horigin n z
          · rcases e with ⟨n, z⟩
            simpa only [h, yCircle, Homeomorph.one_apply] using
              coveringTransformation_fix_yCircle h horigin n z

end FigureEightTangentCircleCover
