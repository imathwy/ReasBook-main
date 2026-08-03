module

public import Topology_Munkres_2000.Book.Definition_52_4.FundamentalGroup
public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Theorem_53_3.Product
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Piecewise
import all Topology_Munkres_2000.Book.Definition_53_5.FigureEight

public section

namespace FigureEightCommutatorGrid

/-- Helper for Lemma 60.5: the coordinatewise circle exponential on the plane. -/
noncomputable def ambientCover : ℝ × ℝ → Torus :=
  Prod.map Circle.turnExp Circle.turnExp

/-- Helper for Lemma 60.5: the inverse image of the figure eight under the coordinatewise
circle exponential. -/
def carrier : Set (ℝ × ℝ) :=
  ambientCover ⁻¹' FigureEight.carrier

/-- Helper for Lemma 60.5: the infinite-grid total space. -/
abbrev Total := carrier

/-- Helper for Lemma 60.5: the coordinatewise circle exponential restricted to the grid. -/
noncomputable def cover : Total → FigureEight :=
  FigureEight.carrier.restrictPreimage ambientCover

/-- Helper for Lemma 60.5: a point lies in the grid exactly when one coordinate is integral. -/
lemma mem_iff (x : ℝ × ℝ) :
    x ∈ carrier ↔ (∃ n : ℤ, x.2 = n) ∨ ∃ n : ℤ, x.1 = n := by
  simp only [carrier, Set.mem_preimage, FigureEight.mem_iff, ambientCover,
    Prod.map_apply', Circle.turnExp_eq_one_iff]

/-- Helper for Lemma 60.5: the grid projection is a covering map. -/
lemma cover_isCoveringMap : IsCoveringMap cover := by
  -- Restrict the product of the two standard circle coverings to the figure eight.
  exact (Circle.isCoveringMap_turnExp.prodMap
    Circle.isCoveringMap_turnExp).restrictPreimage FigureEight.carrier

/-- Helper for Lemma 60.5: the grid projection is coordinatewise circle exponential. -/
lemma cover_apply (x : Total) :
    (cover x : Torus) = ambientCover x := by
  exact congrArg Subtype.val
    (Set.restrictPreimage_mk (t := FigureEight.carrier) (f := ambientCover) x.property)

/-- Helper for Lemma 60.5: a circle-valued detector supported on the horizontal grid line
through the origin. -/
noncomputable def horizontalDetector (x : Total) : Circle :=
  if (x : ℝ × ℝ).2 = 0 then Circle.turnExp (x : ℝ × ℝ).1 else 1

/-- Helper for Lemma 60.5: every frontier point of the horizontal grid line has integral
first coordinate. -/
lemma horizontalLine_frontier_fst_mem_range_intCast
    {x : Total}
    (hx : x ∈ frontier {y : Total | (y : ℝ × ℝ).2 = 0}) :
    (x : ℝ × ℝ).1 ∈ Set.range (Int.cast : ℤ → ℝ) := by
  let horizontalLine : Set Total :=
    {y | (y : ℝ × ℝ).2 = 0}
  have horizontalLine_closed : IsClosed horizontalLine := by
    exact isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have x_horizontal : x ∈ horizontalLine := horizontalLine_closed.frontier_subset hx
  by_contra x_not_integral
  let neighborhood : Set (ℝ × ℝ) :=
    (Set.range (Int.cast : ℤ → ℝ))ᶜ ×ˢ Set.Ioo (-1 : ℝ) 1
  have neighborhood_open : IsOpen neighborhood :=
    Real.isOpen_compl_range_intCast.prod isOpen_Ioo
  have x_mem_neighborhood : (x : ℝ × ℝ) ∈ neighborhood := by
    refine ⟨x_not_integral, ?_⟩
    dsimp [horizontalLine] at x_horizontal
    rw [x_horizontal]
    norm_num
  have neighborhood_preimage_subset :
      Subtype.val ⁻¹' neighborhood ⊆ horizontalLine := by
    intro y hy
    rcases (mem_iff y).mp y.property with hy_grid | hy_grid
    · rcases hy_grid with ⟨n, hn⟩
      have hn_bounds : (-1 : ℝ) < n ∧ (n : ℝ) < 1 := by
        rw [← hn]
        exact hy.2
      have hn_lower : (-1 : ℤ) < n := by
        exact_mod_cast hn_bounds.1
      have hn_upper : n < (1 : ℤ) := by
        exact_mod_cast hn_bounds.2
      have n_zero : n = 0 := by
        omega
      simp [horizontalLine, hn, n_zero]
    · rcases hy_grid with ⟨n, hn⟩
      exact False.elim (hy.1 ⟨n, hn.symm⟩)
  have x_interior : x ∈ interior horizontalLine := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset
      ((neighborhood_open.preimage continuous_subtype_val).mem_nhds x_mem_neighborhood)
      neighborhood_preimage_subset
  exact (mem_frontier_iff_notMem_interior x_horizontal).mp hx x_interior

/-- Helper for Lemma 60.5: the horizontal grid detector is continuous. -/
lemma continuous_horizontalDetector : Continuous horizontalDetector := by
  apply continuous_if
  · intro x hx
    have hx_integral := horizontalLine_frontier_fst_mem_range_intCast hx
    rcases hx_integral with ⟨n, hn⟩
    simpa [hn] using Circle.turnExp_int n
  · exact (Circle.isCoveringMap_turnExp.continuous.comp
      (continuous_fst.comp continuous_subtype_val)).continuousOn
  · exact continuous_const.continuousOn

end FigureEightCommutatorGrid

namespace IsCoveringMap

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X}

/-- Helper for Lemma 60.5: a concrete lift computes the monodromy of its projected loop. -/
lemma monodromy_mk_eq_of_lift (hp : IsCoveringMap p) {x : X}
    {e₀ e₁ : p ⁻¹' {x}} (γ : Path x x) (Γ : Path e₀.1 e₁.1)
    (hΓ : ∀ t, p (Γ t) = γ t) :
    hp.monodromy (Path.Homotopic.Quotient.mk γ) e₀ = e₁ := by
  -- Reduce monodromy to the quotient class of the supplied total-space lift.
  apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ)
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  ext t
  exact hΓ t

end IsCoveringMap

/-- Lemma 60.5. The fundamental group of the figure eight is not abelian. -/
theorem figureEightFundamentalGroup_not_abelian :
    ¬ IsMulCommutative π₁(FigureEight, FigureEight.basepoint) := by
  -- Work in the earlier infinite-grid covering and compare the two routes across one unit square.
  have origin_mem_grid : (0, 0) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 0
    norm_num
  have right_mem_grid : (1, 0) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 0
    norm_num
  have top_mem_grid : (0, 1) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 1
    norm_num
  have corner_mem_grid : (1, 1) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 1
    norm_num
  let origin : FigureEightCommutatorGrid.Total := ⟨(0, 0), origin_mem_grid⟩
  let right : FigureEightCommutatorGrid.Total := ⟨(1, 0), right_mem_grid⟩
  let top : FigureEightCommutatorGrid.Total := ⟨(0, 1), top_mem_grid⟩
  let corner : FigureEightCommutatorGrid.Total := ⟨(1, 1), corner_mem_grid⟩
  have origin_mem : FigureEightCommutatorGrid.cover origin = FigureEight.basepoint := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover origin : Torus) =
          FigureEightCommutatorGrid.ambientCover origin :=
        FigureEightCommutatorGrid.cover_apply _
      _ = (1, 1) := by
        simp only [FigureEightCommutatorGrid.ambientCover, origin, Prod.map_apply',
          Circle.turnExp_zero]
      _ = (FigureEight.basepoint : Torus) := rfl
  have right_mem : FigureEightCommutatorGrid.cover right = FigureEight.basepoint := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover right : Torus) =
          FigureEightCommutatorGrid.ambientCover right :=
        FigureEightCommutatorGrid.cover_apply _
      _ = (1, 1) := by
        simp only [FigureEightCommutatorGrid.ambientCover, right, Prod.map_apply',
          Circle.turnExp_one, Circle.turnExp_zero]
      _ = (FigureEight.basepoint : Torus) := rfl
  have top_mem : FigureEightCommutatorGrid.cover top = FigureEight.basepoint := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover top : Torus) =
          FigureEightCommutatorGrid.ambientCover top :=
        FigureEightCommutatorGrid.cover_apply _
      _ = (1, 1) := by
        simp only [FigureEightCommutatorGrid.ambientCover, top, Prod.map_apply',
          Circle.turnExp_zero, Circle.turnExp_one]
      _ = (FigureEight.basepoint : Torus) := rfl
  have corner_mem : FigureEightCommutatorGrid.cover corner = FigureEight.basepoint := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover corner : Torus) =
          FigureEightCommutatorGrid.ambientCover corner :=
        FigureEightCommutatorGrid.cover_apply _
      _ = (1, 1) := by
        simp only [FigureEightCommutatorGrid.ambientCover, corner, Prod.map_apply',
          Circle.turnExp_one]
      _ = (FigureEight.basepoint : Torus) := rfl
  have bottom_mem (t : unitInterval) :
      ((t : ℝ), 0) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 0
    norm_num
  let bottomMap : unitInterval → FigureEightCommutatorGrid.Total := fun t ↦
    ⟨((t : ℝ), 0), bottom_mem t⟩
  have bottomMap_cont : Continuous bottomMap := by
    exact (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  have bottomMap_zero : bottomMap 0 = origin := by
    rfl
  have bottomMap_one : bottomMap 1 = right := by
    rfl
  let bottom : Path origin right :=
    ⟨⟨bottomMap, bottomMap_cont⟩, bottomMap_zero, bottomMap_one⟩
  have left_mem (t : unitInterval) :
      (0, (t : ℝ)) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    right
    use 0
    norm_num
  let leftMap : unitInterval → FigureEightCommutatorGrid.Total := fun t ↦
    ⟨(0, (t : ℝ)), left_mem t⟩
  have leftMap_cont : Continuous leftMap := by
    exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have leftMap_zero : leftMap 0 = origin := by
    rfl
  have leftMap_one : leftMap 1 = top := by
    rfl
  let left : Path origin top :=
    ⟨⟨leftMap, leftMap_cont⟩, leftMap_zero, leftMap_one⟩
  have rightEdge_mem (t : unitInterval) :
      (1, (t : ℝ)) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    right
    use 1
    norm_num
  let rightEdgeMap : unitInterval → FigureEightCommutatorGrid.Total := fun t ↦
    ⟨(1, (t : ℝ)), rightEdge_mem t⟩
  have rightEdgeMap_cont : Continuous rightEdgeMap := by
    exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have rightEdgeMap_zero : rightEdgeMap 0 = right := by
    rfl
  have rightEdgeMap_one : rightEdgeMap 1 = corner := by
    rfl
  let rightEdge : Path right corner :=
    ⟨⟨rightEdgeMap, rightEdgeMap_cont⟩, rightEdgeMap_zero, rightEdgeMap_one⟩
  have topEdge_mem (t : unitInterval) :
      ((t : ℝ), 1) ∈ FigureEightCommutatorGrid.carrier := by
    rw [FigureEightCommutatorGrid.mem_iff]
    left
    use 1
    norm_num
  let topEdgeMap : unitInterval → FigureEightCommutatorGrid.Total := fun t ↦
    ⟨((t : ℝ), 1), topEdge_mem t⟩
  have topEdgeMap_cont : Continuous topEdgeMap := by
    exact (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  have topEdgeMap_zero : topEdgeMap 0 = top := by
    rfl
  have topEdgeMap_one : topEdgeMap 1 = corner := by
    rfl
  let topEdge : Path top corner :=
    ⟨⟨topEdgeMap, topEdgeMap_cont⟩, topEdgeMap_zero, topEdgeMap_one⟩
  let bottomProjected :=
    bottom.map FigureEightCommutatorGrid.cover_isCoveringMap.continuous
  let leftProjected :=
    left.map FigureEightCommutatorGrid.cover_isCoveringMap.continuous
  let α : Path FigureEight.basepoint FigureEight.basepoint :=
    bottomProjected.cast origin_mem.symm right_mem.symm
  let β : Path FigureEight.basepoint FigureEight.basepoint :=
    leftProjected.cast origin_mem.symm top_mem.symm
  have bottom_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (bottom t) = α t := by
    rfl
  have left_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (left t) = β t := by
    rfl
  have rightEdge_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (rightEdge t) = β t := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover (rightEdge t) : Torus) =
          FigureEightCommutatorGrid.ambientCover (rightEdge t) :=
        FigureEightCommutatorGrid.cover_apply _
      _ = FigureEightCommutatorGrid.ambientCover (left t) := by
        rw [FigureEightCommutatorGrid.ambientCover]
        dsimp [rightEdge, rightEdgeMap, left, leftMap]
        rw [Circle.turnExp_one, Circle.turnExp_zero]
      _ = (FigureEightCommutatorGrid.cover (left t) : Torus) :=
        (FigureEightCommutatorGrid.cover_apply _).symm
      _ = β t := congrArg Subtype.val (left_projects t)
  have topEdge_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (topEdge t) = α t := by
    apply Subtype.ext
    calc
      (FigureEightCommutatorGrid.cover (topEdge t) : Torus) =
          FigureEightCommutatorGrid.ambientCover (topEdge t) :=
        FigureEightCommutatorGrid.cover_apply _
      _ = FigureEightCommutatorGrid.ambientCover (bottom t) := by
        rw [FigureEightCommutatorGrid.ambientCover]
        dsimp [topEdge, topEdgeMap, bottom, bottomMap]
        rw [Circle.turnExp_one, Circle.turnExp_zero]
      _ = (FigureEightCommutatorGrid.cover (bottom t) : Torus) :=
        (FigureEightCommutatorGrid.cover_apply _).symm
      _ = α t := congrArg Subtype.val (bottom_projects t)
  let bottomRight : Path origin corner := bottom.trans rightEdge
  let leftTop : Path origin corner := left.trans topEdge
  have bottomRight_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (bottomRight t) = (α.trans β) t := by
    dsimp [bottomRight]
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact bottom_projects _
    · exact rightEdge_projects _
  have leftTop_projects (t : unitInterval) :
      FigureEightCommutatorGrid.cover (leftTop t) = (β.trans α) t := by
    dsimp [leftTop]
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact left_projects _
    · exact topEdge_projects _
  -- Commutativity would identify the two projected routes across the square.
  intro hcommutative
  let a : π₁(FigureEight, FigureEight.basepoint) :=
    FundamentalGroup.LeftToRight.fromPath (Path.Homotopic.Quotient.mk α)
  let b : π₁(FigureEight, FigureEight.basepoint) :=
    FundamentalGroup.LeftToRight.fromPath (Path.Homotopic.Quotient.mk β)
  have hab : a * b = b * a :=
    (isMulCommutative_iff.mp hcommutative) a b
  have pathClasses_commute :
      (Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk β) =
        (Path.Homotopic.Quotient.mk β).trans (Path.Homotopic.Quotient.mk α) := by
    have hpaths := congrArg FundamentalGroup.LeftToRight.toPath hab
    simpa only [a, b, FundamentalGroup.LeftToRight.mul_def,
      FundamentalGroup.LeftToRight.toPath_fromPath] using hpaths
  have gridClasses_eq :
      Path.Homotopic.Quotient.mk bottomRight = Path.Homotopic.Quotient.mk leftTop := by
    apply FigureEightCommutatorGrid.cover_isCoveringMap.injective_path_homotopic_map
      origin corner
    calc
      (Path.Homotopic.Quotient.mk bottomRight).map
          ⟨FigureEightCommutatorGrid.cover,
            FigureEightCommutatorGrid.cover_isCoveringMap.continuous⟩ =
          ((Path.Homotopic.Quotient.mk α).trans
            (Path.Homotopic.Quotient.mk β)).cast origin_mem corner_mem := by
        rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans,
          ← Path.Homotopic.Quotient.mk_cast]
        apply eq_of_heq
        apply Path.Homotopic.hpath_hext
        intro t
        exact bottomRight_projects t
      _ = ((Path.Homotopic.Quotient.mk β).trans
            (Path.Homotopic.Quotient.mk α)).cast origin_mem corner_mem := by
        exact congrArg (fun γ ↦ γ.cast origin_mem corner_mem) pathClasses_commute
      _ = (Path.Homotopic.Quotient.mk leftTop).map
          ⟨FigureEightCommutatorGrid.cover,
            FigureEightCommutatorGrid.cover_isCoveringMap.continuous⟩ := by
        rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans,
          ← Path.Homotopic.Quotient.mk_cast]
        apply eq_of_heq
        apply Path.Homotopic.hpath_hext
        intro t
        exact (leftTop_projects t).symm
  -- The horizontal detector winds on the bottom edge and is constant on the other route.
  have detector_origin : FigureEightCommutatorGrid.horizontalDetector origin = 1 := by
    simp [FigureEightCommutatorGrid.horizontalDetector, origin, Circle.turnExp_zero]
  have detector_corner : FigureEightCommutatorGrid.horizontalDetector corner = 1 := by
    simp [FigureEightCommutatorGrid.horizontalDetector, corner]
  let detectorMap : C(FigureEightCommutatorGrid.Total, Circle) :=
    ⟨FigureEightCommutatorGrid.horizontalDetector,
      FigureEightCommutatorGrid.continuous_horizontalDetector⟩
  let bottomDetected : Path (1 : Circle) 1 :=
    (bottomRight.map FigureEightCommutatorGrid.continuous_horizontalDetector).cast
      detector_origin.symm detector_corner.symm
  let leftDetected : Path (1 : Circle) 1 :=
    (leftTop.map FigureEightCommutatorGrid.continuous_horizontalDetector).cast
      detector_origin.symm detector_corner.symm
  have detectedClasses_eq :
      Path.Homotopic.Quotient.mk bottomDetected =
        Path.Homotopic.Quotient.mk leftDetected := by
    have mappedClasses_eq := congrArg
      (fun γ ↦ (γ.map detectorMap).cast detector_origin.symm detector_corner.symm)
      gridClasses_eq
    simpa only [bottomDetected, leftDetected, detectorMap,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast] using
        mappedClasses_eq
  let bottomRealMap : unitInterval → ℝ := fun t ↦
    (bottomRight t : ℝ × ℝ).1
  have bottomRealMap_cont : Continuous bottomRealMap := by
    exact continuous_fst.comp (continuous_subtype_val.comp bottomRight.continuous)
  have bottomRealMap_zero : bottomRealMap 0 = 0 := by
    dsimp [bottomRealMap]
    rw [bottomRight.source]
  have bottomRealMap_one : bottomRealMap 1 = 1 := by
    dsimp [bottomRealMap]
    rw [bottomRight.target]
  let bottomReal : Path (0 : ℝ) 1 :=
    ⟨⟨bottomRealMap, bottomRealMap_cont⟩, bottomRealMap_zero, bottomRealMap_one⟩
  have bottomReal_projects (t : unitInterval) :
      Circle.turnExp (bottomReal t) = bottomDetected t := by
    change Circle.turnExp (bottomRight t : ℝ × ℝ).1 =
      FigureEightCommutatorGrid.horizontalDetector (bottomRight t)
    dsimp [bottomRight]
    rw [Path.trans_apply]
    split_ifs
    · simp [bottom, bottomMap, FigureEightCommutatorGrid.horizontalDetector]
    · simp [rightEdge, rightEdgeMap, FigureEightCommutatorGrid.horizontalDetector,
        Circle.turnExp_one]
  let leftReal : Path (0 : ℝ) 0 := Path.refl 0
  have leftReal_projects (t : unitInterval) :
      Circle.turnExp (leftReal t) = leftDetected t := by
    change Circle.turnExp 0 = FigureEightCommutatorGrid.horizontalDetector (leftTop t)
    dsimp [leftTop]
    rw [Path.trans_apply]
    split_ifs
    · simp [left, leftMap, FigureEightCommutatorGrid.horizontalDetector,
        Circle.turnExp_zero]
    · simp [topEdge, topEdgeMap, FigureEightCommutatorGrid.horizontalDetector,
        Circle.turnExp_zero]
  let zeroFiber : Circle.turnExp ⁻¹' {(1 : Circle)} :=
    ⟨0, Circle.turnExp_zero⟩
  let oneFiber : Circle.turnExp ⁻¹' {(1 : Circle)} :=
    ⟨1, Circle.turnExp_one⟩
  have bottomMovesZero :
      Circle.isCoveringMap_turnExp.monodromy
          (Path.Homotopic.Quotient.mk bottomDetected) zeroFiber = oneFiber := by
    exact Circle.isCoveringMap_turnExp.monodromy_mk_eq_of_lift
      bottomDetected bottomReal bottomReal_projects
  have leftFixesZero :
      Circle.isCoveringMap_turnExp.monodromy
          (Path.Homotopic.Quotient.mk leftDetected) zeroFiber = zeroFiber := by
    exact Circle.isCoveringMap_turnExp.monodromy_mk_eq_of_lift
      leftDetected leftReal leftReal_projects
  have fiber_eq := congrArg
    (fun γ ↦ Circle.isCoveringMap_turnExp.monodromy γ zeroFiber)
    detectedClasses_eq
  rw [bottomMovesZero, leftFixesZero] at fiber_eq
  have one_eq_zero := congrArg Subtype.val fiber_eq
  norm_num [oneFiber, zeroFiber] at one_eq_zero
