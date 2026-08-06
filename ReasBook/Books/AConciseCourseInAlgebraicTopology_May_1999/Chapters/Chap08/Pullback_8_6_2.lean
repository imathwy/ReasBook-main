import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.ContinuousMap.Interval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Reformulation_7_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Criterion_8_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1

open CategoryTheory Limits
open scoped PathSpace unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: `CategoryTheory.IsPullback` is the canonical pullback
-- square predicate, and the Chapter 8 surjectivity-free owner for the based lifting conclusion is
-- `HasBasedCoveringHomotopyProperty`, with Chapter 7's
-- `HasCoveringHomotopyProperty` available as a companion instance.

/-- The endpoint map `PY → Y` sends a based path to its terminal value. -/
theorem pathSpaceEndpointContinuous (Y : BasedSpace) :
    Continuous fun χ : P[underTopBasepoint Y] ↦ χ.endpoint := by
  -- Evaluate the ambient continuous path at the endpoint `1`.
  simpa [PathSpace.endpoint] using
    ((continuous_eval_const (1 : I)).comp continuous_subtype_val :
      Continuous fun χ : P[underTopBasepoint Y] ↦ χ.1 1)

/-- The endpoint map `PY → Y` as a morphism in `TopCat`. -/
def pathSpaceEndpoint (Y : BasedSpace) :
    TopCat.of P[underTopBasepoint Y] ⟶ Y.right :=
  TopCat.ofHom ⟨fun χ ↦ χ.endpoint, pathSpaceEndpointContinuous Y⟩

/-- Evaluating `pathSpaceEndpoint Y` returns the terminal point of the path. -/
@[simp] theorem pathSpaceEndpoint_apply (Y : BasedSpace) (χ : P[underTopBasepoint Y]) :
    pathSpaceEndpoint Y χ = χ.endpoint :=
  rfl

/-- The map `F_f → PY` sending a point of the homotopy fiber to its path coordinate is continuous.
-/
theorem homotopyFiberPathContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : HomotopyFiber f ↦ z.path := by
  -- This is the second projection of the ambient product restricted to the subtype.
  simpa [HomotopyFiber.path] using
    (continuous_snd.comp continuous_subtype_val :
      Continuous fun z : HomotopyFiber f ↦ z.1.2)

/-- The canonical map `F_f → PY` from the homotopy fiber to the path space. -/
def homotopyFiberPath {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber f).right ⟶ TopCat.of P[underTopBasepoint Y] :=
  TopCat.ofHom ⟨fun z ↦ z.path, homotopyFiberPathContinuous f⟩

/-- Evaluating `homotopyFiberPath f` returns the path coordinate of a homotopy-fiber point. -/
@[simp] theorem homotopyFiberPath_apply {X Y : BasedSpace} (f : X ⟶ Y) (z : HomotopyFiber f) :
    homotopyFiberPath f z = z.path :=
  rfl

/-- The projection `F_f → X` sending a point of the homotopy fiber to its `X`-coordinate is
continuous. -/
theorem homotopyFiberProjectionContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : HomotopyFiber f ↦ z.point := by
  -- This is the first projection of the ambient product restricted to the subtype.
  simpa [HomotopyFiber.point] using
    (continuous_fst.comp continuous_subtype_val :
      Continuous fun z : HomotopyFiber f ↦ z.1.1)

/-- The underlying `TopCat` morphism of the projection `F_f → X`. -/
def homotopyFiberProjectionHom {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber f).right ⟶ X.right :=
  TopCat.ofHom ⟨fun z ↦ z.point, homotopyFiberProjectionContinuous f⟩

/-- Evaluating `homotopyFiberProjectionHom f` returns the `X`-coordinate. -/
@[simp] theorem homotopyFiberProjectionHom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber f) :
    homotopyFiberProjectionHom f z = z.point :=
  rfl

/-- The projection `F_f → X` preserves the distinguished basepoints. -/
theorem homotopyFiberProjection_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber f).hom ≫ homotopyFiberProjectionHom f = X.hom := by
  -- Both maps out of the terminal object pick out the basepoint of `X`.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((homotopyFiber f).hom ≫ homotopyFiberProjectionHom f) x
        = homotopyFiberProjectionHom f (HomotopyFiber.basepoint f) := rfl
    _ = underTopBasepoint X := by
      simpa using HomotopyFiber.point_basepoint f
    _ = X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = X.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
      rw [hx]
    _ = X.hom x := by
      simp

/-- The based projection `F_f ⟶ X` from the homotopy fiber to the source of `f`. -/
def homotopyFiberProjection {X Y : BasedSpace} (f : X ⟶ Y) : homotopyFiber f ⟶ X :=
  Under.homMk (homotopyFiberProjectionHom f) (homotopyFiberProjection_w f)

/-- The underlying map of `homotopyFiberProjection f` sends `z` to its `X`-coordinate. -/
@[simp] theorem homotopyFiberProjection_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber f) :
    (homotopyFiberProjection f).right.hom z = z.point :=
  rfl

/-- Helper for Pullback 8.6.2: the literal subtype defining `HomotopyFiber f` already satisfies
the pullback universal property when the square is written in the order `(F_f → X, F_f → PY)`. -/
lemma homotopyFiber_isPullback_unflipped {X Y : BasedSpace} (f : X ⟶ Y) :
    IsPullback (homotopyFiberProjection f).right (homotopyFiberPath f)
      f.right (pathSpaceEndpoint Y) := by
  -- The square commutes because a homotopy-fiber point satisfies the endpoint equation.
  refine CategoryTheory.IsPullback.mk' ?_ ?_ ?_
  · ext z
    calc
      ((homotopyFiberProjection f).right ≫ f.right) z = f.right.hom z.point := by
        rfl
      _ = z.path.endpoint := HomotopyFiber.endpoint_eq z
      _ = (homotopyFiberPath f ≫ pathSpaceEndpoint Y) z := by
        rfl
  · intro T φ ψ hφ hψ
    -- Equality in the subtype follows from equality of the point and path coordinates.
    ext t
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun k : T ⟶ X.right ↦ k t) hφ)
      (congrArg (fun k : T ⟶ TopCat.of P[underTopBasepoint Y] ↦ k t) hψ)
  · intro T x χ hcomm
    -- Package the cone legs as a map into the defining pullback subtype.
    refine ⟨TopCat.ofHom ⟨fun t ↦ HomotopyFiber.mk (x t) (χ t) ?_, ?_⟩, ?_, ?_⟩
    · -- The defining equation holds pointwise by evaluating the cone commutativity.
      have ht := congrArg (fun k : T ⟶ Y.right ↦ k t) hcomm
      simpa using ht
    · -- Continuity comes from the product map into `X × PY`, followed by subtype inclusion.
      have hpair : Continuous fun t : T ↦ (x t, χ t) :=
        x.hom.continuous.prodMk χ.hom.continuous
      exact hpair.subtype_mk (fun t ↦ by
        have ht := congrArg (fun k : T ⟶ Y.right ↦ k t) hcomm
        simpa using ht)
    · ext t
      rfl
    · ext t
      rfl

/-- Pullback 8.6.2 (1). The homotopy fiber `F_f` of a based map `f : X ⟶ Y` fits into the
pullback square
`F_f ⟶ PY`
`↓      ↓`
`X  ⟶   Y`,
where the top map is `homotopyFiberPath f`, the left map is `homotopyFiberProjection f`, and the
right map is the path-space endpoint map `pathSpaceEndpoint Y`. -/
theorem homotopyFiber_isPullback {X Y : BasedSpace} (f : X ⟶ Y) :
    IsPullback (homotopyFiberPath f) (homotopyFiberProjection f).right
      (pathSpaceEndpoint Y) f.right := by
  -- Route correction: the subtype coordinates are ordered as `(x, χ)`, so prove the unflipped
  -- pullback square first and then flip it.
  simpa using (homotopyFiber_isPullback_unflipped f).flip

/-- Helper for Pullback 8.6.2: compress the stored `Y`-path in a homotopy-fiber point and then
follow the image of the new `X`-path under `f`. -/
noncomputable def homotopyFiberProjectionLiftValue {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathSpace ((homotopyFiberProjection f).right.hom)) (t s : I) : Y.right :=
  if (s : ℝ) ≤ 1 - (t : ℝ) / 2 then
    z.point.path (Set.projIcc 0 1 zero_le_one ((s : ℝ) / (1 - (t : ℝ) / 2)))
  else
    f.right.hom (z.path (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) + (t : ℝ) - 2)))

/-- Helper for Pullback 8.6.2: the compressed-append lift value is jointly continuous in the
mapping-path input and the two interval parameters. -/
theorem homotopyFiberProjectionLiftValue_continuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
      homotopyFiberProjectionLiftValue f q.1 q.2.1 q.2.2 := by
  have hstoredPath :
      Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
        q.1.point.path.1 := by
    have hpoint :
        Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
          q.1.point := by
      simpa using
        (mappingPathSpacePointProjectionContinuous ((homotopyFiberProjection f).right.hom)).comp
          continuous_fst
    exact continuous_subtype_val.comp ((homotopyFiberPathContinuous f).comp hpoint)
  have houterPath :
      Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
        q.1.path := by
    -- This is the stored path coordinate of the surrounding mapping-path-space point.
    exact
      (mappingPathSpacePathProjectionContinuous ((homotopyFiberProjection f).right.hom)).comp
        continuous_fst
  have hdenom_ne :
      ∀ q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I,
        1 - (q.2.1 : ℝ) / 2 ≠ 0 := by
    intro q hq
    have ht_le_one : (q.2.1 : ℝ) ≤ 1 := q.2.1.2.2
    nlinarith
  have hfirstParam :
      Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
        Set.projIcc 0 1 zero_le_one (((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2))) := by
    exact continuous_projIcc.comp <|
      Continuous.div (by fun_prop) (by fun_prop) hdenom_ne
  have hsecondParam :
      Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I ↦
        Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2) := by
    exact continuous_projIcc.comp <| by fun_prop
  -- The two branches are continuous, and they agree on the cutoff line.
  refine continuous_if_le (by fun_prop) (by fun_prop)
    (continuous_eval.comp (hstoredPath.prodMk hfirstParam)).continuousOn
    ((f.right.hom.continuous.comp
      (continuous_eval.comp (houterPath.prodMk hsecondParam))).continuousOn) ?_
  intro q hq
  have hdenom_pos : 0 < 1 - (q.2.1 : ℝ) / 2 := by
    have ht_le_one : (q.2.1 : ℝ) ≤ 1 := q.2.1.2.2
    nlinarith
  have hfirst :
      Set.projIcc 0 1 zero_le_one (((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2))) = (1 : I) := by
    have hquot : ((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2)) = 1 := by
      rw [hq]
      exact div_self hdenom_pos.ne'
    rw [hquot]
    simp
  have hsecond :
      Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2) = (0 : I) := by
    have hlin : 2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2 = 0 := by
      rw [hq]
      ring
    rw [hlin]
    simp
  calc
    q.1.point.path (Set.projIcc 0 1 zero_le_one (((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2))))
        = q.1.point.path 1 := by rw [hfirst]
    _ = f.right.hom q.1.point.point := by
      simpa [PathSpace.endpoint] using (HomotopyFiber.endpoint_eq q.1.point).symm
    _ = f.right.hom (q.1.path 0) := by
      simpa [homotopyFiberProjection_hom_apply] using
        congrArg (fun x : X.right ↦ f.right.hom x) q.1.path_zero_eq.symm
    _ = f.right.hom
          (q.1.path (Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2))) := by
      rw [hsecond]

/-- The same compressed-append formula is continuous on the ordinary pullback topology used by
the based mapping-path space. -/
theorem homotopyFiberProjectionLiftValue_continuous_based {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
      homotopyFiberProjectionLiftValue f q.1 q.2.1 q.2.2 := by
  have hstoredPath :
      Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
        q.1.point.path.1 := by
    have hpoint :
        Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
          q.1.point := by
      exact (basedMappingPathSpacePointProjection (homotopyFiberProjection f)).continuous.comp
        continuous_fst
    exact continuous_subtype_val.comp ((homotopyFiberPathContinuous f).comp hpoint)
  have houterPath :
      Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
        q.1.path := by
    exact (basedMappingPathSpacePathProjection (homotopyFiberProjection f)).continuous.comp
      continuous_fst
  have hdenom_ne :
      ∀ q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I,
        1 - (q.2.1 : ℝ) / 2 ≠ 0 := by
    intro q hq
    have ht_le_one : (q.2.1 : ℝ) ≤ 1 := q.2.1.2.2
    nlinarith
  have hfirstParam :
      Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
        Set.projIcc 0 1 zero_le_one ((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2)) := by
    exact continuous_projIcc.comp <|
      Continuous.div (by fun_prop) (by fun_prop) hdenom_ne
  have hsecondParam :
      Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I × I ↦
        Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2) := by
    exact continuous_projIcc.comp <| by fun_prop
  refine continuous_if_le (by fun_prop) (by fun_prop)
    (continuous_eval.comp (hstoredPath.prodMk hfirstParam)).continuousOn
    ((f.right.hom.continuous.comp
      (continuous_eval.comp (houterPath.prodMk hsecondParam))).continuousOn) ?_
  intro q hq
  have hdenom_pos : 0 < 1 - (q.2.1 : ℝ) / 2 := by
    have ht_le_one : (q.2.1 : ℝ) ≤ 1 := q.2.1.2.2
    nlinarith
  have hfirst :
      Set.projIcc 0 1 zero_le_one ((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2)) = (1 : I) := by
    have hquot : ((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2)) = 1 := by
      rw [hq]
      exact div_self hdenom_pos.ne'
    rw [hquot]
    simp
  have hsecond :
      Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2) = (0 : I) := by
    have hlin : 2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2 = 0 := by
      rw [hq]
      ring
    rw [hlin]
    simp
  calc
    q.1.point.path
          (Set.projIcc 0 1 zero_le_one ((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2))) =
        q.1.point.path 1 := by rw [hfirst]
    _ = f.right.hom q.1.point.point := by
      simpa [PathSpace.endpoint] using (HomotopyFiber.endpoint_eq q.1.point).symm
    _ = f.right.hom (q.1.path 0) := by
      simpa [homotopyFiberProjection_hom_apply] using
        congrArg (fun x : X.right ↦ f.right.hom x) q.1.source_eq.symm
    _ = f.right.hom
          (q.1.path (Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2))) := by
      rw [hsecond]

/-- Helper for Pullback 8.6.2: each lifted `Y`-path starts at the basepoint of `Y`. -/
theorem homotopyFiberProjectionLiftValue_zero {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathSpace ((homotopyFiberProjection f).right.hom)) (t : I) :
    homotopyFiberProjectionLiftValue f z t 0 = underTopBasepoint Y := by
  have hbranch : ((0 : I) : ℝ) ≤ 1 - (t : ℝ) / 2 := by
    have ht_le_one : (t : ℝ) ≤ 1 := t.2.2
    have hdiv : (t : ℝ) / 2 ≤ (1 : ℝ) / 2 := by
      exact div_le_div_of_nonneg_right ht_le_one (by norm_num : (0 : ℝ) ≤ 2)
    have hbound : (1 : ℝ) / 2 ≤ 1 - (t : ℝ) / 2 := by
      linarith
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbound
  -- At `s = 0`, the formula stays on the stored path from the homotopy-fiber point.
  rw [homotopyFiberProjectionLiftValue, if_pos hbranch]
  simp [PathSpace.source_eq]

/-- Helper for Pullback 8.6.2: at homotopy time `0`, the explicit lift recovers the stored
`Y`-path in the homotopy fiber. -/
theorem homotopyFiberProjectionLiftValue_timeZero {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathSpace ((homotopyFiberProjection f).right.hom)) (s : I) :
    homotopyFiberProjectionLiftValue f z 0 s = z.point.path s := by
  have hbranch : (s : ℝ) ≤ 1 - ((0 : I) : ℝ) / 2 := by
    simpa using s.2.2
  -- When `t = 0`, the reparametrization of the stored path is the identity.
  rw [homotopyFiberProjectionLiftValue, if_pos hbranch]
  have hparam :
      Set.projIcc 0 1 zero_le_one ((s : ℝ) / (1 - (((0 : I) : ℝ) / 2))) = s := by
    have hsimp : ((s : ℝ) / (1 - (((0 : I) : ℝ) / 2))) = (s : ℝ) := by
      norm_num
    rw [hsimp, Set.projIcc_val]
  exact congrArg z.point.path hparam

/-- Helper for Pullback 8.6.2: the endpoint of the lifted `Y`-path is the image under `f` of the
new `X`-path value. -/
theorem homotopyFiberProjectionLiftValue_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathSpace ((homotopyFiberProjection f).right.hom)) (t : I) :
    homotopyFiberProjectionLiftValue f z t 1 = f.right.hom (z.path t) := by
  by_cases ht : t = 0
  · -- At `t = 0`, the stored endpoint equation of the homotopy-fiber point closes the goal.
    calc
      homotopyFiberProjectionLiftValue f z t 1 =
          homotopyFiberProjectionLiftValue f z 0 1 := by simp [ht]
      _ = z.point.path 1 := homotopyFiberProjectionLiftValue_timeZero f z (1 : I)
      _ = f.right.hom z.point.point := by
        simpa [PathSpace.endpoint] using (HomotopyFiber.endpoint_eq z.point).symm
      _ = f.right.hom (z.path 0) := by
        simpa [homotopyFiberProjection_hom_apply] using congrArg (fun x : X.right ↦ f.right.hom x)
          z.path_zero_eq.symm
      _ = f.right.hom (z.path t) := by simp [ht]
  · -- For positive `t`, the endpoint is on the appended `f ∘ z.path` branch.
    have ht_pos : 0 < (t : ℝ) := by
      have ht_nonneg : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht_ne : (t : ℝ) ≠ 0 := by
        simpa using ht
      exact lt_of_le_of_ne ht_nonneg ht_ne.symm
    have hbranch : ¬ (((1 : I) : ℝ) ≤ 1 - (t : ℝ) / 2) := by
      intro h
      have hhalf_pos : 0 < (t : ℝ) / 2 := by
        nlinarith
      have hneg : 0 ≤ -((t : ℝ) / 2) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (sub_nonneg.mpr h)
      have hhalf_nonpos : (t : ℝ) / 2 ≤ 0 := by
        simpa using hneg
      exact not_lt_of_ge hhalf_nonpos hhalf_pos
    have hsum : 2 * (((1 : I) : ℝ)) + (t : ℝ) - 2 = (t : ℝ) := by
      norm_num
    have hmem : 2 * (((1 : I) : ℝ)) + (t : ℝ) - 2 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hsum]
      exact t.2
    have hparam :
        Set.projIcc 0 1 zero_le_one (2 * (((1 : I) : ℝ)) + (t : ℝ) - 2) = t := by
      rw [Set.projIcc_of_mem zero_le_one hmem]
      exact Subtype.ext hsum
    rw [homotopyFiberProjectionLiftValue, if_neg hbranch]
    exact congrArg f.right.hom (congrArg z.path hparam)

/-- Helper for Pullback 8.6.2: for a fixed mapping-path-space point, the explicit lift value is
continuous in the outer and inner interval variables. -/
theorem homotopyFiberProjectionLiftValue_continuous_fixed {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathSpace ((homotopyFiberProjection f).right.hom)) :
    Continuous fun p : I × I ↦ homotopyFiberProjectionLiftValue f z p.1 p.2 := by
  have hconst : Continuous fun p : I × I ↦
      ((z, p.1, p.2) : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I × I) := by
    fun_prop
  simpa using (homotopyFiberProjectionLiftValue_continuous f).comp hconst

/-- Helper for Pullback 8.6.2: the explicit lift varies continuously as a `Y`-path with both the
mapping-path input and the homotopy time. -/
theorem homotopyFiberProjectionLiftPathCoordinateContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I ↦
      (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
        (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
          (continuous_const.prodMk continuous_id)⟩ : C(I, Y.right)) := by
  -- Curry the jointly continuous three-variable formula after rebracketing products.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have huncurried :
      Continuous fun r : (MappingPathSpace ((homotopyFiberProjection f).right.hom) × I) × I ↦
        homotopyFiberProjectionLiftValue f r.1.1 r.1.2 r.2 := by
    simpa using (homotopyFiberProjectionLiftValue_continuous f).comp
      (Homeomorph.prodAssoc (MappingPathSpace ((homotopyFiberProjection f).right.hom)) I I).continuous_toFun
  simpa [Function.uncurry] using huncurried

/-- The lifted path coordinate is continuous for the ordinary topology on the based mapping-path
space. -/
theorem homotopyFiberProjectionLiftPathCoordinateContinuous_based {X Y : BasedSpace}
    (f : X ⟶ Y) :
    Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I ↦
      (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
        (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
          (continuous_const.prodMk continuous_id)⟩ : C(I, Y.right)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have huncurried :
      Continuous fun r : (BasedMappingPathSpace (homotopyFiberProjection f) × I) × I ↦
        homotopyFiberProjectionLiftValue f r.1.1 r.1.2 r.2 := by
    simpa using (homotopyFiberProjectionLiftValue_continuous_based f).comp
      (Homeomorph.prodAssoc (BasedMappingPathSpace (homotopyFiberProjection f)) I I).continuous_toFun
  simpa [Function.uncurry] using huncurried

/-- Helper for Pullback 8.6.2: the explicit formula yields a continuous path lifting function for
the underlying projection `F_f → X`. -/
theorem homotopyFiberProjectionContinuousPathLift {X Y : BasedSpace} (f : X ⟶ Y) :
    Nonempty (ContinuousPathLiftingFunction ((homotopyFiberProjection f).right.hom)) := by
  let liftPoint :
      MappingPathSpace ((homotopyFiberProjection f).right.hom) × I → HomotopyFiber f :=
    fun q ↦
      HomotopyFiber.mk (q.1.path q.2)
        (PathSpace.mk
          (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
            (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
              (continuous_const.prodMk continuous_id)⟩)
          (homotopyFiberProjectionLiftValue_zero f q.1 q.2))
        (homotopyFiberProjectionLiftValue_endpoint f q.1 q.2).symm
  have hliftPoint : Continuous liftPoint := by
    -- The point coordinate is the chosen `X`-path, and the path coordinate is the explicit
    -- lifted `Y`-path.
    have houterPath :
        Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I ↦
          q.1.path q.2 := by
      exact continuous_eval.comp
        (((mappingPathSpacePathProjectionContinuous ((homotopyFiberProjection f).right.hom)).comp
          continuous_fst).prodMk continuous_snd)
    have hpath :
        Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I ↦
          (PathSpace.mk
            (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
              (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
                (continuous_const.prodMk continuous_id)⟩)
            (homotopyFiberProjectionLiftValue_zero f q.1 q.2) :
            P[underTopBasepoint Y]) := by
      have hcoord :
          Continuous fun q : MappingPathSpace ((homotopyFiberProjection f).right.hom) × I ↦
            (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
              (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
                (continuous_const.prodMk continuous_id)⟩ : C(I, Y.right)) := by
        simpa using homotopyFiberProjectionLiftPathCoordinateContinuous f
      exact hcoord.subtype_mk (fun q ↦ homotopyFiberProjectionLiftValue_zero f q.1 q.2)
    exact (houterPath.prodMk hpath).subtype_mk
      (fun q ↦ (homotopyFiberProjectionLiftValue_endpoint f q.1 q.2).symm)
  let liftPath :
      MappingPathSpace ((homotopyFiberProjection f).right.hom) → C(I, HomotopyFiber f) :=
    fun z ↦
      ⟨fun t ↦ liftPoint (z, t),
        hliftPoint.comp (continuous_const.prodMk continuous_id)⟩
  have hliftPath : Continuous liftPath := by
    -- Curry the jointly continuous lift-point map into a path-valued continuous map.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simpa [liftPath, liftPoint, Function.uncurry] using hliftPoint
  refine ⟨{
    toContinuousMap := ⟨liftPath, hliftPath⟩
    source_eq := ?_
    proj_comp_eq := ?_
  }⟩
  · intro z
    -- At time `0`, the explicit lift reproduces the original homotopy-fiber point.
    apply Subtype.ext
    exact Prod.ext
      (by simpa [liftPoint, homotopyFiberProjection_hom_apply] using z.path_zero_eq)
      (by
        apply Subtype.ext
        ext s
        simpa [liftPoint] using homotopyFiberProjectionLiftValue_timeZero f z s)
  · intro z
    -- Projecting back to `X` forgets the lifted `Y`-path and returns the chosen `X`-path.
    ext t
    rfl

/-- Helper for Pullback 8.6.2: the same explicit formula satisfies the additional basepoint
condition needed for a based path lifting function. -/
theorem homotopyFiberProjectionBasedPathLift {X Y : BasedSpace} (f : X ⟶ Y) :
    Nonempty (BasedPathLiftingFunction (homotopyFiberProjection f)) := by
  let liftPoint : BasedMappingPathSpace (homotopyFiberProjection f) × I → HomotopyFiber f :=
    fun q ↦
      HomotopyFiber.mk (q.1.path q.2)
        (PathSpace.mk
          (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
            (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
              (continuous_const.prodMk continuous_id)⟩)
          (homotopyFiberProjectionLiftValue_zero f q.1 q.2))
        (homotopyFiberProjectionLiftValue_endpoint f q.1 q.2).symm
  have hliftPoint : Continuous liftPoint := by
    -- The same continuity proof works because `BasedMappingPathSpace` is definitionally the same
    -- mapping-path-space carrier for the underlying projection map.
    have hstoredXPath :
        Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I ↦ q.1.path := by
      exact (basedMappingPathSpacePathProjection (homotopyFiberProjection f)).continuous.comp
        continuous_fst
    have houterPath :
        Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I ↦ q.1.path q.2 := by
      exact continuous_eval.comp (hstoredXPath.prodMk continuous_snd)
    have hpath :
        Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I ↦
          (PathSpace.mk
            (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
              (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
                (continuous_const.prodMk continuous_id)⟩)
            (homotopyFiberProjectionLiftValue_zero f q.1 q.2) :
            P[underTopBasepoint Y]) := by
      have hcoord :
          Continuous fun q : BasedMappingPathSpace (homotopyFiberProjection f) × I ↦
            (⟨fun s ↦ homotopyFiberProjectionLiftValue f q.1 q.2 s,
              (homotopyFiberProjectionLiftValue_continuous_fixed f q.1).comp
                (continuous_const.prodMk continuous_id)⟩ : C(I, Y.right)) := by
        simpa using homotopyFiberProjectionLiftPathCoordinateContinuous_based f
      exact hcoord.subtype_mk (fun q ↦ homotopyFiberProjectionLiftValue_zero f q.1 q.2)
    exact (houterPath.prodMk hpath).subtype_mk
      (fun q ↦ (homotopyFiberProjectionLiftValue_endpoint f q.1 q.2).symm)
  let liftPath :
      BasedMappingPathSpace (homotopyFiberProjection f) → C(I, HomotopyFiber f) :=
    fun z ↦
      ⟨fun t ↦ liftPoint (z, t),
        hliftPoint.comp (continuous_const.prodMk continuous_id)⟩
  have hliftPath : Continuous liftPath := by
    -- Curry the jointly continuous map into a path-valued continuous map on the based domain.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simpa [liftPath, liftPoint, Function.uncurry] using hliftPoint
  refine ⟨{
    toContinuousMap := ⟨liftPath, hliftPath⟩
    source_eq := ?_
    proj_comp_eq := ?_
    map_basepoint := ?_
  }⟩
  · intro z
    -- The lifted path starts at the prescribed homotopy-fiber point.
    apply Subtype.ext
    exact Prod.ext
      (by simpa [liftPoint, homotopyFiberProjection_hom_apply] using z.source_eq)
      (by
        apply Subtype.ext
        ext s
        simpa [liftPoint] using homotopyFiberProjectionLiftValue_timeZero f z s)
  · intro z
    -- Forgetting the path coordinate recovers the given path in `X`.
    ext t
    rfl
  · -- At the canonical basepoint input, the whole lifted path is constant at the homotopy-fiber
    -- basepoint.
    ext t
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · change (ContinuousMap.const I (underTopBasepoint X)) t = underTopBasepoint X
      rfl
    · apply Subtype.ext
      ext s
      change
        homotopyFiberProjectionLiftValue f
            (basedMappingPathSpaceBasepoint (homotopyFiberProjection f)) t s =
          underTopBasepoint Y
      by_cases hbranch : (s : ℝ) ≤ 1 - (t : ℝ) / 2
      · rw [homotopyFiberProjectionLiftValue, if_pos hbranch]
        change (PathSpace.basepoint (underTopBasepoint Y))
            (Set.projIcc 0 1 zero_le_one (↑s / (1 - ↑t / 2))) = underTopBasepoint Y
        rfl
      · rw [homotopyFiberProjectionLiftValue, if_neg hbranch]
        change f.right.hom (underTopBasepoint X) = underTopBasepoint Y
        exact map_underTopBasepoint f

/-- Pullback 8.6.2 (2). The projection `F_f ⟶ X` of the homotopy-fiber pullback square has the
based covering homotopy property, i.e. the source's based lifting property without an added
surjectivity hypothesis. -/
instance homotopyFiberProjection_hasBasedCoveringHomotopyProperty {X Y : BasedSpace}
    (f : X ⟶ Y) :
    HasBasedCoveringHomotopyProperty (homotopyFiberProjection f) := by
  exact (HasBasedCoveringHomotopyProperty.iff_nonempty_basedPathLiftingFunction
    (homotopyFiberProjection f)).2 (homotopyFiberProjectionBasedPathLift f)

/-- The underlying map of the homotopy-fiber projection has the covering homotopy property. -/
instance homotopyFiberProjection_hasCoveringHomotopyProperty {X Y : BasedSpace}
    (f : X ⟶ Y) : HasCoveringHomotopyProperty (homotopyFiberProjection f).right.hom := by
  obtain ⟨s⟩ := homotopyFiberProjectionBasedPathLift f
  -- Build the path-space lift required by Reformulation 7.1.4 from the explicit lifting
  -- function on the universal mapping-path-space square.
  refine
    (hasCoveringHomotopyProperty_iff_lift_pathSpaceEvalAtZero
      ((homotopyFiberProjection f).right.hom)).2 ?_
  intro A _ _ g₀ d hd
  let sigma : C(A, BasedMappingPathSpace (homotopyFiberProjection f)) :=
    { toFun := fun a ↦ ⟨(g₀ a, d a), by
        have ha := ContinuousMap.congr_fun hd a
        simpa [pathSpaceEvalAtZero, pathSpaceEvalAt] using ha⟩
      continuous_toFun := by
        have hmem :
            ∀ a : A, d a 0 = ((homotopyFiberProjection f).right.hom) (g₀ a) := by
          intro a
          have ha := ContinuousMap.congr_fun hd a
          simpa [pathSpaceEvalAtZero, pathSpaceEvalAt] using ha
        exact (g₀.continuous.prodMk d.continuous).subtype_mk hmem }
  refine ⟨s.toContinuousMap.comp sigma, ?_, ?_⟩
  · ext a
    simpa [pathSpaceEvalAtZero, pathSpaceEvalAt, sigma] using s.source_eq (sigma a)
  · ext a t
    have ht := congrArg (fun γ : I → X.right ↦ γ t) (s.proj_comp_eq (sigma a))
    simpa [sigma, pathSpacePostcompose] using ht
