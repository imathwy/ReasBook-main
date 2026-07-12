import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

/-- Helper for Problem 2-4: splitting off the `i`-th coordinate identifies `ℝ^(k+1)` with
`ℝ^k × ℝ`. -/
def split_at_coordinate {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ EuclideanSpace ℝ (Fin k) × ℝ where
  toFun x :=
    ((EuclideanSpace.equiv (Fin k) ℝ).symm fun j ↦ x (i.succAbove j), x i)
  invFun y :=
    (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm
      (i.insertNth y.2 ((EuclideanSpace.equiv (Fin k) ℝ) y.1))
  left_inv x := by
    -- Check the distinguished coordinate and the complementary coordinates separately.
    apply (EuclideanSpace.equiv (Fin (k + 1)) ℝ).injective
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      simp
  right_inv y := by
    -- The inverse reinserts the omitted coordinate and then drops it again.
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
      ext j
      simp
    · simp

/-- Helper for Problem 2-4: after splitting off coordinate `i`, the second component is exactly
that coordinate. -/
lemma split_at_coordinate_snd_apply {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    (split_at_coordinate i x).2 = x i := by
  -- This is the distinguished scalar component built into the definition.
  rfl

/-- Helper for Problem 2-4: after splitting off coordinate `i`, the first component records the
remaining coordinates indexed by `succAbove i`. -/
lemma split_at_coordinate_fst_apply {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin k) :
    ((split_at_coordinate i x).1 : Fin k → ℝ) j = x (i.succAbove j) := by
  -- The retained coordinates are the `succAbove` coordinates by definition.
  rfl

/-- Helper for Problem 2-4: the inverse of the coordinate split restores the distinguished
coordinate in slot `i`. -/
lemma split_at_coordinate_symm_apply_self {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) :
    (split_at_coordinate i).symm y i = y.2 := by
  -- Re-inserting at the deleted slot recovers the distinguished coordinate.
  simp [split_at_coordinate]

/-- Helper for Problem 2-4: the inverse of the coordinate split restores the complementary
coordinates in the `succAbove i` slots. -/
lemma split_at_coordinate_symm_apply_succAbove {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) (j : Fin k) :
    (split_at_coordinate i).symm y (i.succAbove j) = y.1 j := by
  -- Away from the distinguished slot, the inverse just reads the saved tail coordinates.
  simp [split_at_coordinate]

/-- Helper for Problem 2-4: the coordinate split is continuous, so open neighborhoods can be
transported from the ambient Euclidean space to split coordinates. -/
lemma split_at_coordinate_continuous {k : ℕ} (i : Fin (k + 1)) :
    Continuous (split_at_coordinate i) := by
  let e := (EuclideanSpace.equiv (Fin (k + 1)) ℝ).toHomeomorph
  have hfun :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          (EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) :=
    e.continuous_toFun
  have hcoords :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          fun j : Fin k ↦ ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) (i.succAbove j)) := by
    -- First forget the `i`-th coordinate at the function-space level.
    exact continuous_pi fun j ↦ (continuous_apply (i.succAbove j)).comp hfun
  have hfst :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          (EuclideanSpace.equiv (Fin k) ℝ).symm
            (fun j : Fin k ↦ ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) (i.succAbove j))) := by
    -- Then transport the remaining coordinates back to `EuclideanSpace ℝ (Fin k)`.
    exact ((EuclideanSpace.equiv (Fin k) ℝ).symm.toHomeomorph.continuous_toFun).comp hcoords
  have hsnd :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) i) := by
    -- The distinguished coordinate is just one scalar projection.
    exact (continuous_apply i).comp hfun
  -- Reassemble the dropped coordinates and the distinguished coordinate into the product model.
  simpa [split_at_coordinate] using Continuous.prodMk hfst hsnd

/-- Helper for Problem 2-4: the inverse coordinate split is continuous, so neighborhoods and
charts can be pulled back from split coordinates to the ambient Euclidean space. -/
lemma split_at_coordinate_symm_continuous {k : ℕ} (i : Fin (k + 1)) :
    Continuous (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm y) := by
  have hremove :
      Continuous
        (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦
          ((EuclideanSpace.equiv (Fin k) ℝ) y.1)) := by
    -- View the split-space first component as an honest `Fin k → ℝ` tuple.
    exact ((EuclideanSpace.equiv (Fin k) ℝ).toHomeomorph.continuous_toFun).comp continuous_fst
  have hinsert :
      Continuous
        (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦
          Fin.insertNth (α := fun _ : Fin (k + 1) ↦ ℝ) i y.2
            (((EuclideanSpace.equiv (Fin k) ℝ) y.1))) := by
    -- Reinsert the distinguished coordinate and keep the complementary coordinates unchanged.
    refine continuous_pi fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using continuous_snd
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      simpa using (continuous_apply j').comp hremove
  -- Finally transport the reinserted tuple back to Euclidean space.
  simpa [split_at_coordinate] using
    ((EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.toHomeomorph.continuous_toFun).comp hinsert

/-- Helper for Problem 2-4: the coordinate split is a continuous linear equivalence, so the fixed
coordinate chart changes can be handled by linear algebra rather than repeated tuple unfolding. -/
noncomputable def split_at_coordinate_continuousLinearEquiv {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
  let e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
    { toFun := split_at_coordinate i
      invFun := (split_at_coordinate i).symm
      left_inv := (split_at_coordinate i).left_inv
      right_inv := (split_at_coordinate i).right_inv
      map_add' := by
        intro x y
        -- The split map is linear coordinatewise on the retained coordinates and the
        -- distinguished scalar coordinate.
        apply Prod.ext
        · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
          ext j
          simp [split_at_coordinate_fst_apply]
        · simp [split_at_coordinate_snd_apply]
      map_smul' := by
        intro t x
        -- Scalar multiplication is checked separately on the retained coordinates and the
        -- distinguished scalar coordinate.
        apply Prod.ext
        · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
          ext j
          simp [split_at_coordinate_fst_apply]
        · simp [split_at_coordinate_snd_apply] }
  e.toContinuousLinearEquivOfContinuous (split_at_coordinate_continuous i)

/-- Helper for Problem 2-4: the inverse coordinate split is smooth, so composing with it
preserves the regularity class needed for Lee's boundary inverse formulas. -/
lemma split_at_coordinate_symm_contDiff {k : ℕ} (i : Fin (k + 1)) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm y) := by
  -- Route correction: the upstream file providing this API currently fails to build, so we
  -- localize the stable split-coordinate linear equivalence here and use its global smoothness.
  simpa [split_at_coordinate_continuousLinearEquiv,
    LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm] using
    (split_at_coordinate_continuousLinearEquiv i).symm.contDiff

/-- Helper for Problem 2-4: the forward coordinate split is smooth for the same linear-algebra
reason as its inverse. -/
lemma split_at_coordinate_contDiff {k : ℕ} (i : Fin (k + 1)) :
    ContDiff ℝ ∞ (split_at_coordinate i) := by
  -- The forward split is a continuous linear equivalence, so its smoothness is global.
  simpa [split_at_coordinate_continuousLinearEquiv,
    LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous] using
    (split_at_coordinate_continuousLinearEquiv i).contDiff

section

local notation "B0" => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1

/-- Helper for Problem 2-4: the zero-dimensional closed unit ball is a subsingleton. -/
lemma closed_unit_ball_zero_subsingleton : Subsingleton B0 := by
  -- Every point in `ℝ^0` is equal, so the subtype closed ball is also a subsingleton.
  refine ⟨fun x y ↦ ?_⟩
  exact Subtype.ext (Subsingleton.elim _ _)

instance : Subsingleton B0 := closed_unit_ball_zero_subsingleton

/-- Helper for Problem 2-4: the zero-dimensional closed unit ball has the discrete topology. -/
instance closed_unit_ball_zero_discreteTopology : DiscreteTopology B0 :=
  (subsingleton_iff_discrete_and_indiscrete.mp inferInstance).1

attribute [local instance] ChartedSpace.of_discreteTopology in
/-- Helper for Problem 2-4: the zero-dimensional closed unit ball has the canonical `C^0`
manifold-with-boundary structure. -/
lemma closed_unit_ball_zero_isManifold_zero :
    IsManifold (leeBoundaryModelWithCorners 0) (0 : ℕ∞ω) B0 := by
  -- In dimension zero, the discrete atlas makes every chart transition automatically smooth.
  simpa [leeBoundaryModelWithCorners] using
    (IsManifold.of_discreteTopology (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 0))
      (n := (0 : ℕ∞ω)) (M := B0))

/-- Helper for Problem 2-4: the zero-dimensional closed unit ball has the trivial topological
manifold-with-boundary structure. -/
noncomputable instance closed_unit_ball_zero_topologicalManifoldWithBoundary :
    TopologicalManifoldWithBoundary 0 B0 where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toChartedSpace := by
    -- The discrete closed ball is charted by the unique point of `ℝ^0`.
    simpa [LeeBoundaryModelSpace] using
      (ChartedSpace.of_discreteTopology (M := B0) (H := EuclideanSpace ℝ (Fin 0)))
  toIsManifold := closed_unit_ball_zero_isManifold_zero

attribute [local instance] ChartedSpace.of_discreteTopology in
/-- Helper for Problem 2-4: the zero-dimensional closed unit ball carries the canonical smooth
manifold-with-boundary structure. -/
lemma closed_unit_ball_zero_isManifold_infty :
    IsManifold (leeBoundaryModelWithCorners 0) (⊤ : WithTop ℕ∞) B0 := by
  -- The same discrete atlas is smooth in every regularity class.
  simpa [leeBoundaryModelWithCorners] using
    (IsManifold.of_discreteTopology (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 0))
      (n := (⊤ : ℕ∞ω)) (M := B0))

/-- Helper for Problem 2-4: the zero-dimensional closed unit ball has the canonical smooth
manifold-with-boundary instance. -/
noncomputable instance closed_unit_ball_zero_smoothManifoldWithBoundary :
    SmoothManifoldWithBoundary 0 B0 where
  toTopologicalManifoldWithBoundary := inferInstance
  smooth := closed_unit_ball_zero_isManifold_infty

/-- Helper for Problem 2-4: in dimension zero the subtype inclusion is smooth. -/
lemma closed_unit_ball_zero_inclusion_contMDiff :
    ContMDiff (leeBoundaryModelWithCorners 0) (𝓡 0) ∞
      ((↑) : B0 → EuclideanSpace ℝ (Fin 0)) := by
  -- Once the source is discrete, the ambient inclusion is smooth for free.
  simpa [leeBoundaryModelWithCorners] using
    (contMDiff_of_discreteTopology (I := leeBoundaryModelWithCorners 0) (I' := 𝓡 0)
      (n := (∞ : WithTop ℕ∞)) (f := ((↑) : B0 → EuclideanSpace ℝ (Fin 0))))

end

section

local notation "B1" => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1

/-- Helper for Problem 2-4: the coordinate of a point in the one-dimensional closed unit ball lies
in `[-1, 1]`. -/
lemma closed_unit_ball_one_coord_mem_Icc (x : B1) : x.1 0 ∈ Set.Icc (-1 : ℝ) 1 := by
  -- In dimension one, the unique coordinate is controlled by the ambient Euclidean norm.
  have hxnorm : ‖x.1‖ ≤ 1 := by
    simpa [Metric.closedBall, Metric.mem_closedBall, dist_eq_norm] using x.2
  have hxcoord : |x.1 0| ≤ ‖x.1‖ := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]
  exact abs_le.mp (hxcoord.trans hxnorm)

/-- Helper for Problem 2-4: the interval point `t ∈ [-1, 1]` determines a point of the
one-dimensional closed unit ball. -/
lemma icc_one_mem_closed_unit_ball_one (t : Set.Icc (-1 : ℝ) 1) :
    (WithLp.toLp 2 (V := ∀ _ : Fin 1, ℝ) ![(t : ℝ)] : EuclideanSpace ℝ (Fin 1)) ∈ B1 := by
  -- The Euclidean norm of a one-coordinate vector is the absolute value of that coordinate.
  rcases t.property with ⟨htl, htr⟩
  have ht : |(t : ℝ)| ≤ 1 := by
    refine abs_le.mpr ?_
    constructor
    · linarith
    · exact htr
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using ht

/-- Helper for Problem 2-4: the one-dimensional closed unit ball maps to the interval `[-1, 1]`
by reading off its unique coordinate. -/
def closed_unit_ball_one_to_Icc : B1 → Set.Icc (-1 : ℝ) 1 :=
  fun x ↦ ⟨x.1 0, closed_unit_ball_one_coord_mem_Icc x⟩

/-- Helper for Problem 2-4: the interval `[-1, 1]` maps back to the one-dimensional closed unit
ball by forming the corresponding one-coordinate vector. -/
def icc_to_closed_unit_ball_one : Set.Icc (-1 : ℝ) 1 → B1 :=
  fun t ↦
    ⟨WithLp.toLp 2 (V := ∀ _ : Fin 1, ℝ) ![(t : ℝ)], icc_one_mem_closed_unit_ball_one t⟩

/-- Helper for Problem 2-4: the interval model recovers a point of the one-dimensional closed unit
ball after reading and restoring its unique coordinate. -/
lemma icc_to_closed_unit_ball_one_left_inv (x : B1) :
    icc_to_closed_unit_ball_one (closed_unit_ball_one_to_Icc x) = x := by
  -- Both sides have the same unique coordinate, so the vectors are equal.
  apply Subtype.ext
  ext i
  fin_cases i
  simp [closed_unit_ball_one_to_Icc, icc_to_closed_unit_ball_one]

/-- Helper for Problem 2-4: restoring the vector from an interval point and reading the unique
coordinate gives back the original interval point. -/
lemma closed_unit_ball_one_to_Icc_right_inv (t : Set.Icc (-1 : ℝ) 1) :
    closed_unit_ball_one_to_Icc (icc_to_closed_unit_ball_one t) = t := by
  -- On the interval side, everything is determined by the underlying real number.
  apply Subtype.ext
  simp [closed_unit_ball_one_to_Icc, icc_to_closed_unit_ball_one]

/-- Helper for Problem 2-4: the coordinate map from the one-dimensional closed unit ball to
`[-1, 1]` is continuous. -/
lemma continuous_closed_unit_ball_one_to_Icc :
    Continuous closed_unit_ball_one_to_Icc := by
  -- The underlying coordinate projection is continuous, and the interval constraint is pointwise.
  simpa [closed_unit_ball_one_to_Icc] using
    (Continuous.subtype_mk (by fun_prop) closed_unit_ball_one_coord_mem_Icc)

/-- Helper for Problem 2-4: the interval-to-ball reconstruction map is continuous. -/
lemma continuous_icc_to_closed_unit_ball_one :
    Continuous icc_to_closed_unit_ball_one := by
  -- The ambient one-coordinate vector map is continuous, and the closed-ball constraint is
  -- pointwise.
  simpa [icc_to_closed_unit_ball_one] using
    (Continuous.subtype_mk (by fun_prop) icc_one_mem_closed_unit_ball_one)

/-- Helper for Problem 2-4: the one-dimensional closed unit ball is homeomorphic to the interval
`[-1, 1]`. -/
def closed_unit_ball_one_homeomorph_Icc : B1 ≃ₜ Set.Icc (-1 : ℝ) 1 where
  toEquiv :=
    { toFun := closed_unit_ball_one_to_Icc
      invFun := icc_to_closed_unit_ball_one
      left_inv := icc_to_closed_unit_ball_one_left_inv
      right_inv := closed_unit_ball_one_to_Icc_right_inv }
  continuous_toFun := continuous_closed_unit_ball_one_to_Icc
  continuous_invFun := continuous_icc_to_closed_unit_ball_one

/-- Helper for Problem 2-4: the interval `[-1, 1]` satisfies mathlib's strict-order hypothesis
for the interval manifold API. -/
lemma closed_unit_ball_one_interval_fact : Fact ((-1 : ℝ) < 1) :=
  ⟨by norm_num⟩

/-- Helper for Problem 2-4: the one-dimensional closed unit ball is nonempty. -/
lemma closed_unit_ball_one_nonempty : Nonempty B1 := by
  -- The origin lies in the closed unit ball, so the transported atlas has a base point.
  refine ⟨⟨0, ?_⟩⟩
  simp [Metric.mem_closedBall]

/-- Helper for Problem 2-4: transport the interval singleton charted-space structure to the
one-dimensional closed unit ball. -/
@[reducible] noncomputable def closed_unit_ball_one_chartedSpace_Icc :
    ChartedSpace (Set.Icc (-1 : ℝ) 1) B1 :=
  let _ : Fact ((-1 : ℝ) < 1) := closed_unit_ball_one_interval_fact
  let _ : Nonempty B1 := closed_unit_ball_one_nonempty
  -- Route correction: use the explicit homeomorphism `B1 ≃ₜ Icc (-1) 1` to install the
  -- singleton charted space before composing with the standard interval manifold charts.
  closed_unit_ball_one_homeomorph_Icc.isOpenEmbedding.singletonChartedSpace

/-- Helper for Problem 2-4: compose the transported interval chart with the standard half-space
charts on `[-1, 1]`. -/
@[reducible] noncomputable def closed_unit_ball_one_chartedSpace_halfSpace :
    ChartedSpace (EuclideanHalfSpace 1) B1 :=
  let _ : Fact ((-1 : ℝ) < 1) := closed_unit_ball_one_interval_fact
  let _ : Nonempty B1 := closed_unit_ball_one_nonempty
  let _ : ChartedSpace (Set.Icc (-1 : ℝ) 1) B1 := closed_unit_ball_one_chartedSpace_Icc
  -- This is the source-faithful transport step: first identify `B1` with the interval, then use
  -- the existing interval manifold charts valued in `EuclideanHalfSpace 1`.
  ChartedSpace.comp (EuclideanHalfSpace 1) (Set.Icc (-1 : ℝ) 1) B1

attribute [local instance] closed_unit_ball_one_interval_fact
attribute [local instance] closed_unit_ball_one_nonempty
attribute [local instance] closed_unit_ball_one_chartedSpace_Icc
attribute [local instance] closed_unit_ball_one_chartedSpace_halfSpace

/-- Helper for Problem 2-4: an interval self-chart in the restriction groupoid is locally equal to
the identity on its source. -/
lemma closed_interval_eventuallyEq_id_of_mem_idRestrGroupoid
    {e : OpenPartialHomeomorph (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1)}
    (he : e ∈ (@idRestrGroupoid (Set.Icc (-1 : ℝ) 1) _))
    {x : Set.Icc (-1 : ℝ) 1} (hx : x ∈ e.source) :
    ((e : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) =ᶠ[nhdsWithin x e.source] id) ∧ e x = x := by
  rcases he with ⟨s, hs, hes⟩
  have hEqOn :
      Set.EqOn (e : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1)
        (OpenPartialHomeomorph.ofSet s hs : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) e.source :=
    OpenPartialHomeomorph.EqOnSource.eqOn hes
  have hid :
      Set.EqOn (e : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) id e.source := by
    -- Membership in `idRestrGroupoid` means `e` agrees with a restriction of the identity.
    intro y hy
    calc
      e y = OpenPartialHomeomorph.ofSet s hs y := hEqOn hy
      _ = y := rfl
  constructor
  · -- Once `e` agrees with `id` on its source, it agrees with `id` in the source-local filter.
    exact hid.eventuallyEq_nhdsWithin
  · -- Evaluating the source-local identity relation at `x` gives the pointwise equality.
    exact hid hx

/-- Helper for Problem 2-4: an element of the restriction groupoid is automatically a local
structomorphism for any restriction-closed groupoid on the same model space. -/
lemma liftPropOn_isLocalStructomorph_of_mem_idRestrGroupoid
    {H : Type*} [TopologicalSpace H] {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph H H} (he : e ∈ (@idRestrGroupoid H _)) :
    ChartedSpace.LiftPropOn
      (StructureGroupoid.IsLocalStructomorphWithinAt G) (e : H → H) e.source := by
  -- Route correction: instead of rebuilding local structomorphisms on the transported source,
  -- we first promote `e` from `idRestrGroupoid` into the ambient restriction-closed groupoid.
  have hle : (@idRestrGroupoid H _) ≤ G := (closedUnderRestriction_iff_id_le G).mp inferInstance
  have heG : e ∈ G := StructureGroupoid.le_iff.mp hle _ he
  -- Once `e` is known to lie in `G`, the local-invariant API packages the desired lift.
  refine StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_groupoid
    (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp G)
    (hQ := ?_) heG
  intro y hy
  refine ⟨OpenPartialHomeomorph.refl H, G.id_mem, ?_, ?_⟩
  · intro z hz
    rfl
  · simp

/-- Helper for Problem 2-4: on the standard interval manifold, every `idRestrGroupoid` self-map is
locally a smooth half-space structomorphism. -/
lemma closed_interval_liftPropOn_isLocalStructomorph_of_mem_idRestrGroupoid
    {e : OpenPartialHomeomorph (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1)}
    (he : e ∈ (@idRestrGroupoid (Set.Icc (-1 : ℝ) 1) _)) :
    ChartedSpace.LiftPropOn
      (StructureGroupoid.IsLocalStructomorphWithinAt
        (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ 1)))
      (e : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) e.source := by
  let G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ 1)
  intro x hx
  have hId :
      ChartedSpace.LiftProp
        (StructureGroupoid.IsLocalStructomorphWithinAt G)
        (id : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) := by
    -- Route correction: work on the interval manifold itself and start from the identity germ.
    exact StructureGroupoid.LocalInvariantProp.liftProp_id
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp G)
      (hQ := by
        intro y hy
        refine ⟨OpenPartialHomeomorph.refl _, G.id_mem, ?_, by simp [hy]⟩
        intro z hz
        rfl)
  have hIdWithin :
      ChartedSpace.LiftPropWithinAt
        (StructureGroupoid.IsLocalStructomorphWithinAt G)
        (id : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) e.source x := by
    -- Since `e.source` is open and contains `x`, the identity germ restricts to `e.source`.
    exact StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt_of_mem_nhds
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp G)
      (h := hId x)
      (hs := e.open_source.mem_nhds hx)
  have hEq :
      (e : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1) =ᶠ[nhdsWithin x e.source] id :=
    (closed_interval_eventuallyEq_id_of_mem_idRestrGroupoid he hx).1
  -- The new interval-specific identity lemma lets us replace `e` by `id` in the lifted property.
  exact StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
    (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp G)
    hIdWithin hEq hx

/-- Helper for Problem 2-4: the explicit homeomorphism with `[-1, 1]` transports the standard
interval smooth manifold-with-boundary structure to the one-dimensional closed unit ball. -/
lemma closed_unit_ball_one_isManifold_infty :
    IsManifold (𝓡∂ 1) (⊤ : WithTop ℕ∞) B1 := by
  let G := (@idRestrGroupoid (Set.Icc (-1 : ℝ) 1) _)
  letI : HasGroupoid B1 G :=
    closed_unit_ball_one_homeomorph_Icc.isOpenEmbedding.singleton_hasGroupoid G
  letI : HasGroupoid B1 (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ 1)) :=
    StructureGroupoid.HasGroupoid.comp
      (G₁ := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡∂ 1)) (G₂ := G) <| by
        intro e he
        exact closed_interval_liftPropOn_isLocalStructomorph_of_mem_idRestrGroupoid he
  -- The transported singleton interval atlas now composes with the standard interval manifold.
  exact IsManifold.mk' (𝓡∂ 1) (⊤ : WithTop ℕ∞) B1

/-- Helper for Problem 2-4: the one-dimensional closed unit ball should inherit the standard
interval manifold-with-boundary structure via the explicit homeomorphism with `[-1, 1]`. -/
@[reducible] noncomputable def closed_unit_ball_one_smoothManifoldWithBoundary :
    SmoothManifoldWithBoundary 1 B1 where
  toTopologicalManifoldWithBoundary :=
    { toT2Space := inferInstance
      toSecondCountableTopology := inferInstance
      toChartedSpace := by
        -- The positive-dimensional boundary model is definitionally the half-space charted space.
        simpa [LeeBoundaryModelSpace] using closed_unit_ball_one_chartedSpace_halfSpace
      toIsManifold := by
        -- The smooth interval atlas immediately yields the required `C^0` manifold structure.
        simpa [leeBoundaryModelWithCorners] using
          (closed_unit_ball_one_isManifold_infty.of_le (by simp : (0 : ℕ∞ω) ≤ (⊤ : WithTop ℕ∞))) }
  smooth := by
    -- The transported interval structure is already smooth in the half-space model.
    simpa [leeBoundaryModelWithCorners] using closed_unit_ball_one_isManifold_infty

/-- Helper for Problem 2-4: the preferred linear identification `ℝ → ℝ¹`. -/
def closed_unit_ball_one_real_to_r1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 2-4: the unique coordinate of the chosen `ℝ → ℝ¹` map is the original
real number. -/
lemma closed_unit_ball_one_real_to_r1_apply (t : ℝ) :
    closed_unit_ball_one_real_to_r1 t 0 = t := by
  -- The chosen linear equivalence is the inverse of the standard identification `ℝ¹ ≃ ℝ`.
  simp [closed_unit_ball_one_real_to_r1]

/-- Helper for Problem 2-4: the ambient inclusion of the one-dimensional closed unit ball factors
through the interval model and the standard linear identification `ℝ → ℝ¹`. -/
lemma closed_unit_ball_one_inclusion_eq :
    ((↑) : B1 → EuclideanSpace ℝ (Fin 1)) =
      closed_unit_ball_one_real_to_r1 ∘ Subtype.val ∘ closed_unit_ball_one_to_Icc := by
  -- Both maps read the unique coordinate and rebuild the same one-coordinate vector.
  funext x
  ext i
  fin_cases i
  simp [closed_unit_ball_one_to_Icc, closed_unit_ball_one_real_to_r1_apply]

/-- Helper for Problem 2-4: the transport homeomorphism from the closed unit ball to `[-1, 1]` is
smooth for the composed half-space atlas because, in transported charts, it is the identity. -/
lemma closed_unit_ball_one_to_Icc_contMDiff :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ closed_unit_ball_one_to_Icc := by
  intro x
  rw [contMDiffAt_iff]
  constructor
  · -- The underlying coordinate projection is continuous before any chart calculations.
    exact continuous_closed_unit_ball_one_to_Icc.continuousAt
  · letI : ChartedSpace (Set.Icc (-1 : ℝ) 1) B1 := closed_unit_ball_one_chartedSpace_Icc
    letI : ChartedSpace (EuclideanHalfSpace 1) B1 := closed_unit_ball_one_chartedSpace_halfSpace
    -- In the composed charts, the transported map to the interval is literally the identity germ.
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt ℝ ∞ (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
          (Set.range (𝓡∂ 1)) (extChartAt (𝓡∂ 1) x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 1) x] with y hy
      simpa [writtenInExtChartAt, Function.comp,
        Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq] using
        (writtenInExtChartAt_chartAt_comp
          (I := 𝓡∂ 1) (H := EuclideanHalfSpace 1) (H' := Set.Icc (-1 : ℝ) 1) x hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (I := 𝓡∂ 1) x)
        (mem_extChartAt_target (I := 𝓡∂ 1) x)

/-- Helper for Problem 2-4: in dimension one the ambient inclusion is smooth for the transported
interval manifold-with-boundary structure. -/
lemma closed_unit_ball_one_inclusion_contMDiff :
    ContMDiff (𝓡∂ 1) (𝓡 1) ∞ ((↑) : B1 → EuclideanSpace ℝ (Fin 1)) := by
  have hToIcc : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ closed_unit_ball_one_to_Icc :=
    closed_unit_ball_one_to_Icc_contMDiff
  have hIccInclusion : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) :=
    contMDiff_subtype_coe_Icc (x := (-1 : ℝ)) (y := (1 : ℝ))
  have hLinear : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ closed_unit_ball_one_real_to_r1 := by
    -- The fixed identification `ℝ ≃L[ℝ] ℝ¹` is globally smooth.
    simpa [closed_unit_ball_one_real_to_r1] using
      (((((EuclideanSpace.equiv (Fin 1) ℝ).trans
            (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm :
          ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearMap).contMDiff :
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ closed_unit_ball_one_real_to_r1)
  -- Factor the inclusion through the smooth interval coordinate and the fixed linear map.
  rw [closed_unit_ball_one_inclusion_eq]
  exact hLinear.comp (hIccInclusion.comp hToIcc)

/-- Helper for Problem 2-4: on the open unit ball, the radicand `1 - ‖u‖²` of Lee's boundary
branch function is strictly positive. -/
lemma one_sub_norm_sq_pos_of_mem_unit_ball {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1))}
    (hu : u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    0 < 1 - ‖u‖ ^ 2 := by
  -- Rewrite the geometric condition as `‖u‖ < 1` and then square the inequality.
  have hnorm : ‖u‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hnorm_sq : ‖u‖ ^ 2 < 1 := by
    have habs : |‖u‖| < |(1 : ℝ)| := by
      simpa [abs_of_nonneg (norm_nonneg u)] using hnorm
    have hsq : ‖u‖ ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq.2 habs)
    simpa using hsq
  exact sub_pos.mpr hnorm_sq

/-- Helper for Problem 2-4: Lee's unsigned boundary graphing branch
`u ↦ sqrt (1 - ‖u‖²)` is smooth on the open unit ball. -/
lemma closed_unit_ball_boundary_branch_core_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ω
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦ Real.sqrt (1 - ‖u‖ ^ 2))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) := by
  -- The source route uses `sqrt` of the positive radicand `1 - ‖u‖²`.
  refine (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn.sqrt ?_
  intro u hu
  exact (one_sub_norm_sq_pos_of_mem_unit_ball hu).ne'

/-- Helper for Problem 2-4: the signed boundary graphing branches `± sqrt (1 - ‖u‖²)` are smooth
on the open unit ball. -/
def closed_unit_ball_boundary_branch (k : ℕ) (s : Bool) :
    EuclideanSpace ℝ (Fin (k + 1)) → ℝ :=
  fun u ↦ if s then Real.sqrt (1 - ‖u‖ ^ 2) else -Real.sqrt (1 - ‖u‖ ^ 2)

/-- Helper for Problem 2-4: choosing either sign in Lee's boundary graphing function preserves the
same smoothness on the open unit ball. -/
lemma closed_unit_ball_boundary_branch_contDiffOn (k : ℕ) (s : Bool) :
    ContDiffOn ℝ ω (closed_unit_ball_boundary_branch k s)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) := by
  -- The sign choice only toggles between the core branch and its negation.
  cases s with
  | false =>
      simpa [closed_unit_ball_boundary_branch] using
        (closed_unit_ball_boundary_branch_core_contDiffOn k).neg
  | true =>
      simpa [closed_unit_ball_boundary_branch] using
        closed_unit_ball_boundary_branch_core_contDiffOn k

/-- Helper for Problem 2-4: the higher-dimensional boundary charts use a fixed sign coefficient to
distinguish the upper and lower hemispheres. -/
def closed_unit_ball_boundary_sign (s : Bool) : ℝ :=
  if s then 1 else -1

/-- Helper for Problem 2-4: after normalizing the target half-space with
`split_at_coordinate 0`, every boundary chart lands in the same hypograph target set. -/
def closed_unit_ball_boundary_chart_target (k : ℕ) :
    Set (EuclideanHalfSpace (k + 2)) :=
  {z | let ur := split_at_coordinate (0 : Fin (k + 2)) z.1
    ‖ur.1‖ < 1 ∧ ur.2 < Real.sqrt (1 - ‖ur.1‖ ^ 2)}

/-- Helper for Problem 2-4: in the normalized half-space coordinates, the boundary chart inverse is
Lee's explicit graphing formula with the chosen sign. -/
def closed_unit_ball_boundary_chart_inverse (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    EuclideanHalfSpace (k + 2) → EuclideanSpace ℝ (Fin (k + 2)) :=
  fun z ↦
    let ur := split_at_coordinate (0 : Fin (k + 2)) z.1
    (split_at_coordinate i).symm
      (ur.1,
        closed_unit_ball_boundary_branch k s ur.1 -
          closed_unit_ball_boundary_sign s * ur.2)

/-- Helper for Problem 2-4: the boundary chart inverse has a smooth ambient extension obtained by
forgetting the half-space proof and using the same graphing formula in `ℝ^(k+2)`. -/
def closed_unit_ball_boundary_chart_inverse_extend (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 2)) :=
  fun x ↦
    let ur := split_at_coordinate (0 : Fin (k + 2)) x
    (split_at_coordinate i).symm
      (ur.1,
        closed_unit_ball_boundary_branch k s ur.1 -
          closed_unit_ball_boundary_sign s * ur.2)

/-- Helper for Problem 2-4: the half-space inverse is literally the restriction of the ambient
extension to `EuclideanHalfSpace (k + 2)`. -/
lemma closed_unit_ball_boundary_chart_inverse_eq_extend {k : ℕ}
    (i : Fin (k + 2)) (s : Bool) (z : EuclideanHalfSpace (k + 2)) :
    closed_unit_ball_boundary_chart_inverse k i s z =
      closed_unit_ball_boundary_chart_inverse_extend k i s z.1 := by
  -- The half-space formula and the ambient formula differ only by whether we keep the subtype
  -- proof.
  rfl

/-- Helper for Problem 2-4: membership in the normalized boundary target is exactly the expected
split-coordinate inequality package. -/
lemma closed_unit_ball_boundary_chart_target_mem_iff {k : ℕ}
    {z : EuclideanHalfSpace (k + 2)} :
    z ∈ closed_unit_ball_boundary_chart_target k ↔
      let ur := split_at_coordinate (0 : Fin (k + 2)) z.1
      ‖ur.1‖ < 1 ∧ ur.2 < Real.sqrt (1 - ‖ur.1‖ ^ 2) := by
  -- This is just the normalized target definition rewritten as an iff for later `simp only`.
  rfl

/-- Helper for Problem 2-4: every point of the normalized boundary target lies in the open unit
ball for the retained split coordinates, which is exactly the smoothness domain of the graphing
branch. -/
lemma closed_unit_ball_boundary_chart_target_mem_unit_ball {k : ℕ}
    {z : EuclideanHalfSpace (k + 2)} (hz : z ∈ closed_unit_ball_boundary_chart_target k) :
    ‖(split_at_coordinate (0 : Fin (k + 2)) z.1).1‖ < 1 := by
  -- Unpack the target inequalities and keep only the open-ball condition on the retained
  -- coordinates.
  simpa [closed_unit_ball_boundary_chart_target] using
    (closed_unit_ball_boundary_chart_target_mem_iff.mp hz).1

/-- Helper for Problem 2-4: the ambient extension of Lee's boundary inverse is smooth on the open
set where the retained split coordinates lie in the open unit ball. -/
lemma closed_unit_ball_boundary_chart_inverse_extend_contDiffOn (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    ContDiffOn ℝ ω
      (closed_unit_ball_boundary_chart_inverse_extend k i s)
      {x : EuclideanSpace ℝ (Fin (k + 2)) |
        ‖(split_at_coordinate (0 : Fin (k + 2)) x).1‖ < 1} := by
  let u : EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 1)) :=
    fun x ↦ (split_at_coordinate (0 : Fin (k + 2)) x).1
  let r : EuclideanSpace ℝ (Fin (k + 2)) → ℝ :=
    fun x ↦ (split_at_coordinate (0 : Fin (k + 2)) x).2
  have hu : ContDiff ℝ ω u := by
    -- The retained coordinates are obtained by composing linear maps, hence are analytic.
    fun_prop
  have hr : ContDiff ℝ ω r := by
    -- The distinguished coordinate is another linear projection, so it is analytic as well.
    fun_prop
  have hbranch :
      ContDiffOn ℝ ω (fun x ↦ closed_unit_ball_boundary_branch k s (u x))
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- Compose the branch smoothness on the open unit ball with the retained-coordinate map.
    refine (closed_unit_ball_boundary_branch_contDiffOn k s).comp hu.contDiffOn ?_
    intro x hx
    simpa [Metric.mem_ball, dist_eq_norm, u] using hx
  have hcoord :
      ContDiffOn ℝ ω
        (fun x ↦ closed_unit_ball_boundary_branch k s (u x) -
          closed_unit_ball_boundary_sign s * r x)
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- The graphing coordinate is the branch value corrected by an affine scalar term.
    exact hbranch.sub (((contDiff_const).mul hr).contDiffOn)
  have hpair :
      ContDiffOn ℝ ω
        (fun x ↦ (u x,
          closed_unit_ball_boundary_branch k s (u x) -
            closed_unit_ball_boundary_sign s * r x))
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- Reassemble the retained coordinates and the graphing coordinate into the split target.
    exact hu.contDiffOn.prodMk hcoord
  have hsymm : ContDiff ℝ ω (split_at_coordinate i).symm := by
    -- Reinsert the distinguished coordinate using the inverse linear split.
    simpa [split_at_coordinate_continuousLinearEquiv,
      LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm] using
      (split_at_coordinate_continuousLinearEquiv i).symm.contDiff
  simpa [closed_unit_ball_boundary_chart_inverse_extend, u, r] using
    hsymm.comp_contDiffOn hpair

/-- Helper for Problem 2-4: Lee's normalized boundary inverse is smooth as a map from the
half-space model to the ambient Euclidean space on the boundary target. -/
lemma closed_unit_ball_boundary_chart_inverse_contMDiffOn_target (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    ContMDiffOn (𝓡∂ (k + 2)) (𝓡 (k + 2)) ∞
      (closed_unit_ball_boundary_chart_inverse k i s)
      (closed_unit_ball_boundary_chart_target k) := by
  have hsmooth_model :
      ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          closed_unit_ball_boundary_chart_inverse k i s ((𝓡∂ (k + 2)).symm z))
        ((𝓡∂ (k + 2)) '' closed_unit_ball_boundary_chart_target k) := by
    have hsubset :
        ((𝓡∂ (k + 2)) '' closed_unit_ball_boundary_chart_target k) ⊆
          {x : EuclideanSpace ℝ (Fin (k + 2)) |
            ‖(split_at_coordinate (0 : Fin (k + 2)) x).1‖ < 1} := by
      rintro y ⟨z, hz, rfl⟩
      -- Every image point still satisfies the retained-coordinate unit-ball inequality.
      exact closed_unit_ball_boundary_chart_target_mem_unit_ball hz
    have hEq :
        Set.EqOn
          (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
            closed_unit_ball_boundary_chart_inverse k i s ((𝓡∂ (k + 2)).symm z))
          (closed_unit_ball_boundary_chart_inverse_extend k i s)
          ((𝓡∂ (k + 2)) '' closed_unit_ball_boundary_chart_target k) := by
      rintro y ⟨z, hz, rfl⟩
      -- On points coming from the half-space model, the model inverse returns the original point.
      simpa [ModelWithCorners.left_inv (I := 𝓡∂ (k + 2)) z] using
        closed_unit_ball_boundary_chart_inverse_eq_extend (k := k) i s z
    -- The ambient extension is smooth on a larger ambient neighborhood, so it is smooth on the
    -- actual image of the target; then replace it by the half-space formula on that image.
    have hsmooth_extend :
        ContDiffOn ℝ ∞ (closed_unit_ball_boundary_chart_inverse_extend k i s)
          {x : EuclideanSpace ℝ (Fin (k + 2)) |
            ‖(split_at_coordinate (0 : Fin (k + 2)) x).1‖ < 1} :=
      (closed_unit_ball_boundary_chart_inverse_extend_contDiffOn k i s).of_le (by simp)
    exact (hsmooth_extend.mono hsubset).congr hEq
  -- Route correction: reduce to the single global half-space chart instead of trying to prove a
  -- raw `ContDiffOn` statement on the subtype target.
  simpa [Function.comp, extChartAt_self_eq, extChartAt_model_space_eq_id] using
    (contMDiffOn_iff_of_subset_source'
      (I := 𝓡∂ (k + 2)) (I' := 𝓡 (k + 2))
      (f := closed_unit_ball_boundary_chart_inverse k i s)
      (s := closed_unit_ball_boundary_chart_target k)
      (x := (0 : EuclideanHalfSpace (k + 2)))
      (y := (0 : EuclideanSpace ℝ (Fin (k + 2))))
      (hs := by
        intro x hx
        simp)
      (h2s := by
        intro x hx
        simp)).2 hsmooth_model

/-- Helper for Problem 2-4: splitting off one coordinate preserves the Euclidean norm by turning it
into the sum of the squared tail norm and the squared distinguished coordinate. -/
lemma split_at_coordinate_symm_norm_sq {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) :
    ‖(split_at_coordinate i).symm y‖ ^ 2 = ‖y.1‖ ^ 2 + y.2 ^ 2 := by
  -- Expand the ambient norm as a sum of coordinate squares and split off the distinguished slot.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i, EuclideanSpace.real_norm_sq_eq]
  -- The `succAbove` coordinates are exactly the retained `y.1` coordinates, and slot `i` is `y.2`.
  simp [split_at_coordinate_symm_apply_self, split_at_coordinate_symm_apply_succAbove, add_comm]

/-- Helper for Problem 2-4: Lee's explicit normalized boundary inverse already lands in the closed
unit ball whenever the half-space point satisfies the hypograph target inequalities. -/
lemma closed_unit_ball_boundary_chart_inverse_mem_closedBall {k : ℕ}
    (i : Fin (k + 2)) (s : Bool) {z : EuclideanHalfSpace (k + 2)}
    (hz : z ∈ closed_unit_ball_boundary_chart_target k) :
    closed_unit_ball_boundary_chart_inverse k i s z ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 := by
  let ur := split_at_coordinate (0 : Fin (k + 2)) z.1
  have hur : ‖ur.1‖ < 1 ∧ ur.2 < Real.sqrt (1 - ‖ur.1‖ ^ 2) := by
    -- Start from the normalized target-membership package for the chosen half-space point.
    simpa [closed_unit_ball_boundary_chart_target, ur] using hz
  have hur_nonneg : 0 ≤ ur.2 := by
    -- The normalized scalar coordinate is the original half-space boundary coordinate.
    simpa [ur, split_at_coordinate_snd_apply] using z.2
  have hur_mem_ball : ur.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
    -- The target hypothesis says the retained coordinates lie in the open unit ball.
    simpa [Metric.mem_ball, dist_eq_norm] using hur.1
  have hrad_nonneg : 0 ≤ 1 - ‖ur.1‖ ^ 2 := by
    -- The radicand is positive on the open unit ball, exactly as in Lee's graphing function.
    exact (one_sub_norm_sq_pos_of_mem_unit_ball hur_mem_ball).le
  have hcore_nonneg : 0 ≤ Real.sqrt (1 - ‖ur.1‖ ^ 2) := Real.sqrt_nonneg _
  let t : ℝ :=
    closed_unit_ball_boundary_branch k s ur.1 - closed_unit_ball_boundary_sign s * ur.2
  have ht_sq_le :
      t ^ 2 ≤ (Real.sqrt (1 - ‖ur.1‖ ^ 2)) ^ 2 := by
    -- The correction term differs from `±sqrt(1 - ‖u‖²)` by subtracting a nonnegative `r`
    -- bounded above by the same square root.
    cases s with
    | false =>
        have hLower : -Real.sqrt (1 - ‖ur.1‖ ^ 2) ≤ t := by
          -- In the lower-hemisphere branch, `t = ur.2 - sqrt(...)`, so nonnegativity of `ur.2`
          -- gives the lower bound.
          simp [t, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          linarith [hur_nonneg]
        have hUpper : t ≤ Real.sqrt (1 - ‖ur.1‖ ^ 2) := by
          -- The target inequality `ur.2 ≤ sqrt(...)` bounds the translated lower branch above.
          simp [t, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          linarith [hur.2.le, hcore_nonneg]
        exact sq_le_sq' hLower hUpper
    | true =>
        have hLower : -Real.sqrt (1 - ‖ur.1‖ ^ 2) ≤ t := by
          -- In the upper-hemisphere branch, `t = sqrt(...) - ur.2`, so `ur.2 ≤ sqrt(...)`
          -- keeps `t` above `-sqrt(...)`.
          simp [t, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          linarith [hur.2.le, hcore_nonneg]
        have hUpper : t ≤ Real.sqrt (1 - ‖ur.1‖ ^ 2) := by
          -- Nonnegativity of `ur.2` bounds the translated upper branch above by the core branch.
          simp [t, closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          linarith [hur_nonneg]
        exact sq_le_sq' hLower hUpper
  have hnorm_sq_le :
      ‖closed_unit_ball_boundary_chart_inverse k i s z‖ ^ 2 ≤ 1 := by
    -- Rewrite the inverse through the split norm formula and bound the graphing coordinate by
    -- the square-root branch radius.
    rw [closed_unit_ball_boundary_chart_inverse, split_at_coordinate_symm_norm_sq]
    dsimp [t, ur]
    calc
      ‖(split_at_coordinate (0 : Fin (k + 2)) z.1).1‖ ^ 2 +
          (closed_unit_ball_boundary_branch k s
              (split_at_coordinate (0 : Fin (k + 2)) z.1).1 -
            closed_unit_ball_boundary_sign s *
              (split_at_coordinate (0 : Fin (k + 2)) z.1).2) ^ 2
          ≤ ‖ur.1‖ ^ 2 + (Real.sqrt (1 - ‖ur.1‖ ^ 2)) ^ 2 := by
            gcongr
      _ = ‖ur.1‖ ^ 2 + (1 - ‖ur.1‖ ^ 2) := by
            rw [Real.sq_sqrt hrad_nonneg]
      _ = 1 := by ring
  have hnorm_le :
      ‖closed_unit_ball_boundary_chart_inverse k i s z‖ ≤ 1 := by
    -- Convert the squared norm estimate back to the norm estimate for the closed unit ball.
    rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one]
    simpa [pow_two] using hnorm_sq_le
  -- The closed-ball membership statement is just the norm bound centered at the origin.
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le

/-- Helper for Problem 2-4: the origin belongs to every closed unit ball in Euclidean space, so it
provides a canonical fallback point of the subtype closed ball. -/
lemma zero_mem_closed_unit_ball (m : ℕ) :
    (0 : EuclideanSpace ℝ (Fin m)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  -- The origin has norm `0`, so it automatically satisfies the radius-`1` closed-ball bound.
  simp [Metric.mem_closedBall]

/-- Helper for Problem 2-4: the closed unit ball comes with the canonical basepoint given by the
ambient origin. -/
def closed_unit_ball_basepoint (m : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  ⟨0, zero_mem_closed_unit_ball m⟩

/-- Helper for Problem 2-4: each coordinate of a Euclidean vector is bounded by its ambient
Euclidean norm. -/
lemma closed_unit_ball_coordinate_abs_le_norm {m : ℕ}
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    |x i| ≤ ‖x‖ := by
  -- The ambient `L²` norm dominates every coordinate seminorm.
  simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le x i)

/-- Helper for Problem 2-4: the center chart uses the fixed interior point of the half-space model
whose distinguished coordinate is `1`. -/
def closed_unit_ball_center_target_point (k : ℕ) : EuclideanHalfSpace (k + 2) :=
  ⟨EuclideanSpace.single (0 : Fin (k + 2)) (1 : ℝ), by simp⟩

/-- Helper for Problem 2-4: the center chart source is the radius-`1/2` interior patch of the
closed unit ball. -/
def closed_unit_ball_center_chart_source (k : ℕ) :
    Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
  {x | ‖x.1‖ < (1 : ℝ) / 2}

/-- Helper for Problem 2-4: the center chart target is the radius-`1/2` half-space patch around
the fixed interior point. -/
def closed_unit_ball_center_chart_target (k : ℕ) :
    Set (EuclideanHalfSpace (k + 2)) :=
  {z | ‖z.1 - (closed_unit_ball_center_target_point k).1‖ < (1 : ℝ) / 2}

/-- Helper for Problem 2-4: the center chart source patch is the subtype of the closed unit ball
cut out by the radius-`1/2` interior source set. -/
abbrev closed_unit_ball_center_chart_source_patch (k : ℕ) :=
  {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 //
    x ∈ closed_unit_ball_center_chart_source k}

/-- Helper for Problem 2-4: the center chart target patch is the subtype of the half-space model
cut out by the radius-`1/2` target set around the fixed interior point. -/
abbrev closed_unit_ball_center_chart_target_patch (k : ℕ) :=
  {z : EuclideanHalfSpace (k + 2) // z ∈ closed_unit_ball_center_chart_target k}

section

variable (k : ℕ)

local notation "B" => Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1

/-- Helper for Problem 2-4: translating the small interior source patch by the fixed center point
lands in Lee's half-space model. -/
private theorem closed_unit_ball_center_chart_forward_nonneg
    (x : closed_unit_ball_center_chart_source_patch k) :
    0 ≤ (x.1.1 + (closed_unit_ball_center_target_point k).1) 0 := by
  have hx : ‖x.1.1‖ < (1 : ℝ) / 2 := x.2
  have hcoord : |x.1.1 0| < (1 : ℝ) / 2 := by
    -- The chosen coordinate is controlled by the ambient norm, so the interior radius still
    -- leaves a positive half-space margin after translation by the center point.
    exact lt_of_le_of_lt (closed_unit_ball_coordinate_abs_le_norm x.1.1 0) hx
  have hlower : -((1 : ℝ) / 2) < x.1.1 0 := (abs_lt.mp hcoord).1
  have hpos : 0 < x.1.1 0 + 1 := by
    linarith
  -- The translated distinguished coordinate is therefore strictly positive.
  simpa [closed_unit_ball_center_target_point] using le_of_lt hpos

/-- Helper for Problem 2-4: translating the small interior source patch by the center point lands
in the explicit half-space target patch. -/
private theorem closed_unit_ball_center_chart_forward_mem_target
    (x : closed_unit_ball_center_chart_source_patch k) :
    (⟨x.1.1 + (closed_unit_ball_center_target_point k).1,
      closed_unit_ball_center_chart_forward_nonneg k x⟩ :
        EuclideanHalfSpace (k + 2)) ∈ closed_unit_ball_center_chart_target k := by
  -- After subtracting the fixed center point, the target norm reduces to the original source
  -- norm.
  change
    ‖(x.1.1 + (closed_unit_ball_center_target_point k).1) -
        (closed_unit_ball_center_target_point k).1‖ <
      (1 : ℝ) / 2
  simpa [sub_eq_add_neg, add_assoc] using
    (show ‖x.1.1‖ < (1 : ℝ) / 2 from x.2)

/-- Helper for Problem 2-4: the center chart forward map is the affine translation from the small
interior source patch to the fixed interior half-space patch. -/
private def closed_unit_ball_center_chart_forward
    (x : closed_unit_ball_center_chart_source_patch k) :
    closed_unit_ball_center_chart_target_patch k :=
  ⟨⟨x.1.1 + (closed_unit_ball_center_target_point k).1,
      closed_unit_ball_center_chart_forward_nonneg k x⟩,
    closed_unit_ball_center_chart_forward_mem_target k x⟩

/-- Helper for Problem 2-4: subtracting the fixed center point from a target-patch point lands
back in the closed unit ball. -/
private theorem closed_unit_ball_center_chart_inverse_mem_closedBall
    (z : closed_unit_ball_center_chart_target_patch k) :
    z.1.1 - (closed_unit_ball_center_target_point k).1 ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 := by
  have hz : ‖z.1.1 - (closed_unit_ball_center_target_point k).1‖ < (1 : ℝ) / 2 := z.2
  have hle : ‖z.1.1 - (closed_unit_ball_center_target_point k).1‖ ≤ (1 : ℝ) := by
    linarith
  -- Any point in the radius-`1/2` target patch automatically lies in the ambient closed unit ball
  -- after translating back by the center point.
  simpa [Metric.mem_closedBall, dist_eq_norm] using hle

/-- Helper for Problem 2-4: the center chart inverse is the affine translation back to the small
interior closed-ball patch. -/
private def closed_unit_ball_center_chart_inverse
    (z : closed_unit_ball_center_chart_target_patch k) :
    closed_unit_ball_center_chart_source_patch k :=
  ⟨⟨z.1.1 - (closed_unit_ball_center_target_point k).1,
      closed_unit_ball_center_chart_inverse_mem_closedBall k z⟩,
    z.2⟩

/-- Helper for Problem 2-4: subtracting the center point after adding it recovers the original
closed-ball source point. -/
private theorem closed_unit_ball_center_chart_inverse_forward_val
    (x : closed_unit_ball_center_chart_source_patch k) :
    (closed_unit_ball_center_chart_inverse k
      (closed_unit_ball_center_chart_forward k x)).1 = x.1 := by
  -- The forward and inverse center-chart translations are affine inverses on the ambient
  -- Euclidean space.
  apply Subtype.ext
  ext i
  simp [closed_unit_ball_center_chart_forward, closed_unit_ball_center_chart_inverse,
    closed_unit_ball_center_target_point, sub_eq_add_neg, add_assoc]

/-- Helper for Problem 2-4: adding the center point after subtracting it recovers the original
half-space target point. -/
private theorem closed_unit_ball_center_chart_forward_inverse_val
    (z : closed_unit_ball_center_chart_target_patch k) :
    (closed_unit_ball_center_chart_forward k
      (closed_unit_ball_center_chart_inverse k z)).1 = z.1 := by
  -- The same affine cancellation works on the half-space target side.
  apply EuclideanHalfSpace.ext
  ext i
  simp [closed_unit_ball_center_chart_forward, closed_unit_ball_center_chart_inverse,
    closed_unit_ball_center_target_point, sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Problem 2-4: affine translation identifies the radius-`1/2` source patch of the
closed unit ball with the fixed interior half-space target patch. -/
private noncomputable def closed_unit_ball_center_chart_homeomorph :
    closed_unit_ball_center_chart_source_patch k ≃ₜ
      closed_unit_ball_center_chart_target_patch k where
  toFun := closed_unit_ball_center_chart_forward k
  invFun := closed_unit_ball_center_chart_inverse k
  left_inv x := by
    -- Translating to the center point and back returns the original source point.
    exact Subtype.ext (closed_unit_ball_center_chart_inverse_forward_val k x)
  right_inv z := by
    -- Translating back from the target patch and then forward returns the original target point.
    exact Subtype.ext (closed_unit_ball_center_chart_forward_inverse_val k z)
  continuous_toFun := by
    have hval :
        Continuous
          (fun x : closed_unit_ball_center_chart_source_patch k ↦
            (x.1.1 : EuclideanSpace ℝ (Fin (k + 2)))) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hRaw :
        Continuous
          (fun x : closed_unit_ball_center_chart_source_patch k ↦
            x.1.1 + (closed_unit_ball_center_target_point k).1) :=
      hval.add continuous_const
    -- The forward translation is continuous before and after reattaching the half-space and target
    -- proofs.
    exact Continuous.subtype_mk
      (Continuous.subtype_mk hRaw (fun x ↦ closed_unit_ball_center_chart_forward_nonneg k x))
      (fun x ↦ closed_unit_ball_center_chart_forward_mem_target k x)
  continuous_invFun := by
    have hval :
        Continuous
          (fun z : closed_unit_ball_center_chart_target_patch k ↦
            (z.1.1 : EuclideanSpace ℝ (Fin (k + 2)))) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hRaw :
        Continuous
          (fun z : closed_unit_ball_center_chart_target_patch k ↦
            z.1.1 - (closed_unit_ball_center_target_point k).1) :=
      hval.sub continuous_const
    -- The inverse translation is the corresponding continuous affine subtraction on the target
    -- patch.
    exact Continuous.subtype_mk
      (Continuous.subtype_mk hRaw
        (fun z ↦ closed_unit_ball_center_chart_inverse_mem_closedBall k z))
      (fun z ↦ z.2)

/-- Helper for Problem 2-4: the closed unit ball has an explicit interior chart obtained by
translating the radius-`1/2` interior patch to a fixed interior half-space point. -/
noncomputable def closed_unit_ball_center_chart :
    OpenPartialHomeomorph B (EuclideanHalfSpace (k + 2)) := by
  let sourceOpen : TopologicalSpace.Opens B :=
    ⟨closed_unit_ball_center_chart_source k, by
      have hnorm :
          Continuous (fun x : B ↦ ‖x.1‖) :=
        continuous_norm.comp continuous_subtype_val
      -- The source is the strict sublevel set of the ambient norm restricted to the closed ball.
      simpa [closed_unit_ball_center_chart_source] using isOpen_lt hnorm continuous_const⟩
  let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 2)) :=
    ⟨closed_unit_ball_center_chart_target k, by
      have hnorm :
          Continuous
            (fun z : EuclideanHalfSpace (k + 2) ↦
              ‖z.1 - (closed_unit_ball_center_target_point k).1‖) :=
        continuous_norm.comp (continuous_subtype_val.sub continuous_const)
      -- The target is the corresponding strict sublevel set around the fixed interior point.
      simpa [closed_unit_ball_center_chart_target] using isOpen_lt hnorm continuous_const⟩
  have hsource_nonempty : Nonempty sourceOpen := by
    refine ⟨⟨closed_unit_ball_basepoint (k + 2), ?_⟩⟩
    -- The ambient origin belongs to the radius-`1/2` interior source patch.
    change closed_unit_ball_basepoint (k + 2) ∈ closed_unit_ball_center_chart_source k
    simp [closed_unit_ball_center_chart_source, closed_unit_ball_basepoint]
  have htarget_nonempty : Nonempty targetOpen := by
    refine ⟨⟨closed_unit_ball_center_target_point k, ?_⟩⟩
    -- The chosen target center point is the center of its own radius-`1/2` patch.
    change closed_unit_ball_center_target_point k ∈ closed_unit_ball_center_chart_target k
    simp [closed_unit_ball_center_chart_target]
  -- Route correction: install the interior owner chart explicitly before the later
  -- center-or-boundary case split.
  exact
    (((sourceOpen.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm).trans
      ((closed_unit_ball_center_chart_homeomorph k).toOpenPartialHomeomorph.trans
        (targetOpen.openPartialHomeomorphSubtypeCoe htarget_nonempty)))

end

/-- Helper for Problem 2-4: the inverse of the canonical open-subtype inclusion keeps the
underlying point and only restores the proof of membership in the open set. -/
lemma openPartialHomeomorphSubtypeCoe_symm_eq_mk {X : Type*} [TopologicalSpace X]
    (s : TopologicalSpace.Opens X) (hs : Nonempty s) {x : X} (hx : x ∈ (s : Set X)) :
    ((s.openPartialHomeomorphSubtypeCoe hs).symm x : s) = ⟨x, hx⟩ := by
  -- The inverse inclusion chart is the identity on points, so only the subtype proof changes.
  apply Subtype.ext
  have hxTarget : x ∈ (s.openPartialHomeomorphSubtypeCoe hs).target := by
    simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hx
  simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
    (s.openPartialHomeomorphSubtypeCoe hs).right_inv hxTarget

/-- Helper for Problem 2-4: on the target of the Euclidean half-space model, the inverse model
chart has the original ambient point as its underlying value. -/
lemma modelWithCornersEuclideanHalfSpace_symm_val (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 2))} (hz : z ∈ (𝓡∂ (k + 2)).target) :
    (((𝓡∂ (k + 2)).symm z).1) = z := by
  -- The model with corners is just the subtype inclusion of the half-space into Euclidean space.
  have hzRange : z ∈ Set.range ((𝓡∂ (k + 2)) : EuclideanHalfSpace (k + 2) → _) := by
    simpa [ModelWithCorners.target_eq] using hz
  simpa using (𝓡∂ (k + 2)).right_inv hzRange

/-- Helper for Problem 2-4: on the source of the center chart, the extended chart is literally
translation by the fixed half-space center point. -/
lemma closed_unit_ball_center_chart_extend_eq_add (k : ℕ)
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : x ∈ (closed_unit_ball_center_chart k).source) :
    ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))) x =
      x.1 + (closed_unit_ball_center_target_point k).1 := by
  let sourceOpen : TopologicalSpace.Opens
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    ⟨closed_unit_ball_center_chart_source k, by
      have hnorm :
          Continuous
            (fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 ↦ ‖x.1‖) :=
        continuous_norm.comp continuous_subtype_val
      -- The source is the strict sublevel set of the ambient norm restricted to the closed ball.
      simpa [closed_unit_ball_center_chart_source] using isOpen_lt hnorm continuous_const⟩
  let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 2)) :=
    ⟨closed_unit_ball_center_chart_target k, by
      have hnorm :
          Continuous
            (fun z : EuclideanHalfSpace (k + 2) ↦
              ‖z.1 - (closed_unit_ball_center_target_point k).1‖) :=
        continuous_norm.comp (continuous_subtype_val.sub continuous_const)
      -- The target is the corresponding strict sublevel set around the fixed interior point.
      simpa [closed_unit_ball_center_chart_target] using isOpen_lt hnorm continuous_const⟩
  have hsource_nonempty : Nonempty sourceOpen := by
    refine ⟨⟨closed_unit_ball_basepoint (k + 2), ?_⟩⟩
    -- The ambient origin belongs to the radius-`1/2` interior source patch.
    change closed_unit_ball_basepoint (k + 2) ∈ closed_unit_ball_center_chart_source k
    simp [closed_unit_ball_center_chart_source, closed_unit_ball_basepoint]
  have htarget_nonempty : Nonempty targetOpen := by
    refine ⟨⟨closed_unit_ball_center_target_point k, ?_⟩⟩
    -- The chosen target center point is the center of its own radius-`1/2` patch.
    change closed_unit_ball_center_target_point k ∈ closed_unit_ball_center_chart_target k
    simp [closed_unit_ball_center_chart_target]
  have hx_source : x ∈ closed_unit_ball_center_chart_source k := by
    -- The packaged chart source is definitionally the radius-`1/2` interior source patch.
    simpa [closed_unit_ball_center_chart, OpenPartialHomeomorph.trans_source] using hx
  -- Normalize the packaged chart to the homeomorphism between the explicit source and target
  -- patches, then rewrite the source inclusion inverse using the source-membership witness `hx`.
  change
    (((closed_unit_ball_center_chart_homeomorph k)
      ((sourceOpen.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm x)).1.1) =
      x.1 + (closed_unit_ball_center_target_point k).1
  rw [openPartialHomeomorphSubtypeCoe_symm_eq_mk sourceOpen hsource_nonempty
    (by simpa [sourceOpen] using hx_source)]
  -- After the source inclusion chart is normalized, the interior homeomorphism is literally the
  -- affine translation by the fixed center point.
  rfl

/-- Helper for Problem 2-4: on the target of the extended center chart, the inverse chart is
literally subtraction of the fixed half-space center point. -/
lemma closed_unit_ball_center_chart_symm_extend_val_eq_sub (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 2))}
    (hz : z ∈ ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).target) :
    ((((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z).1) =
      z - (closed_unit_ball_center_target_point k).1 := by
  let sourceOpen : TopologicalSpace.Opens
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    ⟨closed_unit_ball_center_chart_source k, by
      have hnorm :
          Continuous
            (fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 ↦ ‖x.1‖) :=
        continuous_norm.comp continuous_subtype_val
      -- The source is the strict sublevel set of the ambient norm restricted to the closed ball.
      simpa [closed_unit_ball_center_chart_source] using isOpen_lt hnorm continuous_const⟩
  let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 2)) :=
    ⟨closed_unit_ball_center_chart_target k, by
      have hnorm :
          Continuous
            (fun z : EuclideanHalfSpace (k + 2) ↦
              ‖z.1 - (closed_unit_ball_center_target_point k).1‖) :=
        continuous_norm.comp (continuous_subtype_val.sub continuous_const)
      -- The target is the corresponding strict sublevel set around the fixed interior point.
      simpa [closed_unit_ball_center_chart_target] using isOpen_lt hnorm continuous_const⟩
  have hsource_nonempty : Nonempty sourceOpen := by
    refine ⟨⟨closed_unit_ball_basepoint (k + 2), ?_⟩⟩
    -- The ambient origin belongs to the radius-`1/2` interior source patch.
    change closed_unit_ball_basepoint (k + 2) ∈ closed_unit_ball_center_chart_source k
    simp [closed_unit_ball_center_chart_source, closed_unit_ball_basepoint]
  have htarget_nonempty : Nonempty targetOpen := by
    refine ⟨⟨closed_unit_ball_center_target_point k, ?_⟩⟩
    -- The chosen target center point is the center of its own radius-`1/2` patch.
    change closed_unit_ball_center_target_point k ∈ closed_unit_ball_center_chart_target k
    simp [closed_unit_ball_center_chart_target]
  have hz_split :
      z ∈ (𝓡∂ (k + 2)).target ∧
        (𝓡∂ (k + 2)).symm z ∈ (closed_unit_ball_center_chart k).target := by
    -- Extended-target membership records both that `z` lies in the half-space model target and
    -- that its inverse-model point belongs to the raw center-chart target.
    simpa [OpenPartialHomeomorph.extend_target, ModelWithCorners.target_eq] using hz
  have hz_target : (𝓡∂ (k + 2)).symm z ∈ targetOpen := by
    -- The packaged chart target is definitionally the radius-`1/2` target patch.
    simpa [closed_unit_ball_center_chart, OpenPartialHomeomorph.trans_target, targetOpen] using
      hz_split.2
  -- Normalize the packaged inverse chart to the inverse homeomorphism between the explicit target
  -- and source patches, then rewrite the target inclusion inverse using `hz_target`.
  change
    (((sourceOpen.openPartialHomeomorphSubtypeCoe hsource_nonempty)
      ((closed_unit_ball_center_chart_homeomorph k).symm
        ((targetOpen.openPartialHomeomorphSubtypeCoe htarget_nonempty).symm
          ((𝓡∂ (k + 2)).symm z)))).1) =
      z - (closed_unit_ball_center_target_point k).1
  rw [openPartialHomeomorphSubtypeCoe_symm_eq_mk targetOpen htarget_nonempty
    (by simpa [targetOpen] using hz_target)]
  -- After the target inclusion chart is normalized, the interior inverse homeomorphism is
  -- literally the affine subtraction by the fixed center point.
  simp [closed_unit_ball_center_chart_homeomorph, closed_unit_ball_center_chart_inverse,
    modelWithCornersEuclideanHalfSpace_symm_val k hz_split.1]

/-- Helper for Problem 2-4: for a point of the closed unit ball, the distinguished coordinate
obtained after splitting off coordinate `i` is bounded by the graphing square root. -/
lemma closed_unit_ball_split_coordinate_abs_le_branch_core {k : ℕ}
    (i : Fin (k + 2)) {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    |(split_at_coordinate i x).2| ≤
      Real.sqrt (1 - ‖(split_at_coordinate i x).1‖ ^ 2) := by
  -- First convert the closed-ball condition into a norm bound.
  have hnorm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hnorm_sq : ‖x‖ ^ 2 ≤ 1 := by
    nlinarith [hnorm, norm_nonneg x]
  -- Then rewrite the ambient norm after splitting off the `i`-th coordinate.
  have hsplit :
      ‖x‖ ^ 2 = ‖(split_at_coordinate i x).1‖ ^ 2 + (split_at_coordinate i x).2 ^ 2 := by
    simpa using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x)
  have hsnd_sq :
      (split_at_coordinate i x).2 ^ 2 ≤ 1 - ‖(split_at_coordinate i x).1‖ ^ 2 := by
    linarith
  have hrad_nonneg : 0 ≤ 1 - ‖(split_at_coordinate i x).1‖ ^ 2 := by
    linarith [sq_nonneg ((split_at_coordinate i x).2)]
  -- Taking square roots yields the desired bound on the distinguished coordinate.
  rw [← sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt hrad_nonneg]
  exact hsnd_sq

/-- Helper for Problem 2-4: the ambient forward boundary-chart formula is obtained by splitting off
the `i`-th coordinate and recording the signed vertical distance to the chosen graph branch. -/
def closed_unit_ball_boundary_chart_forward_extend (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 2)) :=
  fun x ↦
    let ui := split_at_coordinate i x
    (split_at_coordinate (0 : Fin (k + 2))).symm
      (ui.1,
        closed_unit_ball_boundary_sign s *
          (closed_unit_ball_boundary_branch k s ui.1 - ui.2))

/-- Helper for Problem 2-4: the ambient forward boundary-chart formula is continuous, since it is
built from continuous coordinate splits and the continuous square-root graph branch. -/
lemma closed_unit_ball_boundary_chart_forward_extend_continuous (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    Continuous (closed_unit_ball_boundary_chart_forward_extend k i s) := by
  let ui : EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 1)) × ℝ :=
    split_at_coordinate i
  have hui : Continuous ui := split_at_coordinate_continuous i
  have hbranch : Continuous (closed_unit_ball_boundary_branch k s) := by
    -- The sign choice only toggles between the square-root branch and its negation.
    cases s with
    | false =>
        simpa [closed_unit_ball_boundary_branch] using
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              -Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
    | true =>
        simpa [closed_unit_ball_boundary_branch] using
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
  have htail :
      Continuous (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦ (ui x).1) :=
    continuous_fst.comp hui
  have hcoord :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦
          closed_unit_ball_boundary_sign s *
            (closed_unit_ball_boundary_branch k s (ui x).1 - (ui x).2)) := by
    -- The graph-distance coordinate is built from the branch value and the distinguished split
    -- coordinate by affine operations.
    exact continuous_const.mul ((hbranch.comp htail).sub (continuous_snd.comp hui))
  have hpair :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ((ui x).1,
            closed_unit_ball_boundary_sign s *
              (closed_unit_ball_boundary_branch k s (ui x).1 - (ui x).2))) :=
    htail.prodMk hcoord
  -- Reinsert the normalized split coordinates with the continuous inverse split.
  simpa [closed_unit_ball_boundary_chart_forward_extend, ui] using
    (split_at_coordinate_symm_continuous (i := (0 : Fin (k + 2)))).comp hpair

/-- Helper for Problem 2-4: normalizing the ambient forward chart by `split_at_coordinate 0`
recovers the expected tail coordinates and signed graph-distance coordinate. -/
lemma closed_unit_ball_boundary_chart_forward_extend_split {k : ℕ}
    (i : Fin (k + 2)) (s : Bool) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    split_at_coordinate (0 : Fin (k + 2))
        (closed_unit_ball_boundary_chart_forward_extend k i s x) =
      ((split_at_coordinate i x).1,
        closed_unit_ball_boundary_sign s *
          (closed_unit_ball_boundary_branch k s (split_at_coordinate i x).1 -
            (split_at_coordinate i x).2)) := by
  -- The ambient forward chart was defined by first building these split coordinates and then
  -- reassembling them with `(split_at_coordinate 0).symm`.
  simp [closed_unit_ball_boundary_chart_forward_extend]

/-- Helper for Problem 2-4: on the signed hemisphere source patch of the closed unit ball, the
ambient forward chart lands in the Euclidean half-space. -/
lemma closed_unit_ball_boundary_chart_forward_nonneg {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : 0 < closed_unit_ball_boundary_sign s * x.1 i) :
    0 ≤
      (split_at_coordinate (0 : Fin (k + 2))
        (closed_unit_ball_boundary_chart_forward_extend k i s x.1)).2 := by
  -- The distinguished coordinate is the signed gap between the graph branch and the actual
  -- `i`-th coordinate, and the closed-ball inequality bounds that gap below by `0`.
  have habs :
      |x.1 i| ≤
        Real.sqrt (1 - ‖(split_at_coordinate i x.1).1‖ ^ 2) := by
    simpa [split_at_coordinate_snd_apply] using
      closed_unit_ball_split_coordinate_abs_le_branch_core i x.2
  have habs' := abs_le.mp habs
  cases s with
  | false =>
      have hcoord :
          (split_at_coordinate (0 : Fin (k + 2))
            (closed_unit_ball_boundary_chart_forward_extend k i false x.1)).2 =
            x.1 i + Real.sqrt (1 - ‖(split_at_coordinate i x.1).1‖ ^ 2) := by
        simp [closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
          closed_unit_ball_boundary_sign, split_at_coordinate_snd_apply]
      rw [hcoord]
      linarith [habs'.1]
  | true =>
      have hcoord :
          (split_at_coordinate (0 : Fin (k + 2))
            (closed_unit_ball_boundary_chart_forward_extend k i true x.1)).2 =
            Real.sqrt (1 - ‖(split_at_coordinate i x.1).1‖ ^ 2) - x.1 i := by
        simp [closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
          closed_unit_ball_boundary_sign, split_at_coordinate_snd_apply]
      rw [hcoord]
      linarith [habs'.2]

/-- Helper for Problem 2-4: the actual forward boundary chart from the closed unit ball to the
half-space uses the ambient formula together with the half-space nonnegativity estimate. -/
def closed_unit_ball_boundary_chart_forward (k : ℕ) (i : Fin (k + 2)) (s : Bool)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hx : 0 < closed_unit_ball_boundary_sign s * x.1 i) :
    EuclideanHalfSpace (k + 2) :=
  ⟨closed_unit_ball_boundary_chart_forward_extend k i s x.1,
    closed_unit_ball_boundary_chart_forward_nonneg i s hx⟩

/-- Helper for Problem 2-4: the common hypograph target used for the higher-dimensional boundary
charts is open in the half-space. -/
lemma isOpen_closed_unit_ball_boundary_chart_target (k : ℕ) :
    IsOpen (closed_unit_ball_boundary_chart_target k) := by
  let ufun : EuclideanHalfSpace (k + 2) → EuclideanSpace ℝ (Fin (k + 1)) :=
    fun z ↦ (split_at_coordinate (0 : Fin (k + 2)) z.1).1
  let rfun : EuclideanHalfSpace (k + 2) → ℝ :=
    fun z ↦ (split_at_coordinate (0 : Fin (k + 2)) z.1).2
  have hsplit :
      Continuous (fun z : EuclideanHalfSpace (k + 2) ↦
        split_at_coordinate (0 : Fin (k + 2)) z.1) :=
    (split_at_coordinate_continuous (0 : Fin (k + 2))).comp continuous_subtype_val
  have hu : Continuous ufun := continuous_fst.comp hsplit
  have hr : Continuous rfun := continuous_snd.comp hsplit
  have hbranch :
      Continuous (fun z : EuclideanHalfSpace (k + 2) ↦
        Real.sqrt (1 - ‖ufun z‖ ^ 2)) := by
    -- The defining graph branch is continuous on the whole ambient space.
    fun_prop
  -- The target is the intersection of the open unit-ball condition on the tail coordinates and the
  -- strict hypograph inequality for the graph branch.
  simpa [closed_unit_ball_boundary_chart_target, ufun, rfun] using
    (isOpen_lt hu.norm continuous_const).inter (isOpen_lt hr hbranch)

/-- Helper for Problem 2-4: the explicit forward boundary chart sends the signed hemisphere patch
of the closed unit ball into the common hypograph target. -/
lemma closed_unit_ball_boundary_chart_forward_mem_target {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hx : 0 < closed_unit_ball_boundary_sign s * x.1 i) :
    closed_unit_ball_boundary_chart_forward k i s x hx ∈
      closed_unit_ball_boundary_chart_target k := by
  let ui := split_at_coordinate i x.1
  have hnorm : ‖x.1‖ ≤ 1 := by
    -- Membership in the ambient closed unit ball is exactly the norm bound.
    have hdist :
        dist x.1 (0 : EuclideanSpace ℝ (Fin (k + 2))) ≤ 1 := x.2
    simpa [dist_eq_norm] using hdist
  have hnorm_sq : ‖x.1‖ ^ 2 ≤ 1 := by
    nlinarith [hnorm, norm_nonneg x.1]
  have hsplit :
      ‖x.1‖ ^ 2 = ‖ui.1‖ ^ 2 + ui.2 ^ 2 := by
    -- Splitting off coordinate `i` separates the tail norm and the chosen coordinate.
    simpa [ui] using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x.1)
  have hcoord_ne : ui.2 ≠ 0 := by
    -- The signed hemisphere hypothesis says the chosen coordinate is strictly positive or strictly
    -- negative after the fixed sign normalization, so it cannot vanish.
    cases s with
    | false =>
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx.ne'
    | true =>
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx.ne'
  have hcoord_sq_pos : 0 < ui.2 ^ 2 := by
    exact sq_pos_iff.mpr hcoord_ne
  have htail_sq_lt : ‖ui.1‖ ^ 2 < 1 := by
    -- The strictly nonzero chosen coordinate forces the remaining coordinates to lie in the open
    -- unit ball.
    nlinarith [hnorm_sq, hsplit, hcoord_sq_pos]
  have htail_lt : ‖ui.1‖ < 1 := by
    nlinarith [htail_sq_lt, norm_nonneg ui.1]
  rw [closed_unit_ball_boundary_chart_target_mem_iff]
  constructor
  · -- The retained coordinates are exactly the tail coordinates from the original split at `i`.
    simpa [closed_unit_ball_boundary_chart_forward, ui,
      closed_unit_ball_boundary_chart_forward_extend_split]
      using htail_lt
  · -- The normalized graph-distance coordinate stays strictly below the square-root branch by the
    -- chosen sign of the distinguished coordinate.
    cases s with
    | false =>
        have hneg : ui.2 < 0 := by
          simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx
        have htarget :
            ui.2 + Real.sqrt (1 - ‖ui.1‖ ^ 2) <
              Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
          linarith
        simpa [closed_unit_ball_boundary_chart_forward, ui,
          closed_unit_ball_boundary_chart_forward_extend_split,
          closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          using htarget
    | true =>
        have hpos : 0 < ui.2 := by
          simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx
        have htarget :
            Real.sqrt (1 - ‖ui.1‖ ^ 2) - ui.2 <
              Real.sqrt (1 - ‖ui.1‖ ^ 2) := by
          linarith
        simpa [closed_unit_ball_boundary_chart_forward, ui,
          closed_unit_ball_boundary_chart_forward_extend_split,
          closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
          using htarget

/-- Helper for Problem 2-4: the ambient inverse formula is globally continuous on the half-space,
because it uses only continuous split-coordinate maps and the continuous square-root branch. -/
lemma closed_unit_ball_boundary_chart_inverse_continuous (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    Continuous (closed_unit_ball_boundary_chart_inverse k i s) := by
  let ur : EuclideanHalfSpace (k + 2) → EuclideanSpace ℝ (Fin (k + 1)) × ℝ :=
    fun z ↦ split_at_coordinate (0 : Fin (k + 2)) z.1
  have hur : Continuous ur :=
    (split_at_coordinate_continuous (i := (0 : Fin (k + 2)))).comp continuous_subtype_val
  have hbranch0 : Continuous (closed_unit_ball_boundary_branch k s) := by
    -- As in the forward chart, the sign choice only negates the square-root branch.
    cases s with
    | false =>
        simpa [closed_unit_ball_boundary_branch] using
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              -Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
    | true =>
        simpa [closed_unit_ball_boundary_branch] using
          (show Continuous
            (fun u : EuclideanSpace ℝ (Fin (k + 1)) ↦
              Real.sqrt (1 - ‖u‖ ^ 2)) by
            fun_prop)
  have htail :
      Continuous (fun z : EuclideanHalfSpace (k + 2) ↦ (ur z).1) :=
    continuous_fst.comp hur
  have hcoord :
      Continuous
        (fun z : EuclideanHalfSpace (k + 2) ↦
          closed_unit_ball_boundary_branch k s (ur z).1 -
            closed_unit_ball_boundary_sign s * (ur z).2) := by
    -- The distinguished inverse coordinate is the branch value minus an affine correction term.
    exact (hbranch0.comp htail).sub (continuous_const.mul (continuous_snd.comp hur))
  have hpair :
      Continuous
        (fun z : EuclideanHalfSpace (k + 2) ↦
          ((ur z).1,
            closed_unit_ball_boundary_branch k s (ur z).1 -
              closed_unit_ball_boundary_sign s * (ur z).2)) :=
    htail.prodMk hcoord
  -- The half-space inverse is the continuous inverse split applied to these normalized coordinates.
  simpa [closed_unit_ball_boundary_chart_inverse, ur] using
    (split_at_coordinate_symm_continuous (i := i)).comp hpair

/-- Helper for Problem 2-4: applying the inverse boundary graph formula after the forward chart on
its signed hemisphere source patch recovers the original closed-ball point. -/
lemma closed_unit_ball_boundary_chart_inverse_forward {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hx : 0 < closed_unit_ball_boundary_sign s * x.1 i) :
    closed_unit_ball_boundary_chart_inverse k i s
      (closed_unit_ball_boundary_chart_forward k i s x hx) = x.1 := by
  -- The forward chart records exactly the signed graph-distance coordinate that the inverse
  -- subtracts back off.
  have hright :
      (split_at_coordinate i).symm
        ((split_at_coordinate i x.1).1, (split_at_coordinate i x.1).2) = x.1 := by
    exact (split_at_coordinate i).left_inv x.1
  cases s with
  | false =>
      simpa [closed_unit_ball_boundary_chart_forward, closed_unit_ball_boundary_chart_inverse,
        closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
        closed_unit_ball_boundary_sign, split_at_coordinate_snd_apply] using hright
  | true =>
      simpa [closed_unit_ball_boundary_chart_forward, closed_unit_ball_boundary_chart_inverse,
        closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
        closed_unit_ball_boundary_sign, split_at_coordinate_snd_apply] using hright

/-- Helper for Problem 2-4: a point of the common hypograph target maps under the boundary inverse
into the signed hemisphere source patch determined by the chosen sign. -/
lemma closed_unit_ball_boundary_chart_inverse_signed_coordinate_pos {k : ℕ}
    (i : Fin (k + 2)) (s : Bool) {z : EuclideanHalfSpace (k + 2)}
    (hz : z ∈ closed_unit_ball_boundary_chart_target k) :
    0 <
      closed_unit_ball_boundary_sign s *
        (closed_unit_ball_boundary_chart_inverse k i s z) i := by
  let ur := split_at_coordinate (0 : Fin (k + 2)) z.1
  have hur : ‖ur.1‖ < 1 ∧ ur.2 < Real.sqrt (1 - ‖ur.1‖ ^ 2) := by
    -- The target point satisfies the normalized tail-ball and hypograph inequalities by
    -- definition.
    simpa [closed_unit_ball_boundary_chart_target, ur] using hz
  have hcoord :
      (closed_unit_ball_boundary_chart_inverse k i s z) i =
        closed_unit_ball_boundary_branch k s ur.1 -
          closed_unit_ball_boundary_sign s * ur.2 := by
    -- The distinguished `i`-th coordinate is exactly the scalar reinserted by
    -- `split_at_coordinate i`.
    simp [closed_unit_ball_boundary_chart_inverse, ur, split_at_coordinate_symm_apply_self]
  cases s with
  | false =>
      -- In the lower branch, multiplying by the sign `-1` turns the distinguished coordinate into
      -- `sqrt(1 - ‖u‖²) - r`, which is positive by the target inequality.
      rw [hcoord]
      simp [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
      linarith
  | true =>
      -- In the upper branch, the distinguished coordinate is already `sqrt(1 - ‖u‖²) - r`.
      rw [hcoord]
      simp [closed_unit_ball_boundary_branch, closed_unit_ball_boundary_sign]
      linarith

/-- Helper for Problem 2-4: the forward boundary chart is inverse to the graphing formula on the
common hypograph target. -/
lemma closed_unit_ball_boundary_chart_forward_inverse {k : ℕ}
    (i : Fin (k + 2)) (s : Bool) {z : EuclideanHalfSpace (k + 2)}
    (hz : z ∈ closed_unit_ball_boundary_chart_target k) :
    closed_unit_ball_boundary_chart_forward k i s
      ⟨closed_unit_ball_boundary_chart_inverse k i s z,
        closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s hz⟩
      (closed_unit_ball_boundary_chart_inverse_signed_coordinate_pos i s hz) = z := by
  -- The inverse reconstructs the same normalized split coordinates that the forward chart reads
  -- off, so the half-space point is recovered exactly.
  apply EuclideanHalfSpace.ext
  apply (split_at_coordinate (0 : Fin (k + 2))).injective
  cases s with
  | false =>
      simp [closed_unit_ball_boundary_chart_forward, closed_unit_ball_boundary_chart_inverse,
        closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
        closed_unit_ball_boundary_sign]
  | true =>
      simp [closed_unit_ball_boundary_chart_forward, closed_unit_ball_boundary_chart_inverse,
        closed_unit_ball_boundary_chart_forward_extend, closed_unit_ball_boundary_branch,
        closed_unit_ball_boundary_sign]

attribute [local instance] Classical.propDecidable

/-- Helper for Problem 2-4: membership in the signed hemisphere source set is exactly the
positivity condition used by Lee's explicit forward graph chart. -/
lemma closed_unit_ball_boundary_chart_source_pos {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : x ∈ {x | 0 < closed_unit_ball_boundary_sign s * x.1 i}) :
    0 < closed_unit_ball_boundary_sign s * x.1 i := hx

/-- Helper for Problem 2-4: package Lee's signed hemisphere graph chart as an actual
`OpenPartialHomeomorph` from the closed unit ball to the normalized half-space target. -/
noncomputable def closed_unit_ball_boundary_chart (k : ℕ) (i : Fin (k + 2)) (s : Bool) :
    OpenPartialHomeomorph
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
      (EuclideanHalfSpace (k + 2)) where
  toPartialEquiv :=
    { toFun := fun x ↦
        if hx : x ∈ {x | 0 < closed_unit_ball_boundary_sign s * x.1 i} then
          closed_unit_ball_boundary_chart_forward k i s x
            (closed_unit_ball_boundary_chart_source_pos i s hx)
        else
          0
      invFun := fun z ↦
        if hz : z ∈ closed_unit_ball_boundary_chart_target k then
          ⟨closed_unit_ball_boundary_chart_inverse k i s z,
            closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s hz⟩
        else
          closed_unit_ball_basepoint (k + 2)
      source := {x | 0 < closed_unit_ball_boundary_sign s * x.1 i}
      target := closed_unit_ball_boundary_chart_target k
      map_source' := by
        intro x hx
        have hx0 := closed_unit_ball_boundary_chart_source_pos i s hx
        -- On the signed hemisphere source, the totalized chart agrees with Lee's forward formula.
        simpa [hx, hx0] using
          closed_unit_ball_boundary_chart_forward_mem_target (k := k) i s x hx0
      map_target' := by
        intro z hz
        -- On the common target, the totalized inverse agrees with the graphing inverse and lands
        -- back in the same signed hemisphere source.
        have hz0 : z ∈ closed_unit_ball_boundary_chart_target k := hz
        simpa [hz0] using
          closed_unit_ball_boundary_chart_inverse_signed_coordinate_pos (k := k) i s hz0
      left_inv' := by
        intro x hx
        have hx0 := closed_unit_ball_boundary_chart_source_pos i s hx
        have hz :
            closed_unit_ball_boundary_chart_forward k i s x hx0 ∈
              closed_unit_ball_boundary_chart_target k :=
          closed_unit_ball_boundary_chart_forward_mem_target (k := k) i s x hx0
        -- The graphing inverse cancels the forward chart on the signed hemisphere source patch.
        apply Subtype.ext
        simpa [hx, hx0, hz] using
          closed_unit_ball_boundary_chart_inverse_forward (k := k) i s x hx0
      right_inv' := by
        intro z hz
        have hz0 : z ∈ closed_unit_ball_boundary_chart_target k := hz
        have hs :
            0 <
              closed_unit_ball_boundary_sign s *
                (closed_unit_ball_boundary_chart_inverse k i s z) i :=
          closed_unit_ball_boundary_chart_inverse_signed_coordinate_pos (k := k) i s hz0
        -- The forward chart reconstructs the original target point from the graphing inverse.
        apply EuclideanHalfSpace.ext
        simpa [hz0, hs] using
          congrArg Subtype.val
            (closed_unit_ball_boundary_chart_forward_inverse (k := k) i s hz0) }
  open_source := by
    have hcoord :
        Continuous
          (fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 ↦
            closed_unit_ball_boundary_sign s * x.1 i) := by
      fun_prop
    -- The source is the strict positivity region of one continuous coordinate functional.
    simpa using isOpen_lt continuous_const hcoord
  open_target := isOpen_closed_unit_ball_boundary_chart_target k
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    let S :
        Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
      {x | 0 < closed_unit_ball_boundary_sign s * x.1 i}
    have hval :
        Continuous
          (fun x : S ↦
            ((x.1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1).1 :
              EuclideanSpace ℝ (Fin (k + 2)))) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hforward :
        Continuous (fun x : S ↦ closed_unit_ball_boundary_chart_forward k i s x.1 x.2) := by
      -- On the source subtype, the forward chart is the ambient continuous formula with the
      -- half-space proof attached pointwise.
      simpa [closed_unit_ball_boundary_chart_forward] using
        (Continuous.subtype_mk
          ((closed_unit_ball_boundary_chart_forward_extend_continuous k i s).comp hval)
          (fun x ↦ closed_unit_ball_boundary_chart_forward_nonneg (k := k) i s x.2))
    -- Restricting the totalized map to its source removes the off-source default branch.
    convert hforward using 1
    ext x
    simp [S, closed_unit_ball_boundary_chart_source_pos]
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    let T : Set (EuclideanHalfSpace (k + 2)) := closed_unit_ball_boundary_chart_target k
    have hinv :
        Continuous (fun z : T ↦
          (⟨closed_unit_ball_boundary_chart_inverse k i s z.1,
            closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s z.2⟩ :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)) := by
      -- On the target subtype, the inverse is the continuous graphing formula with the closed-ball
      -- proof attached pointwise.
      simpa using
        (Continuous.subtype_mk
          ((closed_unit_ball_boundary_chart_inverse_continuous k i s).comp continuous_subtype_val)
          (fun z ↦ closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s z.2))
    -- Restricting the totalized inverse to its target removes the off-target default branch.
    simpa [T, Set.restrict_dite] using hinv

/-- Helper for Problem 2-4: a nonzero Euclidean vector has a nonzero coordinate. -/
lemma exists_nonzero_coordinate_of_ne_zero {m : ℕ}
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ≠ 0) :
    ∃ i : Fin m, x i ≠ 0 := by
  by_contra hcoord
  apply hx
  apply (EuclideanSpace.equiv (Fin m) ℝ).injective
  ext i
  -- If every coordinate vanished, the whole vector would be zero.
  by_contra hi
  exact hcoord ⟨i, hi⟩

/-- Helper for Problem 2-4: outside the radius-`1/2` interior patch, some signed coordinate of the
closed unit ball is strictly positive, so Lee's signed boundary chart covers the point. -/
lemma closed_unit_ball_boundary_choice (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hp : ¬ ‖p.1‖ < (1 : ℝ) / 2) :
    ∃ i : Fin (k + 2), ∃ s : Bool,
      0 < closed_unit_ball_boundary_sign s * p.1 i := by
  have hp_ne_zero : p.1 ≠ 0 := by
    intro hp0
    apply hp
    -- The origin lies in the radius-`1/2` interior patch, contradicting the boundary case.
    simp [hp0]
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate_of_ne_zero p.1 hp_ne_zero
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨i, false, ?_⟩
    -- A negative coordinate belongs to the lower signed hemisphere.
    simpa [closed_unit_ball_boundary_sign] using (neg_pos.mpr hneg)
  · refine ⟨i, true, ?_⟩
    -- A positive coordinate belongs to the upper signed hemisphere.
    simpa [closed_unit_ball_boundary_sign] using hpos

/-- Helper for Problem 2-4: package the signed boundary choice datum as a concrete index-sign pair
that can be reused by the pointwise atlas selector. -/
noncomputable def closed_unit_ball_boundary_choice_data (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hp : ¬ ‖p.1‖ < (1 : ℝ) / 2) :
    {is : Fin (k + 2) × Bool // 0 < closed_unit_ball_boundary_sign is.2 * p.1 is.1} :=
  let i := Classical.choose (closed_unit_ball_boundary_choice k p hp)
  let hs := Classical.choose_spec (closed_unit_ball_boundary_choice k p hp)
  let s := Classical.choose hs
  ⟨(i, s), Classical.choose_spec hs⟩

/-- Helper for Problem 2-4: Lee's higher-dimensional atlas selects the center chart on the
radius-`1/2` interior patch and otherwise the signed boundary chart provided by
`closed_unit_ball_boundary_choice_data`. -/
noncomputable def closed_unit_ball_chartAtLocal (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    OpenPartialHomeomorph
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
      (EuclideanHalfSpace (k + 2)) :=
  if hp : ‖p.1‖ < (1 : ℝ) / 2 then
    closed_unit_ball_center_chart k
  else
    let is := (closed_unit_ball_boundary_choice_data k p hp).1
    closed_unit_ball_boundary_chart k is.1 is.2

/-- Helper for Problem 2-4: on the interior radius-`1/2` patch, the pointwise atlas selector
returns the center translation chart. -/
@[simp] lemma closed_unit_ball_chartAtLocal_of_norm_lt (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hp : ‖p.1‖ < (1 : ℝ) / 2) :
    closed_unit_ball_chartAtLocal k p = closed_unit_ball_center_chart k := by
  -- The selector uses Lee's interior chart exactly on the interior patch.
  rw [closed_unit_ball_chartAtLocal, dif_pos hp]

/-- Helper for Problem 2-4: outside the interior radius-`1/2` patch, the pointwise atlas selector
returns the signed boundary chart determined by `closed_unit_ball_boundary_choice_data`. -/
@[simp] lemma closed_unit_ball_chartAtLocal_of_not_norm_lt (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (hp : ¬ ‖p.1‖ < (1 : ℝ) / 2) :
    closed_unit_ball_chartAtLocal k p =
      closed_unit_ball_boundary_chart k
        (closed_unit_ball_boundary_choice_data k p hp).1.1
        (closed_unit_ball_boundary_choice_data k p hp).1.2 := by
  -- In the complementary case, the selector is definitionally the chosen boundary chart.
  rw [closed_unit_ball_chartAtLocal, dif_neg hp]

/-- Helper for Problem 2-4: every point lies in the source of its selected local chart. -/
lemma mem_closed_unit_ball_chartAtLocal_source (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    p ∈ (closed_unit_ball_chartAtLocal k p).source := by
  by_cases hp : ‖p.1‖ < (1 : ℝ) / 2
  · -- On the interior branch, the selected center chart contains the point by construction.
    rw [closed_unit_ball_chartAtLocal_of_norm_lt k p hp]
    simpa [closed_unit_ball_center_chart, OpenPartialHomeomorph.trans_source,
      closed_unit_ball_center_chart_source] using And.intro hp (by trivial)
  · let is := (closed_unit_ball_boundary_choice_data k p hp).1
    have his : 0 < closed_unit_ball_boundary_sign is.2 * p.1 is.1 :=
      (closed_unit_ball_boundary_choice_data k p hp).2
    -- On the boundary branch, the choice datum was built exactly to put `p` in that chart source.
    rw [closed_unit_ball_chartAtLocal_of_not_norm_lt k p hp]
    simpa [is, closed_unit_ball_boundary_chart] using his

/-- Helper for Problem 2-4: Lee's higher-dimensional proof uses the fixed atlas consisting of the
center chart together with all signed boundary charts. -/
def closed_unit_ball_fixed_atlas (k : ℕ) :
    Set
      (OpenPartialHomeomorph
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
        (EuclideanHalfSpace (k + 2))) :=
  insert (closed_unit_ball_center_chart k)
    (Set.range fun is : Fin (k + 2) × Bool ↦
      closed_unit_ball_boundary_chart k is.1 is.2)

/-- Helper for Problem 2-4: the pointwise chart selector always chooses a chart from the fixed Lee
atlas. -/
lemma closed_unit_ball_chartAtLocal_mem_fixed_atlas (k : ℕ)
    (p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
    closed_unit_ball_chartAtLocal k p ∈ closed_unit_ball_fixed_atlas k := by
  by_cases hp : ‖p.1‖ < (1 : ℝ) / 2
  · -- On the interior branch, the selector returns the distinguished center chart.
    rw [closed_unit_ball_chartAtLocal_of_norm_lt k p hp]
    exact Set.mem_insert _ _
  · -- On the complementary branch, the selector returns the chosen signed boundary chart.
    rw [closed_unit_ball_chartAtLocal_of_not_norm_lt k p hp]
    exact Set.mem_insert_of_mem _ (Set.mem_range_self _)

/-- Helper for Problem 2-4: the fixed Lee atlas together with the pointwise selector already
packages the charted-space data needed for the higher-dimensional manifold structure. -/
@[reducible] noncomputable def closed_unit_ball_fixed_chartedSpace (k : ℕ) :
    ChartedSpace (EuclideanHalfSpace (k + 2))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) where
  atlas := closed_unit_ball_fixed_atlas k
  chartAt := closed_unit_ball_chartAtLocal k
  mem_chart_source := mem_closed_unit_ball_chartAtLocal_source k
  chart_mem_atlas := closed_unit_ball_chartAtLocal_mem_fixed_atlas k

/-- Helper for Problem 2-4: the ambient forward boundary-chart formula is smooth exactly on the
open set where the retained split coordinates stay in the open unit ball.

This is the correct Euclidean smoothness domain for the square-root graph branch; the larger raw
signed-hemisphere set would cross the singular radius `‖u‖ = 1`. -/
lemma closed_unit_ball_boundary_chart_forward_extend_contDiffOn (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    ContDiffOn ℝ ω
      (closed_unit_ball_boundary_chart_forward_extend k i s)
      {x : EuclideanSpace ℝ (Fin (k + 2)) |
        ‖(split_at_coordinate i x).1‖ < 1} := by
  let u : EuclideanSpace ℝ (Fin (k + 2)) → EuclideanSpace ℝ (Fin (k + 1)) :=
    fun x ↦ (split_at_coordinate i x).1
  let r : EuclideanSpace ℝ (Fin (k + 2)) → ℝ :=
    fun x ↦ (split_at_coordinate i x).2
  have hu : ContDiff ℝ ω u := by
    -- The retained coordinates are linear in the ambient coordinates.
    fun_prop
  have hr : ContDiff ℝ ω r := by
    -- The distinguished split coordinate is another linear projection.
    fun_prop
  have hbranch :
      ContDiffOn ℝ ω (fun x ↦ closed_unit_ball_boundary_branch k s (u x))
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- Compose Lee's smooth graphing branch with the retained-coordinate map.
    refine (closed_unit_ball_boundary_branch_contDiffOn k s).comp hu.contDiffOn ?_
    intro x hx
    simpa [Metric.mem_ball, dist_eq_norm, u] using hx
  have hcoord :
      ContDiffOn ℝ ω
        (fun x ↦
          closed_unit_ball_boundary_sign s *
            (closed_unit_ball_boundary_branch k s (u x) - r x))
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- The signed graph-distance coordinate is obtained from the branch value by affine
    -- operations.
    simpa [smul_eq_mul] using
      (hbranch.sub hr.contDiffOn).const_smul (closed_unit_ball_boundary_sign s)
  have hpair :
      ContDiffOn ℝ ω
        (fun x ↦
          (u x,
            closed_unit_ball_boundary_sign s *
              (closed_unit_ball_boundary_branch k s (u x) - r x)))
        {x : EuclideanSpace ℝ (Fin (k + 2)) | ‖u x‖ < 1} := by
    -- Reassemble the retained coordinates and the signed graph-distance coordinate before
    -- reinserting the distinguished slot.
    exact hu.contDiffOn.prodMk hcoord
  have hsymm : ContDiff ℝ ω (split_at_coordinate (0 : Fin (k + 2))).symm := by
    -- Reinsert the normalized coordinates using the inverse linear split at slot `0`.
    simpa [split_at_coordinate_continuousLinearEquiv,
      LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm] using
      (split_at_coordinate_continuousLinearEquiv (0 : Fin (k + 2))).symm.contDiff
  simpa [closed_unit_ball_boundary_chart_forward_extend, u, r] using
    hsymm.comp_contDiffOn hpair

section

/-- Helper for Problem 2-4: if a closed-ball point lies in one of Lee's signed boundary chart
sources, then the retained split coordinates already lie in the open unit ball. -/
lemma closed_unit_ball_boundary_chart_source_tail_norm_lt_one {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : x ∈ (closed_unit_ball_boundary_chart k i s).source) :
    ‖(split_at_coordinate i x.1).1‖ < 1 := by
  let ui := split_at_coordinate i x.1
  have hx0 : 0 < closed_unit_ball_boundary_sign s * x.1 i := by
    -- Membership in the explicit boundary source is exactly the signed-coordinate positivity
    -- condition built into Lee's chart.
    simpa [closed_unit_ball_boundary_chart] using hx
  have hnorm : ‖x.1‖ ≤ 1 := by
    -- Closed-ball membership is the ambient norm bound.
    simpa [Metric.closedBall, Metric.mem_closedBall, dist_eq_norm] using x.2
  have hnorm_sq : ‖x.1‖ ^ 2 ≤ 1 := by
    -- Square the closed-ball norm bound to match the split-norm identity.
    nlinarith [hnorm, norm_nonneg x.1]
  have hsplit :
      ‖x.1‖ ^ 2 = ‖ui.1‖ ^ 2 + ui.2 ^ 2 := by
    -- Splitting off the distinguished coordinate separates the ambient norm into tail and normal
    -- components.
    simpa [ui] using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x.1)
  have hcoord_ne : ui.2 ≠ 0 := by
    -- The signed-coordinate positivity says the distinguished split coordinate is nonzero.
    cases s with
    | false =>
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0.ne'
    | true =>
        simpa [ui, split_at_coordinate_snd_apply, closed_unit_ball_boundary_sign] using hx0.ne'
  have hcoord_sq_pos : 0 < ui.2 ^ 2 := by
    exact sq_pos_iff.mpr hcoord_ne
  have htail_sq_lt : ‖ui.1‖ ^ 2 < 1 := by
    -- A nonzero distinguished coordinate forces the remaining coordinates strictly inside the unit
    -- ball.
    nlinarith [hnorm_sq, hsplit, hcoord_sq_pos]
  -- Taking square roots of the strict squared-norm bound gives the required open-ball inequality.
  nlinarith [htail_sq_lt, norm_nonneg ui.1]

/-- Helper for Problem 2-4: forgetting one split coordinate cannot increase the Euclidean norm. -/
lemma split_at_coordinate_fst_norm_le {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖(split_at_coordinate i x).1‖ ≤ ‖x‖ := by
  have hsq :
      ‖(split_at_coordinate i x).1‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hdecomp :
        ‖x‖ ^ 2 =
          ‖(split_at_coordinate i x).1‖ ^ 2 + (split_at_coordinate i x).2 ^ 2 := by
      -- The split norm identity isolates the discarded coordinate as a nonnegative error term.
      simpa using split_at_coordinate_symm_norm_sq i (split_at_coordinate i x)
    nlinarith [hdecomp, sq_nonneg ((split_at_coordinate i x).2)]
  -- Squared-norm monotonicity upgrades to the usual norm inequality because both norms are
  -- nonnegative.
  nlinarith [hsq, norm_nonneg ((split_at_coordinate i x).1), norm_nonneg x]

/-- Helper for Problem 2-4: points in Lee's interior center chart automatically satisfy the
open-unit-ball inequality needed by every boundary forward chart. -/
lemma closed_unit_ball_center_chart_source_tail_norm_lt_one {k : ℕ}
    (i : Fin (k + 2))
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : x ∈ (closed_unit_ball_center_chart k).source) :
    ‖(split_at_coordinate i x.1).1‖ < 1 := by
  have hcenter : ‖x.1‖ < (1 : ℝ) / 2 := by
    -- The packaged center chart source is exactly Lee's radius-`1/2` interior patch.
    have hx' := hx
    rw [closed_unit_ball_center_chart, OpenPartialHomeomorph.trans_source] at hx'
    simpa [closed_unit_ball_center_chart_source] using hx'.1
  have htail : ‖(split_at_coordinate i x.1).1‖ ≤ ‖x.1‖ :=
    split_at_coordinate_fst_norm_le i x.1
  -- The retained split coordinates stay strictly inside the unit ball because the whole point lies
  -- in the smaller interior patch.
  linarith

/-- Helper for Problem 2-4: on its source, the totalized boundary chart is exactly Lee's explicit
forward graphing map. -/
lemma closed_unit_ball_boundary_chart_apply_of_mem_source {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1}
    (hx : x ∈ (closed_unit_ball_boundary_chart k i s).source) :
    closed_unit_ball_boundary_chart k i s x =
      closed_unit_ball_boundary_chart_forward k i s x
        (closed_unit_ball_boundary_chart_source_pos i s
          (by simpa [closed_unit_ball_boundary_chart] using hx)) := by
  have hx0 : 0 < closed_unit_ball_boundary_sign s * x.1 i := by
    -- Unfold the packaged source back to the explicit signed-coordinate positivity condition.
    simpa [closed_unit_ball_boundary_chart] using hx
  have hproof :
      closed_unit_ball_boundary_chart_source_pos i s
          (by simpa [closed_unit_ball_boundary_chart] using hx) =
        hx0 := by
    exact Subsingleton.elim _ _
  -- On the actual source branch, the defining `dite` of the chart chooses the forward formula.
  simp [closed_unit_ball_boundary_chart, hx0]

/-- Helper for Problem 2-4: on its target, the totalized boundary-chart inverse is exactly Lee's
explicit graphing inverse. -/
lemma closed_unit_ball_boundary_chart_symm_apply_of_mem_target {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {z : EuclideanHalfSpace (k + 2)}
    (hz : z ∈ (closed_unit_ball_boundary_chart k i s).target) :
    (closed_unit_ball_boundary_chart k i s).symm z =
      ⟨closed_unit_ball_boundary_chart_inverse k i s z,
        closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s
          (by simpa [closed_unit_ball_boundary_chart] using hz)⟩ := by
  have hz0 : z ∈ closed_unit_ball_boundary_chart_target k := by
    -- Unfold the packaged target back to the explicit common hypograph target.
    simpa [closed_unit_ball_boundary_chart] using hz
  -- On the actual target branch, the defining `dite` of the inverse chooses the graphing formula.
  simp [closed_unit_ball_boundary_chart, hz0]

variable (n : ℕ)

local notation "B" => Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Helper for Problem 2-4: on the target of an extended boundary chart, the underlying ambient
point of the inverse chart is exactly Lee's explicit inverse extension formula. -/
lemma closed_unit_ball_boundary_chart_symm_extend_val_eq_inverse_extend {k : ℕ}
    (i : Fin (k + 2)) (s : Bool)
    {z : EuclideanSpace ℝ (Fin (k + 2))}
    (hz : z ∈ ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).target) :
    ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1) =
      closed_unit_ball_boundary_chart_inverse_extend k i s z := by
  rw [OpenPartialHomeomorph.extend_target] at hz
  have hz_target : (𝓡∂ (k + 2)).symm z ∈ (closed_unit_ball_boundary_chart k i s).target := hz.1
  have hz_model : z ∈ (𝓡∂ (k + 2)).target := by
    simpa [ModelWithCorners.target_eq] using hz.2
  have hsymm :
      (closed_unit_ball_boundary_chart k i s).symm ((𝓡∂ (k + 2)).symm z) =
        ⟨closed_unit_ball_boundary_chart_inverse k i s ((𝓡∂ (k + 2)).symm z),
          closed_unit_ball_boundary_chart_inverse_mem_closedBall (k := k) i s
            (by simpa [closed_unit_ball_boundary_chart] using hz_target)⟩ :=
    closed_unit_ball_boundary_chart_symm_apply_of_mem_target (k := k) i s hz_target
  have hval :
      ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1) =
        closed_unit_ball_boundary_chart_inverse k i s ((𝓡∂ (k + 2)).symm z) := by
    -- The extended inverse is definitionally the chart inverse followed by the model inverse.
    simpa [OpenPartialHomeomorph.extend_coe_symm] using congrArg Subtype.val hsymm
  calc
    ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1)
        = closed_unit_ball_boundary_chart_inverse_extend k i s (((𝓡∂ (k + 2)).symm z).1) := by
            rw [hval, closed_unit_ball_boundary_chart_inverse_eq_extend]
    _ = closed_unit_ball_boundary_chart_inverse_extend k i s z := by
      rw [modelWithCornersEuclideanHalfSpace_symm_val k hz_model]

/-- Helper for Problem 2-4: on the transported center-to-boundary overlap source, Lee's mixed
transition is exactly the ambient forward boundary extension after subtracting the fixed center
point. -/
lemma closed_unit_ball_center_boundary_transition_eqOn_forward_extend (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    Set.EqOn
      (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
        ((𝓡∂ (k + 2)) ∘
          ((closed_unit_ball_center_chart k).symm.trans
            (closed_unit_ball_boundary_chart k i s)) ∘
          (𝓡∂ (k + 2)).symm) z)
      (fun z ↦
        closed_unit_ball_boundary_chart_forward_extend k i s
          (z - (closed_unit_ball_center_target_point k).1))
      (((𝓡∂ (k + 2)).symm ⁻¹'
        ((closed_unit_ball_center_chart k).symm.trans
          (closed_unit_ball_boundary_chart k i s)).source) ∩ Set.range (𝓡∂ (k + 2))) := by
  intro z hz
  rcases hz with ⟨hz_source, hz_range⟩
  rw [OpenPartialHomeomorph.trans_source] at hz_source
  have hz_center_target :
      z ∈ ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).target := by
    -- The transported overlap source already records that `z` lies in the extended center target.
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hz_source.1, hz_range⟩
  have hx_boundary_source :
      ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z ∈
        (closed_unit_ball_boundary_chart k i s).source := by
    -- The second overlap condition says the recovered closed-ball point lies in the chosen signed
    -- boundary source patch.
    simpa [OpenPartialHomeomorph.extend_coe_symm] using hz_source.2
  have hforward :
      (closed_unit_ball_boundary_chart k i s)
          (((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z) =
        closed_unit_ball_boundary_chart_forward k i s
          (((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z)
          (closed_unit_ball_boundary_chart_source_pos i s
            (by simpa [closed_unit_ball_boundary_chart] using hx_boundary_source)) := by
    -- On the actual source branch, the totalized boundary chart is Lee's explicit forward graph.
    simpa using
      closed_unit_ball_boundary_chart_apply_of_mem_source (k := k) i s hx_boundary_source
  have hforward_val :
      ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2)))
          (((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z) =
        closed_unit_ball_boundary_chart_forward_extend k i s
          ((((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z).1) := by
    -- Applying the model inclusion just forgets the half-space proof on the explicit forward
    -- chart value.
    simpa [OpenPartialHomeomorph.extend_coe, closed_unit_ball_boundary_chart_forward] using
      congrArg (fun w : EuclideanHalfSpace (k + 2) ↦ w.1) hforward
  -- Route correction: rewrite through the extended charts first, then substitute the explicit
  -- center inverse formula instead of trying to normalize the transported composition directly.
  calc
    ((𝓡∂ (k + 2)) ∘
        ((closed_unit_ball_center_chart k).symm.trans
          (closed_unit_ball_boundary_chart k i s)) ∘
        (𝓡∂ (k + 2)).symm) z
      = ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2)))
          (((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z) := by
            rfl
    _ = closed_unit_ball_boundary_chart_forward_extend k i s
          ((((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z).1) :=
            hforward_val
    _ = closed_unit_ball_boundary_chart_forward_extend k i s
          (z - (closed_unit_ball_center_target_point k).1) := by
            rw [closed_unit_ball_center_chart_symm_extend_val_eq_sub k hz_center_target]

/-- Helper for Problem 2-4: on the transported boundary-to-center overlap source, Lee's mixed
transition is exactly the ambient boundary inverse extension followed by the fixed center
translation. -/
lemma closed_unit_ball_boundary_center_transition_eqOn_inverse_extend (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) :
    Set.EqOn
      (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
        ((𝓡∂ (k + 2)) ∘
          ((closed_unit_ball_boundary_chart k i s).symm.trans
            (closed_unit_ball_center_chart k)) ∘
          (𝓡∂ (k + 2)).symm) z)
      (fun z ↦
        closed_unit_ball_boundary_chart_inverse_extend k i s z +
          (closed_unit_ball_center_target_point k).1)
      (((𝓡∂ (k + 2)).symm ⁻¹'
        ((closed_unit_ball_boundary_chart k i s).symm.trans
          (closed_unit_ball_center_chart k)).source) ∩ Set.range (𝓡∂ (k + 2))) := by
  intro z hz
  rcases hz with ⟨hz_source, hz_range⟩
  rw [OpenPartialHomeomorph.trans_source] at hz_source
  have hz_boundary_target :
      z ∈ ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).target := by
    -- The transported overlap source already records that `z` lies in the extended boundary
    -- target.
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hz_source.1, hz_range⟩
  have hx_center_source :
      ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z ∈
        (closed_unit_ball_center_chart k).source := by
    -- The recovered closed-ball point lies in the interior center patch on this mixed overlap.
    simpa [OpenPartialHomeomorph.extend_coe_symm] using hz_source.2
  -- Normalize the transported composition to the extended center chart, then rewrite the inverse
  -- point by Lee's explicit boundary inverse formula.
  calc
    ((𝓡∂ (k + 2)) ∘
        ((closed_unit_ball_boundary_chart k i s).symm.trans
          (closed_unit_ball_center_chart k)) ∘
        (𝓡∂ (k + 2)).symm) z
      = ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2)))
          (((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z) := by
            rfl
    _ = ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1) +
          (closed_unit_ball_center_target_point k).1 := by
            rw [closed_unit_ball_center_chart_extend_eq_add k hx_center_source]
    _ = closed_unit_ball_boundary_chart_inverse_extend k i s z +
          (closed_unit_ball_center_target_point k).1 := by
            rw [closed_unit_ball_boundary_chart_symm_extend_val_eq_inverse_extend
              (k := k) i s hz_boundary_target]

/-- Helper for Problem 2-4: on the transported boundary-to-boundary overlap source, Lee's mixed
transition is exactly the ambient forward extension after the ambient inverse extension of the
first boundary chart. -/
lemma closed_unit_ball_boundary_boundary_transition_eqOn_forward_inverse (k : ℕ)
    (i : Fin (k + 2)) (s : Bool) (j : Fin (k + 2)) (t : Bool) :
    Set.EqOn
      (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
        ((𝓡∂ (k + 2)) ∘
          ((closed_unit_ball_boundary_chart k i s).symm.trans
            (closed_unit_ball_boundary_chart k j t)) ∘
          (𝓡∂ (k + 2)).symm) z)
      (fun z ↦
        closed_unit_ball_boundary_chart_forward_extend k j t
          (closed_unit_ball_boundary_chart_inverse_extend k i s z))
      (((𝓡∂ (k + 2)).symm ⁻¹'
        ((closed_unit_ball_boundary_chart k i s).symm.trans
          (closed_unit_ball_boundary_chart k j t)).source) ∩ Set.range (𝓡∂ (k + 2))) := by
  intro z hz
  rcases hz with ⟨hz_source, hz_range⟩
  rw [OpenPartialHomeomorph.trans_source] at hz_source
  have hz_boundary_target :
      z ∈ ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).target := by
    -- The transported overlap source already records that `z` lies in the extended target of the
    -- first boundary chart.
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hz_source.1, hz_range⟩
  have hx_boundary_source :
      ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z ∈
        (closed_unit_ball_boundary_chart k j t).source := by
    -- After applying the first inverse chart, the point lies in the source of the second boundary
    -- chart on the overlap.
    simpa [OpenPartialHomeomorph.extend_coe_symm] using hz_source.2
  have hforward :
      (closed_unit_ball_boundary_chart k j t)
          (((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z) =
        closed_unit_ball_boundary_chart_forward k j t
          (((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z)
          (closed_unit_ball_boundary_chart_source_pos j t
            (by simpa [closed_unit_ball_boundary_chart] using hx_boundary_source)) := by
    -- On the actual source branch, the second boundary chart is Lee's explicit forward graph.
    simpa using
      closed_unit_ball_boundary_chart_apply_of_mem_source (k := k) j t hx_boundary_source
  have hforward_val :
      ((closed_unit_ball_boundary_chart k j t).extend (𝓡∂ (k + 2)))
          (((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z) =
        closed_unit_ball_boundary_chart_forward_extend k j t
          ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1) := by
    -- Applying the model inclusion again just forgets the half-space proof on the explicit
    -- forward chart value.
    simpa [OpenPartialHomeomorph.extend_coe, closed_unit_ball_boundary_chart_forward] using
      congrArg (fun w : EuclideanHalfSpace (k + 2) ↦ w.1) hforward
  -- Normalize first through the two extended charts, then substitute the explicit inverse formula
  -- of the first boundary chart.
  calc
    ((𝓡∂ (k + 2)) ∘
        ((closed_unit_ball_boundary_chart k i s).symm.trans
          (closed_unit_ball_boundary_chart k j t)) ∘
        (𝓡∂ (k + 2)).symm) z
      = ((closed_unit_ball_boundary_chart k j t).extend (𝓡∂ (k + 2)))
          (((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z) := by
            rfl
    _ = closed_unit_ball_boundary_chart_forward_extend k j t
          ((((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z).1) :=
            hforward_val
    _ = closed_unit_ball_boundary_chart_forward_extend k j t
          (closed_unit_ball_boundary_chart_inverse_extend k i s z) := by
            rw [closed_unit_ball_boundary_chart_symm_extend_val_eq_inverse_extend
              (k := k) i s hz_boundary_target]

/-- Helper for Problem 2-4: the fixed center-plus-signed-boundary atlas is smooth in dimensions
at least two once each chart transition is reduced to its explicit ambient formula. -/
lemma closed_unit_ball_higher_dimensional_isManifold_infty (k : ℕ) :
    let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
      closed_unit_ball_fixed_chartedSpace k
    IsManifold (𝓡∂ (k + 2)) (⊤ : WithTop ℕ∞)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) := by
  let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    closed_unit_ball_fixed_chartedSpace k
  refine isManifold_of_contDiffOn (I := 𝓡∂ (k + 2)) (n := (⊤ : WithTop ℕ∞))
    (M := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) ?_
  intro e e' he he'
  have he_fixed : e ∈ closed_unit_ball_fixed_atlas k := by
    simpa [closed_unit_ball_fixed_chartedSpace] using he
  have he'_fixed : e' ∈ closed_unit_ball_fixed_atlas k := by
    simpa [closed_unit_ball_fixed_chartedSpace] using he'
  rw [closed_unit_ball_fixed_atlas, Set.mem_insert_iff, Set.mem_range] at he_fixed he'_fixed
  rcases he_fixed with rfl | ⟨⟨i, s⟩, rfl⟩
  · rcases he'_fixed with rfl | ⟨⟨i, s⟩, rfl⟩
    · -- The center chart transition with itself is already a standard pregroupoid element.
      exact (mem_groupoid_of_pregroupoid.mpr
        (symm_trans_mem_contDiffGroupoid (closed_unit_ball_center_chart k))).1
    · let S : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
        ((𝓡∂ (k + 2)).symm ⁻¹'
          ((closed_unit_ball_center_chart k).symm.trans
            (closed_unit_ball_boundary_chart k i s)).source) ∩
          Set.range (𝓡∂ (k + 2))
      have hsub :
          ContDiff ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              z - (closed_unit_ball_center_target_point k).1) := by
        -- The interior chart is the affine translation by the fixed center point.
        fun_prop
      have hsmooth :
          ContDiffOn ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              closed_unit_ball_boundary_chart_forward_extend k i s
                (z - (closed_unit_ball_center_target_point k).1))
            S := by
        -- On the mixed overlap source, subtracting the center point lands in the boundary
        -- forward-extension smoothness domain.
        refine (closed_unit_ball_boundary_chart_forward_extend_contDiffOn k i s).comp
          hsub.contDiffOn ?_
        intro z hz
        dsimp [S] at hz
        rcases hz with ⟨hz_source, hz_range⟩
        have hz_center_target :
            z ∈ ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).target := by
          rw [OpenPartialHomeomorph.extend_target]
          exact ⟨hz_source.1, hz_range⟩
        have hx_boundary_source :
            ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z ∈
              (closed_unit_ball_boundary_chart k i s).source := by
          simpa [OpenPartialHomeomorph.extend_coe_symm] using hz_source.2
        have htail :
            ‖(split_at_coordinate i
                ((((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z).1)).1‖ < 1 :=
          closed_unit_ball_boundary_chart_source_tail_norm_lt_one (i := i) (s := s)
            hx_boundary_source
        rw [closed_unit_ball_center_chart_symm_extend_val_eq_sub k hz_center_target] at htail
        exact htail
      -- Route correction: replace the transported mixed transition by the explicit ambient
      -- forward-extension formula before using the existing Euclidean smoothness lemma.
      change ContDiffOn ℝ ω
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ((𝓡∂ (k + 2)) ∘
            ((closed_unit_ball_center_chart k).symm.trans
              (closed_unit_ball_boundary_chart k i s)) ∘
            (𝓡∂ (k + 2)).symm) z)
        S
      exact hsmooth.congr
        (closed_unit_ball_center_boundary_transition_eqOn_forward_extend k i s)
  · rcases he'_fixed with rfl | ⟨⟨j, t⟩, rfl⟩
    · let S : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
        ((𝓡∂ (k + 2)).symm ⁻¹'
          ((closed_unit_ball_boundary_chart k i s).symm.trans
            (closed_unit_ball_center_chart k)).source) ∩
          Set.range (𝓡∂ (k + 2))
      have hadd :
          ContDiff ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              z + (closed_unit_ball_center_target_point k).1) := by
        -- Returning to the center chart is an affine translation after the boundary inverse.
        fun_prop
      have hinv :
          ContDiffOn ℝ ω
            (closed_unit_ball_boundary_chart_inverse_extend k i s) S := by
        -- On the mixed overlap source, the transported boundary target condition gives the
        -- inverse-extension smoothness domain.
        refine (closed_unit_ball_boundary_chart_inverse_extend_contDiffOn k i s).mono ?_
        intro z hz
        dsimp [S] at hz
        rcases hz with ⟨hz_source, hz_range⟩
        have hz_model : z ∈ (𝓡∂ (k + 2)).target := by
          simpa [ModelWithCorners.target_eq] using hz_range
        have htail_model :
            ‖(split_at_coordinate (0 : Fin (k + 2))
                (((𝓡∂ (k + 2)).symm z).1)).1‖ < 1 :=
          closed_unit_ball_boundary_chart_target_mem_unit_ball hz_source.1
        simpa [modelWithCornersEuclideanHalfSpace_symm_val k hz_model] using htail_model
      have hsmooth :
          ContDiffOn ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              closed_unit_ball_boundary_chart_inverse_extend k i s z +
                (closed_unit_ball_center_target_point k).1)
            S :=
        hadd.comp_contDiffOn hinv
      change ContDiffOn ℝ ω
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ((𝓡∂ (k + 2)) ∘
            ((closed_unit_ball_boundary_chart k i s).symm.trans
              (closed_unit_ball_center_chart k)) ∘
            (𝓡∂ (k + 2)).symm) z)
        S
      exact hsmooth.congr
        (closed_unit_ball_boundary_center_transition_eqOn_inverse_extend k i s)
    · let S : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
        ((𝓡∂ (k + 2)).symm ⁻¹'
          ((closed_unit_ball_boundary_chart k i s).symm.trans
            (closed_unit_ball_boundary_chart k j t)).source) ∩
          Set.range (𝓡∂ (k + 2))
      have hinv :
          ContDiffOn ℝ ω
            (closed_unit_ball_boundary_chart_inverse_extend k i s) S := by
        -- The first boundary target condition places `z` in the inverse-extension smoothness
        -- domain.
        refine (closed_unit_ball_boundary_chart_inverse_extend_contDiffOn k i s).mono ?_
        intro z hz
        dsimp [S] at hz
        rcases hz with ⟨hz_source, hz_range⟩
        have hz_model : z ∈ (𝓡∂ (k + 2)).target := by
          simpa [ModelWithCorners.target_eq] using hz_range
        have htail_model :
            ‖(split_at_coordinate (0 : Fin (k + 2))
                (((𝓡∂ (k + 2)).symm z).1)).1‖ < 1 :=
          closed_unit_ball_boundary_chart_target_mem_unit_ball hz_source.1
        simpa [modelWithCornersEuclideanHalfSpace_symm_val k hz_model] using htail_model
      have hsmooth :
          ContDiffOn ℝ ω
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              closed_unit_ball_boundary_chart_forward_extend k j t
                (closed_unit_ball_boundary_chart_inverse_extend k i s z))
            S := by
        -- On the mixed overlap source, the boundary inverse lands in the second boundary
        -- forward-extension smoothness domain.
        refine (closed_unit_ball_boundary_chart_forward_extend_contDiffOn k j t).comp hinv ?_
        intro z hz
        dsimp [S] at hz
        rcases hz with ⟨hz_source, hz_range⟩
        have hx_boundary_source :
            ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).symm z ∈
              (closed_unit_ball_boundary_chart k j t).source := by
          simpa [OpenPartialHomeomorph.extend_coe_symm] using hz_source.2
        have hz_boundary_target :
            z ∈ ((closed_unit_ball_boundary_chart k i s).extend (𝓡∂ (k + 2))).target := by
          rw [OpenPartialHomeomorph.extend_target]
          exact ⟨hz_source.1, hz_range⟩
        have htail :
            ‖(split_at_coordinate j
                ((((closed_unit_ball_boundary_chart k i s).extend
                    (𝓡∂ (k + 2))).symm z).1)).1‖ < 1 :=
          closed_unit_ball_boundary_chart_source_tail_norm_lt_one (i := j) (s := t)
            hx_boundary_source
        rw [closed_unit_ball_boundary_chart_symm_extend_val_eq_inverse_extend
          (k := k) i s hz_boundary_target] at htail
        exact htail
      change ContDiffOn ℝ ω
        (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
          ((𝓡∂ (k + 2)) ∘
            ((closed_unit_ball_boundary_chart k i s).symm.trans
              (closed_unit_ball_boundary_chart k j t)) ∘
            (𝓡∂ (k + 2)).symm) z)
        S
      exact hsmooth.congr
        (closed_unit_ball_boundary_boundary_transition_eqOn_forward_inverse
          k i s j t)

/-- Helper for Problem 2-4: with the fixed higher-dimensional atlas installed, the ambient
subtype inclusion is smooth because each chosen local chart writes it as either an affine map or
Lee's explicit boundary inverse. -/
lemma closed_unit_ball_higher_dimensional_inclusion_contMDiff (k : ℕ) :
    let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
      closed_unit_ball_fixed_chartedSpace k
    let _ :
        IsManifold (𝓡∂ (k + 2)) (⊤ : WithTop ℕ∞)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
      closed_unit_ball_higher_dimensional_isManifold_infty k
    ContMDiff (𝓡∂ (k + 2)) (𝓡 (k + 2)) ∞
      ((↑) : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 →
        EuclideanSpace ℝ (Fin (k + 2))) := by
  let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    closed_unit_ball_fixed_chartedSpace k
  let _ :
      IsManifold (𝓡∂ (k + 2)) (⊤ : WithTop ℕ∞)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    closed_unit_ball_higher_dimensional_isManifold_infty k
  dsimp
  intro x
  rw [contMDiffAt_iff_source_of_mem_source
    (I := 𝓡∂ (k + 2)) (I' := 𝓡 (k + 2))
    (x := x) (x' := x)
    (f := ((↑) : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 →
      EuclideanSpace ℝ (Fin (k + 2))))
    (mem_closed_unit_ball_chartAtLocal_source k x)]
  by_cases hx : ‖x.1‖ < (1 : ℝ) / 2
  · have hchart : chartAt (EuclideanHalfSpace (k + 2)) x = closed_unit_ball_center_chart k := by
      simpa [closed_unit_ball_fixed_chartedSpace] using
        closed_unit_ball_chartAtLocal_of_norm_lt k x hx
    rw [extChartAt, hchart, contMDiffWithinAt_iff_contDiffWithinAt]
    have hx_source : x ∈ (closed_unit_ball_center_chart k).source := by
      simpa [closed_unit_ball_chartAtLocal_of_norm_lt k x hx] using
        mem_closed_unit_ball_chartAtLocal_source k x
    let y : EuclideanSpace ℝ (Fin (k + 2)) :=
      ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))) x
    have hy_target :
        y ∈ ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).target := by
      have hx_source_extend :
          x ∈ ((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).source := by
        rwa [OpenPartialHomeomorph.extend_source]
      -- The chosen center chart sends `x` into its extended target.
      simpa [y] using
        (((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).map_source hx_source_extend)
    have hy_range : y ∈ Set.range (𝓡∂ (k + 2)) := by
      have hy_target' := hy_target
      rw [OpenPartialHomeomorph.extend_target] at hy_target'
      exact hy_target'.2
    have hEq :
        Filter.EventuallyEq
          (nhdsWithin y (Set.range (𝓡∂ (k + 2))))
          (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
            ((((closed_unit_ball_center_chart k).extend (𝓡∂ (k + 2))).symm z).1))
          (fun z ↦ z - (closed_unit_ball_center_target_point k).1) := by
      -- Near the chosen center-chart point, the inverse chart is literally subtraction of the
      -- fixed center point.
      filter_upwards
        [(closed_unit_ball_center_chart k).extend_target_mem_nhdsWithin
          (I := 𝓡∂ (k + 2)) hx_source] with z hz
      exact closed_unit_ball_center_chart_symm_extend_val_eq_sub k hz
    have haff :
        ContDiff ℝ ∞
          (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
            z - (closed_unit_ball_center_target_point k).1) := by
      -- The center chart expression is affine on the ambient Euclidean space.
      fun_prop
    simpa [Function.comp, y] using
      (haff.contDiffWithinAt.congr_of_eventuallyEq_of_mem hEq hy_range)
  · let is := (closed_unit_ball_boundary_choice_data k x hx).1
    have hchart :
        chartAt (EuclideanHalfSpace (k + 2)) x =
          closed_unit_ball_boundary_chart k is.1 is.2 := by
      simpa [closed_unit_ball_fixed_chartedSpace, is] using
        closed_unit_ball_chartAtLocal_of_not_norm_lt k x hx
    rw [extChartAt, hchart, contMDiffWithinAt_iff_contDiffWithinAt]
    have hx_source : x ∈ (closed_unit_ball_boundary_chart k is.1 is.2).source := by
      -- On the boundary branch, the selected chart is the chosen signed boundary chart.
      simpa [is, closed_unit_ball_chartAtLocal_of_not_norm_lt k x hx] using
        mem_closed_unit_ball_chartAtLocal_source k x
    let y : EuclideanSpace ℝ (Fin (k + 2)) :=
      ((closed_unit_ball_boundary_chart k is.1 is.2).extend (𝓡∂ (k + 2))) x
    have hy_target :
        y ∈ ((closed_unit_ball_boundary_chart k is.1 is.2).extend
          (𝓡∂ (k + 2))).target := by
      have hx_source_extend :
          x ∈ ((closed_unit_ball_boundary_chart k is.1 is.2).extend
            (𝓡∂ (k + 2))).source := by
        rwa [OpenPartialHomeomorph.extend_source]
      -- The chosen boundary chart sends `x` into its extended target.
      simpa [y] using
        (((closed_unit_ball_boundary_chart k is.1 is.2).extend
          (𝓡∂ (k + 2))).map_source hx_source_extend)
    have hy_target' := hy_target
    rw [OpenPartialHomeomorph.extend_target] at hy_target'
    have hy_range : y ∈ Set.range (𝓡∂ (k + 2)) := hy_target'.2
    have hy_model : y ∈ (𝓡∂ (k + 2)).target := by
      simpa [ModelWithCorners.target_eq] using hy_range
    have htail_model :
        ‖(split_at_coordinate (0 : Fin (k + 2))
            (((𝓡∂ (k + 2)).symm y).1)).1‖ < 1 :=
      closed_unit_ball_boundary_chart_target_mem_unit_ball hy_target'.1
    have htail :
        ‖(split_at_coordinate (0 : Fin (k + 2)) y).1‖ < 1 := by
      simpa [modelWithCornersEuclideanHalfSpace_symm_val k hy_model] using htail_model
    let T : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
      {z | ‖(split_at_coordinate (0 : Fin (k + 2)) z).1‖ < 1}
    have hT_mem :
        T ∈ nhdsWithin y (Set.range (𝓡∂ (k + 2))) := by
      have hcont :
          Continuous
            (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
              ‖(split_at_coordinate (0 : Fin (k + 2)) z).1‖) :=
        continuous_norm.comp
          (continuous_fst.comp (split_at_coordinate_continuous (0 : Fin (k + 2))))
      -- The inverse-extension smoothness domain is open and contains the chosen boundary-chart
      -- point.
      exact mem_nhdsWithin_of_mem_nhds ((isOpen_lt hcont continuous_const).mem_nhds htail)
    have hsmooth :
        ContDiffWithinAt ℝ ∞
          (closed_unit_ball_boundary_chart_inverse_extend k is.1 is.2)
          (Set.range (𝓡∂ (k + 2))) y := by
      -- The explicit boundary inverse is smooth on an ambient open neighborhood of `y`, hence also
      -- within `range (𝓡∂ _)` at `y`.
      have hsmoothT :
          ContDiffWithinAt ℝ ∞
            (closed_unit_ball_boundary_chart_inverse_extend k is.1 is.2) T y := by
        simpa [T] using
          ((closed_unit_ball_boundary_chart_inverse_extend_contDiffOn k is.1 is.2).of_le
            (by simp) y htail)
      exact hsmoothT.mono_of_mem_nhdsWithin hT_mem
    have hEq :
        Filter.EventuallyEq
          (nhdsWithin y (Set.range (𝓡∂ (k + 2))))
          (fun z : EuclideanSpace ℝ (Fin (k + 2)) ↦
            ((((closed_unit_ball_boundary_chart k is.1 is.2).extend
                (𝓡∂ (k + 2))).symm z).1))
          (closed_unit_ball_boundary_chart_inverse_extend k is.1 is.2) := by
      -- Near the chosen boundary-chart point, the inverse chart is literally Lee's explicit
      -- inverse extension.
      filter_upwards
        [(closed_unit_ball_boundary_chart k is.1 is.2).extend_target_mem_nhdsWithin
          (I := 𝓡∂ (k + 2)) hx_source] with z hz
      exact closed_unit_ball_boundary_chart_symm_extend_val_eq_inverse_extend
        (k := k) is.1 is.2 hz
    simpa [Function.comp, y] using
      (hsmooth.congr_of_eventuallyEq_of_mem hEq hy_range)

/-- Helper for Problem 2-4: in dimensions at least two, Lee's closed-ball atlas should give a
smooth manifold-with-boundary structure. -/
@[reducible] noncomputable def closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary
    (k : ℕ) :
    SmoothManifoldWithBoundary (k + 2)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
  { toTopologicalManifoldWithBoundary :=
      { toT2Space := inferInstance
        toSecondCountableTopology := inferInstance
        toChartedSpace := by
          -- The higher-dimensional boundary model is definitionally the Euclidean half-space.
          simpa [LeeBoundaryModelSpace] using closed_unit_ball_fixed_chartedSpace k
        toIsManifold := by
          -- The smooth atlas immediately yields the underlying `C^0` structure.
          let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
            closed_unit_ball_fixed_chartedSpace k
          simpa [leeBoundaryModelWithCorners] using
            (closed_unit_ball_higher_dimensional_isManifold_infty k).of_le
              (by simp : (0 : ℕ∞ω) ≤ (⊤ : WithTop ℕ∞)) }
    smooth := by
      -- The fixed center-plus-boundary atlas is already smooth.
      let _ : ChartedSpace (EuclideanHalfSpace (k + 2))
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
        closed_unit_ball_fixed_chartedSpace k
      simpa [leeBoundaryModelWithCorners] using
        closed_unit_ball_higher_dimensional_isManifold_infty k }

/- Problem 2-4 is `source-facing`: the primitive data are a manifold-with-boundary structure on
the closed unit ball, while smoothness of the ambient inclusion is derived API. The statement
should therefore use the chapter's owner `SmoothManifoldWithBoundary n` rather than quantify over
separate `ChartedSpace` and `IsManifold` witnesses. The inclusion remains a derived
`ContMDiff` statement for the subtype map. -/
/-- Problem 2-4: the closed unit ball in `ℝ^n` admits a smooth manifold-with-boundary structure
for which its inclusion into the ambient Euclidean space is smooth. -/
theorem closedUnitBall_exists_smoothManifoldWithBoundary :
    ∃ instSmooth : SmoothManifoldWithBoundary n B,
      let _ : SmoothManifoldWithBoundary n B := instSmooth
      ContMDiff (leeBoundaryModelWithCorners n) (𝓡 n) ∞
        ((↑) : B → EuclideanSpace ℝ (Fin n)) := by
  -- We split off the genuinely different zero-dimensional case first.
  cases n with
  | zero =>
      refine ⟨closed_unit_ball_zero_smoothManifoldWithBoundary, ?_⟩
      simpa using closed_unit_ball_zero_inclusion_contMDiff
  | succ m =>
      -- We next separate the transported interval case from the genuinely higher-dimensional atlas.
      cases m with
      | zero =>
          refine ⟨closed_unit_ball_one_smoothManifoldWithBoundary, ?_⟩
          -- The one-dimensional case is the transported interval manifold, so the inclusion
          -- factors through the standard smooth interval inclusion.
          simpa using closed_unit_ball_one_inclusion_contMDiff
      | succ k =>
          refine ⟨closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k, ?_⟩
          letI := closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k
          -- The higher-dimensional case reuses the fixed Lee atlas and the chartwise inclusion
          -- formula proved above.
          simpa [leeBoundaryModelWithCorners] using
            closed_unit_ball_higher_dimensional_inclusion_contMDiff k

end
