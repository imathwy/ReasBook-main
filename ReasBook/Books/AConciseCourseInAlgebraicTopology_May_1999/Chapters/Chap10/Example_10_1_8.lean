import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_8.Comparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_8.GraphRealization
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3

universe u v w

open scoped unitInterval

variable {X₀ : Type u} {J : Type v}

/-- If a quotient map identifies exactly the classes of a setoid, then that setoid quotient is
homeomorphic to the codomain. -/
private noncomputable def quotientHomeomorphOfRelIff
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) :
    Quotient r ≃ₜ Y := by
  have hker : Setoid.ker q = r := by
    ext x y
    exact (hrel x y).symm
  -- Replace the explicit setoid by the kernel relation of the quotient map.
  exact hker ▸ Topology.IsQuotientMap.homeomorph hq

/-- If a CW complex has no cells above dimension `1`, then its canonical skeleton already
stabilizes at degree `1`. -/
private theorem dimLE_one_of_isEmpty_higherCells
    {X : Type w} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (hcell :
      ∀ n : ℕ, 1 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    Topology.RelCWComplex.dimLE (Set.univ : Set X) 1 := by
  ext x
  constructor
  · intro hx
    simp
  · intro _
    -- Start from the union of all skeleta and isolate the cell containing `x`.
    have hxUnion : x ∈ ⋃ n : ℕ, Topology.CWComplex.skeleton (Set.univ : Set X) n := by
      simp [Topology.CWComplex.iUnion_skeleton_eq_complex]
    rcases Set.mem_iUnion.mp hxUnion with ⟨n, hn⟩
    rcases (Topology.CWComplex.exists_mem_openCell_of_mem_skeleton).mp hn with ⟨m, hm, j, hj⟩
    -- Any containing cell must have dimension at most `1`.
    have hm1 : m ≤ 1 := by
      by_contra hm1
      exact (hcell m (lt_of_not_ge hm1)).false j
    have hxSkelM : x ∈ Topology.CWComplex.skeleton (Set.univ : Set X) m :=
      Topology.CWComplex.openCell_subset_skeleton m j hj
    exact Topology.CWComplex.skeleton_mono
      (show (m : ℕ∞) ≤ 1 by exact_mod_cast hm1) hxSkelM

/-- Helper for Example 10.1.8: collapsing each edge endpoint to its incident vertex defines an
`Option X₀`-valued invariant on the graph-realization quotient. -/
private noncomputable def graphRealizationOfFamilyVertexInvariant
    (boundary : J → Fin 2 → X₀) : X₀ ⊕ (J × I) → Option X₀
  | Sum.inl x => some x
  | Sum.inr (j, t) =>
      if _ : t = 0 then
        some (boundary j 0)
      else if _ : t = 1 then
        some (boundary j 1)
      else
        none

/-- Helper for Example 10.1.8: the endpoint-vertex invariant is constant along the generating
relation of `graphRealizationOfFamilySetoid boundary`. -/
private theorem graphRealizationOfFamilyVertexInvariant_rel
    (boundary : J → Fin 2 → X₀) :
    ∀ a b : X₀ ⊕ (J × I),
      graphRealizationOfFamilyRel boundary a b →
        graphRealizationOfFamilyVertexInvariant boundary a =
          graphRealizationOfFamilyVertexInvariant boundary b := by
  intro a b hab
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hx, ht⟩ | ⟨hx, ht⟩)
          · subst hx
            subst ht
            -- The first endpoint is sent to its initial vertex label.
            simp [graphRealizationOfFamilyVertexInvariant]
          · subst hx
            subst ht
            -- The second endpoint is sent to its terminal vertex label.
            simp [graphRealizationOfFamilyVertexInvariant]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl x =>
          rcases hab with (⟨ht, hx⟩ | ⟨ht, hx⟩)
          · subst ht
            subst hx
            -- The first endpoint and its attached vertex have the same invariant.
            simp [graphRealizationOfFamilyVertexInvariant]
          · subst ht
            subst hx
            -- The second endpoint and its attached vertex have the same invariant.
            simp [graphRealizationOfFamilyVertexInvariant]
      | inr jt' =>
          cases hab

/-- Helper for Example 10.1.8: the endpoint-vertex invariant descends to the generated setoid
relation on `graphRealizationOfFamily boundary`. -/
private theorem graphRealizationOfFamilyVertexInvariant_setoid
    (boundary : J → Fin 2 → X₀) :
    ∀ a b : X₀ ⊕ (J × I),
      graphRealizationOfFamilySetoid boundary a b →
        graphRealizationOfFamilyVertexInvariant boundary a =
          graphRealizationOfFamilyVertexInvariant boundary b := by
  intro a b hab
  let r : (X₀ ⊕ (J × I)) → (X₀ ⊕ (J × I)) → Prop :=
    fun x y ↦
      graphRealizationOfFamilyVertexInvariant boundary x =
        graphRealizationOfFamilyVertexInvariant boundary y
  have hr_equiv : Equivalence r := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  have hrel :
      ∀ x y : X₀ ⊕ (J × I),
        graphRealizationOfFamilyRel boundary x y → r x y := by
    intro x y hxy
    exact graphRealizationOfFamilyVertexInvariant_rel boundary x y hxy
  exact (Equivalence.eqvGen_iff hr_equiv).1 (Relation.EqvGen.mono hrel hab)

/-- Helper for Example 10.1.8: quotienting the endpoint relation does not identify distinct
vertices. -/
private theorem graphRealizationOfFamily_vertex_eq_iff
    (boundary : J → Fin 2 → X₀) {x y : X₀} :
    graphRealizationOfFamilyVertex boundary x =
      graphRealizationOfFamilyVertex boundary y ↔
    x = y := by
  constructor
  · intro hxy
    let q :
        graphRealizationOfFamily boundary →
          Option X₀ :=
      Quotient.lift
        (graphRealizationOfFamilyVertexInvariant boundary)
        (fun _ _ hab ↦ graphRealizationOfFamilyVertexInvariant_setoid boundary _ _ hab)
    -- Compare the quotient classes through the endpoint-vertex invariant.
    have hq : q (graphRealizationOfFamilyVertex boundary x) =
        q (graphRealizationOfFamilyVertex boundary y) :=
      congrArg q hxy
    simpa [q, graphRealizationOfFamilyVertex, graphRealizationOfFamilyVertexInvariant] using hq
  · intro hxy
    subst hxy
    rfl

/-- An interior point of a graph edge is fixed by the quotient setoid, because the generating
relation only identifies endpoints with vertices. -/
private theorem graphRealizationOfFamilySetoid_interiorFixed
    (boundary : J → Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {z : X₀ ⊕ (J × I)}
    (hz : graphRealizationOfFamilySetoid boundary (Sum.inr (j, t)) z) :
    z = Sum.inr (j, t) := by
  let s : X₀ ⊕ (J × I) := Sum.inr (j, t)
  let fixesInterior : (X₀ ⊕ (J × I)) → (X₀ ⊕ (J × I)) → Prop :=
    fun a b ↦ a = s ↔ b = s
  have hfixes_equiv : Equivalence fixesInterior := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  have hrel :
      ∀ a b : X₀ ⊕ (J × I),
        graphRealizationOfFamilyRel boundary a b → fixesInterior a b := by
    intro a b hab
    constructor
    · intro ha
      subst ha
      -- A generator out of `s` would have to hit an endpoint, contradicting `t ≠ 0, 1`.
      cases b with
      | inl x =>
          rcases hab with (⟨ht, _⟩ | ⟨ht, _⟩)
          · exact (ht₀ ht).elim
          · exact (ht₁ ht).elim
      | inr jt =>
          cases hab
    · intro hb
      subst hb
      -- The symmetric generating case is ruled out by the same endpoint contradiction.
      cases a with
      | inl x =>
          rcases hab with (⟨_, ht⟩ | ⟨_, ht⟩)
          · exact (ht₀ ht).elim
          · exact (ht₁ ht).elim
      | inr jt =>
          cases hab
  have hz' : Relation.EqvGen fixesInterior s z :=
    Relation.EqvGen.mono hrel hz
  have hfixed : fixesInterior s z :=
    (Equivalence.eqvGen_iff hfixes_equiv).1 hz'
  -- Since `s` is related to itself, the induced equivalence forces `z = s`.
  exact hfixed.mp rfl

/-- Helper for Example 10.1.8: two interior edge points in a graph realization agree only when
they come from the same edge and the same parameter value. -/
private theorem graphRealizationOfFamily_edgePoint_eq_iff_of_interior
    (boundary : J → Fin 2 → X₀) {j j' : J} {t s : I}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    graphRealizationOfFamilyEdgePoint boundary j t =
        graphRealizationOfFamilyEdgePoint boundary j' s ↔
      j = j' ∧ t = s := by
  constructor
  · intro h
    -- Reduce equality in the quotient to the generated setoid on representatives.
    have hrel :
        graphRealizationOfFamilySetoid boundary (Sum.inr (j, t)) (Sum.inr (j', s)) := by
      exact Quotient.exact h
    -- First force the second representative to equal the first interior point.
    have hfixed :
        Sum.inr (j', s) = Sum.inr (j, t) :=
      graphRealizationOfFamilySetoid_interiorFixed boundary j t ht₀ ht₁ hrel
    -- Then read off equality of the edge index and the parameter.
    cases hfixed
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Helper for Example 10.1.8: an interior point of an edge is never equal to a vertex in the
graph realization quotient. -/
private theorem graphRealizationOfFamily_vertex_ne_edgePoint_of_interior
    (boundary : J → Fin 2 → X₀) (x : X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    graphRealizationOfFamilyVertex boundary x ≠
      graphRealizationOfFamilyEdgePoint boundary j t := by
  intro h
  -- Rewrite the quotient equality back on representatives.
  have hrel :
      graphRealizationOfFamilySetoid boundary (Sum.inr (j, t)) (Sum.inl x) := by
    exact Quotient.exact h.symm
  -- Interior points are fixed by the generated relation, so the target representative cannot be a
  -- vertex.
  have hfixed :
      Sum.inl x = Sum.inr (j, t) :=
    graphRealizationOfFamilySetoid_interiorFixed boundary j t ht₀ ht₁ hrel
  cases hfixed

/-- Helper for Example 10.1.8: each edge of the graph realization comes with its canonical
parameterization by the unit interval. -/
private def graphRealizationOfFamilyEdgeMap
    (boundary : J → Fin 2 → X₀) (j : J) : I → graphRealizationOfFamily boundary :=
  graphRealizationOfFamilyEdgePoint boundary j

/-- Helper for Example 10.1.8: the left endpoint of the edge parameterization is the initial
vertex of that edge. -/
private theorem graphRealizationOfFamilyEdgeMap_zero
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamilyEdgeMap boundary j 0 =
      graphRealizationOfFamilyVertex boundary (boundary j 0) := by
  -- Unfold the parameterization and use the endpoint identification in the quotient.
  simpa [graphRealizationOfFamilyEdgeMap] using
    (graphRealizationOfFamily_vertex_boundary_zero_eq_edgePoint_zero boundary j).symm

/-- Helper for Example 10.1.8: the right endpoint of the edge parameterization is the terminal
vertex of that edge. -/
private theorem graphRealizationOfFamilyEdgeMap_one
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamilyEdgeMap boundary j 1 =
      graphRealizationOfFamilyVertex boundary (boundary j 1) := by
  -- Unfold the parameterization and use the second endpoint identification in the quotient.
  simpa [graphRealizationOfFamilyEdgeMap] using
    (graphRealizationOfFamily_vertex_boundary_one_eq_edgePoint_one boundary j).symm

/-- Helper for Example 10.1.8: the closed `1`-cell disk model used by `Topology.CWComplex`. -/
private abbrev oneCellClosedBall :=
  Metric.closedBall (0 : Fin 1 → ℝ) 1

/-- Helper for Example 10.1.8: evaluating the unique coordinate identifies the closed unit ball in
`Fin 1 → ℝ` with the interval `[-1, 1]`. -/
private noncomputable def oneCellClosedBallHomeomorphIcc :
    oneCellClosedBall ≃ₜ Set.Icc (-1 : ℝ) 1 where
  toEquiv :=
    { toFun := fun x ↦
        ⟨x.1 0, by
          -- Read the closed-ball bound on the unique coordinate.
          have hxnorm : ‖x.1‖ ≤ 1 := by
            exact mem_closedBall_zero_iff.mp x.2
          have hxcoord : ‖x.1 0‖ ≤ 1 :=
            (pi_norm_le_iff_of_nonneg zero_le_one).1 hxnorm 0
          simpa [Real.norm_eq_abs, abs_le] using hxcoord⟩
      invFun := fun t ↦
        ⟨fun _ ↦ (t : ℝ), by
          -- The constant function with value in `[-1, 1]` lies in the closed unit ball.
          have htcoord : ∀ i : Fin 1, ‖(t : ℝ)‖ ≤ 1 := by
            intro i
            have htbounds : (-1 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 := by
              exact t.2
            simpa [Real.norm_eq_abs, abs_le] using htbounds
          have htnorm : ‖(fun _ : Fin 1 ↦ (t : ℝ))‖ ≤ 1 :=
            (pi_norm_le_iff_of_nonneg zero_le_one).2 htcoord
          simpa [oneCellClosedBall, Metric.mem_closedBall, dist_zero_right] using htnorm⟩
      left_inv := by
        intro x
        -- Functions on `Fin 1` are determined by their unique coordinate.
        apply Subtype.ext
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
      right_inv := by
        intro t
        -- The coordinate extractor is inverse to the constant-function reconstruction.
        apply Subtype.ext
        rfl }
  continuous_toFun := by
    -- The forward map is just evaluation at the unique coordinate.
    refine Continuous.subtype_mk ?_ ?_
    exact
      (continuous_apply 0 : Continuous fun x : Fin 1 → ℝ ↦ x 0).comp continuous_subtype_val
  continuous_invFun := by
    -- The inverse map is the continuous constant-function inclusion.
    refine Continuous.subtype_mk ?_ ?_
    continuity

/-- Helper for Example 10.1.8: the shared `1`-cell reparameterization from the CW closed-ball
model to the unit interval `I`. -/
private noncomputable def oneCellParamHomeomorph :
    oneCellClosedBall ≃ₜ I :=
  oneCellClosedBallHomeomorphIcc.trans (iccHomeoI (-1 : ℝ) 1 (by norm_num))

/-- Helper for Example 10.1.8: the left endpoint of the closed `1`-cell model. -/
private def oneCellLeftPoint : oneCellClosedBall :=
  ⟨fun _ ↦ (-1 : ℝ), by
    -- The constant function `-1` has norm at most `1`.
    have hcoord : ∀ i : Fin 1, ‖(-1 : ℝ)‖ ≤ 1 := by
      intro i
      norm_num
    have hnorm : ‖(fun _ : Fin 1 ↦ (-1 : ℝ))‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 hcoord
    exact mem_closedBall_zero_iff.2 hnorm⟩

/-- Helper for Example 10.1.8: the right endpoint of the closed `1`-cell model. -/
private def oneCellRightPoint : oneCellClosedBall :=
  ⟨fun _ ↦ (1 : ℝ), by
    -- The constant function `1` has norm at most `1`.
    have hcoord : ∀ i : Fin 1, ‖(1 : ℝ)‖ ≤ 1 := by
      intro i
      norm_num
    have hnorm : ‖(fun _ : Fin 1 ↦ (1 : ℝ))‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 hcoord
    exact mem_closedBall_zero_iff.2 hnorm⟩

/-- Helper for Example 10.1.8: the shared reparameterization sends the left boundary point of the
closed `1`-cell model to `0 : I`. -/
private theorem oneCellParamHomeomorph_left :
    oneCellParamHomeomorph oneCellLeftPoint = 0 := by
  -- Reduce the statement to the affine formula for `iccHomeoI`.
  apply Subtype.ext
  simp [oneCellParamHomeomorph, oneCellLeftPoint, oneCellClosedBallHomeomorphIcc]

/-- Helper for Example 10.1.8: the shared reparameterization sends the right boundary point of the
closed `1`-cell model to `1 : I`. -/
private theorem oneCellParamHomeomorph_right :
    oneCellParamHomeomorph oneCellRightPoint = 1 := by
  -- Reduce the statement to the affine formula for `iccHomeoI`.
  apply Subtype.ext
  simp [oneCellParamHomeomorph, oneCellRightPoint, oneCellClosedBallHomeomorphIcc]

/-- Helper for Example 10.1.8: the inverse reparameterization sends `0 : I` back to the left
boundary point of the closed `1`-cell model. -/
private theorem oneCellParamHomeomorph_symm_zero :
    oneCellParamHomeomorph.symm (0 : I) = oneCellLeftPoint := by
  -- Apply injectivity to the already-computed image of the left endpoint.
  apply oneCellParamHomeomorph.injective
  simpa using oneCellParamHomeomorph_left.symm

/-- Helper for Example 10.1.8: the inverse reparameterization sends `1 : I` back to the right
boundary point of the closed `1`-cell model. -/
private theorem oneCellParamHomeomorph_symm_one :
    oneCellParamHomeomorph.symm (1 : I) = oneCellRightPoint := by
  -- Apply injectivity to the already-computed image of the right endpoint.
  apply oneCellParamHomeomorph.injective
  simpa using oneCellParamHomeomorph_right.symm

/-- Helper for Example 10.1.8: non-endpoint interval parameters land in the open unit ball of the
closed `1`-cell model. -/
private theorem oneCellParamHomeomorph_symm_mem_ball_of_ne_endpoints
    {t : I} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.ball 0 1) := by
  rw [mem_ball_zero_iff]
  -- Convert the endpoint exclusions into strict inequalities on the real coordinate of `t`.
  have ht₀' : (0 : ℝ) < (t : ℝ) := by
    have ht₀'' : (t : ℝ) ≠ 0 := by
      intro ht
      apply ht₀
      apply Subtype.ext
      simpa using ht
    exact lt_of_le_of_ne t.2.1 (Ne.symm ht₀'')
  have ht₁' : (t : ℝ) < 1 := by
    have ht₁'' : (t : ℝ) ≠ 1 := by
      intro ht
      apply ht₁
      apply Subtype.ext
      simpa using ht
    exact lt_of_le_of_ne t.2.2 ht₁''
  -- The inverse image is the constant function with value `2 * t - 1`.
  have hcoord :
      (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ)) =
        fun _ ↦ 2 * (t : ℝ) - 1 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change ((1 - (-1 : ℝ)) * (t : ℝ) + (-1)) = 2 * (t : ℝ) - 1
    ring
  have habs : |2 * (t : ℝ) - 1| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hnorm : ‖(fun _ : Fin 1 ↦ 2 * (t : ℝ) - 1)‖ < 1 := by
    calc
      ‖(fun _i : Fin 1 ↦ 2 * (t : ℝ) - 1)‖ = ‖2 * (t : ℝ) - 1‖ := by
        simpa using
          (pi_norm_const' (2 * (t : ℝ) - 1) :
            ‖fun _ : Fin 1 ↦ 2 * (t : ℝ) - 1‖ = ‖2 * (t : ℝ) - 1‖)
      _ = |2 * (t : ℝ) - 1| := by rw [Real.norm_eq_abs]
      _ < 1 := habs
  simpa [hcoord] using hnorm

/-- Helper for Example 10.1.8: every interval parameter is either the left endpoint, the right
endpoint, or an interior point. -/
private theorem unitInterval_eq_zero_or_eq_one_or_ne_endpoints (t : I) :
    t = 0 ∨ t = 1 ∨ (t ≠ 0 ∧ t ≠ 1) := by
  by_cases ht₀ : t = 0
  · exact Or.inl ht₀
  · by_cases ht₁ : t = 1
    · exact Or.inr (Or.inl ht₁)
    · exact Or.inr (Or.inr ⟨ht₀, ht₁⟩)

/-- Helper for Example 10.1.8: the open `1`-cell source used by the graph edge parameterization. -/
private abbrev oneCellOpenBall :=
  Metric.ball (0 : Fin 1 → ℝ) 1

/-- Helper for Example 10.1.8: the open interval of non-endpoint parameters in `I`. -/
private abbrev oneCellInteriorParam :=
  { t : I // t ≠ 0 ∧ t ≠ 1 }

/-- Helper for Example 10.1.8: the endpoint-free locus in `I` is open. -/
private theorem oneCellInteriorParam_isOpen :
    IsOpen ({ t : I | t ≠ 0 ∧ t ≠ 1 } : Set I) := by
  -- Rewrite the endpoint exclusions as the open interval `(0, 1)` inside `I`.
  convert continuous_subtype_val.isOpen_preimage (s := Set.Ioo (0 : ℝ) 1) isOpen_Ioo using 1
  ext t
  constructor
  · rintro ⟨ht0, ht1⟩
    constructor
    · have ht0' : (t : ℝ) ≠ 0 := by
        intro h
        exact ht0 <| Subtype.ext h
      exact lt_of_le_of_ne t.2.1 (Ne.symm ht0')
    · have ht1' : (t : ℝ) ≠ 1 := by
        intro h
        exact ht1 <| Subtype.ext h
      exact lt_of_le_of_ne t.2.2 ht1'
  · intro ht
    constructor
    · intro ht0
      exact (lt_irrefl (0 : ℝ)) <| by simpa [ht0] using ht.1
    · intro ht1
      exact (lt_irrefl (1 : ℝ)) <| by simpa [ht1] using ht.2

/-- Helper for Example 10.1.8: the left boundary point of the closed `1`-cell model lies on the
unit sphere `Metric.sphere 0 1`. -/
private theorem oneCellLeftPoint_mem_sphere :
    ((oneCellLeftPoint : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  -- Compute the norm of the constant `(-1)` function on `Fin 1`.
  rw [mem_sphere_zero_iff_norm]
  simpa [oneCellLeftPoint] using
    (pi_norm_const' (-1 : ℝ) : ‖fun _ : Fin 1 ↦ (-1 : ℝ)‖ = ‖(-1 : ℝ)‖)

/-- Helper for Example 10.1.8: the right boundary point of the closed `1`-cell model lies on the
unit sphere `Metric.sphere 0 1`. -/
private theorem oneCellRightPoint_mem_sphere :
    ((oneCellRightPoint : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  -- Compute the norm of the constant `(1)` function on `Fin 1`.
  rw [mem_sphere_zero_iff_norm]
  simpa [oneCellRightPoint] using
    (pi_norm_const' (1 : ℝ) : ‖fun _ : Fin 1 ↦ (1 : ℝ)‖ = ‖(1 : ℝ)‖)

/-- Helper for Example 10.1.8: the left endpoint of the closed `1`-cell model is not in the open
ball. -/
private theorem oneCellLeftPoint_not_mem_ball :
    (((oneCellLeftPoint : oneCellClosedBall) : Fin 1 → ℝ) ∉ oneCellOpenBall) := by
  intro hx
  rw [mem_ball_zero_iff] at hx
  have hnorm : ‖((oneCellLeftPoint : oneCellClosedBall) : Fin 1 → ℝ)‖ = 1 := by
    have hSphere := oneCellLeftPoint_mem_sphere
    rwa [mem_sphere_zero_iff_norm] at hSphere
  linarith

/-- Helper for Example 10.1.8: the right endpoint of the closed `1`-cell model is not in the open
ball. -/
private theorem oneCellRightPoint_not_mem_ball :
    (((oneCellRightPoint : oneCellClosedBall) : Fin 1 → ℝ) ∉ oneCellOpenBall) := by
  intro hx
  rw [mem_ball_zero_iff] at hx
  have hnorm : ‖((oneCellRightPoint : oneCellClosedBall) : Fin 1 → ℝ)‖ = 1 := by
    have hSphere := oneCellRightPoint_mem_sphere
    rwa [mem_sphere_zero_iff_norm] at hSphere
  linarith

/-- Helper for Example 10.1.8: the open-ball model of the `1`-cell is equivalent to the endpoint
complement of `I`. -/
private noncomputable def oneCellOpenBallEquivInteriorParam :
    oneCellOpenBall ≃ oneCellInteriorParam where
  toFun := fun x ↦
    ⟨oneCellParamHomeomorph ⟨x.1, Metric.ball_subset_closedBall x.2⟩, by
      constructor
      · intro hx0
        have hxLeft : (⟨x.1, Metric.ball_subset_closedBall x.2⟩ : oneCellClosedBall) =
            oneCellLeftPoint := by
          apply oneCellParamHomeomorph.injective
          calc
            oneCellParamHomeomorph ⟨x.1, Metric.ball_subset_closedBall x.2⟩ = 0 := hx0
            _ = oneCellParamHomeomorph oneCellLeftPoint := oneCellParamHomeomorph_left.symm
        exact oneCellLeftPoint_not_mem_ball <| hxLeft ▸ x.2
      · intro hx1
        have hxRight : (⟨x.1, Metric.ball_subset_closedBall x.2⟩ : oneCellClosedBall) =
            oneCellRightPoint := by
          apply oneCellParamHomeomorph.injective
          calc
            oneCellParamHomeomorph ⟨x.1, Metric.ball_subset_closedBall x.2⟩ = 1 := hx1
            _ = oneCellParamHomeomorph oneCellRightPoint := oneCellParamHomeomorph_right.symm
        exact oneCellRightPoint_not_mem_ball <| hxRight ▸ x.2⟩
  invFun := fun t ↦
    ⟨((oneCellParamHomeomorph.symm t.1 : oneCellClosedBall) : Fin 1 → ℝ),
      oneCellParamHomeomorph_symm_mem_ball_of_ne_endpoints t.2.1 t.2.2⟩
  left_inv := by
    intro x
    -- The inverse branch is literally the inverse homeomorphism on the interior point.
    apply Subtype.ext
    simpa using oneCellParamHomeomorph.left_inv ⟨x.1, Metric.ball_subset_closedBall x.2⟩
  right_inv := by
    intro t
    -- The forward branch is literally the forward homeomorphism on the interior parameter.
    apply Subtype.ext
    simpa using oneCellParamHomeomorph.right_inv t.1

/-- Helper for Example 10.1.8: the open-ball/interior-interval equivalence is continuous. -/
private theorem oneCellOpenBallEquivInteriorParam_continuous :
    Continuous oneCellOpenBallEquivInteriorParam := by
  -- This is the original closed-ball homeomorphism restricted to the open source.
  refine Continuous.subtype_mk ?_ ?_
  exact oneCellParamHomeomorph.continuous.comp <|
    Continuous.subtype_mk continuous_subtype_val
      (fun x : oneCellOpenBall ↦ Metric.ball_subset_closedBall x.2)

/-- Helper for Example 10.1.8: the inverse interior-interval/open-ball equivalence is continuous.
-/
private theorem oneCellOpenBallEquivInteriorParam_symm_continuous :
    Continuous oneCellOpenBallEquivInteriorParam.symm := by
  -- The inverse branch is the inverse homeomorphism, with the ball-membership witness added as a
  -- subtype proof.
  refine Continuous.subtype_mk ?_ ?_
  exact
    (continuous_subtype_val.comp oneCellParamHomeomorph.symm.continuous).comp
      continuous_subtype_val

/-- Helper for Example 10.1.8: the open-ball/interior-interval equivalence is an open map because
its inverse is continuous. -/
private theorem oneCellOpenBallEquivInteriorParam_isOpenMap :
    IsOpenMap oneCellOpenBallEquivInteriorParam := by
  intro s hs
  -- Rewrite the image as the inverse-image under the explicit inverse.
  have hImage :
      oneCellOpenBallEquivInteriorParam '' s =
        oneCellOpenBallEquivInteriorParam.symm ⁻¹' s := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro ht
      refine ⟨oneCellOpenBallEquivInteriorParam.symm t, ht, ?_⟩
      exact oneCellOpenBallEquivInteriorParam.apply_symm_apply t
  rw [hImage]
  exact oneCellOpenBallEquivInteriorParam_symm_continuous.isOpen_preimage _ hs

/-- Helper for Example 10.1.8: the open-ball model of the `1`-cell is homeomorphic to the
endpoint complement of `I`. -/
private noncomputable def oneCellOpenBallHomeomorphInteriorParam :
    oneCellOpenBall ≃ₜ oneCellInteriorParam :=
  oneCellOpenBallEquivInteriorParam.toHomeomorphOfContinuousOpen
    oneCellOpenBallEquivInteriorParam_continuous
    oneCellOpenBallEquivInteriorParam_isOpenMap

/-- Helper for Example 10.1.8: the interior-parameter subtype is nonempty. -/
private instance oneCellInteriorParam_nonempty : Nonempty oneCellInteriorParam :=
  ⟨⟨(⟨(1 : ℝ) / 2, by norm_num⟩ : I), by
      intro h
      have h' : (((⟨(1 : ℝ) / 2, by norm_num⟩ : I) : I) : ℝ) = 0 := by
        simpa using congrArg (fun t : I ↦ (t : ℝ)) h
      norm_num at h'
    , by
      intro h
      have h' : (((⟨(1 : ℝ) / 2, by norm_num⟩ : I) : I) : ℝ) = 1 := by
        simpa using congrArg (fun t : I ↦ (t : ℝ)) h
      norm_num at h'⟩⟩

/-- Helper for Example 10.1.8: the source-side inclusion of one edge interior is an open
embedding into `X₀ ⊕ (J × I)`. -/
private theorem graphRealizationOfFamilyEdgeInteriorSource_isOpenEmbedding
    (j : J) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    Topology.IsOpenEmbedding
      (fun t : oneCellInteriorParam ↦ (Sum.inr (j, t.1) : X₀ ⊕ (J × I))) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hSubtype :
      Topology.IsOpenEmbedding ((↑) : oneCellInteriorParam → I) :=
    oneCellInteriorParam_isOpen.isOpenEmbedding_subtypeVal
  have hProd :
      Topology.IsOpenEmbedding (fun t : I ↦ (j, t) : I → J × I) := by
    let _ : DiscreteTopology J := discreteTopology_bot _
    refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_const.prodMk continuous_id) ?_ ?_
    · intro s t hst
      simpa using congrArg Prod.snd hst
    · intro U hU
      have hImage : (fun t : I ↦ (j, t)) '' U = ({j} : Set J) ×ˢ U := by
        ext p
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨by simp, ht⟩
        · rintro ⟨hp, hpU⟩
          refine ⟨p.2, hpU, ?_⟩
          simp at hp
          cases p
          cases hp
          rfl
      rw [hImage]
      exact (isOpen_discrete _).prod hU
  exact Topology.IsOpenEmbedding.inr.comp (hProd.comp hSubtype)

/-- Helper for Example 10.1.8: every `1`-cell in a CW complex of the whole space has two
distinguished endpoint vertices obtained from its characteristic map on the boundary sphere. -/
private theorem oneCellEndpoints_eq_vertices
    {X : Type w} [TopologicalSpace X]
    (cw : Topology.CWComplex (Set.univ : Set X))
    (j : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    ∃ v0 v1 : Topology.CWComplex.cell (Set.univ : Set X) 0,
      Topology.CWComplex.map 1 j oneCellLeftPoint = Topology.CWComplex.map 0 v0 0 ∧
      Topology.CWComplex.map 1 j oneCellRightPoint = Topology.CWComplex.map 0 v1 0 := by
  classical
  letI : Topology.CWComplex (Set.univ : Set X) := cw
  obtain ⟨cells, hI⟩ := Topology.CWComplex.mapsTo 1 j
  -- Evaluate the boundary control at the two explicit endpoints of the closed `1`-cell model.
  have hLeft :
      Topology.CWComplex.map 1 j oneCellLeftPoint ∈
        ⋃ (m < 1) (k ∈ cells m), Topology.CWComplex.map m k '' Metric.closedBall 0 1 := by
    exact hI oneCellLeftPoint_mem_sphere
  have hRight :
      Topology.CWComplex.map 1 j oneCellRightPoint ∈
        ⋃ (m < 1) (k ∈ cells m), Topology.CWComplex.map m k '' Metric.closedBall 0 1 := by
    exact hI oneCellRightPoint_mem_sphere
  rcases Set.mem_iUnion.mp hLeft with ⟨m0, hLeft⟩
  rcases Set.mem_iUnion.mp hLeft with ⟨hm0, hLeft⟩
  have hm0' : m0 = 0 := Nat.lt_one_iff.mp hm0
  subst hm0'
  rcases Set.mem_iUnion.mp hLeft with ⟨v0, hLeft⟩
  rcases Set.mem_iUnion.mp hLeft with ⟨_, hLeft⟩
  rcases Set.mem_iUnion.mp hRight with ⟨m1, hRight⟩
  rcases Set.mem_iUnion.mp hRight with ⟨hm1, hRight⟩
  have hm1' : m1 = 0 := Nat.lt_one_iff.mp hm1
  subst hm1'
  rcases Set.mem_iUnion.mp hRight with ⟨v1, hRight⟩
  rcases Set.mem_iUnion.mp hRight with ⟨_, hRight⟩
  -- Zero-cells are singletons, so membership in a closed `0`-cell identifies the endpoint vertex.
  have hLeftEq :
      Topology.CWComplex.map 1 j oneCellLeftPoint = Topology.CWComplex.map 0 v0 0 := by
    have hLeftClosed :
        Topology.CWComplex.map 1 j oneCellLeftPoint ∈ Topology.CWComplex.closedCell 0 v0 := hLeft
    rw [Topology.CWComplex.closedCell_zero_eq_singleton] at hLeftClosed
    simpa using hLeftClosed
  have hRightEq :
      Topology.CWComplex.map 1 j oneCellRightPoint = Topology.CWComplex.map 0 v1 0 := by
    have hRightClosed :
        Topology.CWComplex.map 1 j oneCellRightPoint ∈ Topology.CWComplex.closedCell 0 v1 := hRight
    rw [Topology.CWComplex.closedCell_zero_eq_singleton] at hRightClosed
    simpa using hRightClosed
  exact ⟨v0, v1, hLeftEq, hRightEq⟩

/-- Helper for Example 10.1.8: the reverse comparison map sends each chosen `0`-cell to its
vertex and each chosen `1`-cell parameter to the corresponding point of `X`. -/
private noncomputable def oneDimensionalComparison
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] :
    ULift (Topology.CWComplex.cell (Set.univ : Set X) 0) ⊕
      (ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) × I) → X
  | Sum.inl v => Topology.CWComplex.map 0 v.down 0
  | Sum.inr (j, t) => Topology.CWComplex.map 1 j.down (oneCellParamHomeomorph.symm t)

/-- Helper for Example 10.1.8: in a one-dimensional CW complex, the reverse comparison map is
surjective because every point lies on either a `0`-cell or a `1`-cell. -/
private theorem oneDimensionalComparison_surjective
    {X : Type w} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h_dim : Topology.RelCWComplex.dimLE (Set.univ : Set X) 1) :
    Function.Surjective (@oneDimensionalComparison X _ _) := by
  intro x
  -- Cover `x` by some closed cell and then rule out dimensions above `1`.
  have hxCell :
      x ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n),
        @Topology.RelCWComplex.closedCell X _ (Set.univ : Set X) ∅ _ n j := by
    have hxUniv : x ∈ (Set.univ : Set X) := by
      simp
    rw [← @Topology.CWComplex.union X _ (Set.univ : Set X) _] at hxUniv
    exact hxUniv
  rcases Set.mem_iUnion.mp hxCell with ⟨n, hxCell⟩
  rcases Set.mem_iUnion.mp hxCell with ⟨j, hxCell⟩
  have hnle : n ≤ 1 := by
    by_contra hnle
    exact (Topology.CWComplex.isEmpty_cell_of_one_lt_of_dimLE_one h_dim n
      (lt_of_not_ge hnle)).false j
  by_cases hn0 : n = 0
  · subst hn0
    -- A point in a closed `0`-cell is the image of the corresponding vertex.
    rw [Topology.CWComplex.closedCell_zero_eq_singleton] at hxCell
    refine ⟨Sum.inl ⟨j⟩, ?_⟩
    simpa [oneDimensionalComparison] using hxCell.symm
  · have hn1 : n = 1 := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      exact le_antisymm hnle (Nat.succ_le_of_lt hnpos)
    subst hn1
    -- A point in a closed `1`-cell comes from the closed-ball parameter of that cell.
    rcases hxCell with ⟨y, hy, hyx⟩
    refine ⟨Sum.inr (⟨j⟩, oneCellParamHomeomorph ⟨y, hy⟩), ?_⟩
    -- The chosen interval coordinate is inverse to the closed-ball parameterization.
    simpa [oneDimensionalComparison] using hyx

/-- Helper for Example 10.1.8: distinct chosen `0`-cells remain distinct under the reverse
comparison map. -/
private theorem oneDimensionalComparison_vertex_eq_iff
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    {v w : ULift (Topology.CWComplex.cell (Set.univ : Set X) 0)} :
    @oneDimensionalComparison X _ _ (Sum.inl v) =
        @oneDimensionalComparison X _ _ (Sum.inl w) ↔
      v = w := by
  let comparison := @oneDimensionalComparison X _ _
  let openCell := @Topology.RelCWComplex.openCell X _ (Set.univ : Set X) ∅ _
  constructor
  · intro h
    change comparison (Sum.inl v) = comparison (Sum.inl w) at h
    -- Put the common image point in both open `0`-cells, then use disjointness.
    have hv : comparison (Sum.inl v) ∈ openCell 0 v.down := by
      simpa [comparison, oneDimensionalComparison] using
        (@Topology.RelCWComplex.map_zero_mem_openCell X _ (Set.univ : Set X) ∅ _ 0 v.down)
    have hw : comparison (Sum.inl w) ∈ openCell 0 w.down := by
      simpa [comparison, oneDimensionalComparison] using
        (@Topology.RelCWComplex.map_zero_mem_openCell X _ (Set.univ : Set X) ∅ _ 0 w.down)
    have hnot : ¬ Disjoint (openCell 0 v.down) (openCell 0 w.down) := by
      intro hdis
      have hmem :
          comparison (Sum.inl v) ∈ openCell 0 v.down ∩ openCell 0 w.down := by
        exact ⟨hv, h ▸ hw⟩
      exact hdis.le_bot hmem
    -- Distinct open cells are disjoint, so the two `0`-cell indices must agree.
    have hcell :=
      @Topology.RelCWComplex.eq_of_not_disjoint_openCell X _ (Set.univ : Set X) ∅ _
        0 v.down 0 w.down hnot
    cases v
    cases w
    simp at hcell ⊢
    exact hcell
  · rintro rfl
    rfl

/-- Helper for Example 10.1.8: a `0`-cell image is disjoint from every interior point of a
`1`-cell under the reverse comparison map. -/
private theorem oneDimensionalComparison_vertex_ne_edge_of_interior
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (v : ULift (Topology.CWComplex.cell (Set.univ : Set X) 0))
    (j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1))
    {t : I} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    @oneDimensionalComparison X _ _ (Sum.inl v) ≠
      @oneDimensionalComparison X _ _ (Sum.inr (j, t)) := by
  let comparison := @oneDimensionalComparison X _ _
  let openCell := @Topology.RelCWComplex.openCell X _ (Set.univ : Set X) ∅ _
  intro h
  change comparison (Sum.inl v) = comparison (Sum.inr (j, t)) at h
  -- Place the two points in open cells of different dimensions.
  have hv : comparison (Sum.inl v) ∈ openCell 0 v.down := by
    simpa [comparison, oneDimensionalComparison] using
      (@Topology.RelCWComplex.map_zero_mem_openCell X _ (Set.univ : Set X) ∅ _ 0 v.down)
  have hjBall :
      (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.ball 0 1) :=
    oneCellParamHomeomorph_symm_mem_ball_of_ne_endpoints ht₀ ht₁
  have hj : comparison (Sum.inr (j, t)) ∈ openCell 1 j.down := by
    refine ⟨((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ), hjBall, ?_⟩
    change
      Topology.CWComplex.map 1 j.down
          (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ)) =
        comparison (Sum.inr (j, t))
    simp [comparison, oneDimensionalComparison]
  have hnot : ¬ Disjoint (openCell 0 v.down) (openCell 1 j.down) := by
    intro hdis
    have hmem : comparison (Sum.inl v) ∈ openCell 0 v.down ∩ openCell 1 j.down := by
      exact ⟨hv, h ▸ hj⟩
    exact hdis.le_bot hmem
  -- Different-dimensional open cells are disjoint, so no such equality can occur.
  have hcell :
      (⟨0, v.down⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n) =
      ⟨1, j.down⟩ :=
    @Topology.RelCWComplex.eq_of_not_disjoint_openCell X _ (Set.univ : Set X) ∅ _
      0 v.down 1 j.down hnot
  cases hcell

/-- Helper for Example 10.1.8: two interior points in the reverse comparison map agree only when
they come from the same `1`-cell and the same interval parameter. -/
private theorem oneDimensionalComparison_edge_eq_iff_of_interior
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    {j j' : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1)} {t s : I}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    @oneDimensionalComparison X _ _ (Sum.inr (j, t)) =
        @oneDimensionalComparison X _ _ (Sum.inr (j', s)) ↔
      j = j' ∧ t = s := by
  let comparison := @oneDimensionalComparison X _ _
  let openCell := @Topology.RelCWComplex.openCell X _ (Set.univ : Set X) ∅ _
  constructor
  · intro h
    change comparison (Sum.inr (j, t)) = comparison (Sum.inr (j', s)) at h
    -- First force the two interior points to lie in the same open `1`-cell.
    have htBall :
        (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.ball 0 1) :=
      oneCellParamHomeomorph_symm_mem_ball_of_ne_endpoints ht₀ ht₁
    have hsBall :
        (((oneCellParamHomeomorph.symm s : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.ball 0 1) :=
      oneCellParamHomeomorph_symm_mem_ball_of_ne_endpoints hs₀ hs₁
    have hj : comparison (Sum.inr (j, t)) ∈ openCell 1 j.down := by
      refine ⟨((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ), htBall, ?_⟩
      change
        Topology.CWComplex.map 1 j.down
            (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ)) =
          comparison (Sum.inr (j, t))
      simp [comparison, oneDimensionalComparison]
    have hj' : comparison (Sum.inr (j', s)) ∈ openCell 1 j'.down := by
      refine ⟨((oneCellParamHomeomorph.symm s : oneCellClosedBall) : Fin 1 → ℝ), hsBall, ?_⟩
      change
        Topology.CWComplex.map 1 j'.down
            (((oneCellParamHomeomorph.symm s : oneCellClosedBall) : Fin 1 → ℝ)) =
          comparison (Sum.inr (j', s))
      simp [comparison, oneDimensionalComparison]
    have hnot : ¬ Disjoint (openCell 1 j.down) (openCell 1 j'.down) := by
      intro hdis
      have hmem : comparison (Sum.inr (j, t)) ∈ openCell 1 j.down ∩ openCell 1 j'.down := by
        exact ⟨hj, h ▸ hj'⟩
      exact hdis.le_bot hmem
    have hcell :
        (⟨1, j.down⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n) =
        ⟨1, j'.down⟩ :=
      @Topology.RelCWComplex.eq_of_not_disjoint_openCell X _ (Set.univ : Set X) ∅ _
        1 j.down 1 j'.down hnot
    have hjEq : j = j' := by
      cases j
      cases j'
      simp at hcell ⊢
      exact hcell
    subst hjEq
    -- Once the cell index matches, the partial equivalence is injective on the open ball.
    have htSource :
        (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ)) ∈
          (Topology.CWComplex.map 1 j.down).source := by
      simpa [@Topology.CWComplex.source_eq X _ (Set.univ : Set X) _ 1 j.down] using htBall
    have hsSource :
        (((oneCellParamHomeomorph.symm s : oneCellClosedBall) : Fin 1 → ℝ)) ∈
          (Topology.CWComplex.map 1 j.down).source := by
      simpa [@Topology.CWComplex.source_eq X _ (Set.univ : Set X) _ 1 j.down] using hsBall
    have hArg :
        (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ)) =
          ((oneCellParamHomeomorph.symm s : oneCellClosedBall) : Fin 1 → ℝ) := by
      exact (Topology.CWComplex.map 1 j.down).injOn htSource hsSource
        (by simpa [comparison, oneDimensionalComparison] using h)
    have hSubtype : oneCellParamHomeomorph.symm t = oneCellParamHomeomorph.symm s := by
      apply Subtype.ext
      simpa using hArg
    exact ⟨rfl, oneCellParamHomeomorph.symm.injective hSubtype⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Helper for Example 10.1.8: the graph realization carries the quotient topology from
`X₀ ⊕ (J × I)`. -/
  private theorem graphRealizationOfFamily_isQuotientMap
    (boundary : J → Fin 2 → X₀) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationOfFamilySourceTopologicalSpace
    Topology.IsQuotientMap
      (Quotient.mk' (s := graphRealizationOfFamilySetoid boundary) :
        X₀ ⊕ (J × I) → graphRealizationOfFamily boundary) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  simpa using
    (isQuotientMap_quotient_mk' :
      Topology.IsQuotientMap
        (Quotient.mk' (s := graphRealizationOfFamilySetoid boundary) :
          X₀ ⊕ (J × I) → graphRealizationOfFamily boundary))

/-- Helper for Example 10.1.8: the vertex inclusion into the graph realization is continuous. -/
private theorem graphRealizationOfFamilyVertex_continuous
    (boundary : J → Fin 2 → X₀) :
    let _ : TopologicalSpace X₀ := ⊥
    Continuous (graphRealizationOfFamilyVertex boundary) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  -- The vertex map is the quotient projection composed with the left summand inclusion.
  change Continuous fun x : X₀ ↦
    (Quotient.mk' (s := graphRealizationOfFamilySetoid boundary) :
      X₀ ⊕ (J × I) → graphRealizationOfFamily boundary) (Sum.inl x)
  exact continuous_quotient_mk'.comp continuous_inl

/-- Helper for Example 10.1.8: the edge parameterization into the graph realization is
continuous. -/
private theorem graphRealizationOfFamilyEdgePoint_continuous
    (boundary : J → Fin 2 → X₀) (j : J) :
    Continuous (graphRealizationOfFamilyEdgePoint boundary j) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  -- The edge map is the quotient projection composed with the continuous inclusion of `I`.
  change Continuous fun t : I ↦
    (Quotient.mk' (s := graphRealizationOfFamilySetoid boundary) :
      X₀ ⊕ (J × I) → graphRealizationOfFamily boundary) (Sum.inr (j, t))
  exact continuous_quotient_mk'.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))

/-- Helper for Example 10.1.8: the graph-realization image of one edge interior. -/
private noncomputable def graphRealizationOfFamilyEdgeInteriorMap
    (boundary : J → Fin 2 → X₀) (j : J) :
    oneCellInteriorParam → graphRealizationOfFamily boundary :=
  fun t ↦ graphRealizationOfFamilyEdgePoint boundary j t.1

/-- Helper for Example 10.1.8: pulling back the image of one open edge along the quotient map
recovers exactly the corresponding interior source slice. -/
private theorem graphRealizationOfFamilyEdgeInterior_preimage_image
    (boundary : J → Fin 2 → X₀) (j : J) (U : Set oneCellInteriorParam) :
    let q :
        X₀ ⊕ (J × I) → graphRealizationOfFamily boundary :=
      Quotient.mk' (s := graphRealizationOfFamilySetoid boundary)
    q ⁻¹' (graphRealizationOfFamilyEdgeInteriorMap boundary j '' U) =
      (fun t : oneCellInteriorParam ↦ (Sum.inr (j, t.1) : X₀ ⊕ (J × I))) '' U := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨t, htU, hz⟩
    have hrel' :
        graphRealizationOfFamilySetoid boundary z (Sum.inr (j, t.1)) := by
      simpa [graphRealizationOfFamilyEdgeInteriorMap] using
        (Quotient.exact (s := graphRealizationOfFamilySetoid boundary) hz.symm)
    have hrel :
        graphRealizationOfFamilySetoid boundary (Sum.inr (j, t.1)) z := by
      exact Relation.EqvGen.symm _ _ hrel'
    have hzEq : z = Sum.inr (j, t.1) :=
      graphRealizationOfFamilySetoid_interiorFixed boundary j t.1 t.2.1 t.2.2 hrel
    exact ⟨t, htU, hzEq.symm⟩
  · rintro ⟨t, htU, rfl⟩
    exact ⟨t, htU, rfl⟩

/-- Helper for Example 10.1.8: the quotient image of an open edge interior is an open embedding in
the graph realization. -/
private theorem graphRealizationOfFamilyEdgeInterior_isOpenEmbedding
    (boundary : J → Fin 2 → X₀) (j : J) :
    Topology.IsOpenEmbedding (graphRealizationOfFamilyEdgeInteriorMap boundary j) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · -- The interior-edge map is just the edge parameterization restricted to the endpoint-free
    -- subtype of `I`.
    exact (graphRealizationOfFamilyEdgePoint_continuous boundary j).comp continuous_subtype_val
  · intro t s hts
    have hts' : t.1 = s.1 := by
      have hEq :
          j = j ∧ t.1 = s.1 :=
        (graphRealizationOfFamily_edgePoint_eq_iff_of_interior
          (boundary := boundary) (j := j) (j' := j) (t := t.1) (s := s.1)
          t.2.1 t.2.2 s.2.1 s.2.2).mp hts
      exact hEq.2
    exact Subtype.ext hts'
  · intro U hU
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    rw [← (graphRealizationOfFamily_isQuotientMap boundary).isOpen_preimage]
    simpa [graphRealizationOfFamilyEdgeInterior_preimage_image] using
      (graphRealizationOfFamilyEdgeInteriorSource_isOpenEmbedding (X₀ := X₀) (J := J) j).isOpenMap U hU

/-- Helper for Example 10.1.8: one open graph edge, viewed as an open partial homeomorphism from
the open-ball source. -/
private noncomputable def graphRealizationOfFamilyOneCellOpenPartialHomeomorph
    (boundary : J → Fin 2 → X₀) (j : J) :
    OpenPartialHomeomorph oneCellOpenBall (graphRealizationOfFamily boundary) :=
  (oneCellOpenBallHomeomorphInteriorParam.toOpenPartialHomeomorph).trans
    ((graphRealizationOfFamilyEdgeInterior_isOpenEmbedding boundary j).toOpenPartialHomeomorph _)

/-- Helper for Example 10.1.8: once the chosen endpoint labels match the reverse comparison map,
the graph-realization setoid is exactly the kernel relation of that comparison map. -/
private theorem oneDimensionalComparison_rel_iff
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (boundary :
      ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) → Fin 2 →
        ULift (Topology.CWComplex.cell (Set.univ : Set X) 0))
    (hEdgeZero :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        @oneDimensionalComparison X _ _ (Sum.inr (j, (0 : I))) =
          @oneDimensionalComparison X _ _ (Sum.inl (boundary j 0)))
    (hEdgeOne :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        @oneDimensionalComparison X _ _ (Sum.inr (j, (1 : I))) =
          @oneDimensionalComparison X _ _ (Sum.inl (boundary j 1))) :
    ∀ a b :
        ULift (Topology.CWComplex.cell (Set.univ : Set X) 0) ⊕
          (ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) × I),
      graphRealizationOfFamilySetoid boundary a b ↔
        @oneDimensionalComparison X _ _ a = @oneDimensionalComparison X _ _ b := by
  let comparison := @oneDimensionalComparison X _ _
  have hLeftRel :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        graphRealizationOfFamilySetoid boundary
          (Sum.inr (j, (0 : I))) (Sum.inl (boundary j 0)) := by
    intro j
    -- Each left endpoint is glued to its chosen initial vertex.
    exact
      (Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩) :
        Relation.EqvGen (graphRealizationOfFamilyRel boundary)
          (Sum.inr (j, (0 : I))) (Sum.inl (boundary j 0)))
  have hRightRel :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        graphRealizationOfFamilySetoid boundary
          (Sum.inr (j, (1 : I))) (Sum.inl (boundary j 1)) := by
    intro j
    -- Each right endpoint is glued to its chosen terminal vertex.
    exact
      (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩) :
        Relation.EqvGen (graphRealizationOfFamilyRel boundary)
          (Sum.inr (j, (1 : I))) (Sum.inl (boundary j 1)))
  have hLeftRelSymm :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        graphRealizationOfFamilySetoid boundary
          (Sum.inl (boundary j 0)) (Sum.inr (j, (0 : I))) := by
    intro j
    exact Relation.EqvGen.symm _ _ (hLeftRel j)
  have hRightRelSymm :
      ∀ j : ULift (Topology.CWComplex.cell (Set.univ : Set X) 1),
        graphRealizationOfFamilySetoid boundary
          (Sum.inl (boundary j 1)) (Sum.inr (j, (1 : I))) := by
    intro j
    exact Relation.EqvGen.symm _ _ (hRightRel j)
  intro a b
  constructor
  · intro hab
    let sameImage :
        (ULift (Topology.CWComplex.cell (Set.univ : Set X) 0) ⊕
            (ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) × I)) →
          (ULift (Topology.CWComplex.cell (Set.univ : Set X) 0) ⊕
            (ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) × I)) →
          Prop :=
      fun x y ↦ comparison x = comparison y
    -- Show first that the generating relation preserves comparison-map values.
    have hsame_equiv : Equivalence sameImage := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        rfl
      · intro x y hxy
        exact hxy.symm
      · intro x y z hxy hyz
        exact hxy.trans hyz
    have hsame_rel :
        ∀ x y :
            ULift (Topology.CWComplex.cell (Set.univ : Set X) 0) ⊕
              (ULift (Topology.CWComplex.cell (Set.univ : Set X) 1) × I),
          graphRealizationOfFamilyRel boundary x y → sameImage x y := by
      intro x y hxy
      cases x with
      | inl v =>
          cases y with
          | inl w =>
              cases hxy
          | inr jt =>
              rcases jt with ⟨j, t⟩
              rcases hxy with (⟨hv, ht⟩ | ⟨hv, ht⟩)
              · subst hv
                subst ht
                -- The left endpoint is sent to the same point as its incident vertex.
                show sameImage (Sum.inl (boundary j 0)) (Sum.inr (j, (0 : I)))
                simpa [sameImage, comparison, oneDimensionalComparison] using (hEdgeZero j).symm
              · subst hv
                subst ht
                -- The right endpoint is sent to the same point as its incident vertex.
                show sameImage (Sum.inl (boundary j 1)) (Sum.inr (j, (1 : I)))
                simpa [sameImage, comparison, oneDimensionalComparison] using (hEdgeOne j).symm
      | inr jt =>
          rcases jt with ⟨j, t⟩
          cases y with
          | inl v =>
              rcases hxy with (⟨ht, hv⟩ | ⟨ht, hv⟩)
              · subst ht
                subst hv
                -- This is the same endpoint comparison, now in the edge-to-vertex direction.
                show sameImage (Sum.inr (j, (0 : I))) (Sum.inl (boundary j 0))
                simpa [sameImage, comparison, oneDimensionalComparison] using hEdgeZero j
              · subst ht
                subst hv
                -- The right-endpoint comparison is identical.
                show sameImage (Sum.inr (j, (1 : I))) (Sum.inl (boundary j 1))
                simpa [sameImage, comparison, oneDimensionalComparison] using hEdgeOne j
          | inr jt' =>
              cases hxy
    exact (Equivalence.eqvGen_iff hsame_equiv).1 (Relation.EqvGen.mono hsame_rel hab)
  · intro hab
    cases a with
    | inl v =>
        cases b with
        | inl w =>
            -- Equality on two chosen vertices forces the indices to agree.
            have hvw : v = w := oneDimensionalComparison_vertex_eq_iff.mp hab
            subst hvw
            exact
              (Relation.EqvGen.refl (Sum.inl v) :
                Relation.EqvGen (graphRealizationOfFamilyRel boundary) (Sum.inl v) (Sum.inl v))
        | inr jt =>
            rcases jt with ⟨j, t⟩
            rcases unitInterval_eq_zero_or_eq_one_or_ne_endpoints t with ht | ht | ht
            · subst ht
              -- Reduce the endpoint case to equality of the corresponding chosen vertices.
              have hv0 :
                  comparison (Sum.inl v) = comparison (Sum.inl (boundary j 0)) := by
                calc
                  comparison (Sum.inl v) = comparison (Sum.inr (j, (0 : I))) := hab
                  _ = comparison (Sum.inl (boundary j 0)) := hEdgeZero j
              have hvEq : v = boundary j 0 := oneDimensionalComparison_vertex_eq_iff.mp hv0
              subst hvEq
              exact hLeftRelSymm j
            · subst ht
              -- The right endpoint reduces in the same way.
              have hv1 :
                  comparison (Sum.inl v) = comparison (Sum.inl (boundary j 1)) := by
                calc
                  comparison (Sum.inl v) = comparison (Sum.inr (j, (1 : I))) := hab
                  _ = comparison (Sum.inl (boundary j 1)) := hEdgeOne j
              have hvEq : v = boundary j 1 := oneDimensionalComparison_vertex_eq_iff.mp hv1
              subst hvEq
              exact hRightRelSymm j
            · -- An interior edge point cannot agree with a vertex image.
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior v j ht.1 ht.2) hab)
    | inr jt =>
        rcases jt with ⟨j, t⟩
        cases b with
        | inl v =>
            rcases unitInterval_eq_zero_or_eq_one_or_ne_endpoints t with ht | ht | ht
            · subst ht
              -- Compare the left endpoint against the vertex through the chosen boundary label.
              have hv0 :
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inl v) := by
                calc
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inr (j, (0 : I))) :=
                    (hEdgeZero j).symm
                  _ = comparison (Sum.inl v) := hab
              have hvEq : boundary j 0 = v := oneDimensionalComparison_vertex_eq_iff.mp hv0
              subst hvEq
              exact hLeftRel j
            · subst ht
              -- The right endpoint uses the second boundary vertex instead.
              have hv1 :
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inl v) := by
                calc
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inr (j, (1 : I))) :=
                    (hEdgeOne j).symm
                  _ = comparison (Sum.inl v) := hab
              have hvEq : boundary j 1 = v := oneDimensionalComparison_vertex_eq_iff.mp hv1
              subst hvEq
              exact hRightRel j
            · -- Interior points cannot map to a chosen vertex.
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior v j ht.1 ht.2) hab.symm)
        | inr jt' =>
            rcases jt' with ⟨j', s⟩
            rcases unitInterval_eq_zero_or_eq_one_or_ne_endpoints t with ht | ht | ht <;>
              rcases unitInterval_eq_zero_or_eq_one_or_ne_endpoints s with hs | hs | hs
            · subst ht
              subst hs
              -- Two left endpoints agree exactly when their boundary vertices agree.
              have hvv :
                  comparison (Sum.inl (boundary j 0)) =
                    comparison (Sum.inl (boundary j' 0)) := by
                calc
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inr (j, (0 : I))) :=
                    (hEdgeZero j).symm
                  _ = comparison (Sum.inr (j', (0 : I))) := hab
                  _ = comparison (Sum.inl (boundary j' 0)) := hEdgeZero j'
              have hbdry : boundary j 0 = boundary j' 0 :=
                oneDimensionalComparison_vertex_eq_iff.mp hvv
              exact Relation.EqvGen.trans _ _ _ (hLeftRel j) (by simpa [hbdry] using hLeftRelSymm j')
            · subst ht
              subst hs
              -- Left and right endpoints agree exactly when the chosen boundary vertices agree.
              have hvv :
                  comparison (Sum.inl (boundary j 0)) =
                    comparison (Sum.inl (boundary j' 1)) := by
                calc
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inr (j, (0 : I))) :=
                    (hEdgeZero j).symm
                  _ = comparison (Sum.inr (j', (1 : I))) := hab
                  _ = comparison (Sum.inl (boundary j' 1)) := hEdgeOne j'
              have hbdry : boundary j 0 = boundary j' 1 :=
                oneDimensionalComparison_vertex_eq_iff.mp hvv
              exact Relation.EqvGen.trans _ _ _ (hLeftRel j) (by simpa [hbdry] using hRightRelSymm j')
            · subst ht
              -- An endpoint cannot coincide with an interior point.
              have hcontra :
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inr (j', s)) := by
                calc
                  comparison (Sum.inl (boundary j 0)) = comparison (Sum.inr (j, (0 : I))) :=
                    (hEdgeZero j).symm
                  _ = comparison (Sum.inr (j', s)) := hab
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior
                  (boundary j 0) j' hs.1 hs.2) hcontra)
            · subst ht
              subst hs
              -- The mixed endpoint case is symmetric.
              have hvv :
                  comparison (Sum.inl (boundary j 1)) =
                    comparison (Sum.inl (boundary j' 0)) := by
                calc
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inr (j, (1 : I))) :=
                    (hEdgeOne j).symm
                  _ = comparison (Sum.inr (j', (0 : I))) := hab
                  _ = comparison (Sum.inl (boundary j' 0)) := hEdgeZero j'
              have hbdry : boundary j 1 = boundary j' 0 :=
                oneDimensionalComparison_vertex_eq_iff.mp hvv
              exact Relation.EqvGen.trans _ _ _ (hRightRel j) (by simpa [hbdry] using hLeftRelSymm j')
            · subst ht
              subst hs
              -- Two right endpoints agree through their shared terminal vertex.
              have hvv :
                  comparison (Sum.inl (boundary j 1)) =
                    comparison (Sum.inl (boundary j' 1)) := by
                calc
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inr (j, (1 : I))) :=
                    (hEdgeOne j).symm
                  _ = comparison (Sum.inr (j', (1 : I))) := hab
                  _ = comparison (Sum.inl (boundary j' 1)) := hEdgeOne j'
              have hbdry : boundary j 1 = boundary j' 1 :=
                oneDimensionalComparison_vertex_eq_iff.mp hvv
              exact Relation.EqvGen.trans _ _ _ (hRightRel j) (by simpa [hbdry] using hRightRelSymm j')
            · subst ht
              -- The right endpoint also cannot hit an interior point.
              have hcontra :
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inr (j', s)) := by
                calc
                  comparison (Sum.inl (boundary j 1)) = comparison (Sum.inr (j, (1 : I))) :=
                    (hEdgeOne j).symm
                  _ = comparison (Sum.inr (j', s)) := hab
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior
                  (boundary j 1) j' hs.1 hs.2) hcontra)
            · subst hs
              -- This is the symmetric endpoint-versus-interior contradiction.
              have hcontra :
                  comparison (Sum.inl (boundary j' 0)) = comparison (Sum.inr (j, t)) := by
                calc
                  comparison (Sum.inl (boundary j' 0)) = comparison (Sum.inr (j', (0 : I))) :=
                    (hEdgeZero j').symm
                  _ = comparison (Sum.inr (j, t)) := hab.symm
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior
                  (boundary j' 0) j ht.1 ht.2) hcontra)
            · subst hs
              -- The second symmetric contradiction uses the right endpoint of `j'`.
              have hcontra :
                  comparison (Sum.inl (boundary j' 1)) = comparison (Sum.inr (j, t)) := by
                calc
                  comparison (Sum.inl (boundary j' 1)) = comparison (Sum.inr (j', (1 : I))) :=
                    (hEdgeOne j').symm
                  _ = comparison (Sum.inr (j, t)) := hab.symm
              exact False.elim
                ((oneDimensionalComparison_vertex_ne_edge_of_interior
                  (boundary j' 1) j ht.1 ht.2) hcontra)
            · -- Interior points agree only when both the cell and parameter agree.
              have hEq :
                  j = j' ∧ t = s := (oneDimensionalComparison_edge_eq_iff_of_interior
                  ht.1 ht.2 hs.1 hs.2).mp hab
              rcases hEq with ⟨rfl, rfl⟩
              exact
                (Relation.EqvGen.refl (Sum.inr (j, t)) :
                  Relation.EqvGen (graphRealizationOfFamilyRel boundary)
                    (Sum.inr (j, t)) (Sum.inr (j, t)))

/-- Helper for Example 10.1.8: each closed `1`-cell is the range of the corresponding comparison
edge slice `t ↦ oneDimensionalComparison (Sum.inr (⟨j⟩, t))`. -/
private theorem oneDimensionalComparison_closedCellOne_eq_range
    {X : Type w} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 1 j =
      Set.range (fun t : I ↦ @oneDimensionalComparison X _ _ (Sum.inr (⟨j⟩, t))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Reparameterize the closed-ball point by the shared interval homeomorphism.
    refine ⟨oneCellParamHomeomorph ⟨y, hy⟩, ?_⟩
    simp [oneDimensionalComparison, Topology.CWComplex.map_def]
  · rintro ⟨t, rfl⟩
    -- Unpack the interval parameter back to the closed-ball model of the `1`-cell.
    refine
      ⟨((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ),
        (oneCellParamHomeomorph.symm t).2, ?_⟩
    simp [oneDimensionalComparison, Topology.CWComplex.map_def]

/-- Helper for Example 10.1.8: in a one-dimensional Hausdorff CW complex, the reverse comparison
map is a quotient map once the cell-index types are given the discrete topologies. -/
private theorem oneDimensionalComparison_isQuotientMap
    {X : Type w} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h_dim : Topology.RelCWComplex.dimLE (Set.univ : Set X) 1) :
    let vertexCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 0)
    let edgeCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 1)
    let _ : TopologicalSpace vertexCell := ⊥
    let _ : TopologicalSpace edgeCell := ⊥
    Topology.IsQuotientMap (@oneDimensionalComparison X _ _) := by
  let vertexCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 0)
  let edgeCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 1)
  let _ : TopologicalSpace vertexCell := ⊥
  let _ : TopologicalSpace edgeCell := ⊥
  let _ : DiscreteTopology vertexCell := discreteTopology_bot _
  let _ : DiscreteTopology edgeCell := discreteTopology_bot _
  let comparison : vertexCell ⊕ (edgeCell × I) → X := @oneDimensionalComparison X _ _
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨oneDimensionalComparison_surjective h_dim, ?_⟩
  intro A
  constructor
  · intro hA
    rw [isClosed_sum_iff]
    constructor
    · -- The vertex summand is discrete, so every subset of it is closed.
      exact isClosed_discrete _
    · -- On each edge slice, the comparison map is continuous through the closed-ball model.
      have hEdgeContinuous :
          Continuous (fun p : edgeCell × I ↦ comparison (Sum.inr p)) := by
        rw [continuous_prod_of_discrete_left]
        intro j
        have hMapContinuous :
            Continuous (fun x : oneCellClosedBall ↦ Topology.CWComplex.map 1 j.down x) := by
          -- Restrict the characteristic map to the closed `1`-cell model.
          simpa using (Topology.CWComplex.continuousOn 1 j.down).restrict
        have hEdgeSliceContinuous :
            Continuous
              (fun t : I ↦
                Topology.CWComplex.map 1 j.down
                  (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ))) := by
          -- Compose the restricted characteristic map with the fixed interval homeomorphism.
          change
            Continuous
              ((oneCellClosedBall.restrict (Topology.CWComplex.map 1 j.down)) ∘
                oneCellParamHomeomorph.symm)
          exact hMapContinuous.comp oneCellParamHomeomorph.symm.continuous
        simpa [comparison, oneDimensionalComparison] using hEdgeSliceContinuous
      simpa [comparison] using hA.preimage hEdgeContinuous
  · intro hPreimage
    rw [isClosed_sum_iff] at hPreimage
    apply (Topology.CWComplex.closed (C := (Set.univ : Set X)) A (by simp)).2
    intro n j
    cases n with
    | zero =>
        -- Intersections with closed `0`-cells are intersections with singletons.
        rw [Topology.CWComplex.closedCell_zero_eq_singleton]
        exact isClosed_inter_singleton
    | succ n =>
        cases n with
        | zero =>
            let edgeSlice : I → X := fun t ↦ comparison (Sum.inr (⟨j⟩, t))
            have hSliceContinuous : Continuous edgeSlice := by
              have hMapContinuous :
                  Continuous (fun x : oneCellClosedBall ↦ Topology.CWComplex.map 1 j x) := by
                -- Restrict the characteristic map to the closed `1`-cell model.
                simpa using (Topology.CWComplex.continuousOn 1 j).restrict
              have hEdgeSliceContinuous :
                  Continuous
                    (fun t : I ↦
                      Topology.CWComplex.map 1 j
                        (((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ))) := by
                -- The slice is the characteristic map composed with the interval homeomorphism.
                change
                  Continuous ((oneCellClosedBall.restrict (Topology.CWComplex.map 1 j)) ∘
                    oneCellParamHomeomorph.symm)
                exact hMapContinuous.comp oneCellParamHomeomorph.symm.continuous
              simpa [edgeSlice, comparison, oneDimensionalComparison] using hEdgeSliceContinuous
            have hSlicePreimageClosed : IsClosed (edgeSlice ⁻¹' A) := by
              -- Pull the global closed preimage back along the inclusion `t ↦ (⟨j⟩, t)`.
              simpa [edgeSlice, comparison] using
                hPreimage.2.preimage (continuous_const.prodMk continuous_id)
            have hSliceImageClosed : IsClosed (edgeSlice '' (edgeSlice ⁻¹' A)) := by
              -- A closed subset of the compact interval is compact, and compact sets are closed in
              -- the Hausdorff ambient.
              exact (hSlicePreimageClosed.isCompact.image hSliceContinuous).isClosed
            have hSliceImageEq :
                A ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 1 j =
                  edgeSlice '' (edgeSlice ⁻¹' A) := by
              ext x
              constructor
              · intro hx
                rw [oneDimensionalComparison_closedCellOne_eq_range (X := X) j] at hx
                rcases hx.2 with ⟨t, rfl⟩
                exact ⟨t, hx.1, rfl⟩
              · rintro ⟨t, htA, rfl⟩
                rw [oneDimensionalComparison_closedCellOne_eq_range (X := X) j]
                exact ⟨htA, ⟨t, rfl⟩⟩
            rw [hSliceImageEq]
            exact hSliceImageClosed
        | succ n =>
            -- Higher-dimensional cells do not exist when the CW structure has dimension at most
            -- `1`.
            have hEmpty :
                IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) (n.succ.succ)) :=
              Topology.CWComplex.isEmpty_cell_of_one_lt_of_dimLE_one h_dim (n.succ.succ)
                (Nat.succ_lt_succ (Nat.zero_lt_succ n))
            exact (hEmpty.false j).elim

/-- Helper for Example 10.1.8: the graph-realization CW model uses lifted vertices in degree `0`,
lifted edges in degree `1`, and no higher-dimensional cells. -/
private def graphRealizationOfFamilyCell (X₀ : Type u) (J : Type v) : ℕ → Type (max u v)
  | 0 => ULift X₀
  | 1 => ULift J
  | _ + 2 => PEmpty

/-- Helper for Example 10.1.8: the vertex cells of the graph realization are singleton
characteristic maps. -/
private def graphRealizationOfFamilyZeroCellMap
    (boundary : J → Fin 2 → X₀) (x : X₀) :
    PartialEquiv (Fin 0 → ℝ) (graphRealizationOfFamily boundary) :=
  PartialEquiv.single 0 (graphRealizationOfFamilyVertex boundary x)

/-- Helper for Example 10.1.8: the `0`-cell source is the standard open ball in `Fin 0 → ℝ`. -/
private theorem graphRealizationOfFamilyZeroCellMap_source_eq
    (boundary : J → Fin 2 → X₀) :
    ∀ x : X₀,
      (graphRealizationOfFamilyZeroCellMap boundary x).source = Metric.ball 0 1 := by
  intro x
  -- In dimension `0`, both sides are the singleton empty tuple.
  ext y
  simp [graphRealizationOfFamilyZeroCellMap, Matrix.empty_eq]

/-- Helper for Example 10.1.8: each vertex characteristic map is continuous on the closed
`0`-cell model. -/
private theorem graphRealizationOfFamilyZeroCellMap_continuousOn
    (boundary : J → Fin 2 → X₀) :
    ∀ x : X₀,
      ContinuousOn (graphRealizationOfFamilyZeroCellMap boundary x) (Metric.closedBall 0 1) := by
  intro x
  -- The `0`-cell map is constant.
  simpa [graphRealizationOfFamilyZeroCellMap] using
    (continuous_const.continuousOn :
      ContinuousOn (Function.const (Fin 0 → ℝ) (graphRealizationOfFamilyVertex boundary x))
        (Metric.closedBall 0 1))

/-- Helper for Example 10.1.8: the inverse of a vertex characteristic map is continuous on its
singleton target. -/
private theorem graphRealizationOfFamilyZeroCellMap_continuousOn_symm
    (boundary : J → Fin 2 → X₀) :
    ∀ x : X₀,
      ContinuousOn
        (graphRealizationOfFamilyZeroCellMap boundary x).symm
        (graphRealizationOfFamilyZeroCellMap boundary x).target := by
  intro x
  -- The inverse is again constant because the target is a singleton.
  simpa [graphRealizationOfFamilyZeroCellMap] using
    (continuous_const.continuousOn :
      ContinuousOn
        (Function.const (graphRealizationOfFamily boundary) (0 : Fin 0 → ℝ))
        {graphRealizationOfFamilyVertex boundary x})

/-- Helper for Example 10.1.8: the closed `1`-cell map is the edge parameterization composed with
the common closed-ball/unit-interval homeomorphism. -/
private noncomputable def graphRealizationOfFamilyOneCellClosedMap
    (boundary : J → Fin 2 → X₀) (j : J) :
    oneCellClosedBall → graphRealizationOfFamily boundary :=
  fun x ↦ graphRealizationOfFamilyEdgeMap boundary j (oneCellParamHomeomorph x)

/-- Helper for Example 10.1.8: the closed `1`-cell map is continuous. -/
private theorem graphRealizationOfFamilyOneCellClosedMap_continuous
    (boundary : J → Fin 2 → X₀) (j : J) :
    Continuous (graphRealizationOfFamilyOneCellClosedMap boundary j) := by
  -- This is the continuous edge parameterization through the fixed closed-ball model.
  exact (graphRealizationOfFamilyEdgePoint_continuous boundary j).comp
    oneCellParamHomeomorph.continuous

/-- Helper for Example 10.1.8: on the open-ball source, the open graph-edge chart is the closed
edge parameterization restricted to the ambient open ball. -/
private theorem graphRealizationOfFamilyOneCellOpenPartialHomeomorph_apply
    (boundary : J → Fin 2 → X₀) (j : J) (x : oneCellOpenBall) :
    graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j x =
      graphRealizationOfFamilyOneCellClosedMap boundary j
        ⟨x.1, Metric.ball_subset_closedBall x.2⟩ := by
  -- The composite open chart is definitionally the interior-edge map after the fixed
  -- open-ball/interior-interval reparameterization.
  rfl

/-- Helper for Example 10.1.8: the ambient total map for the `j`th graph edge agrees with the
closed-ball parameterization on `Metric.closedBall 0 1` and uses the left endpoint as fallback
outside. -/
private noncomputable def graphRealizationOfFamilyOneCellValue
    (boundary : J → Fin 2 → X₀) (j : J) :
    (Fin 1 → ℝ) → graphRealizationOfFamily boundary :=
  let _ : DecidablePred
      (fun x : Fin 1 → ℝ ↦ x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1) :=
    Classical.decPred _
  fun x ↦
    if hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 then
      graphRealizationOfFamilyOneCellClosedMap boundary j ⟨x, hx⟩
    else
      graphRealizationOfFamilyEdgePoint boundary j 0

/-- Helper for Example 10.1.8: the inverse branch of the graph `1`-cell characteristic map is the
existing open-edge chart inverse, viewed in the ambient `Fin 1 → ℝ`. -/
private noncomputable def graphRealizationOfFamilyOneCellInverse
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamily boundary → (Fin 1 → ℝ) :=
  fun y ↦
    ((graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).symm y :
      oneCellOpenBall)

/-- Helper for Example 10.1.8: on the source ball, the ambient total map is exactly the open-edge
chart. -/
private theorem graphRealizationOfFamilyOneCellValue_apply_of_mem_ball
    (boundary : J → Fin 2 → X₀) (j : J) {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    graphRealizationOfFamilyOneCellValue boundary j x =
      graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j ⟨x, hx⟩ := by
  -- On the open ball the ambient map takes the closed-ball branch, so it reduces to the open-edge
  -- chart comparison proved above.
  rw [graphRealizationOfFamilyOneCellOpenPartialHomeomorph_apply]
  unfold graphRealizationOfFamilyOneCellValue
  split_ifs with hClosed
  · rfl
  · exact (hClosed (Metric.ball_subset_closedBall hx)).elim

/-- Helper for Example 10.1.8: source points of the ambient graph `1`-cell map land in the open
edge target. -/
private theorem graphRealizationOfFamilyOneCellValue_map_source
    (boundary : J → Fin 2 → X₀) (j : J) :
    ∀ ⦃x : Fin 1 → ℝ⦄, x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 →
      graphRealizationOfFamilyOneCellValue boundary j x ∈
        (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).target := by
  intro x hx
  -- Rewrite to the genuine open chart and use its source-to-target mapping property.
  rw [graphRealizationOfFamilyOneCellValue_apply_of_mem_ball boundary j hx]
  exact
    (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).map_source <| by
      simp [graphRealizationOfFamilyOneCellOpenPartialHomeomorph, OpenPartialHomeomorph.trans_source]

/-- Helper for Example 10.1.8: target points of the graph `1`-cell map pull back to the open
source ball. -/
private theorem graphRealizationOfFamilyOneCellInverse_map_target
    (boundary : J → Fin 2 → X₀) (j : J) :
    ∀ ⦃y : graphRealizationOfFamily boundary⦄,
      y ∈ (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).target →
        graphRealizationOfFamilyOneCellInverse boundary j y ∈
          Metric.ball (0 : Fin 1 → ℝ) 1 := by
  intro y hy
  exact ((graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).symm y).2

/-- Helper for Example 10.1.8: the ambient graph `1`-cell map has the open-edge chart as inverse
on the source ball. -/
private theorem graphRealizationOfFamilyOneCellInverse_left_inv
    (boundary : J → Fin 2 → X₀) (j : J) :
    ∀ ⦃x : Fin 1 → ℝ⦄, x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 →
      graphRealizationOfFamilyOneCellInverse boundary j
          (graphRealizationOfFamilyOneCellValue boundary j x) = x := by
  intro x hx
  -- After identifying the ambient branch with the open chart, this is the chart's left inverse.
  rw [graphRealizationOfFamilyOneCellValue_apply_of_mem_ball boundary j hx]
  simpa [graphRealizationOfFamilyOneCellInverse] using
    congrArg (fun z : oneCellOpenBall ↦ (z : Fin 1 → ℝ))
      ((graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).left_inv <| by
        simp [graphRealizationOfFamilyOneCellOpenPartialHomeomorph,
          OpenPartialHomeomorph.trans_source])

/-- Helper for Example 10.1.8: on its target, the ambient graph `1`-cell map is the inverse of
the open-edge chart. -/
private theorem graphRealizationOfFamilyOneCellInverse_right_inv
    (boundary : J → Fin 2 → X₀) (j : J) :
    ∀ ⦃y : graphRealizationOfFamily boundary⦄,
      y ∈ (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).target →
        graphRealizationOfFamilyOneCellValue boundary j
            (graphRealizationOfFamilyOneCellInverse boundary j y) = y := by
  intro y hy
  -- The inverse point lies back in the source ball, so the ambient map again reduces to the open
  -- chart before applying the right-inverse law.
  rw [graphRealizationOfFamilyOneCellValue_apply_of_mem_ball boundary j
    (graphRealizationOfFamilyOneCellInverse_map_target boundary j hy)]
  simpa [graphRealizationOfFamilyOneCellInverse] using
    (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).right_inv hy

/-- Helper for Example 10.1.8: the `j`th graph edge admits an ambient `PartialEquiv` with source
`Metric.ball 0 1` and target equal to the open edge image. -/
private noncomputable def graphRealizationOfFamilyOneCellMap
    (boundary : J → Fin 2 → X₀) (j : J) :
    PartialEquiv (Fin 1 → ℝ) (graphRealizationOfFamily boundary) :=
  { toFun := graphRealizationOfFamilyOneCellValue boundary j
    invFun := graphRealizationOfFamilyOneCellInverse boundary j
    source := Metric.ball (0 : Fin 1 → ℝ) 1
    target := (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).target
    map_source' := graphRealizationOfFamilyOneCellValue_map_source boundary j
    map_target' := graphRealizationOfFamilyOneCellInverse_map_target boundary j
    left_inv' := graphRealizationOfFamilyOneCellInverse_left_inv boundary j
    right_inv' := graphRealizationOfFamilyOneCellInverse_right_inv boundary j }

/-- Helper for Example 10.1.8: the ambient graph `1`-cell map uses the standard open ball as its
source. -/
private theorem graphRealizationOfFamilyOneCellMap_source_eq
    (boundary : J → Fin 2 → X₀) (j : J) :
    (graphRealizationOfFamilyOneCellMap boundary j).source = Metric.ball (0 : Fin 1 → ℝ) 1 := by
  rfl

/-- Helper for Example 10.1.8: the ambient graph `1`-cell map is continuous on the closed unit
ball. -/
private theorem graphRealizationOfFamilyOneCellMap_continuousOn
    (boundary : J → Fin 2 → X₀) (j : J) :
    ContinuousOn (graphRealizationOfFamilyOneCellMap boundary j)
      (Metric.closedBall (0 : Fin 1 → ℝ) 1) := by
  -- On the closed ball the ambient map is literally the closed-ball edge parameterization.
  rw [continuousOn_iff_continuous_restrict]
  convert graphRealizationOfFamilyOneCellClosedMap_continuous boundary j using 1
  ext x
  -- The restricted point already lies in the closed ball, so the ambient map can only use the
  -- closed-ball branch.
  change graphRealizationOfFamilyOneCellValue boundary j x.1 =
    graphRealizationOfFamilyOneCellClosedMap boundary j x
  unfold graphRealizationOfFamilyOneCellValue
  split_ifs with h
  · rfl
  · exact (h x.2).elim

/-- Helper for Example 10.1.8: the inverse branch of the ambient graph `1`-cell map is continuous
on the open edge target. -/
private theorem graphRealizationOfFamilyOneCellMap_continuousOn_symm
    (boundary : J → Fin 2 → X₀) (j : J) :
    ContinuousOn
      (graphRealizationOfFamilyOneCellMap boundary j).symm
      (graphRealizationOfFamilyOneCellMap boundary j).target := by
  -- The inverse branch is the open-edge chart inverse followed by the subtype inclusion into the
  -- ambient `Fin 1 → ℝ`.
  simpa [graphRealizationOfFamilyOneCellMap, graphRealizationOfFamilyOneCellInverse] using
    continuous_subtype_val.comp_continuousOn
      ((graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).continuousOn_symm)

/-- Helper for Example 10.1.8: the target of the ambient graph `1`-cell map is exactly the `j`th
open edge interior. -/
private theorem graphRealizationOfFamilyOneCellMap_target_eq_range
    (boundary : J → Fin 2 → X₀) (j : J) :
    (graphRealizationOfFamilyOneCellMap boundary j).target =
      Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary j) := by
  -- The ambient target is inherited from the composite open chart, so `trans_target''` reduces it
  -- to the image of the interior-edge embedding on its full source.
  change (graphRealizationOfFamilyOneCellOpenPartialHomeomorph boundary j).target =
    Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary j)
  rw [graphRealizationOfFamilyOneCellOpenPartialHomeomorph, OpenPartialHomeomorph.trans_target'']
  ext y
  simp

/-- Helper for Example 10.1.8: the closed-ball image of the ambient graph `1`-cell map is the
whole closed edge slice. -/
private theorem graphRealizationOfFamilyOneCellMap_image_closedBall
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamilyOneCellMap boundary j '' Metric.closedBall 0 1 =
      Set.range (graphRealizationOfFamilyEdgeMap boundary j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- On the closed ball the ambient map is exactly the closed-edge parameterization.
    refine ⟨oneCellParamHomeomorph ⟨x, hx⟩, ?_⟩
    change
      graphRealizationOfFamilyEdgeMap boundary j (oneCellParamHomeomorph ⟨x, hx⟩) =
        graphRealizationOfFamilyOneCellValue boundary j x
    unfold graphRealizationOfFamilyOneCellValue
    rw [dif_pos hx]
    rfl
  · rintro ⟨t, rfl⟩
    -- Every edge point comes from the closed-ball model through `oneCellParamHomeomorph.symm`.
    refine ⟨((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ),
      (oneCellParamHomeomorph.symm t).2, ?_⟩
    change
      graphRealizationOfFamilyOneCellValue boundary j
          ((oneCellParamHomeomorph.symm t : oneCellClosedBall) : Fin 1 → ℝ) =
        graphRealizationOfFamilyEdgeMap boundary j t
    unfold graphRealizationOfFamilyOneCellValue
    rw [dif_pos (oneCellParamHomeomorph.symm t).2]
    simpa [graphRealizationOfFamilyOneCellClosedMap, graphRealizationOfFamilyEdgeMap] using
      congrArg (graphRealizationOfFamilyEdgeMap boundary j) (oneCellParamHomeomorph.right_inv t)

/-- Helper for Example 10.1.8: a boundary point of the closed `1`-cell model is one of the two
distinguished endpoints. -/
private theorem oneCellClosedBall_eq_left_or_right_of_mem_sphere
    {x : oneCellClosedBall}
    (hx : ((x : oneCellClosedBall) : Fin 1 → ℝ) ∈ Metric.sphere (0 : Fin 1 → ℝ) 1) :
    x = oneCellLeftPoint ∨ x = oneCellRightPoint := by
  -- Read the unique coordinate of the boundary point and solve `|x 0| = 1`.
  have hnorm : ‖((x : oneCellClosedBall) : Fin 1 → ℝ)‖ = 1 := by
    simpa [Metric.sphere, Metric.mem_sphere, dist_eq_norm] using hx
  have hcoord_le : ‖((x : oneCellClosedBall) : Fin 1 → ℝ) 0‖ ≤ 1 := by
    exact (pi_norm_le_iff_of_nonneg zero_le_one).1 (le_of_eq hnorm) 0
  have hnorm_le_coord : ‖((x : oneCellClosedBall) : Fin 1 → ℝ)‖ ≤ ‖((x : oneCellClosedBall) : Fin 1 → ℝ) 0‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact le_rfl
  have hcoord_norm : ‖((x : oneCellClosedBall) : Fin 1 → ℝ) 0‖ = 1 := by
    exact le_antisymm hcoord_le (by simpa [hnorm] using hnorm_le_coord)
  have habs :
      |((x : oneCellClosedBall) : Fin 1 → ℝ) 0| = 1 := by
    simpa [Real.norm_eq_abs] using hcoord_norm
  have hsq : ((((x : oneCellClosedBall) : Fin 1 → ℝ) 0) : ℝ) ^ 2 = 1 := by
    have habs_sq := congrArg (fun t : ℝ ↦ t ^ 2) habs
    simpa [sq_abs] using habs_sq
  have hcoord :
      (((x : oneCellClosedBall) : Fin 1 → ℝ) 0) = -1 ∨
        (((x : oneCellClosedBall) : Fin 1 → ℝ) 0) = 1 := by
    by_cases h1 : (((x : oneCellClosedBall) : Fin 1 → ℝ) 0) = 1
    · exact Or.inr h1
    · have hm1 : (((x : oneCellClosedBall) : Fin 1 → ℝ) 0) = -1 := by
        have hfac :
            ((((x : oneCellClosedBall) : Fin 1 → ℝ) 0) - 1) *
                ((((x : oneCellClosedBall) : Fin 1 → ℝ) 0) + 1) = 0 := by
          nlinarith [hsq]
        have hneq : (((x : oneCellClosedBall) : Fin 1 → ℝ) 0) - 1 ≠ 0 := by
          intro hzero
          apply h1
          linarith
        have hsum : ((((x : oneCellClosedBall) : Fin 1 → ℝ) 0) + 1) = 0 := by
          exact (eq_zero_or_eq_zero_of_mul_eq_zero hfac).resolve_left hneq
        linarith
      exact Or.inl hm1
  rcases hcoord with hleft | hright
  · left
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa [oneCellLeftPoint] using hleft
  · right
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa [oneCellRightPoint] using hright

/-- Helper for Example 10.1.8: the boundary sphere of the graph `1`-cell model maps exactly to
the two endpoint vertices of that edge. -/
private theorem graphRealizationOfFamilyOneCellMap_image_sphere
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamilyOneCellMap boundary j '' Metric.sphere 0 1 =
      {graphRealizationOfFamilyVertex boundary (boundary j 0),
        graphRealizationOfFamilyVertex boundary (boundary j 1)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxClosed : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 :=
      Metric.sphere_subset_closedBall hx
    have hEndpoint :
        (⟨x, hxClosed⟩ : oneCellClosedBall) = oneCellLeftPoint ∨
          (⟨x, hxClosed⟩ : oneCellClosedBall) = oneCellRightPoint :=
      oneCellClosedBall_eq_left_or_right_of_mem_sphere hx
    -- A sphere point is one of the two distinguished endpoints of the closed-ball model.
    change
      graphRealizationOfFamilyOneCellValue boundary j x ∈
        {graphRealizationOfFamilyVertex boundary (boundary j 0),
          graphRealizationOfFamilyVertex boundary (boundary j 1)}
    unfold graphRealizationOfFamilyOneCellValue
    rw [dif_pos hxClosed]
    rcases hEndpoint with hLeft | hRight
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      simpa [graphRealizationOfFamilyOneCellClosedMap, graphRealizationOfFamilyEdgeMap,
        hLeft, oneCellParamHomeomorph_left] using graphRealizationOfFamilyEdgeMap_zero boundary j
    · right
      simp only [Set.mem_singleton_iff]
      simpa [graphRealizationOfFamilyOneCellClosedMap, graphRealizationOfFamilyEdgeMap,
        hRight, oneCellParamHomeomorph_right] using graphRealizationOfFamilyEdgeMap_one boundary j
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · refine ⟨((oneCellLeftPoint : oneCellClosedBall) : Fin 1 → ℝ), oneCellLeftPoint_mem_sphere, ?_⟩
      -- The left endpoint is represented by the left boundary point of the model edge.
      change
        graphRealizationOfFamilyOneCellValue boundary j ((oneCellLeftPoint : oneCellClosedBall) : Fin 1 → ℝ) =
          graphRealizationOfFamilyVertex boundary (boundary j 0)
      unfold graphRealizationOfFamilyOneCellValue
      rw [dif_pos (Metric.sphere_subset_closedBall oneCellLeftPoint_mem_sphere)]
      simpa [graphRealizationOfFamilyOneCellClosedMap, graphRealizationOfFamilyEdgeMap,
        oneCellParamHomeomorph_left] using graphRealizationOfFamilyEdgeMap_zero boundary j
    · refine ⟨((oneCellRightPoint : oneCellClosedBall) : Fin 1 → ℝ), oneCellRightPoint_mem_sphere, ?_⟩
      -- The right endpoint is represented by the right boundary point of the model edge.
      change
        graphRealizationOfFamilyOneCellValue boundary j ((oneCellRightPoint : oneCellClosedBall) : Fin 1 → ℝ) =
          graphRealizationOfFamilyVertex boundary (boundary j 1)
      unfold graphRealizationOfFamilyOneCellValue
      rw [dif_pos (Metric.sphere_subset_closedBall oneCellRightPoint_mem_sphere)]
      simpa [graphRealizationOfFamilyOneCellClosedMap, graphRealizationOfFamilyEdgeMap,
        oneCellParamHomeomorph_right] using graphRealizationOfFamilyEdgeMap_one boundary j

/-- Helper for Example 10.1.8: if every vertex slice and every closed edge slice of a graph
realization is closed, then the ambient subset is closed. -/
private theorem graphRealizationOfFamilyClosed_of_cellwiseClosed
    (boundary : J → Fin 2 → X₀) {A : Set (graphRealizationOfFamily boundary)}
    (hVertex :
      ∀ x : X₀,
        IsClosed (A ∩ {graphRealizationOfFamilyVertex boundary x}))
    (hEdge :
      ∀ j : J,
        IsClosed (A ∩ Set.range (graphRealizationOfFamilyEdgeMap boundary j))) :
    IsClosed A := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let q :
      X₀ ⊕ (J × I) → graphRealizationOfFamily boundary :=
    Quotient.mk' (s := graphRealizationOfFamilySetoid boundary)
  -- Use the quotient characterization and analyze the left and right source summands separately.
  rw [← (graphRealizationOfFamily_isQuotientMap boundary).isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · -- The vertex source is discrete, so every subset is closed.
    let _ : TopologicalSpace X₀ := ⊥
    let _ : DiscreteTopology X₀ := discreteTopology_bot _
    exact isClosed_discrete _
  · let _ : TopologicalSpace J := ⊥
    let _ : DiscreteTopology J := discreteTopology_bot _
    change IsClosed ((fun p : J × I ↦ q (Sum.inr p)) ⁻¹' A)
    rw [← isOpen_compl_iff, isOpen_prod_iff]
    intro j t hp
    have hFiberClosed :
        IsClosed ((graphRealizationOfFamilyEdgePoint boundary j) ⁻¹' A) := by
      have hPreimageEq :
          (graphRealizationOfFamilyEdgePoint boundary j) ⁻¹' A =
            (graphRealizationOfFamilyEdgePoint boundary j) ⁻¹'
              (A ∩ Set.range (graphRealizationOfFamilyEdgeMap boundary j)) := by
        ext s
        constructor
        · intro hs
          exact ⟨hs, ⟨s, rfl⟩⟩
        · intro hs
          exact hs.1
      rw [hPreimageEq]
      exact (hEdge j).preimage (graphRealizationOfFamilyEdgePoint_continuous boundary j)
    refine
      ⟨({j} : Set J), ((graphRealizationOfFamilyEdgePoint boundary j) ⁻¹' A)ᶜ,
        isOpen_discrete _, hFiberClosed.isOpen_compl, by simp, hp, ?_⟩
    rintro ⟨j', s⟩ hs
    rcases hs with ⟨hj', hs⟩
    simp at hj'
    subst hj'
    simpa using hs

/-- Helper for Example 10.1.8: the degree-wise graph cell family uses the explicit vertex and edge
characteristic maps, and has no higher-dimensional cells. -/
private noncomputable def graphRealizationOfFamilyCellMap
    (boundary : J → Fin 2 → X₀) :
    (n : ℕ) → graphRealizationOfFamilyCell X₀ J n →
      PartialEquiv (Fin n → ℝ) (graphRealizationOfFamily boundary)
  | 0, i => graphRealizationOfFamilyZeroCellMap boundary i.down
  | 1, i => graphRealizationOfFamilyOneCellMap boundary i.down
  | _ + 2, i => nomatch i

/-- Helper for Example 10.1.8: each vertex open cell is exactly the singleton consisting of that
vertex. -/
private theorem graphRealizationOfFamilyZeroCellMap_image_ball
    (boundary : J → Fin 2 → X₀) (x : X₀) :
    graphRealizationOfFamilyZeroCellMap boundary x '' Metric.ball 0 1 =
      {graphRealizationOfFamilyVertex boundary x} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    -- The `0`-cell map is constant on the unique open-ball point.
    simp [graphRealizationOfFamilyZeroCellMap]
  · intro hy
    -- The unique `0`-ball point maps to the chosen vertex.
    refine ⟨0, by simp, ?_⟩
    simpa [graphRealizationOfFamilyZeroCellMap] using hy.symm

/-- Helper for Example 10.1.8: each vertex closed cell is exactly the singleton consisting of
that vertex. -/
private theorem graphRealizationOfFamilyZeroCellMap_image_closedBall
    (boundary : J → Fin 2 → X₀) (x : X₀) :
    graphRealizationOfFamilyZeroCellMap boundary x '' Metric.closedBall 0 1 =
      {graphRealizationOfFamilyVertex boundary x} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    -- The `0`-cell map is constant on the unique closed-ball point.
    simp [graphRealizationOfFamilyZeroCellMap]
  · intro hy
    -- The unique closed-ball point maps to the chosen vertex.
    refine ⟨0, by simp, ?_⟩
    simpa [graphRealizationOfFamilyZeroCellMap] using hy.symm

/-- Helper for Example 10.1.8: the open image of a graph `1`-cell is exactly the corresponding
open edge interior. -/
private theorem graphRealizationOfFamilyOneCellMap_image_ball
    (boundary : J → Fin 2 → X₀) (j : J) :
    graphRealizationOfFamilyOneCellMap boundary j '' Metric.ball 0 1 =
      Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary j) := by
  -- First identify the open-ball image with the `PartialEquiv` target, then rewrite that target
  -- to the normalized range formula.
  calc
    graphRealizationOfFamilyOneCellMap boundary j '' Metric.ball 0 1 =
        (graphRealizationOfFamilyOneCellMap boundary j).target := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact (graphRealizationOfFamilyOneCellMap boundary j).map_source hx
          · intro hy
            refine ⟨graphRealizationOfFamilyOneCellInverse boundary j y, ?_, ?_⟩
            · exact graphRealizationOfFamilyOneCellInverse_map_target boundary j hy
            · exact graphRealizationOfFamilyOneCellInverse_right_inv boundary j hy
    _ = Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary j) :=
      graphRealizationOfFamilyOneCellMap_target_eq_range boundary j

/-- Helper for Example 10.1.8: the graph-side cell maps all use the standard open ball as their
source. -/
private theorem graphRealizationOfFamilyCWComplex_source_eq
    (boundary : J → Fin 2 → X₀) :
    ∀ n (i : graphRealizationOfFamilyCell X₀ J n),
      (graphRealizationOfFamilyCellMap boundary n i).source = Metric.ball 0 1 := by
  intro n i
  cases n with
  | zero =>
      -- Degree `0` uses the singleton vertex charts.
      simpa [graphRealizationOfFamilyCellMap] using
        graphRealizationOfFamilyZeroCellMap_source_eq boundary i.down
  | succ n =>
      cases n with
      | zero =>
          -- Degree `1` uses the normalized open edge charts.
          simpa [graphRealizationOfFamilyCellMap] using
            graphRealizationOfFamilyOneCellMap_source_eq boundary i.down
      | succ n =>
          -- There are no graph cells in degree at least `2`.
          exact PEmpty.elim i

/-- Helper for Example 10.1.8: every graph-side characteristic map is continuous on the closed
ball model. -/
private theorem graphRealizationOfFamilyCWComplex_continuousOn
    (boundary : J → Fin 2 → X₀) :
    ∀ n (i : graphRealizationOfFamilyCell X₀ J n),
      ContinuousOn (graphRealizationOfFamilyCellMap boundary n i) (Metric.closedBall 0 1) := by
  intro n i
  cases n with
  | zero =>
      -- Degree `0` is the constant singleton chart.
      simpa [graphRealizationOfFamilyCellMap] using
        graphRealizationOfFamilyZeroCellMap_continuousOn boundary i.down
  | succ n =>
      cases n with
      | zero =>
          -- Degree `1` is the normalized closed-edge chart.
          simpa [graphRealizationOfFamilyCellMap] using
            graphRealizationOfFamilyOneCellMap_continuousOn boundary i.down
      | succ n =>
          -- There are no higher-dimensional graph cells.
          exact PEmpty.elim i

/-- Helper for Example 10.1.8: each graph-side inverse chart is continuous on its target. -/
private theorem graphRealizationOfFamilyCWComplex_continuousOn_symm
    (boundary : J → Fin 2 → X₀) :
    ∀ n (i : graphRealizationOfFamilyCell X₀ J n),
      ContinuousOn (graphRealizationOfFamilyCellMap boundary n i).symm
        (graphRealizationOfFamilyCellMap boundary n i).target := by
  intro n i
  cases n with
  | zero =>
      -- Degree `0` has constant inverse chart on its singleton target.
      simpa [graphRealizationOfFamilyCellMap] using
        graphRealizationOfFamilyZeroCellMap_continuousOn_symm boundary i.down
  | succ n =>
      cases n with
      | zero =>
          -- Degree `1` uses the inverse of the normalized open edge chart.
          simpa [graphRealizationOfFamilyCellMap] using
            graphRealizationOfFamilyOneCellMap_continuousOn_symm boundary i.down
      | succ n =>
          -- There are no higher-dimensional graph cells.
          exact PEmpty.elim i

/-- Helper for Example 10.1.8: the graph-side open cells are pairwise disjoint in the normalized
vertex/interior-edge forms. -/
private theorem graphRealizationOfFamilyCWComplex_pairwiseDisjoint
    (boundary : J → Fin 2 → X₀) :
    (Set.univ : Set (Σ n, graphRealizationOfFamilyCell X₀ J n)).PairwiseDisjoint
      (fun ni ↦ graphRealizationOfFamilyCellMap boundary ni.1 ni.2 '' Metric.ball 0 1) := by
  intro ni _ nj _ hne
  rcases ni with ⟨n, i⟩
  rcases nj with ⟨m, j⟩
  -- Route correction: normalize each graph open cell once, then use the quotient separation
  -- lemmas on vertices and interior edge points.
  change Disjoint
      (graphRealizationOfFamilyCellMap boundary n i '' Metric.ball (0 : Fin n → ℝ) 1)
      (graphRealizationOfFamilyCellMap boundary m j '' Metric.ball (0 : Fin m → ℝ) 1)
  cases n with
  | zero =>
      cases m with
      | zero =>
          rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_ball]
          rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_ball]
          refine Set.disjoint_left.2 ?_
          intro y hyi hyj
          simp only [Set.mem_singleton_iff] at hyi hyj
          have hij :
              i.down = j.down :=
            (graphRealizationOfFamily_vertex_eq_iff boundary).1 (hyi.symm.trans hyj)
          apply hne
          cases i
          cases j
          cases hij
          rfl
      | succ m =>
          cases m with
          | zero =>
              rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_ball]
              rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyOneCellMap_image_ball]
              refine Set.disjoint_left.2 ?_
              intro y hyi hyj
              simp only [Set.mem_singleton_iff] at hyi
              rcases hyj with ⟨t, rfl⟩
              exact
                (graphRealizationOfFamily_vertex_ne_edgePoint_of_interior boundary i.down j.down
                  t.1 t.2.1 t.2.2) <|
                  by simpa [graphRealizationOfFamilyEdgeInteriorMap] using hyi.symm
          | succ m =>
              exact PEmpty.elim j
  | succ n =>
      cases n with
      | zero =>
          cases m with
          | zero =>
              let hOneImage :
                  graphRealizationOfFamilyCellMap boundary (0 + 1) i '' Metric.ball 0 1 =
                    Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary i.down) := by
                simpa [graphRealizationOfFamilyCellMap] using
                  graphRealizationOfFamilyOneCellMap_image_ball boundary i.down
              rw [hOneImage]
              rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_ball]
              refine Set.disjoint_left.2 ?_
              intro y hyi hyj
              rcases hyi with ⟨t, rfl⟩
              simp only [Set.mem_singleton_iff] at hyj
              exact
                (graphRealizationOfFamily_vertex_ne_edgePoint_of_interior boundary j.down i.down
                  t.1 t.2.1 t.2.2) <|
                  by simpa [graphRealizationOfFamilyEdgeInteriorMap] using hyj.symm
          | succ m =>
              cases m with
              | zero =>
                  let hLeftImage :
                      graphRealizationOfFamilyCellMap boundary (0 + 1) i '' Metric.ball 0 1 =
                        Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary i.down) := by
                    simpa [graphRealizationOfFamilyCellMap] using
                      graphRealizationOfFamilyOneCellMap_image_ball boundary i.down
                  let hRightImage :
                      graphRealizationOfFamilyCellMap boundary (0 + 1) j '' Metric.ball 0 1 =
                        Set.range (graphRealizationOfFamilyEdgeInteriorMap boundary j.down) := by
                    simpa [graphRealizationOfFamilyCellMap] using
                      graphRealizationOfFamilyOneCellMap_image_ball boundary j.down
                  rw [hLeftImage, hRightImage]
                  refine Set.disjoint_left.2 ?_
                  intro y hyi hyj
                  rcases hyi with ⟨t, rfl⟩
                  rcases hyj with ⟨s, hs⟩
                  have hij :
                      i.down = j.down := by
                    have hEq :
                        i.down = j.down ∧ t.1 = s.1 :=
                      (graphRealizationOfFamily_edgePoint_eq_iff_of_interior boundary
                        t.2.1 t.2.2 s.2.1 s.2.2).1 <|
                        by simpa [graphRealizationOfFamilyEdgeInteriorMap] using hs.symm
                    exact hEq.1
                  apply hne
                  cases i
                  cases j
                  cases hij
                  rfl
              | succ m =>
                  exact PEmpty.elim j
      | succ n =>
          exact PEmpty.elim i

/-- Helper for Example 10.1.8: each graph-side cell frontier lands in finitely many lower-degree
closed cells. -/
private theorem graphRealizationOfFamilyCWComplex_mapsTo
    (boundary : J → Fin 2 → X₀) :
    ∀ n (i : graphRealizationOfFamilyCell X₀ J n),
      ∃ idx : Π m, Finset (graphRealizationOfFamilyCell X₀ J m),
      Set.MapsTo (graphRealizationOfFamilyCellMap boundary n i) (Metric.sphere 0 1)
        (⋃ (m < n) (j ∈ idx m), graphRealizationOfFamilyCellMap boundary m j '' Metric.closedBall 0 1) := by
  classical
  intro n i
  cases n with
  | zero =>
      -- The `0`-sphere is empty, so the frontier condition is vacuous.
      refine ⟨fun _ ↦ ∅, ?_⟩
      rw [Set.mapsTo_iff_image_subset]
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxFalse : False := by
        have hzero : x = 0 := by
          ext a
          exact Fin.elim0 a
        have : (0 : ℝ) = 1 := by
          simpa [Metric.sphere, hzero] using hx
        norm_num at this
      exact hxFalse.elim
  | succ n =>
      cases n with
      | zero =>
          let idx : Π m, Finset (graphRealizationOfFamilyCell X₀ J m)
            | 0 => {⟨boundary i.down 0⟩, ⟨boundary i.down 1⟩}
            | _ + 1 => ∅
          refine ⟨idx, ?_⟩
          rw [Set.mapsTo_iff_image_subset]
          intro y hy
          have hy' := hy
          rw [graphRealizationOfFamilyCellMap,
            graphRealizationOfFamilyOneCellMap_image_sphere boundary i.down] at hy'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
          rcases hy' with rfl | rfl
          · -- The left endpoint lands in the left vertex closed `0`-cell.
            simp only [Set.mem_iUnion, exists_prop]
            refine ⟨0, Nat.zero_lt_one, ⟨boundary i.down 0⟩, by simp [idx], ?_⟩
            rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_closedBall]
            simp
          · -- The right endpoint lands in the right vertex closed `0`-cell.
            simp only [Set.mem_iUnion, exists_prop]
            refine ⟨0, Nat.zero_lt_one, ⟨boundary i.down 1⟩, by simp [idx], ?_⟩
            rw [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_closedBall]
            simp
      | succ n =>
          exact PEmpty.elim i

/-- Helper for Example 10.1.8: the graph-realization weak topology reduces to the already-proved
closedness criterion for vertex slices and closed edge slices. -/
private theorem graphRealizationOfFamilyCWComplex_closed
    (boundary : J → Fin 2 → X₀) (A : Set (graphRealizationOfFamily boundary))
    (_hA : A ⊆ Set.univ) :
    (∀ n (j : graphRealizationOfFamilyCell X₀ J n),
        IsClosed (A ∩ graphRealizationOfFamilyCellMap boundary n j '' Metric.closedBall 0 1)) →
      IsClosed A := by
  intro hClosed
  -- Rewrite the cellwise closedness hypotheses into the vertex and closed-edge slices from the
  -- quotient-space criterion.
  apply graphRealizationOfFamilyClosed_of_cellwiseClosed boundary
  · intro x
    simpa [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_closedBall]
      using hClosed 0 ⟨x⟩
  · intro j
    simpa [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyOneCellMap_image_closedBall]
      using hClosed 1 ⟨j⟩

/-- Helper for Example 10.1.8: the closed graph cells cover the whole graph realization. -/
private theorem graphRealizationOfFamilyCWComplex_union
    (boundary : J → Fin 2 → X₀) :
    ⋃ (n : ℕ) (j : graphRealizationOfFamilyCell X₀ J n),
      graphRealizationOfFamilyCellMap boundary n j '' Metric.closedBall 0 1 =
        (Set.univ : Set (graphRealizationOfFamily boundary)) := by
  ext y
  constructor
  · intro _
    simp
  · intro _
    refine Quotient.inductionOn y ?_
    intro z
    cases z with
    | inl x =>
        -- Every vertex is the image of its dedicated closed `0`-cell.
        change graphRealizationOfFamilyVertex boundary x ∈
          ⋃ (n : ℕ) (j : graphRealizationOfFamilyCell X₀ J n),
            graphRealizationOfFamilyCellMap boundary n j '' Metric.closedBall 0 1
        refine Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨⟨x⟩, ?_⟩⟩
        simpa [graphRealizationOfFamilyCellMap, graphRealizationOfFamilyZeroCellMap_image_closedBall]
    | inr jt =>
        rcases jt with ⟨j, t⟩
        -- Every edge point lies in the closed image of its ambient `1`-cell chart.
        change graphRealizationOfFamilyEdgeMap boundary j t ∈
          ⋃ (n : ℕ) (j : graphRealizationOfFamilyCell X₀ J n),
            graphRealizationOfFamilyCellMap boundary n j '' Metric.closedBall 0 1
        have hRange :
            graphRealizationOfFamilyEdgeMap boundary j t ∈
              graphRealizationOfFamilyOneCellMap boundary j '' Metric.closedBall 0 1 := by
          rw [graphRealizationOfFamilyOneCellMap_image_closedBall]
          exact ⟨t, rfl⟩
        refine Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨⟨j⟩, ?_⟩⟩
        simpa [graphRealizationOfFamilyCellMap] using hRange

/-- Helper for Example 10.1.8: the graph realization carries the explicit non-finite CW complex
with vertex cells in degree `0`, edge cells in degree `1`, and no higher cells. -/
@[implicit_reducible] private noncomputable def graphRealizationOfFamilyCWComplex
    (boundary : J → Fin 2 → X₀) :
    Topology.CWComplex (Set.univ : Set (graphRealizationOfFamily boundary)) where
  cell := graphRealizationOfFamilyCell X₀ J
  map := graphRealizationOfFamilyCellMap boundary
  source_eq := graphRealizationOfFamilyCWComplex_source_eq boundary
  continuousOn := graphRealizationOfFamilyCWComplex_continuousOn boundary
  continuousOn_symm := graphRealizationOfFamilyCWComplex_continuousOn_symm boundary
  pairwiseDisjoint' := graphRealizationOfFamilyCWComplex_pairwiseDisjoint boundary
  mapsTo' := graphRealizationOfFamilyCWComplex_mapsTo boundary
  closed' := graphRealizationOfFamilyCWComplex_closed boundary
  union' := graphRealizationOfFamilyCWComplex_union boundary

/-- Helper for Example 10.1.8: the graph-side cell family is empty in every degree above `1`. -/
private theorem graphRealizationOfFamilyCell_isEmpty_of_one_lt
    (n : ℕ) (hn : 1 < n) :
    IsEmpty (graphRealizationOfFamilyCell X₀ J n) := by
  cases n with
  | zero =>
      exact (False.elim ((Nat.not_lt_zero 1) hn))
  | succ n =>
      cases n with
      | zero =>
          exact (False.elim ((lt_irrefl 1) hn))
      | succ n =>
          simpa [graphRealizationOfFamilyCell]
            using (inferInstance : IsEmpty PEmpty)

/-- Helper for Example 10.1.8: postcomposing a partial equivalence with an equivalence transports
its set image by the same equivalence. -/
private theorem partialEquiv_transEquiv_image
    {α β γ : Type*} (e : PartialEquiv α β) (f : β ≃ γ) (s : Set α) :
    (e.transEquiv f) '' s = f '' (e '' s) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Helper for Example 10.1.8: postcomposing a partial equivalence with a homeomorphism preserves
inverse continuity on the transported target. -/
private theorem partialEquiv_transHomeomorph_continuousOnSymm
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    (e : PartialEquiv α β) (h : β ≃ₜ γ)
    (he : ContinuousOn e.symm e.target) :
    ContinuousOn (e.transEquiv h.toEquiv).symm (e.transEquiv h.toEquiv).target := by
  -- On the transported target, the inverse is just `e.symm` after the homeomorphism inverse.
  rw [continuousOn_iff_continuous_restrict]
  have hsymm : Continuous fun y : (e.transEquiv h.toEquiv).target ↦ h.symm y.1 :=
    h.symm.continuous.comp continuous_subtype_val
  have hsymm_mapsTo : ∀ y : (e.transEquiv h.toEquiv).target, h.symm y.1 ∈ e.target := by
    intro y
    exact y.2
  have hcont : Continuous fun y : (e.transEquiv h.toEquiv).target ↦ e.symm (h.symm y.1) :=
    he.comp_continuous hsymm hsymm_mapsTo
  simpa [Set.restrict, PartialEquiv.transEquiv] using hcont

/-- Helper for Example 10.1.8: intersecting with a set and then applying a homeomorphism agrees
with applying the homeomorphism after intersecting with the transported target. -/
private theorem homeomorph_image_inter_eq
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (A : Set X) (B : Set Y) :
    h '' A ∩ B = h '' (A ∩ h.symm '' B) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxA, rfl⟩, hyB⟩
    refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
    exact ⟨h x, hyB, h.symm_apply_apply x⟩
  · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
    rcases hxB with ⟨z, hzB, hz⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    have hz' : z = h x := by
      simpa using congrArg h hz
    simpa [hz'] using hzB

/-- Helper for Example 10.1.8: transporting every graph-side characteristic map along a
homeomorphism produces a CW structure on the source space with the same cell family. -/
@[implicit_reducible] private noncomputable def homeomorphTransportCWComplex
    {X : Type w} {Y : Type (max u v)} [TopologicalSpace X] [TopologicalSpace Y]
    (cw : Topology.CWComplex (Set.univ : Set Y)) (h : X ≃ₜ Y) :
    Topology.CWComplex (Set.univ : Set X) := by
  -- TODO: package the transported cell family with an explicit universe lift from `cw.cell n`
  -- into the universe of `X`, then transport all CW fields across `h`.
  sorry

/-- A space homeomorphic to a graph realization inherits a chosen one-dimensional CW structure. -/
private theorem homeomorph_graphRealizationOfFamily_hasOneDimensionalCWStructure
    (X : Type w) [TopologicalSpace X]
    (boundary : J → Fin 2 → X₀) (hX : X ≃ₜ graphRealizationOfFamily boundary) :
    ∃ cw : Topology.CWComplex (Set.univ : Set X),
      Topology.CWComplex.dimLE cw 1 := by
  -- TODO: after installing the transported CW owner, reuse
  -- `graphRealizationOfFamilyCell_isEmpty_of_one_lt` to prove the dimension bound.
  sorry

/-- A one-dimensional CW structure on `X` is homeomorphic to some graph realization. -/
private theorem homeomorph_graphRealizationOfFamily_of_isOneDimensional
    (X : Type w) [TopologicalSpace X]
    (cw : Topology.CWComplex (Set.univ : Set X))
    (h_dim : Topology.CWComplex.dimLE cw 1) :
    ∃ (X₀ J : Type w) (boundary : J → Fin 2 → X₀)
      (hX : X ≃ₜ graphRealizationOfFamily boundary), True := by
  classical
  letI : Topology.CWComplex (Set.univ : Set X) := cw
  let vertexCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 0)
  let edgeCell : Type w := ULift (Topology.CWComplex.cell (Set.univ : Set X) 1)
  let comparison : vertexCell ⊕ (edgeCell × I) → X := @oneDimensionalComparison X _ _
  have hEndpoints :
      ∀ j : edgeCell, ∃ v0 v1 : vertexCell,
        Topology.CWComplex.map 1 j.down oneCellLeftPoint = Topology.CWComplex.map 0 v0.down 0 ∧
        Topology.CWComplex.map 1 j.down oneCellRightPoint = Topology.CWComplex.map 0 v1.down 0 := by
    intro j
    -- The endpoint data now comes from the boundary-sphere control of each chosen `1`-cell.
    rcases oneCellEndpoints_eq_vertices cw j.down with ⟨v0, v1, h0, h1⟩
    exact ⟨⟨v0⟩, ⟨v1⟩, h0, h1⟩
  let boundary : edgeCell → Fin 2 → vertexCell := fun j b ↦
    Fin.cases
      (Classical.choose (hEndpoints j))
      (fun _ ↦ Classical.choose (Classical.choose_spec (hEndpoints j)))
      b
  have hBoundary_left :
      ∀ j : edgeCell,
        Topology.CWComplex.map 1 j.down oneCellLeftPoint =
          Topology.CWComplex.map 0 (boundary j 0).down 0 := by
    intro j
    -- Unfold the chosen initial vertex of the `j`th cell.
    simpa [boundary] using (Classical.choose_spec (Classical.choose_spec (hEndpoints j))).1
  have hBoundary_right :
      ∀ j : edgeCell,
        Topology.CWComplex.map 1 j.down oneCellRightPoint =
          Topology.CWComplex.map 0 (boundary j 1).down 0 := by
    intro j
    -- Unfold the chosen terminal vertex of the `j`th cell.
    simpa [boundary] using (Classical.choose_spec (Classical.choose_spec (hEndpoints j))).2
  have hEdgeZero :
      ∀ j : edgeCell,
        comparison (Sum.inr (j, (0 : I))) = comparison (Sum.inl (boundary j 0)) := by
    intro j
    -- Evaluate the comparison map at the left endpoint of the chosen `1`-cell.
    simpa [comparison, oneDimensionalComparison, oneCellParamHomeomorph_symm_zero] using
      hBoundary_left j
  have hEdgeOne :
      ∀ j : edgeCell,
        comparison (Sum.inr (j, (1 : I))) = comparison (Sum.inl (boundary j 1)) := by
    intro j
    -- Evaluate the comparison map at the right endpoint of the chosen `1`-cell.
    simpa [comparison, oneDimensionalComparison, oneCellParamHomeomorph_symm_one] using
      hBoundary_right j
  have hLeftRel :
      ∀ j : edgeCell,
        graphRealizationOfFamilySetoid boundary
          (Sum.inr (j, (0 : I))) (Sum.inl (boundary j 0)) := by
    intro j
    -- The generated graph relation identifies each edge's left endpoint with its initial vertex.
    exact
      (Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩) :
        Relation.EqvGen (graphRealizationOfFamilyRel boundary)
          (Sum.inr (j, (0 : I))) (Sum.inl (boundary j 0)))
  have hRightRel :
      ∀ j : edgeCell,
        graphRealizationOfFamilySetoid boundary
          (Sum.inr (j, (1 : I))) (Sum.inl (boundary j 1)) := by
    intro j
    -- The generated graph relation identifies each edge's right endpoint with its terminal
    -- vertex.
    exact
      (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩) :
        Relation.EqvGen (graphRealizationOfFamilyRel boundary)
          (Sum.inr (j, (1 : I))) (Sum.inl (boundary j 1)))
  have hLeftRelSymm :
      ∀ j : edgeCell,
        graphRealizationOfFamilySetoid boundary
          (Sum.inl (boundary j 0)) (Sum.inr (j, (0 : I))) := by
    intro j
    -- Reverse the endpoint-vertex generator when the comparison route needs the opposite
    -- orientation.
    exact Relation.EqvGen.symm _ _ (hLeftRel j)
  have hRightRelSymm :
      ∀ j : edgeCell,
        graphRealizationOfFamilySetoid boundary
          (Sum.inl (boundary j 1)) (Sum.inr (j, (1 : I))) := by
    intro j
    -- Reverse the right-endpoint generator for the same endpoint-normalization step.
    exact Relation.EqvGen.symm _ _ (hRightRel j)
  have hKernel :
      ∀ a b : vertexCell ⊕ (edgeCell × I),
        graphRealizationOfFamilySetoid boundary a b ↔
          comparison a = comparison b :=
    oneDimensionalComparison_rel_iff boundary hEdgeZero hEdgeOne
  let _ : TopologicalSpace vertexCell := ⊥
  let _ : TopologicalSpace edgeCell := ⊥
  let _ : DiscreteTopology vertexCell := discreteTopology_bot _
  let _ : DiscreteTopology edgeCell := discreteTopology_bot _
  let _ : T2Space X := instT2SpaceOfCWComplexUniv X
  have hQuotient : Topology.IsQuotientMap comparison := by
    -- Route correction: the quotient-map step is now isolated as a cellwise closed-set argument.
    simpa [comparison] using oneDimensionalComparison_isQuotientMap (X := X) h_dim
  refine ⟨vertexCell, edgeCell, boundary, ?_, trivial⟩
  -- The quotient-homeomorphism theorem now applies directly because the graph setoid is exactly
  -- the kernel relation of `comparison`.
  exact
    (quotientHomeomorphOfRelIff
      (q := ⟨comparison, hQuotient.continuous⟩) hQuotient
      (graphRealizationOfFamilySetoid boundary) hKernel).symm

/-- Example 10.1.8::statement_repair::2. A graph is exactly a one-dimensional CW complex. -/
theorem graph_iff_oneDimensionalCWStructure (X : Type w) [TopologicalSpace X] :
    (∃ (X₀ J : Type w) (boundary : J → Fin 2 → X₀),
      Nonempty (X ≃ₜ graphRealizationOfFamily boundary)) ↔
      ∃ cw : Topology.CWComplex (Set.univ : Set X),
        Topology.CWComplex.dimLE cw 1 := by
  constructor
  · rintro ⟨X₀, J, boundary, ⟨hX⟩⟩
    -- The forward implication is now reduced to the dedicated graph-to-CW constructor.
    exact homeomorph_graphRealizationOfFamily_hasOneDimensionalCWStructure X boundary hX
  · intro hX
    rcases hX with ⟨cw, h_dim⟩
    -- The reverse implication now only depends on the quotient-packaging helper theorem.
    rcases homeomorph_graphRealizationOfFamily_of_isOneDimensional X cw h_dim with
      ⟨X₀, J, boundary, hGraph, _⟩
    exact ⟨X₀, J, boundary, ⟨hGraph⟩⟩
