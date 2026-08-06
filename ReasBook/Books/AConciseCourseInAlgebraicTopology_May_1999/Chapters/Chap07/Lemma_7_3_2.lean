import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.ContinuousMap.Interval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousMap unitInterval

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]

-- Semantic recall via `lean_leansearch` surfaced only abstract model-category path-object
-- factorization APIs; the source-faithful local owners here are `MappingPathSpace`,
-- `mappingPathSpaceInclusion`, `mappingPathSpaceProjection`, and
-- `HasCoveringHomotopyProperty`.

/-- Helper for Lemma 7.3.2: the path projection `MappingPathSpace p → C(I, B)` is continuous. -/
lemma mappingPathSpacePathProjectionContinuous {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) :
    Continuous fun z : MappingPathSpace p ↦ z.path := by
  simpa [MappingPathSpace.path] using
    (continuous_snd.comp (MappingPathSpace.continuous_subtypeVal (p := p)) :
      Continuous fun z : MappingPathSpace p ↦ (z : E × C(I, B)).2)

/-- Helper for Lemma 7.3.2: scaling the stored path in `MappingPathSpace f` gives a homotopy from
`mappingPathSpaceInclusion f ≫ mappingPathSpacePointProjection f` to the identity. -/
theorem mappingPathSpaceInclusionPointProjection_homotopic_id (f : C(X, Y)) :
    ((mappingPathSpaceInclusion f).comp (mappingPathSpacePointProjection f)).Homotopic
      (ContinuousMap.id (MappingPathSpace f)) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (MappingPathSpace f) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace f
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (I × MappingPathSpace f) :=
    instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval (MappingPathSpace f)
  have hscaledPathContinuous (p : I × MappingPathSpace f) :
      Continuous fun s : I ↦ p.2.path (Set.projIcc 0 1 zero_le_one ((p.1 : ℝ) * s)) := by
    exact p.2.path.continuous.comp <| continuous_projIcc.comp <| by fun_prop
  refine ⟨{
    toFun := fun p ↦ MappingPathSpace.mk p.2.point
      (⟨fun s ↦ p.2.path (Set.projIcc 0 1 zero_le_one ((p.1 : ℝ) * s)),
        hscaledPathContinuous p⟩)
      ?_
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · -- The scaled path still starts at `f p.2.point`, so it remains in `MappingPathSpace f`.
    simp [MappingPathSpace.path_zero_eq, Set.projIcc_left]
  · -- Package the fixed point coordinate and the scaled path coordinate as a continuous
    -- subtype map.
    have hpoint : Continuous fun p : I × MappingPathSpace f ↦ p.2.point := by
      simpa using (mappingPathSpacePointProjectionContinuous f).comp continuous_snd
    have hpath : Continuous fun p : I × MappingPathSpace f ↦
        (⟨fun s ↦ p.2.path (Set.projIcc 0 1 zero_le_one ((p.1 : ℝ) * s)),
          hscaledPathContinuous p⟩ : C(I, Y)) := by
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      have hfamily : Continuous fun r : (I × MappingPathSpace f) × I ↦ r.1.2.path := by
        exact mappingPathSpacePathProjectionContinuous (p := f).comp
          (continuous_snd.comp continuous_fst)
      have hparam : Continuous fun r : (I × MappingPathSpace f) × I ↦
          Set.projIcc 0 1 zero_le_one ((r.1.1 : ℝ) * r.2) := by
        exact continuous_projIcc.comp <| by fun_prop
      simpa using continuous_eval.comp (hfamily.prodMk hparam)
    exact MappingPathSpace.continuous_mk hpoint hpath (fun p ↦ by
      simp [MappingPathSpace.path_zero_eq, Set.projIcc_left])
  · intro xγ
    -- At `t = 0`, the scaled path collapses to the constant path at `f xγ.point`.
    apply MappingPathSpace.ext
    · rfl
    · ext s
      simp [mappingPathSpaceInclusion, MappingPathSpace.path_zero_eq, Set.projIcc_left]
  · intro xγ
    -- At `t = 1`, the reparametrization is the identity on the stored path.
    apply MappingPathSpace.ext
    · rfl
    · ext s
      have hs : Set.projIcc 0 1 zero_le_one (((1 : I) : ℝ) * s) = s := by
        simp
      exact congrArg xγ.path hs

/-- Helper for Lemma 7.3.2: the endpoint-path formula shortens the stored path and then follows
the prescribed base path. -/
noncomputable def mappingPathSpaceProjectionLiftValue (f : C(X, Y))
    (z : MappingPathSpace (mappingPathSpaceProjection f)) (t s : I) : Y :=
  if (s : ℝ) ≤ 1 - (t : ℝ) / 2 then
    z.point.path (Set.projIcc 0 1 zero_le_one ((s : ℝ) / (1 - (t : ℝ) / 2)))
  else
    z.path (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) + (t : ℝ) - 2))

/-- Helper for Lemma 7.3.2: the compressed-append endpoint-path formula is continuous in the
mapping-path input and both interval variables. -/
theorem mappingPathSpaceProjectionLiftValue_continuous (f : C(X, Y)) :
    Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
      mappingPathSpaceProjectionLiftValue f q.1 q.2.1 q.2.2 := by
  have hstoredPath : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
      q.1.point.path := by
    have hpoint : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
        q.1.point := by
      simpa using
        (mappingPathSpacePointProjectionContinuous (mappingPathSpaceProjection f)).comp
          continuous_fst
    exact mappingPathSpacePathProjectionContinuous (p := f) |>.comp hpoint
  have houterPath : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
      q.1.path := by
    exact mappingPathSpacePathProjectionContinuous (p := mappingPathSpaceProjection f) |>.comp
      continuous_fst
  have hdenom_ne :
      ∀ q : MappingPathSpace (mappingPathSpaceProjection f) × I × I,
        1 - (q.2.1 : ℝ) / 2 ≠ 0 := by
    intro q hq
    have ht_le_one : (q.2.1 : ℝ) ≤ 1 := q.2.1.2.2
    nlinarith
  have hfirstParam : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
      Set.projIcc 0 1 zero_le_one (((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2))) := by
    exact continuous_projIcc.comp <|
      Continuous.div (by fun_prop) (by fun_prop) hdenom_ne
  have hsecondParam : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I × I ↦
      Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2) := by
    exact continuous_projIcc.comp <| by fun_prop
  -- The two branches are continuous, and they agree exactly when the cutoff line is met.
  refine continuous_if_le (by fun_prop) (by fun_prop)
    (continuous_eval.comp (hstoredPath.prodMk hfirstParam)).continuousOn
    (continuous_eval.comp (houterPath.prodMk hsecondParam)).continuousOn ?_
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
    q.1.point.path (Set.projIcc 0 1 zero_le_one (((q.2.2 : ℝ) / (1 - (q.2.1 : ℝ) / 2)))) =
        q.1.point.path 1 := by rw [hfirst]
    _ = q.1.path 0 := by
      simpa [mappingPathSpaceProjection_apply] using q.1.path_zero_eq.symm
    _ = q.1.path (Set.projIcc 0 1 zero_le_one (2 * (q.2.2 : ℝ) + (q.2.1 : ℝ) - 2)) := by
      rw [hsecond]

/-- Helper for Lemma 7.3.2: the lifted endpoint-path formula always starts at `f x`. -/
theorem mappingPathSpaceProjectionLiftValue_zero (f : C(X, Y))
    (z : MappingPathSpace (mappingPathSpaceProjection f)) (t : I) :
    mappingPathSpaceProjectionLiftValue f z t 0 = f z.point.point := by
  -- At `s = 0`, the cutoff inequality forces the compressed stored-path branch.
  have hbranch : ((0 : I) : ℝ) ≤ 1 - (t : ℝ) / 2 := by
    have ht_le_one : (t : ℝ) ≤ 1 := t.2.2
    have hdiv : (t : ℝ) / 2 ≤ (1 : ℝ) / 2 := by
      exact div_le_div_of_nonneg_right ht_le_one (by norm_num : (0 : ℝ) ≤ 2)
    have hbound : (1 : ℝ) / 2 ≤ 1 - (t : ℝ) / 2 := by
      linarith
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbound
  -- The compressed parameter is `0`, so the stored path starts at `f z.point.point`.
  rw [mappingPathSpaceProjectionLiftValue, if_pos hbranch]
  simp [MappingPathSpace.path_zero_eq]

/-- Helper for Lemma 7.3.2: at time `0`, the lifting formula recovers the original stored path. -/
theorem mappingPathSpaceProjectionLiftValue_timeZero (f : C(X, Y))
    (z : MappingPathSpace (mappingPathSpaceProjection f)) (s : I) :
    mappingPathSpaceProjectionLiftValue f z 0 s = z.point.path s := by
  -- At homotopy time `0`, the cutoff is `1`, so the first branch covers the whole interval.
  have hbranch : (s : ℝ) ≤ 1 - ((0 : I) : ℝ) / 2 := by
    simpa using s.2.2
  -- The reparametrization is trivial at `t = 0`, so the stored path is unchanged.
  rw [mappingPathSpaceProjectionLiftValue, if_pos hbranch]
  have hparam :
      Set.projIcc 0 1 zero_le_one ((s : ℝ) / (1 - (((0 : I) : ℝ) / 2))) = s := by
    have hsimp : ((s : ℝ) / (1 - (((0 : I) : ℝ) / 2))) = (s : ℝ) := by
      norm_num
    rw [hsimp, Set.projIcc_val]
  exact congrArg z.point.path hparam

/-- Helper for Lemma 7.3.2: at the endpoint `s = 1`, the lifting formula projects to the chosen
base path. -/
theorem mappingPathSpaceProjectionLiftValue_endpoint (f : C(X, Y))
    (z : MappingPathSpace (mappingPathSpaceProjection f)) (t : I) :
    mappingPathSpaceProjectionLiftValue f z t 1 = z.path t := by
  by_cases ht : t = 0
  · -- At `t = 0`, the lifted path is the original stored path in `z.point`.
    calc
      mappingPathSpaceProjectionLiftValue f z t 1 =
          mappingPathSpaceProjectionLiftValue f z 0 1 := by simp [ht]
      _ = z.point.path 1 := mappingPathSpaceProjectionLiftValue_timeZero f z (1 : I)
      _ = z.path 0 := by
        simpa [mappingPathSpaceProjection_apply] using z.path_zero_eq.symm
      _ = z.path t := by simp [ht]
  · -- For positive `t`, the endpoint lies on the appended base-path branch.
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
    -- The endpoint parameter simplifies to `t`, so the base path is recovered.
    rw [mappingPathSpaceProjectionLiftValue, if_neg hbranch]
    exact congrArg z.path hparam

/-- Helper for Lemma 7.3.2: for each stored mapping path, the compressed-append formula is
continuous in the outer and inner path parameters. -/
theorem mappingPathSpaceProjectionLiftValue_continuous_fixed (f : C(X, Y))
    (z : MappingPathSpace (mappingPathSpaceProjection f)) :
    Continuous fun p : I × I ↦ mappingPathSpaceProjectionLiftValue f z p.1 p.2 := by
  -- Freeze the mapping-path input and compose the global continuity theorem with that constant map.
  have hconst : Continuous fun p : I × I ↦
      ((z, p.1, p.2) : MappingPathSpace (mappingPathSpaceProjection f) × I × I) := by
    fun_prop
  simpa using (mappingPathSpaceProjectionLiftValue_continuous f).comp hconst

/-- Helper for Lemma 7.3.2: the compressed-append formula varies continuously as a path in `Y`
with both the outer mapping-path input and the homotopy time. -/
theorem mappingPathSpaceProjectionLiftPath_continuous (f : C(X, Y)) :
    Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I ↦
      (⟨fun s ↦ mappingPathSpaceProjectionLiftValue f q.1 q.2 s,
        (mappingPathSpaceProjectionLiftValue_continuous_fixed f q.1).comp
          (show Continuous fun s : I ↦ (q.2, s) by fun_prop)⟩ : C(I, Y)) := by
  -- Curry the three-variable continuity statement after rebracketing the product domain.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have huncurried :
      Continuous fun r : (MappingPathSpace (mappingPathSpaceProjection f) × I) × I ↦
        mappingPathSpaceProjectionLiftValue f r.1.1 r.1.2 r.2 := by
    simpa using (mappingPathSpaceProjectionLiftValue_continuous f).comp
      (Homeomorph.prodAssoc (MappingPathSpace (mappingPathSpaceProjection f)) I I).continuous_toFun
  simpa [Function.uncurry] using huncurried

/-- Helper for Lemma 7.3.2: the endpoint projection of the mapping path space admits a continuous
path lifting function. -/
theorem mappingPathSpaceProjectionContinuousPathLift (f : C(X, Y)) :
    Nonempty (ContinuousPathLiftingFunction (mappingPathSpaceProjection f)) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (MappingPathSpace f) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace f
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (MappingPathSpace (mappingPathSpaceProjection f)) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace (mappingPathSpaceProjection f)
  let _ : UCompactlyGeneratedSpace.{max u v} I :=
    uCompactlyGeneratedSpaceLift (X := I)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (MappingPathSpace (mappingPathSpaceProjection f) × I) :=
    compactlyGeneratedWeakHausdorffSpaceProdUnitIntervalRight
      (MappingPathSpace (mappingPathSpaceProjection f))
  refine ⟨{
    toContinuousMap := {
      toFun := fun z ↦
        ⟨fun t ↦
          MappingPathSpace.mk z.point.point
            (⟨fun s ↦ mappingPathSpaceProjectionLiftValue f z t s, ?_⟩)
            (mappingPathSpaceProjectionLiftValue_zero f z t), ?_⟩
      continuous_toFun := ?_ }
    source_eq := ?_
    proj_comp_eq := ?_ }⟩
  · -- For fixed `z` and `t`, the inner endpoint-path formula is continuous in `s`.
    have hpair : Continuous fun s : I ↦ (t, s) := by
      fun_prop
    exact (mappingPathSpaceProjectionLiftValue_continuous_fixed f z).comp hpair
  · -- For fixed `z`, the lifted point coordinate is constant and the path coordinate is continuous.
    have hconstPoint : Continuous fun t : I ↦ z.point.point := continuous_const
    have hinnerPair (t : I) : Continuous fun s : I ↦ (t, s) := by
      fun_prop
    have hpair : Continuous fun t : I ↦ (z, t) := by
      fun_prop
    have hpath : Continuous fun t : I ↦
        (⟨fun s ↦ mappingPathSpaceProjectionLiftValue f z t s,
          (mappingPathSpaceProjectionLiftValue_continuous_fixed f z).comp (hinnerPair t)⟩ :
          C(I, Y)) := by
      simpa using (mappingPathSpaceProjectionLiftPath_continuous f).comp hpair
    exact MappingPathSpace.continuous_mk hconstPoint hpath
      (fun t ↦ mappingPathSpaceProjectionLiftValue_zero f z t)
  · -- Curry the jointly continuous lifted map into a path-valued continuous map.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have houterPoint : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I ↦
        q.1.point := by
      simpa using
        (mappingPathSpacePointProjectionContinuous (mappingPathSpaceProjection f)).comp
          continuous_fst
    have hpoint : Continuous fun q : MappingPathSpace (mappingPathSpaceProjection f) × I ↦
        q.1.point.point := by
      simpa using (mappingPathSpacePointProjectionContinuous f).comp houterPoint
    exact MappingPathSpace.continuous_mk hpoint
      (mappingPathSpaceProjectionLiftPath_continuous f)
      (fun q ↦ mappingPathSpaceProjectionLiftValue_zero f q.1 q.2)
  · intro z
    -- At time `0`, the lifted path in `MappingPathSpace f` is the original point `z.point`.
    apply MappingPathSpace.ext
    · rfl
    · ext s
      simpa using mappingPathSpaceProjectionLiftValue_timeZero f z s
  · intro z
    -- Projecting the constructed lift to `Y` recovers the prescribed base path.
    ext t
    simpa [mappingPathSpaceProjection_apply] using
      mappingPathSpaceProjectionLiftValue_endpoint f z t

/-- First part of Lemma 7.3.2: in the mapping path factorization of `f : C(X, Y)`, the canonical
map
`X → MappingPathSpace f` is a homotopy equivalence, with canonical homotopy inverse
`mappingPathSpacePointProjection f`. -/
def mappingPathSpaceInclusion_homotopyEquiv (f : C(X, Y)) :
    X ≃ₕ MappingPathSpace f where
  toFun := mappingPathSpaceInclusion f
  invFun := mappingPathSpacePointProjection f
  left_inv := by
    simpa [mappingPathSpacePointProjection_comp_mappingPathSpaceInclusion] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id X))
  right_inv := by
    -- The right inverse homotopy contracts each stored path by scaling its parameter.
    simpa using mappingPathSpaceInclusionPointProjection_homotopic_id f

/-- The forward map of `mappingPathSpaceInclusion_homotopyEquiv f` is the canonical inclusion
`mappingPathSpaceInclusion f`. -/
@[simp] theorem mappingPathSpaceInclusion_homotopyEquiv_toFun (f : C(X, Y)) :
    (mappingPathSpaceInclusion_homotopyEquiv f).toFun = mappingPathSpaceInclusion f :=
  rfl

/-- The inverse map of `mappingPathSpaceInclusion_homotopyEquiv f` is the canonical point
projection `mappingPathSpacePointProjection f`. -/
@[simp] theorem mappingPathSpaceInclusion_homotopyEquiv_invFun (f : C(X, Y)) :
    (mappingPathSpaceInclusion_homotopyEquiv f).invFun = mappingPathSpacePointProjection f :=
  rfl

/-- Evaluating `mappingPathSpaceInclusion_homotopyEquiv f` on a point of `X` agrees with the
canonical inclusion into the mapping path space. -/
@[simp] theorem mappingPathSpaceInclusion_homotopyEquiv_apply (f : C(X, Y)) (x : X) :
    mappingPathSpaceInclusion_homotopyEquiv f x = mappingPathSpaceInclusion f x :=
  rfl

/-- Evaluating the inverse of `mappingPathSpaceInclusion_homotopyEquiv f` agrees with the
canonical point projection from the mapping path space. -/
@[simp] theorem mappingPathSpaceInclusion_homotopyEquiv_symm_apply (f : C(X, Y))
    (xγ : MappingPathSpace f) :
    (mappingPathSpaceInclusion_homotopyEquiv f).symm xγ =
      mappingPathSpacePointProjection f xγ :=
  rfl

/-- The homotopy equivalence `mappingPathSpaceInclusion_homotopyEquiv f` has the expected
right-inverse homotopy on `MappingPathSpace f`. -/
theorem mappingPathSpaceInclusion_homotopyEquiv_spec (f : C(X, Y)) :
    ((mappingPathSpaceInclusion_homotopyEquiv f).toFun.comp
      (mappingPathSpaceInclusion_homotopyEquiv f).invFun).Homotopic
        (ContinuousMap.id (MappingPathSpace f)) := by
  simpa using (mappingPathSpaceInclusion_homotopyEquiv f).right_inv

section SpaceOverBridge

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

/-- The forward map of `mappingPathSpaceInclusion_homotopyEquiv p` is the underlying continuous
map of the canonical morphism `SpaceOver.mk p ⟶ SpaceOver.mk (mappingPathSpaceProjection p)`. -/
@[simp] theorem mappingPathSpaceInclusion_homotopyEquiv_toFun_spaceOver_homMk (p : C(E, B)) :
    (mappingPathSpaceInclusion_homotopyEquiv p).toFun =
      (SpaceOver.homMk (mappingPathSpaceInclusion p)
        (mappingPathSpaceProjection_comp_mappingPathSpaceInclusion p)).left.hom := by
  change (mappingPathSpaceInclusion_homotopyEquiv p).toFun = mappingPathSpaceInclusion p
  simp

end SpaceOverBridge

/-- Lemma 7.3.2: in the mapping path factorization of `f : C(X, Y)`, the endpoint map
`mappingPathSpaceProjection f : C(MappingPathSpace f, Y)` has the covering homotopy property.
This is the unconditional part of the book's claim that it is a fibration; the Chapter 7 class
`IsFibration` additionally packages surjectivity, and that bridge is recorded below under an
explicit surjectivity hypothesis on `mappingPathSpaceProjection f`. -/
theorem mappingPathSpaceProjection_hasCoveringHomotopyProperty (f : C(X, Y)) :
    HasCoveringHomotopyProperty.{max u v, v, max u v} (mappingPathSpaceProjection f) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v}
      (MappingPathSpace f) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace f
  -- The path-space criterion turns the bundled lifting-function witness into CHP.
  exact
    (HasCoveringHomotopyProperty.iff_nonempty_continuousPathLiftingFunction
      (E := MappingPathSpace f) (B := Y) (p := mappingPathSpaceProjection f)).2
      (mappingPathSpaceProjectionContinuousPathLift f)

/-- The endpoint map in the mapping path factorization carries the induced covering-homotopy
property instance. -/
instance mappingPathSpaceProjectionInstHasCoveringHomotopyProperty (f : C(X, Y)) :
    HasCoveringHomotopyProperty.{max u v, v, max u v} (mappingPathSpaceProjection f) :=
  mappingPathSpaceProjection_hasCoveringHomotopyProperty f

/-- If `f : C(X, Y)` is surjective, then the endpoint map in its mapping path factorization is
surjective as well. -/
theorem mappingPathSpaceProjection_surjective (f : C(X, Y))
    (hf : Function.Surjective f) :
    Function.Surjective (mappingPathSpaceProjection f) := by
  intro y
  rcases hf y with ⟨x, hx⟩
  refine ⟨MappingPathSpace.mk x (ContinuousMap.const I y) ?_, ?_⟩
  · -- The constant path at `y` starts at `f x` because `f x = y`.
    simpa using hx.symm
  · -- Its endpoint is exactly `y`.
    rfl

/-- Companion bridge: if the endpoint map in the mapping path factorization is surjective, then
it is a fibration in the local sense of Definition 7.1.2. -/
theorem mappingPathSpaceProjection_isFibration_of_surjective (f : C(X, Y))
    (hf : Function.Surjective (mappingPathSpaceProjection f)) :
    IsFibration.{max u v, v, max u v} (mappingPathSpaceProjection f) := by
  let hp : HasCoveringHomotopyProperty.{max u v, v, max u v} (mappingPathSpaceProjection f) :=
    mappingPathSpaceProjection_hasCoveringHomotopyProperty f
  refine
    { surjective := hf
      homotopyLift := ?_ }
  -- The covering homotopy property part is inherited from the previous theorem.
  intro A _ _ f₀ f₁ H g₀ hg₀
  exact hp.homotopyLift H hg₀

/-- The endpoint map in the mapping path factorization carries the induced fibration instance
whenever the original map `f` is itself a fibration, so its surjectivity is available through
the Chapter 7 owner API. -/
instance mappingPathSpaceProjectionInstIsFibration (f : C(X, Y))
    [IsFibration f] :
    IsFibration.{max u v, v, max u v} (mappingPathSpaceProjection f) :=
  by
    let hf : Function.Surjective f := IsFibration.instSurjective
    exact mappingPathSpaceProjection_isFibration_of_surjective f
      (mappingPathSpaceProjection_surjective f hf)
