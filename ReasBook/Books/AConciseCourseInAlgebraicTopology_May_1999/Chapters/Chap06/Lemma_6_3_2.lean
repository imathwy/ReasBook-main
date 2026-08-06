import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Construction_6_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_1_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6

open CategoryTheory CategoryTheory.Limits
open ContinuousMap
open scoped ContinuousMap unitInterval

universe u

noncomputable section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- unbased homotopy equivalences, while `IsCofibration` from Definition 6.1.4 is the local owner
-- for the cofibration clause in this chapter.

/-- The canonical copy of `X` sitting at the top `t = 1` of the cylinder summand of the mapping
cylinder of `f`. This is an internal helper for the cofibration construction. -/
private def mappingCylinderTopInclusion (f : C(X, Y)) : C(X, f.mappingCylinder) :=
  (mappingCylinderCylinderInclusion f).comp
    ((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I)))

/-- The source-faithful first map in the mapping cylinder factorization of `f`, namely the
top-slice inclusion `x ↦ (x, 1)` into the cylinder summand of `M_f`.

This remains distinct from `Construction_6_3_1.mappingCylinderIn`, which in the current Chapter 6
construction is the glued time-`0` map. -/
abbrev mappingCylinderFactorizationIn (f : C(X, Y)) : C(X, f.mappingCylinder) :=
  mappingCylinderTopInclusion f

/-- The canonical projection `M_f → Y` restricts on `mappingCylinderTopInclusion f` to `f`. -/
private theorem mappingCylinderProjection_comp_topInclusion (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderTopInclusion f) = f := by
  rw [mappingCylinderTopInclusion, ← ContinuousMap.comp_assoc,
    mappingCylinderProjection_comp_cylinderInclusion]
  ext x
  rfl

/-- The canonical projection `M_f → Y` restricts on the source-faithful factorization map
`mappingCylinderFactorizationIn f` to `f`. -/
theorem mappingCylinderProjection_comp_factorizationIn (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderFactorizationIn f) = f := by
  simpa [mappingCylinderFactorizationIn] using mappingCylinderProjection_comp_topInclusion f

/-- Helper for Lemma 6.3.2: maps out of `f.mappingCylinder` agree once they agree on the target
and cylinder summands. -/
private theorem mappingCylinderHom_ext {Z : Type u} [TopologicalSpace Z] {f : C(X, Y)}
    {u v : C(f.mappingCylinder, Z)}
    (htarget :
      u.comp (mappingCylinderTargetInclusion f) = v.comp (mappingCylinderTargetInclusion f))
    (hcylinder :
      u.comp (mappingCylinderCylinderInclusion f) = v.comp (mappingCylinderCylinderInclusion f)) :
    u = v := by
  -- The pushout universal property reduces equality out of the mapping cylinder to its two legs.
  have hcat : TopCat.ofHom u = TopCat.ofHom v := by
    apply pushout.hom_ext
    · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom htarget
    · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hcylinder
  simpa using congrArg TopCat.Hom.hom hcat

/-- Diagnostic for Lemma 6.3.2: in the current Chapter 6 construction,
`mappingCylinderIn f` is the time-`0` slice of the cylinder summand, equivalently the composite
`X ⟶ Y ⟶ M_f`. This identifies the construction-level owner that is incompatible with the
textbook cofibration leg. -/
theorem mappingCylinderIn_eq_targetInclusion_comp (f : C(X, Y)) :
    mappingCylinderIn f = (mappingCylinderTargetInclusion f).comp f := by
  -- Unfold the source-side inclusion and rewrite with the pushout compatibility at time `0`.
  simpa [mappingCylinderIn] using (mappingCylinderTargetInclusion_comp f).symm

/-- Helper for Lemma 6.3.2: the time-`0` point on the cylinder side is glued to
`mappingCylinderTargetInclusion f (f x)`. -/
private theorem mappingCylinderCylinderInclusion_apply_zero (f : C(X, Y)) (x : X) :
    (mappingCylinderCylinderInclusion f) (x, 0) =
      mappingCylinderTargetInclusion f (f x) := by
  -- Evaluate the pushout compatibility relation at `x`.
  have hx :=
    congrArg (fun g : C(X, f.mappingCylinder) ↦ g x) (mappingCylinderTargetInclusion_comp f)
  simpa [ContinuousMap.mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hx.symm

/-- Helper for Lemma 6.3.2: the target inclusion determines the constant path at each `y : Y`. -/
private def mappingCylinderConstantPathMap (f : C(X, Y)) : C(Y, C(I, f.mappingCylinder)) :=
  ((mappingCylinderTargetInclusion f).comp ContinuousMap.fst).curry

@[simp] private theorem mappingCylinderConstantPathMap_apply (f : C(X, Y)) (y : Y) (t : I) :
    mappingCylinderConstantPathMap f y t = mappingCylinderTargetInclusion f y :=
  rfl

/-- Helper for Lemma 6.3.2: the scaled cylinder coordinate `(x, s, t) ↦ (x, t * s)`. -/
private def scaledCylinderCoordinateMap (X : Type u) [TopologicalSpace X] :
    C((X × I) × I, X × I) where
  toFun z := (z.1.1, z.2 * z.1.2)
  continuous_toFun := by
    refine Continuous.prodMk continuous_fst.fst ?_
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst.snd))
      (fun z ↦ unitInterval.mul_mem z.2.property z.1.2.property)

/-- Helper for Lemma 6.3.2: the cylinder side carries the path `t ↦ (x, t * s)` from
`(x, 0)` to `(x, s)`. -/
private def mappingCylinderScaledCylinderPathMap (f : C(X, Y)) :
    C(X × I, C(I, f.mappingCylinder)) :=
  ((mappingCylinderCylinderInclusion f).comp (scaledCylinderCoordinateMap X)).curry

/-- Helper for Lemma 6.3.2: at `s = 0`, the scaled cylinder path is the constant target path. -/
private theorem mappingCylinderScaledCylinderPathMap_apply_zero (f : C(X, Y)) (x : X) :
    mappingCylinderScaledCylinderPathMap f (x, 0) =
      mappingCylinderConstantPathMap f (f x) := by
  -- At time `0`, the cylinder point is glued to the target inclusion of `f x`.
  ext t
  simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap,
    mappingCylinderConstantPathMap, mappingCylinderCylinderInclusion_apply_zero]

/-- Helper for Lemma 6.3.2: at `s = 1`, the scaled cylinder path is the full cylinder path. -/
private theorem mappingCylinderScaledCylinderPathMap_apply_one (f : C(X, Y)) (x : X) :
    mappingCylinderScaledCylinderPathMap f (x, 1) =
      (mappingCylinderCylinderInclusion f).curry x := by
  -- Scaling by `1` leaves the cylinder parameter unchanged.
  ext t
  simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap]

/-- Helper for Lemma 6.3.2: on the source side, the mapping cylinder projection deformation is
the homotopy `s ↦ (x, t * s)` from the glued target point to the cylinder point. -/
private def mappingCylinderProjectionPathHomotopy (f : C(X, Y)) :
    ((mappingCylinderConstantPathMap f).comp f).Homotopy
      ((mappingCylinderCylinderInclusion f).curry) :=
  ContinuousMap.Homotopy.ofProdSwap
    (mappingCylinderScaledCylinderPathMap f)
    (mappingCylinderScaledCylinderPathMap_apply_zero f)
    (mappingCylinderScaledCylinderPathMap_apply_one f)

/-- Helper for Lemma 6.3.2: descending the constant target paths and the scaled cylinder paths
packages the deformation of `f.mappingCylinder` onto `Y`. -/
private def mappingCylinderProjectionDeformationPathMap (f : C(X, Y)) :
    C(f.mappingCylinder, C(I, f.mappingCylinder)) :=
  mappingCylinderDesc (mappingCylinderConstantPathMap f)
    (mappingCylinderProjectionPathHomotopy f)

/-- Helper for Lemma 6.3.2: evaluating the descended deformation at time `0` gives
`mappingCylinderTargetInclusion f ∘ mappingCylinderProjection f`. -/
private theorem mappingCylinderProjectionDeformationPathMap_evalZero (f : C(X, Y)) :
    (pathSpaceEvalAt 0 f.mappingCylinder).comp
        (mappingCylinderProjectionDeformationPathMap f) =
      (mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f) := by
  -- Compare the two maps on the two pushout legs of the mapping cylinder.
  apply mappingCylinderHom_ext
  · ext y
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap f)
            (mappingCylinderTargetInclusion f y) =
          mappingCylinderConstantPathMap f y := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(Y, C(I, f.mappingCylinder)) ↦ g y)
          (mappingCylinderDesc_comp_targetInclusion
            (mappingCylinderConstantPathMap f)
            (mappingCylinderProjectionPathHomotopy f))
    have hproj : (mappingCylinderProjection f) (mappingCylinderTargetInclusion f y) = y := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun g : C(Y, Y) ↦ g y) (mappingCylinderProjection_comp_targetInclusion f)
    calc
      ((pathSpaceEvalAt 0 f.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap f) |>.comp
          (mappingCylinderTargetInclusion f)) y =
        (pathSpaceEvalAt 0 f.mappingCylinder) (mappingCylinderConstantPathMap f y) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = mappingCylinderTargetInclusion f y := by
        simp [pathSpaceEvalAt]
      _ = ((mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f) |>.comp
            (mappingCylinderTargetInclusion f)) y := by
        simp [ContinuousMap.comp_apply, hproj]
  · ext z
    rcases z with ⟨x, s⟩
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap f)
            (mappingCylinderCylinderInclusion f (x, s)) =
          mappingCylinderScaledCylinderPathMap f (x, s) := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(X × I, C(I, f.mappingCylinder)) ↦ g (x, s))
          (mappingCylinderDesc_comp_cylinderInclusion
            (mappingCylinderConstantPathMap f)
            (mappingCylinderProjectionPathHomotopy f))
    have hproj :
        (mappingCylinderProjection f) (mappingCylinderCylinderInclusion f (x, s)) = f x := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun g : C(X × I, Y) ↦ g (x, s))
          (mappingCylinderProjection_comp_cylinderInclusion f)
    calc
      ((pathSpaceEvalAt 0 f.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap f) |>.comp
          (mappingCylinderCylinderInclusion f)) (x, s) =
        (pathSpaceEvalAt 0 f.mappingCylinder) (mappingCylinderScaledCylinderPathMap f (x, s)) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = mappingCylinderTargetInclusion f (f x) := by
        simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap, pathSpaceEvalAt,
          mappingCylinderCylinderInclusion_apply_zero]
      _ = ((mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f) |>.comp
            (mappingCylinderCylinderInclusion f)) (x, s) := by
        simp [ContinuousMap.comp_apply, hproj]

/-- Helper for Lemma 6.3.2: evaluating the descended deformation at time `1` gives the identity
on `f.mappingCylinder`. -/
private theorem mappingCylinderProjectionDeformationPathMap_evalOne (f : C(X, Y)) :
    (pathSpaceEvalAt 1 f.mappingCylinder).comp
        (mappingCylinderProjectionDeformationPathMap f) =
      ContinuousMap.id f.mappingCylinder := by
  -- The descended path is constant on `Y` and reaches the cylinder point at time `1`.
  apply mappingCylinderHom_ext
  · ext y
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap f)
            (mappingCylinderTargetInclusion f y) =
          mappingCylinderConstantPathMap f y := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(Y, C(I, f.mappingCylinder)) ↦ g y)
          (mappingCylinderDesc_comp_targetInclusion
            (mappingCylinderConstantPathMap f)
            (mappingCylinderProjectionPathHomotopy f))
    calc
      ((pathSpaceEvalAt 1 f.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap f) |>.comp
          (mappingCylinderTargetInclusion f)) y =
        (pathSpaceEvalAt 1 f.mappingCylinder) (mappingCylinderConstantPathMap f y) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = (ContinuousMap.id f.mappingCylinder).comp (mappingCylinderTargetInclusion f) y := by
        simp [pathSpaceEvalAt]
  · ext z
    rcases z with ⟨x, s⟩
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap f)
            (mappingCylinderCylinderInclusion f (x, s)) =
          mappingCylinderScaledCylinderPathMap f (x, s) := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(X × I, C(I, f.mappingCylinder)) ↦ g (x, s))
          (mappingCylinderDesc_comp_cylinderInclusion
            (mappingCylinderConstantPathMap f)
            (mappingCylinderProjectionPathHomotopy f))
    calc
      ((pathSpaceEvalAt 1 f.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap f) |>.comp
          (mappingCylinderCylinderInclusion f)) (x, s) =
        (pathSpaceEvalAt 1 f.mappingCylinder) (mappingCylinderScaledCylinderPathMap f (x, s)) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ =
          (ContinuousMap.id f.mappingCylinder).comp
            (mappingCylinderCylinderInclusion f) (x, s) := by
        simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap, pathSpaceEvalAt,
          ContinuousMap.comp_apply]

/-- Helper for Lemma 6.3.2: the target inclusion followed by the projection deforms to the
identity on the mapping cylinder. -/
private theorem mappingCylinderProjectionDeformationHomotopy (f : C(X, Y)) :
    ContinuousMap.Homotopic
      ((mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f))
      (ContinuousMap.id f.mappingCylinder) := by
  -- Package the descended path-space map as the required homotopy.
  refine ⟨ContinuousMap.Homotopy.ofPathSpaceMap
    (mappingCylinderProjectionDeformationPathMap f)
    (mappingCylinderProjectionDeformationPathMap_evalZero f)
    (mappingCylinderProjectionDeformationPathMap_evalOne f)⟩

/-- Helper for Lemma 6.3.2: on the new mapping cylinder of `mappingCylinderFactorizationIn f`,
the target copy of `Y` carries the constant path at its image in the target summand. -/
private def mappingCylinderFactorizationTargetPathMap (f : C(X, Y)) :
    C(Y, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) :=
  let i := mappingCylinderFactorizationIn f
  (((mappingCylinderTargetInclusion i).comp (mappingCylinderTargetInclusion f)).comp
    ContinuousMap.fst).curry

/-- Helper for Lemma 6.3.2: evaluating the target-side path map gives the constant path on the
target copy of the new mapping cylinder. -/
@[simp] private theorem mappingCylinderFactorizationTargetPathMap_apply (f : C(X, Y)) (y : Y)
    (t : I) :
    mappingCylinderFactorizationTargetPathMap f y t =
      (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
        (mappingCylinderTargetInclusion f y) :=
  rfl

/-- Helper for Lemma 6.3.2: the region `2s + t ≤ 2` in the square parameterizes the part of the
retract that still lives in the target summand of the new mapping cylinder. -/
private def mappingCylinderFactorizationTargetRegion (X : Type u) [TopologicalSpace X] :
    Set ((X × I) × I) :=
  { z | 2 * (z.1.2 : ℝ) + (z.2 : ℝ) ≤ 2 }

/-- Helper for Lemma 6.3.2: the rescaled old-cylinder coordinate used on the target branch always
lands in `I`. -/
private theorem mappingCylinderFactorizationTargetParameter_property
    {X' : Type u} (z : (X' × I) × I) :
    min ((z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ))) 1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hden : 0 < 1 - (z.2 : ℝ) * (1 / 2 : ℝ) := by
    nlinarith [z.2.property.2]
  have hnonneg :
      0 ≤ (z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ)) := by
    exact div_nonneg z.1.2.property.1 (le_of_lt hden)
  exact ⟨le_min hnonneg zero_le_one, min_le_right _ _⟩

/-- Helper for Lemma 6.3.2: the target-branch parameter depends continuously on the square
coordinates. -/
private theorem mappingCylinderFactorizationTargetParameter_continuous :
    Continuous fun z : (X × I) × I ↦
      min ((z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ))) 1 := by
  let hs : Continuous fun z : (X × I) × I ↦ (z.1.2 : ℝ) :=
    continuous_subtype_val.comp continuous_fst.snd
  let ht : Continuous fun z : (X × I) × I ↦ (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hden : Continuous fun z : (X × I) × I ↦ 1 - (z.2 : ℝ) * (1 / 2 : ℝ) := by
    exact continuous_const.sub (ht.mul continuous_const)
  have hquot : Continuous fun z : (X × I) × I ↦
      (z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ)) := by
    refine hs.div hden ?_
    intro z
    nlinarith [z.2.property.2]
  exact hquot.min continuous_const

/-- Helper for Lemma 6.3.2: the target-branch parameter packages the rescaled old-cylinder
coordinate into a bundled map to `I`. -/
private def mappingCylinderFactorizationTargetParameterMap (X : Type u) [TopologicalSpace X] :
    C((X × I) × I, I) where
  toFun z :=
    ⟨min ((z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ))) 1,
      mappingCylinderFactorizationTargetParameter_property z⟩
  continuous_toFun :=
    Continuous.subtype_mk
      mappingCylinderFactorizationTargetParameter_continuous
      (fun z ↦ mappingCylinderFactorizationTargetParameter_property z)

/-- Helper for Lemma 6.3.2: on the complementary region, the new cylinder parameter is the
clamped affine coordinate `max (2s + t - 2) 0`. -/
private theorem mappingCylinderFactorizationCylinderParameter_property
    {X' : Type u} (z : (X' × I) × I) :
    max (2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2) 0 ∈ Set.Icc (0 : ℝ) 1 := by
  have hupper : 2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2 ≤ 1 := by
    nlinarith [z.1.2.property.2, z.2.property.2]
  exact ⟨le_max_right _ _, max_le hupper zero_le_one⟩

/-- Helper for Lemma 6.3.2: the new-cylinder branch parameter varies continuously over the whole
square. -/
private theorem mappingCylinderFactorizationCylinderParameter_continuous :
    Continuous fun z : (X × I) × I ↦ max (2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2) 0 := by
  let hs : Continuous fun z : (X × I) × I ↦ (z.1.2 : ℝ) :=
    continuous_subtype_val.comp continuous_fst.snd
  let ht : Continuous fun z : (X × I) × I ↦ (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hlin : Continuous fun z : (X × I) × I ↦ 2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2 := by
    exact (continuous_const.mul hs).add ht |>.sub continuous_const
  exact hlin.max continuous_const

/-- Helper for Lemma 6.3.2: the complementary branch parameter packages the affine formula into a
bundled map to `I`. -/
private def mappingCylinderFactorizationCylinderParameterMap (X : Type u) [TopologicalSpace X] :
    C((X × I) × I, I) where
  toFun z :=
    ⟨max (2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2) 0,
      mappingCylinderFactorizationCylinderParameter_property z⟩
  continuous_toFun :=
    Continuous.subtype_mk
      mappingCylinderFactorizationCylinderParameter_continuous
      (fun z ↦ mappingCylinderFactorizationCylinderParameter_property z)

/-- Helper for Lemma 6.3.2: on the target-side region of the square, the retract follows the old
cylinder inside the target summand of the new mapping cylinder. -/
private def mappingCylinderFactorizationTargetBranch (f : C(X, Y)) :
    C((X × I) × I, (mappingCylinderFactorizationIn f).mappingCylinder) :=
  let i := mappingCylinderFactorizationIn f
  (mappingCylinderTargetInclusion i).comp
    ((mappingCylinderCylinderInclusion f).comp
      ((ContinuousMap.fst.comp ContinuousMap.fst).prodMk
        (mappingCylinderFactorizationTargetParameterMap X)))

/-- Helper for Lemma 6.3.2: on the complementary region of the square, the retract runs through
the new cylinder summand. -/
private def mappingCylinderFactorizationCylinderBranch (f : C(X, Y)) :
    C((X × I) × I, (mappingCylinderFactorizationIn f).mappingCylinder) :=
  let i := mappingCylinderFactorizationIn f
  (mappingCylinderCylinderInclusion i).comp
    ((ContinuousMap.fst.comp ContinuousMap.fst).prodMk
      (mappingCylinderFactorizationCylinderParameterMap X))

/-- Helper for Lemma 6.3.2: along the interface `2s + t = 2`, the target and cylinder branches
meet at the glued top point of the new mapping cylinder. -/
private theorem mappingCylinderFactorizationBranches_agree_on_frontier (f : C(X, Y))
    (z : (X × I) × I)
    (hz : z ∈ frontier (mappingCylinderFactorizationTargetRegion X)) :
    mappingCylinderFactorizationTargetBranch f z =
      mappingCylinderFactorizationCylinderBranch f z := by
  let i := mappingCylinderFactorizationIn f
  -- Frontier points satisfy `2s + t = 2`, so the two branch parameters become `1` and `0`.
  have hclosed : IsClosed (mappingCylinderFactorizationTargetRegion X) := by
    let hs : Continuous fun w : (X × I) × I ↦ 2 * (w.1.2 : ℝ) + (w.2 : ℝ) :=
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst.snd)).add
        (continuous_subtype_val.comp continuous_snd)
    simpa [mappingCylinderFactorizationTargetRegion] using isClosed_le hs continuous_const
  rw [hclosed.frontier_eq] at hz
  rcases hz with ⟨hmem, hz_not_interior⟩
  have hEq : 2 * (z.1.2 : ℝ) + (z.2 : ℝ) = 2 := by
    have hnotlt : ¬ 2 * (z.1.2 : ℝ) + (z.2 : ℝ) < 2 := by
      intro hlt
      let U : Set ((X × I) × I) := {w | 2 * (w.1.2 : ℝ) + (w.2 : ℝ) < 2}
      have hopen : IsOpen U := by
        let hs : Continuous fun w : (X × I) × I ↦ 2 * (w.1.2 : ℝ) + (w.2 : ℝ) :=
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst.snd)).add
            (continuous_subtype_val.comp continuous_snd)
        simpa [U] using isOpen_lt hs continuous_const
      have hsubset : U ⊆ mappingCylinderFactorizationTargetRegion X := by
        intro w hw
        simpa [U, mappingCylinderFactorizationTargetRegion] using le_of_lt hw
      have hz_int : z ∈ interior (mappingCylinderFactorizationTargetRegion X) := by
        rw [mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (IsOpen.mem_nhds hopen hlt) hsubset
      exact hz_not_interior hz_int
    have hle : 2 * (z.1.2 : ℝ) + (z.2 : ℝ) ≤ 2 := hmem
    nlinarith
  have htargetParam : mappingCylinderFactorizationTargetParameterMap X z = 1 := by
    apply Subtype.ext
    have hden : 0 < 1 - (z.2 : ℝ) * (1 / 2 : ℝ) := by
      nlinarith [z.2.property.2]
    have hs : (z.1.2 : ℝ) = 1 - (z.2 : ℝ) * (1 / 2 : ℝ) := by
      nlinarith [hEq]
    have hquot : (z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ)) = 1 := by
      have hden_ne : 1 - (z.2 : ℝ) * (1 / 2 : ℝ) ≠ 0 := by
        linarith
      rw [hs, div_self hden_ne]
    change min ((z.1.2 : ℝ) / (1 - (z.2 : ℝ) * (1 / 2 : ℝ))) 1 = (1 : ℝ)
    rw [hquot]
    simp
  have hcylinderParam : mappingCylinderFactorizationCylinderParameterMap X z = 0 := by
    apply Subtype.ext
    change max (2 * (z.1.2 : ℝ) + (z.2 : ℝ) - 2) 0 = (0 : ℝ)
    simp [hEq]
  have hglue :
      (mappingCylinderTargetInclusion i) ((mappingCylinderCylinderInclusion f) (z.1.1, 1)) =
        (mappingCylinderCylinderInclusion i) (z.1.1, 0) := by
    -- Evaluate the pushout relation for the new mapping cylinder at the source point `z.1.1`.
    have hx :=
      congrArg (fun g : C(X, i.mappingCylinder) ↦ g z.1.1)
        (mappingCylinderTargetInclusion_comp i)
    simpa [i, mappingCylinderFactorizationIn, mappingCylinderTopInclusion,
      mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hx
  calc
    mappingCylinderFactorizationTargetBranch f z =
      (mappingCylinderTargetInclusion i) ((mappingCylinderCylinderInclusion f) (z.1.1, 1)) := by
        simp [mappingCylinderFactorizationTargetBranch, i, htargetParam]
    _ = (mappingCylinderCylinderInclusion i) (z.1.1, 0) := hglue
    _ = mappingCylinderFactorizationCylinderBranch f z := by
        simp [mappingCylinderFactorizationCylinderBranch, i, hcylinderParam]

/-- Helper for Lemma 6.3.2: the geometric square filler into the new mapping cylinder is obtained
by gluing the target and cylinder branches along the interface `2s + t = 2`. -/
private def mappingCylinderFactorizationRetractSquareMap (f : C(X, Y)) :
    C((X × I) × I, (mappingCylinderFactorizationIn f).mappingCylinder) where
  toFun :=
    let _ : ∀ a, Decidable (a ∈ mappingCylinderFactorizationTargetRegion X) := Classical.decPred _
    Set.piecewise (mappingCylinderFactorizationTargetRegion X)
      (mappingCylinderFactorizationTargetBranch f)
      (mappingCylinderFactorizationCylinderBranch f)
  continuous_toFun :=
    let _ : ∀ a, Decidable (a ∈ mappingCylinderFactorizationTargetRegion X) := Classical.decPred _
    (mappingCylinderFactorizationTargetBranch f).continuous.piecewise
      (mappingCylinderFactorizationBranches_agree_on_frontier f)
      (mappingCylinderFactorizationCylinderBranch f).continuous

/-- Helper for Lemma 6.3.2: currying the geometric square filler packages the cylinder-side data
needed to descend a retract path map through the original mapping cylinder. -/
private def mappingCylinderFactorizationRetractCylinderPathMap (f : C(X, Y)) :
    C(X × I, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) :=
  (mappingCylinderFactorizationRetractSquareMap f).curry

/-- Helper for Lemma 6.3.2: along `s = 0`, the square filler is the constant target-side path. -/
private theorem mappingCylinderFactorizationRetractSquareMap_apply_zero (f : C(X, Y)) (x : X) :
    mappingCylinderFactorizationRetractCylinderPathMap f (x, 0) =
      mappingCylinderFactorizationTargetPathMap f (f x) := by
  -- On the bottom edge `s = 0`, the piecewise filler stays on the target branch and lands at
  -- the glued target point `mappingCylinderTargetInclusion f (f x)`.
  ext t
  have hmem : ((x, 0), t) ∈ mappingCylinderFactorizationTargetRegion X := by
    dsimp [mappingCylinderFactorizationTargetRegion]
    nlinarith [t.property.2]
  have hparam : mappingCylinderFactorizationTargetParameterMap X ((x, 0), t) = 0 := by
    apply Subtype.ext
    change min (((0 : I) : ℝ) / (1 - (t : ℝ) * (1 / 2 : ℝ))) 1 = (0 : ℝ)
    simp
  calc
    mappingCylinderFactorizationRetractCylinderPathMap f (x, 0) t =
      mappingCylinderFactorizationTargetBranch f ((x, 0), t) := by
        simp [mappingCylinderFactorizationRetractCylinderPathMap,
          mappingCylinderFactorizationRetractSquareMap, hmem]
    _ =
        (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
          (mappingCylinderTargetInclusion f (f x)) := by
        simp [mappingCylinderFactorizationTargetBranch, hparam,
          mappingCylinderCylinderInclusion_apply_zero]
    _ = mappingCylinderFactorizationTargetPathMap f (f x) t := by
        symm
        exact mappingCylinderFactorizationTargetPathMap_apply f (f x) t

/-- Helper for Lemma 6.3.2: along `s = 1`, the square filler is exactly the new cylinder
inclusion. -/
private theorem mappingCylinderFactorizationRetractSquareMap_apply_one (f : C(X, Y)) (x : X) :
    mappingCylinderFactorizationRetractCylinderPathMap f (x, 1) =
      (mappingCylinderCylinderInclusion (mappingCylinderFactorizationIn f)).curry x := by
  let i := mappingCylinderFactorizationIn f
  -- On the top edge `s = 1`, the filler reaches the new cylinder inclusion.
  ext t
  by_cases ht : (t : I) = 0
  · have hmem : ((x, 1), t) ∈ mappingCylinderFactorizationTargetRegion X := by
      simp [mappingCylinderFactorizationTargetRegion, ht]
    have hparam : mappingCylinderFactorizationTargetParameterMap X ((x, 1), t) = 1 := by
      apply Subtype.ext
      simp [mappingCylinderFactorizationTargetParameterMap, ht]
    have hglue :
        (mappingCylinderTargetInclusion i) ((mappingCylinderCylinderInclusion f) (x, 1)) =
          (mappingCylinderCylinderInclusion i) (x, 0) := by
      -- At `t = 0`, the target copy of the top point is glued to the new cylinder base point.
      have hx :=
        congrArg (fun g : C(X, i.mappingCylinder) ↦ g x)
          (mappingCylinderTargetInclusion_comp i)
      simpa [i, mappingCylinderFactorizationIn, mappingCylinderTopInclusion,
        mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hx
    calc
      mappingCylinderFactorizationRetractCylinderPathMap f (x, 1) t =
        mappingCylinderFactorizationTargetBranch f ((x, 1), t) := by
          simp [mappingCylinderFactorizationRetractCylinderPathMap,
            mappingCylinderFactorizationRetractSquareMap, hmem]
      _ = (mappingCylinderTargetInclusion i) ((mappingCylinderCylinderInclusion f) (x, 1)) := by
          simp [mappingCylinderFactorizationTargetBranch, i, hparam]
      _ = (mappingCylinderCylinderInclusion i) (x, 0) := hglue
      _ = (mappingCylinderCylinderInclusion i).curry x t := by
          simp [ht]
  · have hnotmem : ((x, 1), t) ∉ mappingCylinderFactorizationTargetRegion X := by
      intro hmem
      have hneq : (t : ℝ) ≠ 0 := by
        intro hzero
        apply ht
        exact Subtype.ext hzero
      have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm hneq)
      have hle : (t : ℝ) ≤ 0 := by
        simpa [mappingCylinderFactorizationTargetRegion] using hmem
      nlinarith
    have hparam : mappingCylinderFactorizationCylinderParameterMap X ((x, 1), t) = t := by
      apply Subtype.ext
      change max (2 * ((1 : I) : ℝ) + (t : ℝ) - 2) 0 = (t : ℝ)
      have hcoord : 2 * ((1 : I) : ℝ) + (t : ℝ) - 2 = (t : ℝ) := by norm_num
      rw [hcoord]
      exact max_eq_left t.property.1
    calc
      mappingCylinderFactorizationRetractCylinderPathMap f (x, 1) t =
        mappingCylinderFactorizationCylinderBranch f ((x, 1), t) := by
          simp [mappingCylinderFactorizationRetractCylinderPathMap,
            mappingCylinderFactorizationRetractSquareMap, hnotmem]
      _ = (mappingCylinderCylinderInclusion i) (x, t) := by
          simp [mappingCylinderFactorizationCylinderBranch, i, hparam]
      _ = (mappingCylinderCylinderInclusion i).curry x t := by
          rfl

/-- Helper for Lemma 6.3.2: the descended square filler is a homotopy from the constant target
path map to the new cylinder path. -/
private def mappingCylinderFactorizationRetractCylinderHomotopy (f : C(X, Y)) :
    ((mappingCylinderFactorizationTargetPathMap f).comp f).Homotopy
      ((mappingCylinderCylinderInclusion (mappingCylinderFactorizationIn f)).curry) :=
  ContinuousMap.Homotopy.ofProdSwap
    (mappingCylinderFactorizationRetractCylinderPathMap f)
    (mappingCylinderFactorizationRetractSquareMap_apply_zero f)
    (mappingCylinderFactorizationRetractSquareMap_apply_one f)

/-- Helper for Lemma 6.3.2: descending the target-side constant path map and the geometric square
filler gives a path-space map on `f.mappingCylinder`. -/
private def mappingCylinderFactorizationRetractPathMap (f : C(X, Y)) :
    C(f.mappingCylinder, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) :=
  mappingCylinderDesc (mappingCylinderFactorizationTargetPathMap f)
    (mappingCylinderFactorizationRetractCylinderHomotopy f)

/-- Helper for Lemma 6.3.2: evaluating the descended path-space map at time `0` recovers the
target inclusion of the new mapping cylinder. -/
private theorem mappingCylinderFactorizationRetractPathMap_evalZero (f : C(X, Y)) :
    (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder).comp
        (mappingCylinderFactorizationRetractPathMap f) =
      mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f) := by
  -- Compare the descended path-space map on the target summand and the cylinder summand of
  -- `f.mappingCylinder`.
  apply mappingCylinderHom_ext
  · ext y
    have hdesc :
        (mappingCylinderFactorizationRetractPathMap f)
            (mappingCylinderTargetInclusion f y) =
          mappingCylinderFactorizationTargetPathMap f y := by
      simpa [mappingCylinderFactorizationRetractPathMap] using
        congrArg
          (fun g :
            C(Y, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) ↦ g y)
          (mappingCylinderDesc_comp_targetInclusion
            (mappingCylinderFactorizationTargetPathMap f)
            (mappingCylinderFactorizationRetractCylinderHomotopy f))
    calc
      ((pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder).comp
          (mappingCylinderFactorizationRetractPathMap f) |>.comp
          (mappingCylinderTargetInclusion f)) y =
        (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder)
          (mappingCylinderFactorizationTargetPathMap f y) := by
            simp [ContinuousMap.comp_apply, hdesc]
      _ =
          (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
            (mappingCylinderTargetInclusion f y) := by
            simp [pathSpaceEvalAt]
      _ =
          ((mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f)).comp
            (mappingCylinderTargetInclusion f)) y := by
            rfl
  · ext z
    rcases z with ⟨x, s⟩
    have hdesc :
        (mappingCylinderFactorizationRetractPathMap f)
            (mappingCylinderCylinderInclusion f (x, s)) =
          mappingCylinderFactorizationRetractCylinderPathMap f (x, s) := by
      simpa [mappingCylinderFactorizationRetractPathMap,
        mappingCylinderFactorizationRetractCylinderHomotopy] using
        congrArg
          (fun g :
            C(X × I, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) ↦ g (x, s))
          (mappingCylinderDesc_comp_cylinderInclusion
            (mappingCylinderFactorizationTargetPathMap f)
            (mappingCylinderFactorizationRetractCylinderHomotopy f))
    have hzero :
        (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder)
            (mappingCylinderFactorizationRetractCylinderPathMap f (x, s)) =
          (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
            ((mappingCylinderCylinderInclusion f) (x, s)) := by
      have hmem : ((x, s), 0) ∈ mappingCylinderFactorizationTargetRegion X := by
        dsimp [mappingCylinderFactorizationTargetRegion]
        nlinarith [s.property.2]
      have hparam : mappingCylinderFactorizationTargetParameterMap X ((x, s), 0) = s := by
        apply Subtype.ext
        change min ((s : ℝ) / (1 - ((0 : I) : ℝ) * (1 / 2 : ℝ))) 1 = (s : ℝ)
        have hden0 : (1 - ((0 : I) : ℝ) * (1 / 2 : ℝ)) = (1 : ℝ) := by norm_num
        rw [hden0, div_one]
        exact min_eq_left s.property.2
      calc
        (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder)
            (mappingCylinderFactorizationRetractCylinderPathMap f (x, s)) =
          mappingCylinderFactorizationRetractCylinderPathMap f (x, s) 0 := rfl
        _ = mappingCylinderFactorizationRetractSquareMap f ((x, s), 0) := by
            rfl
        _ = mappingCylinderFactorizationTargetBranch f ((x, s), 0) := by
            simp [mappingCylinderFactorizationRetractSquareMap, hmem]
        _ =
            (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
              ((mappingCylinderCylinderInclusion f) (x, s)) := by
            simp [mappingCylinderFactorizationTargetBranch, hparam]
    calc
      ((pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder).comp
          (mappingCylinderFactorizationRetractPathMap f) |>.comp
          (mappingCylinderCylinderInclusion f)) (x, s) =
        (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder)
          ((mappingCylinderFactorizationRetractPathMap f)
            (mappingCylinderCylinderInclusion f (x, s))) := by
            rfl
      _ =
          (pathSpaceEvalAt 0 (mappingCylinderFactorizationIn f).mappingCylinder)
            (mappingCylinderFactorizationRetractCylinderPathMap f (x, s)) := by
            rw [hdesc]
      _ =
          (mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f))
            ((mappingCylinderCylinderInclusion f) (x, s)) := hzero
      _ =
          ((mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f)).comp
            (mappingCylinderCylinderInclusion f)) (x, s) := by
            rfl

/-- Helper for Lemma 6.3.2: on the top slice `mappingCylinderFactorizationIn f`, the descended
path-space map is the new cylinder inclusion. -/
private theorem mappingCylinderFactorizationRetractPathMap_comp_factorizationIn (f : C(X, Y)) :
    (mappingCylinderFactorizationRetractPathMap f).comp (mappingCylinderFactorizationIn f) =
      (mappingCylinderCylinderInclusion (mappingCylinderFactorizationIn f)).curry := by
  -- The top inclusion factors through the old cylinder side at `s = 1`, so the descended path
  -- map is read off from the `s = 1` slice of the square filler.
  ext x t
  have hdesc :
      (mappingCylinderFactorizationRetractPathMap f)
          ((mappingCylinderFactorizationIn f) x) =
        mappingCylinderFactorizationRetractCylinderPathMap f (x, 1) := by
    simpa [mappingCylinderFactorizationIn, mappingCylinderTopInclusion,
      mappingCylinderFactorizationRetractPathMap,
      mappingCylinderFactorizationRetractCylinderHomotopy, ContinuousMap.comp_apply] using
      congrArg
        (fun g :
          C(X × I, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) ↦ g (x, 1))
        (mappingCylinderDesc_comp_cylinderInclusion
          (mappingCylinderFactorizationTargetPathMap f)
          (mappingCylinderFactorizationRetractCylinderHomotopy f))
  calc
    ((mappingCylinderFactorizationRetractPathMap f).comp (mappingCylinderFactorizationIn f)) x t =
      mappingCylinderFactorizationRetractCylinderPathMap f (x, 1) t := by
        simpa [ContinuousMap.comp_apply] using congrArg
          (fun γ : C(I, (mappingCylinderFactorizationIn f).mappingCylinder) ↦ γ t) hdesc
    _ = (mappingCylinderCylinderInclusion (mappingCylinderFactorizationIn f)).curry x t := by
        simpa using congrArg
          (fun γ : C(I, (mappingCylinderFactorizationIn f).mappingCylinder) ↦ γ t)
          (mappingCylinderFactorizationRetractSquareMap_apply_one f x)

/-- Helper for Lemma 6.3.2: swapping the descended path-space map gives the desired retract
`f.mappingCylinder × I ⟶ M_(mappingCylinderFactorizationIn f)`. -/
private def mappingCylinderFactorizationRetract (f : C(X, Y)) :
    C(f.mappingCylinder × I, (mappingCylinderFactorizationIn f).mappingCylinder) :=
  (mappingCylinderFactorizationRetractPathMap f).uncurry

/-- Helper for Lemma 6.3.2: the retract restricts on `f.mappingCylinder × {0}` to the target
inclusion of the new mapping cylinder. -/
private theorem mappingCylinderFactorizationRetract_comp_timeZero (f : C(X, Y)) :
    (mappingCylinderFactorizationRetract f).comp
        (mappingCylinderTimeZeroInclusion f.mappingCylinder) =
      mappingCylinderTargetInclusion (mappingCylinderFactorizationIn f) := by
  -- Uncurrying the descended path-space map and restricting to `t = 0` is exactly evaluation at
  -- time `0`.
  ext z
  have hz :=
    congrArg
      (fun g :
        C(f.mappingCylinder, (mappingCylinderFactorizationIn f).mappingCylinder) ↦ g z)
      (mappingCylinderFactorizationRetractPathMap_evalZero f)
  simpa [mappingCylinderFactorizationRetract, mappingCylinderTimeZeroInclusion,
    pathSpaceEvalAt, ContinuousMap.comp_apply] using hz

/-- Helper for Lemma 6.3.2: the retract restricts on the canonical cylinder map
`X × I ⟶ f.mappingCylinder × I` to the new cylinder inclusion. -/
private theorem mappingCylinderFactorizationRetract_comp_cylinderMap (f : C(X, Y)) :
    (mappingCylinderFactorizationRetract f).comp
        (mappingCylinderCylinderMap (mappingCylinderFactorizationIn f)) =
      mappingCylinderCylinderInclusion (mappingCylinderFactorizationIn f) := by
  -- Uncurrying and then restricting along the canonical cylinder map recovers evaluation of the
  -- descended path-space map on the top inclusion.
  ext z
  rcases z with ⟨x, s⟩
  have hx :=
    congrArg
      (fun g :
        C(X, C(I, (mappingCylinderFactorizationIn f).mappingCylinder)) ↦ g x)
      (mappingCylinderFactorizationRetractPathMap_comp_factorizationIn f)
  have hs := congrArg (fun γ : C(I, (mappingCylinderFactorizationIn f).mappingCylinder) ↦ γ s) hx
  simpa [mappingCylinderFactorizationRetract, ContinuousMap.comp_apply,
    mappingCylinderCylinderMap_apply] using hs

/-- Helper for Lemma 6.3.2: the top slice `t = 1` of the cylinder summand is a cofibration. -/
private theorem mappingCylinderTopInclusion_isCofibration (f : C(X, Y)) :
    IsCofibration.{u, u, u} (mappingCylinderTopInclusion f) := by
  -- The constructed retract satisfies the endpoint and cylinder boundary conditions from
  -- Construction 6.2.2.
  exact ContinuousMap.isCofibration_of_mappingCylinderRetract
    (mappingCylinderFactorizationRetract f)
    (mappingCylinderFactorizationRetract_comp_timeZero f)
    (mappingCylinderFactorizationRetract_comp_cylinderMap f)

/-- Lemma 6.3.2 (1): in the mapping cylinder factorization
`X ⟶ M_f ⟶ Y`, the first map is a cofibration.

In the current Chapter 6 implementation, the source-faithful factorization map is
`mappingCylinderFactorizationIn f`; `Construction_6_3_1.mappingCylinderIn f` still denotes the
glued time-`0` map recorded by `mappingCylinderIn_eq_targetInclusion_comp`. -/
theorem mappingCylinderFactorizationIn_isCofibration (f : C(X, Y)) :
    IsCofibration.{u, u, u} (mappingCylinderFactorizationIn f) := by
  -- Route correction: the factorization map is definitionally the top-slice inclusion, so the
  -- cofibration proof should transfer directly from the existing retract-based helper.
  intro Z _ f₀ g H
  -- Unpack the homotopy-extension property so the target codomain is fixed before reducing the
  -- factorization map abbreviation.
  simpa [mappingCylinderFactorizationIn] using
    (mappingCylinderTopInclusion_isCofibration f) f₀ g H

/-- Lemma 6.3.2 (2): in the mapping cylinder factorization of `f : C(X, Y)`, the canonical
projection `M_f → Y`, implemented as `mappingCylinderProjection f`, is a homotopy equivalence. -/
def mappingCylinderProjection_homotopyEquiv (f : C(X, Y)) :
    f.mappingCylinder ≃ₕ Y where
  toFun := mappingCylinderProjection f
  invFun := mappingCylinderTargetInclusion f
  left_inv := by
    -- Use the descended deformation that collapses each cylinder line onto the target copy of `Y`.
    exact mappingCylinderProjectionDeformationHomotopy f
  right_inv := by
    -- On the target copy, the projection is already literally the identity.
    simpa [mappingCylinderProjection_comp_targetInclusion] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id Y))

/-- The forward map of `mappingCylinderProjection_homotopyEquiv f` is the canonical projection
`mappingCylinderProjection f`. -/
@[simp] theorem mappingCylinderProjection_homotopyEquiv_toFun (f : C(X, Y)) :
    (mappingCylinderProjection_homotopyEquiv f).toFun = mappingCylinderProjection f :=
  rfl

/-- The homotopy equivalence `mappingCylinderProjection_homotopyEquiv f` is realized by the
canonical projection `M_f ⟶ Y` and the canonical target inclusion `Y ⟶ M_f`. -/
theorem mappingCylinderProjection_homotopyEquiv_spec (f : C(X, Y)) :
    (mappingCylinderProjection_homotopyEquiv f).toFun = mappingCylinderProjection f ∧
      (mappingCylinderProjection_homotopyEquiv f).invFun = mappingCylinderTargetInclusion f := by
  -- Both structure fields were defined by the canonical projection and target inclusion.
  exact ⟨rfl, rfl⟩

/-- The canonical projection `M_f ⟶ Y` composed with the target inclusion `Y ⟶ M_f` is
homotopic to `id_Y`. -/
theorem mappingCylinderProjection_comp_targetInclusion_homotopic_id (f : C(X, Y)) :
    ContinuousMap.Homotopic
      ((mappingCylinderProjection f).comp (mappingCylinderTargetInclusion f))
      (ContinuousMap.id Y) :=
  (mappingCylinderProjection_homotopyEquiv f).right_inv

/-- The inverse map of `mappingCylinderProjection_homotopyEquiv f` is the canonical target
inclusion `mappingCylinderTargetInclusion f`. -/
@[simp] theorem mappingCylinderProjection_homotopyEquiv_invFun (f : C(X, Y)) :
    (mappingCylinderProjection_homotopyEquiv f).invFun = mappingCylinderTargetInclusion f :=
  rfl

/-- The target inclusion `Y ⟶ M_f` composed with the canonical projection `M_f ⟶ Y` is homotopic
to `ContinuousMap.id f.mappingCylinder`. -/
theorem mappingCylinderTargetInclusion_comp_projection_homotopic_id (f : C(X, Y)) :
    ContinuousMap.Homotopic
      ((mappingCylinderTargetInclusion f).comp (mappingCylinderProjection f))
      (ContinuousMap.id f.mappingCylinder) :=
  (mappingCylinderProjection_homotopyEquiv f).left_inv

/-- Evaluating `mappingCylinderProjection_homotopyEquiv f` on a point of `f.mappingCylinder`
agrees with the canonical projection `mappingCylinderProjection f`. -/
@[simp] theorem mappingCylinderProjection_homotopyEquiv_apply (f : C(X, Y))
    (x : f.mappingCylinder) :
    mappingCylinderProjection_homotopyEquiv f x = mappingCylinderProjection f x :=
  rfl

/-- Evaluating the inverse of `mappingCylinderProjection_homotopyEquiv f` agrees with the
canonical target inclusion `mappingCylinderTargetInclusion f`. -/
@[simp] theorem mappingCylinderProjection_homotopyEquiv_symm_apply (f : C(X, Y)) (y : Y) :
    (mappingCylinderProjection_homotopyEquiv f).symm y = mappingCylinderTargetInclusion f y :=
  rfl

end
