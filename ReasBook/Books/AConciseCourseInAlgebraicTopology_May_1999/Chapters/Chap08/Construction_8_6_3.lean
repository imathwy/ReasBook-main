import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1

open CategoryTheory Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Construction 8.6.3 is stated for arbitrary based topological spaces.  Its mapping-path
-- replacement therefore uses the ordinary pullback-subspace topology, rather than Chapter 7's
-- subsequent compactly generated replacement.

/-- The standard mapping-path replacement of a based map `f : X ⟶ Y`, with its ordinary
pullback-subspace topology.  This is an independent structure so Chapter 7's kified subtype
topology cannot be selected by typeclass inference. -/
structure MappingPathReplacement {X Y : BasedSpace} (f : X ⟶ Y) where
  point : X.right
  path : C(I, Y.right)
  compat : path 0 = f.right.hom point

namespace MappingPathReplacement

variable {X Y : BasedSpace} {f : X ⟶ Y}

/-- The mapping-path replacement inherits the ordinary subtype topology from
`X × C(I, Y)`. -/
instance instTopologicalSpace : TopologicalSpace (MappingPathReplacement f) :=
  TopologicalSpace.induced (fun z ↦ (z.point, z.path)) inferInstance

/-- Forgetting the defining equation is continuous for the ordinary subtype topology. -/
theorem continuous_subtypeVal :
    Continuous (fun z : MappingPathReplacement f ↦ (z.point, z.path)) := by
  exact continuous_induced_dom

/-- A continuously varying compatible point-path pair gives a continuous map into the ordinary
mapping-path replacement. -/
theorem continuous_mk
    {A : Type*} [TopologicalSpace A] {x : A → X.right} {γ : A → C(I, Y.right)}
    (hx : Continuous x) (hγ : Continuous γ)
    (hsource : ∀ a, γ a 0 = f.right.hom (x a)) :
    Continuous fun a ↦
      ({ point := x a, path := γ a, compat := hsource a } :
        MappingPathReplacement f) := by
  rw [continuous_induced_rng]
  exact hx.prodMk hγ

/-- The path coordinate of `z : MappingPathReplacement f`, regarded as a path in `Y` beginning at
`f(z.point)`. -/
def toPath (z : MappingPathReplacement f) : Path (f.right.hom z.point) (z.path 1) where
  toContinuousMap := z.path
  source' := z.compat
  target' := rfl

/-- The endpoint in `Y` underlying an element of `MappingPathReplacement f`. -/
def endpoint (z : MappingPathReplacement f) : Y.right :=
  z.path 1

/-- Construct an element of `MappingPathReplacement f` from a point of `X` and a path in `Y`
starting at its image under `f`. -/
def ofPath (x : X.right) {y : Y.right} (γ : Path (f.right.hom x) y) :
    MappingPathReplacement f :=
  { point := x
    path := γ.toContinuousMap
    compat := γ.source' }

@[simp] theorem point_ofPath (x : X.right) {y : Y.right} (γ : Path (f.right.hom x) y) :
    (ofPath x γ).point = x :=
  rfl

@[simp] theorem path_ofPath (x : X.right) {y : Y.right} (γ : Path (f.right.hom x) y) :
    (ofPath x γ).path = γ.toContinuousMap :=
  rfl

/-- The defining condition on `z : MappingPathReplacement f` says that its path starts at
`f(z.point)`. -/
@[simp] theorem source_eq (z : MappingPathReplacement f) : z.path 0 = f.right.hom z.point :=
  z.compat

/-- The endpoint of the path component of `z` is `z.endpoint`. -/
@[simp] theorem target_eq (z : MappingPathReplacement f) : z.path 1 = z.endpoint :=
  rfl

@[simp] theorem endpoint_ofPath (x : X.right) {y : Y.right} (γ : Path (f.right.hom x) y) :
    endpoint (ofPath x γ) = y := by
  change γ.toContinuousMap 1 = y
  exact γ.target'

@[ext] theorem ext {z z' : MappingPathReplacement f}
    (hpoint : z.point = z'.point) (hpath : z.path = z'.path) : z = z' := by
  cases z
  cases z'
  cases hpoint
  cases hpath
  rfl

/-- The constant path at `f(underTopBasepoint X)` defines the canonical basepoint of
`MappingPathReplacement f`. -/
def basepoint (f : X ⟶ Y) : MappingPathReplacement f :=
  ofPath (underTopBasepoint X)
    (Path.refl (f.right.hom (underTopBasepoint X)))

/-- Endpoint evaluation on the ordinary mapping-path replacement. -/
def projection (f : X ⟶ Y) : C(MappingPathReplacement f, Y.right) where
  toFun z := z.endpoint
  continuous_toFun := by
    exact (continuous_eval_const (1 : I)).comp
      (continuous_snd.comp continuous_subtypeVal)

/-- The constant-path inclusion into the ordinary mapping-path replacement. -/
def inclusion (f : X ⟶ Y) : C(X.right, MappingPathReplacement f) where
  toFun x := ofPath x (Path.refl (f.right.hom x))
  continuous_toFun := by
    have hconst : Continuous fun x : X.right ↦ ContinuousMap.const I (f.right.hom x) := by
      exact ContinuousMap.continuous_const'.comp f.right.hom.continuous
    exact continuous_mk continuous_id hconst (fun _ ↦ rfl)

@[simp] theorem projection_apply (f : X ⟶ Y) (z : MappingPathReplacement f) :
    projection f z = z.endpoint :=
  rfl

@[simp] theorem inclusion_apply (f : X ⟶ Y) (x : X.right) :
    inclusion f x = ofPath x (Path.refl (f.right.hom x)) :=
  rfl

end MappingPathReplacement

/-- The chosen basepoint of the mapping-path replacement is the constant path at the image of the
basepoint of `X` under `f`. -/
@[simp] theorem mappingPathReplacement_basepoint_eq {X Y : BasedSpace} (f : X ⟶ Y) :
    MappingPathReplacement.basepoint f =
      MappingPathReplacement.ofPath (underTopBasepoint X)
        (Path.refl (f.right.hom (underTopBasepoint X))) :=
  rfl

/-- The mapping-path replacement of `f` as a based space. -/
def mappingPathReplacementSpace {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (MappingPathReplacement.basepoint f)))

/-- The chosen basepoint of `mappingPathReplacementSpace f` is the constant path at the
basepoint of `Y`. -/
@[simp] theorem underTopBasepoint_mappingPathReplacementSpace {X Y : BasedSpace} (f : X ⟶ Y) :
    underTopBasepoint (mappingPathReplacementSpace f) = MappingPathReplacement.basepoint f :=
  rfl

/-- The endpoint projection preserves the chosen basepoints. -/
theorem mappingPathProjection_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (mappingPathReplacementSpace f).hom ≫
        TopCat.ofHom (MappingPathReplacement.projection f) = Y.hom := by
  -- Evaluate both terminal maps at an arbitrary point, then identify that point with `PUnit.unit`.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hw : f.right.hom (underTopBasepoint X) = underTopBasepoint Y := by
    have hbase :=
      congrArg
        (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
        (CategoryTheory.Under.w f)
    simpa [underTopBasepoint] using hbase
  calc
    ((mappingPathReplacementSpace f).hom ≫
          TopCat.ofHom (MappingPathReplacement.projection f)) x =
        MappingPathReplacement.projection f (MappingPathReplacement.basepoint f) := rfl
    _ = underTopBasepoint Y := by
      simp [MappingPathReplacement.basepoint, hw]
    _ = Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = Y.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
      rw [hx]
    _ = Y.hom x := by
      simp

/-- The standard mapping-path projection `ρ : N_f → Y` as a morphism of based spaces. -/
def mappingPathFibration {X Y : BasedSpace} (f : X ⟶ Y) :
    mappingPathReplacementSpace f ⟶ Y :=
  Under.homMk (TopCat.ofHom (MappingPathReplacement.projection f))
    (mappingPathProjection_w f)

/-- The underlying continuous map of `mappingPathFibration f` is the Chapter 7 mapping-path
projection of `f.right.hom`. -/
@[simp] theorem mappingPathFibration_hom {X Y : BasedSpace} (f : X ⟶ Y) :
    (mappingPathFibration f).right.hom = MappingPathReplacement.projection f :=
  rfl

/-- Evaluating `mappingPathFibration f` returns the endpoint of the path coordinate. -/
@[simp] theorem mappingPathFibration_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathReplacement f) :
    (mappingPathFibration f).right.hom z = MappingPathReplacement.endpoint z :=
  rfl

/-- The constant-path inclusion preserves the chosen basepoints. -/
theorem mappingPathFactor_w {X Y : BasedSpace} (f : X ⟶ Y) :
    X.hom ≫ TopCat.ofHom (MappingPathReplacement.inclusion f) =
      (mappingPathReplacementSpace f).hom :=
  by
    -- Both maps out of the terminal object pick out the same constant path in `N_f`.
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom x
      rfl
    have hbase : X.hom x = underTopBasepoint X := by
      calc
        X.hom x = X.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
          simp
        _ = X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
          rw [hx]
        _ = underTopBasepoint X := rfl
    have himage : f.right.hom (X.hom x) = f.right.hom (underTopBasepoint X) :=
      congrArg f.right.hom hbase
    apply MappingPathReplacement.ext
    · simpa [hbase]
    · ext t
      simpa [himage]

/-- The canonical map from `X` into the mapping-path replacement `N_f`. -/
def mappingPathFactorMap {X Y : BasedSpace} (f : X ⟶ Y) :
    X ⟶ mappingPathReplacementSpace f :=
  Under.homMk (TopCat.ofHom (MappingPathReplacement.inclusion f)) (mappingPathFactor_w f)

/-- The underlying continuous map of `mappingPathFactorMap f` is the Chapter 7 mapping-path
inclusion of `f.right.hom`. -/
@[simp] theorem mappingPathFactorMap_hom {X Y : BasedSpace} (f : X ⟶ Y) :
    (mappingPathFactorMap f).right.hom = MappingPathReplacement.inclusion f :=
  rfl

/-- Evaluating `mappingPathFactorMap f` sends `x` to the constant path at `f x`. -/
@[simp] theorem mappingPathFactorMap_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) :
    (mappingPathFactorMap f).right.hom x =
      MappingPathReplacement.ofPath x (Path.refl (f.right.hom x)) :=
  rfl

/-- The standard mapping-path projection has the covering homotopy property on underlying spaces.
-/
instance mappingPathFibration_hasCoveringHomotopyProperty {X Y : BasedSpace} (f : X ⟶ Y) :
    HasCoveringHomotopyProperty (mappingPathFibration f).right.hom := by
  change HasCoveringHomotopyProperty (MappingPathReplacement.projection f)
  refine ⟨?_⟩
  intro A _ _ f₀ f₁ H g₀ hg₀
  let liftValue : (I × A) × I → Y.right := fun q ↦
    if (q.2 : ℝ) ≤ 1 - (q.1.1 : ℝ) / 2 then
      (g₀ q.1.2).path
        (Set.projIcc 0 1 zero_le_one ((q.2 : ℝ) / (1 - (q.1.1 : ℝ) / 2)))
    else
      H (Set.projIcc 0 1 zero_le_one (2 * (q.2 : ℝ) + (q.1.1 : ℝ) - 2), q.1.2)
  have hdenom_ne : ∀ q : (I × A) × I, 1 - (q.1.1 : ℝ) / 2 ≠ 0 := by
    intro q hq
    have ht_le_one : (q.1.1 : ℝ) ≤ 1 := q.1.1.2.2
    nlinarith
  have hfirstParam : Continuous fun q : (I × A) × I ↦
      Set.projIcc 0 1 zero_le_one ((q.2 : ℝ) / (1 - (q.1.1 : ℝ) / 2)) := by
    exact continuous_projIcc.comp <|
      Continuous.div (by fun_prop) (by fun_prop) hdenom_ne
  have hsecondParam : Continuous fun q : (I × A) × I ↦
      Set.projIcc 0 1 zero_le_one (2 * (q.2 : ℝ) + (q.1.1 : ℝ) - 2) := by
    exact continuous_projIcc.comp <| by fun_prop
  have hstoredPath : Continuous fun q : (I × A) × I ↦ (g₀ q.1.2).path := by
    have hpath : Continuous fun z : MappingPathReplacement f ↦ z.path := by
      exact continuous_snd.comp MappingPathReplacement.continuous_subtypeVal
    exact hpath.comp (g₀.continuous.comp (continuous_snd.comp continuous_fst))
  have hLiftValue : Continuous liftValue := by
    refine continuous_if_le (by fun_prop) (by fun_prop)
      (continuous_eval.comp (hstoredPath.prodMk hfirstParam)).continuousOn
      (H.continuous.comp
        (hsecondParam.prodMk (continuous_snd.comp continuous_fst))).continuousOn ?_
    intro q hq
    have hdenom_pos : 0 < 1 - (q.1.1 : ℝ) / 2 := by
      have ht_le_one : (q.1.1 : ℝ) ≤ 1 := q.1.1.2.2
      nlinarith
    have hfirst :
        Set.projIcc 0 1 zero_le_one
            ((q.2 : ℝ) / (1 - (q.1.1 : ℝ) / 2)) = (1 : I) := by
      have hquot : (q.2 : ℝ) / (1 - (q.1.1 : ℝ) / 2) = 1 := by
        rw [hq]
        exact div_self hdenom_pos.ne'
      rw [hquot]
      simp
    have hsecond :
        Set.projIcc 0 1 zero_le_one
            (2 * (q.2 : ℝ) + (q.1.1 : ℝ) - 2) = (0 : I) := by
      have hlin : 2 * (q.2 : ℝ) + (q.1.1 : ℝ) - 2 = 0 := by
        rw [hq]
        ring
      rw [hlin]
      simp
    have hproj : (g₀ q.1.2).path 1 = f₀ q.1.2 := by
      have h := ContinuousMap.congr_fun hg₀ q.1.2
      change (g₀ q.1.2).path 1 = f₀ q.1.2 at h
      exact h
    calc
      (g₀ q.1.2).path
          (Set.projIcc 0 1 zero_le_one
            ((q.2 : ℝ) / (1 - (q.1.1 : ℝ) / 2))) =
          (g₀ q.1.2).path 1 := by rw [hfirst]
      _ = f₀ q.1.2 := hproj
      _ = H (0, q.1.2) := (H.map_zero_left q.1.2).symm
      _ = H
          (Set.projIcc 0 1 zero_le_one
            (2 * (q.2 : ℝ) + (q.1.1 : ℝ) - 2), q.1.2) := by rw [hsecond]
  have hLiftValue_zero (ta : I × A) :
      liftValue (ta, 0) = f.right.hom (g₀ ta.2).point := by
    have hbranch : ((0 : I) : ℝ) ≤ 1 - (ta.1 : ℝ) / 2 := by
      have ht_le_one : (ta.1 : ℝ) ≤ 1 := ta.1.2.2
      have hhalf : (ta.1 : ℝ) / 2 ≤ 1 / 2 := by nlinarith
      norm_num at hhalf ⊢
      nlinarith
    simp only [liftValue, if_pos hbranch]
    have hparam :
        Set.projIcc 0 1 zero_le_one
            (((0 : I) : ℝ) / (1 - (ta.1 : ℝ) / 2)) = (0 : I) := by
      simp
    rw [hparam]
    exact MappingPathReplacement.source_eq (g₀ ta.2)
  have hLiftValue_timeZero (a : A) (s : I) :
      liftValue ((0, a), s) = (g₀ a).path s := by
    have hbranch : (s : ℝ) ≤ 1 - (((0 : I) : ℝ) / 2) := by
      simpa using s.2.2
    simp only [liftValue, if_pos hbranch]
    have hparam :
        Set.projIcc 0 1 zero_le_one
            ((s : ℝ) / (1 - (((0 : I) : ℝ) / 2))) = s := by
      norm_num
    exact congrArg (g₀ a).path hparam
  have hLiftValue_one (t : I) (a : A) :
      liftValue ((t, a), 1) = H (t, a) := by
    by_cases ht : t = 0
    · subst t
      rw [hLiftValue_timeZero]
      have hproj : (g₀ a).path 1 = f₀ a := by
        have h := ContinuousMap.congr_fun hg₀ a
        change (g₀ a).path 1 = f₀ a at h
        exact h
      exact hproj.trans (H.map_zero_left a).symm
    · have ht_pos : 0 < (t : ℝ) := by
        have ht_nonneg : (0 : ℝ) ≤ (t : ℝ) := t.2.1
        have ht_ne : (t : ℝ) ≠ 0 := by simpa using ht
        exact lt_of_le_of_ne ht_nonneg ht_ne.symm
      have hbranch : ¬ (((1 : I) : ℝ) ≤ 1 - (t : ℝ) / 2) := by
        intro h
        norm_num at h
        nlinarith
      simp only [liftValue, if_neg hbranch]
      have hparam :
          Set.projIcc 0 1 zero_le_one
              (2 * (((1 : I) : ℝ)) + (t : ℝ) - 2) = t := by
        have hsum : 2 * (((1 : I) : ℝ)) + (t : ℝ) - 2 = (t : ℝ) := by
          norm_num
        rw [hsum, Set.projIcc_val]
      rw [hparam]
  let liftedPath : (I × A) → C(I, Y.right) := fun ta ↦
    ⟨fun s ↦ liftValue (ta, s),
      hLiftValue.comp (continuous_const.prodMk continuous_id)⟩
  have hLiftedPath : Continuous liftedPath := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simpa [liftedPath, Function.uncurry] using hLiftValue
  have hLiftedPoint : Continuous fun ta : I × A ↦ (g₀ ta.2).point := by
    have hpoint : Continuous fun z : MappingPathReplacement f ↦ z.point := by
      exact continuous_fst.comp MappingPathReplacement.continuous_subtypeVal
    exact hpoint.comp (g₀.continuous.comp continuous_snd)
  let lifted : C(I × A, MappingPathReplacement f) :=
    ⟨fun ta ↦
        { point := (g₀ ta.2).point
          path := liftedPath ta
          compat := hLiftValue_zero ta },
      MappingPathReplacement.continuous_mk hLiftedPoint hLiftedPath hLiftValue_zero⟩
  let atOne : C(A, I × A) :=
    ⟨fun a ↦ (1, a), continuous_const.prodMk continuous_id⟩
  let g₁ : C(A, MappingPathReplacement f) := lifted.comp atOne
  have hlifted_zero (a : A) : lifted (0, a) = g₀ a := by
    apply MappingPathReplacement.ext
    · rfl
    · ext s
      exact hLiftValue_timeZero a s
  let G : g₀.Homotopy g₁ :=
    ContinuousMap.Homotopy.mk lifted hlifted_zero (fun _ ↦ rfl)
  refine ⟨g₁, G, ?_⟩
  apply ContinuousMap.ext
  intro ta
  exact hLiftValue_one ta.1 ta.2

/-- The actual fiber of `ρ : N_f → Y` over the chosen basepoint of `Y`. -/
abbrev mappingPathFiber {X Y : BasedSpace} (f : X ⟶ Y) :
    Set (MappingPathReplacement f) :=
  fiber (mappingPathFibration f).right.hom (underTopBasepoint Y)

/-- A point of `MappingPathReplacement f` lies in `mappingPathFiber f` exactly when its endpoint
is the chosen basepoint of `Y`. -/
@[simp] theorem mem_mappingPathFiber_iff {X Y : BasedSpace} (f : X ⟶ Y)
    (z : MappingPathReplacement f) :
    z ∈ mappingPathFiber f ↔ MappingPathReplacement.endpoint z = underTopBasepoint Y :=
  Iff.rfl

/-- Helper for Construction 8.6.3: reversing a path coordinate is precomposition with
`unitInterval.symm`. -/
def reversePathCoordinate {Z : Type*} [TopologicalSpace Z] (γ : C(I, Z)) : C(I, Z) :=
  γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

/-- Helper for Construction 8.6.3: the reversed path coordinate evaluates by applying
`unitInterval.symm` to the parameter. -/
@[simp] theorem reversePathCoordinate_apply {Z : Type*} [TopologicalSpace Z] (γ : C(I, Z))
    (t : I) :
    reversePathCoordinate γ t = γ (unitInterval.symm t) :=
  rfl

/-- Helper for Construction 8.6.3: reversing a path coordinate twice recovers the original
continuous path. -/
@[simp] theorem reversePathCoordinate_involutive {Z : Type*} [TopologicalSpace Z] (γ : C(I, Z)) :
    reversePathCoordinate (reversePathCoordinate γ) = γ := by
  -- Double reversal is pointwise the identity on the unit interval.
  ext t
  simp [reversePathCoordinate]

/-- Helper for Construction 8.6.3: path reversal is continuous on the compact-open path space. -/
theorem continuous_reversePathCoordinate {Z : Type*} [TopologicalSpace Z] :
    Continuous (fun γ : C(I, Z) ↦ reversePathCoordinate γ) := by
  simpa [reversePathCoordinate] using
    (ContinuousMap.continuous_precomp
      (⟨unitInterval.symm, unitInterval.continuous_symm⟩ : C(I, I)))

/-- Helper for Construction 8.6.3: reversing the homotopy-fiber path starts at `f z.point`. -/
theorem homotopyFiberReverse_source {X Y : BasedSpace} (f : X ⟶ Y) (z : HomotopyFiber f) :
    reversePathCoordinate z.path.1 0 = f.right.hom z.point := by
  -- Reversal swaps the endpoint with the start, so time `0` becomes the original endpoint.
  simp [reversePathCoordinate, PathSpace.endpoint, HomotopyFiber.endpoint_eq z]

/-- Helper for Construction 8.6.3: reversing the homotopy-fiber path ends at the chosen basepoint
of `Y`. -/
theorem homotopyFiberReverse_target {X Y : BasedSpace} (f : X ⟶ Y) (z : HomotopyFiber f) :
    reversePathCoordinate z.path.1 1 = underTopBasepoint Y := by
  -- The original path starts at the chosen basepoint, so the reversed path ends there.
  simpa [reversePathCoordinate] using PathSpace.source_eq z.path

/-- Helper for Construction 8.6.3: reversing a point of the actual fiber produces a path in
`P[underTopBasepoint Y]`. -/
theorem mappingPathFiberReverse_source {X Y : BasedSpace} (f : X ⟶ Y) (z : mappingPathFiber f) :
    reversePathCoordinate z.1.path 0 = underTopBasepoint Y := by
  -- Membership in the actual fiber identifies the original endpoint with the basepoint of `Y`.
  calc
    reversePathCoordinate z.1.path 0 = z.1.path 1 := by
      simp [reversePathCoordinate]
    _ = underTopBasepoint Y := z.2

/-- Helper for Construction 8.6.3: reversing a point of the actual fiber ends at
`f(z.1.point)`. -/
theorem mappingPathFiberReverse_endpoint {X Y : BasedSpace} (f : X ⟶ Y) (z : mappingPathFiber f) :
    f.right.hom z.1.point = reversePathCoordinate z.1.path 1 := by
  -- The reversed path at time `1` is the original value at time `0`.
  simpa [reversePathCoordinate] using (MappingPathReplacement.source_eq (f := f) z.1).symm

/-- Helper for Construction 8.6.3: the reversed actual-fiber path, viewed as a point of
`PathSpace (underTopBasepoint Y)`, ends at `f(z.1.point)`. -/
theorem mappingPathFiberReversedPathSpace_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (z : mappingPathFiber f) :
    f.right.hom z.1.point =
      (PathSpace.mk (reversePathCoordinate z.1.path)
        (mappingPathFiberReverse_source f z)).endpoint := by
  -- The endpoint of `PathSpace.mk` is evaluation at `1`.
  simpa [PathSpace.endpoint] using mappingPathFiberReverse_endpoint f z

/-- Helper for Construction 8.6.3: the forward comparison is represented by the reversed path as
an actual `Path`. -/
def homotopyFiberReversedPath {X Y : BasedSpace} (f : X ⟶ Y) (z : HomotopyFiber f) :
    Path (f.right.hom z.point) (underTopBasepoint Y) :=
  Path.mk (reversePathCoordinate z.path.1)
    (homotopyFiberReverse_source f z) (homotopyFiberReverse_target f z)

/-- Helper for Construction 8.6.3: projecting to the point coordinate is continuous on
`HomotopyFiber f`. -/
theorem homotopyFiberPointContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : HomotopyFiber f ↦ z.point := by
  simpa [HomotopyFiber.point] using
    (continuous_fst.comp continuous_subtype_val :
      Continuous fun z : HomotopyFiber f ↦ z.1.1)

/-- Helper for Construction 8.6.3: forgetting the endpoint constraint gives a continuous path
coordinate on `HomotopyFiber f`. -/
theorem homotopyFiberPathContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : HomotopyFiber f ↦ z.path.1 := by
  have hpathSpace : Continuous fun z : HomotopyFiber f ↦ z.1.2 :=
    continuous_snd.comp continuous_subtype_val
  simpa [HomotopyFiber.path] using
    ((continuous_subtype_val :
        Continuous fun χ : PathSpace (underTopBasepoint Y) ↦ χ.1).comp hpathSpace)

/-- Helper for Construction 8.6.3: projecting to the point coordinate is continuous on the actual
fiber of `ρ`. -/
theorem mappingPathFiberPointContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : mappingPathFiber f ↦ z.1.point := by
  have hz0 : Continuous fun z : mappingPathFiber f ↦ z.1 := continuous_subtype_val
  have hz1 : Continuous fun z : MappingPathReplacement f ↦ (z.point, z.path) :=
    MappingPathReplacement.continuous_subtypeVal
  simpa using
    (continuous_fst.comp (hz1.comp hz0) :
      Continuous fun z : mappingPathFiber f ↦ z.1.point)

/-- Helper for Construction 8.6.3: the actual fiber inherits the path-coordinate projection
continuously from `MappingPathReplacement f`. -/
theorem mappingPathFiberPathContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun z : mappingPathFiber f ↦ z.1.path := by
  have hz0 : Continuous fun z : mappingPathFiber f ↦ z.1 := continuous_subtype_val
  have hz1 : Continuous fun z : MappingPathReplacement f ↦ (z.point, z.path) :=
    MappingPathReplacement.continuous_subtypeVal
  simpa using
    (continuous_snd.comp (hz1.comp hz0) :
      Continuous fun z : mappingPathFiber f ↦ z.1.path)

/-- The fiber point of `ρ` determined by `z : HomotopyFiber f` uses the reversed path from
`f(z.point)` back to the basepoint of `Y`. -/
def homotopyFiberToMappingPathFiber {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopyFiber f → mappingPathFiber f
  | z =>
      ⟨MappingPathReplacement.ofPath z.point (homotopyFiberReversedPath f z),
        homotopyFiberReverse_target f z⟩

/-- A point of the actual fiber of `ρ` determines the corresponding point of `HomotopyFiber f`
by reversing its path component. -/
def mappingPathFiberToHomotopyFiber {X Y : BasedSpace} (f : X ⟶ Y) :
    mappingPathFiber f → HomotopyFiber f
  | z =>
      HomotopyFiber.mk z.1.point
        (PathSpace.mk (reversePathCoordinate z.1.path) (mappingPathFiberReverse_source f z))
        (mappingPathFiberReversedPathSpace_endpoint f z)

/-- Helper for Construction 8.6.3: the forward comparison map reverses the path coordinate. -/
@[simp] theorem homotopyFiberToMappingPathFiber_path_eq_reverse {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    (homotopyFiberToMappingPathFiber f z).1.path = reversePathCoordinate z.path.1 :=
  rfl

/-- Helper for Construction 8.6.3: the inverse comparison map reverses the actual-fiber path
coordinate. -/
@[simp] theorem mappingPathFiberToHomotopyFiber_path_eq_reverse {X Y : BasedSpace}
    (f : X ⟶ Y) (z : mappingPathFiber f) :
    (mappingPathFiberToHomotopyFiber f z).path =
      PathSpace.mk (reversePathCoordinate z.1.path) (mappingPathFiberReverse_source f z) :=
  rfl

/-- Construction 8.6.3 (1). Replacing `f` by the mapping-path fibration
`ρ : mappingPathReplacementSpace f ⟶ Y` identifies the homotopy fiber `F_f`, realized here as
`HomotopyFiber f`, with the actual fiber `ρ⁻¹(*)` over the chosen basepoint of `Y`. -/
def homotopyFiberEquivFiberOfMappingPathFibration {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopyFiber f ≃ₜ mappingPathFiber f where
  toFun := homotopyFiberToMappingPathFiber f
  invFun := mappingPathFiberToHomotopyFiber f
  left_inv := by
    intro z
    -- Both comparison maps fix the point coordinate and reverse the path coordinate twice.
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext t
      change reversePathCoordinate (reversePathCoordinate z.path.1) t = z.path.1 t
      simp [reversePathCoordinate]
  right_inv := by
    intro z
    -- The actual-fiber comparison also reduces to double reversal on the path coordinate.
    apply Subtype.ext
    apply MappingPathReplacement.ext
    · rfl
    · ext t
      change reversePathCoordinate (reversePathCoordinate z.1.path) t = z.1.path t
      simp [reversePathCoordinate]
  continuous_toFun := by
    -- First build the reversed path continuously in `MappingPathReplacement f`, then cut down to
    -- the actual fiber using the endpoint condition.
    have hpoint := homotopyFiberPointContinuous f
    have hpath := homotopyFiberPathContinuous f
    have hreversed :
        Continuous fun z : HomotopyFiber f ↦ reversePathCoordinate z.path.1 :=
      continuous_reversePathCoordinate.comp hpath
    have hreplacement :
        Continuous fun z : HomotopyFiber f ↦
          MappingPathReplacement.ofPath z.point (homotopyFiberReversedPath f z) := by
      simpa [homotopyFiberReversedPath, MappingPathReplacement.ofPath] using
        (MappingPathReplacement.continuous_mk hpoint hreversed
          (fun z ↦ homotopyFiberReverse_source f z))
    simpa [homotopyFiberToMappingPathFiber] using
      hreplacement.subtype_mk (fun z ↦ homotopyFiberReverse_target f z)
  continuous_invFun := by
    -- The inverse is built from the same reversed path coordinate, now viewed in `PathSpace`.
    have hpoint := mappingPathFiberPointContinuous f
    have hpath := mappingPathFiberPathContinuous f
    have hreversed :
        Continuous fun z : mappingPathFiber f ↦ reversePathCoordinate z.1.path :=
      continuous_reversePathCoordinate.comp hpath
    have hpathSpace :
        Continuous fun z : mappingPathFiber f ↦
          PathSpace.mk (reversePathCoordinate z.1.path) (mappingPathFiberReverse_source f z) := by
      simpa [PathSpace.mk] using
        hreversed.subtype_mk (fun z ↦ mappingPathFiberReverse_source f z)
    have hpair :
        Continuous fun z : mappingPathFiber f ↦
          (z.1.point,
            PathSpace.mk (reversePathCoordinate z.1.path) (mappingPathFiberReverse_source f z)) :=
      hpoint.prodMk hpathSpace
    simpa [mappingPathFiberToHomotopyFiber] using
      hpair.subtype_mk (fun z ↦ mappingPathFiberReversedPathSpace_endpoint f z)

/-- The homeomorphism of Construction 8.6.3 (1) acts by the explicit map from the homotopy fiber
to the actual fiber of the mapping-path fibration. -/
theorem homotopyFiberEquivFiberOfMappingPathFibration_apply {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber f) :
    homotopyFiberEquivFiberOfMappingPathFibration f z = homotopyFiberToMappingPathFiber f z :=
  rfl

/-- Construction 8.6.3 (2). The original based map `f` factors through the mapping-path
replacement `mappingPathReplacementSpace f` via the canonical inclusion
`mappingPathFactorMap f : X ⟶ mappingPathReplacementSpace f` and the fibration
`mappingPathFibration f : mappingPathReplacementSpace f ⟶ Y`. -/
theorem mappingPathFactorization {X Y : BasedSpace} (f : X ⟶ Y) :
    mappingPathFactorMap f ≫ mappingPathFibration f = f := by
  -- Endpoint evaluation of the constant path at `f x` is `f x`.
  ext x
  rfl
