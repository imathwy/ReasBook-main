import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5

open CategoryTheory
open scoped Topology.Homotopy PathSpace unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `lean_leansearch` did not surface a dedicated owner for the comparison
-- `Ω Y ⟶ F_(π(f))`, so this file follows the local Chapter 8 owners
-- `homotopyFiberProjection`, `homotopyFiberLoopInclusion`, `signedLoopBasedMap`, and
-- `HomotopicUnder`.

/-- The defining equation of the comparison point in `F_(π(f))` attached to a loop in `Y`. -/
theorem homotopyFiberProjectionComparison_condition {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    (homotopyFiberProjection f).right.hom
        (HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
          (homotopyFiberLoopInclusion_condition f χ)) =
      (PathSpace.basepoint (underTopBasepoint X)).endpoint := by
  -- Projecting to `X` forgets the loop coordinate and returns the distinguished point.
  simp [homotopyFiberProjection_hom_apply]

/-- Helper for Lemma 8.6.10: pairing the loop-inclusion point with the constant path in `X` is
continuous into the ambient product defining `F_(π(f))`. -/
theorem homotopyFiberProjectionComparisonPairContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun χ : Ω Y.right (underTopBasepoint Y) ↦
      (homotopyFiberLoopInclusionFun f χ, PathSpace.basepoint (underTopBasepoint X)) := by
  -- Only the loop-inclusion coordinate varies with `χ`.
  exact (homotopyFiberLoopInclusionContinuous f).prodMk continuous_const

/-- The comparison function `ΩY → F_(π(f))` sending a loop `χ` to the point of `F_(π(f))`
represented by `ι(f)(χ)` together with the constant path at `underTopBasepoint X`. -/
def homotopyFiberProjectionComparisonFun {X Y : BasedSpace} (f : X ⟶ Y) :
    Ω Y.right (underTopBasepoint Y) → HomotopyFiber (homotopyFiberProjection f) :=
  fun χ ↦
    HomotopyFiber.mk
      (HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
        (homotopyFiberLoopInclusion_condition f χ))
      (PathSpace.basepoint (underTopBasepoint X))
      (homotopyFiberProjectionComparison_condition f χ)

/-- The comparison function sends `χ` to the point of `F_(π(f))` represented by `ι(f)(χ)` and
the constant path at `underTopBasepoint X`. -/
@[simp] theorem homotopyFiberProjectionComparisonFun_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    homotopyFiberProjectionComparisonFun f χ =
      HomotopyFiber.mk
        (HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
          (homotopyFiberLoopInclusion_condition f χ))
        (PathSpace.basepoint (underTopBasepoint X))
        (homotopyFiberProjectionComparison_condition f χ) :=
  rfl

/-- The comparison function `ΩY → F_(π(f))` is continuous. -/
theorem homotopyFiberProjectionComparisonContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (homotopyFiberProjectionComparisonFun f) := by
  -- Lift the continuous ambient product map into the iterated homotopy-fiber subtype.
  simpa [homotopyFiberProjectionComparisonFun] using
    (homotopyFiberProjectionComparisonPairContinuous f).subtype_mk
      (fun χ ↦ homotopyFiberProjectionComparison_condition f χ)

/-- Helper for Lemma 8.6.10: the comparison function sends the constant loop in `Y` to the chosen
basepoint of `F_(π(f))`. -/
theorem homotopyFiberProjectionComparisonFun_basepoint {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiberProjectionComparisonFun f (Path.refl (underTopBasepoint Y)) =
      underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
  -- After normalizing both chosen basepoints, the two iterated-fiber points are definitionally
  -- the same constant-path representative.
  rfl

/-- The comparison map `ΩY → F_(π(f))` as a continuous map. -/
def homotopyFiberProjectionComparisonContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(Ω Y.right (underTopBasepoint Y), HomotopyFiber (homotopyFiberProjection f)) :=
  { toFun := homotopyFiberProjectionComparisonFun f
    continuous_toFun := homotopyFiberProjectionComparisonContinuous f }

/-- The comparison map `ΩY → F_(π(f))` preserves the chosen basepoints. -/
theorem homotopyFiberProjectionComparison_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (Ωᵇ Y).hom ≫ TopCat.ofHom (homotopyFiberProjectionComparisonContinuousMap f) =
      (homotopyFiber (homotopyFiberProjection f)).hom := by
  -- Both terminal maps evaluate to the canonical point above the constant loop.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((Ωᵇ Y).hom ≫ TopCat.ofHom (homotopyFiberProjectionComparisonContinuousMap f)) x
        = homotopyFiberProjectionComparisonFun f (Path.refl (underTopBasepoint Y)) := rfl
    _ = (homotopyFiber (homotopyFiberProjection f)).hom
          (TopCat.terminalIsoPUnit.inv PUnit.unit) :=
          homotopyFiberProjectionComparisonFun_basepoint f
    _ = (homotopyFiber (homotopyFiberProjection f)).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
          rw [hx]
    _ = (homotopyFiber (homotopyFiberProjection f)).hom x := by
          simp

/-- The comparison morphism `Ωᵇ Y ⟶ F_(π(f))` used in Lemma 8.6.10. -/
def homotopyFiberProjectionComparison {X Y : BasedSpace} (f : X ⟶ Y) :
    Ωᵇ Y ⟶ homotopyFiber (homotopyFiberProjection f) :=
  Under.homMk
    (TopCat.ofHom (homotopyFiberProjectionComparisonContinuousMap f))
    (homotopyFiberProjectionComparison_w f)

/-- The underlying map of `homotopyFiberProjectionComparison f` sends `χ` to the point of
`F_(π(f))` represented by `ι(f)(χ)` and the constant path at `underTopBasepoint X`. -/
@[simp] theorem homotopyFiberProjectionComparison_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    (homotopyFiberProjectionComparison f).right.hom χ =
      HomotopyFiber.mk
        (HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
          (homotopyFiberLoopInclusion_condition f χ))
        (PathSpace.basepoint (underTopBasepoint X))
        (homotopyFiberProjectionComparison_condition f χ) :=
  rfl

/-- Right-triangle half of Lemma 8.6.10. For the map `π(f) : F_f ⟶ X` in the fiber sequence, the
comparison diagram
with `F_(π(f))` has the right triangle commuting: the comparison map `ΩY ⟶ F_(π(f))` followed by
`π(π(f)) : F_(π(f)) ⟶ F_f` is exactly `ι(f) : ΩY ⟶ F_f`. -/
theorem homotopyFiberProjectionComparison_comp_homotopyFiberProjection {X Y : BasedSpace}
    (f : X ⟶ Y) :
    homotopyFiberProjectionComparison f ≫ homotopyFiberProjection (homotopyFiberProjection f) =
      homotopyFiberLoopInclusion f := by
  -- Projecting out of `F_(π(f))` drops the outer constant path and recovers `ι(f)`.
  ext χ
  rfl

/-- Helper for Lemma 8.6.10: evaluating the induced loop map applies `f` pointwise. -/
@[simp] theorem loopBasedMapPath_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (t : I) :
    loopBasedMapPath f χ t = f.right.hom (χ t) := by
  simp [loopBasedMapPath]

/-- Helper for Lemma 8.6.10: path reversal evaluates at the reversed parameter. -/
@[simp] theorem loopBasedSpaceNegPath_apply {X : BasedSpace}
    (χ : Ω X.right (underTopBasepoint X)) (t : I) :
    loopBasedSpaceNegPath X χ t = χ (unitInterval.symm t) := by
  simp [loopBasedSpaceNegPath]

/-- Helper for Lemma 8.6.10: the signed loop map is the reversed image loop. -/
@[simp] theorem signedLoopBasedMap_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    (signedLoopBasedMap f).right.hom χ = loopBasedSpaceNegPath Y (loopBasedMapPath f χ) :=
  rfl

/-- Helper for Lemma 8.6.10: the reversed parameter `t ↦ 1 - t` on the unit interval. -/
def reverseUnitIntervalParam (t : I) : I :=
  ⟨1 - (t : ℝ), by
    constructor
    · linarith [t.2.2]
    · linarith [t.2.1]⟩

/-- Helper for Lemma 8.6.10: reversing the parameter sends `0` to `1`. -/
@[simp] theorem reverseUnitIntervalParam_zero : reverseUnitIntervalParam (0 : I) = (1 : I) := by
  apply Subtype.ext
  simp [reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: reversing the parameter sends `1` to `0`. -/
@[simp] theorem reverseUnitIntervalParam_one : reverseUnitIntervalParam (1 : I) = (0 : I) := by
  apply Subtype.ext
  simp [reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: parameter reversal on `I` is involutive. -/
@[simp] theorem reverseUnitIntervalParam_involutive (t : I) :
    reverseUnitIntervalParam (reverseUnitIntervalParam t) = t := by
  apply Subtype.ext
  simp [reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: `unitInterval.symm` composed with the explicit reversed parameter is
the identity. -/
@[simp] theorem unitIntervalSymm_reverseUnitIntervalParam (t : I) :
    unitInterval.symm (reverseUnitIntervalParam t) = t := by
  apply Subtype.ext
  simp [reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: parameter reversal varies continuously on `I`. -/
theorem reverseUnitIntervalParam_continuous :
    Continuous fun t : I ↦ reverseUnitIntervalParam t := by
  simpa [reverseUnitIntervalParam] using
    (unitInterval.continuous_symm : Continuous unitInterval.symm)

/-- Helper for Lemma 8.6.10: multiplying by `1 - t` stays inside the unit interval. -/
theorem truncatePathParameter_mem (t s : I) :
    ((reverseUnitIntervalParam t : I) : ℝ) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (reverseUnitIntervalParam t).2.1 s.2.1
  · nlinarith [(reverseUnitIntervalParam t).2.1, (reverseUnitIntervalParam t).2.2,
      s.2.1, s.2.2]

/-- Helper for Lemma 8.6.10: the truncation parameter depends continuously on the path variable.
-/
theorem truncatePathParameter_continuous (t : I) :
    Continuous fun s : I ↦
      (⟨((reverseUnitIntervalParam t : I) : ℝ) * (s : ℝ), truncatePathParameter_mem t s⟩ : I) := by
  -- The explicit affine formula is continuous, and the subtype condition is handled pointwise.
  simpa using
    (by
      fun_prop :
        Continuous fun s : I ↦
          (⟨((reverseUnitIntervalParam t : I) : ℝ) * (s : ℝ),
            truncatePathParameter_mem t s⟩ : I))

/-- Helper for Lemma 8.6.10: the reparameterization `s ↦ (1 - t)s` of the unit interval. -/
def truncatePathParameter (t : I) : C(I, I) :=
  ⟨fun s ↦ ⟨((reverseUnitIntervalParam t : I) : ℝ) * (s : ℝ), truncatePathParameter_mem t s⟩,
    truncatePathParameter_continuous t⟩

/-- Helper for Lemma 8.6.10: truncation sends `0` to `0`. -/
@[simp] theorem truncatePathParameter_zero (t : I) :
    truncatePathParameter t 0 = 0 := by
  apply Subtype.ext
  simp [truncatePathParameter]

/-- Helper for Lemma 8.6.10: truncation sends `1` to `1 - t`. -/
@[simp] theorem truncatePathParameter_one (t : I) :
    truncatePathParameter t 1 = reverseUnitIntervalParam t := by
  apply Subtype.ext
  simp [truncatePathParameter]

/-- Helper for Lemma 8.6.10: the two-variable truncation parameter is continuous. -/
theorem truncatePathParameterPair_continuous :
    Continuous fun q : I × I ↦
      (⟨((reverseUnitIntervalParam q.1 : I) : ℝ) * (q.2 : ℝ),
        truncatePathParameter_mem q.1 q.2⟩ : I) := by
  simpa [truncatePathParameter] using
    (by
      fun_prop :
        Continuous fun q : I × I ↦
          (⟨((reverseUnitIntervalParam q.1 : I) : ℝ) * (q.2 : ℝ),
            truncatePathParameter_mem q.1 q.2⟩ : I))

/-- Helper for Lemma 8.6.10: truncating a based path still starts at the chosen basepoint. -/
theorem truncatedBasedPath_source {B : BasedSpace} (χ : P[underTopBasepoint B]) (t : I) :
    (χ.1.comp (truncatePathParameter t)) 0 = underTopBasepoint B := by
  -- At `0`, the truncated path still evaluates the original path at `0`.
  simp [truncatePathParameter_zero]

/-- Helper for Lemma 8.6.10: the initial segment of a based path of length `1 - t`. -/
def truncatedBasedPath {B : BasedSpace} (χ : P[underTopBasepoint B]) (t : I) :
    P[underTopBasepoint B] :=
  PathSpace.mk (χ.1.comp (truncatePathParameter t)) (truncatedBasedPath_source χ t)

/-- Helper for Lemma 8.6.10: truncation ends at the value of the original path at `1 - t`. -/
@[simp] theorem truncatedBasedPath_endpoint {B : BasedSpace} (χ : P[underTopBasepoint B]) (t : I) :
    (truncatedBasedPath χ t).endpoint = χ (reverseUnitIntervalParam t) := by
  -- Evaluating at time `1` reads off the endpoint of the truncated segment.
  simp [truncatedBasedPath, truncatePathParameter_one]

/-- Helper for Lemma 8.6.10: truncating at `t = 0` leaves the path unchanged. -/
@[simp] theorem truncatedBasedPath_zero {B : BasedSpace} (χ : P[underTopBasepoint B]) :
    truncatedBasedPath χ 0 = χ := by
  apply Subtype.ext
  ext s
  simp [truncatedBasedPath, truncatePathParameter, reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: truncating at `t = 1` collapses to the constant basepoint path. -/
@[simp] theorem truncatedBasedPath_one {B : BasedSpace} (χ : P[underTopBasepoint B]) :
    truncatedBasedPath χ 1 = PathSpace.basepoint (underTopBasepoint B) := by
  apply Subtype.ext
  ext s
  change χ.1 (truncatePathParameter 1 s) = underTopBasepoint B
  simp [truncatePathParameter, reverseUnitIntervalParam]

/-- Helper for Lemma 8.6.10: truncating the constant basepoint path keeps it constant. -/
@[simp] theorem truncatedBasedPath_basepoint {B : BasedSpace} (t : I) :
    truncatedBasedPath (PathSpace.basepoint (underTopBasepoint B)) t =
      PathSpace.basepoint (underTopBasepoint B) := by
  apply Subtype.ext
  ext s
  rfl

/-- Helper for Lemma 8.6.10: truncation is continuous in the path and truncation parameters. -/
theorem truncatedBasedPath_continuous {B : BasedSpace} :
    Continuous fun q : P[underTopBasepoint B] × I ↦ truncatedBasedPath q.1 q.2 := by
  let family : P[underTopBasepoint B] × I → C(I, B.right) :=
    fun q ↦ q.1.1.comp (truncatePathParameter q.2)
  have hfamily : Continuous family := by
    have hpath :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ r.1.1.1 := by
      exact continuous_subtype_val.comp continuous_fst.fst
    have hparam :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ truncatePathParameter r.1.2 r.2 := by
      have hpair : Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ (r.1.2, r.2) := by
        fun_prop
      simpa [truncatePathParameter, Function.comp] using
        truncatePathParameterPair_continuous.comp hpair
    have huncurry :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ family r.1 r.2 := by
      -- Evaluate the reparameterized path family pointwise and use compact-open currying.
      simpa [family, Function.comp] using
        (continuous_eval.comp (hpath.prodMk hparam) :
          Continuous fun r : (P[underTopBasepoint B] × I) × I ↦
            r.1.1.1 (truncatePathParameter r.1.2 r.2))
    exact ContinuousMap.continuous_of_continuous_uncurry family huncurry
  -- Package the continuous reparameterized path back into the path-space subtype.
  simpa [truncatedBasedPath, PathSpace.mk] using
    hfamily.subtype_mk (fun q ↦ truncatedBasedPath_source q.1 q.2)

/-- Helper for Lemma 8.6.10: a based relative homotopy determines a homotopy in
`Under (⊤_ TopCat)`. -/
theorem homotopicUnderOfBasedHRel {X Y : BasedSpace} {f₀ f₁ : X ⟶ Y}
    (H : f₀.right.hom HRel[X] f₁.right.hom) :
    HomotopicUnder f₀ f₁ := by
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t
  -- Singleton-relative constancy at the basepoint is exactly the under-category condition.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hstage :
      H (t, underTopBasepoint X) = underTopBasepoint Y := by
    calc
      H (t, underTopBasepoint X) = f₀.right.hom (underTopBasepoint X) := by
        exact H.eq_fst t (by simp [basedBasepointSet])
      _ = underTopBasepoint Y := by
        have hw :=
          congrArg
            (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
            (Under.w f₀)
        simpa [underTopBasepoint] using hw
  calc
    (H.toHomotopy.curry t).comp X.hom.hom x = H (t, X.hom x) := rfl
    _ = H (t, underTopBasepoint X) := by
      rw [show X.hom x = underTopBasepoint X by
        change X.hom x = X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)
        rw [← hx]
        simp]
    _ = underTopBasepoint Y := hstage
    _ = Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = Y.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
      rw [hx]
    _ = Y.hom x := by
      simp

/-- Helper for Lemma 8.6.10: the initial `X`-segment of the loop cut at parameter `u`. -/
def iteratedFiberComparisonFrontPath {X Y : BasedSpace} (_f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    P[underTopBasepoint X] :=
  truncatedBasedPath (PathSpace.ofPath χ) (reverseUnitIntervalParam u)

/-- Helper for Lemma 8.6.10: the reversed image-loop tail from the cut parameter `u`. -/
def iteratedFiberComparisonTailPath {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    P[underTopBasepoint Y] :=
  truncatedBasedPath (PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f χ))) u

/-- Helper for Lemma 8.6.10: evaluating the reversed image loop at the reversed parameter
recovers the pointwise image `f.right.hom (χ u)`. -/
theorem reversedImageLoop_apply_reverse {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f χ)) (reverseUnitIntervalParam u) =
      f.right.hom (χ u) := by
  -- Evaluate the reversed loop at the reversed parameter and cancel the two reversals.
  change loopBasedSpaceNegPath Y (loopBasedMapPath f χ) (reverseUnitIntervalParam u) =
    f.right.hom (χ u)
  simp [loopBasedSpaceNegPath_apply, loopBasedMapPath_apply]

/-- Helper for Lemma 8.6.10: the reversed image of the constant loop is the constant basepoint
path in `Y`. -/
theorem reversedImageLoop_basepointPath {X Y : BasedSpace} (f : X ⟶ Y) :
    PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f
      (Path.refl (underTopBasepoint X)))) =
      PathSpace.basepoint (underTopBasepoint Y) := by
  -- Both sides are the constant path at the basepoint of `Y`.
  apply Subtype.ext
  ext s
  change loopBasedSpaceNegPath Y (loopBasedMapPath f (Path.refl (underTopBasepoint X))) s =
    underTopBasepoint Y
  simp [loopBasedSpaceNegPath_apply, loopBasedMapPath_apply]

/-- Helper for Lemma 8.6.10: the endpoint of the tail path is the image under `f` of the
endpoint of the front path. -/
theorem iteratedFiberComparisonTailPath_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    f.right.hom (iteratedFiberComparisonFrontPath f χ u).endpoint =
      (iteratedFiberComparisonTailPath f χ u).endpoint := by
  -- Rewrite both endpoints to the same canonical pointwise image `f.right.hom (χ u)`.
  calc
    f.right.hom (iteratedFiberComparisonFrontPath f χ u).endpoint
        = f.right.hom ((PathSpace.ofPath χ) u) := by
          simp [iteratedFiberComparisonFrontPath]
    _ = f.right.hom (χ u) := rfl
    _ = PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f χ))
          (reverseUnitIntervalParam u) := by
          symm
          exact reversedImageLoop_apply_reverse f χ u
    _ = (iteratedFiberComparisonTailPath f χ u).endpoint := by
          simp [iteratedFiberComparisonTailPath]

/-- Helper for Lemma 8.6.10: the split-loop point satisfies the outer homotopy-fiber equation. -/
theorem iteratedFiberComparisonSplitPoint_condition {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    (homotopyFiberProjection f).right.hom
        (HomotopyFiber.mk
          (iteratedFiberComparisonFrontPath f χ u).endpoint
          (iteratedFiberComparisonTailPath f χ u)
          (iteratedFiberComparisonTailPath_endpoint f χ u)) =
      (iteratedFiberComparisonFrontPath f χ u).endpoint := by
  -- The outer projection simply reads off the inner point coordinate.
  simp [homotopyFiberProjection_hom_apply]

/-- Helper for Lemma 8.6.10: the split-loop point in `F_(π(f))` at parameters `(χ,u)`. -/
def iteratedFiberComparisonSplitPoint {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    HomotopyFiber (homotopyFiberProjection f) :=
  HomotopyFiber.mk
    (HomotopyFiber.mk
      (iteratedFiberComparisonFrontPath f χ u).endpoint
      (iteratedFiberComparisonTailPath f χ u)
      (iteratedFiberComparisonTailPath_endpoint f χ u))
    (iteratedFiberComparisonFrontPath f χ u)
    (iteratedFiberComparisonSplitPoint_condition f χ u)

/-- Helper for Lemma 8.6.10: at `u = 1`, the split point becomes the loop inclusion for
`π(f)`. -/
theorem iteratedFiberComparisonSplitPoint_one {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    iteratedFiberComparisonSplitPoint f χ 1 =
      (homotopyFiberLoopInclusion (homotopyFiberProjection f)).right.hom χ := by
  -- At `u = 1`, the inner point is the canonical basepoint of `F_f`, and the outer path is `χ`.
  have hFront :
      iteratedFiberComparisonFrontPath f χ 1 = PathSpace.ofPath χ := by
    -- Truncating by the full remaining interval leaves the original loop unchanged.
    simp [iteratedFiberComparisonFrontPath]
  have hTail :
      iteratedFiberComparisonTailPath f χ 1 = PathSpace.basepoint (underTopBasepoint Y) := by
    -- The reversed image-loop tail collapses to the constant basepoint path at `u = 1`.
    simp [iteratedFiberComparisonTailPath]
  calc
    iteratedFiberComparisonSplitPoint f χ 1
        =
          HomotopyFiber.mk
            (HomotopyFiber.basepoint f)
            (PathSpace.ofPath χ)
            (homotopyFiberLoopInclusion_condition (homotopyFiberProjection f) χ) := by
              -- Rewriting the front and tail paths puts the split point in the canonical form.
              simp [iteratedFiberComparisonSplitPoint, HomotopyFiber.basepoint, hFront, hTail]
    _ = (homotopyFiberLoopInclusion (homotopyFiberProjection f)).right.hom χ := by
          simpa [underTopBasepoint_homotopyFiber] using
            (homotopyFiberLoopInclusion_hom_apply (f := homotopyFiberProjection f) χ).symm

/-- Helper for Lemma 8.6.10: splitting the constant loop always gives the basepoint of
`F_(π(f))`. -/
theorem iteratedFiberComparisonSplitPoint_basepoint {X Y : BasedSpace} (f : X ⟶ Y)
    (u : I) :
    iteratedFiberComparisonSplitPoint f (Path.refl (underTopBasepoint X)) u =
      underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
  -- Both the front and tail truncations stay constant on the distinguished loop.
  have hFront :
      iteratedFiberComparisonFrontPath f (Path.refl (underTopBasepoint X)) u =
        PathSpace.basepoint (underTopBasepoint X) := by
    -- Truncating the constant loop keeps the constant basepoint path.
    change
      truncatedBasedPath (PathSpace.basepoint (underTopBasepoint X)) (reverseUnitIntervalParam u) =
        PathSpace.basepoint (underTopBasepoint X)
    simp
  have hTail :
      iteratedFiberComparisonTailPath f (Path.refl (underTopBasepoint X)) u =
        PathSpace.basepoint (underTopBasepoint Y) := by
    -- The reversed image of the constant loop is again the constant basepoint path.
    simp [iteratedFiberComparisonTailPath, reversedImageLoop_basepointPath]
  calc
    iteratedFiberComparisonSplitPoint f (Path.refl (underTopBasepoint X)) u
        =
          HomotopyFiber.mk
            (HomotopyFiber.basepoint f)
            (PathSpace.basepoint (underTopBasepoint X))
            (HomotopyFiber.basepoint_condition (homotopyFiberProjection f)) := by
              -- Rewriting the front and tail paths reduces the split point to the iterated-fiber
              -- basepoint representative.
              simp [iteratedFiberComparisonSplitPoint, HomotopyFiber.basepoint, hFront, hTail]
    _ = underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
          exact (underTopBasepoint_homotopyFiber (f := homotopyFiberProjection f)).symm

/-- Helper for Lemma 8.6.10: the split-loop point depends continuously on `(χ,u)`. -/
theorem iteratedFiberComparisonSplitPointContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun q : Ω X.right (underTopBasepoint X) × I ↦
      iteratedFiberComparisonSplitPoint f q.1 q.2 := by
  -- Build the front and tail path coordinates continuously using the truncation construction.
  have hFrontPath :
      Continuous fun q : Ω X.right (underTopBasepoint X) × I ↦
        iteratedFiberComparisonFrontPath f q.1 q.2 := by
    have hloop :
        Continuous fun χ : Ω X.right (underTopBasepoint X) ↦ PathSpace.ofPath χ :=
      loopToPathSpaceContinuous (Y := X)
    simpa [iteratedFiberComparisonFrontPath] using
      (truncatedBasedPath_continuous (B := X)).comp
        ((hloop.comp continuous_fst).prodMk
          (reverseUnitIntervalParam_continuous.comp continuous_snd))
  have hTailPath :
      Continuous fun q : Ω X.right (underTopBasepoint X) × I ↦
        iteratedFiberComparisonTailPath f q.1 q.2 := by
    have hloop :
        Continuous fun χ : Ω X.right (underTopBasepoint X) ↦
          PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f χ)) := by
      exact (loopToPathSpaceContinuous (Y := Y)).comp
        ((loopBasedSpaceNegContinuous Y).comp (loopBasedMapContinuous f))
    simpa [iteratedFiberComparisonTailPath] using
      (truncatedBasedPath_continuous (B := Y)).comp
        ((hloop.comp continuous_fst).prodMk continuous_snd)
  have hEndpoint :
      Continuous fun q : Ω X.right (underTopBasepoint X) × I ↦
        (iteratedFiberComparisonFrontPath f q.1 q.2).endpoint := by
    exact (pathSpaceEndpointContinuous X).comp hFrontPath
  have hInner :
      Continuous fun q : Ω X.right (underTopBasepoint X) × I ↦
        HomotopyFiber.mk
          (iteratedFiberComparisonFrontPath f q.1 q.2).endpoint
          (iteratedFiberComparisonTailPath f q.1 q.2)
          (iteratedFiberComparisonTailPath_endpoint f q.1 q.2) := by
    -- Package the front endpoint and tail path into the inner homotopy fiber.
    simpa using
      (hEndpoint.prodMk hTailPath).subtype_mk
        (fun q ↦ iteratedFiberComparisonTailPath_endpoint f q.1 q.2)
  -- Then package the front path as the outer path coordinate in the iterated fiber.
  simpa [iteratedFiberComparisonSplitPoint] using
    (hInner.prodMk hFrontPath).subtype_mk
      (fun q ↦ iteratedFiberComparisonSplitPoint_condition f q.1 q.2)

/-- Helper for Lemma 8.6.10: the split-loop homotopy as a curried path family in `F_(π(f))`. -/
def iteratedFiberComparisonSplitFamily {X Y : BasedSpace} (f : X ⟶ Y) :
    C(Ω X.right (underTopBasepoint X), C(I, HomotopyFiber (homotopyFiberProjection f))) :=
  ContinuousMap.curry
    ⟨fun q : Ω X.right (underTopBasepoint X) × I ↦
        iteratedFiberComparisonSplitPoint f q.1 q.2,
      iteratedFiberComparisonSplitPointContinuous f⟩

/-- Helper for Lemma 8.6.10: evaluating the split family returns the explicit split point. -/
@[simp] theorem iteratedFiberComparisonSplitFamily_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (u : I) :
    iteratedFiberComparisonSplitFamily f χ u = iteratedFiberComparisonSplitPoint f χ u :=
  rfl

/-- Helper for Lemma 8.6.10: at `u = 0`, the split family gives the signed-loop comparison map.
-/
theorem iteratedFiberComparisonSplitFamily_zero {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    iteratedFiberComparisonSplitFamily f χ 0 =
      (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom χ := by
  -- The front path collapses while the tail path is the reversed image loop.
  calc
    iteratedFiberComparisonSplitFamily f χ 0 = iteratedFiberComparisonSplitPoint f χ 0 := rfl
    _ =
        HomotopyFiber.mk
          (HomotopyFiber.mk
            (underTopBasepoint X)
            (PathSpace.ofPath (loopBasedSpaceNegPath Y (loopBasedMapPath f χ)))
            (homotopyFiberLoopInclusion_condition f ((signedLoopBasedMap f).right.hom χ)))
          (PathSpace.basepoint (underTopBasepoint X))
          (homotopyFiberProjectionComparison_condition f ((signedLoopBasedMap f).right.hom χ)) := by
            simp [iteratedFiberComparisonSplitPoint, iteratedFiberComparisonFrontPath,
              iteratedFiberComparisonTailPath]
    _ = (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom χ := by
      rfl

/-- Helper for Lemma 8.6.10: at `u = 1`, the split family gives `ι(π(f))`. -/
theorem iteratedFiberComparisonSplitFamily_one {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    iteratedFiberComparisonSplitFamily f χ 1 =
      (homotopyFiberLoopInclusion (homotopyFiberProjection f)).right.hom χ := by
  -- Evaluate the split family at `u = 1` and use the split-point normal form.
  simpa using iteratedFiberComparisonSplitPoint_one f χ

/-- Helper for Lemma 8.6.10: the split family is constant on the distinguished loop of `Ωᵇ X`. -/
theorem iteratedFiberComparisonSplitFamily_rel {X Y : BasedSpace} (f : X ⟶ Y) :
    iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) =
      ContinuousMap.const I (underTopBasepoint (homotopyFiber (homotopyFiberProjection f))) := by
  -- Evaluate the family pointwise and normalize the split point of the constant loop.
  ext u
  simpa using iteratedFiberComparisonSplitPoint_basepoint f u

/-- Helper for Lemma 8.6.10: the signed-loop comparison sends the distinguished loop of `Ωᵇ X`
to the chosen basepoint of `F_(π(f))`. -/
theorem signedLoopComparison_basepoint {X Y : BasedSpace} (f : X ⟶ Y) :
    (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
        (Path.refl (underTopBasepoint X)) =
      underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
  have hrel0 :
      iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) 0 =
        underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
    simpa using congrArg (fun γ : C(I, HomotopyFiber (homotopyFiberProjection f)) ↦ γ 0)
      (iteratedFiberComparisonSplitFamily_rel f)
  exact
    (iteratedFiberComparisonSplitFamily_zero f (Path.refl (underTopBasepoint X))).symm.trans
      hrel0

/-- Lemma 8.6.10 (2). For the map `ι(f) : ΩY ⟶ F_f` in the fiber sequence, the comparison diagram
with `F_(π(f))` has the left triangle commuting up to homotopy: the composite
`ΩX ⟶ ΩY ⟶ F_(π(f))` obtained from `signedLoopBasedMap f` and the comparison map is homotopic
under the basepoint to `ι(π(f)) : ΩX ⟶ F_(π(f))`. -/
theorem homotopyFiberProjectionComparison_comp_signedLoopBasedMap_homotopic
    {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopicUnder
      (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f)
      (homotopyFiberLoopInclusion (homotopyFiberProjection f)) := by
  -- Route correction: the split-loop family is the right global object, but the remaining work is
  -- the normalization of its reversed-image-loop representatives at the endpoint and basepoint.
  -- Package the split family into a singleton-relative homotopy and pass to
  -- `homotopicUnderOfBasedHRel`.
  let H :
      (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom HRel[Ωᵇ X]
        (homotopyFiberLoopInclusion (homotopyFiberProjection f)).right.hom := by
    refine
      { toHomotopy := ?_
        prop' := ?_ }
    · -- Uncurry the split family to obtain the underlying homotopy in `F_(π(f))`.
      refine
        { toFun := fun p ↦ iteratedFiberComparisonSplitFamily f p.2 p.1
          continuous_toFun := ?_
          map_zero_left := ?_
          map_one_left := ?_ }
      · exact
          (ContinuousMap.continuous_uncurry_of_continuous
            (iteratedFiberComparisonSplitFamily f)).comp
            (Homeomorph.prodComm I (Ω X.right (underTopBasepoint X))).continuous_toFun
      · intro χ
        simpa using iteratedFiberComparisonSplitFamily_zero f χ
      · intro χ
        simpa using iteratedFiberComparisonSplitFamily_one f χ
    · intro t χ hχ
      -- On the distinguished loop, the split family is literally constant at the chosen basepoint.
      have hχ' : χ = Path.refl (underTopBasepoint X) := by
        simpa [basedBasepointSet] using hχ
      subst hχ'
      have hconst :
          iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) =
            ContinuousMap.const I
              ((signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
                (Path.refl (underTopBasepoint X))) := by
        ext s
        calc
          iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) s
              = underTopBasepoint (homotopyFiber (homotopyFiberProjection f)) := by
                  simpa using congrArg
                    (fun γ : C(I, HomotopyFiber (homotopyFiberProjection f)) ↦ γ s)
                    (iteratedFiberComparisonSplitFamily_rel f)
          _ = (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
                (Path.refl (underTopBasepoint X)) := by
                  symm
                  exact signedLoopComparison_basepoint f
          _ = (ContinuousMap.const I
                ((signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
                  (Path.refl (underTopBasepoint X)))) s := rfl
      have hconst_t :
          iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) t =
            (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
              (Path.refl (underTopBasepoint X)) := by
        calc
          iteratedFiberComparisonSplitFamily f (Path.refl (underTopBasepoint X)) t
              = (ContinuousMap.const I
                  ((signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
                    (Path.refl (underTopBasepoint X)))) t := by
                      exact congrArg
                        (fun γ : C(I, HomotopyFiber (homotopyFiberProjection f)) ↦ γ t)
                        hconst
          _ = (signedLoopBasedMap f ≫ homotopyFiberProjectionComparison f).right.hom
                (Path.refl (underTopBasepoint X)) := rfl
      simpa using hconst_t
  exact homotopicUnderOfBasedHRel H
