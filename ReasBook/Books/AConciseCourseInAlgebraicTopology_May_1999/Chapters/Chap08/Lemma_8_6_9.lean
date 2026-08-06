import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1

open CategoryTheory
open scoped PathSpace unitInterval

noncomputable section

-- Semantic recall: a `lean_leansearch` query for a dedicated pointed homotopy-equivalence owner
-- returned HTTP 429, so this item follows the local `Under (⊤_ TopCat)` precedent from
-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2` and encodes based homotopy equivalences by
-- `IsCofiberHomotopyEquivalence`.

universe u

variable {E B : Under (⊤_ TopCat.{u})}

/-- The actual fiber of a based map, viewed as the subset `p⁻¹' {underTopBasepoint B}` of the
total space. -/
abbrev actualFiberSet (p : E ⟶ B) : Set E.right :=
  fiber p.right.hom (underTopBasepoint B)

/-- The distinguished point of the actual fiber over `underTopBasepoint B` is the basepoint of
`E`, viewed as a point of that fiber. -/
def actualFiberBasepoint (p : E ⟶ B) : actualFiberSet p :=
  ⟨underTopBasepoint E,
    (mem_fiber_iff p.right.hom (underTopBasepoint B) (underTopBasepoint E)).2
      (fundamentalGroupFunctorMap_basepoint p)⟩

@[simp] theorem actualFiberBasepoint_val (p : E ⟶ B) :
    (actualFiberBasepoint p).1 = underTopBasepoint E :=
  rfl

@[simp] theorem actualFiberBasepoint_property (p : E ⟶ B) :
    p.right.hom (actualFiberBasepoint p).1 = underTopBasepoint B := by
  exact (actualFiberBasepoint p).2

/-- The actual fiber `p⁻¹' {underTopBasepoint B}` of a based map `p : E ⟶ B`, regarded as a based
space with distinguished point `actualFiberBasepoint p`. -/
def actualFiber (p : E ⟶ B) : Under (⊤_ TopCat.{u}) :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (actualFiberBasepoint p)))

/-- The chosen basepoint of `actualFiber p` is `actualFiberBasepoint p`. -/
@[simp] theorem underTopBasepoint_actualFiber (p : E ⟶ B) :
    underTopBasepoint (actualFiber p) = actualFiberBasepoint p :=
  rfl

/-- The inclusion of the actual fiber into the homotopy fiber sends a point of the actual fiber to
the same point of `E` together with the constant path at `underTopBasepoint B`. -/
def actualFiberToHomotopyFiberFun (p : E ⟶ B) :
    actualFiberSet p → HomotopyFiber p :=
  fun x ↦
    HomotopyFiber.mk x.1 (PathSpace.basepoint (underTopBasepoint B))
      (((mem_fiber_iff p.right.hom (underTopBasepoint B) x.1).1 x.2).trans
        (PathSpace.endpoint_basepoint (underTopBasepoint B)).symm)

/-- The inclusion function from the actual fiber to the homotopy fiber is continuous. -/
theorem actualFiberToHomotopyFiberFun_continuous (p : E ⟶ B) :
    Continuous (actualFiberToHomotopyFiberFun p) := by
  -- First pair the fiber point with the constant based path, then cut down to the homotopy fiber.
  have hpair :
      Continuous fun x : actualFiberSet p ↦
        (x.1, PathSpace.basepoint (underTopBasepoint B)) := by
    exact continuous_subtype_val.prodMk continuous_const
  simpa [actualFiberToHomotopyFiberFun] using
    hpair.subtype_mk
      (fun x ↦
        (((mem_fiber_iff p.right.hom (underTopBasepoint B) x.1).1 x.2).trans
          (PathSpace.endpoint_basepoint (underTopBasepoint B)).symm))

/-- The inclusion of the actual fiber into the homotopy fiber as a continuous map. -/
def actualFiberToHomotopyFiberContinuousMap (p : E ⟶ B) :
    C(actualFiberSet p, HomotopyFiber p) :=
  { toFun := actualFiberToHomotopyFiberFun p
    continuous_toFun := actualFiberToHomotopyFiberFun_continuous p }

/-- The actual-fiber inclusion preserves the distinguished basepoints, so it is a morphism of
based spaces. -/
theorem actualFiberToHomotopyFiber_w (p : E ⟶ B) :
    (actualFiber p).hom ≫ TopCat.ofHom (actualFiberToHomotopyFiberContinuousMap p) =
      (homotopyFiber p).hom := by
  -- Both terminal maps pick out the actual-fiber basepoint with the constant path at the target
  -- basepoint.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((actualFiber p).hom ≫ TopCat.ofHom (actualFiberToHomotopyFiberContinuousMap p)) x
        = actualFiberToHomotopyFiberFun p (actualFiberBasepoint p) := rfl
    _ = (homotopyFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = (homotopyFiber p).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
          rw [hx]
    _ = (homotopyFiber p).hom x := by
          simp

/-- The inclusion of the actual fiber into the homotopy fiber as a based map. -/
def actualFiberToHomotopyFiber (p : E ⟶ B) : actualFiber p ⟶ homotopyFiber p :=
  Under.homMk
    (TopCat.ofHom (actualFiberToHomotopyFiberContinuousMap p))
    (actualFiberToHomotopyFiber_w p)

/-- The underlying map of `actualFiberToHomotopyFiber p` sends a fiber point to the same point of
`E` equipped with the constant path at `underTopBasepoint B`. -/
@[simp] theorem actualFiberToHomotopyFiber_hom_apply (p : E ⟶ B) (x : actualFiberSet p) :
    (actualFiberToHomotopyFiber p).right.hom x =
      HomotopyFiber.mk x.1 (PathSpace.basepoint (underTopBasepoint B))
        (((mem_fiber_iff p.right.hom (underTopBasepoint B) x.1).1 x.2).trans
          (PathSpace.endpoint_basepoint (underTopBasepoint B)).symm) :=
  rfl

/-- Helper for Lemma 8.6.9: the parameter `1 - t` lies in the unit interval. -/
theorem oneSub_mem (t : I) : (1 - (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · linarith [t.2.2]
  · linarith [t.2.1]

/-- Helper for Lemma 8.6.9: time reversal on `I` given by `t ↦ 1 - t`. -/
def oneSub (t : I) : I :=
  ⟨1 - (t : ℝ), oneSub_mem t⟩

@[simp] theorem oneSub_zero : oneSub (0 : I) = (1 : I) := by
  apply Subtype.ext
  simp [oneSub]

@[simp] theorem oneSub_one : oneSub (1 : I) = (0 : I) := by
  apply Subtype.ext
  simp [oneSub]

/-- Helper for Lemma 8.6.9: time reversal on `I` is involutive. -/
@[simp] theorem oneSub_oneSub (t : I) : oneSub (oneSub t) = t := by
  apply Subtype.ext
  simp [oneSub]

/-- Helper for Lemma 8.6.9: time reversal varies continuously on `I`. -/
theorem oneSub_continuous : Continuous fun t : I ↦ oneSub t := by
  simpa [oneSub] using (unitInterval.continuous_symm : Continuous unitInterval.symm)

/-- Helper for Lemma 8.6.9: multiplying by `1 - t` defines a self-map of `I`. -/
theorem truncateParameter_mem (t s : I) :
    ((oneSub t : I) : ℝ) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (oneSub t).2.1 s.2.1
  · nlinarith [(oneSub t).2.1, (oneSub t).2.2, s.2.1, s.2.2]

/-- Helper for Lemma 8.6.9: the truncation parameter varies continuously with the path variable.
-/
theorem truncateParameter_continuous (t : I) :
    Continuous fun s : I ↦
      (⟨((oneSub t : I) : ℝ) * (s : ℝ), truncateParameter_mem t s⟩ : I) := by
  -- The explicit affine formula is continuous, and the subtype condition is handled pointwise.
  simpa using
    (by
      fun_prop :
        Continuous fun s : I ↦
          (⟨((oneSub t : I) : ℝ) * (s : ℝ), truncateParameter_mem t s⟩ : I))

/-- Helper for Lemma 8.6.9: reparameterizing `I` by multiplication with `1 - t`. -/
def truncateParameter (t : I) : C(I, I) :=
  ⟨fun s ↦ ⟨((oneSub t : I) : ℝ) * (s : ℝ), truncateParameter_mem t s⟩,
    truncateParameter_continuous t⟩

@[simp] theorem truncateParameter_zero (t : I) :
    truncateParameter t 0 = 0 := by
  apply Subtype.ext
  simp [truncateParameter]

@[simp] theorem truncateParameter_one (t : I) :
    truncateParameter t 1 = oneSub t := by
  apply Subtype.ext
  simp [truncateParameter]

/-- Helper for Lemma 8.6.9: the two-variable truncation parameter is continuous. -/
theorem truncateParameterPair_continuous :
    Continuous fun q : I × I ↦ truncateParameter q.1 q.2 := by
  simpa [truncateParameter] using
    (by
      fun_prop :
        Continuous fun q : I × I ↦
          (⟨((oneSub q.1 : I) : ℝ) * (q.2 : ℝ), truncateParameter_mem q.1 q.2⟩ : I))

/-- Helper for Lemma 8.6.9: truncating a path preserves the prescribed source basepoint. -/
theorem truncatedPath_source (χ : P[underTopBasepoint B]) (t : I) :
    (χ.1.comp (truncateParameter t)) 0 = underTopBasepoint B := by
  -- At `0`, the truncated path still evaluates the original path at `0`.
  simp [truncateParameter_zero]

/-- Helper for Lemma 8.6.9: truncating a path to the initial segment of length `1 - t`. -/
def truncatedPath (χ : P[underTopBasepoint B]) (t : I) : P[underTopBasepoint B] :=
  PathSpace.mk (χ.1.comp (truncateParameter t)) (truncatedPath_source χ t)

@[simp] theorem truncatedPath_endpoint (χ : P[underTopBasepoint B]) (t : I) :
    (truncatedPath χ t).endpoint = χ (oneSub t) := by
  -- Evaluating at time `1` reads off the endpoint of the truncated segment.
  simp [truncatedPath, truncateParameter_one]

/-- Helper for Lemma 8.6.9: truncating at `t = 0` leaves the path unchanged. -/
@[simp] theorem truncatedPath_zero (χ : P[underTopBasepoint B]) :
    truncatedPath χ 0 = χ := by
  apply Subtype.ext
  ext s
  simp [truncatedPath, truncateParameter, oneSub]

/-- Helper for Lemma 8.6.9: truncating at `t = 1` collapses the path to the constant basepoint
path. -/
@[simp] theorem truncatedPath_one (χ : P[underTopBasepoint B]) :
    truncatedPath χ 1 = PathSpace.basepoint (underTopBasepoint B) := by
  apply Subtype.ext
  ext s
  change χ.1 (truncateParameter 1 s) = underTopBasepoint B
  simp [truncateParameter, oneSub]

/-- Helper for Lemma 8.6.9: truncating the constant basepoint path leaves it unchanged. -/
@[simp] theorem truncatedPath_basepoint (t : I) :
    truncatedPath (PathSpace.basepoint (underTopBasepoint B)) t =
      PathSpace.basepoint (underTopBasepoint B) := by
  apply Subtype.ext
  ext s
  rfl

/-- Helper for Lemma 8.6.9: truncation is continuous in both the path and the truncation
parameter. -/
theorem truncatedPath_continuous :
    Continuous fun q : P[underTopBasepoint B] × I ↦ truncatedPath q.1 q.2 := by
  let family : P[underTopBasepoint B] × I → C(I, B.right) :=
    fun q ↦ q.1.1.comp (truncateParameter q.2)
  have hfamily : Continuous family := by
    have hpath :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦
          r.1.1.1 := by
      exact continuous_subtype_val.comp continuous_fst.fst
    have hparam :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ truncateParameter r.1.2 r.2 := by
      have hpair : Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ (r.1.2, r.2) := by
        fun_prop
      exact truncateParameterPair_continuous.comp hpair
    have huncurry :
        Continuous fun r : (P[underTopBasepoint B] × I) × I ↦ family r.1 r.2 := by
      -- Evaluate the reparameterized path family pointwise and use compact-open currying.
      simpa [family, Function.comp] using
        (continuous_eval.comp (hpath.prodMk hparam) :
          Continuous fun r : (P[underTopBasepoint B] × I) × I ↦
            r.1.1.1 (truncateParameter r.1.2 r.2))
    exact ContinuousMap.continuous_of_continuous_uncurry family huncurry
  -- Package the continuous reparameterized path back into the path-space subtype.
  simpa [truncatedPath, PathSpace.mk] using
    hfamily.subtype_mk (fun q ↦ truncatedPath_source q.1 q.2)

/-- Helper for Lemma 8.6.9: a based relative homotopy yields a homotopy in
`Under (⊤_ TopCat)`. -/
theorem homotopicUnder_of_hrel {X Y : BasedSpace} {f₀ f₁ : X ⟶ Y}
    (H : f₀.right.hom HRel[X] f₁.right.hom) :
    HomotopicUnder f₀ f₁ := by
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t
  -- A singleton-relative homotopy fixes the chosen basepoint at every stage, which is exactly
  -- the under-category condition for based spaces.
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

/-- Helper for Lemma 8.6.9: a based map preserves the chosen basepoint. -/
theorem basedMapUnderTopBasepoint {A X : BasedSpace.{u}} (i : A ⟶ X) :
    i.right.hom (underTopBasepoint A) = underTopBasepoint X := by
  -- Evaluate the `Under` commutativity condition at the unique point of the terminal object.
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (Under.w i)
  simpa [underTopBasepoint] using hw

/-- Helper for Lemma 8.6.9: an explicit path family with prescribed endpoints and basepoint
constancy determines a singleton-relative homotopy. -/
def basedHomotopyRelOfPathFamily {A X : BasedSpace.{u}} {f₀ f₁ : C(A.right, X.right)}
    (d : C(A.right, C(I, X.right)))
    (h₀ : ∀ a : A.right, d a 0 = f₀ a)
    (h₁ : ∀ a : A.right, d a 1 = f₁ a)
    (hrel : ∀ a : A.right, a ∈ basedBasepointSet A →
      d a = ContinuousMap.const I (f₀ a)) :
    f₀ HRel[A] f₁ := by
  -- Route correction: localize the path-family-to-`HRel` bridge here so this file no longer
  -- depends on the parse-broken prerequisite `Lemma_8_3_4`.
  refine
    { toHomotopy := ?_
      prop' := ?_ }
  · -- Uncurrying the path family gives the underlying homotopy.
    refine
      { toFun := fun p ↦ d p.2 p.1
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- The compact-open adjunction packages continuity of `d` into continuity on `I × A`.
      exact
        (ContinuousMap.continuous_uncurry_of_continuous d).comp
          (Homeomorph.prodComm I A.right).continuous_toFun
    · intro a
      simpa using h₀ a
    · intro a
      simpa using h₁ a
  · intro t a ha
    -- On the singleton basepoint subset, the path family is literally constant.
    have hconst := hrel a ha
    simp [hconst]

/-- Helper for Lemma 8.6.9: the composite `HomotopyFiber p → E → B` is continuous on underlying
spaces. -/
theorem homotopyFiberPointProjectionContinuous (p : E ⟶ B) :
    Continuous fun z : HomotopyFiber p ↦ z.point := by
  -- Project to the `E`-coordinate of the defining subtype.
  simpa [HomotopyFiber.point] using
    (continuous_fst.comp continuous_subtype_val :
      Continuous fun z : HomotopyFiber p ↦ z.1.1)

/-- Helper for Lemma 8.6.9: the underlying `TopCat` morphism `HomotopyFiber p ⟶ E.right`
remembering only the point coordinate. -/
def homotopyFiberPointProjectionHom (p : E ⟶ B) :
    (homotopyFiber p).right ⟶ E.right :=
  TopCat.ofHom ⟨fun z ↦ z.point, homotopyFiberPointProjectionContinuous p⟩

/-- Helper for Lemma 8.6.9: evaluating the unbased point projection of `HomotopyFiber p`
returns the underlying point of `E`. -/
@[simp] theorem homotopyFiberPointProjectionHom_apply (p : E ⟶ B) (z : HomotopyFiber p) :
    homotopyFiberPointProjectionHom p z = z.point :=
  rfl

/-- Helper for Lemma 8.6.9: the point projection of `HomotopyFiber p` preserves the chosen
basepoints. -/
theorem homotopyFiberPointProjection_w (p : E ⟶ B) :
    (homotopyFiber p).hom ≫ homotopyFiberPointProjectionHom p = E.hom := by
  -- Both terminal maps pick out the source basepoint of `p`.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((homotopyFiber p).hom ≫ homotopyFiberPointProjectionHom p) x
        = underTopBasepoint E := rfl
    _ = E.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = E.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
          rw [hx]
    _ = E.hom x := by
          simp

/-- Helper for Lemma 8.6.9: the based projection `HomotopyFiber p ⟶ E`. -/
def homotopyFiberPointProjection (p : E ⟶ B) : homotopyFiber p ⟶ E :=
  Under.homMk (homotopyFiberPointProjectionHom p) (homotopyFiberPointProjection_w p)

/-- Helper for Lemma 8.6.9: the composite `HomotopyFiber p → E → B` is continuous on underlying
spaces. -/
theorem homotopyFiberProjectionToBase_continuous (p : E ⟶ B) :
    Continuous fun z : HomotopyFiber p ↦ p.right.hom z.point := by
  -- Project to the `E`-coordinate of the defining subtype and then apply `p`.
  exact p.right.hom.continuous.comp (homotopyFiberPointProjectionContinuous p)

/-- Helper for Lemma 8.6.9: the underlying continuous map of `(homotopyFiberProjection p ≫ p)`. -/
def homotopyFiberProjectionToBase (p : E ⟶ B) :
    C((homotopyFiber p).right, B.right) :=
  ⟨fun z ↦ p.right.hom z.point, homotopyFiberProjectionToBase_continuous p⟩

@[simp] theorem homotopyFiberProjectionToBase_apply (p : E ⟶ B) (z : HomotopyFiber p) :
    homotopyFiberProjectionToBase p z = p.right.hom z.point :=
  rfl

/-- Helper for Lemma 8.6.9: rebuilding a homotopy-fiber point from its coordinates recovers the
original point. -/
@[simp] theorem homotopyFiber_eta (p : E ⟶ B) (z : HomotopyFiber p) :
    HomotopyFiber.mk z.point z.path (HomotopyFiber.endpoint_eq z) = z := by
  cases z
  rfl

/-- Helper for Lemma 8.6.9: the path coordinate varies continuously on `HomotopyFiber p`. -/
theorem homotopyFiberPath_continuous (p : E ⟶ B) :
    Continuous fun z : HomotopyFiber p ↦ z.path := by
  -- Project to the path-space coordinate of the defining subtype.
  simpa [HomotopyFiber.path] using
    (continuous_snd.comp continuous_subtype_val :
      Continuous fun z : HomotopyFiber p ↦ z.1.2)

/-- Helper for Lemma 8.6.9: contracting the path coordinate of `HomotopyFiber p` gives a based
homotopy from `(homotopyFiberProjection p ≫ p)` to the constant map at `underTopBasepoint B`. -/
def homotopyFiberPathContraction (p : E ⟶ B) :
    (homotopyFiberProjectionToBase p).HomotopyRel
      (ContinuousMap.const (homotopyFiber p).right (underTopBasepoint B))
      ({underTopBasepoint (homotopyFiber p)} : Set (homotopyFiber p).right) :=
  by
    let reversePathFamily : C((homotopyFiber p).right, C(I, B.right)) :=
      ContinuousMap.curry
        ⟨fun q : HomotopyFiber p × I ↦ q.1.path.1 (oneSub q.2), by
          -- Evaluate the homotopy-fiber path at the reversed parameter.
          have hpath :
              Continuous fun q : HomotopyFiber p × I ↦
                q.1.path.1 := by
            have hpair : Continuous fun q : HomotopyFiber p × I ↦ q.1.1 := by
              exact continuous_subtype_val.comp continuous_fst
            have hpathSpace : Continuous fun q : HomotopyFiber p × I ↦ q.1.1.2 := by
              exact continuous_snd.comp hpair
            simpa [HomotopyFiber.path] using
              ((continuous_subtype_val :
                  Continuous fun χ : P[underTopBasepoint B] ↦ χ.1).comp hpathSpace)
          have hparam : Continuous fun q : HomotopyFiber p × I ↦ oneSub q.2 := by
            exact oneSub_continuous.comp continuous_snd
          -- Evaluate the reversed path coordinate pointwise.
          change Continuous fun q : HomotopyFiber p × I ↦ q.1.path.1 (oneSub q.2)
          simpa [Function.comp] using
            (continuous_eval.comp (hpath.prodMk hparam) :
              Continuous fun q : HomotopyFiber p × I ↦ q.1.path.1 (oneSub q.2))⟩
    -- Reverse each path so that time `0` reads the original endpoint and time `1` reads the
    -- distinguished basepoint.
    refine basedHomotopyRelOfPathFamily reversePathFamily ?_ ?_ ?_
    · intro z
      change z.path (oneSub 0) = p.right.hom z.point
      rw [oneSub_zero]
      exact (HomotopyFiber.endpoint_eq z).symm
    · intro z
      change z.path (oneSub 1) = underTopBasepoint B
      rw [oneSub_one]
      simpa using PathSpace.source_eq z.path
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      -- At the distinguished point, reversing the constant basepoint path does nothing.
      ext t
      simp [reversePathFamily, underTopBasepoint_homotopyFiber]
      rfl

/-- Helper for Lemma 8.6.9: the path contraction, rewritten in the morphism form expected by the
based homotopy lifting property for `p`. -/
def homotopyFiberPathContraction_liftInput (p : E ⟶ B) :
    (homotopyFiberPointProjection p ≫ p).right.hom HRel[homotopyFiber p]
      (constantBasedMap (homotopyFiber p) B).right.hom := by
  -- Recast the already-constructed contraction to the morphism spellings used by the lifting API.
  refine (homotopyFiberPathContraction p).cast ?_ ?_
  · ext z
    rfl
  · ext z
    rfl

/-- Helper for Lemma 8.6.9: the recast path contraction still evaluates by reversing the stored
path coordinate. -/
@[simp] theorem homotopyFiberPathContraction_liftInput_apply (p : E ⟶ B)
    (t : I) (z : HomotopyFiber p) :
    (homotopyFiberPathContraction_liftInput p).toContinuousMap (t, z) = z.path (oneSub t) := by
  -- Unfold the casted relative homotopy and reduce to the original reverse-path family.
  unfold homotopyFiberPathContraction_liftInput homotopyFiberPathContraction
  rfl

/-- Helper for Lemma 8.6.9: lifting the base path contraction produces a terminal map
`homotopyFiber p ⟶ E` together with a based relative homotopy from the projection. -/
theorem exists_homotopyFiberContractionLift (p : E ⟶ B) [IsBasedFibration p] :
    ∃ g₁ : homotopyFiber p ⟶ E,
      ∃ G : (homotopyFiberPointProjection p).right.hom HRel[homotopyFiber p] g₁.right.hom,
        ContinuousMap.comp p.right.hom G.toContinuousMap =
          (homotopyFiberPathContraction_liftInput p).toContinuousMap := by
  -- Apply the based homotopy lifting property to the contraction of the path coordinate.
  exact
    IsBasedFibration.exists_based_homotopyLift
      (p := p)
      (homotopyFiberPathContraction_liftInput p)
      (homotopyFiberPointProjection p)
      rfl

/-- Helper for Lemma 8.6.9: the terminal stage of the lifted contraction. -/
def homotopyFiberLiftTerminal (p : E ⟶ B) [IsBasedFibration p] :
    homotopyFiber p ⟶ E :=
  Classical.choose (exists_homotopyFiberContractionLift p)

/-- Helper for Lemma 8.6.9: the chosen lifted contraction from `homotopyFiberProjection p` to
`homotopyFiberLiftTerminal p`. -/
def homotopyFiberContractionLift (p : E ⟶ B) [IsBasedFibration p] :
    (homotopyFiberPointProjection p).right.hom HRel[homotopyFiber p]
      (homotopyFiberLiftTerminal p).right.hom :=
  Classical.choose (Classical.choose_spec (exists_homotopyFiberContractionLift p))

/-- Helper for Lemma 8.6.9: projecting the chosen lifted contraction along `p` recovers the base
path contraction. -/
theorem homotopyFiberContractionLift_comm (p : E ⟶ B) [IsBasedFibration p] :
    ContinuousMap.comp p.right.hom (homotopyFiberContractionLift p).toContinuousMap =
      (homotopyFiberPathContraction_liftInput p).toContinuousMap :=
  Classical.choose_spec (Classical.choose_spec (exists_homotopyFiberContractionLift p))

/-- Helper for Lemma 8.6.9: the terminal stage of the lifted contraction lands in the actual
fiber. -/
theorem homotopyFiberLiftTerminal_mem_actualFiberSet (p : E ⟶ B) [IsBasedFibration p]
    (z : HomotopyFiber p) :
    p.right.hom ((homotopyFiberLiftTerminal p).right.hom z) = underTopBasepoint B := by
  -- Evaluate the projected lifted homotopy at time `1`, where the base contraction has reached
  -- the constant path at the chosen basepoint of `B`.
  have hcomm :=
    congrArg
      (fun k : C(I × (homotopyFiber p).right, B.right) ↦ k (1, z))
      (homotopyFiberContractionLift_comm p)
  calc
    p.right.hom ((homotopyFiberLiftTerminal p).right.hom z)
        = p.right.hom ((homotopyFiberContractionLift p).toContinuousMap (1, z)) := by
            simpa using congrArg p.right.hom ((homotopyFiberContractionLift p).map_one_left z).symm
    _ = (homotopyFiberPathContraction_liftInput p).toContinuousMap (1, z) := by
          simpa using hcomm
    _ = underTopBasepoint B := by
          simpa [homotopyFiberPathContraction_liftInput, constantBasedMap]

/-- Helper for Lemma 8.6.9: the terminal stage of the lifted contraction, viewed as a point of
the actual fiber. -/
def homotopyFiberToActualFiberFun (p : E ⟶ B) [IsBasedFibration p] :
    HomotopyFiber p → actualFiberSet p :=
  fun z ↦ ⟨(homotopyFiberLiftTerminal p).right.hom z,
    homotopyFiberLiftTerminal_mem_actualFiberSet p z⟩

/-- Helper for Lemma 8.6.9: the terminal stage of the lifted contraction varies continuously in
the actual fiber. -/
theorem homotopyFiberToActualFiberFun_continuous (p : E ⟶ B) [IsBasedFibration p] :
    Continuous (homotopyFiberToActualFiberFun p) := by
  -- The underlying point track is continuous, and the fiber condition is supplied separately.
  exact ((homotopyFiberLiftTerminal p).right.hom.continuous).subtype_mk
    (fun z : (homotopyFiber p).right ↦ homotopyFiberLiftTerminal_mem_actualFiberSet p z)

/-- Helper for Lemma 8.6.9: the lifted terminal stage sends the homotopy-fiber basepoint to the
actual-fiber basepoint. -/
theorem homotopyFiberToActualFiberFun_basepoint (p : E ⟶ B) [IsBasedFibration p] :
    homotopyFiberToActualFiberFun p (underTopBasepoint (homotopyFiber p)) =
      actualFiberBasepoint p := by
  -- Compare the two actual-fiber points by their underlying coordinates in `E`.
  apply Subtype.ext
  change
    (homotopyFiberLiftTerminal p).right.hom (underTopBasepoint (homotopyFiber p)) =
      underTopBasepoint E
  exact basedMapUnderTopBasepoint (homotopyFiberLiftTerminal p)

/-- Helper for Lemma 8.6.9: the terminal stage of the lifted contraction as a based map from the
homotopy fiber to the actual fiber. -/
def homotopyFiberToActualFiber (p : E ⟶ B) [IsBasedFibration p] :
    homotopyFiber p ⟶ actualFiber p :=
  Under.homMk
    (TopCat.ofHom
      ⟨homotopyFiberToActualFiberFun p, homotopyFiberToActualFiberFun_continuous p⟩)
    (by
      -- Both maps out of the terminal object are determined by the actual-fiber basepoint.
      ext x
      have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
        cases h : TopCat.terminalIsoPUnit.hom x
        rfl
      calc
        ((homotopyFiber p).hom ≫
              TopCat.ofHom ⟨homotopyFiberToActualFiberFun p,
                homotopyFiberToActualFiberFun_continuous p⟩) x
            = homotopyFiberToActualFiberFun p (underTopBasepoint (homotopyFiber p)) := rfl
        _ = actualFiberBasepoint p := homotopyFiberToActualFiberFun_basepoint p
        _ = (actualFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
        _ = (actualFiber p).hom
              (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
                rw [hx]
        _ = (actualFiber p).hom x := by
              simp)

/-- Helper for Lemma 8.6.9: the underlying map of `homotopyFiberToActualFiber p` is the terminal
stage of the lifted contraction, packaged as a point of the actual fiber. -/
@[simp] theorem homotopyFiberToActualFiber_hom_apply (p : E ⟶ B) [IsBasedFibration p]
    (z : HomotopyFiber p) :
    (homotopyFiberToActualFiber p).right.hom z =
      ⟨(homotopyFiberLiftTerminal p).right.hom z,
        homotopyFiberLiftTerminal_mem_actualFiberSet p z⟩ :=
  rfl

/-- Helper for Lemma 8.6.9: the chosen lifted contraction and the truncated path define a point of
`HomotopyFiber p` at each time. -/
theorem homotopyFiberDeformation_condition (p : E ⟶ B) [IsBasedFibration p]
    (q : HomotopyFiber p × I) :
    p.right.hom ((homotopyFiberContractionLift p).toContinuousMap (q.2, q.1)) =
      (truncatedPath q.1.path q.2).endpoint := by
  -- Compare the lifted contraction with the contracted base path pointwise.
  have hcomm :=
    congrArg
      (fun k : C(I × (homotopyFiber p).right, B.right) ↦ k (q.2, q.1))
      (homotopyFiberContractionLift_comm p)
  calc
    p.right.hom ((homotopyFiberContractionLift p).toContinuousMap (q.2, q.1))
        = (homotopyFiberPathContraction_liftInput p).toContinuousMap (q.2, q.1) := by
            simpa using hcomm
    _ = q.1.path (oneSub q.2) := by
          simpa using homotopyFiberPathContraction_liftInput_apply p q.2 q.1
    _ = (truncatedPath q.1.path q.2).endpoint := by
          rw [truncatedPath_endpoint]

/-- Helper for Lemma 8.6.9: the actual-fiber inclusion sends the actual-fiber basepoint to the
homotopy-fiber basepoint. -/
@[simp] theorem actualFiberToHomotopyFiberFun_basepoint (p : E ⟶ B) :
    actualFiberToHomotopyFiberFun p (underTopBasepoint (actualFiber p)) =
      underTopBasepoint (homotopyFiber p) := by
  -- Compare the value at the chosen actual-fiber basepoint with the based-map image formula.
  simpa [underTopBasepoint_actualFiber] using
    basedMapUnderTopBasepoint (actualFiberToHomotopyFiber p)

/-- Helper for Lemma 8.6.9: the restricted lifted contraction stays in the actual fiber at every
stage. -/
theorem actualFiberContractionStage_mem (p : E ⟶ B) [IsBasedFibration p]
    (q : actualFiberSet p × I) :
    p.right.hom ((homotopyFiberContractionLift p).toContinuousMap
        (q.2, actualFiberToHomotopyFiberFun p q.1)) = underTopBasepoint B := by
  -- Project the lifted contraction to `B` and evaluate it on a constant-path representative.
  have hcomm :=
    congrArg
      (fun k : C(I × (homotopyFiber p).right, B.right) ↦
        k (q.2, actualFiberToHomotopyFiberFun p q.1))
      (homotopyFiberContractionLift_comm p)
  calc
    p.right.hom ((homotopyFiberContractionLift p).toContinuousMap
        (q.2, actualFiberToHomotopyFiberFun p q.1))
        = (homotopyFiberPathContraction_liftInput p).toContinuousMap
            (q.2, actualFiberToHomotopyFiberFun p q.1) := by
              simpa using hcomm
    _ = (actualFiberToHomotopyFiberFun p q.1).path (oneSub q.2) := by
          simpa using
            homotopyFiberPathContraction_liftInput_apply p q.2
              (actualFiberToHomotopyFiberFun p q.1)
    _ = underTopBasepoint B := by
          rfl

/-- Helper for Lemma 8.6.9: the restricted lifted contraction varies continuously in the actual
fiber. -/
theorem actualFiberRetractionFamily_continuous (p : E ⟶ B) [IsBasedFibration p] :
    Continuous fun q : actualFiberSet p × I ↦
      (⟨(homotopyFiberContractionLift p).toContinuousMap
          (q.2, actualFiberToHomotopyFiberFun p q.1),
        actualFiberContractionStage_mem p q⟩ : actualFiberSet p) := by
  -- Compose the chosen lifted contraction with the actual-fiber inclusion and then repackage the
  -- result into the actual-fiber subtype.
  have hpair :
      Continuous fun q : actualFiberSet p × I ↦
        (q.2, actualFiberToHomotopyFiberFun p q.1) := by
    exact continuous_snd.prodMk ((actualFiberToHomotopyFiberFun_continuous p).comp continuous_fst)
  have hraw :
      Continuous fun q : actualFiberSet p × I ↦
        (homotopyFiberContractionLift p).toContinuousMap
          (q.2, actualFiberToHomotopyFiberFun p q.1) := by
    exact (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair
  exact hraw.subtype_mk (fun q ↦ actualFiberContractionStage_mem p q)

/-- Helper for Lemma 8.6.9: the restricted lifted contraction as an actual-fiber-valued path
family. -/
def actualFiberRetractionFamily (p : E ⟶ B) [IsBasedFibration p] :
    C((actualFiber p).right, C(I, (actualFiber p).right)) :=
  ContinuousMap.curry
    ⟨fun q : actualFiberSet p × I ↦
        ⟨(homotopyFiberContractionLift p).toContinuousMap
            (q.2, actualFiberToHomotopyFiberFun p q.1),
          actualFiberContractionStage_mem p q⟩,
      actualFiberRetractionFamily_continuous p⟩

/-- Helper for Lemma 8.6.9: at time `0`, the restricted lifted contraction is the identity on the
actual fiber. -/
@[simp] theorem actualFiberRetractionFamily_zero (p : E ⟶ B) [IsBasedFibration p]
    (x : actualFiberSet p) :
    actualFiberRetractionFamily p x 0 = x := by
  -- The lifted contraction starts at the homotopy-fiber projection, which recovers the same
  -- underlying point of the actual fiber.
  apply Subtype.ext
  change (homotopyFiberContractionLift p).toContinuousMap
      (0, actualFiberToHomotopyFiberFun p x) = x.1
  calc
    (homotopyFiberContractionLift p).toContinuousMap
        (0, actualFiberToHomotopyFiberFun p x)
        = (homotopyFiberPointProjection p).right.hom (actualFiberToHomotopyFiberFun p x) := by
            simpa using (homotopyFiberContractionLift p).map_zero_left
              (actualFiberToHomotopyFiberFun p x)
    _ = x.1 := by
          rfl

/-- Helper for Lemma 8.6.9: at time `1`, the restricted lifted contraction reaches
`actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p`. -/
@[simp] theorem actualFiberRetractionFamily_one (p : E ⟶ B) [IsBasedFibration p]
    (x : actualFiberSet p) :
    actualFiberRetractionFamily p x 1 =
      (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom x := by
  -- The terminal stage of the lift is exactly the chosen actual-fiber retraction.
  apply Subtype.ext
  change (homotopyFiberContractionLift p).toContinuousMap
      (1, actualFiberToHomotopyFiberFun p x) =
        ((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom x).1
  simpa [Category.assoc, actualFiberToHomotopyFiberFun, actualFiberToHomotopyFiber_hom_apply,
    homotopyFiberToActualFiber_hom_apply] using
    (homotopyFiberContractionLift p).map_one_left (actualFiberToHomotopyFiberFun p x)

/-- Helper for Lemma 8.6.9: the restricted lifted contraction fixes the chosen actual-fiber
basepoint at every stage. -/
theorem actualFiberRetractionFamily_basepoint (p : E ⟶ B) [IsBasedFibration p] :
    actualFiberRetractionFamily p (underTopBasepoint (actualFiber p)) =
      ContinuousMap.const I (underTopBasepoint (actualFiber p)) := by
  -- The homotopy-fiber lift is relative to the basepoint, and the actual-fiber basepoint maps to
  -- the homotopy-fiber basepoint.
  ext t
  apply Subtype.ext
  have hstage :
      (homotopyFiberContractionLift p).toContinuousMap
        (t, actualFiberToHomotopyFiberFun p (underTopBasepoint (actualFiber p))) =
          underTopBasepoint E := by
    have hrel :=
      (homotopyFiberContractionLift p).eq_fst t
        (by simpa [basedBasepointSet] using actualFiberToHomotopyFiberFun_basepoint p)
    simpa [actualFiberToHomotopyFiberFun_basepoint p, homotopyFiberPointProjectionHom_apply,
      underTopBasepoint_homotopyFiber] using hrel
  simpa [actualFiberRetractionFamily, hstage, underTopBasepoint_actualFiber]

/-- Helper for Lemma 8.6.9: the actual-fiber path family is constant on the chosen basepoint. -/
theorem actualFiberRetractionFamily_rel (p : E ⟶ B) [IsBasedFibration p]
    (x : (actualFiber p).right) (hx : x ∈ basedBasepointSet (actualFiber p)) :
    actualFiberRetractionFamily p x = ContinuousMap.const I x := by
  -- The relative condition reduces to the unique point of `basedBasepointSet (actualFiber p)`.
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact actualFiberRetractionFamily_basepoint p

/-- Helper for Lemma 8.6.9: the restricted lifted contraction packages into a relative homotopy
from the identity of the actual fiber to
`actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p`. -/
def actualFiberRetractionHRel (p : E ⟶ B) [IsBasedFibration p] :
    (ContinuousMap.id (actualFiber p).right) HRel[actualFiber p]
      (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom :=
  basedHomotopyRelOfPathFamily
    (actualFiberRetractionFamily p)
    (actualFiberRetractionFamily_zero p)
    (actualFiberRetractionFamily_one p)
    (actualFiberRetractionFamily_rel p)

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation family is continuous. -/
theorem homotopyFiberDeformationFamily_continuous (p : E ⟶ B) [IsBasedFibration p] :
    Continuous fun q : HomotopyFiber p × I ↦
      HomotopyFiber.mk
        ((homotopyFiberContractionLift p).toContinuousMap (q.2, q.1))
        (truncatedPath q.1.path q.2)
        (homotopyFiberDeformation_condition p q) := by
  -- The point coordinate comes from the lifted contraction, and the path coordinate comes from
  -- truncating the original homotopy-fiber path.
  have hpoint :
      Continuous fun q : HomotopyFiber p × I ↦
        (homotopyFiberContractionLift p).toContinuousMap (q.2, q.1) := by
    have hpair : Continuous fun q : HomotopyFiber p × I ↦ (q.2, q.1) := by
      exact continuous_snd.prodMk continuous_fst
    exact (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair
  have hpath :
      Continuous fun q : HomotopyFiber p × I ↦ truncatedPath q.1.path q.2 := by
    have hpair : Continuous fun q : HomotopyFiber p × I ↦ (q.1.path, q.2) := by
      exact ((homotopyFiberPath_continuous p).comp continuous_fst).prodMk continuous_snd
    exact truncatedPath_continuous.comp hpair
  have hraw :
      Continuous fun q : HomotopyFiber p × I ↦
        ((homotopyFiberContractionLift p).toContinuousMap (q.2, q.1),
          truncatedPath q.1.path q.2) := by
    exact hpoint.prodMk hpath
  simpa [HomotopyFiber.mk] using
    hraw.subtype_mk (fun q ↦ homotopyFiberDeformation_condition p q)

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation family. -/
def homotopyFiberDeformationFamily (p : E ⟶ B) [IsBasedFibration p] :
    C((homotopyFiber p).right, C(I, (homotopyFiber p).right)) :=
  ContinuousMap.curry
    ⟨fun q : HomotopyFiber p × I ↦
        HomotopyFiber.mk
          ((homotopyFiberContractionLift p).toContinuousMap (q.2, q.1))
          (truncatedPath q.1.path q.2)
          (homotopyFiberDeformation_condition p q),
      homotopyFiberDeformationFamily_continuous p⟩

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation starts at the identity. -/
@[simp] theorem homotopyFiberDeformationFamily_zero (p : E ⟶ B) [IsBasedFibration p]
    (z : HomotopyFiber p) :
    homotopyFiberDeformationFamily p z 0 = z := by
  -- At time `0`, the point coordinate is the original point and the truncated path is unchanged.
  change
    HomotopyFiber.mk
      ((homotopyFiberContractionLift p).toContinuousMap (0, z))
      (truncatedPath z.path 0)
      (homotopyFiberDeformation_condition p (z, 0)) = z
  have hpoint :
      (homotopyFiberContractionLift p).toContinuousMap (0, z) = z.point := by
    calc
      (homotopyFiberContractionLift p).toContinuousMap (0, z)
          = (homotopyFiberPointProjection p).right.hom z := by
              simpa using (homotopyFiberContractionLift p).map_zero_left z
      _ = z.point := by
            rfl
  simpa [truncatedPath_zero, hpoint] using homotopyFiber_eta p z

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation ends at the constant-path
representative determined by `homotopyFiberToActualFiber p`. -/
@[simp] theorem homotopyFiberDeformationFamily_one (p : E ⟶ B) [IsBasedFibration p]
    (z : HomotopyFiber p) :
    homotopyFiberDeformationFamily p z 1 =
      (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p).right.hom z := by
  -- At time `1`, the truncated path is constant and the point coordinate is the terminal lifted
  -- point in the actual fiber.
  change
    HomotopyFiber.mk
      ((homotopyFiberContractionLift p).toContinuousMap (1, z))
      (truncatedPath z.path 1)
      (homotopyFiberDeformation_condition p (z, 1)) =
        (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p).right.hom z
  have hpoint :
      (homotopyFiberContractionLift p).toContinuousMap (1, z) =
        (homotopyFiberLiftTerminal p).right.hom z := by
    simpa using (homotopyFiberContractionLift p).map_one_left z
  simpa [truncatedPath_one, hpoint, Category.assoc, actualFiberToHomotopyFiber_hom_apply,
    homotopyFiberToActualFiber_hom_apply]

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation fixes the chosen basepoint at every
stage. -/
theorem homotopyFiberDeformationFamily_basepoint (p : E ⟶ B) [IsBasedFibration p] :
    homotopyFiberDeformationFamily p (underTopBasepoint (homotopyFiber p)) =
      ContinuousMap.const I (underTopBasepoint (homotopyFiber p)) := by
  -- The lifted point coordinate is relative to the homotopy-fiber basepoint, and the truncated
  -- path of the constant basepoint path is still constant.
  ext t
  have hstage :
      (homotopyFiberContractionLift p).toContinuousMap (t, underTopBasepoint (homotopyFiber p)) =
        underTopBasepoint E := by
    simpa [basedBasepointSet, homotopyFiberPointProjectionHom_apply, underTopBasepoint_homotopyFiber] using
      (homotopyFiberContractionLift p).eq_fst t (by simp [basedBasepointSet])
  -- Compare only the underlying pair of coordinates; this avoids rewriting inside the subtype
  -- proof of `HomotopyFiber.mk`.
  apply Subtype.ext
  change
    (((homotopyFiberContractionLift p).toContinuousMap (t, underTopBasepoint (homotopyFiber p))),
        truncatedPath (underTopBasepoint (homotopyFiber p)).path t) =
      (underTopBasepoint E, PathSpace.basepoint (underTopBasepoint B))
  rw [hstage, underTopBasepoint_homotopyFiber, HomotopyFiber.path_basepoint,
    truncatedPath_basepoint]

/-- Helper for Lemma 8.6.9: the homotopy-fiber deformation family is constant on the chosen
basepoint. -/
theorem homotopyFiberDeformationFamily_rel (p : E ⟶ B) [IsBasedFibration p]
    (z : (homotopyFiber p).right) (hz : z ∈ basedBasepointSet (homotopyFiber p)) :
    homotopyFiberDeformationFamily p z = ContinuousMap.const I z := by
  -- The relative condition again reduces to the unique point of the singleton basepoint subset.
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact homotopyFiberDeformationFamily_basepoint p

/-- Helper for Lemma 8.6.9: the lifted contraction deforms `HomotopyFiber p` to the constant-path
representatives coming from the actual fiber. -/
def homotopyFiberDeformationHRel (p : E ⟶ B) [IsBasedFibration p] :
    (ContinuousMap.id (homotopyFiber p).right) HRel[homotopyFiber p]
      (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p).right.hom :=
  basedHomotopyRelOfPathFamily
    (homotopyFiberDeformationFamily p)
    (homotopyFiberDeformationFamily_zero p)
    (homotopyFiberDeformationFamily_one p)
    (homotopyFiberDeformationFamily_rel p)

/-- Helper for Lemma 8.6.9: reversing the homotopy-fiber deformation gives a homotopy under from
`homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p` to the identity. -/
theorem homotopyFiberRetractionHomotopicUnder (p : E ⟶ B) [IsBasedFibration p] :
    HomotopicUnder
      ((homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p :
          homotopyFiber p ⟶ homotopyFiber p))
      (𝟙 (homotopyFiber p)) := by
  -- Repackage the reversed relative homotopy as a homotopy in the under category.
  let H : (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p).right.hom
      HRel[homotopyFiber p] (ContinuousMap.id (homotopyFiber p).right) :=
    (homotopyFiberDeformationHRel p).symm
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hstage :
      H (t, underTopBasepoint (homotopyFiber p)) = underTopBasepoint (homotopyFiber p) := by
    calc
      H (t, underTopBasepoint (homotopyFiber p))
          = (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p).right.hom
              (underTopBasepoint (homotopyFiber p)) := by
                exact H.eq_fst t (by simp [basedBasepointSet])
      _ = underTopBasepoint (homotopyFiber p) := by
            simpa using
              basedMapUnderTopBasepoint
                (homotopyFiberToActualFiber p ≫ actualFiberToHomotopyFiber p)
  calc
    (H.toHomotopy.curry t).comp (homotopyFiber p).hom.hom x
        = H (t, (homotopyFiber p).hom x) := rfl
    _ = H (t, underTopBasepoint (homotopyFiber p)) := by
      rw [show (homotopyFiber p).hom x = underTopBasepoint (homotopyFiber p) by
        change (homotopyFiber p).hom x =
          (homotopyFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)
        rw [← hx]
        simp]
    _ = underTopBasepoint (homotopyFiber p) := hstage
    _ = (homotopyFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = (homotopyFiber p).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
            rw [hx]
    _ = (homotopyFiber p).hom x := by
          simp

/-- Helper for Lemma 8.6.9: reversing the restricted lifted contraction gives a homotopy under from
`actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p` to the identity. -/
theorem actualFiberRetractionHomotopicUnder (p : E ⟶ B) [IsBasedFibration p] :
    HomotopicUnder
      ((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p :
          actualFiber p ⟶ actualFiber p))
      (𝟙 (actualFiber p)) := by
  -- Repackage the reversed actual-fiber relative homotopy as a homotopy in the under category.
  let H : (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom
      HRel[actualFiber p] (ContinuousMap.id (actualFiber p).right) :=
    (actualFiberRetractionHRel p).symm
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hstage :
      H (t, underTopBasepoint (actualFiber p)) = underTopBasepoint (actualFiber p) := by
    calc
      H (t, underTopBasepoint (actualFiber p))
          = (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom
              (underTopBasepoint (actualFiber p)) := by
                exact H.eq_fst t (by simp [basedBasepointSet])
      _ = underTopBasepoint (actualFiber p) := by
            simpa using
              basedMapUnderTopBasepoint
                (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p)
  calc
    (H.toHomotopy.curry t).comp (actualFiber p).hom.hom x
        = H (t, (actualFiber p).hom x) := rfl
    _ = H (t, underTopBasepoint (actualFiber p)) := by
      rw [show (actualFiber p).hom x = underTopBasepoint (actualFiber p) by
        change (actualFiber p).hom x =
          (actualFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)
        rw [← hx]
        simp]
    _ = underTopBasepoint (actualFiber p) := hstage
    _ = (actualFiber p).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = (actualFiber p).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
            rw [hx]
    _ = (actualFiber p).hom x := by
          simp

/-- Lemma 8.6.9. If `p : E ⟶ B` is a based fibration, then the inclusion of the actual fiber
`p⁻¹' {underTopBasepoint B}` into the homotopy fiber `homotopyFiber p` is a based homotopy
equivalence; in the `Under (⊤_ TopCat)` model of based spaces, this is
`IsCofiberHomotopyEquivalence (actualFiberToHomotopyFiber p)`. -/
theorem actualFiberToHomotopyFiber_isBasedHomotopyEquivalence
    (p : E ⟶ B) [IsBasedFibration p] :
    IsCofiberHomotopyEquivalence (actualFiberToHomotopyFiber p) := by
  -- Assemble the homotopy inverse from the terminal stage of the lifted contraction.
  rw [isCofiberHomotopyEquivalence_iff]
  refine ⟨homotopyFiberToActualFiber p, ?_, ?_⟩
  · -- Reverse the homotopy-fiber deformation so that it runs from the composite to the identity.
    exact homotopyFiberRetractionHomotopicUnder p
  · -- Reverse the restricted lifted contraction to obtain the actual-fiber retraction homotopy.
    exact actualFiberRetractionHomotopicUnder p

/-- For a based fibration `p`, the inclusion of the actual fiber into the homotopy fiber is a
based homotopy equivalence. -/
instance actualFiberToHomotopyFiber.instIsCofiberHomotopyEquivalence
    (p : E ⟶ B) [IsBasedFibration p] :
    IsCofiberHomotopyEquivalence (actualFiberToHomotopyFiber p) :=
  actualFiberToHomotopyFiber_isBasedHomotopyEquivalence p
