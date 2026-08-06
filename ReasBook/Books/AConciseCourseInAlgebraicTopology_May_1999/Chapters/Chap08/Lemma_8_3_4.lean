import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Corollary_6_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Theorem_6_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open CategoryTheory ConcreteCategory
open scoped unitInterval

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` surfaced only model-category cofibration APIs, so the
-- local pair `IsCofibration` / `IsBasedCofibration` remains the faithful owner here. Because the
-- current Chapter 8 based-cofibration owner uses `Under (⊤_ TopCat)`, while Definition 8.3.3
-- packages well-pointedness for `PointedCompactlyGenerated`, the source side condition is stated
-- here directly as a cofibration condition on the chosen basepoint inclusions in `BasedSpace`.

/-- The inclusion of the chosen basepoint of a based space `X : Under (⊤_ TopCat)` into its
underlying unbased space. -/
abbrev basedSpaceBasepointInclusion (X : BasedSpace) :
    C((⊤_ TopCat), X.right) :=
  hom X.hom

/-- The canonical based map from the terminal based space to `X`. -/
def basedSpaceBasepointMap (X : BasedSpace) : Under.mk (𝟙 (⊤_ TopCat)) ⟶ X :=
  Under.homMk (TopCat.ofHom (basedSpaceBasepointInclusion X)) (by
    rfl)

/-- The canonical based map from the terminal based space to `X` has underlying continuous map
the basepoint inclusion of `X`. -/
@[simp] theorem basedSpaceBasepointMap_hom (X : BasedSpace) :
    (basedSpaceBasepointMap X).right.hom = basedSpaceBasepointInclusion X := by
  rfl

/-- A based space is well pointed when the inclusion of its chosen basepoint into the underlying
unbased space is a cofibration. -/
class WellPointedBasedSpace (X : BasedSpace) : Prop where
  /-- The basepoint inclusion of `X` is a cofibration. -/
  isCofibration : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion X)

/-- The proposition `WellPointedBasedSpace X` is subsingleton. -/
instance wellPointedBasedSpaceSubsingleton (X : BasedSpace) :
    Subsingleton (WellPointedBasedSpace X) :=
  inferInstance

/-- A based space is well pointed exactly when its basepoint inclusion is a cofibration. -/
theorem wellPointedBasedSpace_iff (X : BasedSpace) :
    WellPointedBasedSpace X ↔ IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion X) := by
  constructor
  · intro hX
    exact hX.isCofibration
  · intro hX
    exact ⟨hX⟩

/-- Well pointedness can equivalently be read on the canonical based map from the terminal based
space to `X`. -/
theorem wellPointedBasedSpace_iff_isCofibration_basepointMap (X : BasedSpace) :
    WellPointedBasedSpace X ↔
      IsCofibration.{0, 0, 0} (basedSpaceBasepointMap X).right.hom := by
  simpa [basedSpaceBasepointMap_hom X] using wellPointedBasedSpace_iff X

/-- Helper for Lemma 8.3.4: a based map sends the chosen basepoint of its source to the chosen
basepoint of its target. -/
theorem map_underTopBasepoint {A X : BasedSpace} (i : A ⟶ X) :
    i.right.hom (underTopBasepoint A) = underTopBasepoint X := by
  -- Evaluate the `Under` commutativity condition at the unique point of the terminal object.
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (Under.w i)
  simpa [underTopBasepoint] using hw

/-- Helper for Lemma 8.3.4: a continuous map that carries the chosen basepoint of `Z` to `b`
packages as a based map into `basedSpaceAtPoint S b`. -/
def basedMapOfMapAtBasepoint {Z : BasedSpace} {S : TopCat} (f : C(Z.right, S)) (b : S)
    (hf : f (underTopBasepoint Z) = b) :
    Z ⟶ basedSpaceAtPoint S b :=
  Under.homMk (TopCat.ofHom f) (by
    -- Two terminal-domain maps agree once they agree on the unique point.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun g ↦ g u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    calc
      (Z.hom ≫ TopCat.ofHom f) u = f (Z.hom u) := rfl
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u))) := by
        rw [hu']
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by
        rw [hu]
      _ = b := hf
      _ = (basedSpaceAtPoint S b).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = (basedSpaceAtPoint S b).hom
            (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
            rw [hu]
      _ = (basedSpaceAtPoint S b).hom u := by
            simp)

/-- Helper for Lemma 8.3.4: the underlying map of `basedMapOfMapAtBasepoint` is the original
continuous map. -/
@[simp] theorem basedMapOfMapAtBasepoint_hom {Z : BasedSpace} {S : TopCat}
    (f : C(Z.right, S)) (b : S) (hf : f (underTopBasepoint Z) = b) :
    (basedMapOfMapAtBasepoint f b hf).right.hom = f := by
  rfl

/-- Helper for Lemma 8.3.4: an explicit path family that has prescribed endpoints and is constant
on `basedBasepointSet A` determines a singleton-relative homotopy. -/
def homotopyRelOfPathFamily {A B : BasedSpace} {f₀ f₁ : C(A.right, B.right)}
    (d : C(A.right, C(I, B.right)))
    (h₀ : ∀ a : A.right, d a 0 = f₀ a)
    (h₁ : ∀ a : A.right, d a 1 = f₁ a)
    (hrel : ∀ a : A.right, a ∈ basedBasepointSet A →
      d a = ContinuousMap.const I (f₀ a)) :
    f₀ HRel[A] f₁ := by
  -- Uncurrying the family produces the underlying homotopy.
  refine
    { toHomotopy := ?_
      prop' := ?_ }
  · refine
      { toFun := fun p ↦ d p.2 p.1
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- The compact-open adjunction turns continuity of `d` into continuity of the uncurried map.
      exact
        (ContinuousMap.continuous_uncurry_of_continuous d).comp
          (Homeomorph.prodComm I A.right).continuous_toFun
    · intro a
      simpa using h₀ a
    · intro a
      simpa using h₁ a
  · intro t a ha
    -- On the chosen basepoint subset, the family is literally constant.
    have hconst := hrel a ha
    simp [hconst]

/-- Helper for Lemma 8.3.4: if the terminal-domain basepoint inclusion of `A` is a cofibration,
then the singleton subtype inclusion `basedBasepointSet A ↪ A.right` is also a cofibration. -/
theorem basedBasepointSingletonInclusionIsCofibration {A : BasedSpace}
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A)) :
    IsCofibration.{0, 0, 0} (TopCat.subtypeInclusion (basedBasepointSet A)).hom := by
  intro Y _ f₀ g H
  let base : basedBasepointSet A := ⟨underTopBasepoint A, by simp [basedBasepointSet]⟩
  let j : C((⊤_ TopCat), basedBasepointSet A) := ContinuousMap.const (⊤_ TopCat) base
  have hSubtype :
      (TopCat.subtypeInclusion (basedBasepointSet A)).hom.comp j =
        basedSpaceBasepointInclusion A := by
    -- Both terminal-domain maps pick out the chosen basepoint of `A`.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun f ↦ f u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    calc
      ((TopCat.subtypeInclusion (basedBasepointSet A)).hom.comp j) u
          = ((TopCat.subtypeInclusion (basedBasepointSet A)).hom.comp j)
              (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
                rw [hu', hu]
      _ = underTopBasepoint A := rfl
      _ = (basedSpaceBasepointInclusion A) (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = (basedSpaceBasepointInclusion A) u := by
            rw [hu', hu]
  let HTop : (f₀.comp (basedSpaceBasepointInclusion A)).Homotopy (g.comp j) :=
    (H.compContinuousMap j).cast
      (by
        simpa [ContinuousMap.comp_assoc] using
          congrArg (fun k ↦ f₀.comp k) hSubtype)
      rfl
  -- Extend the singleton-domain homotopy across all of `A`.
  obtain ⟨G, F, hF⟩ := hA.exists_homotopy_extension (f₀ := f₀) (g := g.comp j) HTop
  refine ⟨G, F, ?_⟩
  intro z
  rcases z with ⟨t, a⟩
  have haVal : (a : A.right) = underTopBasepoint A := by
    exact Set.mem_singleton_iff.mp a.2
  have ha : a = base := Subtype.ext haVal
  -- The extension formula on the terminal domain recovers the original singleton-domain value.
  have hAt :
      F (t, underTopBasepoint A) = H (t, base) := by
    simpa [HTop, j, base, basedSpaceBasepointInclusion, underTopBasepoint] using
      hF (t, TopCat.terminalIsoPUnit.inv PUnit.unit)
  calc
    F (t, a) = F (t, underTopBasepoint A) := by rw [haVal]
    _ = H (t, base) := hAt
    _ = H (t, a) := by rw [ha]

/-- Helper for Lemma 8.3.4: the initial and terminal mapping-path sections agree on the singleton
basepoint subset once they agree at the chosen basepoint. -/
theorem sectionEndpointsAgreeOnBasedBasepointSet {A X : BasedSpace} {i : A ⟶ X}
    {Y : Type*} [TopologicalSpace Y] {f₀ : C(X.right, Y)}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAtBase : sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A)) :
    ∀ a : A.right, a ∈ basedBasepointSet A → (sigma0.comp i.right.hom) a = sigmaA a := by
  -- The source-relative subset is a singleton, so every comparison reduces to the chosen
  -- basepoint compatibility.
  intro a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  simpa [map_underTopBasepoint i] using hSigmaAtBase

/-- Helper for Lemma 8.3.4: the source basepoint track determined by a path-space square on `A`
extends across `X` using the cofibration of `basedSpaceBasepointInclusion X`. -/
theorem extendBasepointTrackAcrossX {A X : BasedSpace} {i : A ⟶ X}
    (hX : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion X))
    {Y : Type} [TopologicalSpace Y] {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    (hd : (pathSpaceEvalAtZero Y).comp d = f₀.comp i.right.hom) :
    ∃ D₀ : C(X.right, C(I, Y)),
      D₀.comp (basedSpaceBasepointInclusion X) =
        ContinuousMap.const (⊤_ TopCat) (d (underTopBasepoint A)) ∧
      (pathSpaceEvalAtZero Y).comp D₀ = f₀ := by
  let d₀ : C((⊤_ TopCat), C(I, Y)) :=
    ContinuousMap.const (⊤_ TopCat) (d (underTopBasepoint A))
  have hdBase :
      d (underTopBasepoint A) 0 = f₀ (underTopBasepoint X) := by
    -- Evaluate the original path-space square at the source basepoint.
    simpa [pathSpaceEvalAtZero, map_underTopBasepoint i] using
      ContinuousMap.congr_fun hd (underTopBasepoint A)
  have hd₀ :
      (pathSpaceEvalAtZero Y).comp d₀ = f₀.comp (basedSpaceBasepointInclusion X) := by
    -- The constant basepoint track starts at `f₀ (underTopBasepoint X)`.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
      calc
        u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
          exact (congrArg (fun f ↦ f u) TopCat.terminalIsoPUnit.hom_inv_id).symm
        _ = TopCat.terminalIsoPUnit.inv PUnit.unit := by
          rw [hu]
    calc
      ((pathSpaceEvalAtZero Y).comp d₀) u
          = ((pathSpaceEvalAtZero Y).comp d₀) (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
            rw [hu']
      _ = d (underTopBasepoint A) 0 := by
        rfl
      _ = f₀ (underTopBasepoint X) := hdBase
      _ = (f₀.comp (basedSpaceBasepointInclusion X))
            (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
            rfl
      _ = (f₀.comp (basedSpaceBasepointInclusion X)) u := by
            rw [hu']
  -- Apply the path-space lifting criterion for the target basepoint inclusion.
  exact
    (isCofibration_iff_lift_pathSpaceEvalAtZero (i := basedSpaceBasepointInclusion X)).mp hX
      (Y := Y) f₀ d₀ hd₀

/-- Helper for Lemma 8.3.4: the lifted basepoint track from `extendBasepointTrackAcrossX` takes the
basepoint of `X` to the chosen source track. -/
theorem extendBasepointTrackAcrossX_apply_basepoint {A X : BasedSpace}
    {Y : Type} [TopologicalSpace Y] {d : C(A.right, C(I, Y))} {D₀ : C(X.right, C(I, Y))}
    (hD₀ :
      D₀.comp (basedSpaceBasepointInclusion X) =
        ContinuousMap.const (⊤_ TopCat) (d (underTopBasepoint A))) :
    D₀ (underTopBasepoint X) = d (underTopBasepoint A) := by
  -- Evaluate the terminal-domain equality at the unique point.
  have hEval :=
    congrArg
      (fun k : C((⊤_ TopCat), C(I, Y)) ↦
        k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      hD₀
  simpa [underTopBasepoint, basedSpaceBasepointInclusion] using hEval

/-- Helper for Lemma 8.3.4: scaling the stored path in `MappingPathSpace f` gives an explicit
homotopy from the constant section over the point projection to the identity. -/
abbrev mappingPathSpaceConstantSectionHomotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X] (f : C(X, Y)) :
    ((mappingPathSpaceInclusion f).comp (mappingPathSpacePointProjection f)).Homotopy
      (ContinuousMap.id (MappingPathSpace f)) := by
  let _ : UCompactlyGeneratedSpace (I × MappingPathSpace f) :=
    uCompactlyGeneratedSpaceCompHausProd I (MappingPathSpace f)
  -- Follow each stored path only up to time `t`, so `t = 0` gives the constant section and
  -- `t = 1` recovers the original mapping-path point.
  refine { toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }
  · refine
      ⟨fun tz ↦
        MappingPathSpace.mk tz.2.point
          ⟨fun s ↦ tz.2.path (Set.projIcc 0 1 zero_le_one ((tz.1 : ℝ) * (s : ℝ))), ?_⟩
          ?_,
        ?_⟩
    · -- The scaled path is continuous because multiplication in `I` is continuous.
      refine tz.2.path.continuous.comp ?_
      apply continuous_projIcc.comp
      exact continuous_const.mul continuous_subtype_val
    · -- At time `0`, the scaled path still starts at the original value `f x`.
      simpa [MappingPathSpace.path_zero_eq] using tz.2.path_zero_eq
    · -- Continuity reduces to continuity of the ambient product map into `X × C(I, Y)`.
      have hPoint : Continuous fun tz : I × MappingPathSpace f ↦ tz.2.point := by
        simpa [MappingPathSpace.point] using
          (continuous_fst.comp (MappingPathSpace.continuous_subtypeVal.comp continuous_snd) :
            Continuous fun tz : I × MappingPathSpace f ↦
              ((((tz.2 : MappingPathSpace f) : X × C(I, Y))).1))
      have hScaledPath :
          Continuous fun tz : I × MappingPathSpace f ↦
            (⟨fun s ↦ tz.2.path (Set.projIcc 0 1 zero_le_one ((tz.1 : ℝ) * (s : ℝ))),
              by
                refine tz.2.path.continuous.comp ?_
                apply continuous_projIcc.comp
                exact continuous_const.mul continuous_subtype_val⟩ : C(I, Y)) := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        have hPath : Continuous fun p : (I × MappingPathSpace f) × I ↦ p.1.2.path := by
          simpa [MappingPathSpace.path] using
            (continuous_snd.comp
              (MappingPathSpace.continuous_subtypeVal.comp
                (continuous_snd.comp continuous_fst)) :
              Continuous fun p : (I × MappingPathSpace f) × I ↦
                ((((p.1.2 : MappingPathSpace f) : X × C(I, Y))).2))
        have hScaledArg :
            Continuous fun p : (I × MappingPathSpace f) × I ↦
              Set.projIcc 0 1 zero_le_one ((p.1.1 : ℝ) * (p.2 : ℝ)) := by
          apply continuous_projIcc.comp
          exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
            (continuous_subtype_val.comp continuous_snd)
        exact continuous_eval.comp <|
          hPath.prodMk hScaledArg
      exact MappingPathSpace.continuous_mk hPoint hScaledPath <| by
        -- The defining startpoint condition of `MappingPathSpace f` is preserved throughout the
        -- contraction.
        intro tz
        simpa [MappingPathSpace.path_zero_eq] using tz.2.path_zero_eq
  · intro z
    -- At `t = 0`, every stored path collapses to the constant path at `f z.point`.
    apply MappingPathSpace.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      simp [mappingPathSpaceInclusion, MappingPathSpace.path_zero_eq]
  · intro z
    -- At `t = 1`, scaling by `1` recovers the original stored path.
    apply MappingPathSpace.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      simp

/-- Helper for Lemma 8.3.4: the explicit contraction of mapping-path sections also records the
corresponding homotopy class. -/
theorem mappingPathSpaceConstantSectionHomotopicId
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X] (f : C(X, Y)) :
    ((mappingPathSpaceInclusion f).comp (mappingPathSpacePointProjection f)).Homotopic
      (ContinuousMap.id (MappingPathSpace f)) := by
  exact ⟨mappingPathSpaceConstantSectionHomotopy f⟩

/-- Helper for Lemma 8.3.4: the chosen contraction witness from
`mappingPathSpaceConstantSectionHomotopicId` starts at the constant-section inclusion. -/
@[simp] theorem mappingPathSpaceConstantSectionHomotopicId_some_apply_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X] (f : C(X, Y))
    (z : MappingPathSpace f) :
    mappingPathSpaceConstantSectionHomotopy f (0, z) =
      ((mappingPathSpaceInclusion f).comp (mappingPathSpacePointProjection f)) z := by
  -- This is just the `t = 0` endpoint formula of the explicit contraction.
  exact (mappingPathSpaceConstantSectionHomotopy f).apply_zero z

/-- Helper for Lemma 8.3.4: the chosen contraction witness from
`mappingPathSpaceConstantSectionHomotopicId` ends at the identity map. -/
@[simp] theorem mappingPathSpaceConstantSectionHomotopicId_some_apply_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X] (f : C(X, Y))
    (z : MappingPathSpace f) :
    mappingPathSpaceConstantSectionHomotopy f (1, z) = z := by
  -- This is just the `t = 1` endpoint formula of the explicit contraction.
  exact (mappingPathSpaceConstantSectionHomotopy f).apply_one z

/-- Helper for Lemma 8.3.4: the chosen contraction witness keeps the point projection fixed. -/
@[simp] theorem mappingPathSpaceConstantSectionHomotopicId_some_pointProjection
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X] (f : C(X, Y))
    (tz : I × MappingPathSpace f) :
    mappingPathSpacePointProjection f (mappingPathSpaceConstantSectionHomotopy f tz) =
      mappingPathSpacePointProjection f tz.2 := by
  -- The explicit contraction never changes the stored `X`-coordinate.
  rfl

/-- Helper for Lemma 8.3.4: there is a canonical homotopy from `sigma0.comp i.right.hom` to
`sigmaA` obtained by contracting both sections through the common constant section over
`i.right.hom`. -/
def canonicalSectionHomotopy
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X.right]
    {f₀ : C(X.right, Y)}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom) :
    (sigma0.comp i.right.hom).Homotopy sigmaA :=
  let hConstantSection :
      ((mappingPathSpaceInclusion f₀).comp (mappingPathSpacePointProjection f₀)).Homotopy
        (ContinuousMap.id (MappingPathSpace f₀)) :=
    mappingPathSpaceConstantSectionHomotopy f₀
  let hSigma0Constant :
      ((mappingPathSpaceInclusion f₀).comp (mappingPathSpacePointProjection f₀)).comp
          (sigma0.comp i.right.hom) =
        (mappingPathSpaceInclusion f₀).comp i.right.hom := by
    simpa [ContinuousMap.comp_assoc] using
      congrArg
        (fun k : C(X.right, X.right) ↦
          (mappingPathSpaceInclusion f₀).comp (k.comp i.right.hom))
        hSigma0Proj
  let hSigma0ToConstant :
      (sigma0.comp i.right.hom).Homotopy ((mappingPathSpaceInclusion f₀).comp i.right.hom) := by
    -- Precomposing the canonical contraction with `sigma0 ∘ i` collapses the source section to
    -- the constant section over `i`.
    exact ((hConstantSection.compContinuousMap (sigma0.comp i.right.hom)).symm).cast rfl hSigma0Constant
  let hConstantToSigmaA :
      ((mappingPathSpaceInclusion f₀).comp i.right.hom).Homotopy sigmaA := by
    -- The target section is contracted from the same constant section over `i`.
    exact
      (hConstantSection.compContinuousMap sigmaA).cast
        (by
          simpa [ContinuousMap.comp_assoc] using
            congrArg (fun k : C(A.right, X.right) ↦ (mappingPathSpaceInclusion f₀).comp k)
              hSigmaAProj)
        rfl
  -- Concatenate the two halves to obtain the canonical source homotopy.
  hSigma0ToConstant.trans hConstantToSigmaA

/-- Helper for Lemma 8.3.4: a boundary point that is not on the basepoint strip must lie on the
bottom edge `t = 0`. -/
theorem eq_zero_of_mem_sectionRectificationZeroBoundary_of_not_mem_basepointStrip
    {A : BasedSpace} {z : A.right × I}
    (hz : z ∈ prodPairUnion (basedBasepointSet A) ({0} : Set I))
    (hstrip : z.1 ∉ basedBasepointSet A) :
    z.2 = 0 := by
  -- Membership in the one-sided union forces the time coordinate onto `{0}` off the strip.
  rw [mem_prodPairUnion] at hz
  rcases hz with hz | hz
  · exact (hstrip hz).elim
  · exact Set.mem_singleton_iff.mp hz

/-- Helper for Lemma 8.3.4: the singleton subtype inclusion for `basedBasepointSet A` has image
exactly `basedBasepointSet A`. -/
theorem range_basedBasepointSubtypeInclusion {A : BasedSpace} :
    Set.range (TopCat.subtypeInclusion (basedBasepointSet A)).hom = basedBasepointSet A := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact b.2
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

/-- Helper for Lemma 8.3.4: the canonical terminal-domain basepoint map has image exactly the
chosen basepoint singleton. -/
theorem range_basedSpaceBasepointInclusion (A : BasedSpace) :
    Set.range (basedSpaceBasepointInclusion A) = basedBasepointSet A := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun f ↦ f u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    change (basedSpaceBasepointInclusion A) u = underTopBasepoint A
    calc
      (basedSpaceBasepointInclusion A) u =
          (basedSpaceBasepointInclusion A)
            (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
              rw [hu']
      _ = (basedSpaceBasepointInclusion A) (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
            rw [hu]
      _ = underTopBasepoint A := rfl
  · intro ha
    refine ⟨TopCat.terminalIsoPUnit.inv PUnit.unit, ?_⟩
    simpa [basedBasepointSet, basedSpaceBasepointInclusion, underTopBasepoint] using ha.symm

/-- Helper for Lemma 8.3.4: the chosen basepoint subset is the closed image of the terminal-domain
basepoint inclusion whenever that inclusion is a cofibration. -/
theorem basedBasepointSetIsClosed (A : BasedSpace)
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A)) :
    IsClosed (basedBasepointSet A) := by
  -- Route correction: the basepoint subset is still definitionally a singleton, but this file does
  -- not have a `T1Space` instance for `A.right`. The remaining local route is therefore the closed
  -- range consequence of `hA`, using `range_basedSpaceBasepointInclusion A`.
  -- TODO: reintroduce the Chapter 6 closed-range cofibration consequence theorem-locally, then
  -- rewrite the resulting closed image by `range_basedSpaceBasepointInclusion A`.
  sorry

/-- Helper for Lemma 8.3.4: if the terminal-domain basepoint inclusion of `A` is a cofibration,
then the one-sided cylinder base
`prodPairUnion (basedBasepointSet A) ({0} : Set I) ⊆ A.right × I` is already a DR-pair. -/
theorem basepointCylinderBaseIsDRPair (A : BasedSpace)
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A)) :
    IsDRPair (prodPairUnion (basedBasepointSet A) ({0} : Set I)) := by
  -- Route correction: once the singleton basepoint subset is known to be closed, the Chapter 6
  -- NDR/cofibration equivalence applies directly to its subtype inclusion.
  have hClosed : IsClosed (basedBasepointSet A) :=
    basedBasepointSetIsClosed A hA
  have hSingletonCofibration :
      IsCofibration (TopCat.subtypeInclusion (basedBasepointSet A)).hom :=
    basedBasepointSingletonInclusionIsCofibration hA
  have hSingletonNDR : IsNDRPair (basedBasepointSet A) :=
    (isNDRPair_iff_isCofibration_subtypeVal
      (X := A.right)
      (A := basedBasepointSet A)
      hClosed).2 hSingletonCofibration
  -- The product-with-`{0}` comparison from Chapter 6 turns that NDR data into the desired
  -- cylinder-base DR witness.
  exact
    (isNDRPair_iff_cylinderBaseUnion_isDRPair
      (X := A.right)
      (A := basedBasepointSet A)).1 hSingletonNDR

/-- Helper for Lemma 8.3.4: the one-sided product boundary
`prodPairUnion (basedBasepointSet A) ({0} : Set I)` is a cofibration in `A.right × I`. -/
theorem sectionRectificationZeroBoundaryIsCofibration {A : BasedSpace}
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A)) :
    IsCofibration.{0, 0, 0}
      (TopCat.subtypeInclusion (prodPairUnion (basedBasepointSet A) ({0} : Set I))).hom := by
  -- Route correction: read the zero-boundary cofibration directly from the stronger local
  -- cylinder-base DR witness.
  let U : Set (A.right × I) :=
    prodPairUnion (basedBasepointSet A) ({0} : Set I)
  let hZeroBoundaryDR : IsDRPair U :=
    basepointCylinderBaseIsDRPair A hA
  let hZeroBoundaryNDR : IsNDRPair U :=
    isNDRPair_of_isDRPair hZeroBoundaryDR
  let hZeroBoundaryClosed : IsClosed U :=
    hZeroBoundaryNDR.isClosed
  -- Convert the DR witness back to an NDR pair, then read off the desired subtype cofibration.
  have hZeroBoundaryCofibration :
      IsCofibration.{0, 0, 0}
        (TopCat.subtypeInclusion (X := A.right × I) U).hom :=
    (isNDRPair_iff_isCofibration_subtypeVal
      (X := A.right × I)
      (A := U)
      hZeroBoundaryClosed).1 hZeroBoundaryNDR
  change
    IsCofibration.{0, 0, 0}
      (TopCat.subtypeInclusion
        (X := A.right × I)
        (prodPairUnion (basedBasepointSet A) ({0} : Set I))).hom
  exact hZeroBoundaryCofibration

/-- Helper for Lemma 8.3.4: the diagonal family recorded by `sigmaA` starts at `f₀ ∘ i`. -/
theorem sectionDiagonalStartsAtSource
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1) :
    ∀ a : A.right, d a 0 = f₀ (i.right.hom a) := by
  -- Evaluating the stored path at `0` uses the defining source-point condition of
  -- `MappingPathSpace f₀`.
  intro a
  have hPoint : (sigmaA a).point = i.right.hom a := by
    simpa using congrArg (fun k : C(A.right, X.right) ↦ k a) hSigmaAProj
  calc
    d a 0 = (sigmaA a).path 0 := by
      symm
      exact hSigmaADiag (0, a)
    _ = f₀ ((sigmaA a).point) := (sigmaA a).path_zero_eq
    _ = f₀ (i.right.hom a) := by rw [hPoint]

/-- Helper for Lemma 8.3.4: on the zero boundary away from the singleton strip, the diagonal
condition recorded by `sigmaA` collapses to the source endpoint equation because the time
coordinate is forced to be `0`. -/
theorem sectionDiagonalOnZeroBoundaryOffStrip
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1)
    {z : A.right × I}
    (hz : z ∈ prodPairUnion (basedBasepointSet A) ({0} : Set I))
    (hstrip : z.1 ∉ basedBasepointSet A) :
    d z.1 z.2 = f₀ (i.right.hom z.1) := by
  -- Off the singleton strip, boundary membership forces the time coordinate to be `0`.
  have hzZero :
      z.2 = 0 :=
    eq_zero_of_mem_sectionRectificationZeroBoundary_of_not_mem_basepointStrip hz hstrip
  have hStart :
      ∀ a : A.right, d a 0 = f₀ (i.right.hom a) :=
    sectionDiagonalStartsAtSource (i := i) (sigmaA := sigmaA) hSigmaAProj hSigmaADiag
  -- Rewriting the forced boundary time to `0` reduces to the already isolated source-start
  -- equation.
  calc
    d z.1 z.2 = d z.1 0 := by rw [hzZero]
    _ = f₀ (i.right.hom z.1) := hStart z.1

/-- Helper for Lemma 8.3.4: the bottom-edge value built from `sigma0 ∘ i` satisfies the
projection, diagonal, and terminal conditions required by the rectification subtype. -/
theorem rectificationBottomPointSpec
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hDiagZero : ∀ a : A.right, d a 0 = f₀ (i.right.hom a))
    (a : A.right) :
    mappingPathSpacePointProjection f₀ (sigma0 (i.right.hom a)) = i.right.hom a ∧
      (sigma0 (i.right.hom a)).path 0 = d a 0 ∧
      (0 = (1 : I) → sigma0 (i.right.hom a) = sigmaA a) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The bottom-edge point projection is fixed by the section identity for `sigma0`.
    simpa [ContinuousMap.comp_apply] using
      congrArg (fun k : C(X.right, X.right) ↦ k (i.right.hom a)) hSigma0Proj
  · -- At time `0`, the stored path starts at `f₀ (i a)`, matching the source diagonal value.
    have hPoint :
        mappingPathSpacePointProjection f₀ (sigma0 (i.right.hom a)) = i.right.hom a := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun k : C(X.right, X.right) ↦ k (i.right.hom a)) hSigma0Proj
    calc
      (sigma0 (i.right.hom a)).path 0 = f₀ ((sigma0 (i.right.hom a)).point) := by
        exact (sigma0 (i.right.hom a)).path_zero_eq
      _ = f₀ (i.right.hom a) := by simpa using congrArg f₀ hPoint
      _ = d a 0 := (hDiagZero a).symm
  · -- The endpoint condition is vacuous on the bottom edge because the stored time is `0`.
    intro hOne
    exact (zero_ne_one hOne).elim

/-- Helper for Lemma 8.3.4: on the overlap `basedBasepointSet A × {0}`, the top boundary value
already satisfies the bottom-edge equations and agrees with `sigma0 ∘ i`. -/
theorem rectificationBoundaryOverlapPointSpec
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAtBase : sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A))
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1) :
    ∀ a : A.right, a ∈ basedBasepointSet A →
      mappingPathSpacePointProjection f₀ (sigmaA a) = i.right.hom a ∧
        (sigmaA a).path 0 = d a 0 ∧
          sigmaA a = sigma0 (i.right.hom a) := by
  intro a ha
  -- Package the overlap data once so the later boundary gluing step can consume a single API.
  have hProj :
      mappingPathSpacePointProjection f₀ (sigmaA a) = i.right.hom a := by
    simpa [ContinuousMap.comp_apply] using
      congrArg (fun k : C(A.right, X.right) ↦ k a) hSigmaAProj
  have hDiag :
      (sigmaA a).path 0 = d a 0 := by
    simpa using hSigmaADiag (0, a)
  have hAgree :
      sigmaA a = sigma0 (i.right.hom a) := by
    symm
    exact sectionEndpointsAgreeOnBasedBasepointSet (i := i) hSigmaAtBase a ha
  exact ⟨hProj, hDiag, hAgree⟩

/-- Helper for Lemma 8.3.4: on the overlap `basedBasepointSet A × {0}`, the raw ambient
boundary values coming from the top and bottom branches already agree. -/
theorem rectificationBoundaryOverlapValueEq
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAtBase : sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A))
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1)
    {a : A.right} (ha : a ∈ basedBasepointSet A) :
    ((a, (0 : I)), sigmaA a) = ((a, (0 : I)), sigma0 (i.right.hom a)) := by
  -- Package the overlap equality at the ambient-product level so the later boundary gluing step
  -- can use a single `Subtype.ext` rewrite instead of redoing the pointwise comparison.
  have hOverlap :=
    rectificationBoundaryOverlapPointSpec
      (i := i) (f₀ := f₀) (d := d) (sigma0 := sigma0) (sigmaA := sigmaA)
      hSigmaAtBase hSigmaAProj hSigmaADiag a ha
  exact Prod.ext rfl hOverlap.2.2

/-- Helper for Lemma 8.3.4: the canonical comparison homotopy keeps the point projection fixed at
`i`. -/
theorem canonicalSectionHomotopyPointProjection
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X.right]
    {f₀ : C(X.right, Y)}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom) :
    ∀ z : I × A.right,
      mappingPathSpacePointProjection f₀
        (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
          hSigma0Proj hSigmaAProj z) = i.right.hom z.2 := by
  -- Route correction: instead of simplifying the whole concatenation at once, first normalize the
  -- left and right branches of the canonical homotopy separately.
  let hConstantSection :
      ((mappingPathSpaceInclusion f₀).comp (mappingPathSpacePointProjection f₀)).Homotopy
        (ContinuousMap.id (MappingPathSpace f₀)) :=
    mappingPathSpaceConstantSectionHomotopy f₀
  let hSigma0Constant :
      ((mappingPathSpaceInclusion f₀).comp (mappingPathSpacePointProjection f₀)).comp
          (sigma0.comp i.right.hom) =
        (mappingPathSpaceInclusion f₀).comp i.right.hom := by
    simpa [ContinuousMap.comp_assoc] using
      congrArg
        (fun k : C(X.right, X.right) ↦
          (mappingPathSpaceInclusion f₀).comp (k.comp i.right.hom))
        hSigma0Proj
  let hSigma0ToConstant :
      (sigma0.comp i.right.hom).Homotopy ((mappingPathSpaceInclusion f₀).comp i.right.hom) := by
    -- The source section contracts to the constant section over `i`.
    exact ((hConstantSection.compContinuousMap (sigma0.comp i.right.hom)).symm).cast
      rfl hSigma0Constant
  let hConstantToSigmaA :
      ((mappingPathSpaceInclusion f₀).comp i.right.hom).Homotopy sigmaA := by
    -- The target section expands from the same constant section over `i`.
    exact
      (hConstantSection.compContinuousMap sigmaA).cast
        (by
          simpa [ContinuousMap.comp_assoc] using
            congrArg (fun k : C(A.right, X.right) ↦ (mappingPathSpaceInclusion f₀).comp k)
              hSigmaAProj)
        rfl
  have hLeftBranch :
      ∀ z : I × A.right,
        mappingPathSpacePointProjection f₀ (hSigma0ToConstant z) = i.right.hom z.2 := by
    intro z
    -- The cast does not change the value, and the contraction keeps the point projection fixed.
    have hSigma0Point :
        mappingPathSpacePointProjection f₀ ((sigma0.comp i.right.hom) z.2) = i.right.hom z.2 := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun k : C(X.right, X.right) ↦ k (i.right.hom z.2)) hSigma0Proj
    change
      mappingPathSpacePointProjection f₀
        (((hConstantSection.compContinuousMap (sigma0.comp i.right.hom)).symm) z) =
        i.right.hom z.2
    rw [show ((hConstantSection.compContinuousMap (sigma0.comp i.right.hom)).symm) z =
        (hConstantSection.compContinuousMap (sigma0.comp i.right.hom)) (σ z.1, z.2) by
          rfl]
    calc
      mappingPathSpacePointProjection f₀
          ((hConstantSection.compContinuousMap (sigma0.comp i.right.hom)) (σ z.1, z.2))
          =
          mappingPathSpacePointProjection f₀ ((sigma0.comp i.right.hom) z.2) := by
            simpa [hConstantSection, ContinuousMap.comp_apply] using
              mappingPathSpaceConstantSectionHomotopicId_some_pointProjection f₀
                (σ z.1, (sigma0.comp i.right.hom) z.2)
      _ = i.right.hom z.2 := hSigma0Point
  have hRightBranch :
      ∀ z : I × A.right,
        mappingPathSpacePointProjection f₀ (hConstantToSigmaA z) = i.right.hom z.2 := by
    intro z
    -- The right branch is just the same contraction precomposed with `sigmaA`.
    have hSigmaAPoint :
        mappingPathSpacePointProjection f₀ (sigmaA z.2) = i.right.hom z.2 := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun k : C(A.right, X.right) ↦ k z.2) hSigmaAProj
    have hRaw :
        mappingPathSpacePointProjection f₀ ((hConstantSection.compContinuousMap sigmaA) z) =
          i.right.hom z.2 := by
      calc
        mappingPathSpacePointProjection f₀ ((hConstantSection.compContinuousMap sigmaA) z)
            = mappingPathSpacePointProjection f₀ (sigmaA z.2) := by
                simpa [hConstantSection, ContinuousMap.comp_apply] using
                  mappingPathSpaceConstantSectionHomotopicId_some_pointProjection f₀
                    (z.1, sigmaA z.2)
        _ = i.right.hom z.2 := hSigmaAPoint
    simpa [hConstantToSigmaA] using hRaw
  intro z
  -- The concatenation puts the normalized left branch on `[0, 1/2]` and the normalized right
  -- branch on `[1/2, 1]`.
  rw [show canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
      hSigma0Proj hSigmaAProj = hSigma0ToConstant.trans hConstantToSigmaA by
        rfl]
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hz
  · exact hLeftBranch _
  · exact hRightBranch _

/-- Helper for Lemma 8.3.4: the canonical section homotopy also preserves the `t = 0` diagonal
condition needed for the bottom-edge rectification subtype. -/
theorem canonicalSectionHomotopyPathZero
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X.right]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1) :
    ∀ z : I × A.right,
      (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
        hSigma0Proj hSigmaAProj z).path 0 = d z.2 0 := by
  -- Reading the path at `0` reduces to the already-controlled point projection of the canonical
  -- homotopy together with the source-side diagonal identity at time `0`.
  intro z
  have hPoint :
      mappingPathSpacePointProjection f₀
        (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
          hSigma0Proj hSigmaAProj z) = i.right.hom z.2 :=
    canonicalSectionHomotopyPointProjection
      (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
      hSigma0Proj hSigmaAProj z
  have hDiagZero :
      d z.2 0 = f₀ (i.right.hom z.2) :=
    sectionDiagonalStartsAtSource
      (i := i) (d := d) (sigmaA := sigmaA) hSigmaAProj hSigmaADiag z.2
  calc
    (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
          hSigma0Proj hSigmaAProj z).path 0
        =
          f₀
            ((canonicalSectionHomotopy
              (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
              hSigma0Proj hSigmaAProj z).point) := by
                exact
                  (canonicalSectionHomotopy
                    (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
                    hSigma0Proj hSigmaAProj z).path_zero_eq
    _ = f₀ (i.right.hom z.2) := by
      simpa using congrArg f₀ hPoint
    _ = d z.2 0 := hDiagZero.symm

/-- Helper for Lemma 8.3.4: every point of the canonical comparison homotopy already satisfies
the bottom-edge projection, diagonal, and terminal conditions used in the rectification subtype. -/
theorem canonicalSectionHomotopyBottomPointSpec
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace X.right]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1)
    (z : I × A.right) :
    mappingPathSpacePointProjection f₀
        (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
          hSigma0Proj hSigmaAProj z) = i.right.hom z.2 ∧
      (canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
          hSigma0Proj hSigmaAProj z).path 0 = d z.2 0 ∧
        (0 = (1 : I) →
          canonicalSectionHomotopy (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
            hSigma0Proj hSigmaAProj z = sigmaA z.2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The canonical homotopy keeps the point projection fixed at `i`.
    exact canonicalSectionHomotopyPointProjection
      (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
      hSigma0Proj hSigmaAProj z
  · -- Reading the stored path at `0` recovers the source diagonal value.
    exact canonicalSectionHomotopyPathZero
      (i := i) (f₀ := f₀) (d := d) (sigma0 := sigma0) (sigmaA := sigmaA)
      hSigma0Proj hSigmaAProj hSigmaADiag z
  · -- The terminal condition is vacuous on the bottom edge because the ambient time is fixed at `0`.
    intro hZeroOne
    exact (zero_ne_one hZeroOne).elim

/-- Helper for Lemma 8.3.4: the constant-in-time family `(a, t) ↦ sigmaA a` already lands in the
fixed-coordinate rectification subtype used by the final extension step. -/
theorem existsRectificationTopSection
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1) :
    let RectPoint :=
      { q : (A.right × I) × MappingPathSpace f₀ //
          mappingPathSpacePointProjection f₀ q.2 = i.right.hom q.1.1 ∧
            q.2.path q.1.2 = d q.1.1 q.1.2 ∧
            (q.1.2 = 1 → q.2 = sigmaA q.1.1) }
    ∃ uTop : C(A.right × I, RectPoint),
      ∀ z : A.right × I, ((uTop z).1).2 = sigmaA z.1 := by
  -- Keep the ambient coordinates fixed and attach the already-constructed section `sigmaA`.
  dsimp
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun z ↦ ⟨(z, sigmaA z.1), ?_⟩
        continuous_toFun := ?_ }
    · -- The three rectification constraints come directly from the defining formulas for `sigmaA`.
      refine ⟨?_, ?_, ?_⟩
      · simpa [ContinuousMap.comp_apply] using
          congrArg (fun k : C(A.right, X.right) ↦ k z.1) hSigmaAProj
      · simpa using hSigmaADiag (z.2, z.1)
      · intro _
        rfl
    · -- Continuity is just continuity of the identity on `A.right × I` paired with `sigmaA`.
      exact
        (continuous_id.prodMk (sigmaA.continuous.comp continuous_fst)).subtype_mk
          (fun z ↦ by
            refine ⟨?_, ?_, ?_⟩
            · simpa [ContinuousMap.comp_apply] using
                congrArg (fun k : C(A.right, X.right) ↦ k z.1) hSigmaAProj
            · simpa using hSigmaADiag (z.2, z.1)
            · intro _
              rfl)
  · intro z
    rfl

/-- Helper for Lemma 8.3.4: the bottom-edge family `a ↦ sigma0 (i a)` also lands in the fixed
coordinate rectification subtype at time `0`. -/
theorem existsRectificationBottomSection
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1) :
    let RectPoint :=
      { q : (A.right × I) × MappingPathSpace f₀ //
          mappingPathSpacePointProjection f₀ q.2 = i.right.hom q.1.1 ∧
            q.2.path q.1.2 = d q.1.1 q.1.2 ∧
            (q.1.2 = 1 → q.2 = sigmaA q.1.1) }
    ∃ uBottom : C(A.right, RectPoint),
      ∀ a : A.right, ((uBottom a).1).2 = sigma0 (i.right.hom a) := by
  let hDiagZero :
      ∀ a : A.right, d a 0 = f₀ (i.right.hom a) :=
    sectionDiagonalStartsAtSource (i := i) (d := d) (sigmaA := sigmaA) hSigmaAProj hSigmaADiag
  dsimp
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun a ↦ ⟨(((a, 0), sigma0 (i.right.hom a))), ?_⟩
        continuous_toFun := ?_ }
    · -- The bottom-edge point already satisfies the projection and diagonal equations at time `0`.
      exact rectificationBottomPointSpec
        (i := i) (f₀ := f₀) (d := d) (sigma0 := sigma0) (sigmaA := sigmaA)
        hSigma0Proj hDiagZero a
    · -- Continuity is just continuity of the source coordinate paired with the bottom section.
      exact
        ((continuous_id.prodMk continuous_const).prodMk
          (sigma0.continuous.comp i.right.hom.continuous)).subtype_mk
          (fun a ↦ by
            exact rectificationBottomPointSpec
              (i := i) (f₀ := f₀) (d := d) (sigma0 := sigma0) (sigmaA := sigmaA)
              hSigma0Proj hDiagZero a)
  · intro a
    rfl

/-- Helper for Lemma 8.3.4: once the source mapping-path sections are connected by a
singleton-relative homotopy, the based cofibration of `i` extends that section homotopy from `A`
to `X`. -/
theorem existsExtendedMappingPathSection
    {A X : BasedSpace.{u}} {i : A ⟶ X}
    {Y : Type u} [TopologicalSpace Y] {f₀ : C(X.right, Y)}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hi : IsBasedCofibration i)
    (hSigmaAtBase : sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A))
    (hSectionRel : (sigma0.comp i.right.hom) HRel[A] sigmaA) :
    ∃ Sigma : C(X.right, MappingPathSpace f₀),
      ∃ Fsec : sigma0 HRel[X] Sigma,
        Sigma.comp i.right.hom = sigmaA ∧
          ∀ z : I × A.right, Fsec (z.1, i.right.hom z.2) = hSectionRel z := by
  let b : MappingPathSpace f₀ := sigmaA (underTopBasepoint A)
  have hSigma0Base : sigma0 (underTopBasepoint X) = b := by
    simpa [b] using hSigmaAtBase
  let sigma0Based : X ⟶ basedSpaceAtPoint (TopCat.of (MappingPathSpace f₀)) b :=
    basedMapOfMapAtBasepoint (S := TopCat.of (MappingPathSpace f₀)) sigma0 b hSigma0Base
  let sigmaABased : A ⟶ basedSpaceAtPoint (TopCat.of (MappingPathSpace f₀)) b :=
    basedMapOfMapAtBasepoint (S := TopCat.of (MappingPathSpace f₀)) sigmaA b (by simp [b])
  -- Apply the based homotopy extension property in the mapping-path-space codomain.
  obtain ⟨SigmaBased, FsecBased, hFsecBased⟩ :=
    hi.exists_homotopy_extension sigma0Based sigmaABased hSectionRel
  let Sigma : C(X.right, MappingPathSpace f₀) := SigmaBased.right.hom
  let Fsec : sigma0 HRel[X] Sigma := by
    simpa [Sigma, sigma0Based] using FsecBased
  have hSigmaComp : Sigma.comp i.right.hom = sigmaA := by
    -- Reading the extension formula at time `1` identifies the endpoint section on `A`.
    apply ContinuousMap.ext
    intro a
    have hAt : FsecBased (1, i.right.hom a) = sigmaA a := by
      have hSectionEnd : hSectionRel (1, a) = sigmaA a := by
        simpa using hSectionRel.apply_one a
      exact (hFsecBased (1, a)).trans hSectionEnd
    simpa [Sigma] using (FsecBased.apply_one (i.right.hom a)).symm.trans hAt
  refine ⟨Sigma, Fsec, hSigmaComp, ?_⟩
  -- The pointwise compatibility formula is the one returned by `hi`.
  intro z
  simpa [Fsec, Sigma, sigma0Based, sigmaABased] using hFsecBased z

/-- Helper for Lemma 8.3.4: evaluating the stored path coordinate along an extended homotopy in
`MappingPathSpace f₀` assembles an ordinary path-space lift once the source diagonal is known. -/
theorem assembleDiagonalFromSectionHomotopy
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] {i : C(A, X)} {f₀ : C(X, Y)}
    {sigma0 Sigma : C(X, MappingPathSpace f₀)}
    (F : sigma0.Homotopy Sigma)
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X)
    {d : C(A, C(I, Y))} {Dsec : C(A, C(I, MappingPathSpace f₀))}
    (hFOnA : ∀ z : I × A, F (z.1, i z.2) = Dsec z.2 z.1)
    (hDiag : ∀ z : I × A, (Dsec z.2 z.1).path z.1 = d z.2 z.1) :
    ∃ D : C(X, C(I, Y)),
      D.comp i = d ∧
        (pathSpaceEvalAtZero Y).comp D = f₀ := by
  -- Build the diagonal map `(x, t) ↦ (F (t, x)).path t` before currying back to `X → Path(Y)`.
  have hFswap : Continuous fun xt : X × I ↦ F (xt.2, xt.1) := by
    exact F.continuous.comp (Homeomorph.prodComm X I).continuous_toFun
  have hPath : Continuous fun xt : X × I ↦ (F (xt.2, xt.1)).path := by
    simpa [MappingPathSpace.path] using
      (continuous_snd.comp (MappingPathSpace.continuous_subtypeVal.comp hFswap) :
        Continuous fun xt : X × I ↦
          ((((F (xt.2, xt.1) : MappingPathSpace f₀) : X × C(I, Y))).2))
  have hDiagContinuous : Continuous fun xt : X × I ↦ (F (xt.2, xt.1)).path xt.2 := by
    exact continuous_eval.comp (hPath.prodMk continuous_snd)
  let diagonal : C(X × I, Y) :=
    ⟨fun xt ↦ (F (xt.2, xt.1)).path xt.2, hDiagContinuous⟩
  let D : C(X, C(I, Y)) := ContinuousMap.curry diagonal
  refine ⟨D, ?_, ?_⟩
  · -- On `A`, the extended homotopy matches the prescribed source square, so the diagonal recovers
    -- the original source family `d`.
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro t
    have hAt : F (t, i a) = Dsec a t := hFOnA (t, a)
    change (F (t, i a)).path t = d a t
    rw [hAt]
    exact hDiag (t, a)
  · -- At time `0`, the homotopy starts at `sigma0`, whose point projection is the identity on
    -- `X`; this forces the diagonal to start at `f₀`.
    apply ContinuousMap.ext
    intro x
    have hStart :
        (F (0, x)).path 0 = f₀ x := by
      rw [F.apply_zero x]
      have hProj := congrArg (fun k : C(X, X) ↦ k x) hSigma0Proj
      calc
        (sigma0 x).path 0 = f₀ (sigma0 x).point := (sigma0 x).path_zero_eq
        _ = f₀ x := by simpa using congrArg f₀ hProj
    simpa [D, diagonal, ContinuousMap.curry_apply, pathSpaceEvalAtZero] using hStart

/-- Helper for Lemma 8.3.4: once the source basepoint inclusion is identified with the singleton
subtype inclusion, the remaining source-side task is to rectify the ordinary section homotopy into
an admissible singleton-relative square. -/
theorem existsRectifiedSectionSquare
    {A X : BasedSpace} {i : A ⟶ X} {Y : Type*} [TopologicalSpace Y]
    {f₀ : C(X.right, Y)} {d : C(A.right, C(I, Y))}
    {sigma0 : C(X.right, MappingPathSpace f₀)}
    {sigmaA : C(A.right, MappingPathSpace f₀)}
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A))
    (hSigmaAtBase : sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A))
    (hSigma0Proj : (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right)
    (hSigmaAProj : (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom)
    (hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1)
    :
    ∃ Dsec : C(A.right, C(I, MappingPathSpace f₀)),
      (pathSpaceEvalAt 0 (MappingPathSpace f₀)).comp Dsec = sigma0.comp i.right.hom ∧
        (pathSpaceEvalAt 1 (MappingPathSpace f₀)).comp Dsec = sigmaA ∧
          (∀ a : A.right, a ∈ basedBasepointSet A →
            Dsec a = ContinuousMap.const I ((sigma0.comp i.right.hom) a)) ∧
            (∀ z : I × A.right,
              mappingPathSpacePointProjection f₀ (Dsec z.2 z.1) = i.right.hom z.2) ∧
              (∀ z : I × A.right, (Dsec z.2 z.1).path z.1 = d z.2 z.1) := by
  have hSectionAgree :
      ∀ a : A.right, a ∈ basedBasepointSet A → (sigma0.comp i.right.hom) a = sigmaA a := by
    exact sectionEndpointsAgreeOnBasedBasepointSet (i := i) hSigmaAtBase
  let U : Set (A.right × I) :=
    prodPairUnion (basedBasepointSet A) ({0} : Set I)
  let RectPoint :=
    { q : (A.right × I) × MappingPathSpace f₀ //
        mappingPathSpacePointProjection f₀ q.2 = i.right.hom q.1.1 ∧
          q.2.path q.1.2 = d q.1.1 q.1.2 ∧
          (q.1.2 = 1 → q.2 = sigmaA q.1.1) }
  obtain ⟨uTop, huTop⟩ :=
    existsRectificationTopSection (i := i) (d := d) (sigmaA := sigmaA)
      hSigmaAProj hSigmaADiag
  let zeroBoundaryPoint : A.right → U := fun a ↦ ⟨(a, 0), by
    simpa [U, mem_prodPairUnion]⟩
  let stripBoundaryPoint : ∀ (z : I × A.right), z.2 ∈ basedBasepointSet A → U :=
    fun z hz ↦ ⟨(z.2, z.1), by
      simpa [U, mem_prodPairUnion] using Or.inl hz⟩
  -- Route correction: the rest of the proof is now isolated to one boundary package on
  -- `U = basedBasepointSet A × I ∪ A.right × {0}`. Once that package supplies a bottom endpoint
  -- map in `RectPoint` and a homotopy from the top strip `uTop`, the zero-boundary cofibration
  -- extends it over `A.right × I`, and currying the second coordinate gives the required `Dsec`.
  -- TODO: construct the boundary endpoint map/homotopy on `U` and apply
  -- `sectionRectificationZeroBoundaryIsCofibration hA` exactly as outlined above.
  clear zeroBoundaryPoint stripBoundaryPoint RectPoint uTop huTop hSectionAgree
  sorry

/-- Lemma 8.3.4. If `A` and `X` are nondegenerately based, formalized here by requiring the
basepoint inclusions `basedSpaceBasepointInclusion A` and `basedSpaceBasepointInclusion X` to be
unbased cofibrations, then a based cofibration `i : A ⟶ X` is also an unbased cofibration. -/
theorem IsBasedCofibration.isCofibration_of_wellPointed {A X : BasedSpace} {i : A ⟶ X}
    [CompactlyGeneratedWeakHausdorffSpace.{0, 0} A.right]
    [CompactlyGeneratedWeakHausdorffSpace.{0, 0} X.right]
    (hA : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion A))
    (hX : IsCofibration.{0, 0, 0} (basedSpaceBasepointInclusion X))
    (hi : IsBasedCofibration i) :
    IsCofibration.{0, 0, 0} i.right.hom := by
  -- Switch to the Chapter 6 path-space lifting criterion for the underlying map of `i`.
  refine (isCofibration_iff_lift_pathSpaceEvalAtZero).2 ?_
  intro Y _ f₀ d hd
  let _ : UCompactlyGeneratedSpace.{0} X.right :=
    (inferInstance : CompactlyGeneratedWeakHausdorffSpace X.right).toUCompactlyGeneratedSpace
  let _ : UCompactlyGeneratedSpace.{0} A.right :=
    (inferInstance : CompactlyGeneratedWeakHausdorffSpace A.right).toUCompactlyGeneratedSpace
  -- First extend the source basepoint track across `X` while keeping the `t = 0` endpoint fixed.
  obtain ⟨D₀, hD₀base, hD₀zero⟩ := extendBasepointTrackAcrossX (i := i) hX hd
  have hD₀AtBase :
      D₀ (underTopBasepoint X) = d (underTopBasepoint A) :=
    extendBasepointTrackAcrossX_apply_basepoint (d := d) hD₀base
  let dX : C(A.right, C(I, Y)) := D₀.comp i.right.hom
  have hdXBase :
      dX (underTopBasepoint A) = d (underTopBasepoint A) := by
    -- The lifted track on `X` restricts to the original source track at the chosen basepoint.
    dsimp [dX]
    rw [map_underTopBasepoint i, hD₀AtBase]
  have hdXZero : (pathSpaceEvalAt 0 Y).comp dX = f₀.comp i.right.hom := by
    -- Restrict the `t = 0` endpoint equation for `D₀` along `i`.
    simpa [dX, ContinuousMap.comp_assoc] using
      congrArg (fun k : C(X.right, Y) ↦ k.comp i.right.hom) hD₀zero
  let sigma0 : C(X.right, MappingPathSpace f₀) :=
    { toFun := fun x ↦ MappingPathSpace.mk x (D₀ x) (by
        simpa [pathSpaceEvalAtZero] using ContinuousMap.congr_fun hD₀zero x)
      continuous_toFun := by
        -- Package the lifted `X`-family of paths together with its point coordinate.
        have hmem :
            ∀ x : X.right, D₀ x 0 = f₀ x := by
          intro x
          simpa [pathSpaceEvalAtZero] using ContinuousMap.congr_fun hD₀zero x
        exact MappingPathSpace.continuous_mk continuous_id D₀.continuous hmem }
  let sigmaA : C(A.right, MappingPathSpace f₀) :=
    { toFun := fun a ↦ MappingPathSpace.mk (i.right.hom a) (d a) (by
        simpa [pathSpaceEvalAtZero] using ContinuousMap.congr_fun hd a)
      continuous_toFun := by
        -- The original source family gives the corresponding section of `MappingPathSpace f₀`.
        have hmem :
            ∀ a : A.right, d a 0 = f₀ (i.right.hom a) := by
          intro a
          simpa [pathSpaceEvalAtZero] using ContinuousMap.congr_fun hd a
        exact MappingPathSpace.continuous_mk i.right.hom.continuous d.continuous hmem }
  have hSigmaAtBase :
      sigma0 (underTopBasepoint X) = sigmaA (underTopBasepoint A) := by
    -- Both mapping-path sections are built from the same source path at the chosen basepoint.
    refine MappingPathSpace.ext ?_ ?_
    · simpa [sigma0, sigmaA, map_underTopBasepoint i]
    · simpa [sigma0, sigmaA, hD₀AtBase]
  have hSigma0Proj :
      (mappingPathSpacePointProjection f₀).comp sigma0 = ContinuousMap.id X.right := by
    -- The section `sigma0` was built with point coordinate `x`.
    ext x
    rfl
  have hSigmaAProj :
      (mappingPathSpacePointProjection f₀).comp sigmaA = i.right.hom := by
    -- The section `sigmaA` was built with point coordinate `i a`.
    ext a
    rfl
  have hSigmaADiag : ∀ z : I × A.right, (sigmaA z.2).path z.1 = d z.2 z.1 := by
    -- The source section `sigmaA` was built from the original path family `d`.
    intro z
    rfl
  have hRectified :
      ∃ Dsec : C(A.right, C(I, MappingPathSpace f₀)),
        (pathSpaceEvalAt 0 (MappingPathSpace f₀)).comp Dsec = sigma0.comp i.right.hom ∧
          (pathSpaceEvalAt 1 (MappingPathSpace f₀)).comp Dsec = sigmaA ∧
            (∀ a : A.right, a ∈ basedBasepointSet A →
              Dsec a = ContinuousMap.const I ((sigma0.comp i.right.hom) a)) ∧
              (∀ z : I × A.right,
                mappingPathSpacePointProjection f₀ (Dsec z.2 z.1) = i.right.hom z.2) ∧
                (∀ z : I × A.right, (Dsec z.2 z.1).path z.1 = d z.2 z.1) := by
    -- Delegate the remaining source-side rectification to the isolated helper so the theorem body
    -- stays focused on the already-verified path-space assembly.
    exact existsRectifiedSectionSquare hA hSigmaAtBase hSigma0Proj hSigmaAProj hSigmaADiag
  obtain ⟨Dsec, hDsec0, hDsec1, hDsecRel, hDsecProj, hDsecDiag⟩ := hRectified
  let hSectionRel :
      (sigma0.comp i.right.hom) HRel[A] sigmaA :=
    homotopyRelOfPathFamily
      (A := A)
      (B := basedSpaceAtPoint
        (TopCat.of (MappingPathSpace f₀))
        ((sigma0.comp i.right.hom) (underTopBasepoint A)))
      (f₀ := sigma0.comp i.right.hom)
      (f₁ := sigmaA)
      Dsec
      (fun a ↦ by
        simpa [pathSpaceEvalAt] using ContinuousMap.congr_fun hDsec0 a)
      (fun a ↦ by
        simpa [pathSpaceEvalAt] using ContinuousMap.congr_fun hDsec1 a)
      hDsecRel
  obtain ⟨Sigma, hFsec, hSigmaComp, hFsecComp⟩ :=
    existsExtendedMappingPathSection
      (i := i) (f₀ := f₀) (sigma0 := sigma0) (sigmaA := sigmaA)
      hi hSigmaAtBase hSectionRel
  have hAssemble :
      ∃ D : C(X.right, C(I, Y)),
        D.comp i.right.hom = d ∧
          (pathSpaceEvalAtZero Y).comp D = f₀ := by
    -- Route correction: the extended mapping-path homotopy itself carries the exact diagonal
    -- needed for the ordinary lift once the source square `Dsec` records the diagonal formula.
    have hFOnA :
        ∀ z : I × A.right, hFsec.toHomotopy (z.1, i.right.hom z.2) = Dsec z.2 z.1 := by
      intro z
      simpa [hSectionRel, homotopyRelOfPathFamily] using hFsecComp z
    exact
      assembleDiagonalFromSectionHomotopy
        (i := i.right.hom) (f₀ := f₀) hFsec.toHomotopy hSigma0Proj hFOnA hDsecDiag
  exact hAssemble

/-- A based cofibration between well-pointed based spaces is an unbased cofibration. -/
theorem IsBasedCofibration.isCofibration {A X : BasedSpace} {i : A ⟶ X}
    [CompactlyGeneratedWeakHausdorffSpace.{0, 0} A.right]
    [CompactlyGeneratedWeakHausdorffSpace.{0, 0} X.right]
    [hA : WellPointedBasedSpace A] [hX : WellPointedBasedSpace X] (hi : IsBasedCofibration i) :
    IsCofibration.{0, 0, 0} i.right.hom :=
  IsBasedCofibration.isCofibration_of_wellPointed hA.isCofibration hX.isCofibration hi
