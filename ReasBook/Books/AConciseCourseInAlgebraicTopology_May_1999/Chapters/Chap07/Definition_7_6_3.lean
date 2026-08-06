import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.HomotopyClasses
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Reformulation_7_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_5

universe u v

open Path.Homotopic.Quotient
open scoped unitInterval

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]

-- Semantic recall via `lean_leansearch`: the chapter owner
-- `continuousMapHomotopyClasses X Y` is the canonical quotient of `C(X, Y)` by ordinary homotopy,
-- so fiber translations should be recorded in that owner rather than through a duplicate local
-- setoid.

/-- The quotient type of homotopy classes of maps `fiber p b ⟶ fiber p b'`. -/
abbrev fiberMapHomotopyClasses (p : C(E, B)) (b b' : B) :=
  continuousMapHomotopyClasses (fiber p b) (fiber p b')

/-- A class in `fiberMapHomotopyClasses p b b'` is represented by translation along `β` when it is
the homotopy class of the endpoint map of some lift of `β.toHomotopyConst`. -/
def IsFiberTranslationOfPath (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path b b')
    (τ : fiberMapHomotopyClasses p b b') : Prop :=
  ∃ g₁ : C(fiber p b, fiber p b'),
    ∃ G : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
      p.comp G.toContinuousMap = β.toHomotopyConst.toContinuousMap ∧
        ⟦g₁⟧ = τ

/-- Construction 7.6.2 supplies a represented translation class for each path `β : Path b b'`. -/
theorem exists_isFiberTranslationOfPath (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path b b') : ∃ τ : fiberMapHomotopyClasses p b b', IsFiberTranslationOfPath p β τ := by
  -- Lift the constant-path homotopy and then package its endpoint back into the target fiber.
  rcases IsFibration.exists_homotopyLift
      (p := p) (A := ↥(fiber p b)) (g₀ := fiberInclusion p b) (H := β.toHomotopyConst)
      (comp_fiberInclusion p b) with ⟨g₁E, G, hG⟩
  let hg₁E := comp_endpoint_eq_const_of_fiberInclusionHomotopyLift p G hG
  let g₁ := fiberInclusionHomotopyLiftEndpointMap p g₁E hg₁E
  refine ⟨⟦g₁⟧, g₁, ?_, ?_, rfl⟩
  · -- Rewrite the endpoint map through the canonical inclusion of the target fiber.
    simpa [g₁] using G
  · -- The rewritten lift still projects to the original base homotopy.
    simpa [g₁] using hG

/-- Helper for Definition 7.6.3: a path homotopy induces a homotopy between the corresponding
base homotopies on `fiber p b`. -/
theorem toHomotopyConstHomotopicOnFiber (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    (hβ : β₀.Homotopic β₁) :
    ContinuousMap.Homotopic
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap)
      ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap) := by
  rcases hβ with ⟨H⟩
  -- Precompose the path homotopy with the first projection to forget the fiber coordinate.
  refine ⟨?_⟩
  simpa [Path.toHomotopyConst] using
    H.toHomotopy.compContinuousMap (ContinuousMap.fst : C(I × fiber p b, I))

/-- Helper for Definition 7.6.3: a path homotopy induces a boundary-fixed homotopy between the
corresponding base homotopies on `fiber p b`. -/
theorem toHomotopyConstHomotopicRelOnFiber (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    (hβ : β₀.Homotopic β₁) :
    ContinuousMap.HomotopicRel
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap)
      ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b))) := by
  rcases hβ with ⟨Hβ⟩
  let H :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).Homotopy
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap) := by
    -- Forget the fiber coordinate and reuse the given path homotopy in the base.
    simpa [Path.toHomotopyConst] using
      Hβ.toHomotopy.compContinuousMap (ContinuousMap.fst : C(I × fiber p b, I))
  refine ⟨{ toHomotopy := H, prop' := ?_ }⟩
  intro t x hx
  rcases hx with ⟨hx, _⟩
  rcases x with ⟨s, x⟩
  rcases Set.mem_insert_iff.mp hx with hs | hs
  · -- The left endpoint stays fixed at `b` throughout the path homotopy.
    subst hs
    simpa [H, Path.toHomotopyConst] using Hβ.source t
  · have hs' : s = 1 := Set.mem_singleton_iff.mp hs
    subst hs'
    -- The right endpoint stays fixed at `b'` throughout the path homotopy.
    simpa [H, Path.toHomotopyConst] using Hβ.target t

/-- Helper for Definition 7.6.3: homotopic endpoint maps define the same class in
`fiberMapHomotopyClasses p b b'`. -/
theorem endpointClass_eq_of_homotopic (p : C(E, B)) {b b' : B}
    {g₀ g₁ : C(fiber p b, fiber p b')} (hg : ContinuousMap.Homotopic g₀ g₁) :
    (⟦g₀⟧ : fiberMapHomotopyClasses p b b') = ⟦g₁⟧ :=
  Quotient.sound hg

/-- Helper for Definition 7.6.3: a boundary-fixed homotopy between two lifted homotopies yields
the same endpoint class in `fiberMapHomotopyClasses p b b'`. -/
theorem endpointClass_eq_of_homotopyRelLift (p : C(E, B)) {b b' : B}
    {g₀ g₁ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁)}
    (H :
      G₀.toContinuousMap.HomotopyRel G₁.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))) :
    (⟦g₀⟧ : fiberMapHomotopyClasses p b b') = ⟦g₁⟧ := by
  let endpointFace :
      C(I × fiber p b, E) :=
    ⟨fun sx ↦ H (sx.1, (1, sx.2)),
      by
        fun_prop⟩
  have hEndpointFace :
      ∀ sx : I × fiber p b, endpointFace sx ∈ fiber p b' := by
    intro sx
    -- The time-one face stays over `b'` because the lifted 2-homotopy is fixed on that boundary.
    rw [mem_fiber_iff]
    have hface :
        endpointFace sx = G₀.toContinuousMap (1, sx.2) :=
      H.eq_fst sx.1 ⟨by simp, by simp⟩
    rw [hface]
    change p (G₀ (1, sx.2)) = b'
    rw [G₀.apply_one sx.2]
    exact (g₀ sx.2).2
  let Hendpoint : g₀.Homotopy g₁ := by
    refine
      { toFun := fun sx ↦ ⟨endpointFace sx, hEndpointFace sx⟩
        continuous_toFun := endpointFace.continuous.subtype_mk hEndpointFace
        map_zero_left := ?_
        map_one_left := ?_ }
    · intro x
      apply Subtype.ext
      change endpointFace (0, x) = g₀ x
      rw [show endpointFace (0, x) = G₀.toContinuousMap (1, x) by
        exact H.eq_fst 0 ⟨by simp, by simp⟩]
      simpa using G₀.apply_one x
    · intro x
      apply Subtype.ext
      change endpointFace (1, x) = g₁ x
      rw [show endpointFace (1, x) = G₁.toContinuousMap (1, x) by
        exact H.eq_snd 1 ⟨by simp, by simp⟩]
      simpa using G₁.apply_one x
  -- Quotient equality is exactly homotopy of endpoint maps.
  exact endpointClass_eq_of_homotopic p ⟨Hendpoint⟩

/-- Helper for Definition 7.6.3: a 2-parameter comparison of lifted homotopies whose time-one
face stays over `b'` yields an ordinary homotopy between the endpoint maps into `fiber p b'`. -/
theorem endpointHomotopicOfTargetFaceHomotopy (p : C(E, B)) {b b' : B}
    {f₀ f₁ : C(fiber p b, E)}
    {g₀ g₁ : C(fiber p b, fiber p b')}
    {G₀ : f₀.Homotopy ((fiberInclusion p b').comp g₀)}
    {G₁ : f₁.Homotopy ((fiberInclusion p b').comp g₁)}
    (K : G₀.toContinuousMap.Homotopy G₁.toContinuousMap)
    (hKTarget : ∀ s : I, ∀ x : fiber p b, p (K (s, (1, x))) = b') :
    ContinuousMap.Homotopic g₀ g₁ := by
  let endpointFace : C(I × fiber p b, E) :=
    ⟨fun sx ↦ K (sx.1, (1, sx.2)),
      by
        fun_prop⟩
  have hEndpointFace : ∀ sx : I × fiber p b, endpointFace sx ∈ fiber p b' := by
    intro sx
    -- The time-one face remains in the target fiber by the assumed projection condition.
    rw [mem_fiber_iff]
    exact hKTarget sx.1 sx.2
  refine ⟨{
    toFun := fun sx ↦ ⟨endpointFace sx, hEndpointFace sx⟩
    continuous_toFun := endpointFace.continuous.subtype_mk hEndpointFace
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    -- Evaluating the comparison homotopy at `s = 0` recovers the original endpoint map `g₀`.
    apply Subtype.ext
    change endpointFace (0, x) = g₀ x
    rw [show endpointFace (0, x) = G₀.toContinuousMap (1, x) by
      simpa [endpointFace] using K.apply_zero (1, x)]
    simpa using G₀.apply_one x
  · intro x
    -- Evaluating the comparison homotopy at `s = 1` recovers the transported endpoint map `g₁`.
    apply Subtype.ext
    change endpointFace (1, x) = g₁ x
    rw [show endpointFace (1, x) = G₁.toContinuousMap (1, x) by
      simpa [endpointFace] using K.apply_one (1, x)]
    simpa using G₁.apply_one x

/-- Helper for Definition 7.6.3: a 2-parameter comparison of lifted homotopies whose time-one
face stays over `b'` yields an ordinary homotopy between the endpoint maps into `fiber p b'`. -/
theorem endpointHomotopicOfLiftHomotopy (p : C(E, B)) {b b' : B}
    {g₀ g₁ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁)}
    (K : G₀.toContinuousMap.Homotopy G₁.toContinuousMap)
    (hKTarget : ∀ s : I, ∀ x : fiber p b, p (K (s, (1, x))) = b') :
    ContinuousMap.Homotopic g₀ g₁ := by
  -- Specialize the more flexible endpoint comparison lemma to lifts starting at
  -- `fiberInclusion p b`.
  simpa using endpointHomotopicOfTargetFaceHomotopy (p := p)
    (f₀ := fiberInclusion p b) (f₁ := fiberInclusion p b) K hKTarget

/-- Helper for Definition 7.6.3: first choose the exact boundary-fixed base witness and lift that
specific homotopy, without yet rigidifying the source face back to `fiberInclusion p b`. -/
theorem existsUnrestrictedLiftedWitnessHomotopyOfHomotopic
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₀ β₁ : Path b b'} (hβ : β₀.Homotopic β₁)
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    (hG₀ : p.comp G₀.toContinuousMap = β₀.toHomotopyConst.toContinuousMap) :
    ∃ Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b))),
      ∃ Graw : C(I × fiber p b, E),
        ∃ Kraw : G₀.toContinuousMap.Homotopy Graw,
          p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap ∧
            p.comp Graw = β₁.toHomotopyConst.toContinuousMap := by
  rcases toHomotopyConstHomotopicRelOnFiber p hβ with ⟨Hβrel⟩
  -- Route correction: lift the exact boundary-fixed witness, not an unrelated homotopic copy.
  -- Lift the chosen base homotopy starting from the given witness `G₀`.
  rcases IsFibration.exists_homotopyLift (p := p) (A := I × fiber p b)
      (g₀ := G₀.toContinuousMap) Hβrel.toHomotopy hG₀ with ⟨Graw, Kraw, hKraw⟩
  refine ⟨Hβrel, Graw, Kraw, hKraw, ?_⟩
  -- Evaluating the comparison at `s = 1` reads off the transported base homotopy over `β₁`.
  ext ux
  have hAtOne := ContinuousMap.congr_fun hKraw (1, ux)
  simpa using hAtOne

/-- Helper for Definition 7.6.3: the source face of the transported comparison remains in the
source fiber because the chosen base homotopy is fixed on `u = 0`. -/
theorem sourceFaceProjectsToSourceOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap) :
    ∀ s : I, ∀ x : fiber p b, p (Kraw (s, (0, x))) = b := by
  intro s x
  -- Evaluate the lifted square on the source face and rewrite with the relative boundary formula.
  have hLift := ContinuousMap.congr_fun hKraw (s, (0, x))
  calc
    p (Kraw (s, (0, x))) = Hβrel.toHomotopy (s, (0, x)) := by
      simpa using hLift
    _ = ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap) (0, x) := by
      exact Hβrel.eq_fst s ⟨by simp, by simp⟩
    _ = b := by
      simp [Path.toHomotopyConst]

/-- Helper for Definition 7.6.3: the time-one face of the transported comparison remains in the
target fiber because the chosen base homotopy is fixed on `u = 1`. -/
theorem targetFaceProjectsToTargetOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap) :
    ∀ s : I, ∀ x : fiber p b, p (Kraw (s, (1, x))) = b' := by
  intro s x
  -- Evaluate the lifted square on the target face and rewrite with the relative boundary formula.
  have hLift := ContinuousMap.congr_fun hKraw (s, (1, x))
  calc
    p (Kraw (s, (1, x))) = Hβrel.toHomotopy (s, (1, x)) := by
      simpa using hLift
    _ = ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap) (1, x) := by
      exact Hβrel.eq_snd s ⟨by simp, by simp⟩
    _ = b' := by
      simp [Path.toHomotopyConst]

/-- Helper for Definition 7.6.3: the source face of the transported comparison packages to a map
`fiber p b → fiber p b` homotopic to the identity. -/
theorem existsSourceFaceMapOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap)
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    ∃ gSource : C(fiber p b, fiber p b),
      (fiberInclusion p b).comp gSource = Graw.curry 0 ∧
        ContinuousMap.Homotopic (ContinuousMap.id (fiber p b)) gSource := by
  have hSourceMap :
      p.comp (Graw.curry 0) = ContinuousMap.const (fiber p b) b := by
    -- Evaluating the transported lift at `u = 0` shows that its source face still lies over `b`.
    ext x
    have hFace := ContinuousMap.congr_fun hGraw (0, x)
    simpa [Path.toHomotopyConst] using hFace
  let gSource := fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 0) hSourceMap
  have hgSource :
      (fiberInclusion p b).comp gSource = Graw.curry 0 := by
    -- Forgetting the subtype packaging recovers the original source face map in `E`.
    simpa [gSource] using
      comp_fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 0) hSourceMap
  let sourceFace : C(I × fiber p b, fiber p b) :=
    ⟨fun sx ↦
        ⟨Kraw (sx.1, (0, sx.2)),
          sourceFaceProjectsToSourceOfBoundaryFixedTransport p hKraw sx.1 sx.2⟩,
      Kraw.continuous.comp (by fun_prop) |>.subtype_mk fun sx ↦
        sourceFaceProjectsToSourceOfBoundaryFixedTransport p hKraw sx.1 sx.2⟩
  have hSourceZero : sourceFace.curry 0 = ContinuousMap.id (fiber p b) := by
    -- At `s = 0`, the comparison starts at the original witness `G₀`, whose source edge is `id`.
    ext x
    change Kraw (0, (0, x)) = ((x : fiber p b) : E)
    rw [show Kraw (0, (0, x)) = G₀.toContinuousMap (0, x) by
      simpa using Kraw.apply_zero (0, x)]
    simpa using G₀.apply_zero x
  have hSourceOne : sourceFace.curry 1 = gSource := by
    -- At `s = 1`, the comparison lands on the source face of `Graw`.
    ext x
    change Kraw (1, (0, x)) = ((gSource x : fiber p b) : E)
    rw [show Kraw (1, (0, x)) = Graw.curry 0 x by
      simpa using Kraw.apply_one (0, x)]
    simpa using (ContinuousMap.congr_fun hgSource x).symm
  refine ⟨gSource, hgSource, ?_⟩
  -- Package the source face itself as the required homotopy in the source fiber.
  refine ⟨{
    toFun := sourceFace
    continuous_toFun := sourceFace.continuous
    map_zero_left := by
      intro x
      simpa using ContinuousMap.congr_fun hSourceZero x
    map_one_left := by
      intro x
      simpa using ContinuousMap.congr_fun hSourceOne x }⟩

/-- Helper for Definition 7.6.3: the source-edge correction can be chosen as an honest homotopy
from `fiberInclusion p b` to `Graw.curry 0` whose projection is constantly `b`. -/
theorem existsSourceEdgeHomotopyDataOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap)
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    ∃ HSourceEdge : (fiberInclusion p b).Homotopy (Graw.curry 0),
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap := by
  rcases existsSourceFaceMapOfBoundaryFixedTransport (p := p) (Hβrel := Hβrel)
      (Graw := Graw) (g₀ := g₀) (G₀ := G₀) (Kraw := Kraw) hKraw hGraw with
    ⟨gSource, hgSource, hgSourceHom⟩
  rcases hgSourceHom with ⟨HSourceFiber⟩
  let HSourceEdgeRaw :
      ((fiberInclusion p b).comp (ContinuousMap.id (fiber p b))).Homotopy
        ((fiberInclusion p b).comp gSource) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (fiberInclusion p b)) HSourceFiber
  have hSourceEdgeRaw :
      p.comp HSourceEdgeRaw.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap := by
    -- Every stage of the source-fiber homotopy still lies in the fiber over `b`.
    ext sx
    rcases sx with ⟨s, x⟩
    change p (((HSourceFiber (s, x) : fiber p b) : E)) = b
    exact (HSourceFiber (s, x)).2
  let HSourceEdge :
      (fiberInclusion p b).Homotopy (Graw.curry 0) :=
    HSourceEdgeRaw.cast (by simp) hgSource
  refine ⟨HSourceEdge, ?_⟩
  -- Rewriting the target to `Graw.curry 0` preserves the constant-base projection statement.
  simpa [HSourceEdge] using hSourceEdgeRaw

/-- Helper for Definition 7.6.3: after building the unrestricted transport, the remaining task is
to package the raw transported time-one face as a map into `fiber p b'` and to view `Graw`
itself as a homotopy ending at that packaged endpoint map. -/
theorem rawEndpointWitnessOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    ∃ gRaw : C(fiber p b, fiber p b'),
      (fiberInclusion p b').comp gRaw = Graw.curry 1 ∧
        ∃ GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw),
          GrawLift.toContinuousMap = Graw := by
  have hRawEndpoint : p.comp (Graw.curry 1) = ContinuousMap.const (fiber p b) b' := by
    -- Evaluating the transported square at `u = 1` shows that its endpoint lies in `fiber p b'`.
    ext x
    have hFace := ContinuousMap.congr_fun hGraw (1, x)
    simpa [Path.toHomotopyConst] using hFace
  let gRaw := fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 1) hRawEndpoint
  have hgRaw :
      (fiberInclusion p b').comp gRaw = Graw.curry 1 := by
    -- Forgetting the target-fiber subtype recovers the original time-one face.
    simpa [gRaw] using
      comp_fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 1) hRawEndpoint
  let GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw) :=
    { toFun := Graw
      continuous_toFun := Graw.continuous
      map_zero_left := by
        intro x
        rfl
      map_one_left := by
        intro x
        simpa using (ContinuousMap.congr_fun hgRaw x).symm }
  refine ⟨gRaw, hgRaw, GrawLift, rfl⟩

/-- Helper for Definition 7.6.3: the unrestricted transported square already shows that the
original endpoint map `g₀` is homotopic to the raw transported endpoint map. -/
theorem rawEndpointHomotopicOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap)
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    ∃ gRaw : C(fiber p b, fiber p b'),
      (fiberInclusion p b').comp gRaw = Graw.curry 1 ∧
        ContinuousMap.Homotopic g₀ gRaw := by
  have hTargetFace : ∀ s : I, ∀ x : fiber p b, p (Kraw (s, (1, x))) = b' :=
    targetFaceProjectsToTargetOfBoundaryFixedTransport p hKraw
  rcases rawEndpointWitnessOfBoundaryFixedTransport (p := p) (β₁ := β₁)
      (Graw := Graw) hGraw with ⟨gRaw, hgRaw, GrawLift, hGrawLift⟩
  let hComparison : G₀.toContinuousMap.Homotopy GrawLift.toContinuousMap :=
    Kraw.cast rfl hGrawLift.symm
  have hComparisonTarget : ∀ s : I, ∀ x : fiber p b, p (hComparison (s, (1, x))) = b' := by
    intro s x
    simpa [hComparison] using hTargetFace s x
  refine ⟨gRaw, hgRaw, ?_⟩
  -- Compare the original lift with the packaged raw transported lift along the common time-one
  -- target face.
  exact endpointHomotopicOfTargetFaceHomotopy (p := p) (G₀ := G₀) (G₁ := GrawLift)
    hComparison hComparisonTarget

/-- Helper for Definition 7.6.3: after building the unrestricted transport, the remaining task is
to rigidify its source face so that the transported endpoint map is represented by an actual lift
of `β₁.toHomotopyConst` starting at `fiberInclusion p b`. -/
theorem sourceEdgeHomotopyOfBoundaryFixedTransport
    (p : C(E, B)) {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap)
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    ContinuousMap.Homotopic (fiberInclusion p b) (Graw.curry 0) := by
  rcases existsSourceEdgeHomotopyDataOfBoundaryFixedTransport (p := p) (Hβrel := Hβrel)
      (Graw := Graw) (g₀ := g₀) (G₀ := G₀) (Kraw := Kraw) hKraw hGraw with
    ⟨HSourceEdge, _⟩
  exact ⟨HSourceEdge⟩

/-- Helper for Definition 7.6.3: reinterpret a raw lifted square as a map into the path space
`C(I, E)` by swapping the interval and source coordinates. -/
def rawLiftPathSpaceMap {X : Type u} [TopologicalSpace X] (Graw : C(I × X, E)) : C(X, C(I, E)) :=
  (Graw.comp ContinuousMap.prodSwap).curry

/-- Helper for Definition 7.6.3: evaluating `rawLiftPathSpaceMap` recovers the original raw
lifted square. -/
@[simp] theorem rawLiftPathSpaceMap_apply {X : Type u} [TopologicalSpace X]
    (Graw : C(I × X, E)) (x : X) (t : I) :
    rawLiftPathSpaceMap Graw x t = Graw (t, x) :=
  rfl

/-- Helper for Definition 7.6.3: the raw transported lift becomes a path-space lift of
`(β₁.toHomotopyConst (Y := fiber p b)).toPathSpaceMap`. -/
theorem comp_rawLiftPathSpaceMap
    (p : C(E, B)) {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap) :
    (pathSpacePostcompose p).comp (rawLiftPathSpaceMap Graw) =
      (β₁.toHomotopyConst (Y := fiber p b)).toPathSpaceMap := by
  -- Evaluate the path-space lift pointwise and rewrite with the projected raw transport formula.
  ext x t
  have hPoint := ContinuousMap.congr_fun hGraw (t, x)
  simpa [rawLiftPathSpaceMap, ContinuousMap.Homotopy.toPathSpaceMap, Path.toHomotopyConst] using
    hPoint

/-- Helper for Definition 7.6.3: an honest lift of `β₁.toHomotopyConst` becomes a path-space
lift of `(β₁.toHomotopyConst (Y := fiber p b)).toPathSpaceMap`. -/
theorem comp_homotopyLift_toPathSpaceMap
    (p : C(E, B)) {b b' : B} {β₁ : Path b b'}
    {g₁ : C(fiber p b, fiber p b')}
    {G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁)}
    (hG₁ : p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap) :
    (pathSpacePostcompose p).comp G₁.toPathSpaceMap =
      (β₁.toHomotopyConst (Y := fiber p b)).toPathSpaceMap := by
  -- Evaluate the honest lift pointwise and rewrite with its projected base-homotopy formula.
  ext x t
  have hPoint := ContinuousMap.congr_fun hG₁ (t, x)
  simpa [ContinuousMap.Homotopy.toPathSpaceMap, Path.toHomotopyConst] using hPoint

/-- Helper for Definition 7.6.3: the scalar `t / 2` still lies in the unit interval. -/
theorem leftHalf_mem_I (t : I) : ((t : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  -- The left-half reparameterization preserves the unit interval bounds.
  constructor <;> nlinarith [t.2.1, t.2.2]

/-- Helper for Definition 7.6.3: the scalar `(t + 1) / 2` still lies in the unit interval. -/
theorem rightHalf_mem_I (t : I) : (((t : ℝ) + 1) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  -- The right-half reparameterization also preserves the unit interval bounds.
  constructor <;> nlinarith [t.2.1, t.2.2]

/-- Helper for Definition 7.6.3: the left-half reparameterization of `I`. -/
noncomputable def leftHalf (t : I) : I := ⟨(t : ℝ) / 2, leftHalf_mem_I t⟩

/-- Helper for Definition 7.6.3: the right-half reparameterization of `I`. -/
noncomputable def rightHalf (t : I) : I := ⟨((t : ℝ) + 1) / 2, rightHalf_mem_I t⟩

/-- Helper for Definition 7.6.3: `leftHalf` is continuous. -/
theorem continuous_leftHalf : Continuous leftHalf := by
  -- The left-half reparameterization is the subtype lift of the continuous scalar map `t ↦ t / 2`.
  exact (continuous_subtype_val.div_const (2 : ℝ)).subtype_mk fun t ↦ leftHalf_mem_I t

/-- Helper for Definition 7.6.3: `rightHalf` is continuous. -/
theorem continuous_rightHalf : Continuous rightHalf := by
  -- The right-half reparameterization is the subtype lift of the affine map `t ↦ (t + 1) / 2`.
  exact
    ((continuous_subtype_val.add continuous_const).div_const (2 : ℝ)).subtype_mk
      fun t ↦ rightHalf_mem_I t

/-- Helper for Definition 7.6.3: the left-half reparameterization fixes `0`. -/
@[simp] theorem leftHalf_zero : leftHalf 0 = 0 := by
  -- The left endpoint remains the left endpoint after halving.
  apply Subtype.ext
  norm_num [leftHalf]

/-- Helper for Definition 7.6.3: the right-half reparameterization sends `1` to `1`. -/
@[simp] theorem rightHalf_one : rightHalf 1 = 1 := by
  -- The right endpoint remains the right endpoint after the affine rescaling.
  apply Subtype.ext
  norm_num [rightHalf]

/-- Helper for Definition 7.6.3: the midpoint reached from the left agrees with the midpoint
reached from the right. -/
theorem leftHalf_one_eq_rightHalf_zero : leftHalf 1 = rightHalf 0 := by
  -- Both half-interval parameterizations meet at the midpoint `1 / 2`.
  apply Subtype.ext
  norm_num [leftHalf, rightHalf]

/-- Helper for Definition 7.6.3: the left half of `((Path.refl b).trans β)` is constantly `b`. -/
theorem reflTrans_apply_leftHalf {b b' : B} (β : Path b b') (t : I) :
    ((Path.refl b).trans β) (leftHalf t) = b := by
  -- On the left half, concatenation stays on the trivial leading path.
  have ht :
      (((leftHalf t : I) : ℝ) ≤ (1 : ℝ) / 2) := by
    change ((t : ℝ) / 2 ≤ (1 : ℝ) / 2)
    nlinarith [t.2.2]
  rw [Path.trans_apply, dif_pos ht]
  simp

/-- Helper for Definition 7.6.3: the right half of `((Path.refl b).trans β)` recovers `β`. -/
theorem reflTrans_apply_rightHalf {b b' : B} (β : Path b b') (t : I) :
    ((Path.refl b).trans β) (rightHalf t) = β t := by
  -- Route correction: normalize the concatenated path on the concrete right-half parameter.
  by_cases ht0 : t = 0
  · subst ht0
    have h0 : (((rightHalf (0 : I) : I) : ℝ) ≤ (1 : ℝ) / 2) := by
      norm_num [rightHalf]
    rw [Path.trans_apply, dif_pos h0]
    simp [rightHalf]
  · have hcond : ¬ (((rightHalf t : I) : ℝ) ≤ (1 : ℝ) / 2) := by
      intro h
      have hle : (t : ℝ) ≤ 0 := by
        change (((t : ℝ) + 1) / 2 ≤ (1 : ℝ) / 2) at h
        nlinarith
      have ht0r : (t : ℝ) = 0 := by
        linarith [t.2.1, hle]
      apply ht0
      apply Subtype.ext
      simpa using ht0r
    have hParam :
        ⟨2 * ((rightHalf t : I) : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 hcond).le, (rightHalf t).2.2⟩⟩ = t := by
      apply Subtype.ext
      change 2 * ((((t : ℝ) + 1) / 2)) - 1 = (t : ℝ)
      ring
    rw [Path.trans_apply, dif_neg hcond]
    exact congrArg β hParam

/-- Helper for Definition 7.6.3: a lift over `((Path.refl b).trans β)` splits into a concrete
source-edge correction and a concrete raw tail over `β`. -/
theorem reflTransSourceEdgeAndTail
    (p : C(E, B)) {b b' : B} {β : Path b b'}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    (hG₀ : p.comp G₀.toContinuousMap = ((Path.refl b).trans β).toHomotopyConst.toContinuousMap) :
    ∃ Gtail : C(I × fiber p b, E),
      p.comp Gtail = β.toHomotopyConst.toContinuousMap ∧
        ∃ HSourceEdge : (fiberInclusion p b).Homotopy (Gtail.curry 0),
          p.comp HSourceEdge.toContinuousMap =
              (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap ∧
            (fiberInclusion p b').comp g₀ = Gtail.curry 1 := by
  let Gtail : C(I × fiber p b, E) :=
    ⟨fun tx ↦ G₀ (rightHalf tx.1, tx.2), by
      exact G₀.continuous.comp <|
        (continuous_rightHalf.comp continuous_fst).prodMk continuous_snd⟩
  have hGtail : p.comp Gtail = β.toHomotopyConst.toContinuousMap := by
    -- Restricting `G₀` to the concrete right half produces a literal lift of `β`.
    ext tx
    rcases tx with ⟨t, x⟩
    have hPoint := ContinuousMap.congr_fun hG₀ (rightHalf t, x)
    simpa [Gtail, Path.toHomotopyConst, reflTrans_apply_rightHalf] using hPoint
  let HSourceEdge : (fiberInclusion p b).Homotopy (Gtail.curry 0) :=
    { toFun := fun sx ↦ G₀ (leftHalf sx.1, sx.2)
      continuous_toFun := by
        exact G₀.continuous.comp <|
          (continuous_leftHalf.comp continuous_fst).prodMk continuous_snd
      map_zero_left := by
        intro x
        simpa [leftHalf_zero] using G₀.apply_zero x
      map_one_left := by
        intro x
        change G₀ (leftHalf 1, x) = G₀ (rightHalf 0, x)
        exact congrArg (fun u : I ↦ G₀ (u, x)) leftHalf_one_eq_rightHalf_zero }
  have hSourceEdge :
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap := by
    -- Restricting `G₀` to the left half records the explicit source-edge correction over `b`.
    ext sx
    rcases sx with ⟨t, x⟩
    have hPoint := ContinuousMap.congr_fun hG₀ (leftHalf t, x)
    simpa [HSourceEdge, Path.toHomotopyConst, reflTrans_apply_leftHalf] using hPoint
  have hEndpoint : (fiberInclusion p b').comp g₀ = Gtail.curry 1 := by
    -- The concrete raw tail still ends at the original endpoint map `g₀`.
    ext x
    calc
      ((fiberInclusion p b').comp g₀) x = G₀ (1, x) := by
        simpa using (G₀.apply_one x).symm
      _ = G₀ (rightHalf 1, x) := by
        simpa using (congrArg (fun u : I ↦ G₀ (u, x)) rightHalf_one).symm
      _ = (Gtail.curry 1) x := by
        rfl
  exact ⟨Gtail, hGtail, HSourceEdge, hSourceEdge, hEndpoint⟩

/-- Helper for Definition 7.6.3: concatenating the source-edge correction with the raw
transported lift projects to the left-unit concatenation `(Path.refl b).trans β₁`. -/
theorem comp_sourceEdgeTransRawLift
    (p : C(E, B)) {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap)
    (HSourceEdge : (fiberInclusion p b).Homotopy (Graw.curry 0))
    (hSourceEdge :
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap)
    {gRaw : C(fiber p b, fiber p b')}
    (hgRaw : (fiberInclusion p b').comp gRaw = Graw.curry 1) :
    let GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw) :=
      { toFun := Graw
        continuous_toFun := Graw.continuous
        map_zero_left := by
          intro x
          rfl
        map_one_left := by
          intro x
          simpa using (ContinuousMap.congr_fun hgRaw x).symm }
    let βCombined : Path b b' := (Path.refl b).trans β₁
    let Gcombined : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp gRaw) :=
      HSourceEdge.trans GrawLift
    p.comp Gcombined.toContinuousMap = βCombined.toHomotopyConst.toContinuousMap := by
  -- Route correction: isolate the concatenated projection calculation so the remaining blocker is
  -- only the left-unit witness transport.
  ext tx
  rcases tx with ⟨t, x⟩
  change p ((HSourceEdge.trans
      { toFun := Graw
        continuous_toFun := Graw.continuous
        map_zero_left := by
          intro x
          rfl
        map_one_left := by
          intro x
          simpa using (ContinuousMap.congr_fun hgRaw x).symm }) (t, x)) =
    ((Path.refl b).trans β₁) t
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs with ht
  · have hPoint :=
      ContinuousMap.congr_fun hSourceEdge
        (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x)
    simpa using hPoint
  · have hPoint :=
      ContinuousMap.congr_fun hGraw
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)
    simpa [Path.toHomotopyConst] using hPoint

/-- Helper for Definition 7.6.3: a source-edge correction packages the raw source face into a
self-map of `fiber p b` that is homotopic to the identity. -/
theorem existsSourceSelfMapOfSourceEdgeCorrection
    (p : C(E, B)) {b : B}
    {Graw : C(I × fiber p b, E)}
    (HSourceEdge : (fiberInclusion p b).Homotopy (Graw.curry 0))
    (hSourceEdge :
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap) :
    ∃ gSource : C(fiber p b, fiber p b),
      (fiberInclusion p b).comp gSource = Graw.curry 0 ∧
        ContinuousMap.Homotopic (ContinuousMap.id (fiber p b)) gSource := by
  have hSourceMap :
      p.comp (Graw.curry 0) = ContinuousMap.const (fiber p b) b := by
    -- Evaluating the corrected source edge at time `1` shows that the raw source face lies over
    -- the source fiber.
    ext x
    have hFace := ContinuousMap.congr_fun hSourceEdge (1, x)
    simpa using hFace
  let gSource := fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 0) hSourceMap
  have hgSource :
      (fiberInclusion p b).comp gSource = Graw.curry 0 := by
    -- Forgetting the subtype packaging recovers the original raw source face.
    simpa [gSource] using
      comp_fiberInclusionHomotopyLiftEndpointMap p (Graw.curry 0) hSourceMap
  let HSourceFiber :
      (ContinuousMap.id (fiber p b)).Homotopy gSource :=
    { toFun := fun sx ↦
        ⟨HSourceEdge (sx.1, sx.2), by
          rw [mem_fiber_iff]
          have hStage := ContinuousMap.congr_fun hSourceEdge (sx.1, sx.2)
          simpa using hStage⟩
      continuous_toFun := by
        exact HSourceEdge.continuous.subtype_mk <| fun sx ↦ by
          rw [mem_fiber_iff]
          have hStage := ContinuousMap.congr_fun hSourceEdge (sx.1, sx.2)
          simpa using hStage
      map_zero_left := by
        intro x
        apply Subtype.ext
        simpa using HSourceEdge.apply_zero x
      map_one_left := by
        intro x
        apply Subtype.ext
        change HSourceEdge (1, x) = ((gSource x : fiber p b) : E)
        rw [show HSourceEdge (1, x) = Graw.curry 0 x by simpa using HSourceEdge.apply_one x]
        simpa using (ContinuousMap.congr_fun hgSource x).symm }
  refine ⟨gSource, hgSource, ⟨HSourceFiber⟩⟩

/-- Helper for Definition 7.6.3: the projected loop `H.symm.trans H` contracts relative to the
boundary `({0, 1} : Set I) ×ˢ Set.univ`. -/
theorem homotopySymmTransHomotopicRelRefl
    {X : Type u} [TopologicalSpace X] {r₀ r₁ : C(X, B)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I => H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I => H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Definition 7.6.3: if the projected comparison of two endpoint-inclusion maps
contracts relative to the constant base map, then the endpoint maps are homotopic in the fiber. -/
theorem fiberEndpointHomotopic_of_projectedHomotopyRelConst
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] {b' : B}
    {f₀ f₁ : C(X, fiber p b')}
    (F : ((fiberInclusion p b').comp f₀).Homotopy ((fiberInclusion p b').comp f₁))
    (hFrel :
      (p.comp F.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl (ContinuousMap.const X b')).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    ContinuousMap.Homotopic f₀ f₁ := by
  let overConst : C(X, E) → Prop := fun g ↦ p.comp g = ContinuousMap.const X b'
  rcases hFrel with ⟨hFrel⟩
  -- Route correction: rectify the projected ordinary homotopy to a homotopy that stays over the
  -- constant base map `b'`, then package that rectified comparison back into the fiber.
  rcases IsFibration.exists_homotopyLift
      (p := p) (A := I × X) (H := hFrel.toHomotopy) (g₀ := F.toContinuousMap) rfl with
    ⟨Graw, Kraw, hKraw⟩
  have hGraw : p.comp Graw = (ContinuousMap.Homotopy.refl (ContinuousMap.const X b')).toContinuousMap := by
    -- Evaluating the lifted square at `s = 1` reads off the rectified homotopy over `b'`.
    ext tx
    simpa using ContinuousMap.congr_fun hKraw (1, tx)
  let sourceFace :
      ContinuousMap.HomotopyWith ((fiberInclusion p b').comp f₀) (Graw.curry 0) overConst :=
    { toHomotopy :=
        { toFun := fun sx ↦ Kraw (sx.1, (0, sx.2))
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro x
            rw [Kraw.apply_zero (0, x)]
            simpa using F.apply_zero x
          map_one_left := by
            intro x
            rw [Kraw.apply_one (0, x)]
            rfl }
      prop' := by
        intro s
        ext x
        have hLift := ContinuousMap.congr_fun hKraw (s, (0, x))
        calc
          p (Kraw (s, (0, x))) = hFrel.toHomotopy (s, (0, x)) := by
            simpa using hLift
          _ = (p.comp F.toContinuousMap) (0, x) := by
            exact hFrel.eq_fst s ⟨by simp, by simp⟩
          _ = p (F (0, x)) := rfl
          _ = b' := by
            rw [F.apply_zero]
            exact (f₀ x).2 }
  let middleFace :
      ContinuousMap.HomotopyWith (Graw.curry 0) (Graw.curry 1) overConst :=
    { toHomotopy :=
        { toContinuousMap := Graw
          map_zero_left := by
            intro x
            rfl
          map_one_left := by
            intro x
            rfl }
      prop' := by
        intro t
        ext x
        simpa using ContinuousMap.congr_fun hGraw (t, x) }
  let targetFace :
      ContinuousMap.HomotopyWith ((fiberInclusion p b').comp f₁) (Graw.curry 1) overConst :=
    { toHomotopy :=
        { toFun := fun sx ↦ Kraw (sx.1, (1, sx.2))
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro x
            rw [Kraw.apply_zero (1, x)]
            simpa using F.apply_one x
          map_one_left := by
            intro x
            rw [Kraw.apply_one (1, x)]
            rfl }
      prop' := by
        intro s
        ext x
        have hLift := ContinuousMap.congr_fun hKraw (s, (1, x))
        calc
          p (Kraw (s, (1, x))) = hFrel.toHomotopy (s, (1, x)) := by
            simpa using hLift
          _ = (p.comp F.toContinuousMap) (1, x) := by
            exact hFrel.eq_fst s ⟨by simp, by simp⟩
          _ = p (F (1, x)) := rfl
          _ = b' := by
            rw [F.apply_one]
            exact (f₁ x).2 }
  let rectified :
      ContinuousMap.HomotopyWith ((fiberInclusion p b').comp f₀) ((fiberInclusion p b').comp f₁)
        overConst :=
    sourceFace.trans (middleFace.trans targetFace.symm)
  refine ⟨{
    toFun := fun sx ↦
      ⟨rectified.toHomotopy (sx.1, sx.2), by
        rw [mem_fiber_iff]
        have hStage := rectified.prop sx.1
        simpa using ContinuousMap.congr_fun hStage sx.2⟩
    continuous_toFun := rectified.toHomotopy.continuous_toFun.subtype_mk <| by
      intro sx
      rw [mem_fiber_iff]
      have hStage := rectified.prop sx.1
      simpa using ContinuousMap.congr_fun hStage sx.2
    map_zero_left := by
      intro x
      apply Subtype.ext
      simpa using rectified.toHomotopy.apply_zero x
    map_one_left := by
      intro x
      apply Subtype.ext
      simpa using rectified.toHomotopy.apply_one x }⟩

/-- Helper for Definition 7.6.3: after packaging the source correction as `gSource`, the
comparison between the raw lift and the precomposed honest lift projects to a contractible loop
over the constant target map `b'`. -/
theorem projectedLiftComparisonRelRefl
    (p : C(E, B)) {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap)
    {gSource : C(fiber p b, fiber p b)}
    (hgSource : (fiberInclusion p b).comp gSource = Graw.curry 0)
    {gRaw : C(fiber p b, fiber p b')}
    (hgRaw : (fiberInclusion p b').comp gRaw = Graw.curry 1)
    {g₁ : C(fiber p b, fiber p b')}
    {G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁)}
    (hG₁ : p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap) :
    let GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw) :=
      { toFun := Graw
        continuous_toFun := Graw.continuous
        map_zero_left := by
          intro x
          rfl
        map_one_left := by
          intro x
          simpa using (ContinuousMap.congr_fun hgRaw x).symm }
    let G₁pre :
        (Graw.curry 0).Homotopy ((fiberInclusion p b').comp (g₁.comp gSource)) :=
      (G₁.compContinuousMap gSource).cast hgSource (by
        ext x
        rfl)
    (p.comp (GrawLift.symm.trans G₁pre).toContinuousMap).HomotopicRel
      ((ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b')).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b))) := by
  let H := β₁.toHomotopyConst (Y := fiber p b)
  let GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw) :=
    { toFun := Graw
      continuous_toFun := Graw.continuous
      map_zero_left := by
        intro x
        rfl
      map_one_left := by
        intro x
        simpa using (ContinuousMap.congr_fun hgRaw x).symm }
  let G₁pre :
      (Graw.curry 0).Homotopy ((fiberInclusion p b').comp (g₁.comp gSource)) :=
    (G₁.compContinuousMap gSource).cast hgSource (by
      ext x
      rfl)
  have hGrawLift :
      p.comp GrawLift.toContinuousMap = H.toContinuousMap := by
    -- The raw lift still projects to the chosen base path family `β₁`.
    simpa [GrawLift, H] using hGraw
  have hG₁pre :
      p.comp G₁pre.toContinuousMap = H.toContinuousMap := by
    -- Precomposing the honest lift by `gSource` does not change the projected base homotopy.
    ext tx
    rcases tx with ⟨t, x⟩
    have hPoint := ContinuousMap.congr_fun hG₁ (t, gSource x)
    simpa [G₁pre, H, Path.toHomotopyConst] using hPoint
  have hProjected :
      p.comp (GrawLift.symm.trans G₁pre).toContinuousMap = (H.symm.trans H).toContinuousMap := by
    -- Projecting the comparison reduces it to the standard loop `H.symm.trans H`.
    ext tx
    change p ((GrawLift.symm.trans G₁pre) tx) = (H.symm.trans H) tx
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        ContinuousMap.congr_fun hGrawLift
          (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
    · simpa using
        ContinuousMap.congr_fun hG₁pre
          (⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩,
            tx.2)
  -- Rewrite to the canonical projected loop and contract it rel boundary.
  change (p.comp (GrawLift.symm.trans G₁pre).toContinuousMap).HomotopicRel
      ((ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b')).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))
  exact hProjected ▸ homotopySymmTransHomotopicRelRefl H

/-- Helper for Definition 7.6.3: compare an honest lift over `β₁` with a raw lift over the same
base homotopy after fixing the source edge, but only at the endpoint level needed downstream. -/
theorem endpointHomotopicOfSourceEdgeTransport
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap)
    (HSourceEdge : (fiberInclusion p b).Homotopy (Graw.curry 0))
    (hSourceEdge :
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap)
    {gRaw : C(fiber p b, fiber p b')}
    (hgRaw : (fiberInclusion p b').comp gRaw = Graw.curry 1)
    {g₁ : C(fiber p b, fiber p b')}
    {G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁)}
    (hG₁ : p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap) :
    ContinuousMap.Homotopic gRaw g₁ := by
  rcases existsSourceSelfMapOfSourceEdgeCorrection
      (p := p) (Graw := Graw) HSourceEdge hSourceEdge with
    ⟨gSource, hgSource, hgSourceHom⟩
  let GrawLift : (Graw.curry 0).Homotopy ((fiberInclusion p b').comp gRaw) :=
    { toFun := Graw
      continuous_toFun := Graw.continuous
      map_zero_left := by
        intro x
        rfl
      map_one_left := by
        intro x
        simpa using (ContinuousMap.congr_fun hgRaw x).symm }
  let G₁pre :
      (Graw.curry 0).Homotopy ((fiberInclusion p b').comp (g₁.comp gSource)) :=
    (G₁.compContinuousMap gSource).cast hgSource (by
      ext x
      rfl)
  have hProjectedRel :
      (p.comp (GrawLift.symm.trans G₁pre).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b')).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b))) :=
    projectedLiftComparisonRelRefl
      (p := p) (β₁ := β₁) (Graw := Graw) hGraw hgSource hgRaw (G₁ := G₁) hG₁
  have hRawToPre :
      ContinuousMap.Homotopic gRaw (g₁.comp gSource) := by
    -- Route correction: convert the projected comparison directly into an endpoint homotopy in
    -- the target fiber, instead of producing a stronger path-space comparison family.
    exact fiberEndpointHomotopic_of_projectedHomotopyRelConst
      (p := p) (F := GrawLift.symm.trans G₁pre) hProjectedRel
  have hPreToHonest :
      ContinuousMap.Homotopic (g₁.comp gSource) g₁ := by
    -- Cancel the source correction using the packaged homotopy `gSource ~ id`.
    simpa using ContinuousMap.Homotopic.symm
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g₁) hgSourceHom)
  exact ContinuousMap.Homotopic.trans hRawToPre hPreToHonest

/-- Helper for Definition 7.6.3: a raw lift over `β₁` together with a source-edge correction can
be rectified to an honest witness of `β₁` with homotopic endpoint map. -/
theorem existsRectifiedLiftWitnessOfSourceEdgeTransport
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₁ : Path b b'}
    {Graw : C(I × fiber p b, E)}
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap)
    (HSourceEdge : (fiberInclusion p b).Homotopy (Graw.curry 0))
    (hSourceEdge :
      p.comp HSourceEdge.toContinuousMap =
        (ContinuousMap.Homotopy.refl (ContinuousMap.const (fiber p b) b)).toContinuousMap)
    {gRaw : C(fiber p b, fiber p b')}
    (hgRaw : (fiberInclusion p b').comp gRaw = Graw.curry 1) :
    ∃ g₁ : C(fiber p b, fiber p b'),
      ∃ G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
        p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap ∧
          ContinuousMap.Homotopic gRaw g₁ := by
  rcases exists_fiberInclusionHomotopyLiftEndpoint (p := p) β₁ with ⟨g₁, G₁, hG₁⟩
  refine ⟨g₁, G₁, hG₁, ?_⟩
  -- Route correction: the file now closes the rectification step at the endpoint level, which is
  -- the only comparison consumed downstream.
  exact endpointHomotopicOfSourceEdgeTransport
    (p := p) (β₁ := β₁) (Graw := Graw) hGraw HSourceEdge hSourceEdge hgRaw
    (g₁ := g₁) (G₁ := G₁) hG₁

/-- Helper for Definition 7.6.3: a witness over `((Path.refl b).trans β).toHomotopyConst`
should transfer to a witness over `β.toHomotopyConst` with homotopic endpoint maps. -/
theorem existsFiberTranslationWitness_of_reflTrans
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} (β : Path b b')
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    (hG₀ : p.comp G₀.toContinuousMap = ((Path.refl b).trans β).toHomotopyConst.toContinuousMap) :
    ∃ g₁ : C(fiber p b, fiber p b'),
      ∃ G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
        p.comp G₁.toContinuousMap = β.toHomotopyConst.toContinuousMap ∧
          ContinuousMap.Homotopic g₀ g₁ := by
  rcases reflTransSourceEdgeAndTail (p := p) (β := β) (g₀ := g₀) (G₀ := G₀) hG₀ with
    ⟨Gtail, hGtail, HSourceEdge, hSourceEdge, hTailEndpoint⟩
  -- The left-unit normalization already produced exactly the raw lift and source-edge data
  -- needed by the rectification owner.
  simpa using
    existsRectifiedLiftWitnessOfSourceEdgeTransport
      (p := p) (β₁ := β) (Graw := Gtail) hGtail HSourceEdge hSourceEdge
      (gRaw := g₀) hTailEndpoint

/-- Helper for Definition 7.6.3: after building the unrestricted transport, the remaining task is
to rigidify its source face so that the transported endpoint map is represented by an actual lift
of `β₁.toHomotopyConst` starting at `fiberInclusion p b`. -/
theorem existsRectifiedLiftedWitnessOfBoundaryFixedTransport
    (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₀ β₁ : Path b b'}
    {Hβrel :
      ((β₀.toHomotopyConst (Y := fiber p b)).toContinuousMap).HomotopyRel
        ((β₁.toHomotopyConst (Y := fiber p b)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (fiber p b)))}
    {Graw : C(I × fiber p b, E)}
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    {Kraw : G₀.toContinuousMap.Homotopy Graw}
    {gRaw : C(fiber p b, fiber p b')}
    (hKraw : p.comp Kraw.toContinuousMap = Hβrel.toHomotopy.toContinuousMap)
    (hGraw : p.comp Graw = β₁.toHomotopyConst.toContinuousMap)
    (hgRaw : (fiberInclusion p b').comp gRaw = Graw.curry 1) :
    ∃ g₁ : C(fiber p b, fiber p b'),
      ∃ G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
        p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap ∧
          ContinuousMap.Homotopic gRaw g₁ := by
  -- Route correction: the endpoint theorem now consumes a single comparison family rather than
  -- trying to rectify the source edge implicitly inside the endpoint argument.
  rcases existsSourceEdgeHomotopyDataOfBoundaryFixedTransport (p := p) (Hβrel := Hβrel)
      (Graw := Graw) (g₀ := g₀) (G₀ := G₀) (Kraw := Kraw) hKraw hGraw with
    ⟨HSourceEdge, hSourceEdge⟩
  -- Route correction: instead of constructing a separate path-space comparison family, prepend
  -- the source-edge correction to the raw lift and then remove the trivial leading base segment.
  exact existsRectifiedLiftWitnessOfSourceEdgeTransport
    (p := p) (β₁ := β₁) (Graw := Graw) hGraw HSourceEdge hSourceEdge
    (gRaw := gRaw) hgRaw

/-- Helper for Definition 7.6.3: a lifted witness for `β₀` should transfer across a path
homotopy `hβ : β₀.Homotopic β₁` to a lifted witness for `β₁` with homotopic endpoint maps. -/
theorem existsFiberTranslationWitness_of_homotopic (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₀ β₁ : Path b b'} (hβ : β₀.Homotopic β₁)
    {g₀ : C(fiber p b, fiber p b')}
    {G₀ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₀)}
    (hG₀ : p.comp G₀.toContinuousMap = β₀.toHomotopyConst.toContinuousMap) :
    ∃ g₁ : C(fiber p b, fiber p b'),
      ∃ G₁ : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
        p.comp G₁.toContinuousMap = β₁.toHomotopyConst.toContinuousMap ∧
          ContinuousMap.Homotopic g₀ g₁ := by
  rcases existsUnrestrictedLiftedWitnessHomotopyOfHomotopic p hβ hG₀ with
    ⟨Hβrel, Graw, Kraw, hKraw, hGraw⟩
  rcases rawEndpointHomotopicOfBoundaryFixedTransport
      (p := p) (g₀ := g₀) (G₀ := G₀) (Hβrel := Hβrel) (Graw := Graw) (Kraw := Kraw)
      hKraw hGraw with ⟨gRaw, hgRaw, hg₀raw⟩
  rcases existsRectifiedLiftedWitnessOfBoundaryFixedTransport
      (p := p) (Hβrel := Hβrel) (Graw := Graw) (g₀ := g₀) (G₀ := G₀)
      (Kraw := Kraw) (gRaw := gRaw) hKraw hGraw hgRaw with ⟨g₁, G₁, hG₁, hgRaw₁⟩
  refine ⟨g₁, G₁, hG₁, ?_⟩
  -- Compose the unrestricted endpoint comparison with the remaining rectification step.
  exact ContinuousMap.Homotopic.trans hg₀raw hgRaw₁

/-- Helper for Definition 7.6.3: a represented translation class stays represented after
replacing a path by a homotopic path with the same endpoints. -/
theorem isFiberTranslationOfPath_of_homotopic (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B} {β₀ β₁ : Path b b'} (hβ : β₀.Homotopic β₁)
    (τ : fiberMapHomotopyClasses p b b') :
    IsFiberTranslationOfPath p β₀ τ → IsFiberTranslationOfPath p β₁ τ := by
  intro hτ
  rcases hτ with ⟨g₀, G₀, hG₀, hg₀τ⟩
  -- Transfer the chosen witness across the path homotopy.
  rcases existsFiberTranslationWitness_of_homotopic p hβ hG₀ with ⟨g₁, G₁, hG₁, hg⟩
  refine ⟨g₁, G₁, hG₁, ?_⟩
  -- Homotopic endpoint maps determine the same quotient class.
  calc
    (⟦g₁⟧ : fiberMapHomotopyClasses p b b') = ⟦g₀⟧ := by
      exact (endpointClass_eq_of_homotopic p hg).symm
    _ = τ := hg₀τ

/-- Endpoint-fixed homotopic paths determine the same translation classes. -/
theorem isFiberTranslationOfPath_iff_of_homotopic (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B}
    {β₀ β₁ : Path b b'} (hβ : β₀.Homotopic β₁) (τ : fiberMapHomotopyClasses p b b') :
    IsFiberTranslationOfPath p β₀ τ ↔ IsFiberTranslationOfPath p β₁ τ := by
  -- Reduce the equivalence to the one-direction transport lemma and symmetry of path homotopy.
  constructor
  · exact isFiberTranslationOfPath_of_homotopic p hβ τ
  · exact isFiberTranslationOfPath_of_homotopic p hβ.symm τ

/-- Definition 7.6.3: for a fibration `p : C(E, B)` and a path class
`[β] : Path.Homotopic.Quotient b b'`, a class `τ[β] : fiberMapHomotopyClasses p b b'` is a fiber
translation along `[β]` when it is represented by the endpoint map of a lifted homotopy of any
path representative of `[β]`. -/
def IsFiberTranslation (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path.Homotopic.Quotient b b') (τ : fiberMapHomotopyClasses p b b') : Prop :=
  Quotient.liftOn β
    (fun γ : Path b b' ↦ IsFiberTranslationOfPath p γ τ)
    (fun _ _ hγ ↦ propext (isFiberTranslationOfPath_iff_of_homotopic p hγ τ))

/-- Every path class in `Path.Homotopic.Quotient b b'` admits a represented fiber-translation
class. -/
theorem exists_isFiberTranslation (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path.Homotopic.Quotient b b') :
    ∃ τ : fiberMapHomotopyClasses p b b', IsFiberTranslation p β τ := by
  refine Quotient.inductionOn β ?_
  intro γ
  exact exists_isFiberTranslationOfPath p γ

/-- The canonical homotopy class of fiber translations along the path class `β`. -/
noncomputable def fiberTranslationClass (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path.Homotopic.Quotient b b') : fiberMapHomotopyClasses p b b' :=
  Classical.choose (exists_isFiberTranslation p β)

/-- `fiberTranslationClass p β` satisfies the defining translation property along `β`. -/
theorem isFiberTranslation_fiberTranslationClass (p : C(E, B)) [IsFibration.{u, v, u} p]
    {b b' : B}
    (β : Path.Homotopic.Quotient b b') :
    IsFiberTranslation p β (fiberTranslationClass p β) :=
  Classical.choose_spec (exists_isFiberTranslation p β)

/-- On a represented path class, `IsFiberTranslation` reduces to the path-level specification. -/
theorem isFiberTranslation_mk_iff (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path b b')
    (τ : fiberMapHomotopyClasses p b b') :
    IsFiberTranslation p (mk β) τ ↔ IsFiberTranslationOfPath p β τ :=
  Iff.rfl

/-- On a represented path class, `fiberTranslationClass p (mk β)` satisfies the path-level
translation specification from Construction 7.6.2. -/
theorem isFiberTranslationOfPath_fiberTranslationClass_mk (p : C(E, B))
    [IsFibration.{u, v, u} p] {b b' : B} (β : Path b b') :
    IsFiberTranslationOfPath p β (fiberTranslationClass p (mk β)) := by
  simpa [isFiberTranslation_mk_iff] using isFiberTranslation_fiberTranslationClass p (mk β)

/-- On a represented path class, Construction 7.6.2 still yields some fiber-translation class. -/
theorem exists_isFiberTranslation_mk (p : C(E, B)) [IsFibration.{u, v, u} p] {b b' : B}
    (β : Path b b') :
    ∃ τ : fiberMapHomotopyClasses p b b', IsFiberTranslation p (mk β) τ := by
  simpa [isFiberTranslation_mk_iff] using exists_isFiberTranslationOfPath p β
