import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Construction_7_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Problem_5_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_5

open scoped unitInterval

universe u v w

variable {ι : Type u} {E : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{w, w} B]

-- `lean_leansearch` points to `PartitionOfUnity` as the closest mathlib analogue for May's
-- numerability data. This item keeps `ContinuousMap.restrictPreimage` as the canonical restricted
-- map `p⁻¹(U) → U`.

/-- Helper for Theorem 7.4.3: restricting a fibration to an open subset of the base again yields a
fibration. -/
theorem isFibration_restrictPreimage_of_isFibration {p : C(E, B)}
    (hp : IsFibration.{v, w, max v w} p)
    (U : TopologicalSpace.Opens B) : IsFibration.{v, w, max v w} (p.restrictPreimage U) := by
  refine
    { toHasCoveringHomotopyProperty := ?_
      surjective := ?_ }
  · refine
      { homotopyLift := ?_ }
    intro A _ _ f₀ f₁ H g₀ hg₀
    -- Forget the subtype data, lift in the ambient fibration, and then repackage the image.
    let inclusion : C(U, B) := ⟨Subtype.val, continuous_subtype_val⟩
    let g₀Ambient : C(A, E) :=
      ⟨fun a ↦ (g₀ a).1, continuous_subtype_val.comp g₀.continuous⟩
    let HAmbient : (inclusion.comp f₀).Homotopy (inclusion.comp f₁) :=
      (ContinuousMap.Homotopy.refl inclusion).comp H
    have hg₀Ambient : p.comp g₀Ambient = inclusion.comp f₀ := by
      ext a
      simpa [g₀Ambient, inclusion, ContinuousMap.restrictPreimage] using
        congrArg Subtype.val (ContinuousMap.congr_fun hg₀ a)
    -- Local instance justification (instance bridge): `IsFibration.exists_homotopyLift`
    -- is stated via typeclass inference, and here the explicit hypothesis `hp` is the intended
    -- instance at the required universe specialization.
    letI : IsFibration.{v, w, max v w} p := hp
    obtain ⟨g₁Ambient, GAmbient, hGAmbient⟩ :=
      IsFibration.exists_homotopyLift (p := p) (A := A) (H := HAmbient) (g₀ := g₀Ambient)
        hg₀Ambient
    have g₁_mem : ∀ a : A, p (g₁Ambient a) ∈ U := by
      intro a
      have hproj :
          p (g₁Ambient a) = (f₁ a).1 := by
        calc
          p (g₁Ambient a) = p (GAmbient (1, a)) := by rw [GAmbient.apply_one]
          _ = HAmbient (1, a) := ContinuousMap.congr_fun hGAmbient (1, a)
          _ = (f₁ a).1 := by simp [HAmbient, inclusion]
      simpa [hproj] using (f₁ a).2
    let g₁ : C(A, p ⁻¹' U) :=
      ⟨fun a ↦ ⟨g₁Ambient a, g₁_mem a⟩, g₁Ambient.continuous.subtype_mk g₁_mem⟩
    have gAmbient_mem : ∀ z : I × A, p (GAmbient z) ∈ U := by
      intro z
      have hproj :
          p (GAmbient z) = (H z).1 := by
        simpa [HAmbient, inclusion] using ContinuousMap.congr_fun hGAmbient z
      simpa [hproj] using (H z).2
    let G : g₀.Homotopy g₁ :=
      { toFun := fun z ↦ ⟨GAmbient z, gAmbient_mem z⟩
        continuous_toFun := GAmbient.continuous.subtype_mk gAmbient_mem
        map_zero_left := by
          intro a
          apply Subtype.ext
          simpa [g₀Ambient] using GAmbient.apply_zero a
        map_one_left := by
          intro a
          apply Subtype.ext
          simpa [g₁] using GAmbient.apply_one a }
    refine ⟨g₁, G, ?_⟩
    -- Forgetting the subtype structure identifies the lifted restricted homotopy with `H`.
    ext z
    simpa [ContinuousMap.restrictPreimage, G, HAmbient, inclusion] using
      ContinuousMap.congr_fun hGAmbient z
  · intro b
    -- Lift the ambient base point first, then package the witness into the restricted fiber.
    rcases hp.surjective b.1 with ⟨e, he⟩
    refine ⟨⟨e, ?_⟩, ?_⟩
    · simpa [he] using b.2
    · apply Subtype.ext
      simpa [ContinuousMap.restrictPreimage] using he

/-- Helper for Theorem 7.4.3: if each restricted map over the members of a numerable open cover is
a fibration, then the original map is surjective. -/
theorem surjective_of_forall_restrictPreimage_isFibration (𝒰 : NumerableOpenCover ι B)
    (p : C(E, B)) (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) :
    Function.Surjective p := by
  intro b
  -- Choose a cover member containing `b`, then lift the subtype point in that restricted map.
  rcases 𝒰.exists_pos b with ⟨i, hi⟩
  have hb : b ∈ 𝒰.cover i := (𝒰.mem_cover_iff_pos i b).2 hi
  rcases (hlocal i).surjective ⟨b, hb⟩ with ⟨e, he⟩
  refine ⟨e.1, ?_⟩
  simpa [ContinuousMap.restrictPreimage] using congrArg Subtype.val he

/-- A basic patching neighborhood pulled back to the mapping-path space is a positive locus, so
it is compactly generated with its ordinary subtype topology. -/
theorem mappingPathPatchingOpen_uCompactlyGeneratedSpace
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {p : C(E, B)} (T : NumerableOpenCover.OrderedSubfamily ι) :
    UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} := by
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w}
      (MappingPathSpace p) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace p
  let weight : MappingPathSpace p → ℝ := fun x ↦
    (NumerableOpenCover.patchingWeight 𝒰 hcont T x.path : ℝ)
  have hweight : Continuous weight := by
    exact continuous_subtype_val.comp <|
      (NumerableOpenCover.patchingWeight 𝒰 hcont T).continuous.comp
        (mappingPathSpacePathContinuous p)
  change UCompactlyGeneratedSpace.{max v w} {x : MappingPathSpace p | 0 < weight x}
  exact Subtype.uCompactlyGeneratedSpaceOfContinuousPositive hweight

/-- Mapping paths that stay in one numerated cover member form the one-slot basic patching
neighborhood and hence carry the ordinary compactly generated subtype topology. -/
theorem singleCoverMappingPath_uCompactlyGeneratedSpace
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {p : C(E, B)} (i : ι) :
    UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} := by
  classical
  let T : NumerableOpenCover.OrderedSubfamily ι := ⟨[i], by simp⟩
  have hT : 0 < T.length := by
    simp [T, NumerableOpenCover.OrderedSubfamily.length,
      NumerableOpenCover.OrderedSubfamily.toList]
  have hiff (x : MappingPathSpace p) :
      (∀ t : I, x.path t ∈ 𝒰.cover i) ↔
        x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T := by
    rw [NumerableOpenCover.mem_patchingOpen_iff 𝒰 hcont hT]
    constructor
    · intro hx j t ht
      simpa [T, NumerableOpenCover.OrderedSubfamily.get,
        NumerableOpenCover.OrderedSubfamily.toList] using hx t
    · intro hx t
      let j : Fin T.length := ⟨0, hT⟩
      have ht : t ∈ T.patchingSlot j := by
        simpa only [T, j, NumerableOpenCover.OrderedSubfamily.patchingSlot,
          NumerableOpenCover.OrderedSubfamily.length,
          NumerableOpenCover.OrderedSubfamily.toList,
          NumerableOpenCover.patchingSlot, List.length_cons, List.length_nil,
          Nat.cast_zero, Nat.cast_one, zero_div, one_div, inv_one, zero_add] using t.2
      simpa [T, j, NumerableOpenCover.OrderedSubfamily.get,
        NumerableOpenCover.OrderedSubfamily.toList] using hx j t ht
  let e :
      {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} ≃ₜ
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} :=
    { toFun := fun x ↦ ⟨x.1, (hiff x.1).1 x.2⟩
      invFun := fun x ↦ ⟨x.1, (hiff x.1).2 x.2⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl
      continuous_toFun := continuous_subtype_val.subtype_mk fun x ↦ (hiff x.1).1 x.2
      continuous_invFun := continuous_subtype_val.subtype_mk fun x ↦ (hiff x.1).2 x.2 }
  let _ : UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} :=
    mappingPathPatchingOpen_uCompactlyGeneratedSpace 𝒰 hcont T
  exact uCompactlyGeneratedSpace_homeomorph e.symm

/-- Helper for Theorem 7.4.3: a path lifting function on a restricted map yields an ordinary lift
for any path that remains inside the chosen cover member. -/
theorem liftPathWithinCover (𝒰 : NumerableOpenCover ι B) {p : C(E, B)} {i : ι}
    (s : PathLiftingFunction (p.restrictPreimage (𝒰.cover i))) (x : MappingPathSpace p)
    (hx : ∀ t : I, x.path t ∈ 𝒰.cover i) :
    ∃ γ : C(I, E), γ 0 = x.point ∧ p.comp γ = x.path := by
  let liftedPath : C(I, 𝒰.cover i) :=
    ⟨fun t ↦ ⟨x.path t, hx t⟩, by fun_prop⟩
  have hx₀ : p x.point ∈ 𝒰.cover i := by
    simpa [x.path_zero_eq] using hx 0
  let liftedPoint : p ⁻¹' (𝒰.cover i) :=
    ⟨x.point, hx₀⟩
  have liftedStart :
      liftedPath 0 = (p.restrictPreimage (𝒰.cover i)) liftedPoint := by
    apply Subtype.ext
    simpa [liftedPath, liftedPoint, ContinuousMap.restrictPreimage] using x.path_zero_eq
  let liftedInput : MappingPathSpace (p.restrictPreimage (𝒰.cover i)) :=
    MappingPathSpace.mk liftedPoint liftedPath liftedStart
  let γ : C(I, E) :=
    ⟨fun t ↦ (s liftedInput t).1, by fun_prop⟩
  refine ⟨γ, ?_, ?_⟩
  · -- Evaluate the restricted lift at `0` and forget the subtype structure.
    simpa [γ, liftedInput, liftedPoint] using
      congrArg Subtype.val (s.apply_zero liftedInput)
  · -- Evaluate the restricted projection identity pointwise and forget the subtype structure.
    ext t
    have hproj_t :
        ((p.restrictPreimage (𝒰.cover i)) (s liftedInput t)).1 = (liftedPath t).1 :=
      congrArg Subtype.val <|
        congrArg (fun η : I → 𝒰.cover i ↦ η t) (s.proj_comp_eq liftedInput)
    calc
      p ((s liftedInput t).1) = ((p.restrictPreimage (𝒰.cover i)) (s liftedInput t)).1 := rfl
      _ = (liftedPath t).1 := hproj_t
      _ = x.path t := rfl

/-- Helper for Theorem 7.4.3: each restricted fibration contributes an ordinary path lifting
function on the corresponding cover member. -/
theorem nonempty_pathLiftingFunction_restrictPreimage (𝒰 : NumerableOpenCover ι B)
    (p : C(E, B))
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    (i : ι) :
    Nonempty (PathLiftingFunction (p.restrictPreimage (𝒰.cover i))) := by
  -- Expand the path-space criterion for the restricted fibration and forget continuity.
  rcases
      (IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction
        (p.restrictPreimage (𝒰.cover i))).1 (hlocal i) with
    ⟨_, ⟨s⟩⟩
  exact ⟨s.toPathLiftingFunction⟩

/-- Helper for Theorem 7.4.3: a mapping path pulls the numerable open cover back to an open cover
of `I`, and mathlib's subdivision lemma then gives a monotone breakpoint sequence subordinate to
that pulled-back cover. -/
theorem existsSubdivisionWithinCover (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (x : MappingPathSpace p) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ n ≥ N, t n = 1) ∧
      ∀ n : ℕ, ∃ i : ι, Set.Icc (t n) (t (n + 1)) ⊆ x.path ⁻¹' (𝒰.cover i) := by
  let c : ι → Set I := fun i ↦ x.path ⁻¹' (𝒰.cover i)
  have hc_open : ∀ i : ι, IsOpen (c i) := by
    intro i
    simpa [c] using (𝒰.cover i).isOpen.preimage x.path.continuous
  have hc_cover : Set.univ ⊆ ⋃ i : ι, c i := by
    intro s _
    rcases 𝒰.isOpenCover.exists_mem (x.path s) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, htop, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  refine ⟨t, ht0, hmono, htop, ?_⟩
  intro n
  rcases hsub n with ⟨i, hi⟩
  exact ⟨i, hi⟩

/-- Helper for Theorem 7.4.3: if a segment of the base path stays inside one member of the cover,
then a chosen restricted path lifting function lifts that whole segment from any chosen lift of
its left endpoint. -/
theorem liftSegmentWithinCover (𝒰 : NumerableOpenCover ι B) {p : C(E, B)} {i : ι}
    (s : PathLiftingFunction (p.restrictPreimage (𝒰.cover i))) (x : MappingPathSpace p)
    {a b : I} (hab : (a : ℝ) < b) {e₀ : E} (he₀ : p e₀ = x.path a)
    (hx :
      ∀ z : Set.Icc (a : ℝ) (b : ℝ),
        x.path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ ∈ 𝒰.cover i) :
    ∃ γ : C(Set.Icc (a : ℝ) (b : ℝ), E),
      γ ⟨a, Set.left_mem_Icc.2 hab.le⟩ = e₀ ∧
        ∀ z : Set.Icc (a : ℝ) (b : ℝ),
          p (γ z) = x.path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ := by
  let intervalHomeomorph : Set.Icc (a : ℝ) (b : ℝ) ≃ₜ I :=
    iccHomeoI (a : ℝ) (b : ℝ) hab
  let intervalToUnit : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ⟨intervalHomeomorph, intervalHomeomorph.continuous_toFun⟩
  let unitToInterval : C(I, Set.Icc (a : ℝ) (b : ℝ)) :=
    ⟨intervalHomeomorph.symm, intervalHomeomorph.symm.continuous_toFun⟩
  let intervalInclusion : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ContinuousMap.inclusion fun z hz ↦
      ⟨le_trans a.2.1 hz.1, le_trans hz.2 b.2.2⟩
  let segmentPath : C(I, B) := x.path.comp (intervalInclusion.comp unitToInterval)
  have hsegmentStart : segmentPath 0 = p e₀ := by
    -- The reparameterized segment starts at `a`, so the prescribed lift starts at `e₀`.
    calc
      segmentPath 0 = x.path (intervalInclusion (unitToInterval 0)) := rfl
      _ = x.path a := by
        have hleftReal :
            (((unitToInterval 0 : Set.Icc (a : ℝ) (b : ℝ)) : ℝ)) = a := by
          simpa [unitToInterval, intervalHomeomorph] using
            iccHomeoI_symm_apply_coe (a : ℝ) (b : ℝ) hab (0 : I)
        have hleft :
            intervalInclusion (unitToInterval 0) = a := by
          apply Subtype.ext
          simpa [intervalInclusion] using hleftReal
        simpa [hleft]
      _ = p e₀ := he₀.symm
  have hsegmentMem : ∀ t : I, segmentPath t ∈ 𝒰.cover i := by
    -- Every parameter value lands in the chosen subinterval, so the segment stays in one cover
    -- member by hypothesis.
    intro t
    simpa [segmentPath, intervalInclusion, unitToInterval] using hx (unitToInterval t)
  let segmentInput : MappingPathSpace p := MappingPathSpace.mk e₀ segmentPath hsegmentStart
  obtain ⟨δ, hδ₀, hδproj⟩ := liftPathWithinCover 𝒰 s segmentInput hsegmentMem
  let γ : C(Set.Icc (a : ℝ) (b : ℝ), E) := δ.comp intervalToUnit
  refine ⟨γ, ?_, ?_⟩
  · -- Evaluate the lifted segment at the left endpoint of the interval.
    calc
      γ ⟨a, Set.left_mem_Icc.2 hab.le⟩ = δ (intervalToUnit ⟨a, Set.left_mem_Icc.2 hab.le⟩) := rfl
      _ = δ 0 := by
        congr
        apply Subtype.ext
        simp [intervalToUnit, intervalHomeomorph]
      _ = e₀ := hδ₀
  · -- Projecting the lifted segment back to `B` recovers the original path on the interval.
    intro z
    calc
      p (γ z) = segmentPath (intervalToUnit z) := by
        simpa [γ] using ContinuousMap.congr_fun hδproj (intervalToUnit z)
      _ = x.path (intervalInclusion (unitToInterval (intervalToUnit z))) := rfl
      _ = x.path (intervalInclusion z) := by
        congr
        exact intervalHomeomorph.symm_apply_apply z
      _ = x.path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ := rfl

/-- Helper for Theorem 7.4.3: `x.path` restricted to a closed subinterval of `I`. -/
def mappingPathInterval {p : C(E, B)} (x : MappingPathSpace p) (a b : I)
    (hab : (a : ℝ) ≤ b) : C(Set.Icc (a : ℝ) (b : ℝ), B) :=
  x.path.comp <|
    ContinuousMap.inclusion fun z hz ↦
      ⟨le_trans a.2.1 hz.1, le_trans hz.2 b.2.2⟩

/-- Helper for Theorem 7.4.3: evaluating the restricted path just forgets the interval subtype. -/
@[simp] theorem mappingPathInterval_apply {p : C(E, B)} (x : MappingPathSpace p) (a b : I)
    (hab : (a : ℝ) ≤ b) (z : Set.Icc (a : ℝ) (b : ℝ)) :
    mappingPathInterval x a b hab z =
      x.path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ :=
  rfl

/-- Helper for Theorem 7.4.3: the left endpoint of a closed interval in `I`, viewed in the
corresponding real interval subtype. -/
def intervalLeftEndpoint (a b : I) (hab : (a : ℝ) ≤ b) : Set.Icc (a : ℝ) (b : ℝ) :=
  ⟨a, Set.left_mem_Icc.2 hab⟩

/-- Helper for Theorem 7.4.3: the right endpoint of a closed interval in `I`, viewed in the
corresponding real interval subtype. -/
def intervalRightEndpoint (a b : I) (hab : (a : ℝ) ≤ b) : Set.Icc (a : ℝ) (b : ℝ) :=
  ⟨b, Set.right_mem_Icc.2 hab⟩

/-- Helper for Theorem 7.4.3: the left endpoint of the full unit interval is the ordinary zero
point of `I`. -/
@[simp] theorem intervalLeftEndpoint_zero_one :
    intervalLeftEndpoint (0 : I) 1 (show ((0 : I) : ℝ) ≤ 1 by simp) = (0 : I) := by
  apply Subtype.ext
  rfl

/-- Helper for Theorem 7.4.3: the restricted path at the left endpoint is the original path at
that endpoint. -/
@[simp] theorem mappingPathInterval_leftEndpoint {p : C(E, B)} (x : MappingPathSpace p) (a b : I)
    (hab : (a : ℝ) ≤ b) :
    mappingPathInterval x a b hab (intervalLeftEndpoint a b hab) = x.path a := by
  rfl

/-- Helper for Theorem 7.4.3: the restricted path at the right endpoint is the original path at
that endpoint. -/
@[simp] theorem mappingPathInterval_rightEndpoint {p : C(E, B)} (x : MappingPathSpace p) (a b : I)
    (hab : (a : ℝ) ≤ b) :
    mappingPathInterval x a b hab (intervalRightEndpoint a b hab) = x.path b := by
  rfl

/-- Helper for Theorem 7.4.3: restricting to the whole unit interval does not change the mapping
path. -/
@[simp] theorem mappingPathInterval_zero_one {p : C(E, B)} (x : MappingPathSpace p) :
    mappingPathInterval x 0 1 (show ((0 : I) : ℝ) ≤ 1 by simp) = x.path := by
  -- On `Set.Icc (0 : ℝ) 1 = I`, the restriction map is the identity.
  ext z
  rfl

/-- Helper for Theorem 7.4.3: the left subinterval includes into the combined adjacent interval. -/
def intervalInclusionLeft (a b c : I) (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c) :
    C(Set.Icc (a : ℝ) (b : ℝ), Set.Icc (a : ℝ) (c : ℝ)) :=
  ContinuousMap.inclusion fun z hz ↦ ⟨hz.1, le_trans hz.2 hbc⟩

/-- Helper for Theorem 7.4.3: the right subinterval includes into the combined adjacent interval. -/
def intervalInclusionRight (a b c : I) (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c) :
    C(Set.Icc (b : ℝ) (c : ℝ), Set.Icc (a : ℝ) (c : ℝ)) :=
  ContinuousMap.inclusion fun z hz ↦ ⟨le_trans hab hz.1, hz.2⟩

/-- Helper for Theorem 7.4.3: restricting the full interval path to the left adjacent subinterval
recovers the left segment path. -/
theorem mappingPathInterval_comp_intervalInclusionLeft {p : C(E, B)} (x : MappingPathSpace p)
    {a b c : I} (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c) :
    mappingPathInterval x a b hab =
      (mappingPathInterval x a c (le_trans hab hbc)).comp (intervalInclusionLeft a b c hab hbc) := by
  -- Both sides evaluate by forgetting the subtype information on the same left interval point.
  ext z
  rfl

/-- Helper for Theorem 7.4.3: restricting the full interval path to the right adjacent
subinterval recovers the right segment path. -/
theorem mappingPathInterval_comp_intervalInclusionRight {p : C(E, B)} (x : MappingPathSpace p)
    {a b c : I} (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c) :
    mappingPathInterval x b c hbc =
      (mappingPathInterval x a c (le_trans hab hbc)).comp (intervalInclusionRight a b c hab hbc) := by
  -- Both sides evaluate by forgetting the subtype information on the same right interval point.
  ext z
  rfl

/-- Helper for Theorem 7.4.3: concatenating compatible lifts on adjacent closed intervals keeps
the same initial point and the same projected base path on the combined interval. -/
theorem concatAdjacentIntervalLifts {p : C(E, B)} {a b c : I}
    (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c) {e₀ : E}
    {γ₁ : C(Set.Icc (a : ℝ) (b : ℝ), E)} {γ₂ : C(Set.Icc (b : ℝ) (c : ℝ), E)}
    {β : C(Set.Icc (a : ℝ) (c : ℝ), B)}
    (hstart : γ₁ (intervalLeftEndpoint a b hab) = e₀)
    (hcompat :
      γ₁ (intervalRightEndpoint a b hab) = γ₂ (intervalLeftEndpoint b c hbc))
    (hleft : p.comp γ₁ = β.comp (intervalInclusionLeft a b c hab hbc))
    (hright : p.comp γ₂ = β.comp (intervalInclusionRight a b c hab hbc)) :
    ∃ γ : C(Set.Icc (a : ℝ) (c : ℝ), E),
      γ (intervalLeftEndpoint a c (le_trans hab hbc)) = e₀ ∧ p.comp γ = β := by
  -- Local instance justification (interval order facts): `ContinuousMap.concat` is parameterized
  -- by `Fact` instances for the two adjoining order inequalities.
  letI : Fact ((a : ℝ) ≤ (b : ℝ)) := ⟨hab⟩
  letI : Fact ((b : ℝ) ≤ (c : ℝ)) := ⟨hbc⟩
  refine ⟨ContinuousMap.concat γ₁ γ₂, ?_, ?_⟩
  · -- Evaluate the concatenation at the left endpoint using the left-piece formula.
    calc
      ContinuousMap.concat γ₁ γ₂ (intervalLeftEndpoint a c (le_trans hab hbc)) =
          γ₁ (intervalLeftEndpoint a b hab) := by
        simpa [intervalLeftEndpoint] using
          (ContinuousMap.concat_left (f := γ₁) (g := γ₂) hcompat
            (t := intervalLeftEndpoint a c (le_trans hab hbc)) hab)
      _ = e₀ := hstart
  · -- Compare the projected concatenation with `β` separately on the left and right subintervals.
    ext z
    by_cases hz : (z : ℝ) ≤ b
    · have hleftEval := ContinuousMap.congr_fun hleft ⟨z.1, z.2.1, hz⟩
      calc
        (p.comp (ContinuousMap.concat γ₁ γ₂)) z = p ((ContinuousMap.concat γ₁ γ₂) z) := rfl
        _ = p (γ₁ ⟨z.1, z.2.1, hz⟩) := by
          rw [ContinuousMap.concat_left (f := γ₁) (g := γ₂) hcompat hz]
        _ = β z := by
          simpa [intervalInclusionLeft] using hleftEval
    · have hz' : (b : ℝ) ≤ z := le_of_not_ge hz
      have hrightEval := ContinuousMap.congr_fun hright ⟨z.1, hz', z.2.2⟩
      calc
        (p.comp (ContinuousMap.concat γ₁ γ₂)) z = p ((ContinuousMap.concat γ₁ γ₂) z) := rfl
        _ = p (γ₂ ⟨z.1, hz', z.2.2⟩) := by
          rw [ContinuousMap.concat_right (f := γ₁) (g := γ₂) hcompat hz']
        _ = β z := by
          simpa [intervalInclusionRight] using hrightEval

/-- Helper for Theorem 7.4.3: transporting a lift across an equality of closed interval domains
preserves both the initial point equation and the projected base path equation. -/
theorem transportLiftAlongIccEq {p : C(E, B)} (x : MappingPathSpace p)
    {a b a' b' : I} (hab : (a : ℝ) ≤ b) (ha'b' : (a' : ℝ) ≤ b')
    (hIcc : Set.Icc (a : ℝ) b = Set.Icc (a' : ℝ) b')
    {γ : C(Set.Icc (a : ℝ) (b : ℝ), E)}
    (hγ₀ : γ (intervalLeftEndpoint a b hab) = x.point)
    (hγproj : p.comp γ = mappingPathInterval x a b hab) :
    ∃ γ' : C(Set.Icc (a' : ℝ) (b' : ℝ), E),
      γ' (intervalLeftEndpoint a' b' ha'b') = x.point ∧
        p.comp γ' = mappingPathInterval x a' b' ha'b' := by
  let castInterval : C(Set.Icc (a' : ℝ) (b' : ℝ), Set.Icc (a : ℝ) (b : ℝ)) :=
    ContinuousMap.inclusion hIcc.symm.subset
  refine ⟨γ.comp castInterval, ?_, ?_⟩
  · -- The transported lift still starts at the same left endpoint after reindexing the interval.
    have hleftReal : (a' : ℝ) = a := by
      have ha' : (a' : ℝ) ∈ Set.Icc (a : ℝ) b := by
        simpa [hIcc] using (Set.left_mem_Icc.2 ha'b' : (a' : ℝ) ∈ Set.Icc (a' : ℝ) b')
      have ha : (a : ℝ) ∈ Set.Icc (a' : ℝ) b' := by
        simpa [hIcc] using (Set.left_mem_Icc.2 hab : (a : ℝ) ∈ Set.Icc (a : ℝ) b)
      apply le_antisymm
      · exact ha.1
      · exact ha'.1
    have hleft :
        castInterval (intervalLeftEndpoint a' b' ha'b') = intervalLeftEndpoint a b hab := by
      apply Subtype.ext
      simpa [intervalLeftEndpoint] using hleftReal
    simpa [castInterval, hleft] using hγ₀
  · -- The transported lift still projects to the same base path after reindexing the domain.
    ext z
    simpa [castInterval, mappingPathInterval, hIcc] using
      ContinuousMap.congr_fun hγproj (castInterval z)

/-- Helper for Theorem 7.4.3: a lift over each subdivision slot inductively extends to a lift over
every initial subdivision prefix. -/
theorem existsLiftOnSubdivisionPrefix (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (x : MappingPathSpace p) (t : ℕ → I) (ht0 : t 0 = 0) (hmono : Monotone t)
    (slot : ℕ → ι)
    (hslot : ∀ n : ℕ, Set.Icc (t n) (t (n + 1)) ⊆ x.path ⁻¹' (𝒰.cover (slot n)))
    (s : ∀ i : ι, PathLiftingFunction (p.restrictPreimage (𝒰.cover i))) :
    ∀ m : ℕ, ∃ γ : C(Set.Icc (t 0 : ℝ) (t m : ℝ), E),
      γ (intervalLeftEndpoint (t 0) (t m) (hmono (Nat.zero_le m))) = x.point ∧
        p.comp γ = mappingPathInterval x (t 0) (t m) (hmono (Nat.zero_le m)) := by
  intro m
  induction m with
  | zero =>
      refine ⟨ContinuousMap.const _ x.point, ?_, ?_⟩
      · -- The constant lift on the degenerate initial interval starts at the chosen point.
        rfl
      · -- On the degenerate interval, the base path is constant with value `p x.point`.
        ext z
        have hz : z = intervalLeftEndpoint (t 0) (t 0) (hmono (Nat.zero_le 0)) := by
          apply Subtype.ext
          exact le_antisymm z.2.2 z.2.1
        calc
          (p.comp (ContinuousMap.const _ x.point)) z = p x.point := rfl
          _ = x.path (t 0) := by simpa [ht0] using x.path_zero_eq.symm
          _ = mappingPathInterval x (t 0) (t 0) (hmono (Nat.zero_le 0))
                (intervalLeftEndpoint (t 0) (t 0) (hmono (Nat.zero_le 0))) := by
              simpa using
                (mappingPathInterval_leftEndpoint x (t 0) (t 0) (hmono (Nat.zero_le 0))).symm
          _ = mappingPathInterval x (t 0) (t 0) (hmono (Nat.zero_le 0)) z := by
              rw [hz]
  | succ m hm =>
      rcases hm with ⟨γ, hγ₀, hγproj⟩
      have htm : (t m : ℝ) ≤ t (m + 1) := hmono (Nat.le_succ m)
      cases eq_or_lt_of_le htm with
      | inl hdeg =>
          -- Route correction: a degenerate subdivision step contributes no new segment; just reuse
          -- the previous prefix lift after transporting it across the equal interval domains.
          have hIcc :
              Set.Icc (t 0 : ℝ) (t m : ℝ) = Set.Icc (t 0 : ℝ) (t (m + 1) : ℝ) := by
            simpa [hdeg]
          exact
            transportLiftAlongIccEq x (hmono (Nat.zero_le m)) (hmono (Nat.zero_le (m + 1)))
              hIcc hγ₀ hγproj
      | inr hlt =>
          have hγright :
              p (γ (intervalRightEndpoint (t 0) (t m) (hmono (Nat.zero_le m)))) = x.path (t m) := by
            -- Evaluate the prefix projection identity at the right endpoint of the current prefix.
            simpa using
              ContinuousMap.congr_fun hγproj
                (intervalRightEndpoint (t 0) (t m) (hmono (Nat.zero_le m)))
          obtain ⟨γseg, hseg₀, hsegproj⟩ :=
            liftSegmentWithinCover 𝒰 (s (slot m)) x hlt hγright
              (fun z ↦ hslot m z.2)
          have hcompat :
              γ (intervalRightEndpoint (t 0) (t m) (hmono (Nat.zero_le m))) =
                γseg (intervalLeftEndpoint (t m) (t (m + 1)) htm) := by
            -- The new segment starts exactly at the current prefix endpoint.
            simpa using hseg₀.symm
          have hleft :
              p.comp γ =
                (mappingPathInterval x (t 0) (t (m + 1)) (hmono (Nat.zero_le (m + 1)))).comp
                  (intervalInclusionLeft (t 0) (t m) (t (m + 1))
                    (hmono (Nat.zero_le m)) htm) := by
            -- Rewrite the left piece as a restriction of the longer interval path.
            calc
              p.comp γ = mappingPathInterval x (t 0) (t m) (hmono (Nat.zero_le m)) := hγproj
              _ =
                  (mappingPathInterval x (t 0) (t (m + 1)) (hmono (Nat.zero_le (m + 1)))).comp
                    (intervalInclusionLeft (t 0) (t m) (t (m + 1))
                      (hmono (Nat.zero_le m)) htm) :=
                mappingPathInterval_comp_intervalInclusionLeft x
                  (hmono (Nat.zero_le m)) htm
          have hright :
              p.comp γseg =
                (mappingPathInterval x (t 0) (t (m + 1)) (hmono (Nat.zero_le (m + 1)))).comp
                  (intervalInclusionRight (t 0) (t m) (t (m + 1))
                    (hmono (Nat.zero_le m)) htm) := by
            -- Rewrite the new segment path as the right restriction of the longer interval path.
            calc
              p.comp γseg = mappingPathInterval x (t m) (t (m + 1)) htm := by
                ext z
                simpa [mappingPathInterval] using hsegproj z
              _ =
                  (mappingPathInterval x (t 0) (t (m + 1)) (hmono (Nat.zero_le (m + 1)))).comp
                    (intervalInclusionRight (t 0) (t m) (t (m + 1))
                      (hmono (Nat.zero_le m)) htm) :=
                mappingPathInterval_comp_intervalInclusionRight x
                  (hmono (Nat.zero_le m)) htm
          -- Append the new lifted segment to the existing prefix lift.
          exact
            concatAdjacentIntervalLifts (p := p)
              (a := t 0) (b := t m) (c := t (m + 1))
              (hmono (Nat.zero_le m)) htm hγ₀ hcompat hleft hright

/-- Helper for Theorem 7.4.3: a subdivision subordinate to the pulled-back cover yields a global
lift of the whole mapping path. -/
theorem existsLiftOfSubordinateSubdivision (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    (x : MappingPathSpace p) :
    ∃ γ : C(I, E), γ 0 = x.point ∧ p.comp γ = x.path := by
  classical
  obtain ⟨t, ht0, hmono, htop, hslot⟩ := existsSubdivisionWithinCover 𝒰 x
  choose slot hslot using hslot
  let s : ∀ i : ι, PathLiftingFunction (p.restrictPreimage (𝒰.cover i)) :=
    fun i ↦ Classical.choice (nonempty_pathLiftingFunction_restrictPreimage 𝒰 p hlocal i)
  obtain ⟨N, hNtop⟩ := htop
  have hN : t N = 1 := hNtop N le_rfl
  obtain ⟨γ, hγ₀, hγproj⟩ :=
    existsLiftOnSubdivisionPrefix 𝒰 x t ht0 hmono slot hslot s N
  -- Read the terminal prefix lift as a lift on `I` by rewriting `t 0 = 0` and `t N = 1`.
  have hIcc : Set.Icc (t 0 : ℝ) (t N : ℝ) = Set.Icc (0 : ℝ) 1 := by
    simpa [ht0, hN]
  obtain ⟨γI, hγI₀, hγIproj⟩ :=
    transportLiftAlongIccEq (p := p) (x := x) (a := t 0) (b := t N) (a' := (0 : I)) (b' := 1)
      (hmono (Nat.zero_le N)) (show ((0 : I) : ℝ) ≤ 1 by simp) hIcc hγ₀ hγproj
  refine ⟨γI, ?_, ?_⟩
  · simpa using hγI₀
  · simpa using hγIproj

/-- Helper for Theorem 7.4.3: if each restriction of `p` to a cover member is a fibration, then
every mapping path for `p` admits some lift. -/
theorem existsLift_of_forall_restrictPreimage_isFibration (𝒰 : NumerableOpenCover ι B)
    (p : C(E, B))
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    (x : MappingPathSpace p) :
    ∃ γ : C(I, E), γ 0 = x.point ∧ p.comp γ = x.path := by
  -- Route correction: solve the pointwise lifting problem by prefix induction on a subdivision
  -- subordinate to the pulled-back cover, then read the terminal prefix as a lift on `I`.
  exact existsLiftOfSubordinateSubdivision 𝒰 hlocal x

/-- Helper for Theorem 7.4.3: a continuous path lifting function on the restriction
`p⁻¹(𝒰.cover i) → 𝒰.cover i` induces a continuous family of ambient lifts on the subtype of
mapping paths that remain inside `𝒰.cover i`. -/
theorem continuousLiftWithinSingleCover (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) (i : ι) :
    ∃ lift :
        C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  classical
  let _ : UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} :=
    singleCoverMappingPath_uCompactlyGeneratedSpace 𝒰 hcont i
  rcases
      (IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction
        (p.restrictPreimage (𝒰.cover i))).1 (hlocal i) with
    ⟨_, ⟨s⟩⟩
  let ambientInclusion : C(p ⁻¹' (𝒰.cover i), E) := ⟨Subtype.val, continuous_subtype_val⟩
  let forgetRestrictedPaths : C(C(I, p ⁻¹' (𝒰.cover i)), C(I, E)) :=
    ⟨ContinuousMap.comp ambientInclusion, ContinuousMap.continuous_postcomp ambientInclusion⟩
  let restrictedInput :
      C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        MappingPathSpace (p.restrictPreimage (𝒰.cover i))) := by
    let pointMap : C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p ⁻¹' (𝒰.cover i)) :=
      { toFun := fun x ↦
          ⟨x.1.point, by
            -- Membership of the starting point follows from the defining equation at `0`.
            simpa [x.1.path_zero_eq] using x.2 0⟩
        continuous_toFun := by
          -- The point coordinate is the first ambient projection, then packaged into the fiber.
          have hpoint :
              Continuous fun x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} ↦
                x.1.point := by
            simpa [MappingPathSpace.point] using
              (continuous_fst.comp
                ((MappingPathSpace.continuous_subtypeVal (p := p)).comp continuous_subtype_val) :
                Continuous fun x :
                    {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} ↦
                  (((x : MappingPathSpace p) : E × C(I, B)).1))
          exact hpoint.subtype_mk fun x ↦ by
            simpa [x.1.path_zero_eq] using x.2 0 }
    let pathMap : C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        C(I, 𝒰.cover i)) :=
      { toFun := fun x ↦
          ⟨fun t ↦ ⟨x.1.path t, x.2 t⟩,
            x.1.path.continuous.subtype_mk fun t ↦ x.2 t⟩
        continuous_toFun := by
          -- Continuity into the compact-open function space is proved on the uncurried map.
          refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
          refine Continuous.subtype_mk ?_ fun y ↦ y.1.2 y.2
          have hpath :
              Continuous fun x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} ↦
                x.1.path := by
            simpa [MappingPathSpace.path] using
              (continuous_snd.comp
                ((MappingPathSpace.continuous_subtypeVal (p := p)).comp continuous_subtype_val) :
                Continuous fun x :
                    {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} ↦
                  (((x : MappingPathSpace p) : E × C(I, B)).2))
          have huncurry :
              Continuous fun y :
                  ({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i} × I) ↦
                y.1.1.path y.2 := by
            exact continuous_eval.comp ((hpath.comp continuous_fst).prodMk continuous_snd)
          simpa using huncurry }
    refine
      { toFun := fun x ↦ MappingPathSpace.mk (pointMap x) (pathMap x) ?_
        continuous_toFun := ?_ }
    · -- The restricted mapping path starts at the restricted starting point.
      apply Subtype.ext
      simpa [pointMap, pathMap, ContinuousMap.restrictPreimage] using x.1.path_zero_eq
    · -- Package the point and path maps into the subtype defining `MappingPathSpace`.
      exact
        MappingPathSpace.continuous_mk pointMap.continuous pathMap.continuous fun x ↦ by
          apply Subtype.ext
          simpa [pointMap, pathMap, ContinuousMap.restrictPreimage] using x.1.path_zero_eq
  let lift :
      C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)) :=
    forgetRestrictedPaths.comp (s.toContinuousMap.comp restrictedInput)
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Forget the subtype value in the local lift's source equation.
    simpa [lift, forgetRestrictedPaths, ambientInclusion, restrictedInput] using
      congrArg Subtype.val (s.source_eq (restrictedInput x))
  · intro x
    -- Evaluate the restricted projection identity pointwise and forget the subtype path values.
    ext t
    have hproj_t :
        p (((s.toContinuousMap (restrictedInput x)) t).1) = x.1.path t := by
      simpa [restrictedInput, ContinuousMap.restrictPreimage] using
        congrArg Subtype.val <|
          congrArg (fun η : I → 𝒰.cover i ↦ η t) (s.proj_comp_eq (restrictedInput x))
    simpa [lift, forgetRestrictedPaths, ambientInclusion] using hproj_t

/-- Helper for Theorem 7.4.3: a continuous family of paths that stays inside one cover member
admits a continuous family of lifts with the prescribed starting points. -/
theorem continuousLiftFromSingleCoverFamily (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) (i : ι)
    {X : Type*} [TopologicalSpace X] [UCompactlyGeneratedSpace.{max v w} X]
    (point : C(X, E)) (path : C(X, C(I, B)))
    (hstart : ∀ x, path x 0 = p (point x))
    (hmem : ∀ x (t : I), path x t ∈ 𝒰.cover i) :
    ∃ lift : C(X, C(I, E)), (∀ x, lift x 0 = point x) ∧ (∀ x, p.comp (lift x) = path x) := by
  rcases continuousLiftWithinSingleCover 𝒰 hcont hlocal i with ⟨localLift, hsource, hproj⟩
  let mappingPathFamily : C(X, MappingPathSpace p) :=
    { toFun := fun x ↦ MappingPathSpace.mk (point x) (path x) (hstart x)
      continuous_toFun := by
        -- Package the starting-point and path families into `MappingPathSpace p`.
        exact MappingPathSpace.continuous_mk point.continuous path.continuous hstart }
  let coveredFamily : C(X, {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}) :=
    { toFun := fun x ↦ ⟨mappingPathFamily x, fun t ↦ hmem x t⟩
      continuous_toFun := by
        -- Strengthen the mapping-path family to the subtype cut out by the cover member.
        exact mappingPathFamily.continuous.subtype_mk fun x ↦ hmem x }
  let lift : C(X, C(I, E)) := localLift.comp coveredFamily
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- The single-cover lifting function starts at the supplied starting-point family.
    simpa [lift, coveredFamily, mappingPathFamily] using hsource (coveredFamily x)
  · intro x
    -- Projecting the lifted family back to `B` recovers the supplied base-path family.
    simpa [lift, coveredFamily, mappingPathFamily] using hproj (coveredFamily x)

/-- Helper for Theorem 7.4.3: a continuous family of mapping paths whose restriction to a fixed
closed subinterval stays inside one cover member admits a continuous family of lifts on that
subinterval with the prescribed left endpoints. -/
theorem continuousLiftSegmentWithinCoverFamily (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) (i : ι)
    {X : Type*} [TopologicalSpace X] [UCompactlyGeneratedSpace.{max v w} X]
    (family : C(X, MappingPathSpace p)) {a b : I}
    (hab : (a : ℝ) < b) (point : C(X, E))
    (hstart : ∀ x, p (point x) = (family x).path a)
    (hmem :
      ∀ x (z : Set.Icc (a : ℝ) (b : ℝ)),
        (family x).path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ ∈ 𝒰.cover i) :
    ∃ lift : C(X, C(Set.Icc (a : ℝ) (b : ℝ), E)),
      (∀ x, lift x (intervalLeftEndpoint a b hab.le) = point x) ∧
        (∀ x, p.comp (lift x) = mappingPathInterval (family x) a b hab.le) := by
  let intervalHomeomorph : Set.Icc (a : ℝ) (b : ℝ) ≃ₜ I := iccHomeoI (a : ℝ) (b : ℝ) hab
  let intervalToUnit : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ⟨intervalHomeomorph, intervalHomeomorph.continuous_toFun⟩
  let unitToInterval : C(I, Set.Icc (a : ℝ) (b : ℝ)) :=
    ⟨intervalHomeomorph.symm, intervalHomeomorph.symm.continuous_toFun⟩
  let intervalInclusion : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ContinuousMap.inclusion fun z hz ↦
      ⟨le_trans a.2.1 hz.1, le_trans hz.2 b.2.2⟩
  let segmentIntervalFamily : C(X, C(Set.Icc (a : ℝ) (b : ℝ), B)) :=
    { toFun := fun x ↦ mappingPathInterval (family x) a b hab.le
      continuous_toFun := by
        -- Restrict the bundled family of mapping paths to the chosen interval.
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        have hpath :
            Continuous fun x : X ↦ (family x).path := by
          simpa using
            (continuous_snd.comp
              ((MappingPathSpace.continuous_subtypeVal (p := p)).comp family.continuous) :
              Continuous fun x : X ↦ (((family x : MappingPathSpace p) : E × C(I, B)).2))
        have huncurry :
            Continuous fun y : X × Set.Icc (a : ℝ) (b : ℝ) ↦
              (family y.1).path (intervalInclusion y.2) := by
          simpa using
            (continuous_eval.comp <|
              (hpath.comp continuous_fst).prodMk (intervalInclusion.continuous.comp continuous_snd))
        simpa [mappingPathInterval, intervalInclusion] using huncurry }
  let segmentPath : C(X, C(I, B)) :=
    { toFun := fun x ↦ (segmentIntervalFamily x).comp unitToInterval
      continuous_toFun := by
        -- Reparameterize the interval family back to the unit interval expected by the local API.
        exact (ContinuousMap.continuous_precomp unitToInterval).comp
          segmentIntervalFamily.continuous }
  have hsegmentStart : ∀ x, segmentPath x 0 = p (point x) := by
    intro x
    -- The reparameterized interval path starts at the original left endpoint.
    have hleftReal :
        (((unitToInterval 0 : Set.Icc (a : ℝ) (b : ℝ)) : ℝ)) = a := by
      simpa [unitToInterval, intervalHomeomorph] using
        iccHomeoI_symm_apply_coe (a : ℝ) (b : ℝ) hab (0 : I)
    have hleft :
        unitToInterval 0 = intervalLeftEndpoint a b hab.le := by
      apply Subtype.ext
      simpa [intervalLeftEndpoint] using hleftReal
    calc
      segmentPath x 0 =
          mappingPathInterval (family x) a b hab.le (unitToInterval 0) := rfl
      _ = mappingPathInterval (family x) a b hab.le (intervalLeftEndpoint a b hab.le) := by
        rw [hleft]
      _ = (family x).path a := by
        simpa using mappingPathInterval_leftEndpoint (family x) a b hab.le
      _ = p (point x) := (hstart x).symm
  have hsegmentMem : ∀ x (t : I), segmentPath x t ∈ 𝒰.cover i := by
    intro x t
    -- Every point of the reparameterized interval path stays inside the chosen cover member.
    simpa [segmentPath, unitToInterval] using hmem x (unitToInterval t)
  obtain ⟨liftI, hliftI₀, hliftIproj⟩ :=
    continuousLiftFromSingleCoverFamily 𝒰 hcont hlocal i point segmentPath hsegmentStart hsegmentMem
  let lift : C(X, C(Set.Icc (a : ℝ) (b : ℝ), E)) :=
    { toFun := fun x ↦ (liftI x).comp intervalToUnit
      continuous_toFun := by
        -- Reindex the lifted `I`-family back to the original interval.
        exact (ContinuousMap.continuous_precomp intervalToUnit).comp liftI.continuous }
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Evaluate the reindexed family at the left endpoint of the interval.
    have hleftReal :
        (((intervalToUnit (intervalLeftEndpoint a b hab.le) : I) : ℝ)) = 0 := by
      simp [intervalToUnit, intervalHomeomorph, intervalLeftEndpoint, hab.ne']
    have hleft :
        intervalToUnit (intervalLeftEndpoint a b hab.le) = (0 : I) := by
      apply Subtype.ext
      simpa using hleftReal
    calc
      lift x (intervalLeftEndpoint a b hab.le) =
          liftI x (intervalToUnit (intervalLeftEndpoint a b hab.le)) := rfl
      _ = liftI x 0 := by rw [hleft]
      _ = point x := hliftI₀ x
  · intro x
    -- Projecting the reindexed lift back to `B` recovers the original restricted path family.
    ext z
    calc
      (p.comp (lift x)) z = p (liftI x (intervalToUnit z)) := rfl
      _ = segmentPath x (intervalToUnit z) := by
        simpa [lift] using ContinuousMap.congr_fun (hliftIproj x) (intervalToUnit z)
      _ = mappingPathInterval (family x) a b hab.le (unitToInterval (intervalToUnit z)) := rfl
      _ = mappingPathInterval (family x) a b hab.le z := by
        congr
        exact intervalHomeomorph.symm_apply_apply z

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family can be applied to any continuous
family of paths that stays inside one chosen cover member. -/
theorem continuousLiftFromSingleCoverFamilyOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (i : ι) {X : Type*} [TopologicalSpace X] [UCompactlyGeneratedSpace.{max v w} X]
    (point : C(X, E)) (path : C(X, C(I, B)))
    (hstart : ∀ x, path x 0 = p (point x))
    (hmem : ∀ x (t : I), path x t ∈ 𝒰.cover i) :
    ∃ lift : C(X, C(I, E)), (∀ x, lift x 0 = point x) ∧ (∀ x, p.comp (lift x) = path x) := by
  let mappingPathFamily : C(X, MappingPathSpace p) :=
    { toFun := fun x ↦ MappingPathSpace.mk (point x) (path x) (hstart x)
      continuous_toFun := by
        -- Package the starting-point and path families into `MappingPathSpace p`.
        exact MappingPathSpace.continuous_mk point.continuous path.continuous hstart }
  let coveredFamily : C(X, {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}) :=
    { toFun := fun x ↦ ⟨mappingPathFamily x, fun t ↦ hmem x t⟩
      continuous_toFun := by
        -- Strengthen the mapping-path family to the subtype cut out by the chosen cover member.
        exact mappingPathFamily.continuous.subtype_mk fun x ↦ hmem x }
  let lift : C(X, C(I, E)) := (liftSingle i).comp coveredFamily
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- The fixed single-cover lift starts at the supplied starting-point family.
    simpa [lift, coveredFamily, mappingPathFamily] using hliftSingleSource i (coveredFamily x)
  · intro x
    -- Projecting the fixed single-cover lift back to `B` recovers the supplied path family.
    simpa [lift, coveredFamily, mappingPathFamily] using hliftSingleProj i (coveredFamily x)

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family also lifts continuous path
families on any closed subinterval that stays inside one chosen cover member. -/
theorem continuousLiftSegmentWithinCoverFamilyOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (i : ι) {X : Type*} [TopologicalSpace X] [UCompactlyGeneratedSpace.{max v w} X]
    (family : C(X, MappingPathSpace p)) {a b : I}
    (hab : (a : ℝ) < b) (point : C(X, E))
    (hstart : ∀ x, p (point x) = (family x).path a)
    (hmem :
      ∀ x (z : Set.Icc (a : ℝ) (b : ℝ)),
        (family x).path ⟨z.1, ⟨le_trans a.2.1 z.2.1, le_trans z.2.2 b.2.2⟩⟩ ∈ 𝒰.cover i) :
    ∃ lift : C(X, C(Set.Icc (a : ℝ) (b : ℝ), E)),
      (∀ x, lift x (intervalLeftEndpoint a b hab.le) = point x) ∧
        (∀ x, p.comp (lift x) = mappingPathInterval (family x) a b hab.le) := by
  let intervalHomeomorph : Set.Icc (a : ℝ) (b : ℝ) ≃ₜ I := iccHomeoI (a : ℝ) (b : ℝ) hab
  let intervalToUnit : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ⟨intervalHomeomorph, intervalHomeomorph.continuous_toFun⟩
  let unitToInterval : C(I, Set.Icc (a : ℝ) (b : ℝ)) :=
    ⟨intervalHomeomorph.symm, intervalHomeomorph.symm.continuous_toFun⟩
  let intervalInclusion : C(Set.Icc (a : ℝ) (b : ℝ), I) :=
    ContinuousMap.inclusion fun z hz ↦
      ⟨le_trans a.2.1 hz.1, le_trans hz.2 b.2.2⟩
  let segmentIntervalFamily : C(X, C(Set.Icc (a : ℝ) (b : ℝ), B)) :=
    { toFun := fun x ↦ mappingPathInterval (family x) a b hab.le
      continuous_toFun := by
        -- Restrict the bundled family of mapping paths to the chosen interval.
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        have hpath :
            Continuous fun x : X ↦ (family x).path := by
          simpa using
            (continuous_snd.comp
              ((MappingPathSpace.continuous_subtypeVal (p := p)).comp family.continuous) :
              Continuous fun x : X ↦ (((family x : MappingPathSpace p) : E × C(I, B)).2))
        have huncurry :
            Continuous fun y : X × Set.Icc (a : ℝ) (b : ℝ) ↦
              (family y.1).path (intervalInclusion y.2) := by
          simpa using
            (continuous_eval.comp <|
              (hpath.comp continuous_fst).prodMk (intervalInclusion.continuous.comp continuous_snd))
        simpa [mappingPathInterval, intervalInclusion] using huncurry }
  let segmentPath : C(X, C(I, B)) :=
    { toFun := fun x ↦ (segmentIntervalFamily x).comp unitToInterval
      continuous_toFun := by
        -- Reparameterize the interval family back to the unit interval expected by the fixed
        -- single-cover lift.
        exact (ContinuousMap.continuous_precomp unitToInterval).comp
          segmentIntervalFamily.continuous }
  have hsegmentStart : ∀ x, segmentPath x 0 = p (point x) := by
    intro x
    -- The reparameterized interval path starts at the original left endpoint.
    have hleftReal :
        (((unitToInterval 0 : Set.Icc (a : ℝ) (b : ℝ)) : ℝ)) = a := by
      simpa [unitToInterval, intervalHomeomorph] using
        iccHomeoI_symm_apply_coe (a : ℝ) (b : ℝ) hab (0 : I)
    have hleft :
        unitToInterval 0 = intervalLeftEndpoint a b hab.le := by
      apply Subtype.ext
      simpa [intervalLeftEndpoint] using hleftReal
    calc
      segmentPath x 0 =
          mappingPathInterval (family x) a b hab.le (unitToInterval 0) := rfl
      _ = mappingPathInterval (family x) a b hab.le (intervalLeftEndpoint a b hab.le) := by
        rw [hleft]
      _ = (family x).path a := by
        simpa using mappingPathInterval_leftEndpoint (family x) a b hab.le
      _ = p (point x) := (hstart x).symm
  have hsegmentMem : ∀ x (t : I), segmentPath x t ∈ 𝒰.cover i := by
    intro x t
    -- Every point of the reparameterized interval path stays inside the chosen cover member.
    simpa [segmentPath, unitToInterval] using hmem x (unitToInterval t)
  obtain ⟨liftI, hliftI₀, hliftIproj⟩ :=
    continuousLiftFromSingleCoverFamilyOfSingleCoverLifts 𝒰
      (p := p) liftSingle hliftSingleSource hliftSingleProj i point segmentPath
      hsegmentStart hsegmentMem
  let lift : C(X, C(Set.Icc (a : ℝ) (b : ℝ), E)) :=
    { toFun := fun x ↦ (liftI x).comp intervalToUnit
      continuous_toFun := by
        -- Reindex the lifted `I`-family back to the original interval.
        exact (ContinuousMap.continuous_precomp intervalToUnit).comp liftI.continuous }
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Evaluate the reindexed family at the left endpoint of the interval.
    have hleftReal :
        (((intervalToUnit (intervalLeftEndpoint a b hab.le) : I) : ℝ)) = 0 := by
      simp [intervalToUnit, intervalHomeomorph, intervalLeftEndpoint, hab.ne']
    have hleft :
        intervalToUnit (intervalLeftEndpoint a b hab.le) = (0 : I) := by
      apply Subtype.ext
      simpa using hleftReal
    calc
      lift x (intervalLeftEndpoint a b hab.le) =
          liftI x (intervalToUnit (intervalLeftEndpoint a b hab.le)) := rfl
      _ = liftI x 0 := by rw [hleft]
      _ = point x := hliftI₀ x
  · intro x
    -- Projecting the reindexed lift back to `B` recovers the original restricted path family.
    ext z
    calc
      (p.comp (lift x)) z = p (liftI x (intervalToUnit z)) := rfl
      _ = segmentPath x (intervalToUnit z) := by
        simpa [lift] using ContinuousMap.congr_fun (hliftIproj x) (intervalToUnit z)
      _ = mappingPathInterval (family x) a b hab.le (unitToInterval (intervalToUnit z)) := rfl
      _ = mappingPathInterval (family x) a b hab.le z := by
        congr
        exact intervalHomeomorph.symm_apply_apply z

/-- Helper for Theorem 7.4.3: the path coordinate of `MappingPathSpace p` packaged as a bundled
continuous map. -/
theorem mappingPathSpacePathProjectionContinuous {p : C(E, B)} :
    Continuous fun x : MappingPathSpace p ↦ x.path := by
  -- The path coordinate is the second projection from the defining subtype.
  simpa [MappingPathSpace.path] using
    (continuous_snd.comp (MappingPathSpace.continuous_subtypeVal (p := p)) :
      Continuous fun x : MappingPathSpace p ↦ ((x : E × C(I, B)).2))

/-- Helper for Theorem 7.4.3: the path projection from `MappingPathSpace p` to `C(I, B)`. -/
def mappingPathSpacePathProjection (p : C(E, B)) : C(MappingPathSpace p, C(I, B)) :=
  ⟨fun x ↦ x.path, mappingPathSpacePathProjectionContinuous⟩

/-- Helper for Theorem 7.4.3: a path in the basic patching neighborhood forces the ordered
subfamily to be nonempty. -/
theorem orderedSubfamily_length_pos_of_mem_patchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {T : NumerableOpenCover.OrderedSubfamily ι} {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T) :
    0 < T.length := by
  -- Unfold the empty-subfamily case: the patching weight is then exactly `0`.
  by_contra hT
  have hβ' : (0 : ℝ) < (NumerableOpenCover.patchingWeight 𝒰 hcont T β : ℝ) := hβ
  simp [NumerableOpenCover.coe_patchingWeight_apply, NumerableOpenCover.patchingWeightReal, hT] at hβ'

/-- Helper for Theorem 7.4.3: a path in the refined patching neighborhood also forces the ordered
subfamily to be nonempty. -/
theorem orderedSubfamily_length_pos_of_mem_patchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {T : NumerableOpenCover.OrderedSubfamily ι} {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T) :
    0 < T.length := by
  -- Reduce to the basic neighborhood via the canonical containment lemma.
  exact orderedSubfamily_length_pos_of_mem_patchingOpen 𝒰 hcont <|
    NumerableOpenCover.patchingRefinedOpen_subset_patchingOpen 𝒰 hcont T hβ

/-- Helper for Theorem 7.4.3: the right endpoint of the `m`th prefix of the subdivision attached
to `T`. -/
theorem prefixEndpoint_mem (T : NumerableOpenCover.OrderedSubfamily ι) {m : ℕ}
    (hm : m ≤ T.length) : ((m : ℝ) / T.length) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg (by positivity) (by positivity)
  · have hm' : (m : ℝ) ≤ T.length := by
      exact_mod_cast hm
    exact div_le_one_of_le₀ hm' (by positivity)

/-- Helper for Theorem 7.4.3: the bundled endpoint of the `m`th prefix interval. -/
noncomputable def prefixEndpoint (T : NumerableOpenCover.OrderedSubfamily ι) (m : ℕ)
    (hm : m ≤ T.length) : I :=
  ⟨(m : ℝ) / T.length, prefixEndpoint_mem T hm⟩

/-- Helper for Theorem 7.4.3: the subdivision prefix endpoints are nonnegative. -/
theorem prefixEndpoint_zero_le (T : NumerableOpenCover.OrderedSubfamily ι) {m : ℕ}
    (hm : m ≤ T.length) : ((0 : I) : ℝ) ≤ prefixEndpoint T m hm :=
  (prefixEndpoint T m hm).2.1

/-- Helper for Theorem 7.4.3: the zeroth prefix endpoint is `0`. -/
@[simp] theorem prefixEndpoint_zero (T : NumerableOpenCover.OrderedSubfamily ι) :
    prefixEndpoint T 0 (Nat.zero_le T.length) = (0 : I) := by
  apply Subtype.ext
  simp [prefixEndpoint]

/-- Helper for Theorem 7.4.3: under `0 < T.length`, the terminal prefix endpoint is `1`. -/
@[simp] theorem prefixEndpoint_self (T : NumerableOpenCover.OrderedSubfamily ι)
    (hT : 0 < T.length) : prefixEndpoint T T.length le_rfl = (1 : I) := by
  apply Subtype.ext
  have hT_ne : (T.length : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hT
  simp [prefixEndpoint, hT_ne]

/-- Helper for Theorem 7.4.3: consecutive subdivision prefix endpoints are strictly ordered. -/
theorem prefixEndpoint_lt_succ (T : NumerableOpenCover.OrderedSubfamily ι) {m : ℕ}
    (hm : m + 1 ≤ T.length) :
    ((prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm) : I) : ℝ) <
      prefixEndpoint T (m + 1) hm := by
  have hdenNat : 0 < T.length := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ m) hm
  have hden : (0 : ℝ) < T.length := by
    exact_mod_cast hdenNat
  have hnum : (m : ℝ) < (m + 1 : ℝ) := by
    exact_mod_cast Nat.lt_succ_self m
  simpa [prefixEndpoint] using div_lt_div_of_pos_right hnum hden

/-- Helper for Theorem 7.4.3: a point of the `j`th slot interval defines a point of `I`. -/
theorem slotIntervalPoint_mem (T : NumerableOpenCover.OrderedSubfamily ι) (j : Fin T.length)
    (z : Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) :
    z.1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hdenNat : 0 < T.length := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ j.1) (Nat.succ_le_of_lt j.2)
  have hden : (0 : ℝ) < T.length := by
    exact_mod_cast hdenNat
  have hright :
      (((j : ℕ) + 1 : ℝ) / T.length) ≤ 1 := by
    have hnum : ((j : ℕ) : ℝ) + 1 ≤ (T.length : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.2
    have hright' :
        ((((j : ℕ) : ℝ) + 1) / T.length) ≤ (T.length : ℝ) / T.length := by
      exact div_le_div_of_nonneg_right hnum hden.le
    simpa [Nat.cast_add, hden.ne'] using hright'
  refine ⟨?_, le_trans z.2.2 hright⟩
  exact le_trans (by positivity) z.2.1

/-- Helper for Theorem 7.4.3: view a point of the `j`th slot interval as a point of `I`. -/
def slotIntervalPoint (T : NumerableOpenCover.OrderedSubfamily ι) (j : Fin T.length)
    (z : Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) : I :=
  ⟨z.1, slotIntervalPoint_mem T j z⟩

/-- Helper for Theorem 7.4.3: coercing `slotIntervalPoint T j z : I` back to `ℝ` recovers the
underlying coordinate of `z`. -/
@[simp] theorem slotIntervalPoint_coe (T : NumerableOpenCover.OrderedSubfamily ι) (j : Fin T.length)
    (z : Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) :
    ((slotIntervalPoint T j z : I) : ℝ) = z.1 :=
  rfl

/-- Helper for Theorem 7.4.3: a point of the `j`th slot interval lies in the `j`th patching slot
when viewed in `I`. -/
theorem slotIntervalPoint_mem_patchingSlot (T : NumerableOpenCover.OrderedSubfamily ι)
    (j : Fin T.length)
    (z : Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) :
    slotIntervalPoint T j z ∈ T.patchingSlot j := by
  -- Rewrite slot membership to the defining interval inequalities for the slot coordinate.
  rw [NumerableOpenCover.OrderedSubfamily.patchingSlot, NumerableOpenCover.patchingSlot]
  constructor
  · simpa only [slotIntervalPoint_coe] using z.2.1
  · simpa only [slotIntervalPoint_coe, Nat.cast_add, Nat.cast_one] using z.2.2

/-- Helper for Theorem 7.4.3: reparameterize `I` onto the `j`th patching slot of `T`, viewed as
that closed subinterval. -/
noncomputable def patchingSlotParameterIcc (T : NumerableOpenCover.OrderedSubfamily ι)
    (j : Fin T.length) :
    C(I, Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) := by
  let left :
      I := by
        refine
          ⟨((j : ℕ) : ℝ) / T.length, unitInterval.div_mem ?_ ?_ ?_⟩
        · positivity
        · positivity
        · exact_mod_cast Nat.le_of_lt j.2
  let right :
      I := by
        refine
          ⟨(((j : ℕ) + 1 : ℝ) / T.length), unitInterval.div_mem ?_ ?_ ?_⟩
        · positivity
        · positivity
        · exact_mod_cast Nat.succ_le_of_lt j.2
  have hlength_nat : 0 < T.length := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ j.1) (Nat.succ_le_of_lt j.2)
  have hlength : (0 : ℝ) < T.length := by
    exact_mod_cast hlength_nat
  have hlt : (left : ℝ) < right := by
    change ((j : ℕ) : ℝ) / T.length < ((j : ℕ) + 1 : ℝ) / T.length
    have hj : ((j : ℕ) : ℝ) < ((j : ℕ) + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_self j.1
    have hlength_ne : (T.length : ℝ) ≠ 0 := by positivity
    by_contra hlt'
    have hle : ((j : ℕ) + 1 : ℝ) / T.length ≤ ((j : ℕ) : ℝ) / T.length := le_of_not_gt hlt'
    field_simp [hlength_ne] at hle
    exact (not_le_of_gt hj) hle
  let slotHomeomorph :
      Set.Icc (left : ℝ) (right : ℝ) ≃ₜ I := iccHomeoI (left : ℝ) (right : ℝ) hlt
  exact ⟨slotHomeomorph.symm.toFun, slotHomeomorph.symm.continuous_toFun⟩

/-- Helper for Theorem 7.4.3: reparameterize `I` onto the `j`th patching slot of `T`, viewed as a
self-map of `I`. -/
noncomputable def patchingSlotParameter (T : NumerableOpenCover.OrderedSubfamily ι)
    (j : Fin T.length) : C(I, I) := by
  let slotInclusion :
      C(Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length), I) :=
    ContinuousMap.inclusion <|
      Set.Icc_subset_Icc
        (by
          have hlength_nat : 0 < T.length := by
            exact lt_of_lt_of_le (Nat.zero_lt_succ j.1) (Nat.succ_le_of_lt j.2)
          have hlength : (0 : ℝ) < T.length := by
            exact_mod_cast hlength_nat
          have hleft : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := by positivity
          exact div_nonneg hleft hlength.le)
        (by
          have hlength_nat : 0 < T.length := by
            exact lt_of_lt_of_le (Nat.zero_lt_succ j.1) (Nat.succ_le_of_lt j.2)
          have hlength : (0 : ℝ) < T.length := by
            exact_mod_cast hlength_nat
          have hright : ((j : ℕ) + 1 : ℝ) ≤ T.length := by
            exact_mod_cast Nat.succ_le_of_lt j.2
          exact div_le_one_of_le₀ hright hlength.le)
  exact slotInclusion.comp (patchingSlotParameterIcc T j)

/-- Helper for Theorem 7.4.3: the slot reparameterization lands inside the chosen patching slot. -/
theorem patchingSlotParameter_mem (T : NumerableOpenCover.OrderedSubfamily ι) (j : Fin T.length)
    (t : I) : patchingSlotParameter T j t ∈ T.patchingSlot j := by
  -- Forget the subtype-valued parameterization and read its range bounds as slot membership.
  have hslot :
      ((j : ℕ) : ℝ) / T.length ≤
          ((patchingSlotParameterIcc T j t :
              Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) : ℝ) ∧
        ((patchingSlotParameterIcc T j t :
            Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) : ℝ) ≤
          ((j : ℕ) + 1 : ℝ) / T.length :=
    (patchingSlotParameterIcc T j t).2
  simpa [NumerableOpenCover.OrderedSubfamily.patchingSlot, NumerableOpenCover.patchingSlot,
    patchingSlotParameter] using hslot

/-- Helper for Theorem 7.4.3: on a basic patching neighborhood, the `j`th slot of each base path
forms a bundled continuous family of paths. -/
noncomputable def continuousPatchingSlotFamily (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (hcont : ∀ i, Continuous (𝒰 i)) {T : NumerableOpenCover.OrderedSubfamily ι}
    (j : Fin T.length) :
    C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, C(I, B)) := by
  refine
    { toFun := fun x ↦ x.1.path.comp (patchingSlotParameter T j)
      continuous_toFun := ?_ }
  -- Package the fixed slot reparameterization into a continuous map-valued family by proving
  -- continuity of the corresponding uncurried evaluation map.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hpath :
      Continuous fun x :
          {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} ↦
        x.1.path := by
    simpa [MappingPathSpace.path] using
      (continuous_snd.comp
        ((MappingPathSpace.continuous_subtypeVal (p := p)).comp continuous_subtype_val) :
        Continuous fun x :
            {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} ↦
          (((x : MappingPathSpace p) : E × C(I, B)).2))
  have huncurry :
      Continuous fun y :
          ({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} × I) ↦
        y.1.1.path (patchingSlotParameter T j y.2) := by
    exact
      continuous_eval.comp <|
        (hpath.comp continuous_fst).prodMk
          ((patchingSlotParameter T j).continuous.comp continuous_snd)
  simpa using huncurry

/-- Helper for Theorem 7.4.3: the `j`th slot family produced from a basic patching neighborhood
stays inside the corresponding cover member. -/
theorem continuousPatchingSlotFamily_mem_cover (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (hcont : ∀ i, Continuous (𝒰 i)) {T : NumerableOpenCover.OrderedSubfamily ι}
    (j : Fin T.length)
    (x : {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}) (t : I) :
    continuousPatchingSlotFamily 𝒰 hcont (p := p) j x t ∈ 𝒰.cover (T.get j) := by
  -- Route correction: isolate the slot-membership normalization once so later prefix gluing can
  -- call `continuousLiftFromSingleCoverFamily` directly on this bundled family.
  have hT : 0 < T.length := orderedSubfamily_length_pos_of_mem_patchingOpen 𝒰 hcont x.2
  have hx :
      ∀ j' : Fin T.length, ∀ s ∈ T.patchingSlot j', x.1.path s ∈ 𝒰.cover (T.get j') :=
    (NumerableOpenCover.mem_patchingOpen_iff 𝒰 hcont hT x.1.path).1 x.2
  exact hx j (patchingSlotParameter T j t) (patchingSlotParameter_mem T j t)

/-- Helper for Theorem 7.4.3: on a basic patching neighborhood, each point of the `j`th slot
interval lies in the corresponding cover member. -/
theorem mappingPath_mem_cover_of_mem_patchingOpen_slotInterval (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) (j : Fin T.length)
    (x : {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T})
    (z : Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length)) :
    x.1.path (slotIntervalPoint T j z) ∈ 𝒰.cover (T.get j) := by
  -- Rewrite the slot condition using the canonical slot-point in `I`.
  have hx :
      ∀ j' : Fin T.length, ∀ s ∈ T.patchingSlot j', x.1.path s ∈ 𝒰.cover (T.get j') :=
    (NumerableOpenCover.mem_patchingOpen_iff 𝒰 hcont hT x.1.path).1 x.2
  exact hx j (slotIntervalPoint T j z) (slotIntervalPoint_mem_patchingSlot T j z)

/-- Helper for Theorem 7.4.3: compatible continuous families of lifts on adjacent closed
subintervals concatenate to a continuous family on the combined interval. -/
theorem continuousConcatAdjacentIntervalLifts {p : C(E, B)} {X : Type*} [TopologicalSpace X]
    {a b c : I} (hab : (a : ℝ) ≤ b) (hbc : (b : ℝ) ≤ c)
    (lift₁ : C(X, C(Set.Icc (a : ℝ) (b : ℝ), E)))
    (lift₂ : C(X, C(Set.Icc (b : ℝ) (c : ℝ), E))) (point : C(X, E))
    (β : C(X, C(Set.Icc (a : ℝ) (c : ℝ), B)))
    (hstart : ∀ x, lift₁ x (intervalLeftEndpoint a b hab) = point x)
    (hcompat :
      ∀ x, lift₁ x (intervalRightEndpoint a b hab) = lift₂ x (intervalLeftEndpoint b c hbc))
    (hleft :
      ∀ x,
        p.comp (lift₁ x) = (β x).comp (intervalInclusionLeft a b c hab hbc))
    (hright :
      ∀ x,
        p.comp (lift₂ x) = (β x).comp (intervalInclusionRight a b c hab hbc)) :
    ∃ lift : C(X, C(Set.Icc (a : ℝ) (c : ℝ), E)),
      (∀ x, lift x (intervalLeftEndpoint a c (le_trans hab hbc)) = point x) ∧
        (∀ x, p.comp (lift x) = β x) := by
  -- Local instance justification (interval order facts): `ContinuousMap.concatCM` is parameterized
  -- by `Fact` witnesses for the two adjoining real-interval inequalities.
  letI : Fact ((a : ℝ) ≤ (b : ℝ)) := ⟨hab⟩
  letI : Fact ((b : ℝ) ≤ (c : ℝ)) := ⟨hbc⟩
  let compatiblePair :
      C(X,
        {fg : C(Set.Icc (a : ℝ) (b : ℝ), E) × C(Set.Icc (b : ℝ) (c : ℝ), E) //
          fg.1 ⊤ = fg.2 ⊥}) :=
    { toFun := fun x ↦
        ⟨(lift₁ x, lift₂ x), by
          -- Rephrase the endpoint compatibility in the `⊤`/`⊥` spelling used by `concatCM`.
          simpa [intervalRightEndpoint, intervalLeftEndpoint] using hcompat x⟩
      continuous_toFun := by
        -- Bundle the compatible pair of interval families into the subtype expected by `concatCM`.
        exact (lift₁.continuous.prodMk lift₂.continuous).subtype_mk fun x ↦ by
          simpa [intervalRightEndpoint, intervalLeftEndpoint] using hcompat x }
  let lift : C(X, C(Set.Icc (a : ℝ) (c : ℝ), E)) := ContinuousMap.concatCM.comp compatiblePair
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Evaluate the family-wise concatenation at the left endpoint of the combined interval.
    calc
      lift x (intervalLeftEndpoint a c (le_trans hab hbc)) =
          lift₁ x (intervalLeftEndpoint a b hab) := by
        simpa [lift, compatiblePair, intervalLeftEndpoint] using
          (ContinuousMap.concatCM_left
            (fg := compatiblePair x) (x := intervalLeftEndpoint a c (le_trans hab hbc)) hab)
      _ = point x := hstart x
  · intro x
    -- Compare the projected concatenated family with the base path on the left and right pieces.
    ext z
    by_cases hz : (z : ℝ) ≤ b
    · have hleftEval := ContinuousMap.congr_fun (hleft x) ⟨z.1, z.2.1, hz⟩
      calc
        (p.comp (lift x)) z = p (lift x z) := rfl
        _ = p (lift₁ x ⟨z.1, z.2.1, hz⟩) := by
          exact congrArg p <|
            (by
              simpa [lift, compatiblePair] using
                (ContinuousMap.concatCM_left (fg := compatiblePair x) (x := z) hz))
        _ = β x z := by
          simpa [intervalInclusionLeft] using hleftEval
    · have hz' : (b : ℝ) ≤ z := le_of_not_ge hz
      have hrightEval := ContinuousMap.congr_fun (hright x) ⟨z.1, hz', z.2.2⟩
      calc
        (p.comp (lift x)) z = p (lift x z) := rfl
        _ = p (lift₂ x ⟨z.1, hz', z.2.2⟩) := by
          exact congrArg p <|
            (by
              simpa [lift, compatiblePair] using
                (ContinuousMap.concatCM_right (fg := compatiblePair x) (x := z) hz'))
        _ = β x z := by
          simpa [intervalInclusionRight] using hrightEval

/-- Helper for Theorem 7.4.3: extending a prefix lift by one additional subdivision slot produces
the next prefix lift on the same basic patching neighborhood. -/
theorem continuousLiftOnPatchingPrefixSucc (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) {m : ℕ}
    (hm : m + 1 ≤ T.length)
    (lift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        C(Set.Icc (0 : ℝ)
          ((prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm) : I)), E)))
    (hsource :
      ∀ x,
        lift x
            (intervalLeftEndpoint 0
              (prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm))
              (prefixEndpoint_zero_le T (Nat.le_trans (Nat.le_succ m) hm))) =
          x.1.point)
    (hproj :
      ∀ x,
        p.comp (lift x) =
          mappingPathInterval x.1 0
            (prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm))
            (prefixEndpoint_zero_le T (Nat.le_trans (Nat.le_succ m) hm))) :
    ∃ succLift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
          C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), E)),
      (∀ x,
        succLift x
            (intervalLeftEndpoint 0 (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hm)) =
          x.1.point) ∧
        (∀ x, p.comp (succLift x) =
          mappingPathInterval x.1 0 (prefixEndpoint T (m + 1) hm)
            (prefixEndpoint_zero_le T hm)) := by
  let hmPrev : m ≤ T.length := Nat.le_trans (Nat.le_succ m) hm
  let j : Fin T.length := ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) hm⟩
  let family :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        MappingPathSpace p) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let prefixRightPoint :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, E) :=
    { toFun := fun x ↦
        lift x
          (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev))
      continuous_toFun := by
        -- Evaluate the current prefix lift at its right endpoint to get the next starting point.
        exact (continuous_eval_const _).comp lift.continuous }
  let nextPrefixPath :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), B)) :=
    by
      let intervalInclusion :
          C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), I) :=
        ContinuousMap.inclusion fun z hz ↦
          ⟨hz.1, le_trans hz.2 (prefixEndpoint T (m + 1) hm).2.2⟩
      let pathFamily :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, C(I, B)) :=
        (mappingPathSpacePathProjection p).comp family
      refine
        { toFun := fun x ↦ mappingPathInterval x.1 0 (prefixEndpoint T (m + 1) hm)
            (prefixEndpoint_zero_le T hm)
          continuous_toFun := ?_ }
      -- Restrict the bundled family of base paths to the larger successor prefix interval.
      simpa [mappingPathInterval, intervalInclusion] using
        (ContinuousMap.continuous_precomp intervalInclusion).comp pathFamily.continuous
  have hprefixRightPoint :
      ∀ x,
        p (prefixRightPoint x) = (family x).path (prefixEndpoint T m hmPrev) := by
    intro x
    -- Evaluate the current prefix projection identity at the right endpoint.
    simpa [prefixRightPoint, family] using
      ContinuousMap.congr_fun (hproj x)
        (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev))
  have hsegmentMem :
      ∀ x
        (z : Set.Icc ((prefixEndpoint T m hmPrev : I) : ℝ) ((prefixEndpoint T (m + 1) hm : I) : ℝ)),
        (family x).path ⟨z.1, ⟨le_trans (prefixEndpoint T m hmPrev).2.1 z.2.1,
          le_trans z.2.2 (prefixEndpoint T (m + 1) hm).2.2⟩⟩ ∈ 𝒰.cover (T.get j) := by
    intro x z
    -- Rewrite the successor slot interval to the canonical slot interval attached to `j`.
    let zSlot :
        Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length) :=
      ⟨z.1, by simpa [prefixEndpoint, j] using z.2⟩
    simpa [family, prefixEndpoint, j, slotIntervalPoint, zSlot] using
      mappingPath_mem_cover_of_mem_patchingOpen_slotInterval 𝒰 hcont (p := p) hT j x zSlot
  let _ : UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} :=
    mappingPathPatchingOpen_uCompactlyGeneratedSpace 𝒰 hcont T
  obtain ⟨segmentLift, hsegmentSource, hsegmentProj⟩ :=
    continuousLiftSegmentWithinCoverFamily 𝒰 hcont hlocal (T.get j) family
      (prefixEndpoint_lt_succ T hm) prefixRightPoint hprefixRightPoint hsegmentMem
  have hcompat :
      ∀ x,
        lift x
            (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev)) =
          segmentLift x
            (intervalLeftEndpoint (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The new slot lift starts at the current right endpoint by construction.
    simpa [prefixRightPoint] using (hsegmentSource x).symm
  have hleft :
      ∀ x,
        p.comp (lift x) =
          (nextPrefixPath x).comp
            (intervalInclusionLeft 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The old prefix interval is the left restriction of the new combined prefix interval.
    calc
      p.comp (lift x) =
          mappingPathInterval x.1 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev) :=
        hproj x
      _ =
          (nextPrefixPath x).comp
            (intervalInclusionLeft 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
        simpa [nextPrefixPath] using
          mappingPathInterval_comp_intervalInclusionLeft x.1
            (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))
  have hright :
      ∀ x,
        p.comp (segmentLift x) =
          (nextPrefixPath x).comp
            (intervalInclusionRight 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The freshly lifted slot is the right restriction of the new combined prefix interval.
    calc
      p.comp (segmentLift x) =
          mappingPathInterval x.1 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
            (le_of_lt (prefixEndpoint_lt_succ T hm)) := hsegmentProj x
      _ =
          (nextPrefixPath x).comp
            (intervalInclusionRight 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
        simpa [nextPrefixPath] using
          mappingPathInterval_comp_intervalInclusionRight x.1
            (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))
  -- Concatenate the previous prefix lift with the new slot lift in one family-wise step.
  exact
    continuousConcatAdjacentIntervalLifts
      (p := p)
      (a := 0)
      (b := prefixEndpoint T m hmPrev)
      (c := prefixEndpoint T (m + 1) hm)
      (prefixEndpoint_zero_le T hmPrev)
      (le_of_lt (prefixEndpoint_lt_succ T hm))
      lift segmentLift
      { toFun := fun x ↦ x.1.point
        continuous_toFun := by
          -- The starting point is the first coordinate of the mapping-path-space subtype.
          simpa using
            (mappingPathSpacePointContinuous (p := p)).comp continuous_subtype_val }
      nextPrefixPath hsource hcompat hleft hright

/-- Helper for Theorem 7.4.3: over a basic patching neighborhood, the local slot lifts concatenate
inductively to a continuous family of lifts on each initial subdivision prefix. -/
theorem continuousLiftOnPatchingPrefix (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) :
    ∀ m : ℕ, ∀ hm : m ≤ T.length,
      ∃ lift :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
            C(Set.Icc (0 : ℝ) ((prefixEndpoint T m hm : I)), E)),
        (∀ x,
          lift x
              (intervalLeftEndpoint 0 (prefixEndpoint T m hm) (prefixEndpoint_zero_le T hm)) =
            x.1.point) ∧
          (∀ x, p.comp (lift x) =
            mappingPathInterval x.1 0 (prefixEndpoint T m hm) (prefixEndpoint_zero_le T hm)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      let lift :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
            C(Set.Icc (0 : ℝ) ((prefixEndpoint T 0 hm : I)), E)) :=
        { toFun := fun x ↦
            ⟨fun _ ↦ x.1.point, continuous_const⟩
          continuous_toFun := by
            -- On the degenerate initial interval, the lift is constantly the stored starting point.
            refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
            simpa using
              (mappingPathSpacePointContinuous (p := p)).comp
                (continuous_subtype_val.comp continuous_fst) }
      refine ⟨lift, ?_, ?_⟩
      · intro x
        -- The degenerate prefix lift starts at the stored point by construction.
        rfl
      · intro x
        -- On the degenerate interval, both sides are constant at the path value at `0`.
        ext z
        have hz :
            z = intervalLeftEndpoint 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm) := by
          apply Subtype.ext
          have hz0 : (z : ℝ) = 0 := by
            have hleft : (0 : ℝ) ≤ z := z.2.1
            have hright0 : (z : ℝ) ≤ 0 := by
              simpa [prefixEndpoint_zero] using z.2.2
            exact le_antisymm hright0 hleft
          simpa [intervalLeftEndpoint, prefixEndpoint_zero] using hz0
        calc
          (p.comp (lift x)) z = p x.1.point := rfl
          _ = x.1.path 0 := x.1.path_zero_eq.symm
          _ =
              mappingPathInterval x.1 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm)
                (intervalLeftEndpoint 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm)) := by
            simpa using
              (mappingPathInterval_leftEndpoint x.1 0 (prefixEndpoint T 0 hm)
                (prefixEndpoint_zero_le T hm)).symm
          _ =
              mappingPathInterval x.1 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm) z := by
            rw [hz]
  | succ m ih =>
      intro hm
      obtain ⟨lift, hsource, hproj⟩ := ih (Nat.le_trans (Nat.le_succ m) hm)
      -- Extend the current prefix by one subdivision slot using the family-wise concatenation helper.
      exact
        continuousLiftOnPatchingPrefixSucc 𝒰 hcont (p := p) hlocal hT hm lift hsource hproj

/-- Helper for Theorem 7.4.3: every nonempty basic patching neighborhood carries a continuous
family of full path lifts. -/
theorem continuousLiftOnPatchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  obtain ⟨lift, hsource, hproj⟩ :=
    continuousLiftOnPatchingPrefix 𝒰 hcont (p := p) hlocal hT T.length le_rfl
  let castInterval :
      C(I, Set.Icc (0 : ℝ) ((prefixEndpoint T T.length le_rfl : I))) :=
    ContinuousMap.inclusion <| by
      intro t ht
      simpa [prefixEndpoint_self T hT] using ht
  let terminalIntervalInclusion :
      C(Set.Icc (0 : ℝ) ((prefixEndpoint T T.length le_rfl : I)), I) :=
    ContinuousMap.inclusion fun z hz ↦
      ⟨hz.1, le_trans hz.2 (prefixEndpoint T T.length le_rfl).2.2⟩
  let fullLift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, C(I, E)) :=
    { toFun := fun x ↦ (lift x).comp castInterval
      continuous_toFun := by
        -- Reindex the terminal prefix family along the identification of the terminal prefix with `I`.
        exact (ContinuousMap.continuous_precomp castInterval).comp lift.continuous }
  -- The terminal prefix interval is all of `I`, so the prefix lift is already a full path lift.
  refine ⟨fullLift, ?_, ?_⟩
  · intro x
    calc
      fullLift x 0 = lift x (castInterval 0) := rfl
      _ = lift x
            (intervalLeftEndpoint 0 (prefixEndpoint T T.length le_rfl)
              (prefixEndpoint_zero_le T le_rfl)) := by
          have hcast :
              castInterval 0 =
                intervalLeftEndpoint 0 (prefixEndpoint T T.length le_rfl)
                  (prefixEndpoint_zero_le T le_rfl) := by
            apply Subtype.ext
            rfl
          rw [hcast]
      _ = x.1.point := hsource x
  · intro x
    ext t
    calc
      (p.comp (fullLift x)) t = p (lift x (castInterval t)) := rfl
      _ =
          mappingPathInterval x.1 0 (prefixEndpoint T T.length le_rfl)
            (prefixEndpoint_zero_le T le_rfl) (castInterval t) := by
          simpa [fullLift] using
            ContinuousMap.congr_fun (hproj x) (castInterval t)
      _ = x.1.path t := by
          calc
            mappingPathInterval x.1 0 (prefixEndpoint T T.length le_rfl)
                (prefixEndpoint_zero_le T le_rfl) (castInterval t) =
              x.1.path (terminalIntervalInclusion (castInterval t)) := rfl
            _ = x.1.path t := by
              rfl

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family extends one prefix of the basic
patching construction by one more slot. -/
theorem continuousLiftOnPatchingPrefixSuccOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) {m : ℕ}
    (hm : m + 1 ≤ T.length)
    (lift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        C(Set.Icc (0 : ℝ)
          ((prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm) : I)), E)))
    (hsource :
      ∀ x,
        lift x
            (intervalLeftEndpoint 0
              (prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm))
              (prefixEndpoint_zero_le T (Nat.le_trans (Nat.le_succ m) hm))) =
          x.1.point)
    (hproj :
      ∀ x,
        p.comp (lift x) =
          mappingPathInterval x.1 0
            (prefixEndpoint T m (Nat.le_trans (Nat.le_succ m) hm))
            (prefixEndpoint_zero_le T (Nat.le_trans (Nat.le_succ m) hm))) :
    ∃ succLift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
          C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), E)),
      (∀ x,
        succLift x
            (intervalLeftEndpoint 0 (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hm)) =
          x.1.point) ∧
        (∀ x, p.comp (succLift x) =
          mappingPathInterval x.1 0 (prefixEndpoint T (m + 1) hm)
            (prefixEndpoint_zero_le T hm)) := by
  let hmPrev : m ≤ T.length := Nat.le_trans (Nat.le_succ m) hm
  let j : Fin T.length := ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) hm⟩
  let family :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        MappingPathSpace p) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let prefixRightPoint :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, E) :=
    { toFun := fun x ↦
        lift x
          (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev))
      continuous_toFun := by
        -- Evaluate the current prefix lift at its right endpoint to get the next starting point.
        exact (continuous_eval_const _).comp lift.continuous }
  let nextPrefixPath :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
        C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), B)) :=
    by
      let intervalInclusion :
          C(Set.Icc (0 : ℝ) ((prefixEndpoint T (m + 1) hm : I)), I) :=
        ContinuousMap.inclusion fun z hz ↦
          ⟨hz.1, le_trans hz.2 (prefixEndpoint T (m + 1) hm).2.2⟩
      let pathFamily :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, C(I, B)) :=
        (mappingPathSpacePathProjection p).comp family
      refine
        { toFun := fun x ↦ mappingPathInterval x.1 0 (prefixEndpoint T (m + 1) hm)
            (prefixEndpoint_zero_le T hm)
          continuous_toFun := ?_ }
      -- Restrict the bundled family of base paths to the larger successor prefix interval.
      simpa [mappingPathInterval, intervalInclusion] using
        (ContinuousMap.continuous_precomp intervalInclusion).comp pathFamily.continuous
  have hprefixRightPoint :
      ∀ x,
        p (prefixRightPoint x) = (family x).path (prefixEndpoint T m hmPrev) := by
    intro x
    -- Evaluate the current prefix projection identity at the right endpoint.
    simpa [prefixRightPoint, family] using
      ContinuousMap.congr_fun (hproj x)
        (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev))
  have hsegmentMem :
      ∀ x
        (z : Set.Icc ((prefixEndpoint T m hmPrev : I) : ℝ) ((prefixEndpoint T (m + 1) hm : I) : ℝ)),
        (family x).path ⟨z.1, ⟨le_trans (prefixEndpoint T m hmPrev).2.1 z.2.1,
          le_trans z.2.2 (prefixEndpoint T (m + 1) hm).2.2⟩⟩ ∈ 𝒰.cover (T.get j) := by
    intro x z
    -- Rewrite the successor slot interval to the canonical slot interval attached to `j`.
    let zSlot :
        Set.Icc (((j : ℕ) : ℝ) / T.length) (((j : ℕ) + 1 : ℝ) / T.length) :=
      ⟨z.1, by simpa [prefixEndpoint, j] using z.2⟩
    simpa [family, prefixEndpoint, j, slotIntervalPoint, zSlot] using
      mappingPath_mem_cover_of_mem_patchingOpen_slotInterval 𝒰 hcont (p := p) hT j x zSlot
  let _ : UCompactlyGeneratedSpace.{max v w}
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} :=
    mappingPathPatchingOpen_uCompactlyGeneratedSpace 𝒰 hcont T
  obtain ⟨segmentLift, hsegmentSource, hsegmentProj⟩ :=
    continuousLiftSegmentWithinCoverFamilyOfSingleCoverLifts 𝒰 (p := p)
      liftSingle hliftSingleSource hliftSingleProj (T.get j) family
      (prefixEndpoint_lt_succ T hm) prefixRightPoint hprefixRightPoint hsegmentMem
  have hcompat :
      ∀ x,
        lift x
            (intervalRightEndpoint 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev)) =
          segmentLift x
            (intervalLeftEndpoint (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The new slot lift starts at the current right endpoint by construction.
    simpa [prefixRightPoint] using (hsegmentSource x).symm
  have hleft :
      ∀ x,
        p.comp (lift x) =
          (nextPrefixPath x).comp
            (intervalInclusionLeft 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The old prefix interval is the left restriction of the new combined prefix interval.
    calc
      p.comp (lift x) =
          mappingPathInterval x.1 0 (prefixEndpoint T m hmPrev) (prefixEndpoint_zero_le T hmPrev) :=
        hproj x
      _ =
          (nextPrefixPath x).comp
            (intervalInclusionLeft 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
        simpa [nextPrefixPath] using
          mappingPathInterval_comp_intervalInclusionLeft x.1
            (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))
  have hright :
      ∀ x,
        p.comp (segmentLift x) =
          (nextPrefixPath x).comp
            (intervalInclusionRight 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
    intro x
    -- The freshly lifted slot is the right restriction of the new combined prefix interval.
    calc
      p.comp (segmentLift x) =
          mappingPathInterval x.1 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
            (le_of_lt (prefixEndpoint_lt_succ T hm)) := hsegmentProj x
      _ =
          (nextPrefixPath x).comp
            (intervalInclusionRight 0 (prefixEndpoint T m hmPrev) (prefixEndpoint T (m + 1) hm)
              (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))) := by
        simpa [nextPrefixPath] using
          mappingPathInterval_comp_intervalInclusionRight x.1
            (prefixEndpoint_zero_le T hmPrev) (le_of_lt (prefixEndpoint_lt_succ T hm))
  -- Concatenate the previous prefix lift with the new slot lift in one family-wise step.
  exact
    continuousConcatAdjacentIntervalLifts
      (p := p)
      (a := 0)
      (b := prefixEndpoint T m hmPrev)
      (c := prefixEndpoint T (m + 1) hm)
      (prefixEndpoint_zero_le T hmPrev)
      (le_of_lt (prefixEndpoint_lt_succ T hm))
      lift segmentLift
      { toFun := fun x ↦ x.1.point
        continuous_toFun := by
          -- The starting point is the first coordinate of the mapping-path-space subtype.
          simpa using
            (mappingPathSpacePointContinuous (p := p)).comp continuous_subtype_val }
      nextPrefixPath hsource hcompat hleft hright

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family concatenates along every prefix of
the basic patching construction. -/
theorem continuousLiftOnPatchingPrefixOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) :
    ∀ m : ℕ, ∀ hm : m ≤ T.length,
      ∃ lift :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
            C(Set.Icc (0 : ℝ) ((prefixEndpoint T m hm : I)), E)),
        (∀ x,
          lift x
              (intervalLeftEndpoint 0 (prefixEndpoint T m hm) (prefixEndpoint_zero_le T hm)) =
            x.1.point) ∧
          (∀ x, p.comp (lift x) =
            mappingPathInterval x.1 0 (prefixEndpoint T m hm) (prefixEndpoint_zero_le T hm)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      let lift :
          C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
            C(Set.Icc (0 : ℝ) ((prefixEndpoint T 0 hm : I)), E)) :=
        { toFun := fun x ↦
            ⟨fun _ ↦ x.1.point, continuous_const⟩
          continuous_toFun := by
            -- On the degenerate initial interval, the lift is constantly the stored starting point.
            refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
            simpa using
              (mappingPathSpacePointContinuous (p := p)).comp
                (continuous_subtype_val.comp continuous_fst) }
      refine ⟨lift, ?_, ?_⟩
      · intro x
        -- The degenerate prefix lift starts at the stored point by construction.
        rfl
      · intro x
        -- On the degenerate interval, both sides are constant at the path value at `0`.
        ext z
        have hz :
            z = intervalLeftEndpoint 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm) := by
          apply Subtype.ext
          have hz0 : (z : ℝ) = 0 := by
            have hleft : (0 : ℝ) ≤ z := z.2.1
            have hright0 : (z : ℝ) ≤ 0 := by
              simpa [prefixEndpoint_zero] using z.2.2
            exact le_antisymm hright0 hleft
          simpa [intervalLeftEndpoint, prefixEndpoint_zero] using hz0
        calc
          (p.comp (lift x)) z = p x.1.point := rfl
          _ = x.1.path 0 := x.1.path_zero_eq.symm
          _ =
              mappingPathInterval x.1 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm)
                (intervalLeftEndpoint 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm)) := by
            simpa using
              (mappingPathInterval_leftEndpoint x.1 0 (prefixEndpoint T 0 hm)
                (prefixEndpoint_zero_le T hm)).symm
          _ =
              mappingPathInterval x.1 0 (prefixEndpoint T 0 hm) (prefixEndpoint_zero_le T hm) z := by
            rw [hz]
  | succ m ih =>
      intro hm
      obtain ⟨lift, hsource, hproj⟩ := ih (Nat.le_trans (Nat.le_succ m) hm)
      -- Extend the current prefix by one subdivision slot using the fixed single-cover lift family.
      exact
        continuousLiftOnPatchingPrefixSuccOfSingleCoverLifts 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hT hm lift hsource hproj

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family produces a canonical lift on every
nonempty basic patching neighborhood. -/
theorem continuousLiftOnPatchingOpenOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {T : NumerableOpenCover.OrderedSubfamily ι} (hT : 0 < T.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  obtain ⟨lift, hsource, hproj⟩ :=
    continuousLiftOnPatchingPrefixOfSingleCoverLifts 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj hT T.length le_rfl
  let castInterval :
      C(I, Set.Icc (0 : ℝ) ((prefixEndpoint T T.length le_rfl : I))) :=
    ContinuousMap.inclusion <| by
      intro t ht
      simpa [prefixEndpoint_self T hT] using ht
  let terminalIntervalInclusion :
      C(Set.Icc (0 : ℝ) ((prefixEndpoint T T.length le_rfl : I)), I) :=
    ContinuousMap.inclusion fun z hz ↦
      ⟨hz.1, le_trans hz.2 (prefixEndpoint T T.length le_rfl).2.2⟩
  let fullLift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T}, C(I, E)) :=
    { toFun := fun x ↦ (lift x).comp castInterval
      continuous_toFun := by
        -- Reindex the terminal prefix family along the identification of the terminal prefix with `I`.
        exact (ContinuousMap.continuous_precomp castInterval).comp lift.continuous }
  -- The terminal prefix interval is all of `I`, so the prefix lift is already a full path lift.
  refine ⟨fullLift, ?_, ?_⟩
  · intro x
    calc
      fullLift x 0 = lift x (castInterval 0) := rfl
      _ = lift x
            (intervalLeftEndpoint 0 (prefixEndpoint T T.length le_rfl)
              (prefixEndpoint_zero_le T le_rfl)) := by
          have hcast :
              castInterval 0 =
                intervalLeftEndpoint 0 (prefixEndpoint T T.length le_rfl)
                  (prefixEndpoint_zero_le T le_rfl) := by
            apply Subtype.ext
            rfl
          rw [hcast]
      _ = x.1.point := hsource x
  · intro x
    ext t
    calc
      (p.comp (fullLift x)) t = p (lift x (castInterval t)) := rfl
      _ =
          mappingPathInterval x.1 0 (prefixEndpoint T T.length le_rfl)
            (prefixEndpoint_zero_le T le_rfl) (castInterval t) := by
          simpa [fullLift] using
            ContinuousMap.congr_fun (hproj x) (castInterval t)
      _ = x.1.path t := by
          calc
            mappingPathInterval x.1 0 (prefixEndpoint T T.length le_rfl)
                (prefixEndpoint_zero_le T le_rfl) (castInterval t) =
              x.1.path (terminalIntervalInclusion (castInterval t)) := rfl
            _ = x.1.path t := by
              rfl

/-- Helper for Theorem 7.4.3: if `x.path` lies in a canonical refined patching neighborhood,
its pullback along the path projection is a neighborhood of `x` in `MappingPathSpace p`. -/
theorem mem_nhds_pulledBackPatchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {T : NumerableOpenCover.OrderedSubfamily ι}
    {x : MappingPathSpace p}
    (hx : x.path ∈ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T) :
    {y : MappingPathSpace p | y.path ∈ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T} ∈ nhds x := by
  -- Pull back the open refined neighborhood of `x.path` along the continuous path projection.
  simpa [mappingPathSpacePathProjection] using
    (mappingPathSpacePathProjectionContinuous (p := p)).continuousAt.preimage_mem_nhds
      ((NumerableOpenCover.isOpen_patchingRefinedOpen 𝒰 hcont T).mem_nhds hx)

/-- Helper for Theorem 7.4.3: if `x.path` lies in a basic patching neighborhood, its pullback
along the path projection is a neighborhood of `x` in `MappingPathSpace p`. -/
theorem mem_nhds_pulledBackPatchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {T : NumerableOpenCover.OrderedSubfamily ι}
    {x : MappingPathSpace p}
    (hx : x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T) :
    {y : MappingPathSpace p | y.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T} ∈ nhds x := by
  -- Pull back the open basic neighborhood of `x.path` along the continuous path projection.
  simpa [mappingPathSpacePathProjection] using
    (mappingPathSpacePathProjectionContinuous (p := p)).continuousAt.preimage_mem_nhds
      ((NumerableOpenCover.isOpen_patchingOpen 𝒰 hcont T).mem_nhds hx)

/-- Helper for Theorem 7.4.3: one basic patching neighborhood is covered by its residual refined
piece together with the basic patching neighborhoods of the chosen predecessor subfamilies. -/
theorem patchingOpen_subset_patchingRefinedOpenFrom_union_predecessorPatchingOpen
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {T : List ι}
    (refinement : NumerableOpenCover.PatchingRefinement T) :
    (NumerableOpenCover.patchingOpen 𝒰 hcont refinement.orderedSubfamily : Set (C(I, B))) ⊆
      (NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement : Set (C(I, B))) ∪
        ⋃ a : refinement.predecessor,
          (NumerableOpenCover.patchingOpen 𝒰 hcont (refinement.predecessorSubfamily a) :
            Set (C(I, B))) := by
  intro β hβ
  by_cases hrefined :
      β ∈ (NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement : Set (C(I, B)))
  · -- If the residual refined weight is already positive, we are in the first cover piece.
    exact Or.inl hrefined
  · -- Otherwise the predecessor sum must absorb the positive basic patching weight.
    right
    -- Local instance justification (finite predecessor family): the refinement data already
    -- carries the finite predecessor indexing needed for the finite sums below.
    let _ : Fintype refinement.predecessor := refinement.finite_predecessor
    have hβpos :
        0 < NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β := by
      simpa [NumerableOpenCover.patchingOpen, NumerableOpenCover.coe_patchingWeight_apply] using hβ
    have hrefined_nonpos :
        NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β -
            (T.length : ℝ) * ∑ a : refinement.predecessor,
              NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β ≤
          0 := by
      have hmax_nonpos :
          max 0
              (NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β -
                (T.length : ℝ) * ∑ a : refinement.predecessor,
                  NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β) ≤
            0 := by
        have hrefined_eq_zero :
            NumerableOpenCover.patchingRefinedWeightFrom 𝒰 hcont refinement β = 0 := by
          simpa [NumerableOpenCover.patchingRefinedOpenFrom] using hrefined
        have hmax_eq_zero :
            max 0
                (NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β -
                  (T.length : ℝ) * ∑ a : refinement.predecessor,
                    NumerableOpenCover.patchingWeightReal 𝒰
                      (refinement.predecessorSubfamily a) β) =
              0 := by
          simpa [NumerableOpenCover.patchingRefinedWeightFrom,
            NumerableOpenCover.patchingRefinedWeightRealFrom] using
            congrArg (fun x : I ↦ (x : ℝ)) hrefined_eq_zero
        rw [hmax_eq_zero]
      exact le_trans (le_max_right 0 _) hmax_nonpos
    have hlength_pos : 0 < refinement.orderedSubfamily.length := by
      exact orderedSubfamily_length_pos_of_mem_patchingOpen 𝒰 hcont hβ
    have hlength_real_pos : (0 : ℝ) < T.length := by
      exact_mod_cast hlength_pos
    let predecessorWeight : refinement.predecessor → ℝ := fun a ↦
      NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β
    have hpredecessor_nonneg : ∀ a : refinement.predecessor, 0 ≤ predecessorWeight a := by
      intro a
      exact
        (NumerableOpenCover.patchingWeightReal_mem_unitInterval 𝒰
          (refinement.predecessorSubfamily a) β).1
    have hsum_pos : 0 < ∑ a : refinement.predecessor, predecessorWeight a := by
      have hsum_nonneg : 0 ≤ ∑ a : refinement.predecessor, predecessorWeight a := by
        exact Finset.sum_nonneg fun a _ ↦ hpredecessor_nonneg a
      have hweight_le :
          NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β ≤
            (T.length : ℝ) * ∑ a : refinement.predecessor, predecessorWeight a := by
        linarith
      by_contra hsum_not_pos
      have hsum_nonpos : ∑ a : refinement.predecessor, predecessorWeight a ≤ 0 :=
        le_of_not_gt hsum_not_pos
      have hproduct_nonpos :
          (T.length : ℝ) * ∑ a : refinement.predecessor, predecessorWeight a ≤ 0 := by
        nlinarith
      have hweight_nonpos :
          NumerableOpenCover.patchingWeightReal 𝒰 refinement.orderedSubfamily β ≤ 0 := by
        linarith
      linarith
    have hpredecessor_exists :
        ∃ a : refinement.predecessor,
          0 < NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
      by_contra hnone
      push Not at hnone
      have hpredecessor_zero :
          ∀ a : refinement.predecessor,
            NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β = 0 := by
        intro a
        have hnonneg := hpredecessor_nonneg a
        have hnot_pos :
            ¬ 0 <
                NumerableOpenCover.patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
          exact not_lt_of_ge (hnone a)
        linarith
      have hsum_zero : ∑ a : refinement.predecessor, predecessorWeight a = 0 := by
        classical
        simp [predecessorWeight, hpredecessor_zero]
      linarith
    rcases hpredecessor_exists with ⟨a, ha⟩
    refine Set.mem_iUnion.mpr ⟨a, ?_⟩
    -- Positivity of one predecessor weight puts the path in that predecessor patching neighborhood.
    simpa [NumerableOpenCover.patchingOpen, NumerableOpenCover.coe_patchingWeight_apply] using ha

/-- Helper for Theorem 7.4.3: if a path lies in a basic patching neighborhood but not in the
canonical refined neighborhood, then it lies in one predecessor basic patching neighborhood of the
canonical refinement. -/
theorem existsPredecessor_mem_patchingOpen_of_mem_patchingOpen_not_refined
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {T : NumerableOpenCover.OrderedSubfamily ι} {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T)
    (hrefined : β ∉ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T) :
    ∃ a : (NumerableOpenCover.patchingRefinement T).predecessor,
      β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont
        ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a) := by
  -- Route correction: normalize first from canonical `patchingRefinedOpen` to the bridge-form
  -- `patchingRefinedOpenFrom`, then read the predecessor witness out of the union cover.
  have hrefinedFrom :
      β ∉ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont
        (NumerableOpenCover.patchingRefinement T) := by
    simpa [NumerableOpenCover.patchingRefinedOpen_eq_from] using hrefined
  have hcover :=
    patchingOpen_subset_patchingRefinedOpenFrom_union_predecessorPatchingOpen 𝒰 hcont
      (refinement := NumerableOpenCover.patchingRefinement T) hβ
  rcases hcover with hrefinedMem | hpred
  · exact (hrefinedFrom hrefinedMem).elim
  · simpa using Set.mem_iUnion.mp hpred

/-- Helper for Theorem 7.4.3: a non-refined basic patching witness can be replaced by a strictly
shorter basic patching witness. -/
theorem existsShorterOrderedSubfamily_mem_patchingOpen_of_mem_patchingOpen_not_refined
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {T : NumerableOpenCover.OrderedSubfamily ι} {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T)
    (hrefined : β ∉ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T) :
    ∃ S : NumerableOpenCover.OrderedSubfamily ι,
      S.length < T.length ∧ β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont S := by
  -- Extract the predecessor witness and then forget the index, retaining the strict length drop.
  rcases
      existsPredecessor_mem_patchingOpen_of_mem_patchingOpen_not_refined 𝒰 hcont hβ hrefined with
    ⟨a, ha⟩
  refine ⟨(NumerableOpenCover.patchingRefinement T).predecessorSubfamily a, ?_, ha⟩
  simpa [NumerableOpenCover.OrderedSubfamily.length] using
    (NumerableOpenCover.patchingRefinement T).shorter a

/-- Helper for Theorem 7.4.3: a basic patching witness of minimal length is already a refined
witness. -/
theorem mem_patchingRefinedOpen_of_minimal_mem_patchingOpen
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {T : NumerableOpenCover.OrderedSubfamily ι} {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T)
    (hminimal :
      ∀ S : NumerableOpenCover.OrderedSubfamily ι,
        β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont S → T.length ≤ S.length) :
    β ∈ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T := by
  -- A shorter predecessor basic witness would contradict the assumed minimality of `T.length`.
  by_contra hrefined
  rcases
      existsShorterOrderedSubfamily_mem_patchingOpen_of_mem_patchingOpen_not_refined
        𝒰 hcont hβ hrefined with
    ⟨S, hSlt, hSβ⟩
  exact Nat.not_lt_of_ge (hminimal S hSβ) hSlt

/-- Helper for Theorem 7.4.3: once a path admits some basic patching witness, a minimal-length
choice upgrades it to a canonical refined witness. -/
theorem existsOrderedSubfamily_mem_patchingRefinedOpen_of_exists_mem_patchingOpen
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {β : C(I, B)}
    (hbasic :
      ∃ T : NumerableOpenCover.OrderedSubfamily ι,
        β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T) :
    ∃ T : NumerableOpenCover.OrderedSubfamily ι,
      β ∈ NumerableOpenCover.patchingRefinedOpen 𝒰 hcont T := by
  classical
  -- Choose a basic witness with minimal length and invoke the previous minimality lemma.
  let P : ℕ → Prop := fun m ↦
    ∃ T : NumerableOpenCover.OrderedSubfamily ι,
      T.length = m ∧ β ∈ NumerableOpenCover.patchingOpen 𝒰 hcont T
  have hlenWitness : ∃ m : ℕ, P m := by
    rcases hbasic with ⟨T, hT⟩
    exact ⟨T.length, T, rfl, hT⟩
  let n : ℕ := Nat.find hlenWitness
  have hn :
      P n := Nat.find_spec hlenWitness
  rcases hn with ⟨T, hTlen, hTβ⟩
  refine ⟨T, ?_⟩
  -- The `Nat.find` witness is minimal among all basic patching witnesses.
  apply mem_patchingRefinedOpen_of_minimal_mem_patchingOpen 𝒰 hcont hTβ
  intro S hSβ
  have hmin :
      n ≤ S.length :=
    Nat.find_min' hlenWitness ⟨S, rfl, hSβ⟩
  simpa [hTlen] using hmin

/-- Helper for Theorem 7.4.3: a repeated word is reindexed by its slot positions together with the
original cover indices used only to keep the ambient family an actual open cover of `B`. -/
abbrev wordIndex (w : List ι) := Sum (Fin w.length) ι

/-- Helper for Theorem 7.4.3: a repeated word of cover labels defines a genuine numerable open
cover by duplicating the selected word slots on the left summand and retaining the original cover
on the right summand. -/
noncomputable def wordCover (𝒰 : NumerableOpenCover ι B) (w : List ι) :
    NumerableOpenCover (wordIndex w) B := by
  let v : wordIndex w → Set B :=
    Sum.elim (fun j ↦ (𝒰.cover (w.get j) : Set B)) (fun i ↦ (𝒰.cover i : Set B))
  let hvopen : ∀ k : wordIndex w, IsOpen (v k) := by
    intro k
    cases k with
    | inl j =>
        simpa [v] using (𝒰.cover (w.get j)).isOpen
    | inr i =>
        simpa [v] using (𝒰.cover i).isOpen
  refine
    { cover := fun k ↦ ⟨v k, hvopen k⟩
      toFun := Sum.elim (fun j ↦ 𝒰 (w.get j)) 𝒰
      isOpenCover := by
        refine TopologicalSpace.IsOpenCover.of_sets hvopen ?_
        ext b
        constructor
        · intro _
          simp [v]
        · intro _
          obtain ⟨i, hi⟩ := 𝒰.isOpenCover.exists_mem b
          exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
      iocPreimage_eq := by
        intro k
        cases k with
        | inl j =>
            simpa [v] using 𝒰.iocPreimage_eq (w.get j)
        | inr i =>
            simpa [v] using 𝒰.iocPreimage_eq i
      locallyFinite := by
        let leftFamily : Fin w.length → Set B := fun j ↦ (𝒰.cover (w.get j) : Set B)
        have hleft : LocallyFinite leftFamily := locallyFinite_of_finite leftFamily
        have hright : LocallyFinite fun i : ι ↦ (𝒰.cover i : Set B) := 𝒰.locallyFinite
        simpa [leftFamily, v, wordIndex] using
          (LocallyFinite.sumElim hleft hright :
            LocallyFinite (fun i : wordIndex w ↦
              Sum.elim leftFamily (fun i : ι ↦ (𝒰.cover i : Set B)) i)) }

/-- Helper for Theorem 7.4.3: the duplicated numerating functions in `wordCover` stay continuous
when the original numerating family is continuous. -/
theorem wordCoverContinuous (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (w : List ι) :
    ∀ k : wordIndex w, Continuous ((wordCover 𝒰 w) k) := by
  intro k
  cases k with
  | inl j =>
      -- The left summand just repeats one of the original numerating functions.
      simpa [wordCover, wordIndex] using hcont (w.get j)
  | inr i =>
      -- The right summand is the original numerating family itself.
      simpa [wordCover, wordIndex] using hcont i

/-- Helper for Theorem 7.4.3: the repeated slot indices of a word form a canonical nodup ordered
subfamily for `wordCover`. -/
noncomputable def wordFullSubfamily (w : List ι) :
    NumerableOpenCover.OrderedSubfamily (wordIndex w) :=
  ⟨List.ofFn (fun j : Fin w.length ↦ Sum.inl j), by
    -- Distinct slot positions remain distinct after the left-summand embedding.
    apply List.nodup_ofFn.mpr
    intro i j hij
    exact Sum.inl.inj hij⟩

/-- Helper for Theorem 7.4.3: the canonical full slot subfamily has the same length as the
underlying word. -/
@[simp] theorem wordFullSubfamily_length (w : List ι) :
    (wordFullSubfamily w).length = w.length := by
  simp [wordFullSubfamily, NumerableOpenCover.OrderedSubfamily.length,
    NumerableOpenCover.OrderedSubfamily.toList]

/-- Helper for Theorem 7.4.3: the basic patching neighborhood attached to a word is just the
existing `patchingOpen` construction applied to `wordCover` and the full slot subfamily. -/
noncomputable abbrev wordPatchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (w : List ι) :
    TopologicalSpace.Opens (C(I, B)) :=
  NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
    (wordFullSubfamily w)

/-- Helper for Theorem 7.4.3: the refined patching neighborhood attached to a word reuses the
existing refinement construction after slot-position reindexing. -/
noncomputable abbrev wordPatchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (w : List ι) :
    TopologicalSpace.Opens (C(I, B)) :=
  NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
    (wordFullSubfamily w)

/-- Helper for Theorem 7.4.3: if `x.path` lies in a basic word patching neighborhood, its pullback
along the path projection is a neighborhood of `x` in `MappingPathSpace p`. -/
theorem mem_nhds_pulledBackWordPatchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι} {x : MappingPathSpace p}
    (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w) :
    {y : MappingPathSpace p | y.path ∈ wordPatchingOpen 𝒰 hcont w} ∈ nhds x := by
  -- Pull back the open basic word neighborhood of `x.path` along the continuous path projection.
  simpa [mappingPathSpacePathProjection, wordPatchingOpen] using
    (mappingPathSpacePathProjectionContinuous (p := p)).continuousAt.preimage_mem_nhds
      ((NumerableOpenCover.isOpen_patchingOpen (wordCover 𝒰 w)
        (wordCoverContinuous 𝒰 hcont w) (wordFullSubfamily w)).mem_nhds hx)

/-- Helper for Theorem 7.4.3: forgetting the duplicate-slot bookkeeping in `wordCover 𝒰 w`
remembers only the underlying original cover label. -/
def wordCoverLabel (w : List ι) : wordIndex w → ι
  | Sum.inl j => w.get j
  | Sum.inr i => i

/-- Helper for Theorem 7.4.3: an ordered subfamily of `wordCover 𝒰 w` determines the ordinary
word of cover labels used along its subdivision slots. -/
def wordOfOrderedSubfamily (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w)) : List ι :=
  T.toList.map (wordCoverLabel w)

/-- Helper for Theorem 7.4.3: forgetting duplicate-slot bookkeeping preserves the ordered
subfamily length. -/
@[simp] theorem wordOfOrderedSubfamily_length (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w)) :
    (wordOfOrderedSubfamily w T).length = T.length := by
  simp [wordOfOrderedSubfamily, NumerableOpenCover.OrderedSubfamily.length,
    NumerableOpenCover.OrderedSubfamily.toList]

/-- Helper for Theorem 7.4.3: the `j`th entry of the forgotten word is the underlying label of
the `j`th member of the original ordered subfamily. -/
@[simp] theorem wordOfOrderedSubfamily_get (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w))
    (j : Fin (wordOfOrderedSubfamily w T).length) :
    (wordOfOrderedSubfamily w T).get j =
      wordCoverLabel w (T.get (Fin.cast (wordOfOrderedSubfamily_length w T) j)) := by
  simpa [wordOfOrderedSubfamily, NumerableOpenCover.OrderedSubfamily.get,
    NumerableOpenCover.OrderedSubfamily.length, NumerableOpenCover.OrderedSubfamily.toList]

/-- Helper for Theorem 7.4.3: membership in the basic word patching neighborhood is exactly the
slotwise cover condition on the original repeated word. -/
theorem mem_wordPatchingOpen_iff (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {w : List ι} (hw : 0 < w.length) (β : C(I, B)) :
    β ∈ wordPatchingOpen 𝒰 hcont w ↔
      ∀ j : Fin w.length, ∀ t ∈ NumerableOpenCover.patchingSlot w j, β t ∈ 𝒰.cover (w.get j) := by
  -- Route correction: normalize the repeated-word neighborhood by passing to the slot-indexed
  -- cover, then rewrite the ordered-subfamily API back to the original word slots.
  constructor
  · intro hβ j t ht
    let j' : Fin (wordFullSubfamily w).length := Fin.cast (wordFullSubfamily_length w).symm j
    have hslot :
        β t ∈ (wordCover 𝒰 w).cover ((wordFullSubfamily w).get j') :=
      (NumerableOpenCover.mem_patchingOpen_iff (wordCover 𝒰 w)
        (wordCoverContinuous 𝒰 hcont w) (T := wordFullSubfamily w)
        (by simpa using hw) β).1 hβ j' t <|
          by
            simpa [j', wordFullSubfamily, NumerableOpenCover.OrderedSubfamily.length,
              NumerableOpenCover.OrderedSubfamily.toList,
              NumerableOpenCover.OrderedSubfamily.patchingSlot, NumerableOpenCover.patchingSlot]
              using ht
    simpa [j', wordFullSubfamily, wordCover, wordIndex,
      NumerableOpenCover.OrderedSubfamily.length, NumerableOpenCover.OrderedSubfamily.toList,
      NumerableOpenCover.OrderedSubfamily.get, NumerableOpenCover.OrderedSubfamily.patchingSlot,
      NumerableOpenCover.patchingSlot] using hslot
  · intro hβ
    refine
      (NumerableOpenCover.mem_patchingOpen_iff (wordCover 𝒰 w)
        (wordCoverContinuous 𝒰 hcont w) (T := wordFullSubfamily w)
        (by simpa using hw) β).2 ?_
    intro j t ht
    let j' : Fin w.length := Fin.cast (wordFullSubfamily_length w) j
    have hslot : β t ∈ 𝒰.cover (w.get j') :=
      hβ j' t <|
        by
          simpa [j', wordFullSubfamily, NumerableOpenCover.OrderedSubfamily.length,
            NumerableOpenCover.OrderedSubfamily.toList,
            NumerableOpenCover.OrderedSubfamily.patchingSlot, NumerableOpenCover.patchingSlot]
            using ht
    simpa [j', wordFullSubfamily, wordCover, wordIndex,
      NumerableOpenCover.OrderedSubfamily.length, NumerableOpenCover.OrderedSubfamily.toList,
      NumerableOpenCover.OrderedSubfamily.get, NumerableOpenCover.OrderedSubfamily.patchingSlot,
      NumerableOpenCover.patchingSlot] using hslot

/-- Helper for Theorem 7.4.3: every path in `C(I,B)` lies in a basic patching neighborhood for
some repeated finite word of cover labels. -/
theorem existsWord_mem_wordPatchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (β : C(I, B)) :
    ∃ w : List ι, β ∈ wordPatchingOpen 𝒰 hcont w := by
  let c : ι → Set I := fun i ↦ β ⁻¹' (𝒰.cover i)
  have hc_open : ∀ i : ι, IsOpen (c i) := by
    intro i
    simpa [c] using (𝒰.cover i).isOpen.preimage β.continuous
  have hc_cover : Set.univ ⊆ ⋃ i : ι, c i := by
    intro t ht
    rcases 𝒰.isOpenCover.exists_mem (β t) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδpos, hδcover⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hc_open hc_cover
  obtain ⟨N, hNδ⟩ := exists_nat_one_div_lt hδpos
  have hmeshPointMem :
      ∀ j : Fin (N + 1), ((j : ℕ) : ℝ) / (N + 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    refine unitInterval.div_mem ?_ ?_ ?_
    · positivity
    · positivity
    · exact_mod_cast Nat.le_of_lt j.2
  let meshPoint : Fin (N + 1) → I := fun j ↦
    ⟨((j : ℕ) : ℝ) / (N + 1 : ℝ), hmeshPointMem j⟩
  have hmeshCover : ∀ j : Fin (N + 1), ∃ i : ι, Metric.ball (meshPoint j) δ ⊆ c i := by
    intro j
    exact hδcover (meshPoint j) (Set.mem_univ _)
  choose slot hslot using hmeshCover
  let w : List ι := List.ofFn slot
  have hwlen : w.length = N + 1 := by
    simp [w]
  have hw : 0 < w.length := by
    simpa [hwlen]
  refine ⟨w, ?_⟩
  rw [mem_wordPatchingOpen_iff 𝒰 hcont hw β]
  intro j t ht
  let j' : Fin (N + 1) := Fin.cast hwlen j
  have ht' :
      (((j' : ℕ) : ℝ) / (N + 1 : ℝ) ≤ (t : ℝ)) ∧
        ((t : ℝ) ≤ (((j' : ℕ) + 1 : ℝ) / (N + 1 : ℝ))) := by
    simpa [w, j', hwlen, NumerableOpenCover.patchingSlot] using ht
  have hNp1_ne : (N + 1 : ℝ) ≠ 0 := by
    positivity
  have hdist_le :
      |(t : ℝ) - (((j' : ℕ) : ℝ) / (N + 1 : ℝ))| ≤ 1 / (N + 1 : ℝ) := by
    have hsub_nonneg :
        0 ≤ (t : ℝ) - (((j' : ℕ) : ℝ) / (N + 1 : ℝ)) := sub_nonneg.mpr ht'.1
    rw [abs_of_nonneg hsub_nonneg]
    have hstep :
        (((j' : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) - (((j' : ℕ) : ℝ) / (N + 1 : ℝ)) =
          1 / (N + 1 : ℝ) := by
      field_simp [hNp1_ne]
      ring
    have hsub_le :
        (t : ℝ) - (((j' : ℕ) : ℝ) / (N + 1 : ℝ)) ≤
          (((j' : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) - (((j' : ℕ) : ℝ) / (N + 1 : ℝ)) := by
      linarith
    simpa [hstep] using hsub_le
  have htBall : t ∈ Metric.ball (meshPoint j') δ := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    exact lt_of_le_of_lt hdist_le hNδ
  have hwget : w.get j = slot j' := by
    simpa [w, j', hwlen] using (List.get_ofFn slot j)
  -- The uniform mesh slot lies in the chosen cover member because the whole slot sits inside the
  -- Lebesgue ball around its left endpoint.
  rw [hwget]
  simpa [c] using hslot j' htBall

/-- Helper for Theorem 7.4.3: a basic patching witness for an ordered subfamily of `wordCover 𝒰 w`
can be re-read as a basic word witness for the corresponding list of underlying cover labels. -/
theorem mem_wordPatchingOpen_of_mem_patchingOpen_wordCover (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)} (hT : 0 < T.length) {β : C(I, B)}
    (hβ : β ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w) T) :
    β ∈ wordPatchingOpen 𝒰 hcont (wordOfOrderedSubfamily w T) := by
  have hword : 0 < (wordOfOrderedSubfamily w T).length := by
    simpa using hT
  rw [mem_wordPatchingOpen_iff 𝒰 hcont hword β]
  intro j t ht
  let j' : Fin T.length := Fin.cast (wordOfOrderedSubfamily_length w T) j
  have hslot :
      β t ∈ (wordCover 𝒰 w).cover (T.get j') :=
    (NumerableOpenCover.mem_patchingOpen_iff (wordCover 𝒰 w)
      (wordCoverContinuous 𝒰 hcont w) (T := T) hT β).1 hβ j' t <|
      by
        simpa [j', wordOfOrderedSubfamily, NumerableOpenCover.OrderedSubfamily.length,
          NumerableOpenCover.OrderedSubfamily.toList,
          NumerableOpenCover.OrderedSubfamily.patchingSlot, NumerableOpenCover.patchingSlot]
          using ht
  have hlabelPos :
      0 < 𝒰 (wordCoverLabel w (T.get j')) (β t) := by
    cases hget : T.get j' with
    | inl j'' =>
        have hslot' : β t ∈ (wordCover 𝒰 w).cover (Sum.inl j'') := by
          simpa [hget] using hslot
        simpa [NumerableOpenCover.mem_cover_iff_pos, wordCover, wordIndex, wordCoverLabel, hget]
          using hslot'
    | inr i =>
        have hslot' : β t ∈ (wordCover 𝒰 w).cover (Sum.inr i) := by
          simpa [hget] using hslot
        simpa [NumerableOpenCover.mem_cover_iff_pos, wordCover, wordIndex, wordCoverLabel, hget]
          using hslot'
  have hlabel :
      wordCoverLabel w (T.get j') = (wordOfOrderedSubfamily w T).get j := by
    simpa [j'] using (wordOfOrderedSubfamily_get w T j).symm
  simpa [NumerableOpenCover.mem_cover_iff_pos, hlabel] using hlabelPos

/-- Helper for Theorem 7.4.3: a predecessor-piece subtype in an ambient duplicated-cover chart
maps continuously to the shorter ordinary-word basic patching subtype obtained by forgetting the
slot bookkeeping. -/
theorem continuous_wordCoverPredecessorPatchingOpenInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    Continuous fun x :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)} ↦
      (⟨x.1,
          mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
            (orderedSubfamily_length_pos_of_mem_patchingOpen
              (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) x.2)
            x.2⟩ :
        {x : MappingPathSpace p //
          x.path ∈ wordPatchingOpen 𝒰 hcont
            (wordOfOrderedSubfamily w
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))}) := by
  -- The map is just subtype restriction along the ambient-to-ordinary-word membership bridge.
  have hval :
      Continuous fun x :
          {x : MappingPathSpace p //
            x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)} ↦
        (x : MappingPathSpace p) := continuous_subtype_val
  exact hval.subtype_mk fun x ↦
    mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
      (orderedSubfamily_length_pos_of_mem_patchingOpen
        (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) x.2)
      x.2

/-- Helper for Theorem 7.4.3: the canonical inclusion from a predecessor chart in the ambient
duplicated cover to the shorter ordinary-word patching chart obtained by forgetting slot labels.
-/
noncomputable def wordCoverPredecessorPatchingOpenInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    C({x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)},
      {x : MappingPathSpace p //
        x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))}) :=
  { toFun := fun x ↦
      ⟨x.1,
        mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
          (orderedSubfamily_length_pos_of_mem_patchingOpen
            (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) x.2)
          x.2⟩
    continuous_toFun :=
      continuous_wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w)
        (T := T) a }

/-- Helper for Theorem 7.4.3: forgetting the generalized predecessor-piece inclusion recovers the
underlying mapping path. -/
@[simp] theorem wordCoverPredecessorPatchingOpenInclusion_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor)
    (x :
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)}) :
    ((wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w) (T := T) a x :
        {x : MappingPathSpace p //
          x.path ∈ wordPatchingOpen 𝒰 hcont
            (wordOfOrderedSubfamily w
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))}) :
      MappingPathSpace p) = x := rfl

/-- Helper for Theorem 7.4.3: a recursive lift on the shorter ordinary word obtained from a
predecessor subfamily restricts to a lift on that predecessor chart inside the ambient duplicated
cover. -/
theorem wordCoverPredecessorPieceLiftFromShorterWord
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor)
    (liftShorter :
      C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))},
        C(I, E)))
    (hsourceShorter :
      ∀ x, liftShorter x 0 = x.1.point)
    (hprojShorter :
      ∀ x, p.comp (liftShorter x) = x.1.path) :
    ∃ lift :
        C({x : MappingPathSpace p //
            x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  let lift :
      C({x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)},
        C(I, E)) :=
    liftShorter.comp (wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w)
      (T := T) a)
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Transporting the shorter-word lift only changes the domain subtype bookkeeping.
    simpa [lift] using
      hsourceShorter
        (wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w) (T := T) a x)
  · intro x
    -- The projection equation is likewise preserved after forgetting the ambient predecessor chart.
    simpa [lift] using
      hprojShorter
        (wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w) (T := T) a x)

/-- Helper for Theorem 7.4.3: a canonical predecessor of `wordFullSubfamily w` forgets to a
strictly shorter ordinary word. -/
theorem predecessorSubwordOfWordFullSubfamily (w : List ι)
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    (wordOfOrderedSubfamily w
      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)).length <
        w.length := by
  -- Forgetting the predecessor slot bookkeeping preserves length, so the refinement's strict
  -- predecessor shortening descends immediately to the ordinary repeated word.
  simpa [wordOfOrderedSubfamily_length,
    NumerableOpenCover.PatchingRefinement.predecessorSubfamily,
    NumerableOpenCover.OrderedSubfamily.length,
    NumerableOpenCover.OrderedSubfamily.toList,
    wordFullSubfamily] using
    (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).shorter a

/-- Helper for Theorem 7.4.3: a predecessor patching witness in `wordCover 𝒰 w` can be re-read as
a basic word patching witness for the shorter predecessor word. -/
theorem mem_wordPatchingOpen_of_mem_predecessorPatchingOpen
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    {β : C(I, B)}
    (hβ :
      β ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)) :
    β ∈ wordPatchingOpen 𝒰 hcont
      (wordOfOrderedSubfamily w
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)) := by
  have hpredPos :
      0 <
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a).length :=
    orderedSubfamily_length_pos_of_mem_patchingOpen (𝒰 := wordCover 𝒰 w)
      (hcont := wordCoverContinuous 𝒰 hcont w) hβ
  -- The predecessor piece already lives in the repeated-word cover, so the earlier normalization
  -- lemma transports it to the ordinary shorter word without new choices.
  exact mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont hpredPos hβ

/-- Helper for Theorem 7.4.3: the predecessor-piece subtype of `wordCover 𝒰 w` maps continuously
to the shorter-word basic patching subtype. -/
theorem continuous_predecessorWordPatchingOpenInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    Continuous fun x :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)} ↦
      (⟨x.1, mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont a x.2⟩ :
        {x : MappingPathSpace p //
          x.path ∈ wordPatchingOpen 𝒰 hcont
            (wordOfOrderedSubfamily w
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a))}) := by
  -- The map is just subtype restriction along the predecessor-to-shorter-word membership bridge.
  have hval :
      Continuous fun x :
          {x : MappingPathSpace p //
            x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a)} ↦
        (x : MappingPathSpace p) := continuous_subtype_val
  exact hval.subtype_mk fun x ↦ mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont a x.2

/-- Helper for Theorem 7.4.3: the canonical predecessor-piece inclusion into the shorter-word
basic patching neighborhood. -/
noncomputable def predecessorWordPatchingOpenInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    C({x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)},
      {x : MappingPathSpace p //
        x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))}) :=
  { toFun := fun x ↦
      ⟨x.1, mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont a x.2⟩
    continuous_toFun := continuous_predecessorWordPatchingOpenInclusion 𝒰 hcont a }

/-- Helper for Theorem 7.4.3: forgetting the predecessor-piece inclusion just recovers the
original mapping path. -/
@[simp] theorem predecessorWordPatchingOpenInclusion_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    (x :
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)}) :
    ((predecessorWordPatchingOpenInclusion 𝒰 hcont a x : {x : MappingPathSpace p //
        x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))}) : MappingPathSpace p) = x := rfl

/-- Helper for Theorem 7.4.3: if a word witness is not yet refined, one predecessor basic witness
produces a strictly shorter word witness. -/
theorem existsShorterWord_mem_wordPatchingOpen_of_mem_wordPatchingOpen_not_refined
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {w : List ι} {β : C(I, B)} (hβ : β ∈ wordPatchingOpen 𝒰 hcont w)
    (hrefined : β ∉ wordPatchingRefinedOpen 𝒰 hcont w) :
    ∃ w' : List ι, w'.length < w.length ∧ β ∈ wordPatchingOpen 𝒰 hcont w' := by
  rcases
      existsShorterOrderedSubfamily_mem_patchingOpen_of_mem_patchingOpen_not_refined
        (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w)
        (T := wordFullSubfamily w) (β := β)
        (by simpa [wordPatchingOpen] using hβ)
        (by simpa [wordPatchingRefinedOpen] using hrefined) with
    ⟨S, hSlt, hSβ⟩
  have hSpos : 0 < S.length :=
    orderedSubfamily_length_pos_of_mem_patchingOpen (𝒰 := wordCover 𝒰 w)
      (hcont := wordCoverContinuous 𝒰 hcont w) hSβ
  refine ⟨wordOfOrderedSubfamily w S, ?_, ?_⟩
  · simpa using hSlt
  · exact mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont hSpos hSβ

/-- Helper for Theorem 7.4.3: a minimal-length basic word witness is already a canonical refined
word witness. -/
theorem mem_wordPatchingRefinedOpen_of_minimal_mem_wordPatchingOpen
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {w : List ι} {β : C(I, B)} (hβ : β ∈ wordPatchingOpen 𝒰 hcont w)
    (hminimal : ∀ w' : List ι, β ∈ wordPatchingOpen 𝒰 hcont w' → w.length ≤ w'.length) :
    β ∈ wordPatchingRefinedOpen 𝒰 hcont w := by
  -- Route correction: minimize among ordinary words, then use the shorter-word predecessor bridge
  -- instead of minimizing over arbitrary `Σ w, T` chart data.
  by_contra hrefined
  rcases
      existsShorterWord_mem_wordPatchingOpen_of_mem_wordPatchingOpen_not_refined
        𝒰 hcont hβ hrefined with
    ⟨w', hw'lt, hw'β⟩
  exact Nat.not_lt_of_ge (hminimal w' hw'β) hw'lt

/-- Helper for Theorem 7.4.3: every path in `C(I,B)` lies in a canonical refined patching
neighborhood for some positive-length repeated word. -/
theorem existsWord_mem_wordPatchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (β : C(I, B)) :
    ∃ w : List ι, 0 < w.length ∧ β ∈ wordPatchingRefinedOpen 𝒰 hcont w := by
  classical
  let P : ℕ → Prop := fun m ↦
    ∃ w : List ι, w.length = m ∧ β ∈ wordPatchingOpen 𝒰 hcont w
  have hlenWitness : ∃ m : ℕ, P m := by
    rcases existsWord_mem_wordPatchingOpen 𝒰 hcont β with ⟨w, hw⟩
    exact ⟨w.length, w, rfl, hw⟩
  let n : ℕ := Nat.find hlenWitness
  have hn : P n := Nat.find_spec hlenWitness
  rcases hn with ⟨w, hwlen, hβw⟩
  have hwpos : 0 < w.length := by
    simpa [wordPatchingOpen, wordFullSubfamily_length] using
      orderedSubfamily_length_pos_of_mem_patchingOpen (𝒰 := wordCover 𝒰 w)
        (hcont := wordCoverContinuous 𝒰 hcont w) hβw
  refine ⟨w, hwpos, ?_⟩
  apply mem_wordPatchingRefinedOpen_of_minimal_mem_wordPatchingOpen 𝒰 hcont hβw
  intro w' hw'β
  have hmin : n ≤ w'.length :=
    Nat.find_min' hlenWitness ⟨w', rfl, hw'β⟩
  simpa [hwlen] using hmin

/-- Helper for Theorem 7.4.3: every path in `C(I,B)` also lies in a canonical refined patching
neighborhood for some repeated word cover. -/
theorem existsWordOrderedSubfamily_mem_patchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (β : C(I, B)) :
    ∃ w : List ι, ∃ T : NumerableOpenCover.OrderedSubfamily (wordIndex w),
      β ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
        (wordCoverContinuous 𝒰 hcont w) T := by
  rcases existsWord_mem_wordPatchingOpen 𝒰 hcont β with ⟨w, hw⟩
  have hbasic :
      ∃ T : NumerableOpenCover.OrderedSubfamily (wordIndex w),
        β ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w) T := by
    -- The explicit repeated word already gives one basic patching witness for the duplicated cover.
    refine ⟨wordFullSubfamily w, ?_⟩
    simpa [wordPatchingOpen]
      using hw
  rcases
      existsOrderedSubfamily_mem_patchingRefinedOpen_of_exists_mem_patchingOpen
        (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) hbasic with
    ⟨T, hT⟩
  exact ⟨w, T, hT⟩

/-- Helper for Theorem 7.4.3: every restricted map over a duplicated word cover is a fibration
because each duplicated cover member is one of the original cover members. -/
theorem isFibration_restrictPreimage_wordCover (𝒰 : NumerableOpenCover ι B) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    (w : List ι) :
    ∀ k : wordIndex w,
      IsFibration.{v, w, max v w} (p.restrictPreimage ((wordCover 𝒰 w).cover k)) := by
  intro k
  cases k with
  | inl j =>
      -- The left summand just repeats the restricted fibration over the chosen word slot.
      simpa [wordCover, wordIndex] using hlocal (w.get j)
  | inr i =>
      -- The right summand is the original restricted fibration itself.
      simpa [wordCover, wordIndex] using hlocal i

/-- Helper for Theorem 7.4.3: a basic patching lift restricts along the residual refined-open
inclusion. -/
theorem continuousLiftOnPatchingRefinedOpenFromBasic (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) {T : List ι}
    (refinement : NumerableOpenCover.PatchingRefinement T)
    (hT : 0 < refinement.orderedSubfamily.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  obtain ⟨basicLift, hsource, hproj⟩ :=
    continuousLiftOnPatchingOpen 𝒰 hcont (p := p) hlocal hT
  let refinedInclusion :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
        {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont refinement.orderedSubfamily}) :=
    { toFun := fun x ↦
        ⟨x.1,
          NumerableOpenCover.patchingRefinedOpenFrom_subset_patchingOpen 𝒰 hcont refinement x.2⟩
      continuous_toFun := by
        -- The residual refined-open subtype maps continuously to the ambient basic patching subtype.
        have hval :
            Continuous fun x :
                {x : MappingPathSpace p //
                  x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement} ↦
              (x : MappingPathSpace p) := continuous_subtype_val
        exact hval.subtype_mk fun x ↦
          NumerableOpenCover.patchingRefinedOpenFrom_subset_patchingOpen 𝒰 hcont refinement x.2 }
  let lift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
        C(I, E)) :=
    basicLift.comp refinedInclusion
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Restricting the basic patching family does not change the stored starting point.
    simpa [lift, refinedInclusion] using hsource (refinedInclusion x)
  · intro x
    -- Restricting the basic patching family also preserves the projection identity.
    simpa [lift, refinedInclusion] using hproj (refinedInclusion x)

/-- Helper for Theorem 7.4.3: a fixed single-cover lift family restricts along the residual
refined-open inclusion. -/
theorem continuousLiftOnPatchingRefinedOpenFromBasicOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {T : List ι} (refinement : NumerableOpenCover.PatchingRefinement T)
    (hT : 0 < refinement.orderedSubfamily.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  obtain ⟨basicLift, hsource, hproj⟩ :=
    continuousLiftOnPatchingOpenOfSingleCoverLifts 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj hT
  let refinedInclusion :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
        {x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingOpen 𝒰 hcont refinement.orderedSubfamily}) :=
    { toFun := fun x ↦
        ⟨x.1,
          NumerableOpenCover.patchingRefinedOpenFrom_subset_patchingOpen 𝒰 hcont refinement x.2⟩
      continuous_toFun := by
        -- The residual refined-open subtype maps continuously to the ambient basic patching subtype.
        have hval :
            Continuous fun x :
                {x : MappingPathSpace p //
                  x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement} ↦
              (x : MappingPathSpace p) := continuous_subtype_val
        exact hval.subtype_mk fun x ↦
          NumerableOpenCover.patchingRefinedOpenFrom_subset_patchingOpen 𝒰 hcont refinement x.2 }
  let lift :
      C({x : MappingPathSpace p // x.path ∈ NumerableOpenCover.patchingRefinedOpenFrom 𝒰 hcont refinement},
        C(I, E)) :=
    basicLift.comp refinedInclusion
  refine ⟨lift, ?_, ?_⟩
  · intro x
    -- Restricting the basic patching family does not change the stored starting point.
    simpa [lift, refinedInclusion] using hsource (refinedInclusion x)
  · intro x
    -- Restricting the basic patching family also preserves the projection identity.
    simpa [lift, refinedInclusion] using hproj (refinedInclusion x)

/-- Helper for Theorem 7.4.3: each canonical refined neighborhood in a repeated word cover carries
the corresponding continuous family of path lifts. -/
theorem continuousLiftOnWordPatchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)))
    (w : List ι) {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)} (hT : 0 < T.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈
            NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w) T},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  -- Specialize the generic refined-open lifting theorem to the duplicated word cover.
  simpa [NumerableOpenCover.patchingRefinedOpen_eq_from] using
    continuousLiftOnPatchingRefinedOpenFromBasic (𝒰 := wordCover 𝒰 w)
      (hcont := wordCoverContinuous 𝒰 hcont w) (p := p)
      (hlocal := isFibration_restrictPreimage_wordCover 𝒰 hlocal w)
      (refinement := NumerableOpenCover.patchingRefinement T) hT

/-- Helper for Theorem 7.4.3: each canonical refined neighborhood in a repeated word cover
inherits the fixed single-cover lift family chosen once for the original cover. -/
theorem continuousLiftOnWordPatchingRefinedOpenOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (w : List ι) {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)} (hT : 0 < T.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈
            NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w) T},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  have hwordLocal :
      ∀ k : wordIndex w,
        ∃ lift :
            C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ (wordCover 𝒰 w).cover k}, C(I, E)),
          (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
    intro k
    cases k with
    | inl j =>
        -- The left summand of `wordCover` just reuses the chosen lift for the repeated slot.
        refine ⟨liftSingle (w.get j), ?_, ?_⟩
        · intro x
          simpa [wordCover, wordIndex] using hliftSingleSource (w.get j) x
        · intro x
          simpa [wordCover, wordIndex] using hliftSingleProj (w.get j) x
    | inr i =>
        -- The right summand of `wordCover` is exactly the original cover member.
        refine ⟨liftSingle i, ?_, ?_⟩
        · intro x
          simpa [wordCover, wordIndex] using hliftSingleSource i x
        · intro x
          simpa [wordCover, wordIndex] using hliftSingleProj i x
  choose wordLiftSingle hwordSource hwordProj using hwordLocal
  -- Route correction: build the word-level refined lift by restricting the one fixed
  -- `wordCover` basic lift family rather than re-choosing local data inside each chart.
  simpa [NumerableOpenCover.patchingRefinedOpen_eq_from] using
    continuousLiftOnPatchingRefinedOpenFromBasicOfSingleCoverLifts (𝒰 := wordCover 𝒰 w)
      (hcont := wordCoverContinuous 𝒰 hcont w) (p := p)
      wordLiftSingle hwordSource hwordProj
      (refinement := NumerableOpenCover.patchingRefinement T) hT

/-- Helper for Theorem 7.4.3: the canonical refined neighborhood attached to a repeated word
itself inherits the fixed single-cover lift family. -/
theorem continuousLiftOnWordRefinedOpenOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}, C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  -- Normalize the repeated-word refined open to the ambient duplicated-cover refinement API.
  simpa [wordPatchingRefinedOpen] using
    continuousLiftOnWordPatchingRefinedOpenOfSingleCoverLifts 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj w
      (T := wordFullSubfamily w) (by simpa [wordFullSubfamily_length] using hw)

/-- Helper for Theorem 7.4.3: for a nonempty word, the refined patching neighborhood carries a
concrete single-cover lift obtained once and for all from
`continuousLiftOnWordRefinedOpenOfSingleCoverLifts`. -/
noncomputable def wordPatchingRefinedSingleCoverLift
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length) :
    C({x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}, C(I, E)) :=
  Classical.choose <|
    continuousLiftOnWordRefinedOpenOfSingleCoverLifts 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj hw

/-- Helper for Theorem 7.4.3: the canonical refined single-cover lift still starts at the stored
point of the mapping path space. -/
theorem wordPatchingRefinedSingleCoverLift_source
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (x : {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) :
    wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw x 0 =
      x.1.point := by
  -- Read the source equation off the chosen refined lift witness.
  exact
    (Classical.choose_spec <|
      continuousLiftOnWordRefinedOpenOfSingleCoverLifts 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw).1 x

/-- Helper for Theorem 7.4.3: the canonical refined single-cover lift still projects to the
original base path. -/
theorem wordPatchingRefinedSingleCoverLift_proj
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (x : {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) :
    p.comp
        (wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw x) =
      x.1.path := by
  -- The projection equation is the second component of the chosen refined lift witness.
  exact
    (Classical.choose_spec <|
      continuousLiftOnWordRefinedOpenOfSingleCoverLifts 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw).2 x

/-- Helper for Theorem 7.4.3: every point of a basic patching neighborhood in the ambient
duplicated cover has a local neighborhood chart coming either from the current refined piece or
from one predecessor basic piece of the canonical refinement. -/
theorem wordCoverPatchingOpenNeighborhoodCover
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)} {x : MappingPathSpace p}
    (hx :
      x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        T) :
    ({y : MappingPathSpace p |
        y.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w) T} ∈ nhds x) ∨
      ∃ a : (NumerableOpenCover.patchingRefinement T).predecessor,
        {y : MappingPathSpace p |
            y.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)} ∈ nhds x := by
  have hstepCover :=
    patchingOpen_subset_patchingRefinedOpenFrom_union_predecessorPatchingOpen
      (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w)
      (refinement := NumerableOpenCover.patchingRefinement T) hx
  rcases hstepCover with hrefined | hpred
  · -- The residual refined piece already gives the required ambient neighborhood chart.
    left
    simpa [NumerableOpenCover.patchingRefinedOpen_eq_from] using
      (mem_nhds_pulledBackPatchingRefinedOpen (𝒰 := wordCover 𝒰 w)
        (hcont := wordCoverContinuous 𝒰 hcont w) (p := p)
        (T := T) hrefined)
  · -- Otherwise one predecessor basic piece already contains `x.path`.
    right
    rcases Set.mem_iUnion.mp hpred with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact
      mem_nhds_pulledBackPatchingOpen (𝒰 := wordCover 𝒰 w)
        (hcont := wordCoverContinuous 𝒰 hcont w) (p := p) ha

/-- Helper for Theorem 7.4.3: the ambient duplicated-cover neighborhood decomposition can be read
directly inside the subtype domain of the current basic patching neighborhood. -/
theorem wordCoverPatchingOpenNeighborhoodCoverSubtype
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    {x :
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
          T}} :
    ({y :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w) T} |
        y.1.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w) T} ∈ nhds x) ∨
      ∃ a : (NumerableOpenCover.patchingRefinement T).predecessor,
        {y :
            {x : MappingPathSpace p //
              x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                (wordCoverContinuous 𝒰 hcont w) T} |
            y.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)} ∈ nhds x := by
  rcases
      wordCoverPatchingOpenNeighborhoodCover (𝒰 := 𝒰) (hcont := hcont) (p := p)
        (w := w) (T := T) (x := x.1) x.2 with
    hrefined | ⟨a, ha⟩
  · -- Pull the ambient refined neighborhood back along the subtype inclusion.
    left
    simpa using (continuous_subtype_val.tendsto x).eventually hrefined
  · -- Pull the predecessor chart neighborhood back along the same subtype inclusion.
    right
    refine ⟨a, ?_⟩
    simpa using (continuous_subtype_val.tendsto x).eventually ha

/-- Helper for Theorem 7.4.3: the common overlap domain between the refined chart of an ambient
duplicated-cover patching neighborhood and one predecessor chart of its canonical refinement. -/
abbrev wordCoverRefinedPredecessorOverlap
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w))
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :=
  {x : MappingPathSpace p //
    x.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
      (wordCoverContinuous 𝒰 hcont w) T ∧
    x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
      (wordCoverContinuous 𝒰 hcont w)
      ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)}

/-- Helper for Theorem 7.4.3: the refined/predecessor overlap subtype maps continuously to the
ambient refined chart. -/
theorem continuous_wordCoverRefinedPredecessorOverlapToRefined
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    Continuous fun x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a ↦
      (⟨x.1, x.2.1⟩ :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w) T}) := by
  -- This inclusion only forgets the predecessor-chart component of the overlap subtype.
  have hval :
      Continuous fun x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a ↦
        (x : MappingPathSpace p) := continuous_subtype_val
  exact hval.subtype_mk fun x ↦ x.2.1

/-- Helper for Theorem 7.4.3: the refined/predecessor overlap subtype maps continuously to the
ambient predecessor chart. -/
theorem continuous_wordCoverRefinedPredecessorOverlapToPredecessor
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    Continuous fun x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a ↦
      (⟨x.1, x.2.2⟩ :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)}) := by
  -- This inclusion only forgets the refined-chart component of the overlap subtype.
  have hval :
      Continuous fun x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a ↦
        (x : MappingPathSpace p) := continuous_subtype_val
  exact hval.subtype_mk fun x ↦ x.2.2

/-- Helper for Theorem 7.4.3: the canonical overlap inclusion into the ambient refined chart. -/
noncomputable def wordCoverRefinedPredecessorOverlapToRefined
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w))
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    C(wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a,
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w) T}) :=
  { toFun := fun x ↦ ⟨x.1, x.2.1⟩
    continuous_toFun :=
      continuous_wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) (w := w)
        (T := T) a }

/-- Helper for Theorem 7.4.3: forgetting the refined-overlap inclusion back to the ambient
mapping path changes only subtype bookkeeping. -/
@[simp] theorem wordCoverRefinedPredecessorOverlapToRefined_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor)
    (x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a) :
    ((wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w T a x :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingRefinedOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w) T}) :
      MappingPathSpace p) = x := by
  -- The overlap-to-refined chart map simply forgets one conjunct of the subtype witness.
  rfl

/-- Helper for Theorem 7.4.3: the canonical overlap inclusion into the ambient predecessor chart.
-/
noncomputable def wordCoverRefinedPredecessorOverlapToPredecessor
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w))
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    C(wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a,
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)}) :=
  { toFun := fun x ↦ ⟨x.1, x.2.2⟩
    continuous_toFun :=
      continuous_wordCoverRefinedPredecessorOverlapToPredecessor 𝒰 hcont (p := p) (w := w)
        (T := T) a }

/-- Helper for Theorem 7.4.3: forgetting the predecessor-overlap inclusion back to the ambient
mapping path also changes only subtype bookkeeping. -/
@[simp] theorem wordCoverRefinedPredecessorOverlapToPredecessor_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor)
    (x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a) :
    ((wordCoverRefinedPredecessorOverlapToPredecessor 𝒰 hcont (p := p) w T a x :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)}) :
      MappingPathSpace p) = x := by
  -- The overlap-to-predecessor chart map forgets the refined component of the overlap witness.
  rfl

/-- Helper for Theorem 7.4.3: the mixed refined/predecessor overlap is compared in the shorter
ordinary-word chart obtained by forgetting the ambient predecessor bookkeeping once and for all. -/
noncomputable def wordCoverRefinedPredecessorOverlapToShorterWord
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (T : NumerableOpenCover.OrderedSubfamily (wordIndex w))
    (a : (NumerableOpenCover.patchingRefinement T).predecessor) :
    C(wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a,
      {x : MappingPathSpace p //
        x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))}) :=
  (wordCoverPredecessorPatchingOpenInclusion 𝒰 hcont (p := p) (w := w) (T := T) a).comp
    (wordCoverRefinedPredecessorOverlapToPredecessor 𝒰 hcont (p := p) w T a)

/-- Helper for Theorem 7.4.3: forgetting the overlap-to-shorter-word adapter still recovers the
same ambient mapping path, so later overlap equalities can stay in one spelling world. -/
@[simp] theorem wordCoverRefinedPredecessorOverlapToShorterWord_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a : (NumerableOpenCover.patchingRefinement T).predecessor)
    (x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w T a) :
    ((wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w T a x :
        {x : MappingPathSpace p //
          x.path ∈ wordPatchingOpen 𝒰 hcont
            (wordOfOrderedSubfamily w
              ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))}) :
      MappingPathSpace p) = x := by
  -- The composed adapter only repackages subtype membership data.
  rfl

/-- Helper for Theorem 7.4.3: every point of a basic word patching neighborhood has a local
neighborhood chart coming either from the current refined piece or from one predecessor basic
piece of the canonical refinement. -/
theorem wordPatchingOpenNeighborhoodCover
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {x : MappingPathSpace p} (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w) :
    ({y : MappingPathSpace p | y.path ∈ wordPatchingRefinedOpen 𝒰 hcont w} ∈ nhds x) ∨
      ∃ a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor,
        {y : MappingPathSpace p |
            y.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a)} ∈ nhds x := by
  -- Specialize the ambient duplicated-cover neighborhood decomposition to the full repeated word.
  simpa [wordPatchingOpen, wordPatchingRefinedOpen] using
    (wordCoverPatchingOpenNeighborhoodCover (𝒰 := 𝒰) (hcont := hcont) (p := p)
      (w := w) (T := wordFullSubfamily w)
      (x := x) (by simpa [wordPatchingOpen] using hx))

/-- Helper for Theorem 7.4.3: the neighborhood cover of one word patching neighborhood can be read
directly inside the subtype domain of that neighborhood. -/
theorem wordPatchingOpenNeighborhoodCoverSubtype
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}} :
    ({y : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} |
        y.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w} ∈ nhds x) ∨
      ∃ a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor,
        {y : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} |
            y.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a)} ∈ nhds x := by
  rcases wordPatchingOpenNeighborhoodCover (𝒰 := 𝒰) (hcont := hcont) (p := p) x.2 with
    hrefined | ⟨a, ha⟩
  · -- Pull the ambient refined neighborhood back along the subtype inclusion.
    left
    simpa using (continuous_subtype_val.tendsto x).eventually hrefined
  · -- Pull the ambient predecessor-chart neighborhood back along the same subtype inclusion.
    right
    refine ⟨a, ?_⟩
    simpa using (continuous_subtype_val.tendsto x).eventually ha

/-- Helper for Theorem 7.4.3: the refined chart inside one word patching neighborhood maps
continuously to the ambient refined-word chart. -/
theorem continuous_wordPatchingRefinedChartInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι} :
    Continuous fun x :
        {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
          x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w} ↦
      (⟨x.1.1, x.2⟩ :
        {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) := by
  -- This map only forgets the ambient basic-word membership witness.
  have hval :
      Continuous fun x :
          {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
            x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w} ↦
        (x.1 : MappingPathSpace p) := continuous_subtype_val.comp continuous_subtype_val
  exact hval.subtype_mk fun x ↦ x.2

/-- Helper for Theorem 7.4.3: the canonical inclusion from the refined chart inside one word
patching neighborhood to the ambient refined-word chart. -/
noncomputable def wordPatchingRefinedChartInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι) :
    C({x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w},
      {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    continuous_toFun := continuous_wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) }

/-- Helper for Theorem 7.4.3: forgetting the refined-chart inclusion back to `MappingPathSpace p`
changes only subtype bookkeeping. -/
@[simp] theorem wordPatchingRefinedChartInclusion_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (x :
      {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) :
    ((wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w x :
        {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}) :
      MappingPathSpace p) = x := by
  -- The refined-chart inclusion forgets only the outer word-patching witness.
  rfl

/-- Helper for Theorem 7.4.3: a predecessor chart inside one word patching neighborhood maps
continuously to the ambient predecessor chart of the duplicated-cover refinement. -/
theorem continuous_wordPatchingPredecessorChartInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    Continuous fun x :
        {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
          x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a)} ↦
      (⟨x.1.1, x.2⟩ :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a)}) := by
  -- This map also just forgets the outer basic-word witness.
  have hval :
      Continuous fun x :
          {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
            x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a)} ↦
        (x.1 : MappingPathSpace p) := continuous_subtype_val.comp continuous_subtype_val
  exact hval.subtype_mk fun x ↦ x.2

/-- Helper for Theorem 7.4.3: the canonical inclusion from a predecessor chart inside one word
patching neighborhood to the ambient predecessor chart. -/
noncomputable def wordPatchingPredecessorChartInclusion
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    C({x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)},
      {x : MappingPathSpace p //
        x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
            a)}) :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    continuous_toFun :=
      continuous_wordPatchingPredecessorChartInclusion 𝒰 hcont (p := p) a }

/-- Helper for Theorem 7.4.3: forgetting the predecessor-chart inclusion back to
`MappingPathSpace p` changes only subtype bookkeeping. -/
@[simp] theorem wordPatchingPredecessorChartInclusion_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    (x :
      {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
            a)}) :
    ((wordPatchingPredecessorChartInclusion 𝒰 hcont (p := p) w a x :
        {x : MappingPathSpace p //
          x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a)}) :
      MappingPathSpace p) = x := by
  -- The predecessor-chart inclusion forgets only the outer word-patching witness.
  rfl

/-- Helper for Theorem 7.4.3: a predecessor chart inside one word patching neighborhood maps
directly to the shorter-word basic patching neighborhood attached to that predecessor. -/
noncomputable def wordPatchingPredecessorChartToShorterWord
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι)
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor) :
    C({x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)},
      {x : MappingPathSpace p //
        x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))}) :=
  (predecessorWordPatchingOpenInclusion 𝒰 hcont (p := p) a).comp
    (wordPatchingPredecessorChartInclusion 𝒰 hcont (p := p) w a)

/-- Helper for Theorem 7.4.3: forgetting the direct predecessor-chart map to the shorter word
still recovers the same ambient mapping path. -/
@[simp] theorem wordPatchingPredecessorChartToShorterWord_coe
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    (x :
      {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
            a)}) :
    ((wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a x :
        {x : MappingPathSpace p //
          x.path ∈ wordPatchingOpen 𝒰 hcont
            (wordOfOrderedSubfamily w
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a))}) :
      MappingPathSpace p) = x := by
  -- The composed map only repackages subtype membership data on the predecessor chart.
  simp [wordPatchingPredecessorChartToShorterWord]

/-- Helper for Theorem 7.4.3: an ambient refined/predecessor overlap equality immediately
descends to the subtype chart interface used by `ContinuousMap.liftCover`. -/
theorem wordRefinedLiftCompatWithPredecessorLift
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    (liftShorter :
      C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))},
        C(I, E)))
    (hambient :
      ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
        wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw
            (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
              (wordFullSubfamily w) a x) =
          liftShorter
            (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
              (wordFullSubfamily w) a x))
    (x :
      {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
        x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w ∧
          x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
            (wordCoverContinuous 𝒰 hcont w)
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a)}) :
    wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw
        (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w ⟨x.1, x.2.1⟩) =
      liftShorter
        (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a ⟨x.1, x.2.2⟩) := by
  -- Repackage the subtype overlap point into the ambient overlap object and then reuse the
  -- ambient comparison after normalizing both chart maps back to the same mapping path.
  let xAmbient : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a :=
    ⟨x.1.1, ⟨x.2.1, x.2.2⟩⟩
  simpa [xAmbient] using hambient xAmbient

/-- Helper for Theorem 7.4.3: a recursive lift on the shorter predecessor word restricts along
`predecessorWordPatchingOpenInclusion 𝒰 hcont a` to a lift on the corresponding predecessor chart
inside the current word patching neighborhood. -/
theorem predecessorPieceLiftFromShorterWord
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} {w : List ι}
    (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    (liftShorter :
      C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))},
        C(I, E)))
    (hsourceShorter :
      ∀ x, liftShorter x 0 = x.1.point)
    (hprojShorter :
      ∀ x, p.comp (liftShorter x) = x.1.path) :
    ∃ lift :
        C({x : MappingPathSpace p //
            x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
              (wordCoverContinuous 𝒰 hcont w)
              ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                a)},
          C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  -- Reuse the ambient predecessor transport API specialized to the full slot family of `w`.
  exact
    wordCoverPredecessorPieceLiftFromShorterWord 𝒰 hcont (p := p) (w := w)
      (T := wordFullSubfamily w) a liftShorter hsourceShorter hprojShorter

/-- Helper for Theorem 7.4.3: predecessor basic pieces inside one word patching neighborhood are
already compatible once the shorter-word recursion is known to be compatible by length. -/
theorem predecessorWordLiftCompatOfShorterWords
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftOpen :
      ∀ w : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)))
    (hcompatOpen :
      ∀ {w w' : List ι} (_ : w'.length ≤ w.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont w'),
          liftOpen w ⟨x, hx⟩ = liftOpen w' ⟨x, hx'⟩)
    {w : List ι}
    (a b : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
    {x : MappingPathSpace p}
    (hxA :
      x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a))
    (hxB :
      x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily b)) :
    liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a))
        ⟨x, mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont a hxA⟩ =
      liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily b))
        ⟨x, mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont b hxB⟩ := by
  let wa :=
    wordOfOrderedSubfamily w
      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)
  let wb :=
    wordOfOrderedSubfamily w
      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily b)
  have hwa : x.path ∈ wordPatchingOpen 𝒰 hcont wa := by
    -- Re-read the predecessor chart in the ambient duplicated cover as a shorter ordinary word.
    simpa [wa] using mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont a hxA
  have hwb : x.path ∈ wordPatchingOpen 𝒰 hcont wb := by
    -- The same normalization applies to the second predecessor chart.
    simpa [wb] using mem_wordPatchingOpen_of_mem_predecessorPatchingOpen 𝒰 hcont b hxB
  rcases Nat.le_total wa.length wb.length with hab | hba
  · -- Compare through the longer predecessor word and then reverse the resulting equality.
    exact (hcompatOpen (w := wb) (w' := wa) hab x hwb hwa).symm
  · -- Or compare in the opposite direction if the first predecessor word is longer.
    exact hcompatOpen (w := wa) (w' := wb) hba x hwa hwb

/-- Helper for Theorem 7.4.3: predecessor basic pieces inside one ambient duplicated-cover
patching neighborhood are already compatible once the shorter-word recursion is known to be
compatible by length. -/
theorem wordCoverPredecessorLiftCompatOfShorterWords
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftOpen :
      ∀ w : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)))
    (hcompatOpen :
      ∀ {w w' : List ι} (_ : w'.length ≤ w.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont w'),
          liftOpen w ⟨x, hx⟩ = liftOpen w' ⟨x, hx'⟩)
    {w : List ι} {T : NumerableOpenCover.OrderedSubfamily (wordIndex w)}
    (a b : (NumerableOpenCover.patchingRefinement T).predecessor)
    {x : MappingPathSpace p}
    (hxA :
      x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))
    (hxB :
      x.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily b)) :
    liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a))
        ⟨x,
          mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
            (orderedSubfamily_length_pos_of_mem_patchingOpen
              (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) hxA)
            hxA⟩ =
      liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily b))
        ⟨x,
          mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
            (orderedSubfamily_length_pos_of_mem_patchingOpen
              (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) hxB)
            hxB⟩ := by
  let wa :=
    wordOfOrderedSubfamily w
      ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily a)
  let wb :=
    wordOfOrderedSubfamily w
      ((NumerableOpenCover.patchingRefinement T).predecessorSubfamily b)
  have hwa : x.path ∈ wordPatchingOpen 𝒰 hcont wa := by
    -- Re-read the predecessor chart in the ambient duplicated cover as a shorter ordinary word.
    simpa [wa] using
      mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
        (orderedSubfamily_length_pos_of_mem_patchingOpen
          (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) hxA)
        hxA
  have hwb : x.path ∈ wordPatchingOpen 𝒰 hcont wb := by
    -- The same normalization applies to the second predecessor chart.
    simpa [wb] using
      mem_wordPatchingOpen_of_mem_patchingOpen_wordCover 𝒰 hcont
        (orderedSubfamily_length_pos_of_mem_patchingOpen
          (𝒰 := wordCover 𝒰 w) (hcont := wordCoverContinuous 𝒰 hcont w) hxB)
        hxB
  rcases Nat.le_total wa.length wb.length with hab | hba
  · -- Compare through the longer predecessor word and then reverse the resulting equality.
    exact (hcompatOpen (w := wb) (w' := wa) hab x hwb hwa).symm
  · -- Or compare in the opposite direction if the first predecessor word is longer.
    exact hcompatOpen (w := wa) (w' := wb) hba x hwa hwb

/-- Helper for Theorem 7.4.3: once `MappingPathSpace p` is covered by neighbourhoods carrying
pairwise-compatible local continuous lifts, the final gluing step produces a global continuous
path lifting function. -/
theorem nonempty_continuousPathLiftingFunction_of_localLiftCover {κ : Type*} {p : C(E, B)}
    (S : κ → Set (MappingPathSpace p)) (lift : ∀ k, C(S k, C(I, E)))
    (hcompat :
      ∀ i j (x : MappingPathSpace p) (hxi : x ∈ S i) (hxj : x ∈ S j),
        lift i ⟨x, hxi⟩ = lift j ⟨x, hxj⟩)
    (hcover : ∀ x : MappingPathSpace p, ∃ i, S i ∈ nhds x)
    (hsource : ∀ i (x : S i), lift i x 0 = x.1.point)
    (hproj : ∀ i (x : S i), p.comp (lift i x) = x.1.path) :
    Nonempty (ContinuousPathLiftingFunction p) := by
  let globalLift : C(MappingPathSpace p, C(I, E)) :=
    ContinuousMap.liftCover S lift hcompat hcover
  refine ⟨
    { toContinuousMap := globalLift
      source_eq := ?_
      proj_comp_eq := ?_ }⟩
  · intro x
    rcases hcover x with ⟨i, hi⟩
    let xi : S i := ⟨x, mem_of_mem_nhds hi⟩
    have hglue : globalLift x = lift i xi := by
      -- Evaluate the glued map through one neighborhood chart containing `x`.
      simpa [globalLift, xi] using
        (ContinuousMap.liftCover_coe (S := S) (φ := lift) (hφ := hcompat) (hS := hcover) xi)
    -- The local source equation passes through the glued map on that chart.
    calc
      globalLift x 0 = lift i xi 0 := congrArg (fun γ : C(I, E) ↦ γ 0) hglue
      _ = x.point := by simpa [xi] using hsource i xi
  · intro x
    rcases hcover x with ⟨i, hi⟩
    let xi : S i := ⟨x, mem_of_mem_nhds hi⟩
    have hglue : globalLift x = lift i xi := by
      -- Evaluate the glued map through one neighborhood chart containing `x`.
      simpa [globalLift, xi] using
        (ContinuousMap.liftCover_coe (S := S) (φ := lift) (hφ := hcompat) (hS := hcover) xi)
    -- The local projection equation likewise passes through the glued map on that chart.
    ext t
    calc
      (p.comp (globalLift x)) t = (p.comp (lift i xi)) t := by
        exact congrArg (fun γ : C(I, E) ↦ (p.comp γ) t) hglue
      _ = x.path t := by
        simpa [xi] using ContinuousMap.congr_fun (hproj i xi) t

/-- Helper for Theorem 7.4.3: each basic word patching neighborhood inherits the canonical
single-cover lift family coming from the duplicated cover attached to that word. -/
theorem continuousLiftOnWordPatchingOpenOfSingleCoverLifts
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (w : List ι) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  by_cases hw : 0 < w.length
  · have hwordLocal :
        ∀ k : wordIndex w,
          ∃ lift :
              C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ (wordCover 𝒰 w).cover k}, C(I, E)),
            (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
      intro k
      cases k with
      | inl j =>
          -- The left summand of `wordCover` just reuses the chosen lift for the repeated slot.
          refine ⟨liftSingle (w.get j), ?_, ?_⟩
          · intro x
            simpa [wordCover, wordIndex] using hliftSingleSource (w.get j) x
          · intro x
            simpa [wordCover, wordIndex] using hliftSingleProj (w.get j) x
      | inr i =>
          -- The right summand of `wordCover` is exactly the original cover member.
          refine ⟨liftSingle i, ?_, ?_⟩
          · intro x
            simpa [wordCover, wordIndex] using hliftSingleSource i x
          · intro x
            simpa [wordCover, wordIndex] using hliftSingleProj i x
    choose wordLiftSingle hwordSource hwordProj using hwordLocal
    -- Specialize the canonical basic-patching lift theorem to the duplicated cover of `w`.
    simpa [wordPatchingOpen] using
      continuousLiftOnPatchingOpenOfSingleCoverLifts (𝒰 := wordCover 𝒰 w)
        (hcont := wordCoverContinuous 𝒰 hcont w) (p := p)
        wordLiftSingle hwordSource hwordProj
        (T := wordFullSubfamily w) (by simpa [wordFullSubfamily_length] using hw)
  · let hEmpty :
        IsEmpty {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} := by
        refine ⟨?_⟩
        intro x
        apply hw
        simpa [wordPatchingOpen, wordFullSubfamily_length] using
          (orderedSubfamily_length_pos_of_mem_patchingOpen (𝒰 := wordCover 𝒰 w)
            (hcont := wordCoverContinuous 𝒰 hcont w) x.2)
    let emptyLift :
        C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)) :=
      { toFun := isEmptyElim
        continuous_toFun := by
          -- The empty-word patching neighborhood has empty domain, so any target family is
          -- continuous once we identify every preimage as `∅`.
          refine continuous_def.2 ?_
          intro s hs
          have hpreimage :
              (isEmptyElim :
                {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} →
                  C(I, E)) ⁻¹' s = ∅ := by
            ext x
            exact False.elim (hEmpty.false x)
          rw [hpreimage]
          exact isOpen_empty }
    refine ⟨emptyLift, ?_, ?_⟩
    · intro x
      exact False.elim (hEmpty.false x)
    · intro x
      exact False.elim (hEmpty.false x)

/-- Helper for Theorem 7.4.3: the canonical basic patching neighborhood of a repeated word carries
one fixed single-cover lift family, named explicitly so later recursive gluing can refer to a
stable constructor instead of a local `choose` witness. -/
noncomputable def wordPatchingOpenSingleCoverLift
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (w : List ι) :
    C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)) :=
  Classical.choose <|
    continuousLiftOnWordPatchingOpenOfSingleCoverLifts 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj w

/-- Helper for Theorem 7.4.3: the explicit basic single-cover word lift still starts at the stored
point of the mapping path space. -/
theorem wordPatchingOpenSingleCoverLift_source
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (w : List ι)
    (x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}) :
    wordPatchingOpenSingleCoverLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj w x 0 =
      x.1.point := by
  -- Read the source equation off the chosen basic lift witness.
  exact
    (Classical.choose_spec <|
      continuousLiftOnWordPatchingOpenOfSingleCoverLifts 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj w).1 x

/-- Helper for Theorem 7.4.3: the explicit basic single-cover word lift still projects to the
original base path. -/
theorem wordPatchingOpenSingleCoverLift_proj
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    (w : List ι)
    (x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}) :
    p.comp
        (wordPatchingOpenSingleCoverLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj w x) =
      x.1.path := by
  -- The projection equation is the second component of the chosen basic lift witness.
  exact
    (Classical.choose_spec <|
      continuousLiftOnWordPatchingOpenOfSingleCoverLifts 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj w).2 x

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step works on the current basic
word patching neighborhood. -/
abbrev wordPatchingOpenStepDomain
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι) :=
  {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step is indexed by the refined
chart together with the predecessor charts of the canonical refinement. -/
abbrev wordPatchingOpenStepPred (w : List ι) :=
  (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step uses the refined chart and
all predecessor charts as its local cover. -/
def wordPatchingOpenStepChartSet
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)} (w : List ι) :
    Option (wordPatchingOpenStepPred w) →
      Set (wordPatchingOpenStepDomain 𝒰 hcont (p := p) w)
  | none => {x | x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}
  | some a =>
      {x | x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
        (wordCoverContinuous 𝒰 hcont w)
        ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)}

/-- Helper for Theorem 7.4.3: the refined chart of the explicit gluing step uses the canonical
refined single-cover lift, while predecessor charts immediately descend to shorter words. -/
noncomputable def wordPatchingOpenStepChartLift
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E))) :
    ∀ i : Option (wordPatchingOpenStepPred w),
      C(wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w i, C(I, E))
  | none =>
      -- The refined chart uses the canonical refined single-cover lift.
      (wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw).comp
        (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w)
  | some a =>
      -- Each predecessor chart is read immediately as the shorter predecessor word.
      (liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
            a))).comp
        (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a)

/-- Helper for Theorem 7.4.3: the explicit chart family of the nonempty-word gluing step covers
the whole basic word patching neighborhood. -/
theorem wordPatchingOpenStepChartCover
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    {w : List ι} :
    ∀ x : wordPatchingOpenStepDomain 𝒰 hcont (p := p) w,
      ∃ i, wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w i ∈ nhds x := by
  intro x
  -- The basic word neighborhood is covered by its refined chart and its predecessor charts.
  rcases
      wordPatchingOpenNeighborhoodCoverSubtype (𝒰 := 𝒰) (hcont := hcont) (p := p) (w := w)
        (x := x) with
    hrefined | ⟨a, ha⟩
  · exact ⟨none, hrefined⟩
  · exact ⟨some a, ha⟩

/-- Helper for Theorem 7.4.3: the explicit chart family of the nonempty-word gluing step is
pairwise compatible on overlaps. -/
theorem wordPatchingOpenStepChartCompat
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x)) :
    ∀ i j (x : wordPatchingOpenStepDomain 𝒰 hcont (p := p) w)
      (hxi : x ∈ wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w i)
      (hxj : x ∈ wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w j),
        wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen i ⟨x, hxi⟩ =
          wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen j ⟨x, hxj⟩ := by
  intro i j x hxi hxj
  cases i with
  | none =>
      cases j with
      | none =>
          -- On one refined chart, both sides evaluate the same chart map at the same point.
          have hxEq :
              (⟨x, hxi⟩ :
                wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w none) =
              ⟨x, hxj⟩ := by
            apply Subtype.ext
            rfl
          exact congrArg
            (wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw liftOpen none) hxEq
      | some a =>
          -- Mixed overlaps are normalized once through the closed subtype adapter theorem.
          let xOverlap :
              {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
                x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w ∧
                  x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                    (wordCoverContinuous 𝒰 hcont w)
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a)} :=
            ⟨x, ⟨hxi, hxj⟩⟩
          simpa [wordPatchingOpenStepChartLift, xOverlap] using
            wordRefinedLiftCompatWithPredecessorLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw a
              (liftShorter :=
                liftOpen
                  (wordOfOrderedSubfamily w
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a)))
              (hambient := hambient a) xOverlap
  | some a =>
      cases j with
      | none =>
          -- Reverse the same mixed-overlap comparison when the predecessor chart comes first.
          let xOverlap :
              {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
                x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w ∧
                  x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                    (wordCoverContinuous 𝒰 hcont w)
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a)} :=
            ⟨x, ⟨hxj, hxi⟩⟩
          simpa [wordPatchingOpenStepChartLift, xOverlap] using
            (wordRefinedLiftCompatWithPredecessorLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw a
              (liftShorter :=
                liftOpen
                  (wordOfOrderedSubfamily w
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a)))
              (hambient := hambient a) xOverlap).symm
      | some b =>
          -- Two predecessor charts compare by descending to the already-compatible shorter words.
          simpa [wordPatchingOpenStepChartLift] using
            predecessorWordLiftCompatOfShorterWords 𝒰 hcont (p := p)
              liftOpen hcompatOpen a b (x := x.1) hxi hxj

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step is the `liftCover`
construction hidden inside `continuousLiftOnWordPatchingOpenStep`. -/
noncomputable def wordPatchingOpenStepLift
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x)) :
    C(wordPatchingOpenStepDomain 𝒰 hcont (p := p) w, C(I, E)) :=
  ContinuousMap.liftCover
    (wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w)
    (wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj hw liftOpen)
    (wordPatchingOpenStepChartCompat 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient)
    (wordPatchingOpenStepChartCover 𝒰 hcont (p := p) (w := w))

/-- Helper for Theorem 7.4.3: evaluating the explicit nonempty-word gluing step on the refined
chart recovers the canonical refined single-cover lift. -/
theorem wordPatchingOpenStepLift_refined_eq
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x))
    (x : wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w none) :
    wordPatchingOpenStepLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x.1 =
      wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw
        (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w x) := by
  -- Read the explicit glued map through the refined chart, then simplify that chart branch.
  have hglue :
      wordPatchingOpenStepLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x.1 =
        wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen none x := by
    simpa [wordPatchingOpenStepLift] using
      (ContinuousMap.liftCover_coe
        (S := wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w)
        (φ := wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen)
        (hφ := wordPatchingOpenStepChartCompat 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient)
        (hS := wordPatchingOpenStepChartCover 𝒰 hcont (p := p) (w := w))
        x)
  simpa [wordPatchingOpenStepChartLift] using hglue

/-- Helper for Theorem 7.4.3: evaluating the explicit nonempty-word gluing step on a predecessor
chart recovers the recursive shorter-word lift. -/
theorem wordPatchingOpenStepLift_predecessor_eq
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x))
    (a : wordPatchingOpenStepPred w)
    (x : wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w (some a)) :
    wordPatchingOpenStepLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x.1 =
      liftOpen
        (wordOfOrderedSubfamily w
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a))
        (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a x) := by
  -- Read the explicit glued map through the predecessor chart, then simplify that chart branch.
  have hglue :
      wordPatchingOpenStepLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x.1 =
        wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen (some a) x := by
    simpa [wordPatchingOpenStepLift] using
      (ContinuousMap.liftCover_coe
        (S := wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w)
        (φ := wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen)
        (hφ := wordPatchingOpenStepChartCompat 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient)
        (hS := wordPatchingOpenStepChartCover 𝒰 hcont (p := p) (w := w))
        x)
  simpa [wordPatchingOpenStepChartLift] using hglue

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step starts at the stored
point of the mapping path. -/
theorem wordPatchingOpenStepLift_source
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hsourceOpen :
      ∀ u x, liftOpen u x 0 = x.1.point)
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x))
    (x : wordPatchingOpenStepDomain 𝒰 hcont (p := p) w) :
    wordPatchingOpenStepLift 𝒰 hcont (p := p)
        liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x 0 =
      x.1.point := by
  rcases wordPatchingOpenStepChartCover (𝒰 := 𝒰) (hcont := hcont) (p := p) (w := w) x with
    ⟨i, hi⟩
  let xi : wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w i := ⟨x, mem_of_mem_nhds hi⟩
  have hglue :
      wordPatchingOpenStepLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x =
        wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen i xi := by
    -- Read the glued map through one chart containing `x`.
    simpa [wordPatchingOpenStepLift, xi] using
      (ContinuousMap.liftCover_coe
        (S := wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w)
        (φ := wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen)
        (hφ := wordPatchingOpenStepChartCompat 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient)
        (hS := wordPatchingOpenStepChartCover 𝒰 hcont (p := p) (w := w))
        xi)
  cases i with
  | none =>
      -- On the refined chart, the step lift starts where the refined single-cover lift starts.
      calc
        wordPatchingOpenStepLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x 0 =
          wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen none xi 0 :=
          congrArg (fun γ : C(I, E) ↦ γ 0) hglue
        _ = x.1.point := by
            simpa [wordPatchingOpenStepChartLift, xi] using
              wordPatchingRefinedSingleCoverLift_source 𝒰 hcont (p := p)
                liftSingle hliftSingleSource hliftSingleProj hw
                (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w xi)
  | some a =>
      -- On a predecessor chart, the step lift starts where the recursive shorter-word lift starts.
      calc
        wordPatchingOpenStepLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x 0 =
          wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
            liftSingle hliftSingleSource hliftSingleProj hw liftOpen (some a) xi 0 :=
          congrArg (fun γ : C(I, E) ↦ γ 0) hglue
        _ = x.1.point := by
            simpa [wordPatchingOpenStepChartLift, xi] using
              hsourceOpen
                (wordOfOrderedSubfamily w
                  ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                    a))
                (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a xi)

/-- Helper for Theorem 7.4.3: the explicit nonempty-word gluing step projects to the original
base path. -/
theorem wordPatchingOpenStepLift_proj
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hprojOpen :
      ∀ u x, p.comp (liftOpen u x) = x.1.path)
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : wordPatchingOpenStepPred w,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x))
    (x : wordPatchingOpenStepDomain 𝒰 hcont (p := p) w) :
    p.comp
        (wordPatchingOpenStepLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x) =
      x.1.path := by
  rcases wordPatchingOpenStepChartCover (𝒰 := 𝒰) (hcont := hcont) (p := p) (w := w) x with
    ⟨i, hi⟩
  let xi : wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w i := ⟨x, mem_of_mem_nhds hi⟩
  have hglue :
      wordPatchingOpenStepLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x =
        wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen i xi := by
    -- Read the glued map through one chart containing `x`.
    simpa [wordPatchingOpenStepLift, xi] using
      (ContinuousMap.liftCover_coe
        (S := wordPatchingOpenStepChartSet 𝒰 hcont (p := p) w)
        (φ := wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen)
        (hφ := wordPatchingOpenStepChartCompat 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient)
        (hS := wordPatchingOpenStepChartCover 𝒰 hcont (p := p) (w := w))
        xi)
  cases i with
  | none =>
      -- On the refined chart, the step lift projects through the refined single-cover lift.
      ext t
      calc
        (p.comp
            (wordPatchingOpenStepLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x)) t =
          (p.comp
            (wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw liftOpen none xi)) t := by
            exact congrArg (fun γ : C(I, E) ↦ (p.comp γ) t) hglue
        _ = x.1.path t := by
            simpa [wordPatchingOpenStepChartLift, xi] using
              ContinuousMap.congr_fun
                (wordPatchingRefinedSingleCoverLift_proj 𝒰 hcont (p := p)
                  liftSingle hliftSingleSource hliftSingleProj hw
                  (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w xi)) t
  | some a =>
      -- On a predecessor chart, the step lift projects through the recursive shorter-word lift.
      ext t
      calc
        (p.comp
            (wordPatchingOpenStepLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw liftOpen hcompatOpen hambient x)) t =
          (p.comp
            (wordPatchingOpenStepChartLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw liftOpen (some a) xi)) t := by
            exact congrArg (fun γ : C(I, E) ↦ (p.comp γ) t) hglue
        _ = x.1.path t := by
            simpa [wordPatchingOpenStepChartLift, xi] using
              ContinuousMap.congr_fun
                (hprojOpen
                  (wordOfOrderedSubfamily w
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a))
                  (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a xi)) t

/-- Helper for Theorem 7.4.3: once the fixed single-cover lift family is upgraded to a recursive
coherent system on canonical word neighborhoods, the generic local-to-global gluing theorem
produces a continuous path lifting function. -/
theorem continuousLiftOnWordPatchingOpenStep
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path)
    {w : List ι} (hw : 0 < w.length)
    (liftOpen :
      ∀ u : List ι, C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont u}, C(I, E)))
    (hsourceOpen :
      ∀ u x, liftOpen u x 0 = x.1.point)
    (hprojOpen :
      ∀ u x, p.comp (liftOpen u x) = x.1.path)
    (hcompatOpen :
      ∀ {u u' : List ι} (_ : u'.length ≤ u.length) (x : MappingPathSpace p)
        (hx : x.path ∈ wordPatchingOpen 𝒰 hcont u)
        (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont u'),
          liftOpen u ⟨x, hx⟩ = liftOpen u' ⟨x, hx'⟩)
    (hambient :
      ∀ a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor,
        ∀ x : wordCoverRefinedPredecessorOverlap 𝒰 hcont (p := p) w (wordFullSubfamily w) a,
          wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
              liftSingle hliftSingleSource hliftSingleProj hw
              (wordCoverRefinedPredecessorOverlapToRefined 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x) =
            liftOpen
              (wordOfOrderedSubfamily w
                ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                  a))
              (wordCoverRefinedPredecessorOverlapToShorterWord 𝒰 hcont (p := p) w
                (wordFullSubfamily w) a x)) :
    ∃ lift :
        C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)),
      (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
  let Dw := {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}
  let Pred := (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor
  let S : Option Pred → Set Dw
    | none => {x | x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}
    | some a =>
        {x | x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
          (wordCoverContinuous 𝒰 hcont w)
          ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily a)}
  let φ : ∀ i : Option Pred, C(S i, C(I, E))
    | none =>
        -- The refined chart uses the canonical refined single-cover lift.
        (wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
          liftSingle hliftSingleSource hliftSingleProj hw).comp
          (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w)
    | some a =>
        -- Each predecessor chart is read immediately as the shorter predecessor word.
        (liftOpen
          (wordOfOrderedSubfamily w
            ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
              a))).comp
          (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a)
  have hS : ∀ x : Dw, ∃ i, S i ∈ nhds x := by
    intro x
    -- The basic word neighborhood is covered by its refined chart and its predecessor charts.
    rcases
        wordPatchingOpenNeighborhoodCoverSubtype (𝒰 := 𝒰) (hcont := hcont) (p := p) (w := w)
          (x := x) with
      hrefined | ⟨a, ha⟩
    · exact ⟨none, hrefined⟩
    · exact ⟨some a, ha⟩
  have hφ :
      ∀ i j (x : Dw) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    cases i with
    | none =>
        cases j with
        | none =>
            -- On one refined chart, both sides evaluate the same chart map at the same point.
            have hxEq : (⟨x, hxi⟩ : S none) = ⟨x, hxj⟩ := by
              apply Subtype.ext
              rfl
            exact congrArg (φ none) hxEq
        | some a =>
            -- Mixed overlaps are normalized once through the closed subtype adapter theorem.
            let xOverlap :
                {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
                  x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w ∧
                    x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                      (wordCoverContinuous 𝒰 hcont w)
                      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                        a)} :=
              ⟨x, ⟨hxi, hxj⟩⟩
            simpa [φ, xOverlap] using
              wordRefinedLiftCompatWithPredecessorLift 𝒰 hcont (p := p)
                liftSingle hliftSingleSource hliftSingleProj hw a
                (liftShorter :=
                  liftOpen
                    (wordOfOrderedSubfamily w
                      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                        a)))
                (hambient := hambient a) xOverlap
    | some a =>
        cases j with
        | none =>
            -- Reverse the same mixed-overlap comparison when the predecessor chart comes first.
            let xOverlap :
                {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
                  x.1.path ∈ wordPatchingRefinedOpen 𝒰 hcont w ∧
                    x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                      (wordCoverContinuous 𝒰 hcont w)
                      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                        a)} :=
              ⟨x, ⟨hxj, hxi⟩⟩
            simpa [φ, xOverlap] using
              (wordRefinedLiftCompatWithPredecessorLift 𝒰 hcont (p := p)
                liftSingle hliftSingleSource hliftSingleProj hw a
                (liftShorter :=
                  liftOpen
                    (wordOfOrderedSubfamily w
                      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                        a)))
                (hambient := hambient a) xOverlap).symm
        | some b =>
            -- Two predecessor charts compare by descending to the already-compatible shorter words.
            simpa [φ] using
              predecessorWordLiftCompatOfShorterWords 𝒰 hcont (p := p)
                liftOpen hcompatOpen a b (x := x.1) hxi hxj
  let lift : C(Dw, C(I, E)) := ContinuousMap.liftCover S φ hφ hS
  refine ⟨lift, ?_, ?_⟩
  · intro x
    rcases hS x with ⟨i, hi⟩
    let xi : S i := ⟨x, mem_of_mem_nhds hi⟩
    have hglue : lift x = φ i xi := by
      -- Read the glued family through one neighborhood chart containing `x`.
      simpa [lift, xi] using
        (ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS) xi)
    cases i with
    | none =>
        -- On the refined chart, the glued family starts where the refined single-cover lift starts.
        calc
          lift x 0 = φ none xi 0 := congrArg (fun γ : C(I, E) ↦ γ 0) hglue
          _ = x.1.point := by
              simpa [φ, xi] using
                wordPatchingRefinedSingleCoverLift_source 𝒰 hcont (p := p)
                  liftSingle hliftSingleSource hliftSingleProj hw
                  (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w xi)
    | some a =>
        -- On a predecessor chart, the glued family starts where the recursive shorter-word lift starts.
        calc
          lift x 0 = φ (some a) xi 0 := congrArg (fun γ : C(I, E) ↦ γ 0) hglue
          _ = x.1.point := by
              simpa [φ, xi] using
                hsourceOpen
                  (wordOfOrderedSubfamily w
                    ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                      a))
                  (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a xi)
  · intro x
    rcases hS x with ⟨i, hi⟩
    let xi : S i := ⟨x, mem_of_mem_nhds hi⟩
    have hglue : lift x = φ i xi := by
      -- Read the glued family through one neighborhood chart containing `x`.
      simpa [lift, xi] using
        (ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS) xi)
    cases i with
    | none =>
        -- On the refined chart, the glued family projects to the original base path.
        ext t
        calc
          (p.comp (lift x)) t = (p.comp (φ none xi)) t := by
            exact congrArg (fun γ : C(I, E) ↦ (p.comp γ) t) hglue
          _ = x.1.path t := by
              simpa [φ, xi] using
                ContinuousMap.congr_fun
                  (wordPatchingRefinedSingleCoverLift_proj 𝒰 hcont (p := p)
                    liftSingle hliftSingleSource hliftSingleProj hw
                    (wordPatchingRefinedChartInclusion 𝒰 hcont (p := p) w xi)) t
    | some a =>
        -- On a predecessor chart, the glued family projects through the recursive shorter-word lift.
        ext t
        calc
          (p.comp (lift x)) t = (p.comp (φ (some a) xi)) t := by
            exact congrArg (fun γ : C(I, E) ↦ (p.comp γ) t) hglue
          _ = x.1.path t := by
              simpa [φ, xi] using
                ContinuousMap.congr_fun
                  (hprojOpen
                    (wordOfOrderedSubfamily w
                      ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                        a))
                    (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a xi)) t

/-- Helper for Theorem 7.4.3: once the fixed single-cover lift family is upgraded to a recursive
coherent system on canonical word neighborhoods, the generic local-to-global gluing theorem
produces a continuous path lifting function. -/
theorem continuousLiftOnWordPatchingOpenRecPackage
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path) :
    ∃ liftOpen :
        ∀ w : List ι,
          C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)),
        (∀ w x, liftOpen w x 0 = x.1.point) ∧
        (∀ w x, p.comp (liftOpen w x) = x.1.path) ∧
        (∀ {w w' : List ι} (hshort : w'.length ≤ w.length) (x : MappingPathSpace p)
            (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w)
            (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont w'),
            liftOpen w ⟨x, hx⟩ = liftOpen w' ⟨x, hx'⟩) ∧
        (∀ {w : List ι} (hw : 0 < w.length)
            (x : {x : MappingPathSpace p // x.path ∈ wordPatchingRefinedOpen 𝒰 hcont w}),
            liftOpen w
                ⟨x.1, by
                  simpa [wordPatchingRefinedOpen, wordPatchingOpen] using
                    NumerableOpenCover.patchingRefinedOpen_subset_patchingOpen
                      (wordCover 𝒰 w) (wordCoverContinuous 𝒰 hcont w) (wordFullSubfamily w) x.2⟩ =
              wordPatchingRefinedSingleCoverLift 𝒰 hcont (p := p)
                liftSingle hliftSingleSource hliftSingleProj hw x) ∧
        (∀ {w : List ι} (hw : 0 < w.length)
            (a : (NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessor)
            (x :
              {x : {x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w} //
                x.1.path ∈ NumerableOpenCover.patchingOpen (wordCover 𝒰 w)
                  (wordCoverContinuous 𝒰 hcont w)
                  ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                    a)}),
            liftOpen w x.1 =
              liftOpen
                (wordOfOrderedSubfamily w
                  ((NumerableOpenCover.patchingRefinement (wordFullSubfamily w)).predecessorSubfamily
                    a))
                (wordPatchingPredecessorChartToShorterWord 𝒰 hcont (p := p) w a x)) := by
  -- Route correction: the old direct proof compared the fixed families
  -- `wordPatchingOpenSingleCoverLift ... w`, which are independent `Classical.choose` witnesses.
  -- TODO: build the recursive family from `wordPatchingOpenStepLift` by strong induction on
  -- `w.length`, carrying both the refined-chart and predecessor-chart evaluation laws in the
  -- package. The remaining blocker is the descent lemma from the current refined single-cover
  -- lift to an arbitrary shorter recursive lift across `wordPatchingOpenNeighborhoodCoverSubtype`.
  sorry

/-- Helper for Theorem 7.4.3: once the fixed single-cover lift family is upgraded to a recursive
coherent system on canonical word neighborhoods, the generic local-to-global gluing theorem
produces a continuous path lifting function. -/
theorem continuousLiftOnWordPatchingOpenRec
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path) :
    ∃ liftOpen :
        ∀ w : List ι,
          C({x : MappingPathSpace p // x.path ∈ wordPatchingOpen 𝒰 hcont w}, C(I, E)),
        (∀ w x, liftOpen w x 0 = x.1.point) ∧
        (∀ w x, p.comp (liftOpen w x) = x.1.path) ∧
        (∀ {w w' : List ι} (hshort : w'.length ≤ w.length) (x : MappingPathSpace p)
            (hx : x.path ∈ wordPatchingOpen 𝒰 hcont w)
            (hx' : x.path ∈ wordPatchingOpen 𝒰 hcont w'),
            liftOpen w ⟨x, hx⟩ = liftOpen w' ⟨x, hx'⟩) := by
  obtain ⟨liftOpen, hsourceOpen, hprojOpen, hcompatOpen, _, _⟩ :=
    continuousLiftOnWordPatchingOpenRecPackage 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj
  exact ⟨liftOpen, hsourceOpen, hprojOpen, hcompatOpen⟩

/-- Helper for Theorem 7.4.3: once the fixed single-cover lift family is upgraded to a recursive
coherent system on canonical word neighborhoods, the generic local-to-global gluing theorem
produces a continuous path lifting function. -/
theorem globalContinuousPathLiftOfRefinedWordSystem
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i)) {p : C(E, B)}
    (liftSingle :
      ∀ i : ι, C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)))
    (hliftSingleSource :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        liftSingle i x 0 = x.1.point)
    (hliftSingleProj :
      ∀ i : ι, ∀ x : {x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i},
        p.comp (liftSingle i x) = x.1.path) :
    Nonempty (ContinuousPathLiftingFunction p) := by
  classical
  obtain ⟨liftOpen, hsourceOpen, hprojOpen, hcompatOpen⟩ :=
    continuousLiftOnWordPatchingOpenRec 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj
  let hasWordOfLength : MappingPathSpace p → ℕ → Prop := fun x m ↦
    ∃ w : List ι, w.length = m ∧ x.path ∈ wordPatchingOpen 𝒰 hcont w
  have hwordExists : ∀ x : MappingPathSpace p, ∃ m : ℕ, hasWordOfLength x m := by
    intro x
    rcases existsWord_mem_wordPatchingOpen 𝒰 hcont x.path with ⟨w, hw⟩
    exact ⟨w.length, w, rfl, hw⟩
  let wordMinLength : MappingPathSpace p → ℕ := fun x ↦ Nat.find (hwordExists x)
  let wordMinWitness : ∀ x : MappingPathSpace p, List ι := fun x ↦
    Classical.choose (Nat.find_spec (hwordExists x))
  have hwordMinLength :
      ∀ x : MappingPathSpace p, (wordMinWitness x).length = wordMinLength x := by
    intro x
    exact (Classical.choose_spec (Nat.find_spec (hwordExists x))).1
  have hwordMinMem :
      ∀ x : MappingPathSpace p, x.path ∈ wordPatchingOpen 𝒰 hcont (wordMinWitness x) := by
    intro x
    exact (Classical.choose_spec (Nat.find_spec (hwordExists x))).2
  let S : MappingPathSpace p → Set (MappingPathSpace p) := fun x ↦
    {y : MappingPathSpace p | y.path ∈ wordPatchingOpen 𝒰 hcont (wordMinWitness x)}
  let lift : ∀ x : MappingPathSpace p, C(S x, C(I, E)) := fun x ↦
    liftOpen (wordMinWitness x)
  have hcover : ∀ x : MappingPathSpace p, ∃ y : MappingPathSpace p, S y ∈ nhds x := by
    intro x
    refine ⟨x, ?_⟩
    -- Pull the chosen minimal basic word neighborhood back along the path projection.
    simpa [S] using
      mem_nhds_pulledBackWordPatchingOpen (𝒰 := 𝒰) (hcont := hcont) (p := p)
        (w := wordMinWitness x) (x := x) (hwordMinMem x)
  have hcompat :
      ∀ x y (z : MappingPathSpace p) (hx : z ∈ S x) (hy : z ∈ S y),
        lift x ⟨z, hx⟩ = lift y ⟨z, hy⟩ := by
    intro x y z hx hy
    -- Compare the two chosen minimal words by length, then apply the recursive overlap
    -- compatibility theorem in the longer-to-shorter direction.
    rcases Nat.le_total (wordMinLength x) (wordMinLength y) with hxy | hyx
    · have hxy' : (wordMinWitness x).length ≤ (wordMinWitness y).length := by
        simpa [hwordMinLength x, hwordMinLength y] using hxy
      exact
        (hcompatOpen (w := wordMinWitness y) (w' := wordMinWitness x) hxy' z hy hx).symm
    · have hyx' : (wordMinWitness y).length ≤ (wordMinWitness x).length := by
        simpa [hwordMinLength x, hwordMinLength y] using hyx
      exact hcompatOpen (w := wordMinWitness x) (w' := wordMinWitness y) hyx' z hx hy
  have hsource :
      ∀ x (z : S x), lift x z 0 = z.1.point := by
    intro x z
    exact hsourceOpen (wordMinWitness x) z
  have hproj :
      ∀ x (z : S x), p.comp (lift x z) = z.1.path := by
    intro x z
    exact hprojOpen (wordMinWitness x) z
  -- Once the recursive word-open system is available, the generic gluing theorem finishes.
  exact
    nonempty_continuousPathLiftingFunction_of_localLiftCover S lift hcompat hcover hsource hproj

/-- Helper for Theorem 7.4.3: the numerable patching argument assembles the local path lifting
functions for the restricted fibrations into a global lifting function that is continuous in the
mapping-path-space variable. -/
theorem nonempty_continuousPathLiftingFunction_of_forall_restrictPreimage_isFibration
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (hsum : ∀ b, ∑' i, (𝒰 i b : ℝ) = 1) (p : C(E, B))
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) :
    Nonempty (ContinuousPathLiftingFunction p) := by
  classical
  -- The partition-of-unity hypothesis remains part of the theorem interface even though the
  -- current extracted globalization helper does not consume it yet.
  let _ := hsum
  -- Route correction: the final `liftCover` assembly is now packaged in
  -- `nonempty_continuousPathLiftingFunction_of_localLiftCover`. The remaining missing data is a
  -- concrete neighbourhood cover of `MappingPathSpace p` by canonical full-word refined patching
  -- opens, together with the compatible local lifts on those neighborhoods.
  have hliftSingle :
      ∀ i : ι, ∃ lift : C({x : MappingPathSpace p // ∀ t : I, x.path t ∈ 𝒰.cover i}, C(I, E)),
        (∀ x, lift x 0 = x.1.point) ∧ (∀ x, p.comp (lift x) = x.1.path) := by
    intro i
    -- Choose the local single-cover lift data once so every refined word chart reuses it.
    exact continuousLiftWithinSingleCover 𝒰 hcont hlocal i
  choose liftSingle hliftSingleSource hliftSingleProj using hliftSingle
  -- Route correction: delegate the remaining work to the recursive word-neighborhood globalization
  -- helper, so this theorem now only packages the local single-cover lifts once.
  exact
    globalContinuousPathLiftOfRefinedWordSystem 𝒰 hcont (p := p)
      liftSingle hliftSingleSource hliftSingleProj

/-- Theorem 7.4.3: if `𝒰` is a numerable open cover of `B` whose numerating functions are
continuous and form a partition of unity, then `p : C(E, B)` is a fibration if and only if every
restricted map `p⁻¹(𝒰.cover i) → 𝒰.cover i` is a fibration. -/
theorem isFibration_iff_forall_restrictPreimage_isFibration
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (hsum : ∀ b, ∑' i, (𝒰 i b : ℝ) = 1) (p : C(E, B)) :
    IsFibration.{v, w, max v w} p ↔
      ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)) := by
  constructor
  · intro hp i
    -- The forward implication is restriction stability for fibrations.
    exact isFibration_restrictPreimage_of_isFibration hp (𝒰.cover i)
  · intro hlocal
    -- Reduce the reverse implication to surjectivity plus a global continuous path lifting
    -- function, and isolate the remaining work in the numerable patching helper above.
    have hsurj : Function.Surjective p :=
      surjective_of_forall_restrictPreimage_isFibration 𝒰 p hlocal
    have hpath : Nonempty (ContinuousPathLiftingFunction p) :=
      nonempty_continuousPathLiftingFunction_of_forall_restrictPreimage_isFibration
        𝒰 hcont hsum p hlocal
    exact (IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction.{v, w} p).2
      ⟨hsurj, hpath⟩

/-- If the restrictions of `p` to the members of a numerable open cover are fibrations, then `p`
itself is a fibration. -/
theorem isFibration_of_forall_restrictPreimage_isFibration
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (hsum : ∀ b, ∑' i, (𝒰 i b : ℝ) = 1) (p : C(E, B))
    (hlocal : ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i))) :
    IsFibration.{v, w, max v w} p :=
  (isFibration_iff_forall_restrictPreimage_isFibration 𝒰 hcont hsum p).2 hlocal

namespace IsFibration

/-- A fibration restricts to a fibration over each member of a numerable open cover whose
numerating functions are continuous and sum to `1`. -/
theorem forall_restrictPreimage_of_numerableOpenCover {p : C(E, B)}
    (hp : IsFibration.{v, w, max v w} p)
    (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (hsum : ∀ b, ∑' i, (𝒰 i b : ℝ) = 1) :
    ∀ i : ι, IsFibration.{v, w, max v w} (p.restrictPreimage (𝒰.cover i)) :=
  (isFibration_iff_forall_restrictPreimage_isFibration 𝒰 hcont hsum p).1 hp

end IsFibration
