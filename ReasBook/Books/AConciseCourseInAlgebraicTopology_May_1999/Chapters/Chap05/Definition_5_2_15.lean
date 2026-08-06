import Mathlib.Topology.CompactOpen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_8

open scoped Topology

universe u v w

namespace CompactlyGenerated

/-- Helper for Definition 5.2.15: a weak Hausdorff space is `T1`. -/
private lemma weaklyHausdorff_t1
    (Z : Type v) [TopologicalSpace Z] [WeaklyHausdorffSpace.{v, w} Z] :
    T1Space Z := by
  -- Reduce `T1` to closed singletons coming from compact Hausdorff one-point sources.
  refine ⟨fun z ↦ ?_⟩
  simpa [Set.range_const] using
    (show IsClosed (Set.range (fun _ : ULift.{w} Unit ↦ z)) from
      (show Continuous (fun _ : ULift.{w} Unit ↦ z) from continuous_const).isClosed_range)

/-- Helper for Definition 5.2.15: a surjective closed map from a compact Hausdorff space to a
`T1` space has Hausdorff codomain. -/
private lemma t2Space_of_surjective_closedMap_from_compactHausdorff
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type v} [TopologicalSpace Z] [T1Space Z]
    {f : K → Z} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) : T2Space Z := by
  rw [t2Space_iff]
  intro x y hxy
  let A : Set K := f ⁻¹' {x}
  let B : Set K := f ⁻¹' {y}
  have hAClosed : IsClosed A := by
    simpa [A] using isClosed_singleton.preimage hf_cont
  have hBClosed : IsClosed B := by
    simpa [B] using isClosed_singleton.preimage hf_cont
  have hACompact : IsCompact A := isCompact_univ.of_isClosed_subset hAClosed (by simp [A])
  have hBCompact : IsCompact B := isCompact_univ.of_isClosed_subset hBClosed (by simp [B])
  have hABDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro a haA haB
    have hx : f a = x := by simpa [A] using haA
    have hy : f a = y := by simpa [B] using haB
    exact hxy (hx.symm.trans hy)
  -- Separate the two fibers upstairs, then saturate those neighborhoods downstairs.
  obtain ⟨U, V, hUOpen, hVOpen, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hACompact hBCompact hBClosed hABDisjoint
  have hUImageClosed : IsClosed (f '' Uᶜ) := hf_closed _ hUOpen.isClosed_compl
  have hVImageClosed : IsClosed (f '' Vᶜ) := hf_closed _ hVOpen.isClosed_compl
  refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ, hUImageClosed.isOpen_compl, hVImageClosed.isOpen_compl, ?_, ?_,
    ?_⟩
  · -- The whole fiber over `x` lies in `U`, so `x` avoids the image of `Uᶜ`.
    rw [Set.mem_compl_iff]
    intro hxU
    rcases hxU with ⟨a, haU, hfa⟩
    exact haU <| hAU <| by simp [A, hfa]
  · -- The whole fiber over `y` lies in `V`, so `y` avoids the image of `Vᶜ`.
    rw [Set.mem_compl_iff]
    intro hyV
    rcases hyV with ⟨a, haV, hfa⟩
    exact haV <| hBV <| by simp [B, hfa]
  · -- A common image point would have a preimage in both saturated neighborhoods.
    rw [Set.disjoint_left]
    intro z hzU hzV
    rcases hf_surj z with ⟨a, rfl⟩
    have haU : a ∈ U := by
      by_contra haU
      exact hzU ⟨a, haU, rfl⟩
    have haV : a ∈ V := by
      by_contra haV
      exact hzV ⟨a, haV, rfl⟩
    exact hUV.le_bot ⟨haU, haV⟩

/-- Helper for Definition 5.2.15: a continuous map from a compact Hausdorff space into a weak
Hausdorff space is a closed map. -/
private lemma isClosedMap_of_continuous_to_weaklyHausdorff
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type v} [TopologicalSpace Z] [WeaklyHausdorffSpace.{v, u} Z]
    {f : K → Z} (hf : Continuous f) : IsClosedMap f := by
  intro s hs
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  -- Closed subsets of a compact Hausdorff source are compact Hausdorff, so their images are
  -- closed by weak Hausdorffness.
  let hZ : WeaklyHausdorffSpace Z := inferInstance
  simpa [Set.range_restrict] using
    (show IsClosed (Set.range (s.restrict f)) from
      hZ.isClosed_range (s.restrict f) (show Continuous (s.restrict f) from
        hf.comp continuous_subtype_val))

/-- Helper for Definition 5.2.15: the union of two compact Hausdorff images in a weak Hausdorff
space is Hausdorff. -/
private lemma unionRange_t2Space_of_compactHausdorffMaps
    {Z : Type v} [TopologicalSpace Z] [WeaklyHausdorffSpace.{v, u} Z]
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → Z} (hf : Continuous f) (hg : Continuous g) :
    T2Space ((Set.range f ∪ Set.range g : Set Z)) := by
  let h : K ⊕ K → (Set.range f ∪ Set.range g : Set Z) :=
    Sum.elim
      (fun x ↦ ⟨f x, Or.inl ⟨x, rfl⟩⟩)
      (fun x ↦ ⟨g x, Or.inr ⟨x, rfl⟩⟩)
  -- The copair map is continuous because each branch lands in the union subtype.
  have hh_cont : Continuous h := by
    rw [continuous_sumElim]
    constructor
    · exact Continuous.subtype_mk hf fun x ↦ Or.inl ⟨x, rfl⟩
    · exact Continuous.subtype_mk hg fun x ↦ Or.inr ⟨x, rfl⟩
  let _ : WeaklyHausdorffSpace ((Set.range f ∪ Set.range g : Set Z)) := inferInstance
  let _ : T1Space ((Set.range f ∪ Set.range g : Set Z)) :=
    weaklyHausdorff_t1 ((Set.range f ∪ Set.range g : Set Z))
  -- Every point in the union comes from one of the two summands.
  have hh_surj : Function.Surjective h := by
    intro z
    rcases z.2 with hz | hz
    · rcases hz with ⟨x, hx⟩
      refine ⟨Sum.inl x, Subtype.ext ?_⟩
      simpa [h] using hx
    · rcases hz with ⟨x, hx⟩
      refine ⟨Sum.inr x, Subtype.ext ?_⟩
      simpa [h] using hx
  -- The weak Hausdorff target turns the copair map into a closed surjection from a compact
  -- Hausdorff source.
  have hh_closed : IsClosedMap h := isClosedMap_of_continuous_to_weaklyHausdorff hh_cont
  exact t2Space_of_surjective_closedMap_from_compactHausdorff hh_cont hh_surj hh_closed

/-- Helper for Definition 5.2.15: equalizers of maps from a compact Hausdorff space into a weak
Hausdorff space are closed. -/
private lemma isClosed_eqLocus_of_continuous_compHaus
    {Z : Type v} [TopologicalSpace Z] [WeaklyHausdorffSpace.{v, u} Z]
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → Z} (hf : Continuous f) (hg : Continuous g) :
    IsClosed {k : K | f k = g k} := by
  let U : Set Z := Set.range f ∪ Set.range g
  let f' : K → U := fun k ↦ ⟨f k, Or.inl ⟨k, rfl⟩⟩
  let g' : K → U := fun k ↦ ⟨g k, Or.inr ⟨k, rfl⟩⟩
  have hf' : Continuous f' := Continuous.subtype_mk hf fun k ↦ Or.inl ⟨k, rfl⟩
  have hg' : Continuous g' := Continuous.subtype_mk hg fun k ↦ Or.inr ⟨k, rfl⟩
  let _ : T2Space U := unionRange_t2Space_of_compactHausdorffMaps hf hg
  -- Move the equalizer into the Hausdorff union-range subtype and apply `isClosed_eq`.
  simpa [U, f', g'] using isClosed_eq hf' hg'

-- Semantic recall via `lean_leansearch`: `ContinuousMap.compactOpen` provides the compact-open
-- topology on `C(X, Y)`, while Chapter 5 already packages `k`-ification by `Kified`. The source
-- mapping space is therefore the source-facing bridge `Kified C(X, Y)`, not a second wrapper
-- owner parallel to `Kified`.

/-- Source-facing mapping-space model for Definition 5.2.15: `Y ^ X` is implemented as the
`k`-ification of the compact-open mapping space `C(X, Y)`. -/
abbrev MapSpace (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    Type (max u v) :=
  Kified C(X, Y)

/- The source-facing exponential notation `Y ^ X` for the compactly generated mapping space from
`X` to `Y`. -/
scoped[Topology] notation:80 Y:81 " ^ " X:80 => _root_.CompactlyGenerated.MapSpace X Y

namespace MapSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

instance : Coe (Y ^ X) C(X, Y) := ⟨Kified.of⟩

instance : CoeTC C(X, Y) (Y ^ X) := ⟨Kified.mk⟩

instance : CoeFun (Y ^ X) (fun _ ↦ X → Y) := ⟨fun f ↦ (f : C(X, Y))⟩

/-- The underlying continuous map of a point of `Y ^ X`. -/
abbrev toContinuousMap (f : Y ^ X) : C(X, Y) :=
  f

/-- A continuous map determines a point of the compactly generated mapping space. -/
abbrev ofContinuousMap (f : C(X, Y)) : Y ^ X :=
  f

@[simp] theorem toContinuousMap_ofContinuousMap (f : C(X, Y)) :
    toContinuousMap (ofContinuousMap f) = f :=
  rfl

@[simp] theorem ofContinuousMap_toContinuousMap (f : Y ^ X) :
    ofContinuousMap (toContinuousMap f) = f := by
  cases f
  rfl

@[simp] theorem ofContinuousMap_apply (f : C(X, Y)) (x : X) :
    ofContinuousMap f x = f x :=
  rfl

/-- Equality of elements of `Y ^ X` can be checked after forgetting the `k`-ification. -/
theorem ext_toContinuousMap (f g : Y ^ X)
    (h : toContinuousMap f = toContinuousMap g) : f = g := by
  cases f
  cases g
  exact congrArg Kified.mk h

@[ext] theorem ext (f g : Y ^ X) (h : ∀ x, f x = g x) : f = g := by
  apply ext_toContinuousMap
  exact ContinuousMap.ext h

/-- Forgetting the `k`-ification identifies `Y ^ X` with `C(X, Y)` on the underlying carrier. -/
def equivContinuousMap : (Y ^ X) ≃ C(X, Y) where
  toFun := toContinuousMap
  invFun := ofContinuousMap
  left_inv := ofContinuousMap_toContinuousMap
  right_inv := fun _ ↦ rfl

@[simp] theorem equivContinuousMap_apply (f : Y ^ X) :
    equivContinuousMap f = toContinuousMap f :=
  rfl

@[simp] theorem equivContinuousMap_symm_apply (f : C(X, Y)) :
    equivContinuousMap.symm f = ofContinuousMap f :=
  rfl

end MapSpace

section

variable (X : Type u) (Y : Type v) [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- Helper for Definition 5.2.15: the image of a compact Hausdorff map into a weak Hausdorff
space is Hausdorff as a subspace. -/
lemma range_t2Space_of_compactHausdorffMap
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type v} [TopologicalSpace Z] [WeaklyHausdorffSpace.{v, w} Z]
    {g : K → Z} (hg : Continuous g) : T2Space (Set.range g) := by
  classical
  let _ : T1Space Z := weaklyHausdorff_t1 Z
  rw [t2Space_iff]
  intro p q hpq
  let A : Set K := {k : K | g k = p.1}
  let B : Set K := {k : K | g k = q.1}
  have hAClosed : IsClosed A := by
    simpa [A] using
      (isClosed_eqLocus_of_continuous_compHaus
        (Z := Z) (f := g) (g := fun _ : K ↦ p.1) hg continuous_const)
  have hBClosed : IsClosed B := by
    simpa [B] using
      (isClosed_eqLocus_of_continuous_compHaus
        (Z := Z) (f := g) (g := fun _ : K ↦ q.1) hg continuous_const)
  have hACompact : IsCompact A := isCompact_univ.of_isClosed_subset hAClosed (by simp [A])
  have hBCompact : IsCompact B := isCompact_univ.of_isClosed_subset hBClosed (by simp [B])
  have hABDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro k hkA hkB
    have hp' : g k = p.1 := by simpa [A] using hkA
    have hq' : g k = q.1 := by simpa [B] using hkB
    exact hpq (Subtype.ext (hp'.symm.trans hq'))
  -- Separate the fibers of `p` and `q` upstairs in the compact Hausdorff source.
  obtain ⟨U, V, hUOpen, hVOpen, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hACompact hBCompact hBClosed hABDisjoint
  let _ : CompactSpace ↥(Uᶜ) :=
    isCompact_iff_compactSpace.mp <|
      isCompact_univ.of_isClosed_subset hUOpen.isClosed_compl (by simp)
  let _ : CompactSpace ↥(Vᶜ) :=
    isCompact_iff_compactSpace.mp <|
      isCompact_univ.of_isClosed_subset hVOpen.isClosed_compl (by simp)
  have hRangeUClosed : IsClosed (g '' Uᶜ) := by
    simpa [Set.range_restrict] using
      (Continuous.isClosed_range
        (show Continuous (Uᶜ.restrict g) from hg.comp continuous_subtype_val))
  have hRangeVClosed : IsClosed (g '' Vᶜ) := by
    simpa [Set.range_restrict] using
      (Continuous.isClosed_range
        (show Continuous (Vᶜ.restrict g) from hg.comp continuous_subtype_val))
  refine ⟨((↑) ⁻¹' (g '' Uᶜ)ᶜ), ((↑) ⁻¹' (g '' Vᶜ)ᶜ),
    hRangeUClosed.isOpen_compl.preimage continuous_subtype_val,
    hRangeVClosed.isOpen_compl.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · -- Every preimage of `p` lies in `U`, so `p` avoids the image of `Uᶜ`.
    change p.1 ∈ (g '' Uᶜ)ᶜ
    rw [Set.mem_compl_iff]
    rintro ⟨k, hkU, hk⟩
    have hkA : k ∈ A := by simpa [A] using hk
    exact hkU (hAU hkA)
  · -- The same argument puts `q` outside the image of `Vᶜ`.
    change q.1 ∈ (g '' Vᶜ)ᶜ
    rw [Set.mem_compl_iff]
    rintro ⟨k, hkV, hk⟩
    have hkB : k ∈ B := by simpa [B] using hk
    exact hkV (hBV hkB)
  · -- A common range point would come from a source point lying in both disjoint neighborhoods.
    rw [Set.disjoint_left]
    intro r hrU hrV
    change r.1 ∈ (g '' Uᶜ)ᶜ at hrU
    change r.1 ∈ (g '' Vᶜ)ᶜ at hrV
    rcases r.2 with ⟨k, hk⟩
    have hrU' : g k ∈ (g '' Uᶜ)ᶜ := by simpa [hk] using hrU
    have hrV' : g k ∈ (g '' Vᶜ)ᶜ := by simpa [hk] using hrV
    have hkU : k ∈ U := by
      by_contra hkU
      exact hrU' ⟨k, hkU, rfl⟩
    have hkV : k ∈ V := by
      by_contra hkV
      exact hrV' ⟨k, hkV, rfl⟩
    exact hUV.le_bot ⟨hkU, hkV⟩

/-- Helper for Definition 5.2.15: finite evaluation images of compact probes into `C(X, Y)` are
closed in the finite product codomain. -/
lemma finiteEvaluationRangeClosed
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [WeaklyHausdorffSpace.{v, w} Y]
    {g : K → C(X, Y)} (hg : Continuous g) (s : Finset X) :
    IsClosed (Set.range (fun k : K ↦ fun x : s ↦ g k x)) := by
  let admissible : Set (s → Y) :=
    {u | ∀ x : s, u x ∈ Set.range (fun k : K ↦ g k x)}
  have hAdmissibleEq :
      admissible = ⋂ x : s, {u : s → Y | u x ∈ Set.range (fun k : K ↦ g k x)} := by
    ext u
    simp [admissible]
  have hAdmissibleClosed : IsClosed admissible := by
    rw [hAdmissibleEq]
    refine isClosed_iInter fun x ↦ ?_
    -- Each coordinate condition cuts out a closed set because the coordinate image is closed.
    have hCoordClosed : IsClosed (Set.range (fun k : K ↦ g k x)) :=
      Continuous.isClosed_range ((continuous_eval_const (x : X)).comp hg)
    change IsClosed ((fun u : s → Y ↦ u x) ⁻¹' Set.range (fun k : K ↦ g k x))
    exact hCoordClosed.preimage (continuous_apply x)
  let admissibleSubtype := ↥admissible
  let admissibleEquiv :
      admissibleSubtype ≃ₜ ((x : s) → Set.range (fun k : K ↦ g k x)) :=
    { toEquiv :=
        { toFun := fun u x ↦ ⟨u.1 x, u.2 x⟩
          invFun := fun u ↦ ⟨fun x ↦ (u x).1, fun x ↦ (u x).2⟩
          left_inv := by
            intro u
            cases u
            rfl
          right_inv := by
            intro u
            rfl }
      continuous_toFun := by
        -- Coordinatewise continuity is inherited from the subtype inclusion.
        refine continuous_pi fun x ↦ ?_
        exact Continuous.subtype_mk
          ((continuous_apply x).comp continuous_subtype_val)
          (fun u ↦ by
            have hu : ∀ y : s, (u : s → Y) y ∈ Set.range (fun k : K ↦ g k y) := by
              simpa [admissible] using (show (u : s → Y) ∈ admissible from u.2)
            exact hu x)
      continuous_invFun := by
        -- Reassembling the tuple only forgets subtype wrappers coordinatewise.
        exact Continuous.subtype_mk
          (continuous_pi fun x ↦ continuous_subtype_val.comp (continuous_apply x))
          (fun u ↦ fun x ↦ (u x).2) }
  let _ : ∀ x : s, T2Space (Set.range (fun k : K ↦ g k x)) := fun x ↦
    range_t2Space_of_compactHausdorffMap
      (g := fun k : K ↦ g k x) ((continuous_eval_const (x : X)).comp hg)
  let _ : T2Space admissibleSubtype := admissibleEquiv.symm.t2Space
  let admissibleLift : K → admissibleSubtype := fun k ↦
    ⟨fun x : s ↦ g k x, fun x ↦ ⟨k, rfl⟩⟩
  have hAdmissibleLift : Continuous admissibleLift := by
    -- The lift is continuous because each coordinate is an evaluation map.
    have hUnderlying : Continuous (fun k : K ↦ fun x : s ↦ g k x) := by
      exact continuous_pi fun x : s ↦ (continuous_eval_const (x : X)).comp hg
    have hMembership : ∀ k : K, (fun x : s ↦ g k x) ∈ admissible := by
      intro k
      simp [admissible]
    simpa [admissibleLift] using Continuous.subtype_mk hUnderlying hMembership
  have hClosedRangeLift : IsClosed (Set.range admissibleLift) :=
    Continuous.isClosed_range hAdmissibleLift
  have hClosedImage :
      IsClosed (((↑) : admissibleSubtype → s → Y) '' Set.range admissibleLift) :=
    hAdmissibleClosed.isClosedMap_subtype_val _ hClosedRangeLift
  have hImageEq :
      ((↑) : admissibleSubtype → s → Y) '' Set.range admissibleLift =
        Set.range (fun k : K ↦ fun x : s ↦ g k x) := by
    ext u
    constructor
    · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨admissibleLift k, ⟨k, rfl⟩, rfl⟩
  rw [hImageEq] at hClosedImage
  exact hClosedImage

/-- Helper for Definition 5.2.15: a compact probe lands in the range of `g` exactly when every
finite evaluation tuple does. -/
lemma mem_range_iff_allFiniteEvaluations
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [WeaklyHausdorffSpace.{v, w} Y]
    {g : K → C(X, Y)} (hg : Continuous g) (f : C(X, Y)) :
    f ∈ Set.range g ↔
      ∀ s : Finset X, (fun x : s ↦ f x) ∈ Set.range (fun k : K ↦ fun x : s ↦ g k x) := by
  classical
  constructor
  · rintro ⟨k, rfl⟩ s
    exact ⟨k, rfl⟩
  · intro hs
    let A : X → Set K := fun x ↦ {k : K | g k x = f x}
    have hAClosed : ∀ x : X, IsClosed (A x) := by
      intro x
      simpa [A] using
        (isClosed_eqLocus_of_continuous_compHaus
          (Z := Y) (f := fun k : K ↦ g k x) (g := fun _ : K ↦ f x)
          ((continuous_eval_const x).comp hg) continuous_const)
    have hFiniteIntersections : ∀ s : Finset X, (⋂ x ∈ s, A x).Nonempty := by
      intro s
      rcases hs s with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only [Set.mem_iInter]
      intro x hx
      have hxEq : g k x = f x := by
        simpa using congrFun hk ⟨x, hx⟩
      simpa [A] using hxEq
    rcases CompactSpace.iInter_nonempty hAClosed hFiniteIntersections with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- Membership in every equalizer gives pointwise equality of continuous maps.
    have hkAll : ∀ x : X, k ∈ A x := by
      simpa [Set.mem_iInter] using hk
    ext x
    simpa [A] using hkAll x

/-- Helper for Definition 5.2.15: the range of a compact probe into `C(X, Y)` is the intersection
of the closed finite-evaluation preimages. -/
lemma continuousMapRange_eq_iInter_finiteEvaluationPreimage
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [WeaklyHausdorffSpace.{v, w} Y]
    {g : K → C(X, Y)} (hg : Continuous g) :
    Set.range g =
      ⋂ s : Finset X,
        {f : C(X, Y) | (fun x : s ↦ f x) ∈ Set.range (fun k : K ↦ fun x : s ↦ g k x)} := by
  ext f
  -- Normalize range membership to the finite-evaluation criterion.
  simp [mem_range_iff_allFiniteEvaluations (X := X) (Y := Y) hg f]

omit tX tY in
/-- Definition 5.2.15. If `Y` is weak Hausdorff, then the compact-open mapping space `C(X, Y)`
is weak Hausdorff. The proof only uses finite evaluations in the codomain, so no compact-generation
hypothesis on `X` or `Y` is needed here. -/
instance continuousMapWeaklyHausdorffSpace
    [WeaklyHausdorffSpace.{v, max u v} Y] :
    WeaklyHausdorffSpace.{max u v, max u v} C(X, Y) := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  -- Test closedness of the probe range via all finite evaluation maps.
  have hRangeDescription :=
    continuousMapRange_eq_iInter_finiteEvaluationPreimage (X := X) (Y := Y) (g := g) hg
  rw [hRangeDescription]
  refine isClosed_iInter fun s ↦ ?_
  let finiteEvaluation : C(X, Y) → (s → Y) := fun f x ↦ f x
  have hFiniteEvaluation : Continuous finiteEvaluation := by
    -- The compact-open topology is generated so that point evaluations are continuous.
    exact continuous_pi fun x ↦ continuous_eval_const (x : X)
  simpa [finiteEvaluation] using
    (finiteEvaluationRangeClosed (X := X) (Y := Y) (g := g) hg s).preimage hFiniteEvaluation

omit tX tY in
/-- The `k`-ified compact-open topology on `C(X, Y)` is compactly generated weak Hausdorff when
`X` and `Y` are compactly generated weak Hausdorff spaces. -/
instance mapSpaceCompactlyGeneratedWeakHausdorffSpace
    [CompactlyGeneratedWeakHausdorffSpace.{u, max u v} X]
    [CompactlyGeneratedWeakHausdorffSpace.{v, max u v} Y] :
    CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} (Y ^ X) := by
  let _ : WeaklyHausdorffSpace.{max u v, max u v} C(X, Y) :=
    continuousMapWeaklyHausdorffSpace X Y
  simpa [MapSpace] using
    (instCompactlyGeneratedWeakHausdorffSpaceKified (X := C(X, Y)) :
      CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} (Kified C(X, Y)))

end

end CompactlyGenerated
