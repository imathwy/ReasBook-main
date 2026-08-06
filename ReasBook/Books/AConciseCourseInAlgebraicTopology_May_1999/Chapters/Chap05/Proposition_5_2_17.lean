import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_19
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9

open scoped Topology

universe u v w s

namespace CompactlyGenerated

-- Proposition 5.2.17 uses the chapter-wide kification owner `Kified` from Definition 5.2.8.
-- The compactly generated product object is therefore `Kified (X × Y)`, not a second local
-- carrier wrapper with its own topology and instances.

/-- Helper for Proposition 5.2.17: a compact Hausdorff probe into `Y` is automatically continuous
for the compactly generated replacement topology on `Y`, in any target universe. -/
theorem continuousToCompactlyGeneratedOfCompactProbe
    {Y : Type v} [TopologicalSpace Y] (S : CompHaus.{u}) (g : C(S, Y)) :
    @Continuous S Y inferInstance (TopologicalSpace.compactlyGenerated.{u, v} Y) g := by
  let i : (T : CompHaus.{u}) × C(T, Y) := ⟨S, g⟩
  let e : S → Σ j : (T : CompHaus.{u}) × C(T, Y), j.1 := fun s ↦ ⟨i, s⟩
  have he : Continuous e := continuous_sigmaMk.comp continuous_id
  have hEq :
      g =
        (fun x : Σ j : (T : CompHaus.{u}) × C(T, Y), j.1 ↦ x.1.2 x.2) ∘ e := by
    funext s
    rfl
  -- Rewriting through the universal compact-Hausdorff generator exposes the coinduced topology.
  rw [continuous_iff_coinduced_le, hEq, TopologicalSpace.compactlyGenerated, ← coinduced_compose]
  exact coinduced_mono he.coinduced_le

/-- Helper for Proposition 5.2.17: a continuous map from a compact Hausdorff source into a weakly
Hausdorff space is already continuous for the codomain's same-universe compactly generated
topology. -/
theorem continuousToCompactlyGeneratedOfContinuousWeaklyHausdorff
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {Y : Type v} [TopologicalSpace Y] [WeaklyHausdorffSpace.{v, v} Y]
    {f : S → Y} (hf : Continuous f) :
    Continuous[‹TopologicalSpace S›, TopologicalSpace.compactlyGenerated.{v, v} Y] f := by
  let fRange : S → Set.range f := fun s ↦ ⟨f s, ⟨s, rfl⟩⟩
  have hfRange : Continuous fRange :=
    hf.subtype_mk fun s ↦ ⟨s, rfl⟩
  let _ : CompactSpace (Set.range f) :=
    isCompact_iff_compactSpace.mp (isCompact_range hf)
  let _ : WeaklyHausdorffSpace (Set.range f) := Subtype.weaklyHausdorffSpace
  let _ : T2Space (Set.range f) :=
    CompactSpace.toT2Space_of_weaklyHausdorffSpace (Set.range f)
  have hValCG :
      Continuous[ inferInstance, TopologicalSpace.compactlyGenerated.{v, v} Y]
        (Subtype.val : Set.range f → Y) := by
    -- The compact range subtype is a compact Hausdorff probe in the codomain universe.
    simpa using
      (continuousToCompactlyGeneratedOfCompactProbe (Y := Y) (S := CompHaus.of (Set.range f))
        ⟨Subtype.val, continuous_subtype_val⟩)
  have hComp :
      Continuous[‹TopologicalSpace S›, TopologicalSpace.compactlyGenerated.{v, v} Y]
        ((Subtype.val : Set.range f → Y) ∘ fRange) := by
    -- Composing the range factorization with the range inclusion recovers the original map.
    exact
      @Continuous.comp S (Set.range f) Y ‹TopologicalSpace S› inferInstance
        (TopologicalSpace.compactlyGenerated.{v, v} Y) fRange (Subtype.val : Set.range f → Y)
        hValCG hfRange
  simpa [fRange, Function.comp] using hComp

/-- Helper for Proposition 5.2.17: a continuous map from a compact Hausdorff source into a weakly
Hausdorff space remains continuous after viewing the codomain as `Kified Y`. -/
theorem continuousToKifiedOfContinuousOfCompHaus
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {Y : Type v} [TopologicalSpace Y] [WeaklyHausdorffSpace.{v, v} Y]
    {f : S → Y} (hf : Continuous f) :
    Continuous (fun s : S ↦ (Kified.mk (f s) : Kified Y)) := by
  have hToCompactlyGenerated :
      Continuous[‹TopologicalSpace S›, TopologicalSpace.compactlyGenerated.{v, v} Y] f :=
    continuousToCompactlyGeneratedOfContinuousWeaklyHausdorff hf
  have hCompositeToCompactlyGenerated :
      @Continuous S Y ‹TopologicalSpace S› (TopologicalSpace.compactlyGenerated.{v, v} Y)
        (Kified.of ∘ fun s : S ↦ (Kified.mk (f s) : Kified Y)) := by
    -- Forgetting the target k-topology leaves the original compact-range comparison.
    simpa [Function.comp] using hToCompactlyGenerated
  -- Continuity into the induced `Kified` topology is checked after forgetting back to `Y`.
  simpa [Function.comp, kifiedTopologicalSpace] using
    (continuous_induced_rng.2 hCompositeToCompactlyGenerated :
      Continuous (fun s : S ↦ (Kified.mk (f s) : Kified Y)))

/-- Helper for Proposition 5.2.17: a continuous map from a `U`-compactly generated source into a
weak Hausdorff target is continuous into the default k-ification of that target. -/
theorem continuousToKifiedOfContinuousOfUCompactlyGenerated
    {S : Type s} [TopologicalSpace S] [UCompactlyGeneratedSpace.{s} S]
    {Y : Type v} [TopologicalSpace Y] [WeaklyHausdorffSpace.{v, v} Y]
    {f : S → Y} (hf : Continuous f) :
    Continuous (fun s : S ↦ (Kified.mk (f s) : Kified Y)) := by
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro T g
  -- Route correction: the only bridge needed here is the compact-Hausdorff probe theorem above.
  simpa [Function.comp] using
    (continuousToKifiedOfContinuousOfCompHaus (Y := Y) (f := f ∘ g)
      (hf := hf.comp g.continuous))

/-- Helper for Proposition 5.2.17: a continuous family of ordinary continuous maps from a
`U`-compactly generated source induces a continuous family in the kified mapping space. -/
theorem continuousToMapSpaceOfContinuous
    {S : Type s} [TopologicalSpace S] [UCompactlyGeneratedSpace.{s} S]
    {A : Type u} [TopologicalSpace A]
    {B : Type v} [TopologicalSpace B] [WeaklyHausdorffSpace.{max u v, max u v} C(A, B)]
    {f : S → C(A, B)} (hf : Continuous f) :
    Continuous (fun s : S ↦ (MapSpace.ofContinuousMap (f s) : B ^ A)) := by
  -- This is exactly the kification bridge applied to the compact-open mapping space.
  simpa [MapSpace, MapSpace.ofContinuousMap] using
    (continuousToKifiedOfContinuousOfUCompactlyGenerated
      (Y := C(A, B)) hf)

/-- Helper for Proposition 5.2.17: evaluating a compact-Hausdorff family of continuous maps along
another compact-Hausdorff probe is continuous. -/
theorem continuousEvalAlongOfCompHaus
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {A : Type u} [TopologicalSpace A] [WeaklyHausdorffSpace.{u, u} A]
    {B : Type v} [TopologicalSpace B]
    (F : C(S, C(A, B))) (a : C(S, A)) :
    Continuous (fun s : S ↦ F s (a s)) := by
  let _ : CompactSpace (Set.range a) :=
    isCompact_iff_compactSpace.mp (isCompact_range a.continuous)
  let _ : T2Space (Set.range a) :=
    range_t2Space_of_weaklyHausdorffSpace (g := a) a.continuous
  let aLift : C(S, Set.range a) :=
    ⟨fun s ↦ ⟨a s, ⟨s, rfl⟩⟩, a.continuous.subtype_mk fun s ↦ ⟨s, rfl⟩⟩
  let restrictFamily : C(S, C(Set.range a, B)) :=
    ⟨fun s ↦ (F s).comp ⟨Subtype.val, continuous_subtype_val⟩,
      (ContinuousMap.continuous_precomp ⟨Subtype.val, continuous_subtype_val⟩).comp F.continuous⟩
  have hUncurry :
      Continuous (Function.uncurry fun s (y : Set.range a) ↦ F s y.1) := by
    -- After restricting the evaluation variable to the compact range, ordinary uncurry applies.
    simpa [restrictFamily, Function.uncurry] using
      (ContinuousMap.continuous_uncurry_of_continuous restrictFamily)
  have hPair : Continuous (fun s : S ↦ (s, aLift s)) :=
    continuous_id.prodMk aLift.continuous
  -- Evaluating on the lifted probe is the desired composite.
  simpa [Function.comp, aLift] using hUncurry.comp hPair

/-- Helper for Proposition 5.2.17: weak Hausdorffness lifts from same-universe probes to larger
probe universes. -/
theorem weaklyHausdorffSpaceLift
    (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    WeaklyHausdorffSpace.{u, max u v} X := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  let _ : CompactSpace (Set.range g) :=
    isCompact_iff_compactSpace.mp (isCompact_range hg)
  let _ : T2Space (Set.range g) :=
    range_t2Space_of_weaklyHausdorffSpace (g := g) hg
  have hClosedRangeSubtype : IsClosed (Set.range (Subtype.val : Set.range g → X)) := by
    -- Re-test the compact range inclusion in the smaller probe universe where weak Hausdorffness
    -- is already available.
    exact (inferInstance : WeaklyHausdorffSpace.{u, u} X).isClosed_range _ continuous_subtype_val
  have hRangeEq : Set.range (Subtype.val : Set.range g → X) = Set.range g := by
    -- Forgetting the range subtype recovers the original image exactly.
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · rintro hx
      rcases hx with ⟨k, rfl⟩
      exact ⟨⟨g k, ⟨k, rfl⟩⟩, rfl⟩
  simpa [hRangeEq] using hClosedRangeSubtype

/-- Helper for Proposition 5.2.17: compact generation lifts from same-universe probes to larger
probe universes by reindexing compact tests along `ULift`. -/
theorem uCompactlyGeneratedSpaceLift
    (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{max u v} X := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
  refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  let g : ULift.{v} S → X := f ∘ ULift.down
  have hg : Continuous g := hf.comp continuous_uliftDown
  -- The larger-universe test map on `ULift S` reduces the original preimage after pulling back
  -- along `ULift.up`.
  simpa [g, Set.preimage_comp, Function.comp] using
    (hs (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- Helper for Proposition 5.2.17: compactly generated weak Hausdorff spaces admit the same
probe-universe lift by combining the weak-Hausdorff and compact-generation bridges. -/
theorem compactlyGeneratedWeakHausdorffSpaceLift
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    CompactlyGeneratedWeakHausdorffSpace.{u, max u v} X := by
  -- Package the two universe-lifted structures into the standard Chapter 5 owner.
  exact
    @CompactlyGeneratedWeakHausdorffSpace.mk.{u, max u v} X ‹TopologicalSpace X›
      (weaklyHausdorffSpaceLift (X := X)) (uCompactlyGeneratedSpaceLift (X := X))

/-- The kified ordinary product `Kified (X × Y)` is compactly generated weak Hausdorff when `X`
and `Y` are. -/
instance instCompactlyGeneratedWeakHausdorffSpaceKifiedProd
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y] :
    CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} (Kified (X × Y)) := by
  let _ : WeaklyHausdorffSpace.{u, max u v} X := weaklyHausdorffSpaceLift (X := X)
  let _ : WeaklyHausdorffSpace.{v, max u v} Y := by
    simpa [max_comm] using
      (weaklyHausdorffSpaceLift (X := Y) :
        WeaklyHausdorffSpace.{v, max v u} Y)
  let _ : WeaklyHausdorffSpace.{max u v, max u v} (X × Y) :=
    weaklyHausdorffSpaceProd_direct (X := X) (Y := Y)
  -- Once the ordinary product is weak Hausdorff in the ambient probe universe, the standard
  -- `Kified` owner supplies the compactly generated weak Hausdorff structure.
  exact instCompactlyGeneratedWeakHausdorffSpaceKified (X := X × Y)

/-- For fixed `f : Z ^ Kified (X × Y)` and `x : X`, the slice
`y ↦ f (Kified.mk (x, y))` is continuous. -/
theorem mapSpaceCurry_apply_continuous
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (f : Z ^ Kified (X × Y)) (x : X) :
    Continuous fun y : Y ↦ f (Kified.mk (x, y)) := by
  let _ : WeaklyHausdorffSpace.{u, max u v} X := weaklyHausdorffSpaceLift (X := X)
  let _ : WeaklyHausdorffSpace.{v, max u v} Y := by
    simpa [max_comm] using
      (weaklyHausdorffSpaceLift (X := Y) :
        WeaklyHausdorffSpace.{v, max v u} Y)
  let _ : WeaklyHausdorffSpace.{max u v, max u v} (X × Y) :=
    weaklyHausdorffSpaceProd_direct (X := X) (Y := Y)
  have hPair : Continuous (fun y : Y ↦ ((x, y) : X × Y)) :=
    continuous_const.prodMk continuous_id
  have hKified : Continuous (fun y : Y ↦ (Kified.mk ((x, y) : X × Y) : Kified (X × Y))) := by
    -- Repackage the ordinary slice map into the default kified product.
    simpa using
      (continuousToKifiedOfContinuousOfUCompactlyGenerated (Y := X × Y)
        (f := fun y : Y ↦ ((x, y) : X × Y)) hPair)
  -- Compose the fixed slice into the kified product with the given continuous map `f`.
  simpa [Function.comp] using (f : C(Kified (X × Y), Z)).continuous.comp hKified

/-- Helper for Proposition 5.2.17: along a compact probe `k : C(S, X)`, the map
`(s, y) ↦ Kified.mk (k s, y)` into the kified product is continuous. -/
theorem continuousProbePairToKifiedProd
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (k : C(S, X)) :
    Continuous (fun p : S × Y ↦ (Kified.mk (k p.1, p.2) : Kified (X × Y))) := by
  let _ : WeaklyHausdorffSpace.{u, max u v} X := weaklyHausdorffSpaceLift (X := X)
  let _ : WeaklyHausdorffSpace.{v, max u v} Y := by
    simpa [max_comm] using
      (weaklyHausdorffSpaceLift (X := Y) :
        WeaklyHausdorffSpace.{v, max v u} Y)
  let _ : WeaklyHausdorffSpace.{max u v, max u v} (X × Y) :=
    weaklyHausdorffSpaceProd_direct (X := X) (Y := Y)
  let _ : LocallyCompactSpace S := inferInstance
  let _ : UCompactlyGeneratedSpace.{max s v} (S × Y) :=
    ordinaryProductTopology_uCompactlyGenerated (X := S) (Y := Y)
  have hPair : Continuous (fun p : S × Y ↦ ((k p.1, p.2) : X × Y)) :=
    (k.continuous.comp continuous_fst).prodMk continuous_snd
  -- The compact probe source `S × Y` is already compactly generated, so the pair map upgrades
  -- directly to the default kified product.
  simpa using
    (continuousToKifiedOfContinuousOfUCompactlyGenerated (Y := X × Y)
      (f := fun p : S × Y ↦ ((k p.1, p.2) : X × Y)) hPair)

/-- For fixed `f : Z ^ Kified (X × Y)`, the curried map
`x ↦ (y ↦ f (Kified.mk (x, y)))` is continuous. -/
theorem mapSpaceCurry_continuousMap
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (f : Z ^ Kified (X × Y)) :
    Continuous fun x : X ↦
      MapSpace.ofContinuousMap
        ⟨fun y ↦ f (Kified.mk (x, y)), mapSpaceCurry_apply_continuous X Y Z f x⟩ := by
  have hContinuousMapWH : WeaklyHausdorffSpace.{max v w, max v w} C(Y, Z) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y :=
      compactlyGeneratedWeakHausdorffSpaceLift (X := Y)
    let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} Z := by
      simpa [max_comm] using
        (compactlyGeneratedWeakHausdorffSpaceLift (X := Z) :
          CompactlyGeneratedWeakHausdorffSpace.{w, max w v} Z)
    exact continuousMapWeaklyHausdorffSpace (X := Y) (Y := Z)
  let _ : WeaklyHausdorffSpace.{max v w, max v w} C(Y, Z) := hContinuousMapWH
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro S k
  let F : S → C(Y, Z) := fun s ↦
    ⟨fun y ↦ f (Kified.mk (k s, y)),
      mapSpaceCurry_apply_continuous X Y Z f (k s)⟩
  have hUncurry : Continuous (Function.uncurry fun s y ↦ F s y) := by
    -- Along a compact probe into `X`, the ordinary uncurry is the composite of `f` with the
    -- continuous probe-pair map into the kified product.
    simpa [F, Function.uncurry] using
      ((f : C(Kified (X × Y), Z)).continuous.comp
        (continuousProbePairToKifiedProd (X := X) (Y := Y) (k := k)))
  have hF : Continuous F :=
    ContinuousMap.continuous_of_continuous_uncurry F hUncurry
  -- Transport the ordinary compact-open family into the kified mapping-space owner once.
  simpa [F, Function.comp] using
    (continuousToMapSpaceOfContinuous (A := Y) (B := Z) (f := F) hF)

/-- Curry a map on the kified product into a map valued in the compactly generated mapping
space. -/
def mapSpaceCurry
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    (Z ^ Kified (X × Y)) → ((Z ^ Y) ^ X) :=
  fun f ↦
    MapSpace.ofContinuousMap
      ⟨fun x ↦
          MapSpace.ofContinuousMap
            ⟨fun y ↦ f (Kified.mk (x, y)), mapSpaceCurry_apply_continuous X Y Z f x⟩,
        mapSpaceCurry_continuousMap X Y Z f⟩

/-- Evaluating `mapSpaceCurry` gives the usual curried map. -/
@[simp] theorem mapSpaceCurry_apply
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (f : Z ^ Kified (X × Y)) (x : X) (y : Y) :
    mapSpaceCurry X Y Z f x y = f (Kified.mk (x, y)) :=
  rfl

/-- For fixed `g : (Z ^ Y) ^ X`, the associated uncurried map
`p ↦ g p.of.1 p.of.2` is continuous. -/
theorem mapSpaceUncurry_continuousMap
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (g : (Z ^ Y) ^ X) :
    Continuous fun p : Kified (X × Y) ↦ g p.of.1 p.of.2 := by
  -- Route correction: the naive ordinary-compact-open uncurry theorem reintroduces a
  -- `LocallyCompactSpace Y` side condition, so the remaining proof must instead use compact probes
  -- and the kified evaluation interface.
  let _ : WeaklyHausdorffSpace.{v, v} Y := inferInstance
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro S k
  let a : C(S, X) :=
    ⟨fun s ↦ (k s).of.1,
      ((continuousKifiedForget (X × Y)).comp k.continuous).fst⟩
  let b : C(S, Y) :=
    ⟨fun s ↦ (k s).of.2,
      ((continuousKifiedForget (X × Y)).comp k.continuous).snd⟩
  let F : C(S, C(Y, Z)) :=
    ⟨fun s ↦ (g (a s) : C(Y, Z)),
      (continuousKifiedForget (C(Y, Z))).comp <|
        (show Continuous fun s : S ↦ g (a s) from (g : C(X, Z ^ Y)).continuous.comp a.continuous)⟩
  -- Evaluate the compact-Hausdorff family of ordinary maps along the second coordinate probe.
  simpa [Function.comp, a, b, F] using continuousEvalAlongOfCompHaus F b

/-- Uncurry a map valued in a compactly generated mapping space. -/
def mapSpaceUncurry
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    ((Z ^ Y) ^ X) → (Z ^ Kified (X × Y)) :=
  fun g ↦
    MapSpace.ofContinuousMap
      ⟨fun p : Kified (X × Y) ↦ g p.of.1 p.of.2,
        mapSpaceUncurry_continuousMap X Y Z g⟩

/-- Evaluating `mapSpaceUncurry` gives the usual uncurried map. -/
@[simp] theorem mapSpaceUncurry_apply
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (g : (Z ^ Y) ^ X) (p : Kified (X × Y)) :
    mapSpaceUncurry X Y Z g p = g p.of.1 p.of.2 :=
  rfl

/-- Helper for Proposition 5.2.17: evaluating a compact probe into a kified mapping space is
jointly continuous on the ordinary product with the argument space. -/
theorem continuousProbeEval
    (A : Type u) [TopologicalSpace A] [CompactlyGeneratedWeakHausdorffSpace.{u, u} A]
    (B : Type v) [TopologicalSpace B] [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (k : C(S, B ^ A)) :
    Continuous fun q : S × A ↦ k q.1 q.2 := by
  let _ : WeaklyHausdorffSpace.{s, max s u} S := weaklyHausdorffSpaceLift (X := S)
  let _ : WeaklyHausdorffSpace.{u, max s u} A := by
    simpa [max_comm] using
      (weaklyHausdorffSpaceLift (X := A) :
        WeaklyHausdorffSpace.{u, max u s} A)
  let _ : WeaklyHausdorffSpace.{max s u, max s u} (S × A) :=
    weaklyHausdorffSpaceProd_direct (X := S) (Y := A)
  let _ : LocallyCompactSpace S := inferInstance
  let _ : UCompactlyGeneratedSpace.{max s u} (S × A) :=
    ordinaryProductTopology_uCompactlyGenerated (X := S) (Y := A)
  have hKifiedProd : Continuous fun q : S × A ↦ (Kified.mk q : Kified (S × A)) := by
    -- The ordinary product of the compact probe with `A` is compactly generated, so the identity
    -- map upgrades to the default kified product.
    simpa using
      (continuousToKifiedOfContinuousOfUCompactlyGenerated (Y := S × A)
        (f := fun q : S × A ↦ q) continuous_id)
  let evalMap : (B ^ A) ^ S :=
    MapSpace.ofContinuousMap k
  have hEval :
      Continuous fun q : Kified (S × A) ↦ evalMap q.of.1 q.of.2 := by
    -- The universal uncurry map on `evalMap` is the required evaluation on the kified product.
    simpa [evalMap] using
      (mapSpaceUncurry_continuousMap (X := S) (Y := A) (Z := B) (g := evalMap))
  -- Compose the universal kified evaluation with the comparison from the ordinary product.
  simpa [evalMap] using hEval.comp hKifiedProd

/-- Helper for Proposition 5.2.17: a compact probe into `Z ^ Kified (X × Y)` yields a continuous
ordinary family `S × X → C(Y, Z)`. -/
theorem continuousProbeCurryFamily
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (k : C(S, Z ^ Kified (X × Y))) :
    Continuous fun p : S × X ↦
      MapSpace.ofContinuousMap
        ⟨fun y ↦ k p.1 (Kified.mk (p.2, y)),
          mapSpaceCurry_apply_continuous X Y Z (k p.1) p.2⟩ := by
  have hContinuousMapWH : WeaklyHausdorffSpace.{max v w, max v w} C(Y, Z) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y :=
      compactlyGeneratedWeakHausdorffSpaceLift (X := Y)
    let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} Z := by
      simpa [max_comm] using
        (compactlyGeneratedWeakHausdorffSpaceLift (X := Z) :
          CompactlyGeneratedWeakHausdorffSpace.{w, max w v} Z)
    exact continuousMapWeaklyHausdorffSpace (X := Y) (Y := Z)
  let _ : WeaklyHausdorffSpace.{max v w, max v w} C(Y, Z) := hContinuousMapWH
  let _ : LocallyCompactSpace S := inferInstance
  let _ : UCompactlyGeneratedSpace.{max s u} (S × X) :=
    ordinaryProductTopology_uCompactlyGenerated (X := S) (Y := X)
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro T t
  let a : C(T, S) := ⟨fun q ↦ (t q).1, t.continuous.fst⟩
  let b : C(T, X) := ⟨fun q ↦ (t q).2, t.continuous.snd⟩
  let F : T → C(Y, Z) := fun q ↦
    ⟨fun y ↦ k (a q) (Kified.mk (b q, y)),
      mapSpaceCurry_apply_continuous X Y Z (k (a q)) (b q)⟩
  have hPair :
      Continuous fun q : T × Y ↦ (q.1, (Kified.mk (b q.1, q.2) : Kified (X × Y))) :=
    continuous_fst.prodMk (continuousProbePairToKifiedProd (X := X) (Y := Y) (k := b))
  have hUncurry : Continuous (Function.uncurry fun q y ↦ F q y) := by
    -- Evaluate the compact probe `k.comp a` after inserting the probe-varying `X`-coordinate.
    simpa [F, Function.uncurry, a, b] using
      (continuousProbeEval (A := Kified (X × Y)) (B := Z) (k := k.comp a)).comp hPair
  have hF : Continuous F :=
    ContinuousMap.continuous_of_continuous_uncurry F hUncurry
  -- Repackage the ordinary compact-open family into the kified mapping-space owner.
  simpa [F, Function.comp, a, b] using
    (continuousToMapSpaceOfContinuous (A := Y) (B := Z) (f := F) hF)

/-- Helper for Proposition 5.2.17: a compact probe into `(Z ^ Y) ^ X` has jointly continuous
uncurried evaluation on `S × Kified (X × Y)`. -/
theorem continuousProbeUncurryEval
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (k : C(S, (Z ^ Y) ^ X)) :
    Continuous fun q : S × Kified (X × Y) ↦ k q.1 q.2.of.1 q.2.of.2 := by
  -- Route correction: prove joint continuity on `S × Kified (X × Y)` first, then curry later.
  let _ : LocallyCompactSpace S := inferInstance
  let _ : UCompactlyGeneratedSpace.{max s (max u v)} (S × Kified (X × Y)) :=
    ordinaryProductTopology_uCompactlyGenerated (X := S) (Y := Kified (X × Y))
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro T t
  let a : C(T, S) := ⟨fun q ↦ (t q).1, t.continuous.fst⟩
  let d : C(T, Kified (X × Y)) := ⟨fun q ↦ (t q).2, t.continuous.snd⟩
  let e : C(T, X × Y) :=
    ⟨fun q ↦ (d q).of, (continuousKifiedForget (X × Y)).comp d.continuous⟩
  let b : C(T, X) := ⟨fun q ↦ (e q).1, e.continuous.fst⟩
  let c : C(T, Y) := ⟨fun q ↦ (e q).2, e.continuous.snd⟩
  let G : C(T, C(X, Z ^ Y)) :=
    ⟨fun q ↦ (k (a q) : C(X, Z ^ Y)),
      (continuousKifiedForget (C(X, Z ^ Y))).comp <|
        (show Continuous fun q : T ↦ k (a q) from
          (k : C(S, (Z ^ Y) ^ X)).continuous.comp a.continuous)⟩
  have hFirstEval : Continuous fun q : T ↦ k (a q) (b q) := by
    -- First evaluate the `X`-variable along the probe extracted from the kified product.
    simpa [G, a, b] using continuousEvalAlongOfCompHaus G b
  let F : C(T, C(Y, Z)) :=
    ⟨fun q ↦ (k (a q) (b q) : C(Y, Z)),
      (continuousKifiedForget (C(Y, Z))).comp hFirstEval⟩
  -- Then evaluate the resulting `Y`-family along the second extracted probe.
  simpa [F, a, d, e, b, c] using continuousEvalAlongOfCompHaus F c

/-- Helper for Proposition 5.2.17: a compact probe into `(Z ^ Y) ^ X` yields a continuous
ordinary family `S → C(Kified (X × Y), Z)`. -/
theorem continuousProbeUncurryFamily
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (k : C(S, (Z ^ Y) ^ X)) :
    Continuous fun s : S ↦
      (⟨fun p : Kified (X × Y) ↦ k s p.of.1 p.of.2,
        mapSpaceUncurry_continuousMap X Y Z (k s)⟩ : C(Kified (X × Y), Z)) := by
  let F : S → C(Kified (X × Y), Z) := fun s ↦
    ⟨fun p : Kified (X × Y) ↦ k s p.of.1 p.of.2,
      mapSpaceUncurry_continuousMap X Y Z (k s)⟩
  have hUncurry : Continuous (Function.uncurry fun s p ↦ F s p) := by
    -- The structural joint-evaluation lemma is exactly the uncurried continuity needed here.
    simpa [F, Function.uncurry] using
      (continuousProbeUncurryEval (X := X) (Y := Y) (Z := Z) (k := k))
  exact ContinuousMap.continuous_of_continuous_uncurry F hUncurry

/-- The curry and uncurry operators are inverse on `Z^(X × Y)`. -/
theorem mapSpaceCurry_leftInverse
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    Function.LeftInverse (mapSpaceUncurry X Y Z) (mapSpaceCurry X Y Z) := by
  intro f
  -- Compare the two maps pointwise after forgetting the mapping-space kification.
  ext p
  simp [mapSpaceCurry_apply, mapSpaceUncurry_apply]

/-- The curry and uncurry operators are inverse on `(Z^Y)^X`. -/
theorem mapSpaceCurry_rightInverse
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    Function.RightInverse (mapSpaceUncurry X Y Z) (mapSpaceCurry X Y Z) := by
  intro g
  -- Compare the outer and inner mapping spaces pointwise.
  ext x y
  simp [mapSpaceCurry_apply, mapSpaceUncurry_apply]

/-- The curry operator is continuous for the compactly generated mapping-space topologies. -/
theorem mapSpaceCurry_continuous
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    Continuous (mapSpaceCurry X Y Z) := by
  let _ :
      CompactlyGeneratedWeakHausdorffSpace.{max (max u v) w, max (max u v) w}
        (Z ^ Kified (X × Y)) := by
    let _ :
        CompactlyGeneratedWeakHausdorffSpace.{max u v, max (max u v) w} (Kified (X × Y)) :=
      (show CompactlyGeneratedWeakHausdorffSpace.{max u v, max (max u v) w} (Kified (X × Y)) from
        compactlyGeneratedWeakHausdorffSpaceLift (X := Kified (X × Y)))
    let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max (max u v) w} Z := by
      simpa [max_assoc, max_comm, max_left_comm] using
        (show CompactlyGeneratedWeakHausdorffSpace.{w, max w (max u v)} Z from
          compactlyGeneratedWeakHausdorffSpaceLift (X := Z))
    exact mapSpaceCompactlyGeneratedWeakHausdorffSpace (X := Kified (X × Y)) (Y := Z)
  have hInnerMapSpace :
      CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w} (Z ^ Y) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y :=
      (show CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y from
        compactlyGeneratedWeakHausdorffSpaceLift (X := Y))
    let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} Z := by
      simpa [max_comm] using
        (show CompactlyGeneratedWeakHausdorffSpace.{w, max w v} Z from
          compactlyGeneratedWeakHausdorffSpaceLift (X := Z))
    exact mapSpaceCompactlyGeneratedWeakHausdorffSpace (X := Y) (Y := Z)
  have hContinuousMapWH :
      WeaklyHausdorffSpace.{max u (max v w), max u (max v w)} C(X, Z ^ Y) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{u, max u (max v w)} X :=
      @CompactlyGeneratedWeakHausdorffSpace.mk.{u, max u (max v w)} X ‹TopologicalSpace X›
        (show WeaklyHausdorffSpace.{u, max u (max v w)} X from
          (weaklyHausdorffSpaceLift.{u, max v w} (X := X) :
            WeaklyHausdorffSpace.{u, max u (max v w)} X))
        (show UCompactlyGeneratedSpace.{max u (max v w)} X from
          (uCompactlyGeneratedSpaceLift.{u, max v w} (X := X) :
            UCompactlyGeneratedSpace.{max u (max v w)} X))
    let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y) := by
      let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w} (Z ^ Y) := hInnerMapSpace
      exact
        @CompactlyGeneratedWeakHausdorffSpace.mk.{max v w, max u (max v w)} (Z ^ Y)
          inferInstance
          (show WeaklyHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y) from
            (weaklyHausdorffSpaceLift.{max v w, u} (X := Z ^ Y) :
              WeaklyHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y)))
          (show UCompactlyGeneratedSpace.{max u (max v w)} (Z ^ Y) from
            (uCompactlyGeneratedSpaceLift.{max v w, u} (X := Z ^ Y) :
              UCompactlyGeneratedSpace.{max u (max v w)} (Z ^ Y)))
    exact continuousMapWeaklyHausdorffSpace (X := X) (Y := Z ^ Y)
  let _ : WeaklyHausdorffSpace.{max u (max v w), max u (max v w)} C(X, Z ^ Y) :=
    hContinuousMapWH
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro S k
  let F : S → C(X, Z ^ Y) := fun s ↦
    ⟨fun x ↦
        MapSpace.ofContinuousMap
          ⟨fun y ↦ k s (Kified.mk (x, y)),
            mapSpaceCurry_apply_continuous X Y Z (k s) x⟩,
      mapSpaceCurry_continuousMap X Y Z (k s)⟩
  have hUncurry : Continuous (Function.uncurry fun s x ↦ F s x) := by
    -- Compact-probe continuity of the curried family is the remaining operator-level bridge.
    simpa [F, Function.uncurry] using
      (continuousProbeCurryFamily (X := X) (Y := Y) (Z := Z) (k := k))
  have hF : Continuous F :=
    ContinuousMap.continuous_of_continuous_uncurry F hUncurry
  -- Repackage the ordinary `C(X, Z ^ Y)`-family into the outer kified mapping space.
  simpa [mapSpaceCurry, F, Function.comp] using
    (continuousToMapSpaceOfContinuous (A := X) (B := Z ^ Y) (f := F) hF)

/-- The uncurry operator is continuous for the compactly generated mapping-space topologies. -/
theorem mapSpaceUncurry_continuous
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    Continuous (mapSpaceUncurry X Y Z) := by
  let _ :
      CompactlyGeneratedWeakHausdorffSpace.{max (max u v) w, max (max u v) w} ((Z ^ Y) ^ X) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{u, max u (max v w)} X :=
      @CompactlyGeneratedWeakHausdorffSpace.mk.{u, max u (max v w)} X ‹TopologicalSpace X›
        (show WeaklyHausdorffSpace.{u, max u (max v w)} X from
          (weaklyHausdorffSpaceLift.{u, max v w} (X := X) :
            WeaklyHausdorffSpace.{u, max u (max v w)} X))
        (show UCompactlyGeneratedSpace.{max u (max v w)} X from
          (uCompactlyGeneratedSpaceLift.{u, max v w} (X := X) :
            UCompactlyGeneratedSpace.{max u (max v w)} X))
    let _ :
        CompactlyGeneratedWeakHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y) := by
      let _ : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y :=
        (show CompactlyGeneratedWeakHausdorffSpace.{v, max v w} Y from
          compactlyGeneratedWeakHausdorffSpaceLift (X := Y))
      let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} Z := by
        simpa [max_comm] using
          (show CompactlyGeneratedWeakHausdorffSpace.{w, max w v} Z from
            compactlyGeneratedWeakHausdorffSpaceLift (X := Z))
      let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w} (Z ^ Y) :=
        mapSpaceCompactlyGeneratedWeakHausdorffSpace (X := Y) (Y := Z)
      exact
        @CompactlyGeneratedWeakHausdorffSpace.mk.{max v w, max u (max v w)} (Z ^ Y)
          inferInstance
          (show WeaklyHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y) from
            (weaklyHausdorffSpaceLift.{max v w, u} (X := Z ^ Y) :
              WeaklyHausdorffSpace.{max v w, max u (max v w)} (Z ^ Y)))
          (show UCompactlyGeneratedSpace.{max u (max v w)} (Z ^ Y) from
            (uCompactlyGeneratedSpaceLift.{max v w, u} (X := Z ^ Y) :
              UCompactlyGeneratedSpace.{max u (max v w)} (Z ^ Y)))
    simpa [max_assoc] using
      (mapSpaceCompactlyGeneratedWeakHausdorffSpace (X := X) (Y := Z ^ Y) :
        CompactlyGeneratedWeakHausdorffSpace.{max u (max v w), max u (max v w)} ((Z ^ Y) ^ X))
  have hContinuousMapWH :
      WeaklyHausdorffSpace.{max (max u v) w, max (max u v) w} C(Kified (X × Y), Z) := by
    let _ :
        CompactlyGeneratedWeakHausdorffSpace.{max u v, max (max u v) w} (Kified (X × Y)) := by
      let _ :
          CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} (Kified (X × Y)) :=
        instCompactlyGeneratedWeakHausdorffSpaceKifiedProd (X := X) (Y := Y)
      exact
        (show
            CompactlyGeneratedWeakHausdorffSpace.{max u v, max (max u v) w} (Kified (X × Y)) from
          compactlyGeneratedWeakHausdorffSpaceLift (X := Kified (X × Y)))
    let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max (max u v) w} Z := by
      simpa [max_assoc, max_comm, max_left_comm] using
        (show CompactlyGeneratedWeakHausdorffSpace.{w, max w (max u v)} Z from
          compactlyGeneratedWeakHausdorffSpaceLift (X := Z))
    exact continuousMapWeaklyHausdorffSpace (X := Kified (X × Y)) (Y := Z)
  let _ :
      WeaklyHausdorffSpace.{max (max u v) w, max (max u v) w} C(Kified (X × Y), Z) :=
    hContinuousMapWH
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro S k
  let F : S → C(Kified (X × Y), Z) := fun s ↦
    ⟨fun p : Kified (X × Y) ↦ k s p.of.1 p.of.2,
      mapSpaceUncurry_continuousMap X Y Z (k s)⟩
  have hF : Continuous F :=
    continuousProbeUncurryFamily (X := X) (Y := Y) (Z := Z) (k := k)
  -- Repackage the ordinary `C(Kified (X × Y), Z)`-family into the kified mapping space.
  simpa [mapSpaceUncurry, F, Function.comp] using
    (continuousToMapSpaceOfContinuous (A := Kified (X × Y)) (B := Z) (f := F) hF)

/-- Proposition 5.2.17. For spaces `X`, `Y`, and `Z` in `U`, the canonical bijection
`Z^(X × Y) ≃ (Z^Y)^X` is a homeomorphism. -/
def mapSpaceCurryHomeomorph
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    (Z ^ Kified (X × Y)) ≃ₜ ((Z ^ Y) ^ X) :=
  { toEquiv :=
      { toFun := mapSpaceCurry X Y Z
        invFun := mapSpaceUncurry X Y Z
        left_inv := mapSpaceCurry_leftInverse X Y Z
        right_inv := mapSpaceCurry_rightInverse X Y Z }
    continuous_toFun := mapSpaceCurry_continuous X Y Z
    continuous_invFun := mapSpaceUncurry_continuous X Y Z }

/-- The forward map of `mapSpaceCurryHomeomorph` is `mapSpaceCurry`. -/
@[simp] theorem mapSpaceCurryHomeomorph_def
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    (mapSpaceCurryHomeomorph X Y Z :
      (Z ^ Kified (X × Y)) → ((Z ^ Y) ^ X)) =
        mapSpaceCurry X Y Z :=
  rfl

/-- The inverse map of `mapSpaceCurryHomeomorph` is `mapSpaceUncurry`. -/
@[simp] theorem mapSpaceCurryHomeomorph_symm_def
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z] :
    ((mapSpaceCurryHomeomorph X Y Z).symm :
      ((Z ^ Y) ^ X) → (Z ^ Kified (X × Y))) =
        mapSpaceUncurry X Y Z :=
  rfl

/-- Evaluating `mapSpaceCurryHomeomorph` gives the usual curried map. -/
@[simp] theorem mapSpaceCurryHomeomorph_apply
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (f : Z ^ Kified (X × Y)) (x : X) (y : Y) :
    mapSpaceCurryHomeomorph X Y Z f x y = f (Kified.mk (x, y)) :=
  rfl

/-- Evaluating the inverse of `mapSpaceCurryHomeomorph` gives the usual uncurried map. -/
@[simp] theorem mapSpaceCurryHomeomorph_symm_apply
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (Y : Type v) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
    (Z : Type w) [TopologicalSpace Z] [CompactlyGeneratedWeakHausdorffSpace.{w, w} Z]
    (g : (Z ^ Y) ^ X) (p : Kified (X × Y)) :
    (mapSpaceCurryHomeomorph X Y Z).symm g p = g p.of.1 p.of.2 :=
  rfl

end CompactlyGenerated
