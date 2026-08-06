import Mathlib.Topology.CompactOpen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_16
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_19
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Construction_6_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Criterion_6_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2

open scoped Topology unitInterval

universe u v w s

variable {A : Type u} {X : Type v} {B : Type w}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]

/-- Helper for Lemma 7.2.5: the compactly generated replacement topology is itself
`UCompactlyGeneratedSpace`. -/
theorem compactlyGeneratedTopologyUCompactlyGeneratedSpace
    (Y : Type s) [TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{s} Y (TopologicalSpace.compactlyGenerated.{s} Y) := by
  -- Present the replacement topology as the standard coinduced topology on compact probes.
  let f : (Σ (i : (S : CompHaus.{s}) × C(S, Y)), i.fst) → Y := fun y ↦ y.1.2 y.2
  have hf : @Continuous ((Σ (i : (S : CompHaus.{s}) × C(S, Y)), i.fst)) Y
      instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{s, _, _}
    ((Σ (i : (S : CompHaus.{s}) × C(S, Y)), i.fst)) Y instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Lemma 7.2.5: the kified carrier `Kified Y` is compactly generated. -/
theorem kifiedCompactlyGeneratedSpace
    (Y : Type s) [TopologicalSpace Y] :
    CompactlyGeneratedSpace (Kified Y) := by
  -- Transfer compact generation across the `Kified.mk`/`Kified.of` equivalence.
  have hcgY : @UCompactlyGeneratedSpace.{s} Y (TopologicalSpace.compactlyGenerated.{s} Y) :=
    compactlyGeneratedTopologyUCompactlyGeneratedSpace Y
  let e : Kified Y ≃ Y :=
    { toFun := Kified.of
      invFun := Kified.mk
      left_inv := by
        intro y
        cases y
        rfl
      right_inv := by
        intro y
        rfl }
  have hcont : @Continuous Y (Kified Y)
      (TopologicalSpace.compactlyGenerated.{s} Y) (kifiedTopologicalSpace.{s, s} Y) Kified.mk := by
    rw [kifiedTopologicalSpace, continuous_induced_rng]
    change @Continuous Y Y (TopologicalSpace.compactlyGenerated.{s} Y)
      (TopologicalSpace.compactlyGenerated.{s} Y) (fun y : Y ↦ y)
    exact @continuous_id Y (TopologicalSpace.compactlyGenerated.{s} Y)
  have htop : kifiedTopologicalSpace.{s, s} Y =
      TopologicalSpace.coinduced Kified.mk (TopologicalSpace.compactlyGenerated.{s} Y) := by
    rw [kifiedTopologicalSpace]
    exact congrArg (fun t ↦ t (TopologicalSpace.compactlyGenerated.{s} Y))
      (Equiv.coinduced_symm e).symm
  have hcgK : @UCompactlyGeneratedSpace.{s} (Kified Y) (kifiedTopologicalSpace.{s, s} Y) :=
    @uCompactlyGeneratedSpace_of_coinduced.{s} Y (Kified Y)
      (TopologicalSpace.compactlyGenerated.{s} Y) (kifiedTopologicalSpace.{s, s} Y) hcgY Kified.mk
      hcont htop
  simpa [instTopologicalSpaceKified, kifiedTopologicalSpace] using hcgK

/-- The restriction map on compactly generated mapping spaces induced by `i`. -/
noncomputable def mapSpaceRestriction (i : C(A, X))
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] : C(B ^ X, B ^ A) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace.{u, u} A := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{v, v} X := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{w, w} B := inferInstance
  let _ : WeaklyHausdorffSpace.{u, u} A := inferInstance
  let _ : WeaklyHausdorffSpace.{v, v} X := inferInstance
  let _ : WeaklyHausdorffSpace.{w, w} B := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} A := inferInstance
  let _ : UCompactlyGeneratedSpace.{v} X := inferInstance
  let _ : UCompactlyGeneratedSpace.{w} B := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{u, max u w} A :=
    CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := A)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} B := by
    simpa [max_comm] using
      (CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := B) :
        CompactlyGeneratedWeakHausdorffSpace.{w, max w u} B)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} X :=
    CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := X)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} B := by
    let _ : WeaklyHausdorffSpace.{w, max v w} B := by
      simpa [max_comm] using
        (show WeaklyHausdorffSpace.{w, max w v} B from
          CompactlyGenerated.weaklyHausdorffSpaceLift.{w, v} (X := B))
    let _ : UCompactlyGeneratedSpace.{max v w} B := by
      simpa [max_comm] using
        (show UCompactlyGeneratedSpace.{max w v} B from
          CompactlyGenerated.uCompactlyGeneratedSpaceLift.{w, v} (X := B))
    exact
      @CompactlyGeneratedWeakHausdorffSpace.mk.{w, max v w} B inferInstance
        inferInstance inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w} (B ^ X) :=
    inferInstance
  let _ : WeaklyHausdorffSpace.{max u w, max u w} C(A, B) :=
    inferInstance
  refine
    ⟨fun f ↦ CompactlyGenerated.MapSpace.ofContinuousMap ((f : C(X, B)).comp i), ?_⟩
  -- Forget the source k-topology once, apply ordinary precomposition, then repackage the result.
  have hForget : Continuous fun f : B ^ X ↦ ((f : B ^ X) : C(X, B)) :=
    continuousKifiedForget C(X, B)
  have hPrecomp :
      Continuous fun f : B ^ X ↦ ((f : C(X, B)).comp i : C(A, B)) :=
    (ContinuousMap.continuous_precomp i).comp hForget
  simpa using
    (CompactlyGenerated.continuousToMapSpaceOfContinuous
      (A := A) (B := B) (f := fun f : B ^ X ↦ ((f : C(X, B)).comp i)) hPrecomp)

/-- Postcomposition by a continuous map induces a continuous map between compactly generated
mapping spaces. -/
noncomputable def mapSpacePostcomposition
    {K : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedWeakHausdorffSpace K]
    [CompactlyGeneratedWeakHausdorffSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace Z]
    (j : C(Y, Z)) : C(Y ^ K, Z ^ K) := by
  let _ : CompactlyGeneratedSpace (Y ^ K) := kifiedCompactlyGeneratedSpace C(K, Y)
  let hK : CompactlyGeneratedWeakHausdorffSpace.{u, max u w} K :=
    CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := K)
  let hZ : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} Z := by
    simpa [max_comm] using
      (CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := Z) :
        CompactlyGeneratedWeakHausdorffSpace.{w, max w u} Z)
  let _ : WeaklyHausdorffSpace C(K, Z) :=
    @CompactlyGenerated.continuousMapWeaklyHausdorffSpace.{u, w}
      K Z inferInstance inferInstance hZ.toWeaklyHausdorffSpace
  refine
    ⟨fun f ↦ CompactlyGenerated.MapSpace.ofContinuousMap (j.comp (f : C(K, Y))), ?_⟩
  have hPostcomp :
      Continuous fun f : Y ^ K ↦ (j.comp (f : C(K, Y)) : C(K, Z)) :=
    (ContinuousMap.continuous_postcomp j).comp (continuousKifiedForget C(K, Y))
  simpa [CompactlyGenerated.MapSpace.ofContinuousMap] using
    (CompactlyGenerated.continuousToMapSpaceOfContinuous
      (A := K) (B := Z)
      (f := fun f : Y ^ K ↦ (j.comp (f : C(K, Y)) : C(K, Z))) hPostcomp)

/-- Helper for Lemma 7.2.5: evaluating the point coordinate of the restriction mapping-path space
on `X` is jointly continuous. -/
theorem restrictionMappingPathPointUncurryContinuous
    {A : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]
    (i : C(A, X))
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    Continuous
      fun q : Kified (X × MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) ↦
        (q.of.2.point : B ^ X) q.of.1 := by
  let p : C(B ^ X, B ^ A) := mapSpaceRestriction i
  let _ : CompactlyGeneratedSpace (Kified (X × MappingPathSpace p)) :=
    kifiedCompactlyGeneratedSpace (X × MappingPathSpace p)
  -- Test continuity on compact probes into the kified product source.
  refine continuous_from_compactlyGeneratedSpace _ ?_
  intro S _ _ _ k hk
  let xProbe : C(S, X) :=
    ⟨fun s ↦ (k s).of.1,
      ((continuousKifiedForget (X × MappingPathSpace p)).comp hk).fst⟩
  let mappingPathProbe : C(S, MappingPathSpace p) :=
    ⟨fun s ↦ (k s).of.2,
      ((continuousKifiedForget (X × MappingPathSpace p)).comp hk).snd⟩
  let pointFamily : C(S, C(X, B)) :=
    ⟨fun s ↦ ((mappingPathProbe s).point : C(X, B)),
      (continuousKifiedForget C(X, B)).comp <|
        (mappingPathSpacePointContinuous p).comp mappingPathProbe.continuous⟩
  -- The desired map is the compact-probe evaluation of the point family along the `X`-coordinate.
  simpa [p, xProbe, mappingPathProbe, pointFamily, MappingPathSpace.point] using
    (CompactlyGenerated.continuousEvalAlongOfCompHaus
      (A := X) (B := B) pointFamily xProbe)

/-- Helper for Lemma 7.2.5: evaluating the stored base path of the restriction mapping-path space
on `A × I` is jointly continuous. -/
theorem restrictionMappingPathBoundaryUncurryContinuous
    {A : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]
    (i : C(A, X))
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    Continuous
      fun q : Kified ((A × I) × MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) ↦
        ((q.of.2.path q.of.1.2 : B ^ A) q.of.1.1) := by
  let p : C(B ^ X, B ^ A) := mapSpaceRestriction i
  let _ : CompactlyGeneratedSpace (Kified ((A × I) × MappingPathSpace p)) :=
    kifiedCompactlyGeneratedSpace ((A × I) × MappingPathSpace p)
  -- Test continuity on compact probes, first evaluating the stored path at time `t`.
  refine continuous_from_compactlyGeneratedSpace _ ?_
  intro S _ _ _ k hk
  let pointProbe : C(S, A) :=
    ⟨fun s ↦ (k s).of.1.1,
      ((continuousKifiedForget ((A × I) × MappingPathSpace p)).comp hk).fst.fst⟩
  let timeProbe : C(S, I) :=
    ⟨fun s ↦ (k s).of.1.2,
      ((continuousKifiedForget ((A × I) × MappingPathSpace p)).comp hk).fst.snd⟩
  let mappingPathProbe : C(S, MappingPathSpace p) :=
    ⟨fun s ↦ (k s).of.2,
      ((continuousKifiedForget ((A × I) × MappingPathSpace p)).comp hk).snd⟩
  let pathFamily : C(S, C(I, B ^ A)) :=
    ⟨fun s ↦ (mappingPathProbe s).path,
      (mappingPathSpacePathContinuous p).comp mappingPathProbe.continuous⟩
  have hTimeSlice : Continuous fun s : S ↦ (pathFamily s (timeProbe s) : B ^ A) := by
    -- Evaluate the compact-probe family of paths at the chosen time parameter.
    simpa [pathFamily, timeProbe, MappingPathSpace.path] using
      (CompactlyGenerated.continuousEvalAlongOfCompHaus
        (A := I) (B := B ^ A) pathFamily timeProbe)
  let boundaryFamily : C(S, C(A, B)) :=
    ⟨fun s ↦ ((pathFamily s (timeProbe s) : B ^ A) : C(A, B)),
      (continuousKifiedForget C(A, B)).comp hTimeSlice⟩
  -- Evaluating that time-slice family at the `A`-coordinate gives the target formula.
  simpa [p, pointProbe, timeProbe, mappingPathProbe, pathFamily, boundaryFamily,
    MappingPathSpace.path] using
    (CompactlyGenerated.continuousEvalAlongOfCompHaus
      (A := A) (B := B) boundaryFamily pointProbe)

/-- Helper for Lemma 7.2.5: the time-`0` slice of a restriction mapping path agrees, as an
ordinary continuous map `A → B`, with restricting the stored point along `i`. -/
theorem restrictionMappingPathZero_eq_restriction {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :
    ((z.path 0 : B ^ A) : C(A, B)) = (z.point : C(X, B)).comp i := by
  -- Expand the time-`0` condition of the mapping path space using the explicit restriction-map
  -- formula, then forget the target k-topology.
  exact congrArg (fun f : B ^ A ↦ (f : C(A, B))) <| by
    simpa [mapSpaceRestriction] using z.path_zero_eq

/-- Helper for Lemma 7.2.5: evaluating the time-`0` compatibility pointwise gives the expected
restriction formula on `A`. -/
theorem restrictionMappingPathZero_apply {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) (a : A) :
    ((z.path 0 : B ^ A) a) = (z.point : B ^ X) (i a) := by
  -- Evaluate the zero-time compatibility theorem at the chosen point of `A`.
  simpa [ContinuousMap.comp_apply] using
    congrArg (fun f : C(A, B) ↦ f a) (restrictionMappingPathZero_eq_restriction (i := i) z)

namespace ContinuousMap

/-- Helper for Lemma 7.2.5: lift a same-universe map `i : A → X` by applying the same
`ULift.{s}` to source and target. -/
def sameUniverseULiftMap {A X : Type u}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    C(ULift.{s} A, ULift.{s} X) where
  toFun := fun a ↦ ULift.up (i a.down)
  continuous_toFun := continuous_uliftUp.comp <| i.continuous.comp continuous_uliftDown

/-- Helper for Lemma 7.2.5: the same-universe `ULift` model evaluates by applying `i` and then
lifting the value. -/
@[simp] theorem sameUniverseULiftMap_apply {A X : Type u}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : ULift.{s} A) :
    sameUniverseULiftMap i a = ULift.up (i a.down) :=
  rfl

/-- Helper for Lemma 7.2.5: cofibration is preserved when a same-universe map is lifted by
`ULift.{s}` on both source and target. -/
theorem isCofibration_sameUniverseULiftMap_iff {A X : Type u}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    IsCofibration.{max s u, max s u, w}
        (sameUniverseULiftMap i : C(ULift.{s} A, ULift.{s} X)) ↔
      IsCofibration.{u, u, w} i := by
  constructor
  · intro hiLift Y _ f₀ g H
    let downA : C(ULift.{s} A, A) := ⟨ULift.down, continuous_uliftDown⟩
    let downX : C(ULift.{s} X, X) := ⟨ULift.down, continuous_uliftDown⟩
    let f₀Lift : C(ULift.{s} X, Y) := f₀.comp downX
    let gLift : C(ULift.{s} A, Y) := g.comp downA
    -- Precompose the original homotopy with `ULift.down` to move into the lifted HEP problem.
    let HLift : (f₀Lift.comp (sameUniverseULiftMap i : C(ULift.{s} A, ULift.{s} X))).Homotopy gLift := by
      simpa [f₀Lift, gLift, downA, downX, sameUniverseULiftMap, ContinuousMap.comp_assoc] using
        H.compContinuousMap downA
    obtain ⟨G, F, hF⟩ := hiLift.exists_homotopy_extension f₀Lift gLift HLift
    let upX : C(X, ULift.{s} X) := ⟨ULift.up, continuous_uliftUp⟩
    let GDown : C(X, Y) := G.comp upX
    -- Restrict the lifted extension back along `ULift.up : X → ULift X`.
    let FDown : f₀.Homotopy GDown := by
      simpa [f₀Lift, GDown, upX, downX, ContinuousMap.comp_assoc] using
        F.compContinuousMap upX
    refine ⟨GDown, FDown, ?_⟩
    intro z
    rcases z with ⟨t, a⟩
    -- Evaluate the lifted compatibility on `ULift.up a` and then forget the `ULift` wrappers.
    simpa [HLift, FDown, GDown, f₀Lift, gLift, downA, upX, downX, sameUniverseULiftMap,
      ContinuousMap.comp_apply] using hF (t, ULift.up a)
  · intro hi Y _ f₀ g H
    let upX : C(X, ULift.{s} X) := ⟨ULift.up, continuous_uliftUp⟩
    let upA : C(A, ULift.{s} A) := ⟨ULift.up, continuous_uliftUp⟩
    let f₀Base : C(X, Y) := f₀.comp upX
    let gBase : C(A, Y) := g.comp upA
    -- Precompose the lifted homotopy with `ULift.up` to reduce to the original cofibration.
    let HBase : (f₀Base.comp i).Homotopy gBase := by
      simpa [f₀Base, gBase, upA, upX, sameUniverseULiftMap, ContinuousMap.comp_assoc] using
        H.compContinuousMap upA
    obtain ⟨G, F, hF⟩ := hi.exists_homotopy_extension f₀Base gBase HBase
    let downX : C(ULift.{s} X, X) := ⟨ULift.down, continuous_uliftDown⟩
    let GLift : C(ULift.{s} X, Y) := G.comp downX
    -- Extend back to the lifted source by precomposing with `ULift.down`.
    let FLift : f₀.Homotopy GLift := by
      simpa [f₀Base, GLift, upX, downX, ContinuousMap.comp_assoc] using
        F.compContinuousMap downX
    refine ⟨GLift, FLift, ?_⟩
    intro z
    rcases z with ⟨t, a⟩
    -- Evaluate the original compatibility on `a.down` and then reinsert the `ULift` wrappers.
    simpa [HBase, FLift, GLift, f₀Base, gBase, upA, upX, downX, sameUniverseULiftMap,
      ContinuousMap.comp_apply] using hF (t, a.down)

/-- Helper for Lemma 7.2.5: lift a map `i : A → X` to a common universe by applying `ULift` to
both source and target. -/
def commonUniverseULiftMap {A : Type u} {X : Type v}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    C(ULift.{v} A, ULift.{u} X) where
  toFun := fun a ↦ ULift.up (i a.down)
  continuous_toFun := continuous_uliftUp.comp <| i.continuous.comp continuous_uliftDown

/-- Helper for Lemma 7.2.5: the common-universe `ULift` model evaluates by applying `i` and then
lifting the value. -/
@[simp] theorem commonUniverseULiftMap_apply {A : Type u} {X : Type v}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : ULift.{v} A) :
    commonUniverseULiftMap i a = ULift.up (i a.down) :=
  rfl

/-- Helper for Lemma 7.2.5: cofibration is preserved when `i` is replaced by its common-universe
`ULift` model. -/
theorem isCofibration_commonUniverseULiftMap_iff {A : Type u} {X : Type v}
    [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    IsCofibration.{max u v, max u v, w} (commonUniverseULiftMap i) ↔
      IsCofibration.{u, v, w} i := by
  constructor
  · intro hiLift Y _ f₀ g H
    let downA : C(ULift.{v} A, A) := ⟨ULift.down, continuous_uliftDown⟩
    let downX : C(ULift.{u} X, X) := ⟨ULift.down, continuous_uliftDown⟩
    let f₀Lift : C(ULift.{u} X, Y) := f₀.comp downX
    let gLift : C(ULift.{v} A, Y) := g.comp downA
    -- Precompose the original homotopy with `ULift.down : ULift A → A` to move into the lifted
    -- HEP problem.
    let HLift :
        (f₀Lift.comp (commonUniverseULiftMap i)).Homotopy gLift := by
      simpa [f₀Lift, gLift, downA, downX, commonUniverseULiftMap, ContinuousMap.comp_assoc] using
        H.compContinuousMap downA
    obtain ⟨G, F, hF⟩ := hiLift.exists_homotopy_extension f₀Lift gLift HLift
    let upX : C(X, ULift.{u} X) := ⟨ULift.up, continuous_uliftUp⟩
    let GDown : C(X, Y) := G.comp upX
    -- Restrict the lifted extension back along `ULift.up : X → ULift X`.
    let FDown : f₀.Homotopy GDown := by
      simpa [f₀Lift, GDown, upX, downX, ContinuousMap.comp_assoc] using
        F.compContinuousMap upX
    refine ⟨GDown, FDown, ?_⟩
    intro z
    rcases z with ⟨t, a⟩
    -- Evaluate the lifted compatibility on `ULift.up a` and then forget the `ULift` wrappers.
    simpa [HLift, FDown, GDown, f₀Lift, gLift, downA, upX, downX, commonUniverseULiftMap,
      ContinuousMap.comp_apply] using hF (t, ULift.up a)
  · intro hi Y _ f₀ g H
    let upX : C(X, ULift.{u} X) := ⟨ULift.up, continuous_uliftUp⟩
    let upA : C(A, ULift.{v} A) := ⟨ULift.up, continuous_uliftUp⟩
    let f₀Base : C(X, Y) := f₀.comp upX
    let gBase : C(A, Y) := g.comp upA
    -- Precompose the lifted homotopy with `ULift.up : A → ULift A` to reduce to the original
    -- cofibration problem for `i`.
    let HBase : (f₀Base.comp i).Homotopy gBase := by
      simpa [f₀Base, gBase, upA, upX, commonUniverseULiftMap, ContinuousMap.comp_assoc] using
        H.compContinuousMap upA
    obtain ⟨G, F, hF⟩ := hi.exists_homotopy_extension f₀Base gBase HBase
    let downX : C(ULift.{u} X, X) := ⟨ULift.down, continuous_uliftDown⟩
    let GLift : C(ULift.{u} X, Y) := G.comp downX
    -- Extend back to the lifted source by precomposing the original extension with
    -- `ULift.down : ULift X → X`.
    let FLift : f₀.Homotopy GLift := by
      simpa [f₀Base, GLift, upX, downX, ContinuousMap.comp_assoc] using
        F.compContinuousMap downX
    refine ⟨GLift, FLift, ?_⟩
    intro z
    rcases z with ⟨t, a⟩
    -- Evaluate the original compatibility on `a.down` and then reinsert the `ULift` wrappers.
    simpa [HBase, FLift, GLift, f₀Base, gBase, upA, upX, downX, commonUniverseULiftMap,
      ContinuousMap.comp_apply] using hF (t, a.down)

/-- Helper for Lemma 7.2.5: after lifting `i` to a common universe, the Chapter 6 mapping-cylinder
criterion becomes available without changing the cofibration hypothesis. -/
theorem isCofibration_iff_exists_mappingCylinderRetract_commonUniverseULiftMap
    {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    IsCofibration.{u, v, max u v} i ↔
      ∃ r : C(ULift.{u} X × I, (commonUniverseULiftMap i).mappingCylinder),
        IsMappingCylinderRetract r := by
  rw [← isCofibration_commonUniverseULiftMap_iff (i := i)]
  exact isCofibration_iff_exists_mappingCylinderRetract (i := commonUniverseULiftMap i)

end ContinuousMap

/-- Helper for Lemma 7.2.5: compact generation transfers across a homeomorphism. -/
theorem uCompactlyGeneratedSpace_homeomorph
    {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{v} X]
    {Y : Type s} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{v} Y := by
  -- Check continuity after pulling back along the homeomorphism and then compose with the inverse.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  have hPullback : Continuous (f ∘ e) := by
    refine continuous_from_uCompactlyGeneratedSpace (f ∘ e) ?_
    intro S g
    have hComp : Continuous ((f ∘ e) ∘ g) := by
      simpa [Function.comp_def] using hf (CompHaus.of S) ⟨e ∘ g, e.continuous.comp g.continuous⟩
    simpa [Function.comp_def] using hComp
  simpa [Function.comp_def] using hPullback.comp e.symm.continuous

/-- Helper for Lemma 7.2.5: a closed subtype of a same-universe `UCompactlyGeneratedSpace` is
again `UCompactlyGeneratedSpace`. -/
theorem closedSubtypeUCompactlyGeneratedSpace
    {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    {s : Set X} (hs : IsClosed s) :
    UCompactlyGeneratedSpace.{u} s := by
  refine uCompactlyGeneratedSpace_of_isClosed fun t ht ↦ ?_
  refine hs.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.2 <|
    UCompactlyGeneratedSpace.isClosed fun K g ↦ ?_
  let probePreimage : Set K := g ⁻¹' s
  have hProbePreimage : IsClosed probePreimage := hs.preimage g.continuous
  letI : CompactSpace probePreimage := isCompact_iff_compactSpace.mp hProbePreimage.isCompact
  let liftedProbe : C(probePreimage, s) :=
    ⟨fun x : probePreimage ↦ ⟨g x, x.2⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk fun x : probePreimage ↦ x.2⟩
  have hClosed : IsClosed (liftedProbe ⁻¹' t) := ht (CompHaus.of probePreimage) liftedProbe
  have hImageClosed : IsClosed (((↑) : probePreimage → K) '' (liftedProbe ⁻¹' t)) :=
    hProbePreimage.isClosedMap_subtype_val _ hClosed
  suffices
      ((↑) : probePreimage → K) '' (liftedProbe ⁻¹' t) = g ⁻¹' ((↑) '' (t : Set s)) by
    simpa [this] using hImageClosed
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨liftedProbe x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxProbe : x ∈ probePreimage := by
      change g x ∈ s
      simpa [hyx] using y.2
    refine ⟨⟨x, hxProbe⟩, ?_, rfl⟩
    change (⟨g x, hxProbe⟩ : s) ∈ t
    have hxy : (⟨g x, hxProbe⟩ : s) = y := by
      apply Subtype.ext
      simp [hyx]
    simpa [hxy] using hy

/- The former implementation inserted here claimed that products preserve arbitrary coinduced
topologies, and used that claim to conclude that the ordinary product of two compactly generated
spaces is compactly generated.  Both claims are false in general.  The obsolete block is retained
temporarily as a comment while the valid `U`-product interfaces below replace its consumers.

/-- Helper for Lemma 7.2.5: the product of two coinduced topologies is the coinduced topology of
the corresponding product map. -/
theorem prodCoinduced_eq_coinduced_prodMap
    {A : Type _} {B : Type _} {C : Type _} {D : Type _}
    [TopologicalSpace A] [TopologicalSpace C] (f : A → B) (g : C → D) :
    @instTopologicalSpaceProd B D (TopologicalSpace.coinduced f inferInstance)
      (TopologicalSpace.coinduced g inferInstance) =
        TopologicalSpace.coinduced (Prod.map f g)
          (inferInstance : TopologicalSpace (A × C)) := by
  let s : Set (Set B) := {u | IsOpen (f ⁻¹' u)}
  let t : Set (Set D) := {v | IsOpen (g ⁻¹' v)}
  have hs : ⋃₀ s = (Set.univ : Set B) := by
    ext b
    constructor
    · intro _
      simp
    · intro _
      refine Set.mem_sUnion.2 ?_
      refine ⟨Set.univ, ?_, ?_⟩
      · simp [s]
      · simp
  have ht : ⋃₀ t = (Set.univ : Set D) := by
    ext d
    constructor
    · intro _
      simp
    · intro _
      refine Set.mem_sUnion.2 ?_
      refine ⟨Set.univ, ?_, ?_⟩
      · simp [t]
      · simp
  have hsOpen :
      {u | IsOpen[TopologicalSpace.coinduced f inferInstance] u} = s := by
    ext u
    show IsOpen[TopologicalSpace.coinduced f inferInstance] u ↔ IsOpen (f ⁻¹' u)
    rw [isOpen_coinduced]
  have htOpen :
      {v | IsOpen[TopologicalSpace.coinduced g inferInstance] v} = t := by
    ext v
    show IsOpen[TopologicalSpace.coinduced g inferInstance] v ↔ IsOpen (g ⁻¹' v)
    rw [isOpen_coinduced]
  rw [← TopologicalSpace.generateFrom_setOf_isOpen (TopologicalSpace.coinduced f inferInstance),
    ← TopologicalSpace.generateFrom_setOf_isOpen (TopologicalSpace.coinduced g inferInstance),
    hsOpen, htOpen]
  rw [prod_generateFrom_generateFrom_eq hs ht]
  have hLeft :
      Continuous[ inferInstance, TopologicalSpace.generateFrom s]
        (fun p : A × C ↦ f p.1) := by
    rw [continuous_iff_coinduced_le]
    refine le_generateFrom ?_
    intro u hu
    have huOpen : IsOpen (f ⁻¹' u) := by
      simpa [s] using hu
    simpa [Function.comp] using huOpen.preimage continuous_fst
  have hRight :
      Continuous[ inferInstance, TopologicalSpace.generateFrom t]
        (fun p : A × C ↦ g p.2) := by
    rw [continuous_iff_coinduced_le]
    refine le_generateFrom ?_
    intro v hv
    have hvOpen : IsOpen (g ⁻¹' v) := by
      simpa [t] using hv
    simpa [Function.comp] using hvOpen.preimage continuous_snd
  apply le_antisymm
  · refine le_generateFrom ?_
    rintro _ ⟨u, hu, v, hv, rfl⟩
    have huOpen : IsOpen (f ⁻¹' u) := by
      simpa [s] using hu
    have hvOpen : IsOpen (g ⁻¹' v) := by
      simpa [t] using hv
    show IsOpen[TopologicalSpace.coinduced (Prod.map f g) inferInstance] (u ×ˢ v)
    rw [isOpen_coinduced]
    simpa [Prod.map] using huOpen.prod hvOpen
  · have hFst :
        Continuous[TopologicalSpace.coinduced (Prod.map f g) inferInstance,
          TopologicalSpace.generateFrom s] Prod.fst := by
      rw [continuous_coinduced_dom]
      simpa [Function.comp, Prod.map] using hLeft
    have hSnd :
        Continuous[TopologicalSpace.coinduced (Prod.map f g) inferInstance,
          TopologicalSpace.generateFrom t] Prod.snd := by
      rw [continuous_coinduced_dom]
      simpa [Function.comp, Prod.map] using hRight
    have hId :
        @Continuous (B × D) (B × D)
          (TopologicalSpace.coinduced (Prod.map f g) inferInstance)
          (@instTopologicalSpaceProd B D
            (TopologicalSpace.generateFrom s) (TopologicalSpace.generateFrom t))
          id := by
      -- Package the two coordinate maps into the identity written as a pair.
      simpa using
        (show
            @Continuous (B × D) (B × D)
              (TopologicalSpace.coinduced (Prod.map f g) inferInstance)
              (@instTopologicalSpaceProd B D
                (TopologicalSpace.generateFrom s) (TopologicalSpace.generateFrom t))
              (fun p : B × D ↦ (Prod.fst p, Prod.snd p))
          from hFst.prodMk hSnd)
    exact continuous_id_iff_le.mp hId

/-- Helper for Lemma 7.2.5: compactly generated weak Hausdorff spaces are closed under finite
products. -/
theorem compactlyGeneratedWeakHausdorffSpaceProd
    (Y : Type u) (Z : Type v)
    [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]
    [CompactlyGeneratedWeakHausdorffSpace.{v, v} Z] :
    CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} (Y × Z) := by
  let YIndex := (S : CompHaus.{max u v}) × C(S, Y)
  let ZIndex := (S : CompHaus.{max u v}) × C(S, Z)
  let YSource := Σ j : YIndex, j.1
  let ZSource := Σ j : ZIndex, j.1
  let yEval : YSource → Y := fun y ↦ y.1.2 y.2
  let zEval : ZSource → Z := fun z ↦ z.1.2 z.2
  let _ : ∀ j : YIndex, UCompactlyGeneratedSpace j.1 := by
    intro j
    exact compactHausdorff_uCompactlyGenerated
  let _ : ∀ j : ZIndex, UCompactlyGeneratedSpace j.1 := by
    intro j
    exact compactHausdorff_uCompactlyGenerated
  let _ : UCompactlyGeneratedSpace.{max u v} YSource := inferInstance
  let _ : UCompactlyGeneratedSpace.{max u v} ZSource := inferInstance
  let _ : WeaklyLocallyCompactSpace YSource := by
    refine ⟨?_⟩
    intro y
    refine ⟨Set.range (Sigma.mk y.1), ?_, ?_⟩
    · simpa using (show IsCompact (Set.range (Sigma.mk y.1 : y.1.1 → YSource)) from
        Continuous.isCompact_range continuous_sigmaMk)
    · exact isOpen_range_sigmaMk.mem_nhds ⟨y.2, rfl⟩
  let _ : WeaklyLocallyCompactSpace ZSource := by
    refine ⟨?_⟩
    intro z
    refine ⟨Set.range (Sigma.mk z.1), ?_, ?_⟩
    · simpa using (show IsCompact (Set.range (Sigma.mk z.1 : z.1.1 → ZSource)) from
        Continuous.isCompact_range continuous_sigmaMk)
    · exact isOpen_range_sigmaMk.mem_nhds ⟨z.2, rfl⟩
  let _ : T2Space ZSource := inferInstance
  let _ : WeaklyHausdorffSpace.{max u v, max u v} ZSource := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u v, max u v} ZSource := by
    exact
      @CompactlyGeneratedWeakHausdorffSpace.mk.{max u v, max u v} ZSource inferInstance
        inferInstance inferInstance
  let hWeak : WeaklyHausdorffSpace.{max u v, max u v} (Y × Z) :=
    weaklyHausdorffSpaceProd_direct (X := Y) (Y := Z)
  have hYk :
      TopologicalSpace.compactlyGenerated.{max u v, u} Y = ‹TopologicalSpace Y› := by
    let _ : UCompactlyGeneratedSpace.{max u v} Y :=
      CompactlyGenerated.uCompactlyGeneratedSpaceLift (X := Y)
    exact (eq_compactlyGenerated (X := Y)).symm
  have hZk :
      TopologicalSpace.compactlyGenerated.{max u v, v} Z = ‹TopologicalSpace Z› := by
    let _ : UCompactlyGeneratedSpace.{max u v} Z :=
      CompactlyGenerated.uCompactlyGeneratedSpaceLift (X := Z)
    exact (eq_compactlyGenerated (X := Z)).symm
  have hCompact : UCompactlyGeneratedSpace.{max u v} (Y × Z) := by
    let _ : UCompactlyGeneratedSpace.{max u v} (YSource × ZSource) := inferInstance
    have hCoinduced :
        @UCompactlyGeneratedSpace.{max u v} (Y × Z)
          (TopologicalSpace.coinduced (Prod.map yEval zEval)
            (inferInstance : TopologicalSpace (YSource × ZSource))) := by
      let _ : TopologicalSpace (Y × Z) :=
        TopologicalSpace.coinduced (Prod.map yEval zEval)
          (inferInstance : TopologicalSpace (YSource × ZSource))
      exact uCompactlyGeneratedSpace_of_coinduced
        (f := Prod.map yEval zEval) continuous_coinduced_rng rfl
    have hProdCoinduced :
        @instTopologicalSpaceProd Y Z
            (TopologicalSpace.coinduced yEval inferInstance)
            (TopologicalSpace.coinduced zEval inferInstance) =
          TopologicalSpace.coinduced (Prod.map yEval zEval)
            (inferInstance : TopologicalSpace (YSource × ZSource)) := by
      simpa [yEval, zEval, YSource, ZSource, YIndex, ZIndex] using
        (prodCoinduced_eq_coinduced_prodMap yEval zEval)
    have hYCoinduced :
        TopologicalSpace.coinduced yEval inferInstance =
          TopologicalSpace.compactlyGenerated.{max u v, u} Y := by
      rfl
    have hZCoinduced :
        TopologicalSpace.coinduced zEval inferInstance =
          TopologicalSpace.compactlyGenerated.{max u v, v} Z := by
      rfl
    rw [← hYk, ← hZk, hYCoinduced, hZCoinduced] at hProdCoinduced
    rw [← hProdCoinduced]
    exact hCoinduced
  exact
    @CompactlyGeneratedWeakHausdorffSpace.mk.{max u v, max u v} (Y × Z) inferInstance hWeak
      hCompact
-/

/-- Helper for Lemma 7.2.5: `Y × I` is compactly generated weak Hausdorff whenever `Y` is. -/
theorem compactlyGeneratedWeakHausdorffSpaceProdUnitIntervalRight
    (Y : Type u) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y] :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (Y × I) := by
  let _ : WeaklyHausdorffSpace.{0, u} I :=
    CompactlyGenerated.weaklyHausdorffSpaceLift (X := I)
  let hWeak : WeaklyHausdorffSpace.{u, u} (Y × I) :=
    weaklyHausdorffSpaceProd_direct (X := Y) (Y := I)
  let hIntervalProduct : UCompactlyGeneratedSpace.{u} (I × Y) :=
    ordinaryProductTopology_uCompactlyGenerated (X := I) (Y := Y)
  let _ : UCompactlyGeneratedSpace.{u} (I × Y) := hIntervalProduct
  let hCompact : UCompactlyGeneratedSpace.{u} (Y × I) :=
    uCompactlyGeneratedSpace_homeomorph (Homeomorph.prodComm I Y)
  exact
    @CompactlyGeneratedWeakHausdorffSpace.mk.{u, u} (Y × I) inferInstance hWeak hCompact

/-- Helper for Lemma 7.2.5: compact generation passes to `ULift X`. -/
instance uliftUCompactlyGeneratedSpace
    (Y : Type u) [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y] :
    UCompactlyGeneratedSpace.{max u w} (ULift.{w} Y) := by
  let _ : UCompactlyGeneratedSpace.{max u w} Y := by
    simpa [max_comm] using
      (CompactlyGenerated.uCompactlyGeneratedSpaceLift.{u, w} (X := Y) :
        UCompactlyGeneratedSpace.{max u w} Y)
  exact uCompactlyGeneratedSpace_homeomorph
    (e := (Homeomorph.ulift.symm : Y ≃ₜ ULift.{w} Y))

/-- Helper for Lemma 7.2.5: weak Hausdorffness passes to `ULift X`. -/
instance uliftWeaklyHausdorffSpace
    (Y : Type u) [TopologicalSpace Y] [WeaklyHausdorffSpace.{u, u} Y] :
    WeaklyHausdorffSpace.{max u w, max u w} (ULift.{w} Y) := by
  let _ : WeaklyHausdorffSpace.{u, max u w} Y := by
    simpa [max_comm] using
      (CompactlyGenerated.weaklyHausdorffSpaceLift.{u, w} (X := Y) :
        WeaklyHausdorffSpace.{u, max u w} Y)
  simpa using
    (Homeomorph.ulift : ULift.{w} Y ≃ₜ Y).isEmbedding.weaklyHausdorffSpace

/-- Helper for Lemma 7.2.5: compactly generated weak Hausdorff spaces remain so after `ULift`. -/
instance uliftCompactlyGeneratedWeakHausdorffSpace
    (Y : Type u) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y] :
    CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (ULift.{w} Y) := by
  exact
    @CompactlyGeneratedWeakHausdorffSpace.mk.{max u w, max u w} _ inferInstance
      inferInstance inferInstance

section TransportHelpers

variable {A : Type u} {X : Type v} {B : Type w}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace A]
variable [CompactlyGeneratedWeakHausdorffSpace X]
variable [CompactlyGeneratedWeakHausdorffSpace B]

/-- Helper for Lemma 7.2.5: the product of the unit interval with a compactly generated weak
Hausdorff space is again compactly generated weak Hausdorff. -/
instance instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval
    (Y : Type s) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{s, s} Y] :
    CompactlyGeneratedWeakHausdorffSpace.{s, s} (I × Y) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace I := inferInstance
  let _ : WeaklyHausdorffSpace.{0, s} I :=
    CompactlyGenerated.weaklyHausdorffSpaceLift.{0, s} (X := I)
  -- The weak Hausdorff part comes from the direct product theorem.
  let hwh : WeaklyHausdorffSpace.{s, s} (I × Y) :=
    weaklyHausdorffSpaceProd_direct (X := I) (Y := Y)
  -- Compact generation follows because `I` is locally compact.
  let hcg : UCompactlyGeneratedSpace.{s} (I × Y) :=
    ordinaryProductTopology_uCompactlyGenerated (X := I) (Y := Y)
  exact
    @CompactlyGeneratedWeakHausdorffSpace.mk.{s, s} (I × Y) inferInstance hwh hcg

/-- Helper for Lemma 7.2.5: a compactly generated weak Hausdorff space is homeomorphic to its
`Kified` replacement. -/
noncomputable def kifiedHomeomorph
    (Y : Type s) [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace.{s, s} Y] :
    Kified Y ≃ₜ Y :=
  { toEquiv :=
      { toFun := Kified.of
        invFun := Kified.mk
        left_inv := by
          intro y
          cases y
          rfl
        right_inv := by
          intro y
          rfl }
    continuous_toFun := continuousKifiedForget Y
    continuous_invFun := by
      -- Compact generation makes the identity map continuous into the kified codomain.
      simpa using
        (continuousToKifiedOfContinuous (f := fun y : Y ↦ y) continuous_id) }

/-- Helper for Lemma 7.2.5: swapping the factors of a product commutes with `Kified`. -/
noncomputable def kifiedProdCommHomeomorph
    (Y : Type u) (Z : Type v) [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedWeakHausdorffSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace Z] :
    Kified (Y × Z) ≃ₜ Kified (Z × Y) :=
  { toEquiv :=
      { toFun := fun q ↦ Kified.mk (q.of.2, q.of.1)
        invFun := fun q ↦ Kified.mk (q.of.2, q.of.1)
        left_inv := by rintro ⟨⟨y, z⟩⟩; rfl
        right_inv := by rintro ⟨⟨z, y⟩⟩; rfl }
    continuous_toFun := by
      have h : Continuous fun q : Kified (Y × Z) ↦ (q.of.2, q.of.1) :=
        (Homeomorph.prodComm Y Z).continuous.comp (continuousKifiedForget (Y × Z))
      exact continuousToKifiedOfContinuous h
    continuous_invFun := by
      have h : Continuous fun q : Kified (Z × Y) ↦ (q.of.2, q.of.1) :=
        (Homeomorph.prodComm Z Y).continuous.comp (continuousKifiedForget (Z × Y))
      exact continuousToKifiedOfContinuous h }

/-- Helper for Lemma 7.2.5: a continuous family `M → B ^ Z` may be transposed into a continuous
family `Z → B ^ M` by uncurrying, swapping the two parameters, and currying again. -/
noncomputable abbrev mapSpaceTranspose
    (M : Type u) (Z : Type v) (B : Type w)
    [TopologicalSpace M] [TopologicalSpace Z] [TopologicalSpace B]
    [CompactlyGeneratedWeakHausdorffSpace M]
    [CompactlyGeneratedWeakHausdorffSpace Z]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (g : C(M, B ^ Z)) : C(Z, B ^ M) :=
  CompactlyGenerated.mapSpaceCurryHomeomorph Z M B <|
    CompactlyGenerated.MapSpace.ofContinuousMap
      (((CompactlyGenerated.mapSpaceUncurry M Z B g : B ^ Kified (M × Z)) :
          C(Kified (M × Z), B)).comp
        ⟨kifiedProdCommHomeomorph Z M, (kifiedProdCommHomeomorph Z M).continuous_toFun⟩)

/-- Helper for Lemma 7.2.5: transposing a family `M → B ^ Z` simply swaps the two evaluation
variables. -/
@[simp] theorem mapSpaceTranspose_apply
    (M : Type u) (Z : Type v) (B : Type w)
    [TopologicalSpace M] [TopologicalSpace Z] [TopologicalSpace B]
    [CompactlyGeneratedWeakHausdorffSpace M]
    [CompactlyGeneratedWeakHausdorffSpace Z]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (g : C(M, B ^ Z)) (z : Z) (m : M) :
    mapSpaceTranspose M Z B g z m = g m z := by
  -- Evaluate the curried/uncurried composite through the product-swap homeomorphism.
  rfl

/-- Helper for Lemma 7.2.5: a map `X × I → B` may be repackaged as a path in `B ^ X` by swapping
the two source coordinates and currying. -/
noncomputable def mapSpaceProdToPathMap
    (X : Type u) (B : Type w)
    [TopologicalSpace X] [TopologicalSpace B]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    C(B ^ (X × I), C(I, B ^ X)) := by
  let hX : CompactlyGeneratedWeakHausdorffSpace.{u, u} X := inferInstance
  let hB : CompactlyGeneratedWeakHausdorffSpace.{w, w} B := inferInstance
  let hI : CompactlyGeneratedWeakHausdorffSpace.{0, 0} I := inferInstance
  let hXI : CompactlyGeneratedWeakHausdorffSpace.{u, u} (X × I) :=
    compactlyGeneratedWeakHausdorffSpaceProdUnitIntervalRight X
  let hIX : CompactlyGeneratedWeakHausdorffSpace.{u, u} (I × X) :=
    instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval X
  let hXILift : CompactlyGeneratedWeakHausdorffSpace.{u, max u w} (X × I) :=
    @CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{u, w}
      (X × I) inferInstance hXI
  let hBLift : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} B := by
    simpa [max_comm] using
      (@CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{w, u} B inferInstance hB)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} B := hBLift
  let hMapSource : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ (X × I)) :=
    @CompactlyGenerated.mapSpaceCompactlyGeneratedWeakHausdorffSpace.{u, w}
      (X × I) B inferInstance inferInstance hXILift hBLift
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ (X × I)) := hMapSource
  let hKifiedIX : CompactlyGeneratedWeakHausdorffSpace.{u, u} (Kified (I × X)) := by
    let _ : CompactlyGeneratedWeakHausdorffSpace.{u, u} (I × X) := hIX
    exact inferInstance
  let hKifiedIXLift :
      CompactlyGeneratedWeakHausdorffSpace.{u, max u w} (Kified (I × X)) :=
    @CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{u, w}
      (Kified (I × X)) inferInstance hKifiedIX
  let hContinuousMap : WeaklyHausdorffSpace.{max u w, max u w} C(Kified (I × X), B) :=
    @CompactlyGenerated.continuousMapWeaklyHausdorffSpace.{u, w}
      (Kified (I × X)) B inferInstance inferInstance hBLift.toWeaklyHausdorffSpace
  let _ : WeaklyHausdorffSpace.{max u w, max u w} C(Kified (I × X), B) := hContinuousMap
  let swapSource : C(Kified (I × X), X × I) :=
    ⟨fun q ↦ (q.of.2, q.of.1),
      (Homeomorph.prodComm I X).continuous.comp (continuousKifiedForget (I × X))⟩
  let swapMap : C(B ^ (X × I), C(Kified (I × X), B)) :=
    ⟨fun f ↦
        ((f : C(X × I, B)).comp swapSource),
      by
        -- Forget the k-topology once, then precompose the underlying ordinary maps with the
        -- swapped source homeomorphism.
        exact
          (ContinuousMap.continuous_precomp
            swapSource).comp
              (continuousKifiedForget C(X × I, B))⟩
  let swappedMap : C(B ^ (X × I), B ^ Kified (I × X)) :=
    ⟨fun f ↦
        CompactlyGenerated.MapSpace.ofContinuousMap
          ((f : C(X × I, B)).comp swapSource),
      by
        -- Forget the k-topology once, precompose by the swap homeomorphism, then repackage the
        -- resulting ordinary map family into the compactly generated mapping space.
        let _ : UCompactlyGeneratedSpace (B ^ (X × I)) := inferInstance
        have hSwap :
            Continuous fun f : B ^ (X × I) ↦
              (((f : C(X × I, B)).comp
                  swapSource) :
                C(Kified (I × X), B)) :=
          (ContinuousMap.continuous_precomp
            swapSource).comp
              (continuousKifiedForget C(X × I, B))
        simpa [CompactlyGenerated.MapSpace.ofContinuousMap] using
          (CompactlyGenerated.continuousToMapSpaceOfContinuous
            (A := Kified (I × X)) (B := B)
            (f := fun f : B ^ (X × I) ↦
              (((f : C(X × I, B)).comp
                  swapSource) :
                C(Kified (I × X), B))) hSwap)⟩
  let curryHomeomorph :=
    @CompactlyGenerated.mapSpaceCurryHomeomorph.{0, u, w}
      I inferInstance hI X inferInstance hX B inferInstance hB
  let curryMap : C(B ^ Kified (I × X), C(I, B ^ X)) :=
    ⟨fun f ↦ curryHomeomorph f,
      (continuousKifiedForget C(I, B ^ X)).comp
        curryHomeomorph.continuous_toFun⟩
  -- The desired map is the composition: forget, swap, repackage, and finally curry.
  exact curryMap.comp swappedMap

/-- Helper for Lemma 7.2.5: evaluating `mapSpaceProdToPathMap` recovers the original map on the
swapped pair `(x, t)`. -/
@[simp] theorem mapSpaceProdToPathMap_apply
    (X : Type u) (B : Type w)
    [TopologicalSpace X] [TopologicalSpace B]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (f : B ^ (X × I)) (t : I) (x : X) :
    mapSpaceProdToPathMap X B f t x = f (x, t) := by
  -- Evaluate the swapped-source curry formula on the generator `(t, x)` of `I × X`.
  rfl

/-- Helper for Lemma 7.2.5: the point coordinate of a restriction mapping path yields the family
`X → B ^ MappingPathSpace (mapSpaceRestriction i)`. -/
noncomputable abbrev restrictionMappingPathPointFamily {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))] :
    C(X, B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :=
  CompactlyGenerated.mapSpaceCurryHomeomorph X
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) B <|
    CompactlyGenerated.MapSpace.ofContinuousMap
      ⟨fun q : Kified (X × MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) ↦
          (q.of.2.point : B ^ X) q.of.1,
        restrictionMappingPathPointUncurryContinuous i⟩

/-- Helper for Lemma 7.2.5: evaluating the point family recovers the stored point of the mapping
path. -/
@[simp] theorem restrictionMappingPathPointFamily_apply {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))]
    (x : X) (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :
    restrictionMappingPathPointFamily (B := B) (i := i) x z = (z.point : B ^ X) x := by
  -- Read the curried family on the generator `(x, z)` of the product source.
  simp [restrictionMappingPathPointFamily]

/-- Helper for Lemma 7.2.5: the stored base path of a restriction mapping path yields the family
`A × I → B ^ MappingPathSpace (mapSpaceRestriction i)`. -/
noncomputable abbrev restrictionMappingPathBoundaryFamily {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))] :
    C(A × I, B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :=
  CompactlyGenerated.mapSpaceCurryHomeomorph (A × I)
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) B <|
    CompactlyGenerated.MapSpace.ofContinuousMap
      ⟨fun q : Kified ((A × I) × MappingPathSpace
            ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) ↦
          ((q.of.2.path q.of.1.2 : B ^ A) q.of.1.1),
        restrictionMappingPathBoundaryUncurryContinuous i⟩

/-- Helper for Lemma 7.2.5: evaluating the boundary family recovers the stored base path of the
mapping path. -/
@[simp] theorem restrictionMappingPathBoundaryFamily_apply {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))]
    (a : A) (t : I) (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :
    restrictionMappingPathBoundaryFamily (B := B) (i := i) (a, t) z =
      ((z.path t : B ^ A) a) := by
  -- Read the curried boundary family on the generator `((a, t), z)` of the product source.
  simp [restrictionMappingPathBoundaryFamily]

/-- Helper for Lemma 7.2.5: the time-`0` face of the boundary family is the restriction of the
point family along `i`. -/
theorem restrictionMappingPathBoundaryZero {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))]
    (a : A) :
    restrictionMappingPathBoundaryFamily (B := B) (i := i) (a, 0) =
      (restrictionMappingPathPointFamily (B := B) (i := i).comp i) a := by
  -- Reduce the map-space equality to the pointwise zero-time identity in the mapping path space.
  ext z
  simp [restrictionMappingPathBoundaryFamily, restrictionMappingPathPointFamily,
    ContinuousMap.comp_apply, restrictionMappingPathZero_apply]

/-- Helper for Lemma 7.2.5: the boundary family packages to a homotopy in `B ^ MappingPathSpace
(mapSpaceRestriction i)` whose initial map is the restriction of the point family. -/
theorem restrictionMappingPathBoundaryOne {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))]
    (a : A) :
    restrictionMappingPathBoundaryFamily (B := B) (i := i) (a, 1) =
      (restrictionMappingPathBoundaryFamily (B := B) (i := i)).comp
        ((ContinuousMap.id A).prodMk (ContinuousMap.const A (1 : I))) a := by
  -- The terminal face is definitionally the `t = 1` slice of the same `I × A` family.
  simp [restrictionMappingPathBoundaryFamily, ContinuousMap.comp_apply]

/-- Helper for Lemma 7.2.5: the boundary family packages to a homotopy in `B ^ MappingPathSpace
(mapSpaceRestriction i)` whose initial map is the restriction of the point family. -/
noncomputable def restrictionMappingPathBoundaryHomotopy {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))] :
    ((restrictionMappingPathPointFamily (B := B) (i := i)).comp i).Homotopy
      ((restrictionMappingPathBoundaryFamily (B := B) (i := i)).comp
        ((ContinuousMap.id A).prodMk (ContinuousMap.const A (1 : I)))) :=
  ContinuousMap.Homotopy.ofProdSwap
    (restrictionMappingPathBoundaryFamily (B := B) (i := i))
    (restrictionMappingPathBoundaryZero (B := B) (i := i))
    (restrictionMappingPathBoundaryOne (B := B) (i := i))

/-- Helper for Lemma 7.2.5: evaluating the packaged boundary homotopy reads off the stored base
path coordinate. -/
@[simp] theorem restrictionMappingPathBoundaryHomotopy_apply {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace (A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A)))]
    (a : A) (t : I) (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) :
    restrictionMappingPathBoundaryHomotopy (B := B) (i := i) (t, a) z =
      ((z.path t : B ^ A) a) := by
  -- Unpack the `prodSwap` homotopy and then read off the boundary-family value at `(a, t)`.
  change restrictionMappingPathBoundaryFamily (B := B) (i := i) (a, t) z =
    ((z.path t : B ^ A) a)
  simp [restrictionMappingPathBoundaryFamily]

end TransportHelpers

/-- Helper for Lemma 7.2.5: lifting both source and target of `i` by the same `ULift.{s}`
conjugates the restriction map to the original one. -/
theorem restrictionMap_sameUniverseULiftMap_conj {A X : Type u} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]
    {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    ∃ eX : (B ^ ULift.{s} X) ≃ₜ (B ^ X),
      ∃ eA : (B ^ ULift.{s} A) ≃ₜ (B ^ A),
        let eXMap : C(B ^ ULift.{s} X, B ^ X) := ⟨eX, eX.continuous_toFun⟩
        let eAMap : C(B ^ ULift.{s} A, B ^ A) := ⟨eA, eA.continuous_toFun⟩
        eAMap.comp ((mapSpaceRestriction (B := B) (ContinuousMap.sameUniverseULiftMap i :
          C(ULift.{s} A, ULift.{s} X))) :
          C(B ^ ULift.{s} X, B ^ ULift.{s} A)) =
          ((mapSpaceRestriction i) : C(B ^ X, B ^ A)).comp eXMap := by
  let _ : CompactlyGeneratedWeakHausdorffSpace (ULift.{s} X) := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace (ULift.{s} A) := inferInstance
  let upX : C(X, ULift.{s} X) := ⟨ULift.up, continuous_uliftUp⟩
  let downX : C(ULift.{s} X, X) := ⟨ULift.down, continuous_uliftDown⟩
  let upA : C(A, ULift.{s} A) := ⟨ULift.up, continuous_uliftUp⟩
  let downA : C(ULift.{s} A, A) := ⟨ULift.down, continuous_uliftDown⟩
  let eXTo : C(B ^ ULift.{s} X, B ^ X) := mapSpaceRestriction upX
  let eXInv : C(B ^ X, B ^ ULift.{s} X) := mapSpaceRestriction downX
  let eATo : C(B ^ ULift.{s} A, B ^ A) := mapSpaceRestriction upA
  let eAInv : C(B ^ A, B ^ ULift.{s} A) := mapSpaceRestriction downA
  let eX : (B ^ ULift.{s} X) ≃ₜ (B ^ X) :=
    { toEquiv :=
        { toFun := eXTo
          invFun := eXInv
          left_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, upX, downX, mapSpaceRestriction]
          right_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, upX, downX, mapSpaceRestriction] }
      continuous_toFun := eXTo.continuous
      continuous_invFun := eXInv.continuous }
  let eA : (B ^ ULift.{s} A) ≃ₜ (B ^ A) :=
    { toEquiv :=
        { toFun := eATo
          invFun := eAInv
          left_inv := by
            intro f
            ext a
            simp [eATo, eAInv, upA, downA, mapSpaceRestriction]
          right_inv := by
            intro f
            ext a
            simp [eATo, eAInv, upA, downA, mapSpaceRestriction] }
      continuous_toFun := eATo.continuous
      continuous_invFun := eAInv.continuous }
  refine ⟨eX, eA, ?_⟩
  -- Evaluate both sides on an arbitrary map `f : B ^ ULift A` and point `a : A`; both compute to
  -- `f (ULift.up (i a))`.
  ext f a
  simp [eX, eA, eXTo, eATo, upX, upA, mapSpaceRestriction, ContinuousMap.sameUniverseULiftMap,
    ContinuousMap.comp_apply]

namespace ContinuousPathLiftingFunction

/-- Helper for Lemma 7.2.5: a continuous path lifting function transports across a conjugation
square of maps. -/
noncomputable def ofConjugate
    {E : Type u} {B : Type v} {E' : Type w} {B' : Type s}
    [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace B']
    {p : C(E, B)} {p' : C(E', B')}
    [UCompactlyGeneratedSpace.{max w s} (MappingPathSpace p)]
    (eE : E' ≃ₜ E) (eB : B' ≃ₜ B)
    (hsquare :
      ((⟨eB, eB.continuous_toFun⟩ : C(B', B)).comp p') =
        p.comp (⟨eE, eE.continuous_toFun⟩ : C(E', E)))
    (s : ContinuousPathLiftingFunction p') :
    ContinuousPathLiftingFunction p := by
  let eEMap : C(E', E) := ⟨eE, eE.continuous_toFun⟩
  let eEInvMap : C(E, E') := ⟨eE.symm, eE.symm.continuous_toFun⟩
  let eBMap : C(B', B) := ⟨eB, eB.continuous_toFun⟩
  let eBInvMap : C(B, B') := ⟨eB.symm, eB.symm.continuous_toFun⟩
  let transportedInput : C(MappingPathSpace p, MappingPathSpace p') :=
    { toFun := fun z ↦
        MappingPathSpace.mk (eE.symm z.point) (eBInvMap.comp z.path) <| by
          have hsquarePoint :
              eB (p' (eE.symm z.point)) = p z.point := by
            simpa [eEMap, eBMap, ContinuousMap.comp_apply] using
              congrArg (fun f : C(E', B) ↦ f (eE.symm z.point)) hsquare
          apply eB.injective
          simpa [eBInvMap, ContinuousMap.comp_apply, z.path_zero_eq] using hsquarePoint.symm
      continuous_toFun := by
        have hpoint : Continuous fun z : MappingPathSpace p ↦ eE.symm z.point := by
          exact eE.symm.continuous.comp (mappingPathSpacePointContinuous p)
        have hpath : Continuous fun z : MappingPathSpace p ↦ eBInvMap.comp z.path := by
          exact (ContinuousMap.continuous_postcomp eBInvMap).comp
            (mappingPathSpacePathContinuous p)
        exact MappingPathSpace.continuous_mk hpoint hpath fun z ↦ by
          have hsquarePoint :
              eB (p' (eE.symm z.point)) = p z.point := by
            simpa [eEMap, eBMap, ContinuousMap.comp_apply] using
              congrArg (fun f : C(E', B) ↦ f (eE.symm z.point)) hsquare
          apply eB.injective
          simpa [eBInvMap, ContinuousMap.comp_apply, z.path_zero_eq] using hsquarePoint.symm }
  let pathTransport : C(C(I, E'), C(I, E)) :=
    ⟨fun γ ↦ eEMap.comp γ, ContinuousMap.continuous_postcomp eEMap⟩
  let lifted : C(MappingPathSpace p, C(I, E)) :=
    pathTransport.comp (s.toContinuousMap.comp transportedInput)
  refine
    { toContinuousMap := lifted
      source_eq := ?_
      proj_comp_eq := ?_ }
  · intro z
    simpa [lifted, pathTransport, transportedInput, eEMap] using
      congrArg eE (s.source_eq (transportedInput z))
  · intro z
    ext t
    have hsquarePoint :
        eB (p' (s.toContinuousMap (transportedInput z) t)) = p (lifted z t) := by
      simpa [lifted, pathTransport, eEMap, eBMap, ContinuousMap.comp_apply] using
        congrArg (fun f : C(E', B) ↦ f (s.toContinuousMap (transportedInput z) t)) hsquare
    have hsproj :
        eB (p' (s.toContinuousMap (transportedInput z) t)) = z.path t := by
      have hproj :=
        congrArg (fun γ : I → B' ↦ eB (γ t)) (s.proj_comp_eq (transportedInput z))
      simpa [transportedInput, eBInvMap, ContinuousMap.comp_apply] using hproj
    calc
      (p.comp (lifted z)) t = p (lifted z t) := rfl
      _ = eB (p' (s.toContinuousMap (transportedInput z) t)) := by
        exact hsquarePoint.symm
      _ = z.path t := hsproj

end ContinuousPathLiftingFunction

section SameUniverse

variable {A X : Type u} {B : Type w}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace A]
variable [CompactlyGeneratedWeakHausdorffSpace X]
variable [CompactlyGeneratedWeakHausdorffSpace B]

/-- Helper for Lemma 7.2.5: after lifting the source and target of `i` into the codomain
universe, descending the point and boundary families across the mapping cylinder gives the
canonical map into `B ^ MappingPathSpace (mapSpaceRestriction i)`. -/
noncomputable abbrev restrictionMappingCylinderDescSameUniverse {i : C(ULift.{w} A, ULift.{w} X)}
    [CompactlyGeneratedWeakHausdorffSpace (ULift.{w} A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A)))] :
    C(i.mappingCylinder,
      B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A))) :=
  -- Route correction: descend once to `C(i.mappingCylinder, B ^ Z)` and postpone every transpose
  -- until after the retract removes the mapping-cylinder variable.
  ContinuousMap.mappingCylinderDesc
    (restrictionMappingPathPointFamily (B := B) (i := i))
    (restrictionMappingPathBoundaryHomotopy (B := B) (i := i))

/-- Helper for Lemma 7.2.5: evaluating the descended mapping-cylinder family on the target-side
inclusion recovers the stored point of the mapping path. -/
theorem restrictionMappingCylinderDescSameUniverse_target_apply {i : C(ULift.{w} A, ULift.{w} X)}
    [CompactlyGeneratedWeakHausdorffSpace (ULift.{w} A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A)))]
    (x : ULift.{w} X)
    (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A))) :
    restrictionMappingCylinderDescSameUniverse (B := B) (i := i)
        ((ContinuousMap.mappingCylinderTargetInclusion i) x) z =
      (z.point : B ^ ULift.{w} X) x := by
  -- Read the target-side computation rule for the descended map and then evaluate the point
  -- family at the chosen point of `X` and mapping-path witness `z`.
  have hTarget :
      (restrictionMappingCylinderDescSameUniverse (B := B) (i := i)).comp
          (ContinuousMap.mappingCylinderTargetInclusion i) =
        restrictionMappingPathPointFamily (B := B) (i := i) := by
    simpa [restrictionMappingCylinderDescSameUniverse] using
      (ContinuousMap.mappingCylinderDesc_comp_targetInclusion
        (f₀ := restrictionMappingPathPointFamily (B := B) (i := i))
        (H := restrictionMappingPathBoundaryHomotopy (B := B) (i := i)))
  have hx :=
    congrArg
      (fun f :
        C(ULift.{w} X,
          B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A))) ↦
            f x) hTarget
  exact congrArg
    (fun f : B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A)) ↦
      f z) hx

/-- Helper for Lemma 7.2.5: evaluating the descended mapping-cylinder family on the cylinder-side
inclusion recovers the stored base path of the mapping path. -/
theorem restrictionMappingCylinderDescSameUniverse_cylinder_apply {i : C(ULift.{w} A, ULift.{w} X)}
    [CompactlyGeneratedWeakHausdorffSpace (ULift.{w} A × I)]
    [CompactlyGeneratedWeakHausdorffSpace
      (MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A)))]
    (a : ULift.{w} A) (t : I)
    (z : MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A))) :
    restrictionMappingCylinderDescSameUniverse (B := B) (i := i)
        ((ContinuousMap.mappingCylinderCylinderInclusion i) (a, t)) z =
      ((z.path t : B ^ ULift.{w} A) a) := by
  -- Read the cylinder-side computation rule for the descended map and then evaluate the boundary
  -- family at the chosen point `(t, a)` and mapping-path witness `z`.
  have hCylinder :
      (restrictionMappingCylinderDescSameUniverse (B := B) (i := i)).comp
          (ContinuousMap.mappingCylinderCylinderInclusion i) =
        (restrictionMappingPathBoundaryHomotopy (B := B) (i := i)).prodSwap := by
    simpa [restrictionMappingCylinderDescSameUniverse] using
      (ContinuousMap.mappingCylinderDesc_comp_cylinderInclusion
        (f₀ := restrictionMappingPathPointFamily (B := B) (i := i))
        (H := restrictionMappingPathBoundaryHomotopy (B := B) (i := i)))
  have hat :=
    congrArg
      (fun f :
        C(ULift.{w} A × I,
          B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A))) ↦
          f (a, t)) hCylinder
  -- Reduce the cylinder-side formula to the generic boundary-homotopy evaluation lemma.
  simpa using
    congrArg
      (fun f : B ^ MappingPathSpace ((mapSpaceRestriction i) : C(B ^ ULift.{w} X, B ^ ULift.{w} A)) ↦
        f z) hat

/-- Helper for Lemma 7.2.5: in one universe, a mapping-cylinder retract for `i` produces a
continuous path lifting function for the restriction map `B ^ X → B ^ A`. -/
theorem restrictionNonemptyContinuousPathLiftingFunctionSameUniverse {i : C(A, X)}
    (hi : IsCofibration.{u, u, max u w} i) :
    Nonempty (ContinuousPathLiftingFunction ((mapSpaceRestriction i) : C(B ^ X, B ^ A))) := by
  let A' := ULift.{w} A
  let X' := ULift.{w} X
  let j : C(A', X') := ContinuousMap.sameUniverseULiftMap i
  have hj : IsCofibration.{max u w, max u w, max u w} j := by
    change IsCofibration.{max u w, max u w, max u w}
      (ContinuousMap.sameUniverseULiftMap i)
    exact
      (@ContinuousMap.isCofibration_sameUniverseULiftMap_iff.{u, max u w, w}
        A X inferInstance inferInstance i).2 hi
  let hA' : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} A' := inferInstance
  let hX' : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} X' := inferInstance
  let hB : CompactlyGeneratedWeakHausdorffSpace.{w, w} B := inferInstance
  let hBLift : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} B := by
    simpa [max_comm, max_left_comm, max_assoc] using
      (@CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{w, u} B inferInstance hB)
  let hMapX : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ X') :=
    @CompactlyGenerated.mapSpaceCompactlyGeneratedWeakHausdorffSpace.{max u w, w}
      X' B inferInstance inferInstance hX' hBLift
  let hMapA : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ A') :=
    @CompactlyGenerated.mapSpaceCompactlyGeneratedWeakHausdorffSpace.{max u w, w}
      A' B inferInstance inferInstance hA' hBLift
  -- Reset the output-universe-sensitive instance cache to the original `B` universe after the
  -- explicit lifted instances above have been constructed.
  let _ : CompactlyGeneratedWeakHausdorffSpace.{w, w} B := hB
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ X') := hMapX
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ A') := hMapA
  let p : C(B ^ X', B ^ A') := mapSpaceRestriction j
  let Z : Type (max u w) := MappingPathSpace p
  let _ : CompactlyGeneratedWeakHausdorffSpace (A' × I) :=
    compactlyGeneratedWeakHausdorffSpaceProdUnitIntervalRight A'
  let _ : CompactlyGeneratedWeakHausdorffSpace (X' × I) :=
    compactlyGeneratedWeakHausdorffSpaceProdUnitIntervalRight X'
  let _ : CompactlyGeneratedWeakHausdorffSpace Z :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace p
  obtain ⟨r, hr⟩ :=
    (isCofibration_iff_exists_mappingCylinderRetract (i := j)).1 hj
  let descended : C(j.mappingCylinder, B ^ Z) :=
    restrictionMappingCylinderDescSameUniverse (B := B) (i := j)
  let retractFamily : C(X' × I, B ^ Z) := descended.comp r
  let transposed : C(Z, B ^ (X' × I)) :=
    mapSpaceTranspose (X' × I) Z B retractFamily
  let lift : C(Z, C(I, B ^ X')) := (mapSpaceProdToPathMap X' B).comp transposed
  let sLifted : ContinuousPathLiftingFunction p :=
    { toContinuousMap := lift
      source_eq := by
        intro z
        change MappingPathSpace
          ((mapSpaceRestriction j) : C(B ^ X', B ^ A')) at z
        -- Evaluate the retract on `X' × {0}` and read off the target-side descent formula.
        ext x
        have hx0 :=
          congrArg (fun f : C(X', j.mappingCylinder) ↦ f x) hr.endpoint
        have hx :
            r (x, 0) = (ContinuousMap.mappingCylinderTargetInclusion j) x := by
          simpa [ContinuousMap.mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hx0
        calc
          lift z 0 x = transposed z (x, 0) := by
            simpa [lift] using (mapSpaceProdToPathMap_apply X' B (transposed z) (0 : I) x)
          _ = retractFamily (x, 0) z := by
            simpa [transposed] using
              (mapSpaceTranspose_apply (X' × I) Z B retractFamily z (x, 0))
          _ = descended (r (x, 0)) z := rfl
          _ = descended ((ContinuousMap.mappingCylinderTargetInclusion j) x) z := by
            rw [hx]
          _ = (z.point : B ^ X') x := by
            simpa [descended, p] using
              restrictionMappingCylinderDescSameUniverse_target_apply (B := B) (i := j) x z
      proj_comp_eq := by
        intro z
        change MappingPathSpace
          ((mapSpaceRestriction j) : C(B ^ X', B ^ A')) at z
        -- Evaluate the retract on `A' × I` and read off the cylinder-side descent formula.
        ext t a
        have hat :=
          congrArg (fun f : C(A' × I, j.mappingCylinder) ↦ f (a, t)) hr.cylinder
        have ha :
            r (j a, t) = (ContinuousMap.mappingCylinderCylinderInclusion j) (a, t) := by
          simpa [ContinuousMap.mappingCylinderCylinderMap_apply, ContinuousMap.comp_apply] using hat
        calc
          ((p.comp (lift z)) t : B ^ A') a = (lift z t : B ^ X') (j a) := by
            simp [p, mapSpaceRestriction, ContinuousMap.comp_apply]
          _ = transposed z (j a, t) := by
            simpa [lift] using (mapSpaceProdToPathMap_apply X' B (transposed z) t (j a))
          _ = retractFamily (j a, t) z := by
            simpa [transposed] using
              (mapSpaceTranspose_apply (X' × I) Z B retractFamily z (j a, t))
          _ = descended (r (j a, t)) z := rfl
          _ = descended ((ContinuousMap.mappingCylinderCylinderInclusion j) (a, t)) z := by
            rw [ha]
          _ = ((z.path t : B ^ A') a) := by
            simpa [descended, p] using
              restrictionMappingCylinderDescSameUniverse_cylinder_apply (B := B) (i := j) a t z }
  obtain ⟨eX, eA, hsquare⟩ := restrictionMap_sameUniverseULiftMap_conj (B := B) (i := i)
  exact ⟨ContinuousPathLiftingFunction.ofConjugate eX eA hsquare sLifted⟩

end SameUniverse

/-- Helper for Lemma 7.2.5: postcomposing by `ULift.down` conjugates the restriction map with
codomain `ULift.{s} B` to the original restriction map with codomain `B`. -/
theorem restrictionMap_uliftCodomain_conj {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    ∃ eX : ((ULift.{s} B) ^ X) ≃ₜ (B ^ X),
      ∃ eA : ((ULift.{s} B) ^ A) ≃ₜ (B ^ A),
        let eXMap : C((ULift.{s} B) ^ X, B ^ X) := ⟨eX, eX.continuous_toFun⟩
        let eAMap : C((ULift.{s} B) ^ A, B ^ A) := ⟨eA, eA.continuous_toFun⟩
        eAMap.comp ((mapSpaceRestriction (B := ULift.{s} B) i) :
          C((ULift.{s} B) ^ X, (ULift.{s} B) ^ A)) =
          ((mapSpaceRestriction (B := B) i) : C(B ^ X, B ^ A)).comp eXMap := by
  let upB : C(B, ULift.{s} B) := ⟨ULift.up, continuous_uliftUp⟩
  let downB : C(ULift.{s} B, B) := ⟨ULift.down, continuous_uliftDown⟩
  let eXTo : C((ULift.{s} B) ^ X, B ^ X) :=
    mapSpacePostcomposition downB
  let eXInv : C(B ^ X, (ULift.{s} B) ^ X) :=
    mapSpacePostcomposition upB
  let eATo : C((ULift.{s} B) ^ A, B ^ A) :=
    mapSpacePostcomposition downB
  let eAInv : C(B ^ A, (ULift.{s} B) ^ A) :=
    mapSpacePostcomposition upB
  let eX : ((ULift.{s} B) ^ X) ≃ₜ (B ^ X) :=
    { toEquiv :=
        { toFun := eXTo
          invFun := eXInv
          left_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, downB, upB, mapSpacePostcomposition]
          right_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, downB, upB, mapSpacePostcomposition] }
      continuous_toFun := eXTo.continuous
      continuous_invFun := eXInv.continuous }
  let eA : ((ULift.{s} B) ^ A) ≃ₜ (B ^ A) :=
    { toEquiv :=
        { toFun := eATo
          invFun := eAInv
          left_inv := by
            intro f
            ext a
            simp [eATo, eAInv, downB, upB, mapSpacePostcomposition]
          right_inv := by
            intro f
            ext a
            simp [eATo, eAInv, downB, upB, mapSpacePostcomposition] }
      continuous_toFun := eATo.continuous
      continuous_invFun := eAInv.continuous }
  refine ⟨eX, eA, ?_⟩
  -- Evaluate both sides on an arbitrary map `f : (ULift B) ^ X` and point `a : A`; both compute
  -- to `ULift.down (f (i a))`.
  ext f a
  simp [eX, eA, eXTo, eATo, downB, mapSpaceRestriction, mapSpacePostcomposition,
    ContinuousMap.comp_apply]

/-- Helper for Lemma 7.2.5: the lifted restriction map is conjugate to the original restriction
map via the canonical `ULift` homeomorphisms on `A` and `X`. -/
theorem restrictionMap_commonUniverseULiftMap_conj {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B] :
    ∃ eX : (B ^ ULift.{u} X) ≃ₜ (B ^ X),
      ∃ eA : (B ^ ULift.{v} A) ≃ₜ (B ^ A),
        let eXMap : C(B ^ ULift.{u} X, B ^ X) := ⟨eX, eX.continuous_toFun⟩
        let eAMap : C(B ^ ULift.{v} A, B ^ A) := ⟨eA, eA.continuous_toFun⟩
        eAMap.comp ((mapSpaceRestriction (B := B) (ContinuousMap.commonUniverseULiftMap i)) :
          C(B ^ ULift.{u} X, B ^ ULift.{v} A)) =
          ((mapSpaceRestriction i) : C(B ^ X, B ^ A)).comp eXMap := by
  let _ : CompactlyGeneratedWeakHausdorffSpace (ULift.{u} X) := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace (ULift.{v} A) := inferInstance
  let upX : C(X, ULift.{u} X) := ⟨ULift.up, continuous_uliftUp⟩
  let downX : C(ULift.{u} X, X) := ⟨ULift.down, continuous_uliftDown⟩
  let upA : C(A, ULift.{v} A) := ⟨ULift.up, continuous_uliftUp⟩
  let downA : C(ULift.{v} A, A) := ⟨ULift.down, continuous_uliftDown⟩
  let eXTo : C(B ^ ULift.{u} X, B ^ X) := mapSpaceRestriction upX
  let eXInv : C(B ^ X, B ^ ULift.{u} X) := mapSpaceRestriction downX
  let eATo : C(B ^ ULift.{v} A, B ^ A) := mapSpaceRestriction upA
  let eAInv : C(B ^ A, B ^ ULift.{v} A) := mapSpaceRestriction downA
  let eX : (B ^ ULift.{u} X) ≃ₜ (B ^ X) :=
    { toEquiv :=
        { toFun := eXTo
          invFun := eXInv
          left_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, upX, downX, mapSpaceRestriction]
          right_inv := by
            intro f
            ext x
            simp [eXTo, eXInv, upX, downX, mapSpaceRestriction] }
      continuous_toFun := eXTo.continuous
      continuous_invFun := eXInv.continuous }
  let eA : (B ^ ULift.{v} A) ≃ₜ (B ^ A) :=
    { toEquiv :=
        { toFun := eATo
          invFun := eAInv
          left_inv := by
            intro f
            ext a
            simp [eATo, eAInv, upA, downA, mapSpaceRestriction]
          right_inv := by
            intro f
            ext a
            simp [eATo, eAInv, upA, downA, mapSpaceRestriction] }
      continuous_toFun := eATo.continuous
      continuous_invFun := eAInv.continuous }
  refine ⟨eX, eA, ?_⟩
  -- Evaluate both sides on an arbitrary map `f : B ^ ULift X` and point `a : A`; both compute to
  -- `f (ULift.up (i a))`.
  ext f a
  simp [eX, eA, eXTo, eATo, upX, upA, mapSpaceRestriction, ContinuousMap.commonUniverseULiftMap,
    ContinuousMap.comp_apply]

/-- Helper for Lemma 7.2.5: lifting `i` to a common universe for its source and target leaves the
restriction-path theorem in the same shape. -/
theorem restrictionNonemptyContinuousPathLiftingFunctionCommonUniverseULift {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (hi : IsCofibration.{u, v, max (max u v) w} i) :
    Nonempty
      (ContinuousPathLiftingFunction
        ((mapSpaceRestriction (B := B) (ContinuousMap.commonUniverseULiftMap i)) :
          C(B ^ ULift.{u} X, B ^ ULift.{v} A))) := by
  let A' := ULift.{v} A
  let X' := ULift.{u} X
  let j : C(A', X') := ContinuousMap.commonUniverseULiftMap i
  have hj : IsCofibration.{max u v, max u v, max (max u v) w} j :=
    (ContinuousMap.isCofibration_commonUniverseULiftMap_iff (i := i)).2 hi
  -- Apply the same-universe theorem to the lifted codomain, then descend the codomain `ULift`
  -- through the explicit restriction-map conjugation square.
  obtain ⟨sLifted⟩ :=
    restrictionNonemptyContinuousPathLiftingFunctionSameUniverse
      (A := A') (X := X') (B := ULift.{max u v} B) (i := j) hj
  obtain ⟨eX, eA, hsquare⟩ :=
    restrictionMap_uliftCodomain_conj
      (A := A') (X := X') (B := B) (i := j)
  exact ⟨ContinuousPathLiftingFunction.ofConjugate eX eA hsquare sLifted⟩

/-- Lemma 7.2.5: if `i : C(A, X)` is a cofibration and `B` is a space, then the restriction map
`B ^ X → B ^ A` given by precomposition with `i` has the covering homotopy property. This is the
source-faithful local formalization of the book's restriction-fibration claim, because the Chapter
7 class `IsFibration` also requires surjectivity. -/
theorem restriction_hasCoveringHomotopyProperty_of_isCofibration {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    (hi : IsCofibration.{u, v, max (max u v) w} i) :
    HasCoveringHomotopyProperty.{max v w, max u w, max (max u v) w}
      ((mapSpaceRestriction i) : C(B ^ X, B ^ A)) := by
  -- Route correction: the remaining blocker is the common-universe descent from the lifted
  -- restriction map back to the original one via a restriction-map conjugation square.
  have hpathLifted :
      Nonempty
        (ContinuousPathLiftingFunction
          ((mapSpaceRestriction (B := B) (ContinuousMap.commonUniverseULiftMap i)) :
            C(B ^ ULift.{u} X, B ^ ULift.{v} A))) :=
    restrictionNonemptyContinuousPathLiftingFunctionCommonUniverseULift (B := B) (i := i) hi
  obtain ⟨sLifted⟩ := hpathLifted
  obtain ⟨eX, eA, hsquare⟩ := restrictionMap_commonUniverseULiftMap_conj (B := B) (i := i)
  let p : C(B ^ X, B ^ A) := mapSpaceRestriction i
  have hpath :
      Nonempty (ContinuousPathLiftingFunction p) := by
    -- Descend the source-side `ULift` along the restriction-map conjugation square.
    exact ⟨ContinuousPathLiftingFunction.ofConjugate eX eA hsquare sLifted⟩
  let hB0 : CompactlyGeneratedWeakHausdorffSpace.{w, w} B := inferInstance
  let hX : CompactlyGeneratedWeakHausdorffSpace.{v, max v w} X :=
    CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := X)
  let hBX : CompactlyGeneratedWeakHausdorffSpace.{w, max v w} B := by
    simpa [max_comm] using
      (@CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{w, v}
        B inferInstance hB0)
  let hA : CompactlyGeneratedWeakHausdorffSpace.{u, max u w} A :=
    CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift (X := A)
  let hBA : CompactlyGeneratedWeakHausdorffSpace.{w, max u w} B := by
    simpa [max_comm] using
      (@CompactlyGenerated.compactlyGeneratedWeakHausdorffSpaceLift.{w, u}
        B inferInstance hB0)
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max v w, max v w} (B ^ X) :=
    @CompactlyGenerated.mapSpaceCompactlyGeneratedWeakHausdorffSpace.{v, w}
      X B inferInstance inferInstance hX hBX
  let _ : CompactlyGeneratedWeakHausdorffSpace.{max u w, max u w} (B ^ A) :=
    @CompactlyGenerated.mapSpaceCompactlyGeneratedWeakHausdorffSpace.{u, w}
      A B inferInstance inferInstance hA hBA
  -- Criterion 7.2.3 identifies CHP with existence of a continuous path lifting function.
  have hchp :
      HasCoveringHomotopyProperty.{max v w, max u w, max (max u v) w} p :=
    (HasCoveringHomotopyProperty.iff_nonempty_continuousPathLiftingFunction p).2 hpath
  simpa [p] using hchp

/-- The restriction map along a cofibration also carries the induced covering-homotopy property
instance. -/
instance restrictionInstHasCoveringHomotopyProperty {i : C(A, X)}
    [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X]
    [CompactlyGeneratedWeakHausdorffSpace B]
    [hi : Fact (IsCofibration.{u, v, max (max u v) w} i)] :
    HasCoveringHomotopyProperty.{max v w, max u w, max (max u v) w}
      ((mapSpaceRestriction i) : C(B ^ X, B ^ A)) :=
  restriction_hasCoveringHomotopyProperty_of_isCofibration hi.1
