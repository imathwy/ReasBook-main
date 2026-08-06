import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2

-- Semantic recall via `lean_leansearch`: the verified hits were only the abstract categorical
-- `Adjunction.unit`/`Adjunction.counit` API, so this file records the source-faithful explicit
-- based-space maps using the local models `reducedSuspension` and `Path`.

open CategoryTheory
open scoped unitInterval

noncomputable section

universe u w

/-- Helper for Definition 8.7.1: the `k`-ification of any topology is compactly generated. -/
private theorem uCompactlyGeneratedSpace_compactlyGenerated
    (X : Type w) [TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{u} X (TopologicalSpace.compactlyGenerated.{u, w} X) := by
  -- Present the replacement topology as the standard coinduced topology on compact probes.
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun x ↦ x.1.2 x.2
  have hf :
      @Continuous ((Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst)) X
        instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{u, _, _}
    ((Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst)) X instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Definition 8.7.1: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators for the coinduced topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Definition 8.7.1: a continuous map from a compactly generated domain remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousToCompactlyGeneratedOfContinuous
    {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    {Y : Type w} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    @Continuous X Y ‹TopologicalSpace X› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  -- Test continuity against compact Hausdorff probes into the compactly generated domain.
  exact continuous_from_uCompactlyGeneratedSpace
    (tY := TopologicalSpace.compactlyGenerated.{u, w} Y) f fun S g ↦ by
      simpa [Function.comp] using
        (continuousCompHausToCompactlyGenerated (Y := Y) (f := f ∘ g)
          (hf := hf.comp g.continuous))

/-- Helper for Definition 8.7.1: products with the compact interval preserve compact generation. -/
private theorem uCompactlyGeneratedSpaceProdUnitInterval
    (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (X × I) := by
  -- Prove continuity on `X × I` by currying into the compact-open space `C(I, Y)`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Y tY f hf
  let F : X → C(I, Y) := fun x ↦
    ⟨fun t ↦ f (x, t), by
      let gx : C(ULift.{u} I, X × I) :=
        ⟨fun t ↦ (x, t.down), (continuous_const.prodMk continuous_uliftDown)⟩
      have hsec : Continuous fun t : ULift.{u} I ↦ f (x, t.down) := by
        simpa [gx] using hf (CompHaus.of (ULift.{u} I)) gx
      simpa using hsec.comp continuous_uliftUp⟩
  have hF : Continuous F := by
    -- Continuity into `C(I, Y)` is checked after precomposing with compact Hausdorff sources.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro S g
    apply ContinuousMap.continuous_of_continuous_uncurry
    let h : C(S × I, X × I) :=
      ⟨fun p ↦ (g p.1, p.2), (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
    simpa [F, h, Function.comp_def] using hf (CompHaus.of (S × I)) h
  -- Uncurrying the continuous family `x ↦ (t ↦ f (x,t))` recovers `f`.
  simpa [F] using ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩

/-- Helper for Definition 8.7.1: the loop carrier uses the compactly generated replacement of the
raw path topology. -/
private abbrev loopPathTopologicalSpace (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (Path X.point X.point) :=
  TopologicalSpace.compactlyGenerated.{u, w} (Path X.point X.point)

/-- The path space `Path X.point X.point` carries the compactly generated replacement of its
compact-open topology. -/
private theorem loopPathUCompactlyGeneratedSpace (X : PointedCompactlyGenerated.{u, w}) :
    @UCompactlyGeneratedSpace.{u} (Path X.point X.point) (loopPathTopologicalSpace X) := by
  -- The chosen loop topology is literally the `k`-ification of the raw path topology.
  simpa [loopPathTopologicalSpace] using
    (uCompactlyGeneratedSpace_compactlyGenerated (X := Path X.point X.point))

/-- The pointed compactly generated loop space of a based compactly generated space. -/
abbrev loopPointedSpace (X : PointedCompactlyGenerated.{u, w}) :
    PointedCompactlyGenerated.{u, w} :=
  let _ : TopologicalSpace (Path X.point X.point) := loopPathTopologicalSpace X
  let _ : UCompactlyGeneratedSpace.{u} (Path X.point X.point) := loopPathUCompactlyGeneratedSpace X
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (Path X.point X.point))
    (Path.refl X.point)

prefix:max "Ω " => loopPointedSpace

/-- A point of the pointed loop space `Ω X` evaluates at `t : I` as the corresponding loop in
`X`. -/
instance loopPointedSpaceCoeFun (X : PointedCompactlyGenerated.{u, w}) :
    CoeFun (Ω X).toCompactlyGenerated (fun _ ↦ I → X.toCompactlyGenerated) where
  coe χ := (show Path X.point X.point from χ)

/-- The distinguished basepoint of `Ω X` is the constant loop at `X.point`. -/
@[simp] theorem loopPointedSpace_point (X : PointedCompactlyGenerated.{u, w}) :
    (Ω X).point = Path.refl X.point := rfl

/-- The meridian through `x` starts at the suspension basepoint. -/
theorem suspensionLoopAdjunctionUnitPath_source
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    reducedSuspensionMk X (x, (0 : I)) = (Σ X).point := by
  simp

/-- The meridian through `x` ends at the suspension basepoint. -/
theorem suspensionLoopAdjunctionUnitPath_target
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    reducedSuspensionMk X (x, (1 : I)) = (Σ X).point := by
  simp

/-- The loop in `ΣX` traced by the suspension meridian through `x`. -/
def suspensionLoopAdjunctionUnitPath (X : PointedCompactlyGenerated.{u, w})
    (x : X.toCompactlyGenerated) :
    Path (Σ X).point (Σ X).point where
  toContinuousMap :=
    { toFun := fun t ↦ reducedSuspensionMk X (x, t)
      continuous_toFun := by
        simpa using
          (continuous_reducedSuspensionMk_meridian X x :
            Continuous
              (show I → (Σ X).toCompactlyGenerated from
                fun t : I ↦ reducedSuspensionMk X (x, t))) }
  source' := suspensionLoopAdjunctionUnitPath_source X x
  target' := suspensionLoopAdjunctionUnitPath_target X x

/-- The unit meridian loop evaluates to the suspension class `x ∧ t`. -/
@[simp] theorem suspensionLoopAdjunctionUnitPath_apply
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) (t : I) :
    suspensionLoopAdjunctionUnitPath X x t = reducedSuspensionMk X (x, t) := rfl

/-- The unit of the suspension-loop adjunction is continuous as a map into the loop space. -/
private theorem suspensionLoopAdjunctionUnitContinuous
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous fun x : X.toCompactlyGenerated ↦
      (show (Ω (Σ X)).toCompactlyGenerated from suspensionLoopAdjunctionUnitPath X x) := by
  -- First prove continuity for the raw path topology via the uncurry criterion.
  have hraw : Continuous fun x : X.toCompactlyGenerated ↦ suspensionLoopAdjunctionUnitPath X x := by
    rw [← Path.continuous_uncurry_iff]
    simpa [Function.uncurry] using
      (continuous_reducedSuspensionMk X :
        Continuous fun p : X.toCompactlyGenerated × I ↦ reducedSuspensionMk X p)
  -- Then upgrade the codomain to the chosen compactly generated loop topology.
  exact continuousToCompactlyGeneratedOfContinuous (Y := Path (Σ X).point (Σ X).point) hraw

/-- The continuous map underlying the unit of the suspension-loop adjunction. -/
private def suspensionLoopAdjunctionUnitContinuousMap (X : PointedCompactlyGenerated.{u, w}) :
    C(X.toCompactlyGenerated, (Ω (Σ X)).toCompactlyGenerated) :=
  ⟨suspensionLoopAdjunctionUnitPath X, suspensionLoopAdjunctionUnitContinuous X⟩

/-- The unit sends the basepoint of `X` to the constant loop at the suspension basepoint. -/
private theorem suspensionLoopAdjunctionUnitContinuousMap_map_point
    (X : PointedCompactlyGenerated.{u, w}) :
    suspensionLoopAdjunctionUnitContinuousMap X X.point =
      Path.refl (Σ X).point := by
  -- Two loops with the same pointwise values are equal by path extensionality.
  change suspensionLoopAdjunctionUnitPath X X.point = Path.refl (Σ X).point
  ext t
  change reducedSuspensionMk X (X.point, t) = (Σ X).point
  simp

/-- The unit continuous map preserves the distinguished basepoints. -/
private theorem suspensionLoopAdjunctionUnit_w (X : PointedCompactlyGenerated.{u, w}) :
    CategoryStruct.comp X.hom
        (CompactlyGenerated.ofHom (suspensionLoopAdjunctionUnitContinuousMap X)) =
      (Ω (Σ X)).hom := by
  -- Both based maps send the unique point of the source point object to the constant loop.
  ext x
  cases x
  exact suspensionLoopAdjunctionUnitContinuousMap_map_point X

/-- The unit map appearing in Definition 8.7.1 sends `x` to the loop `t ↦ x ∧ t` in `ΣX`. -/
def suspensionLoopAdjunctionUnit (X : PointedCompactlyGenerated.{u, w}) :
    X ⟶ Ω (Σ X) :=
  let _ : TopologicalSpace (Path (Σ X).point (Σ X).point) := loopPathTopologicalSpace (Σ X)
  let _ : UCompactlyGeneratedSpace.{u} (Path (Σ X).point (Σ X).point) :=
    loopPathUCompactlyGeneratedSpace (Σ X)
  Under.homMk
    (CompactlyGenerated.ofHom (suspensionLoopAdjunctionUnitContinuousMap X))
    (suspensionLoopAdjunctionUnit_w X)

/-- The underlying based map of `suspensionLoopAdjunctionUnit X` sends `x` to its meridian loop. -/
@[simp] theorem suspensionLoopAdjunctionUnit_hom_apply
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    PointedCompactlyGenerated.Hom.hom (suspensionLoopAdjunctionUnit X) x =
      suspensionLoopAdjunctionUnitPath X x := by
  -- The underlying map is the unit continuous map evaluated at `x`.
  change suspensionLoopAdjunctionUnitContinuousMap X x = suspensionLoopAdjunctionUnitPath X x
  rfl

/-- Evaluating the unit map at `t : I` returns the suspension class `x ∧ t`. -/
@[simp] theorem suspensionLoopAdjunctionUnit_hom_apply_apply
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) (t : I) :
    PointedCompactlyGenerated.Hom.hom (suspensionLoopAdjunctionUnit X) x t =
      reducedSuspensionMk X (x, t) := by
  -- Evaluate the unit map first on `x`, then along the path parameter `t`.
  rw [suspensionLoopAdjunctionUnit_hom_apply]
  rfl

/-- The unit sends the basepoint of `X` to the constant loop at the suspension basepoint. -/
@[simp] theorem suspensionLoopAdjunctionUnit_hom_apply_point
    (X : PointedCompactlyGenerated.{u, w}) :
    PointedCompactlyGenerated.Hom.hom (suspensionLoopAdjunctionUnit X) X.point =
      Path.refl (Σ X).point :=
by
  simpa [suspensionLoopAdjunctionUnit] using
    suspensionLoopAdjunctionUnitContinuousMap_map_point X

/-- The raw evaluation map `(χ, t) ↦ χ(t)` used to define the counit `Σ ΩX ⟶ X`. -/
private def suspensionLoopAdjunctionCounitRaw (X : PointedCompactlyGenerated.{u, w}) :
    (Ω X).toCompactlyGenerated × I → X.toCompactlyGenerated :=
  fun p ↦ p.1 p.2

/-- Definitional-equality pin: the counit is defined on the compactly generated topology carried by
`(Σ (Ω X)).toCompactlyGenerated`, not the raw quotient topology on `reducedSuspensionType (Ω X)`.
-/
private instance counitReducedSuspensionTopologicalSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedSuspensionType (Ω X)) :=
  inferInstanceAs (TopologicalSpace ((Σ (Ω X)).toCompactlyGenerated))

private instance counitReducedSuspensionUCompactlyGeneratedSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    UCompactlyGeneratedSpace.{u} ((Σ (Ω X)).toCompactlyGenerated) :=
by
  -- Reuse the bundled compact-generation instance carried by `(Σ (Ω X)).toCompactlyGenerated`.
  let Y : CompactlyGenerated.{u, w} := (Σ (Ω X)).toCompactlyGenerated
  exact Y.is_compactly_generated

/-- The raw counit formula is continuous on `ΩX × I`. -/
private theorem suspensionLoopAdjunctionCounitRaw_continuous
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous (suspensionLoopAdjunctionCounitRaw X) := by
  -- Forget the kified loop topology back to the raw path topology, then evaluate.
  have hforget :
      Continuous fun χ : (Ω X).toCompactlyGenerated ↦
        (show Path X.point X.point from χ) := by
    let f : Path X.point X.point → Path X.point X.point := id
    have hraw :
        @Continuous (Path X.point X.point) (Path X.point X.point)
          (loopPathTopologicalSpace X) inferInstance f := by
      refine continuous_from_compactlyGenerated f ?_
      intro S g
      simpa [f, Function.comp_def] using g.continuous
    simpa [f, loopPathTopologicalSpace, loopPointedSpace] using hraw
  have hpair :
      Continuous fun p : (Ω X).toCompactlyGenerated × I ↦
        ((show Path X.point X.point from p.1), p.2) := by
    exact (hforget.comp continuous_fst).prodMk continuous_snd
  simpa [suspensionLoopAdjunctionCounitRaw] using
    (continuous_eval.comp hpair :
      Continuous fun p : (Ω X).toCompactlyGenerated × I ↦
        (show Path X.point X.point from p.1) p.2)

/-- Helper for Definition 8.7.1: the raw counit formula sends every collapsed representative in
`Ω X × I` to the basepoint of `X`. -/
private theorem suspensionLoopAdjunctionCounitRaw_eq_point_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p : (Ω X).toCompactlyGenerated × I}
    (hp : p ∈ reducedSuspensionCollapsedSet (Ω X)) :
    suspensionLoopAdjunctionCounitRaw X p = X.point := by
  rcases p with ⟨χ, t⟩
  -- Split along the three pieces of the collapsed subset.
  rcases hp with hχ | ht | ht
  · subst hχ
    simpa [suspensionLoopAdjunctionCounitRaw, Path.refl] using
      (ContinuousMap.const_apply X.point t)
  · subst ht
    simpa [suspensionLoopAdjunctionCounitRaw] using Path.source χ
  · subst ht
    simpa [suspensionLoopAdjunctionCounitRaw] using Path.target χ

/-- The raw counit formula respects the suspension quotient relation on `ΩX × I`. -/
private theorem suspensionLoopAdjunctionCounitRaw_respects
    (X : PointedCompactlyGenerated.{u, w}) (p q : (Ω X).toCompactlyGenerated × I)
    (hpq : (reducedSuspensionSetoid (Ω X)).r p q) :
    suspensionLoopAdjunctionCounitRaw X p = suspensionLoopAdjunctionCounitRaw X q := by
  -- The setoid identifies equal representatives and collapses the same distinguished subset.
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (suspensionLoopAdjunctionCounitRaw_eq_point_of_memCollapsedSet X hp).trans
        (suspensionLoopAdjunctionCounitRaw_eq_point_of_memCollapsedSet X hq).symm

/-- The quotient lift of the raw counit formula on `Σ ΩX`. -/
private def suspensionLoopAdjunctionCounitFun (X : PointedCompactlyGenerated.{u, w}) :
    (Σ (Ω X)).toCompactlyGenerated → X.toCompactlyGenerated :=
  Quotient.lift
    (suspensionLoopAdjunctionCounitRaw X)
    (suspensionLoopAdjunctionCounitRaw_respects X)

/-- Helper for Definition 8.7.1: the raw quotient topology on `reducedSuspensionType (Ω X)` is
already compactly generated. -/
private theorem loopReducedSuspensionTypeQuot_eq_kTopologicalSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionTypeQuotTopologicalSpace (Ω X) =
      reducedSuspensionTypeKTopologicalSpace (Ω X) := by
  let _ : TopologicalSpace (reducedSuspensionType (Ω X)) :=
    reducedSuspensionTypeQuotTopologicalSpace (Ω X)
  let _ : UCompactlyGeneratedSpace.{u} (reducedSuspensionType (Ω X)) := by
    let X' : Type w := (Ω X).toCompactlyGenerated
    let _ : TopologicalSpace X' := inferInstanceAs (TopologicalSpace ((Ω X).toCompactlyGenerated))
    let _ : UCompactlyGeneratedSpace.{u} X' :=
      inferInstanceAs (UCompactlyGeneratedSpace ((Ω X).toCompactlyGenerated))
    have hprod : UCompactlyGeneratedSpace.{u} (X' × I) :=
      uCompactlyGeneratedSpaceProdUnitInterval (X := X')
    let _ : UCompactlyGeneratedSpace.{u} (X' × I) := hprod
    infer_instance
  -- The raw quotient topology already equals its compactly generated replacement.
  simpa [reducedSuspensionTypeKTopologicalSpace] using
    (eq_compactlyGenerated (X := reducedSuspensionType (Ω X)))

/-- The quotient lift of the raw counit formula is continuous on `Σ ΩX`. -/
private theorem suspensionLoopAdjunctionCounitFun_continuous
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous (suspensionLoopAdjunctionCounitFun X) := by
  -- First descend the raw evaluation map along the quotient presentation of `Σ (Ω X)`.
  let _ : TopologicalSpace ((Σ (Ω X)).toCompactlyGenerated) :=
    reducedSuspensionTypeQuotTopologicalSpace (Ω X)
  have hraw :
      @Continuous ((Σ (Ω X)).toCompactlyGenerated) X.toCompactlyGenerated
        (reducedSuspensionTypeQuotTopologicalSpace (Ω X))
        inferInstance (suspensionLoopAdjunctionCounitFun X) := by
    simpa [suspensionLoopAdjunctionCounitFun] using
      (suspensionLoopAdjunctionCounitRaw_continuous X).quotient_lift
        (suspensionLoopAdjunctionCounitRaw_respects X)
  -- Replace the public suspension topology by the named `k`-ification, then rewrite back to raw.
  change
    @Continuous ((Σ (Ω X)).toCompactlyGenerated) X.toCompactlyGenerated
      (reducedSuspensionTypeKTopologicalSpace (Ω X))
      inferInstance (suspensionLoopAdjunctionCounitFun X)
  rw [← loopReducedSuspensionTypeQuot_eq_kTopologicalSpace X]
  exact hraw

/-- The continuous map underlying the counit `Σ ΩX ⟶ X`. -/
private def suspensionLoopAdjunctionCounitContinuousMap (X : PointedCompactlyGenerated.{u, w}) :
    C((Σ (Ω X)).toCompactlyGenerated, X.toCompactlyGenerated) :=
  { toFun := suspensionLoopAdjunctionCounitFun X
    continuous_toFun := suspensionLoopAdjunctionCounitFun_continuous X }

/-- The counit evaluates the suspension class of `(χ, t)` to `χ(t)`. -/
@[simp] private theorem suspensionLoopAdjunctionCounitContinuousMap_apply_mk
    (X : PointedCompactlyGenerated.{u, w})
    (χ : Path X.point X.point) (t : I) :
    suspensionLoopAdjunctionCounitContinuousMap X
        (reducedSuspensionMk (Ω X) (χ, t)) =
      χ t := by
  -- The quotient lift computes on representatives by definition.
  rfl

/-- The counit sends the suspension basepoint of `Σ ΩX` to the basepoint of `X`. -/
private theorem suspensionLoopAdjunctionCounitContinuousMap_map_point
    (X : PointedCompactlyGenerated.{u, w}) :
    suspensionLoopAdjunctionCounitContinuousMap X
        (reducedSuspensionPoint (Ω X)) =
      X.point := by
  -- Evaluate the representative `(Path.refl X.point, 0)` of the suspension basepoint.
  simpa [reducedSuspensionPoint, loopPointedSpace_point] using
    suspensionLoopAdjunctionCounitContinuousMap_apply_mk X (Path.refl X.point) (0 : I)

/-- The counit continuous map preserves the distinguished basepoints. -/
private theorem suspensionLoopAdjunctionCounit_w (X : PointedCompactlyGenerated.{u, w}) :
    CategoryStruct.comp (Σ (Ω X)).hom
        (ConcreteCategory.ofHom (suspensionLoopAdjunctionCounitContinuousMap X)) =
      X.hom := by
  -- Both maps send the unique point of the source point object to `X.point`.
  ext x
  cases x
  simpa using suspensionLoopAdjunctionCounitContinuousMap_map_point X

/-- Definition 8.7.1 (2): the counit `ε : Σ Ω X ⟶ X` of the suspension-loop adjunction sends
the suspension class `χ ∧ t` to the value `χ(t)`. -/
def suspensionLoopAdjunctionCounit (X : PointedCompactlyGenerated.{u, w}) :
    Σ (Ω X) ⟶ X :=
  Under.homMk
    (ConcreteCategory.ofHom (suspensionLoopAdjunctionCounitContinuousMap X))
    (suspensionLoopAdjunctionCounit_w X)

/-- The underlying based map of `suspensionLoopAdjunctionCounit X` evaluates `χ ∧ t` to `χ(t)`. -/
@[simp] theorem suspensionLoopAdjunctionCounit_hom_apply_mk
    (X : PointedCompactlyGenerated.{u, w})
    (χ : Path X.point X.point) (t : I) :
    PointedCompactlyGenerated.Hom.hom (suspensionLoopAdjunctionCounit X)
        (reducedSuspensionMk (Ω X) (χ, t)) =
      χ t := by
  simpa [suspensionLoopAdjunctionCounit] using
    suspensionLoopAdjunctionCounitContinuousMap_apply_mk X χ t

/-- The counit sends the suspension basepoint of `Σ ΩX` to the basepoint of `X`. -/
@[simp] theorem suspensionLoopAdjunctionCounit_hom_apply_point
    (X : PointedCompactlyGenerated.{u, w}) :
    PointedCompactlyGenerated.Hom.hom (suspensionLoopAdjunctionCounit X)
        (reducedSuspensionPoint (Ω X)) =
      X.point := by
  simpa [suspensionLoopAdjunctionCounit] using
    suspensionLoopAdjunctionCounitContinuousMap_map_point X
