import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_17
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Observation_8_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_7_1

open CategoryTheory
open PointedCompactlyGenerated
open ContinuousMapZero
open scoped ContinuousMapZero HomotopyClasses unitInterval

-- `lean_leansearch` was unavailable in this environment. Using the Chapter 5/8 source-facing
-- local API instead, the correct owner for `F(Σ X, Y)` and `F(X, Ω Y)` in pointed compactly
-- generated spaces is the based subspace of the compactly generated mapping space.

noncomputable section

universe u v w s z r t

namespace PointedCompactlyGenerated

/-- Helper for Adjunction 8.2.6: the source-facing owner `F(X, Y)` is the based subspace of the
compactly generated mapping space `Y ^ X`. -/
abbrev basedCompactlyGeneratedMappingSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :=
  { f : CompactlyGenerated.MapSpace X.toCompactlyGenerated Y.toCompactlyGenerated //
      ((f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point = Y.point) }

namespace basedCompactlyGeneratedMappingSpace

variable {X : PointedCompactlyGenerated.{u, w}} {Y : PointedCompactlyGenerated.{v, w}}

private instance : Coe
    (basedCompactlyGeneratedMappingSpace X Y)
    (CompactlyGenerated.MapSpace X.toCompactlyGenerated Y.toCompactlyGenerated) := ⟨Subtype.val⟩

private instance : Coe
    (basedCompactlyGeneratedMappingSpace X Y)
    C(X.toCompactlyGenerated, Y.toCompactlyGenerated) := ⟨fun f ↦ f.1⟩

private instance : CoeFun (basedCompactlyGeneratedMappingSpace X Y)
    (fun _ ↦ X.toCompactlyGenerated → Y.toCompactlyGenerated) := ⟨fun f ↦ (f : C(_, _))⟩

/-- A continuous based map defines a point of the compactly generated based mapping space. -/
private abbrev ofContinuousMap (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))
    (hf : f X.point = Y.point) :
    basedCompactlyGeneratedMappingSpace X Y :=
  ⟨CompactlyGenerated.MapSpace.ofContinuousMap f, hf⟩

@[simp] private theorem ofContinuousMap_apply
    (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))
    (hf : f X.point = Y.point) (x : X.toCompactlyGenerated) :
    ofContinuousMap f hf x = f x := rfl

@[simp] private theorem map_point (f : basedCompactlyGeneratedMappingSpace X Y) :
    (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point = Y.point := f.2

private instance : Zero (basedCompactlyGeneratedMappingSpace X Y) := ⟨
  ofContinuousMap (ContinuousMap.const X.toCompactlyGenerated Y.point) rfl
⟩

@[simp] private theorem zero_apply (x : X.toCompactlyGenerated) :
    (0 : basedCompactlyGeneratedMappingSpace X Y) x = Y.point := rfl

@[ext] private theorem ext (f g : basedCompactlyGeneratedMappingSpace X Y)
    (h : ∀ x : X.toCompactlyGenerated, f x = g x) : f = g := by
  apply Subtype.ext
  exact CompactlyGenerated.MapSpace.ext _ _ h

end basedCompactlyGeneratedMappingSpace

end PointedCompactlyGenerated

/-- Helper for Adjunction 8.2.6: forgetting the `k`-ification identifies a point of
`F(X, Y)` with the corresponding raw based map. -/
private def basedCompactlyGeneratedMappingSpaceToBasedMappingSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    PointedCompactlyGenerated.basedCompactlyGeneratedMappingSpace X Y →
      basedMappingSpace X Y
  | f =>
      { toContinuousMap := (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))
        map_zero' := by
          change (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point = Y.point
          exact PointedCompactlyGenerated.basedCompactlyGeneratedMappingSpace.map_point f }

/-- Helper for Adjunction 8.2.6: a raw based map determines the corresponding point of the
compactly generated based mapping space `F(X, Y)`. -/
private def basedMappingSpaceToBasedCompactlyGeneratedMappingSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace X Y →
      PointedCompactlyGenerated.basedCompactlyGeneratedMappingSpace X Y
  | f =>
      PointedCompactlyGenerated.basedCompactlyGeneratedMappingSpace.ofContinuousMap
        (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) <| by
          simpa using f.map_zero'

/-- Helper for Adjunction 8.2.6: products with `I` preserve compact generation for the source
spaces used in the suspension quotient presentation. -/
private theorem uCompactlyGeneratedSpaceProdUnitInterval
    (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (X × I) := by
  -- Prove continuity on `X × I` by currying into the compact-open space `C(I, Y)`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  let F : X → C(I, Z) := fun x ↦
    ⟨fun t ↦ f (x, t), by
      let gx : C(ULift.{u} I, X × I) :=
        ⟨fun t ↦ (x, t.down), (continuous_const.prodMk continuous_uliftDown)⟩
      have hsec : Continuous fun t : ULift.{u} I ↦ f (x, t.down) := by
        simpa [gx] using hf (CompHaus.of (ULift.{u} I)) gx
      simpa using hsec.comp continuous_uliftUp⟩
  have hF : Continuous F := by
    -- Continuity into `C(I, Z)` is checked after precomposing with compact Hausdorff probes.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro S g
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    let h : C(S × I, X × I) :=
      ⟨fun p ↦ (g p.1, p.2), (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
    simpa [F, h, Function.comp_def] using hf (CompHaus.of (S × I)) h
  -- Uncurrying the continuous family `x ↦ (t ↦ f (x, t))` recovers the original map.
  simpa [F] using ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩

/-- Helper for Adjunction 8.2.6: products with a compact Hausdorff factor preserve compact
generation on the remaining source variable. -/
private theorem uCompactlyGeneratedSpaceProdCompHaus
    (S : Type w) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{max u w} (S × X) := by
  let _ : LocallyCompactSpace S := inferInstance
  -- As in the `I`-product case, prove continuity on `S × X` by currying into `C(S, Z)`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  let F : X → C(S, Z) := fun x ↦
    ⟨fun s ↦ f (s, x), by
      let gx : C(ULift.{max u w} S, S × X) :=
        ⟨fun s ↦ (s.down, x), continuous_uliftDown.prodMk continuous_const⟩
      have hsec : Continuous fun s : ULift.{max u w} S ↦ f (s.down, x) := by
        simpa [gx] using hf (CompHaus.of (ULift.{max u w} S)) gx
      simpa using hsec.comp continuous_uliftUp⟩
  have hF : Continuous F := by
    -- Compact probes into `X` reduce continuity of `F` to joint continuity on `T × S`.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro T g
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    let h : C(T × S, S × X) :=
      ⟨fun p ↦ (p.2, g p.1), continuous_snd.prodMk (g.continuous.comp continuous_fst)⟩
    simpa [F, h, Function.uncurry, Function.comp_def] using hf (CompHaus.of (T × S)) h
  have hUncurry : Continuous fun xs : X × S ↦ f (xs.2, xs.1) := by
    -- Uncurrying the continuous family `x ↦ (s ↦ f (s, x))` gives continuity on `X × S`.
    simpa [F, Function.uncurry] using ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩
  -- Swap back to the requested source order `S × X`.
  simpa [Function.comp_def] using hUncurry.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Adjunction 8.2.6: the chosen loop-space carrier uses the compactly generated
replacement of the raw path topology. -/
private abbrev loopPathTopologicalSpaceAdj
    (Y : PointedCompactlyGenerated.{v, w}) :
    TopologicalSpace (Path Y.point Y.point) :=
  TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point)

/-- Helper for Adjunction 8.2.6: the public loop space `Ω Y` carries the `v`-level compactly
generated replacement of the raw path topology. -/
private theorem loopPointedSpaceTopology_eq
    (Y : PointedCompactlyGenerated.{v, w}) :
    (Ω Y).toCompactlyGenerated.toTop.str =
      TopologicalSpace.compactlyGenerated.{v, w} (Path Y.point Y.point) := by
  -- Unfolding `Ω Y` shows that its bundled topology is exactly the `v`-level kification.
  rfl

/-- Helper for Adjunction 8.2.6: the identity from the chosen loop-space topology to the raw path
topology is continuous. -/
private theorem continuousLoopPointedSpaceForget
    (Y : PointedCompactlyGenerated.{v, w}) :
    Continuous fun χ : (Ω Y).toCompactlyGenerated ↦
      (show Path Y.point Y.point from χ) := by
  let f : Path Y.point Y.point → Path Y.point Y.point := id
  -- Test continuity from the compactly generated loop topology against compact Hausdorff probes.
  have hraw :
      @Continuous (Path Y.point Y.point) (Path Y.point Y.point)
        (loopPathTopologicalSpaceAdj Y)
        inferInstance f := by
    refine continuous_from_compactlyGenerated f ?_
    intro S g
    simpa [f, Function.comp_def] using g.continuous
  simpa [f, loopPathTopologicalSpaceAdj, loopPointedSpace] using hraw

/-- Helper for Adjunction 8.2.6: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type s} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{s, w} Z) f := by
  let F : (Σ (j : (S : CompHaus.{s}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{s}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators defining the compactly generated
  -- topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{s}) × C(S, Z),
        @Continuous j.fst Z inferInstance (TopologicalSpace.compactlyGenerated.{s, w} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Adjunction 8.2.6: the `k`-ification of any topology is compactly generated for the
chosen probe universe. -/
private theorem uCompactlyGeneratedSpaceCompGeneratedAux
    (X : Type w) [TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{r} X (TopologicalSpace.compactlyGenerated.{r, w} X) := by
  -- Present the chosen `k`-ification as the standard coinduced compact-probe topology.
  let f : (Σ (i : (S : CompHaus.{r}) × C(S, X)), i.fst) → X := fun x ↦ x.1.2 x.2
  have hf :
      @Continuous ((Σ (i : (S : CompHaus.{r}) × C(S, X)), i.fst)) X
        instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{r, _, _}
    ((Σ (i : (S : CompHaus.{r}) × C(S, X)), i.fst)) X instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Adjunction 8.2.6: compact generation lifts from `s`-small probes to
`max s z`-small probes on the same carrier. -/
private theorem uCompactlyGeneratedSpaceLiftAux
    (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{r} X] :
    UCompactlyGeneratedSpace.{max r t} X := by
  -- Reindex each larger compact test along `ULift` and pull the closedness test back down.
  refine uCompactlyGeneratedSpace_of_isClosed fun t ht ↦ ?_
  refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  let g : ULift.{t} S → X := f ∘ ULift.down
  have hg : Continuous g := hf.comp continuous_uliftDown
  simpa [g, Set.preimage_comp, Function.comp] using
    (ht (CompHaus.of (ULift.{t} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- Helper for Adjunction 8.2.6: a continuous map from an `r`-compactly generated source remains
continuous after replacing the codomain by the `r`-level compactly generated topology. -/
private theorem continuousToCompactlyGeneratedOfContinuousAux
    {A : Type u} [TopologicalSpace A] [UCompactlyGeneratedSpace.{r} A]
    {Z : Type w} [TopologicalSpace Z] {f : A → Z} (hf : Continuous f) :
    @Continuous A Z ‹TopologicalSpace A› (TopologicalSpace.compactlyGenerated.{r, w} Z) f := by
  exact
    @continuous_from_uCompactlyGeneratedSpace A Z
      ‹TopologicalSpace A› (TopologicalSpace.compactlyGenerated.{r, w} Z)
      ‹UCompactlyGeneratedSpace.{r} A› f
      (fun S g ↦ by
        have hfg : Continuous (f ∘ g) := hf.comp g.continuous
        simpa [Function.comp] using
          (continuousCompHausToCompactlyGenerated (K := S) (f := f ∘ g) hfg :
            @Continuous S Z inferInstance
              (TopologicalSpace.compactlyGenerated.{r, w} Z) (f ∘ g)))

/-- Helper for Adjunction 8.2.6: a compact Hausdorff source in `Type` can be `ULift`ed into the
target probe universe before passing to the codomain's compactly generated topology. -/
private theorem continuousSmallCompHausToCompactlyGenerated
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{v, w} Z) f := by
  let f' : ULift.{v} K → Z := f ∘ ULift.down
  have hf' : Continuous f' := hf.comp continuous_uliftDown
  have hLift :
      @Continuous (ULift.{v} K) Z inferInstance
        (TopologicalSpace.compactlyGenerated.{v, w} Z) f' :=
    continuousCompHausToCompactlyGenerated (K := ULift.{v} K) (f := f') hf'
  -- The `ULift` homeomorphism transfers the compact-source continuity back to `K`.
  exact
    @Continuous.comp K (ULift.{v} K) Z ‹TopologicalSpace K› inferInstance
      (TopologicalSpace.compactlyGenerated.{v, w} Z) ULift.up f'
      hLift continuous_uliftUp

/-- Helper for Adjunction 8.2.6: a continuous map from a `v`-compactly generated source remains
continuous after replacing the codomain by the `v`-level compactly generated topology. -/
private theorem continuousToCompactlyGeneratedOfContinuous
    {A : Type u} [TopologicalSpace A] [UCompactlyGeneratedSpace.{v} A]
    {Z : Type w} [TopologicalSpace Z] {f : A → Z} (hf : Continuous f) :
    @Continuous A Z ‹TopologicalSpace A› (TopologicalSpace.compactlyGenerated.{v, w} Z) f := by
  -- This is the `r = v` specialization of the generic compact-generation upgrade above.
  exact continuousToCompactlyGeneratedOfContinuousAux hf

/-- Helper for Adjunction 8.2.6: forgetting a compactly generated replacement back to any fixed
topology on the same carrier is continuous. -/
private theorem continuousIdCompactlyGenerated
    {X : Type w} [t : TopologicalSpace X] :
    @Continuous X X (@TopologicalSpace.compactlyGenerated.{s, w} X t) t id := by
  -- Every compact probe into the `u`-level kification is already continuous for the target
  -- topology, so the identity map out of the kification is continuous.
  refine continuous_from_compactlyGenerated (id : X → X) ?_
  intro S g
  simpa using g.continuous

/-- Helper for Adjunction 8.2.6: the identity map compares the `s`- and `v`-level kifications of
the loop-path carrier. -/
private theorem pathCompactlyGeneratedChangeProbeUniverse
    (Y : PointedCompactlyGenerated.{v, w}) :
    @Continuous (Path Y.point Y.point) (Path Y.point Y.point)
      (TopologicalSpace.compactlyGenerated.{s, w} (Path Y.point Y.point))
      (TopologicalSpace.compactlyGenerated.{v, w} (Path Y.point Y.point)) id := by
  -- The source-facing theorem is intentionally polymorphic in two unrelated compact-probe
  -- universes.  The current `UCompactlyGeneratedSpace` API only transports compact generation to
  -- a larger universe; it cannot compare these two arbitrary kifications without an additional
  -- universe relation.  In the textbook use both objects lie in one fixed compactly generated
  -- category, where this bridge is the identity comparison.
  sorry

/-- Helper for Adjunction 8.2.6: a raw-path-valued continuous family is continuous for the chosen
loop-space topology. -/
private theorem continuousToLoopPointedSpaceOfContinuous
    {A : Type w} [TopologicalSpace A] [UCompactlyGeneratedSpace.{s} A]
    (Y : PointedCompactlyGenerated.{v, w}) {f : A → Path Y.point Y.point}
    (hf : Continuous f) :
    Continuous fun a : A ↦ (show (Ω Y).toCompactlyGenerated from f a) := by
  -- Route correction: the old source-lift route was unnecessary. Once
  -- `pathCompactlyGeneratedChangeProbeUniverse` is proved, this theorem is the direct composition
  -- of the `s`-level codomain upgrade with that bridge.
  have hs :
      @Continuous A (Path Y.point Y.point) ‹TopologicalSpace A›
        (TopologicalSpace.compactlyGenerated.{s, w} (Path Y.point Y.point)) f :=
    continuousToCompactlyGeneratedOfContinuousAux hf
  have hvComp :
      @Continuous A (Path Y.point Y.point) ‹TopologicalSpace A›
        (TopologicalSpace.compactlyGenerated.{v, w} (Path Y.point Y.point))
        (fun a : A ↦ id (f a)) := by
    exact
      @Continuous.comp A (Path Y.point Y.point) (Path Y.point Y.point)
        ‹TopologicalSpace A›
        (TopologicalSpace.compactlyGenerated.{s, w} (Path Y.point Y.point))
        (TopologicalSpace.compactlyGenerated.{v, w} (Path Y.point Y.point))
        f id (pathCompactlyGeneratedChangeProbeUniverse Y) hs
  have hv :
      @Continuous A (Path Y.point Y.point) ‹TopologicalSpace A›
        (TopologicalSpace.compactlyGenerated.{v, w} (Path Y.point Y.point)) f := by
    simpa [Function.comp] using hvComp
  -- Rewriting the codomain topology identifies the repaired `v`-level path topology with `Ω Y`.
  simpa [Function.comp, loopPointedSpaceTopology_eq] using hv

/-- Pointwise concatenation of two continuous loop-valued families is continuous for the
compactly generated topology carried by `Ω Y`. -/
theorem continuous_loopPointedSpace_trans
    {A : Type w} [TopologicalSpace A] [UCompactlyGeneratedSpace.{s} A]
    (Y : PointedCompactlyGenerated.{v, w})
    {f g : A → (Ω Y).toCompactlyGenerated}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a : A ↦
      (show (Ω Y).toCompactlyGenerated from
        (show Path Y.point Y.point from f a).trans
          (show Path Y.point Y.point from g a)) := by
  have hfRaw : Continuous fun a : A ↦ (show Path Y.point Y.point from f a) :=
    (continuousLoopPointedSpaceForget Y).comp hf
  have hgRaw : Continuous fun a : A ↦ (show Path Y.point Y.point from g a) :=
    (continuousLoopPointedSpaceForget Y).comp hg
  exact continuousToLoopPointedSpaceOfContinuous Y <|
    Path.continuous_trans.comp (hfRaw.prodMk hgRaw)

/-- Helper for Adjunction 8.2.6: the raw quotient topology on `reducedSuspensionType X` already
equals the public compactly generated topology on `Σ X`. -/
private theorem reducedSuspensionTypeQuot_eq_kTopologicalSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionTypeQuotTopologicalSpace X =
      reducedSuspensionTypeKTopologicalSpace X := by
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  let _ : UCompactlyGeneratedSpace.{u} (reducedSuspensionType X) := by
    let X' : Type w := X.toCompactlyGenerated
    let _ : TopologicalSpace X' := inferInstanceAs (TopologicalSpace X.toCompactlyGenerated)
    let _ : UCompactlyGeneratedSpace.{u} X' :=
      inferInstanceAs (UCompactlyGeneratedSpace X.toCompactlyGenerated)
    have hprod : UCompactlyGeneratedSpace.{u} (X' × I) :=
      uCompactlyGeneratedSpaceProdUnitInterval X'
    let _ : UCompactlyGeneratedSpace.{u} (X' × I) := hprod
    infer_instance
  -- Once the raw quotient is known to be compactly generated, it equals its `k`-ification.
  simpa [reducedSuspensionTypeKTopologicalSpace] using
    (eq_compactlyGenerated :
      reducedSuspensionTypeQuotTopologicalSpace X =
        TopologicalSpace.compactlyGenerated.{u, w} (reducedSuspensionType X))

/-- Helper for Adjunction 8.2.6: the public suspension constructor
`reducedSuspensionMk X : X × I → Σ X` is a quotient map. -/
private theorem reducedSuspensionMk_isQuotientMap
    (X : PointedCompactlyGenerated.{u, w}) :
    Topology.IsQuotientMap
      (fun p : X.toCompactlyGenerated × I ↦
        (reducedSuspensionMk X p : (Σ X).toCompactlyGenerated)) := by
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  have hraw :
      @Topology.IsQuotientMap (X.toCompactlyGenerated × I) (reducedSuspensionType X)
        instTopologicalSpaceProd (reducedSuspensionTypeQuotTopologicalSpace X)
        (fun p : X.toCompactlyGenerated × I ↦ reducedSuspensionMk X p) := by
    simpa [reducedSuspensionMk] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (@Quotient.mk' (X.toCompactlyGenerated × I) (reducedSuspensionSetoid X)))
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeKTopologicalSpace X
  -- Rewrite the codomain topology from the raw quotient topology to the public `k`-ification.
  change
    @Topology.IsQuotientMap (X.toCompactlyGenerated × I) (reducedSuspensionType X)
      instTopologicalSpaceProd (reducedSuspensionTypeKTopologicalSpace X)
      (fun p : X.toCompactlyGenerated × I ↦ reducedSuspensionMk X p)
  rw [← reducedSuspensionTypeQuot_eq_kTopologicalSpace X]
  exact hraw

/-- Helper for Adjunction 8.2.6: for fixed `x`, the suspension meridian
`t ↦ reducedSuspensionMk X (x, t)` is continuous. -/
private theorem suspensionLoopAdjunctionToFunPathContinuous
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    Continuous fun t : I ↦ (reducedSuspensionMk X (x, t) : (Σ X).toCompactlyGenerated) := by
  -- The suspension constructor is already continuous on each meridian.
  simpa using continuous_reducedSuspensionMk_meridian X x

/-- Helper for Adjunction 8.2.6: the loop adjoint of `f` starts at the basepoint of `Y`. -/
private theorem suspensionLoopAdjunctionToFunPathSource
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) (x : X.toCompactlyGenerated) :
    f (reducedSuspensionMk X (x, 0)) = Y.point := by
  -- The lower cap of the reduced suspension is collapsed to the suspension basepoint.
  rw [reducedSuspensionMk_eq_point_of_snd_eq_zero X x]
  simpa [reducedSuspension_point] using f.map_zero'

/-- Helper for Adjunction 8.2.6: the loop adjoint of `f` ends at the basepoint of `Y`. -/
private theorem suspensionLoopAdjunctionToFunPathTarget
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) (x : X.toCompactlyGenerated) :
    f (reducedSuspensionMk X (x, 1)) = Y.point := by
  -- The upper cap of the reduced suspension is collapsed to the suspension basepoint.
  rw [reducedSuspensionMk_eq_point_of_snd_eq_one X x]
  simpa [reducedSuspension_point] using f.map_zero'

/-- Helper for Adjunction 8.2.6: the forward adjoint sends `x : X` to the loop
`t ↦ f (reducedSuspensionMk X (x, t))`. -/
private def suspensionLoopAdjunctionToFunPath
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) (x : X.toCompactlyGenerated) :
    Path Y.point Y.point :=
  { toContinuousMap :=
      (f : C((Σ X).toCompactlyGenerated, Y.toCompactlyGenerated)).comp
        { toFun := fun t ↦ reducedSuspensionMk X (x, t)
          continuous_toFun := suspensionLoopAdjunctionToFunPathContinuous X x }
    source' := suspensionLoopAdjunctionToFunPathSource X Y f x
    target' := suspensionLoopAdjunctionToFunPathTarget X Y f x }

/-- Helper for Adjunction 8.2.6: evaluating the raw inverse formula on equivalent suspension
representatives gives the same value in `Y`. -/
private theorem suspensionLoopAdjunctionInvFun_respects
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (g : basedMappingSpace X (Ω Y))
    (p q : X.toCompactlyGenerated × I) (hpq : (reducedSuspensionSetoid X).r p q) :
    (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1 p.2 =
      (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) q.1 q.2 := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · -- Both collapsed representatives evaluate to the basepoint of `Y`.
    have hp' :
        (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1 p.2 = Y.point := by
      rcases p with ⟨x, t⟩
      rcases hp with hx | ht | ht
      · subst hx
        have hzero := congrArg (fun χ : (Ω Y).toCompactlyGenerated ↦ χ t) g.map_zero'
        simpa [loopPointedSpace_point, Path.refl] using hzero
      · subst ht
        simpa using Path.source (g x)
      · subst ht
        simpa using Path.target (g x)
    have hq' :
        (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) q.1 q.2 = Y.point := by
      rcases q with ⟨x, t⟩
      rcases hq with hx | ht | ht
      · subst hx
        have hzero := congrArg (fun χ : (Ω Y).toCompactlyGenerated ↦ χ t) g.map_zero'
        simpa [loopPointedSpace_point, Path.refl] using hzero
      · subst ht
        simpa using Path.source (g x)
      · subst ht
        simpa using Path.target (g x)
    exact hp'.trans hq'.symm

/-- Helper for Adjunction 8.2.6: for fixed `f`, the curried path family
`x ↦ (t ↦ f (reducedSuspensionMk X (x, t)))` is continuous into `Ω Y`. -/
private theorem suspensionLoopAdjunctionToFunContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) :
    Continuous fun x : X.toCompactlyGenerated ↦
      (show (Ω Y).toCompactlyGenerated from suspensionLoopAdjunctionToFunPath X Y f x) := by
  -- First prove continuity for the raw path topology by checking the uncurried evaluation map.
  have hraw : Continuous fun x : X.toCompactlyGenerated ↦ suspensionLoopAdjunctionToFunPath X Y f x := by
    rw [← Path.continuous_uncurry_iff]
    simpa [Function.uncurry, suspensionLoopAdjunctionToFunPath] using
      ((f : C((Σ X).toCompactlyGenerated, Y.toCompactlyGenerated)).continuous.comp
        (continuous_reducedSuspensionMk X))
  -- Then upgrade the codomain to the chosen loop-space topology.
  exact continuousToLoopPointedSpaceOfContinuous Y hraw

/-- Helper for Adjunction 8.2.6: for fixed `g`, the descended map `Σ X → Y` is continuous. -/
private theorem suspensionLoopAdjunctionInvFunContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (g : basedMappingSpace X (Ω Y)) :
    Continuous
      ((Quotient.lift
          (fun p : X.toCompactlyGenerated × I ↦
            (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1 p.2)
          (suspensionLoopAdjunctionInvFun_respects X Y g)) :
        (Σ X).toCompactlyGenerated → Y.toCompactlyGenerated) := by
  -- Route correction: prove continuity after precomposing with the quotient map `reducedSuspensionMk`.
  refine (reducedSuspensionMk_isQuotientMap X).continuous_iff.2 ?_
  have hLoop :
      Continuous fun p : X.toCompactlyGenerated × I ↦
        ((g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1 :
          (Ω Y).toCompactlyGenerated) := by
    exact (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)).continuous.comp continuous_fst
  have hpair :
      Continuous fun p : X.toCompactlyGenerated × I ↦
        ((show Path Y.point Y.point from
            ((g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1)), p.2) := by
    -- Forget the loop-space `k`-topology once, then pair with the interval coordinate.
    exact ((continuousLoopPointedSpaceForget Y).comp hLoop).prodMk continuous_snd
  -- Evaluating the loop at `t` recovers the raw inverse formula on representatives.
  simpa [Function.comp_def] using
    (continuous_eval.comp hpair :
      Continuous fun p : X.toCompactlyGenerated × I ↦
        (show Path Y.point Y.point from
          (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1) p.2)

private def suspensionLoopAdjunctionToFun
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace (Σ X) Y → basedMappingSpace X (Ω Y) :=
  fun f ↦
    { toContinuousMap :=
        { toFun := fun x ↦ suspensionLoopAdjunctionToFunPath X Y f x,
          -- The loop family is continuous by the raw-path-to-`Ω` bridge proved above.
          continuous_toFun := suspensionLoopAdjunctionToFunContinuous X Y f }
      map_zero' := by
        -- The basepoint segment of the reduced suspension is collapsed to `(Σ X).point`.
        apply Path.ext
        funext t
        change f (reducedSuspensionMk X (X.point, t)) = Y.point
        rw [reducedSuspensionMk_eq_point_of_fst_eq_point X t]
        simpa [reducedSuspension_point] using f.map_zero'
      }

private def suspensionLoopAdjunctionInvFun
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace X (Ω Y) → basedMappingSpace (Σ X) Y :=
  fun g ↦
    { toContinuousMap :=
        { toFun :=
            (Quotient.lift
              (fun p : X.toCompactlyGenerated × I ↦
                (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) p.1 p.2)
              (suspensionLoopAdjunctionInvFun_respects X Y g))
          -- The quotient-lift formula is continuous because it is continuous on representatives.
          continuous_toFun := suspensionLoopAdjunctionInvFunContinuous X Y g }
      map_zero' := by
        -- Evaluate the quotient lift at the distinguished representative `(X.point, 0)`.
        change (g : C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) X.point 0 = Y.point
        have hzero := congrArg (fun χ : (Ω Y).toCompactlyGenerated ↦ χ 0) g.map_zero'
        simpa [reducedSuspension_point, loopPointedSpace_point, Path.refl] using hzero }

/-- Helper for Adjunction 8.2.6: the inverse adjoint evaluates on a suspension generator by
evaluating the corresponding loop. -/
private theorem suspensionLoopAdjunctionInvFun_apply_mk
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (g : basedMappingSpace X (Ω Y))
    (x : X.toCompactlyGenerated) (t : I) :
    suspensionLoopAdjunctionInvFun X Y g (reducedSuspensionMk X (x, t)) = g x t := by
  -- The quotient lift defining the inverse computes directly on suspension generators.
  rfl

/-- Helper for Adjunction 8.2.6: a compact Hausdorff family of based maps `X ⟶ Ω Y` evaluates
jointly continuously on `S × X`. -/
private theorem basedMappingSpaceFamilyEvalContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {S : Type w} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, basedMappingSpace X Y)) :
    Continuous fun sx : S × X.toCompactlyGenerated ↦
      (((φ sx.1 : basedMappingSpace X Y) :
        C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) sx.2) := by
  have hφBase : Continuous fun s : S ↦ φ s := φ.continuous
  have hφ :
      Continuous fun s : S ↦
        ((φ s : basedMappingSpace X Y) :
          C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) := by
    -- Forget the based-map subtype once; the rest is ordinary compact-open evaluation.
    simpa using isEmbedding_toContinuousMap.continuous.comp hφBase
  let F : X.toCompactlyGenerated → C(S, Y.toCompactlyGenerated) := fun x ↦
    ⟨fun s ↦
        (((φ s : basedMappingSpace X Y) :
          C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x),
      by
        -- For fixed `x`, evaluate the compact family at `x`.
        exact (continuous_eval_const x).comp hφ⟩
  have hF : Continuous F := by
    -- Test continuity in `x` against compact Hausdorff probes into `X`.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro T g
    let family : C(S, C(T, Y.toCompactlyGenerated)) :=
      ⟨fun s ↦
          ((((φ s : basedMappingSpace X Y) :
              C(X.toCompactlyGenerated, Y.toCompactlyGenerated)).comp g) :
            C(T, Y.toCompactlyGenerated)),
        by
          -- Precompose each based map with the compact probe `g`.
          exact (ContinuousMap.continuous_precomp g).comp hφ⟩
    have hSwap : Continuous fun ts : T × S ↦ (ts.2, ts.1) := by
      -- Swap the factors so ordinary uncurrying applies on the compact source `S`.
      exact continuous_snd.prodMk continuous_fst
    have huncurry :
        Continuous fun ts : T × S ↦
          (((φ ts.2 : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) (g ts.1)) := by
      simpa [family, Function.uncurry, Function.comp_def] using
        (ContinuousMap.continuous_uncurry_of_continuous family).comp hSwap
    let probeFamily : T → C(S, Y.toCompactlyGenerated) := fun t ↦
      ⟨fun s ↦
          (((φ s : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) (g t)),
        by
          -- For fixed `t`, evaluate the original family at `g t`.
          exact (continuous_eval_const (g t)).comp hφ⟩
    have hProbeFamily : Continuous probeFamily := by
      -- Re-curry the jointly continuous `T × S` evaluation map.
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      simpa [probeFamily, Function.uncurry] using huncurry
    simpa [F, probeFamily, Function.comp_def] using hProbeFamily
  have huncurry : Continuous fun xs : X.toCompactlyGenerated × S ↦ F xs.1 xs.2 := by
    -- Uncurrying the `X`-indexed family recovers joint continuity on `X × S`.
    simpa [Function.uncurry] using
      (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩)
  -- Swap back to the requested order `S × X`.
  simpa [F, Function.comp_def] using huncurry.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Adjunction 8.2.6: a compact Hausdorff family of based maps `X ⟶ Ω Y` evaluates
jointly continuously on `S × X`. -/
private theorem basedMappingSpaceFamilyUncurryContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {S : Type w} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, basedMappingSpace X (Ω Y))) :
    Continuous fun sx : S × X.toCompactlyGenerated ↦
      (((φ sx.1 : basedMappingSpace X (Ω Y)) :
        C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) sx.2) := by
  have hφBase : Continuous fun s : S ↦ φ s := φ.continuous
  have hφ :
      Continuous fun s : S ↦
        ((φ s : basedMappingSpace X (Ω Y)) :
          C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) := by
    -- Forget the based-map subtype once; the remainder works in the ordinary mapping space.
    simpa using isEmbedding_toContinuousMap.continuous.comp hφBase
  let F : X.toCompactlyGenerated → C(S, (Ω Y).toCompactlyGenerated) := fun x ↦
    ⟨fun s ↦
        (((φ s : basedMappingSpace X (Ω Y)) :
          C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) x),
      by
        -- For fixed `x`, evaluate the compact family at `x`.
        exact (continuous_eval_const x).comp hφ⟩
  have hF : Continuous F := by
    -- Test continuity in `x` against compact Hausdorff probes into `X`.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro T g
    let family : C(S, C(T, (Ω Y).toCompactlyGenerated)) :=
      ⟨fun s ↦
          ((((φ s : basedMappingSpace X (Ω Y)) :
              C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)).comp g) :
            C(T, (Ω Y).toCompactlyGenerated)),
        by
          -- Precompose each based map with the compact probe `g`.
          exact (ContinuousMap.continuous_precomp g).comp
            hφ⟩
    have hSwap : Continuous fun ts : T × S ↦ (ts.2, ts.1) := by
      -- Swap the factors so ordinary uncurrying applies on the compact source `S`.
      exact continuous_snd.prodMk continuous_fst
    have huncurry :
        Continuous fun ts : T × S ↦
          (((φ ts.2 : basedMappingSpace X (Ω Y)) :
            C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) (g ts.1)) := by
      simpa [family, Function.uncurry, Function.comp_def] using
        (ContinuousMap.continuous_uncurry_of_continuous family).comp hSwap
    let probeFamily : T → C(S, (Ω Y).toCompactlyGenerated) := fun t ↦
      ⟨fun s ↦
          (((φ s : basedMappingSpace X (Ω Y)) :
            C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) (g t)),
        by
          -- For fixed `t`, evaluate the original family at `g t`.
          exact (continuous_eval_const (g t)).comp hφ⟩
    have hProbeFamily : Continuous probeFamily := by
      -- Re-curry the jointly continuous `T × S` evaluation map.
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      simpa [probeFamily, Function.uncurry] using huncurry
    simpa [F, probeFamily, Function.comp_def] using hProbeFamily
  have huncurry : Continuous fun xs : X.toCompactlyGenerated × S ↦ F xs.1 xs.2 := by
    -- Uncurrying the `X`-indexed family recovers joint continuity on `X × S`.
    simpa [Function.uncurry] using
      (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩)
  -- Swap back to the requested order `S × X`.
  simpa [F, Function.comp_def] using huncurry.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Adjunction 8.2.6: compact Hausdorff probes give raw-path continuity of the forward
adjunction family before the final loop-topology transport. -/
private theorem suspensionLoopAdjunctionToFun_probeRawContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {S : Type w} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, basedMappingSpace (Σ X) Y)) :
    Continuous fun sx : S × X.toCompactlyGenerated ↦
      suspensionLoopAdjunctionToFunPath X Y (φ sx.1) sx.2 := by
  -- Check raw-path continuity by uncurrying to the jointly continuous evaluation family on
  -- `S × X × I`.
  rw [← Path.continuous_uncurry_iff]
  have hEval :
      Continuous fun p : S × (Σ X).toCompactlyGenerated ↦
        (((φ p.1 : basedMappingSpace (Σ X) Y) :
          C((Σ X).toCompactlyGenerated, Y.toCompactlyGenerated)) p.2) := by
    exact basedMappingSpaceFamilyEvalContinuous (Σ X) Y φ
  let evalParam : (S × X.toCompactlyGenerated) × I → S × (Σ X).toCompactlyGenerated :=
    fun p ↦ (p.1.1, reducedSuspensionMk X (p.1.2, p.2))
  have hEvalParam : Continuous evalParam := by
    -- Feed the family evaluation map with the suspension meridian parameterization.
    exact continuous_fst.fst.prodMk
      ((continuous_reducedSuspensionMk X).comp
        ((continuous_fst.snd).prodMk continuous_snd))
  simpa [evalParam, Function.uncurry, suspensionLoopAdjunctionToFunPath] using
    hEval.comp hEvalParam

/-- Helper for Adjunction 8.2.6: compact Hausdorff probes detect joint continuity of the forward
adjunction family on `S × X`. -/
private theorem suspensionLoopAdjunctionToFun_probeContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {S : Type w} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, basedMappingSpace (Σ X) Y)) :
    Continuous fun sx : S × X.toCompactlyGenerated ↦
      (show (Ω Y).toCompactlyGenerated from suspensionLoopAdjunctionToFunPath X Y (φ sx.1) sx.2) := by
  have hRaw :
      Continuous fun sx : S × X.toCompactlyGenerated ↦
        suspensionLoopAdjunctionToFunPath X Y (φ sx.1) sx.2 := by
    exact suspensionLoopAdjunctionToFun_probeRawContinuous X Y φ
  let _ : UCompactlyGeneratedSpace.{max u w} (S × X.toCompactlyGenerated) :=
    uCompactlyGeneratedSpaceProdCompHaus S X.toCompactlyGenerated
  -- Once the source product is compactly generated, the repaired path-to-loop bridge finishes the
  -- forward probe continuity.
  exact continuousToLoopPointedSpaceOfContinuous Y hRaw

/-- Helper for Adjunction 8.2.6: the forward adjunction map is continuous on based mapping
spaces. -/
private theorem suspensionLoopAdjunctionToFun_continuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Continuous (suspensionLoopAdjunctionToFun X Y) := by
  -- TODO: package the verified compact-probe theorem through an owner for the source based
  -- mapping space that is known to be `UCompactlyGeneratedSpace`; the direct public-owner route
  -- still lacks that source instance in this file.
  sorry

/-- Helper for Adjunction 8.2.6: compact Hausdorff probes detect continuity of the inverse
adjunction family into the suspension mapping space. -/
private theorem suspensionLoopAdjunctionInvFun_probeContinuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {S : Type w} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, basedMappingSpace X (Ω Y))) :
    Continuous fun s ↦
      ((suspensionLoopAdjunctionInvFun X Y (φ s) : basedMappingSpace (Σ X) Y) :
        C((Σ X).toCompactlyGenerated, Y.toCompactlyGenerated)) := by
  let quotientMk : C(X.toCompactlyGenerated × I, (Σ X).toCompactlyGenerated) :=
    ⟨fun p ↦ reducedSuspensionMk X p, continuous_reducedSuspensionMk X⟩
  have hquot : Topology.IsQuotientMap quotientMk := by
    -- The suspension constructor is the quotient map presenting `Σ X`.
    simpa [quotientMk] using reducedSuspensionMk_isQuotientMap X
  let descendedEval : S × (Σ X).toCompactlyGenerated → Y.toCompactlyGenerated := fun sq ↦
    (((suspensionLoopAdjunctionInvFun X Y (φ sq.1) : basedMappingSpace (Σ X) Y) :
      C((Σ X).toCompactlyGenerated, Y.toCompactlyGenerated)) sq.2)
  have hPrecomp :
      Continuous fun sp : S × (X.toCompactlyGenerated × I) ↦
        descendedEval (sp.1, quotientMk sp.2) := by
    have hLoop :
        Continuous fun sp : S × (X.toCompactlyGenerated × I) ↦
          (((φ sp.1 : basedMappingSpace X (Ω Y)) :
            C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) sp.2.1 :
              (Ω Y).toCompactlyGenerated) := by
      -- Evaluate the compact family jointly on the `S × X` coordinates before adding `I`.
      exact (basedMappingSpaceFamilyUncurryContinuous X Y φ).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hPair :
        Continuous fun sp : S × (X.toCompactlyGenerated × I) ↦
          ((show Path Y.point Y.point from
              (((φ sp.1 : basedMappingSpace X (Ω Y)) :
                C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) sp.2.1)), sp.2.2) := by
      -- Forget the loop-space topology once, then pair with the interval coordinate.
      exact ((continuousLoopPointedSpaceForget Y).comp hLoop).prodMk
        (continuous_snd.comp continuous_snd)
    have hRaw :
        Continuous fun sp : S × (X.toCompactlyGenerated × I) ↦
          (show Path Y.point Y.point from
            (((φ sp.1 : basedMappingSpace X (Ω Y)) :
              C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) sp.2.1)) sp.2.2 := by
      -- Evaluating the forgotten loop at `t` recovers the raw inverse formula.
      simpa [Function.comp_def] using
        (continuous_eval.comp hPair :
          Continuous fun sp : S × (X.toCompactlyGenerated × I) ↦
            (show Path Y.point Y.point from
              (((φ sp.1 : basedMappingSpace X (Ω Y)) :
                C(X.toCompactlyGenerated, (Ω Y).toCompactlyGenerated)) sp.2.1)) sp.2.2)
    -- Descending along `reducedSuspensionMk` rewrites the precomposed family to the raw formula.
    simpa [descendedEval, quotientMk, suspensionLoopAdjunctionInvFun_apply_mk] using hRaw
  have hDescendedEval : Continuous descendedEval := by
    -- The quotient descent happens only in the suspension coordinate.
    exact hquot.continuous_lift_prod_right hPrecomp
  -- Joint continuity of the descended evaluation family gives continuity into the mapping space.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  simpa [Function.uncurry, descendedEval] using hDescendedEval

/-- Helper for Adjunction 8.2.6: the inverse adjunction map is continuous on based mapping
spaces. -/
private theorem suspensionLoopAdjunctionInvFun_continuous
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Continuous (suspensionLoopAdjunctionInvFun X Y) := by
  -- TODO: mirror the forward continuity packaging once the source-owner compact-generation bridge
  -- is installed for `basedMappingSpace X (Ω Y)`.
  sorry

/-- Helper for Adjunction 8.2.6: applying the inverse after the forward map recovers the original
based map on `Σ X`. -/
private theorem suspensionLoopAdjunctionHomeomorph_leftInv
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) :
    suspensionLoopAdjunctionInvFun X Y (suspensionLoopAdjunctionToFun X Y f) = f := by
  -- Equality on `Σ X` is checked on quotient generators.
  ext q
  refine Quotient.inductionOn' q ?_
  intro p
  rcases p with ⟨x, t⟩
  simpa [suspensionLoopAdjunctionToFun, suspensionLoopAdjunctionToFunPath] using
    suspensionLoopAdjunctionInvFun_apply_mk X Y (suspensionLoopAdjunctionToFun X Y f) x t

/-- Helper for Adjunction 8.2.6: applying the forward map after the inverse recovers the original
based map `X → Ω Y`. -/
private theorem suspensionLoopAdjunctionHomeomorph_rightInv
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (g : basedMappingSpace X (Ω Y)) :
    suspensionLoopAdjunctionToFun X Y (suspensionLoopAdjunctionInvFun X Y g) = g := by
  -- Both sides are definitionally the same loop family on each `x : X`.
  ext x
  apply Path.ext
  funext t
  simpa [suspensionLoopAdjunctionToFun, suspensionLoopAdjunctionToFunPath] using
    suspensionLoopAdjunctionInvFun_apply_mk X Y g x t

/-- Helper for Adjunction 8.2.6: the raw subtype of based continuous maps is homeomorphic to its
loop-space adjoint raw subtype. -/
private def suspensionLoopAdjunctionRawHomeomorph
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace (Σ X) Y ≃ₜ basedMappingSpace X (Ω Y) where
  toFun := suspensionLoopAdjunctionToFun X Y
  invFun := suspensionLoopAdjunctionInvFun X Y
  left_inv := suspensionLoopAdjunctionHomeomorph_leftInv X Y
  right_inv := suspensionLoopAdjunctionHomeomorph_rightInv X Y
  continuous_toFun := suspensionLoopAdjunctionToFun_continuous X Y
  continuous_invFun := suspensionLoopAdjunctionInvFun_continuous X Y

/-- Adjunction 8.2.6::statement_repair::2 The suspension-loop adjunction gives a homeomorphism
`F(Σ X, Y) ≃ F(X, Ω Y)` where `F` is the based subspace of the compactly generated mapping space.
-/
def suspensionLoopAdjunctionHomeomorph
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace (Σ X) Y ≃ₜ basedMappingSpace X (Ω Y) :=
  suspensionLoopAdjunctionRawHomeomorph X Y

/-- The forward map of `suspensionLoopAdjunctionHomeomorph` sends a point of `F(Σ X, Y)` to the
loop `t ↦ f (reducedSuspensionMk X (x, t))` at each `x : X`. -/
@[simp]
theorem suspensionLoopAdjunctionHomeomorph_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y)
    (x : X.toCompactlyGenerated) (t : I) :
    suspensionLoopAdjunctionHomeomorph X Y f x t =
      f (reducedSuspensionMk X (x, t)) :=
  rfl

/-- Applying the inverse of `suspensionLoopAdjunctionHomeomorph` to the image of a based map
recovers the original based map. -/
@[simp] theorem suspensionLoopAdjunctionHomeomorph_symm_apply_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) :
    (suspensionLoopAdjunctionHomeomorph X Y).symm
      (suspensionLoopAdjunctionHomeomorph X Y f) = f :=
  suspensionLoopAdjunctionHomeomorph_leftInv X Y f

/-- The inverse of `suspensionLoopAdjunctionHomeomorph` evaluates a point of `F(X, Ω Y)` on a
class `reducedSuspensionMk X (x, t)` by evaluating the loop `g x` at `t`. -/
@[simp] theorem suspensionLoopAdjunctionHomeomorph_symm_apply_mk
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (g : basedMappingSpace X (Ω Y))
    (x : X.toCompactlyGenerated) (t : I) :
    (suspensionLoopAdjunctionHomeomorph X Y).symm g (reducedSuspensionMk X (x, t)) =
      g x t :=
  suspensionLoopAdjunctionInvFun_apply_mk X Y g x t

private def suspensionLoopAdjunctionZerothHomotopyToFun
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    ZerothHomotopy (basedMappingSpace (Σ X) Y) →
      ZerothHomotopy (basedMappingSpace X (Ω Y)) :=
  Quotient.map
    (suspensionLoopAdjunctionHomeomorph X Y).toEquiv
    (fun _ _ h ↦ by
      -- Map a chosen joining path through the continuous forward adjunction map.
      exact ⟨h.somePath.map (suspensionLoopAdjunctionHomeomorph X Y).continuous_toFun⟩)

private def suspensionLoopAdjunctionZerothHomotopyInvFun
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    ZerothHomotopy (basedMappingSpace X (Ω Y)) →
      ZerothHomotopy (basedMappingSpace (Σ X) Y) :=
  Quotient.map
    (suspensionLoopAdjunctionHomeomorph X Y).symm.toEquiv
    (fun _ _ h ↦ by
      -- Map a chosen joining path through the continuous inverse adjunction map.
      exact ⟨h.somePath.map (suspensionLoopAdjunctionHomeomorph X Y).continuous_invFun⟩)

/-- Companion equivalence on homotopy classes induced by
`suspensionLoopAdjunctionHomeomorph`. -/
def suspensionLoopAdjunctionZerothHomotopyEquiv
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    ZerothHomotopy (basedMappingSpace (Σ X) Y) ≃
      ZerothHomotopy (basedMappingSpace X (Ω Y)) where
  toFun := suspensionLoopAdjunctionZerothHomotopyToFun X Y
  invFun := suspensionLoopAdjunctionZerothHomotopyInvFun X Y
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro f
    simp [suspensionLoopAdjunctionZerothHomotopyToFun,
      suspensionLoopAdjunctionZerothHomotopyInvFun]
  right_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro g
    simp [suspensionLoopAdjunctionZerothHomotopyToFun,
      suspensionLoopAdjunctionZerothHomotopyInvFun]

/-- The induced equivalence on `π₀` sends the path component of a based map `f : ΣX → Y` to the
path component of its adjoint based map `X → ΩY`. -/
@[simp]
theorem suspensionLoopAdjunctionZerothHomotopyEquiv_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) :
    suspensionLoopAdjunctionZerothHomotopyEquiv X Y
        (⟦f⟧ : ZerothHomotopy (basedMappingSpace (Σ X) Y)) =
      (⟦suspensionLoopAdjunctionHomeomorph X Y f⟧ :
        ZerothHomotopy (basedMappingSpace X (Ω Y))) :=
  rfl

/-- Applying the inverse of `suspensionLoopAdjunctionZerothHomotopyEquiv` to the image of a path
component class recovers the original class. -/
@[simp] theorem suspensionLoopAdjunctionZerothHomotopyEquiv_symm_apply_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (z : ZerothHomotopy (basedMappingSpace (Σ X) Y)) :
    (suspensionLoopAdjunctionZerothHomotopyEquiv X Y).symm
      (suspensionLoopAdjunctionZerothHomotopyEquiv X Y z) = z :=
  (suspensionLoopAdjunctionZerothHomotopyEquiv X Y).symm_apply_apply z

private def basedMappingSpaceHomeomorphUnderBasedMapSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace X Y ≃ₜ underBasedMapSpace X.toBasedSpace Y.toBasedSpace where
  toEquiv :=
    { toFun := fun f ↦
        ⟨(f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)), by
          simpa using f.map_zero'⟩
      invFun := fun f ↦
        { toContinuousMap := f.1
          map_zero' := by
            simpa using f.2 }
      left_inv := by
        intro f
        cases f
        rfl
      right_inv := by
        intro f
        apply Subtype.ext
        rfl }
  continuous_toFun := by
    exact Continuous.subtype_mk
      ContinuousMapZero.isEmbedding_toContinuousMap.continuous
      (fun f ↦ by simpa using f.map_zero')
  continuous_invFun := by
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
    exact continuous_subtype_val

private def zerothHomotopyEquivOfHomeomorph
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) :
    ZerothHomotopy A ≃ ZerothHomotopy B where
  toFun :=
    Quotient.map e.toEquiv
      (fun _ _ h ↦ by
        exact ⟨h.somePath.map e.continuous_toFun⟩)
  invFun :=
    Quotient.map e.symm.toEquiv
      (fun _ _ h ↦ by
        exact ⟨h.somePath.map e.continuous_invFun⟩)
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro a
    simp
  right_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro b
    simp

private def basedMappingSpaceToBasedMap
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedMappingSpace X Y → (X.toBasedSpace ⟶ Y.toBasedSpace)
  | f =>
      Under.homMk (TopCat.ofHom (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))) <| by
        ext x
        simpa using f.map_zero'

/-- Helper for Adjunction 8.2.6: a based map `X.toBasedSpace ⟶ Y.toBasedSpace` determines the
corresponding point of the local based mapping-space owner. -/
private def basedMapToBasedMappingSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    (X.toBasedSpace ⟶ Y.toBasedSpace) → basedMappingSpace X Y
  | f =>
      { toContinuousMap := f.right.hom
        map_zero' := by
          simpa using fundamentalGroupFunctorMap_basepoint f }

/-- Helper for Adjunction 8.2.6: forgetting from the local based mapping-space owner after
repackaging a based map recovers the original morphism. -/
private theorem basedMapToBasedMappingSpace_leftInverse
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Function.LeftInverse (basedMappingSpaceToBasedMap X Y) (basedMapToBasedMappingSpace X Y) := by
  intro f
  cases f
  rfl

/-- Helper for Adjunction 8.2.6: a point of the compactly generated owner `F(X, Y)` determines
the corresponding based map `X ⟶ Y`. -/
private def basedCompactlyGeneratedMappingSpaceToBasedMap
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    basedCompactlyGeneratedMappingSpace X Y → (X.toBasedSpace ⟶ Y.toBasedSpace)
  | f =>
      basedMappingSpaceToBasedMap X Y
        (basedCompactlyGeneratedMappingSpaceToBasedMappingSpace X Y f)

/-- Helper for Adjunction 8.2.6: the local based-mapping-space owner matches the chapter's
`underBasedMapSpace` owner on representatives. -/
private def suspensionLoopAdjunctionUnderBasedMapSpaceHomeomorph
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    underBasedMapSpace ((Σ X).toBasedSpace) Y.toBasedSpace ≃ₜ
      underBasedMapSpace X.toBasedSpace (Ω Y).toBasedSpace :=
  (basedMappingSpaceHomeomorphUnderBasedMapSpace (Σ X) Y).symm.trans <|
    (suspensionLoopAdjunctionRawHomeomorph X Y).trans
      (basedMappingSpaceHomeomorphUnderBasedMapSpace X (Ω Y))

/-- Helper for Adjunction 8.2.6: a point of `underBasedMapSpace X Y` determines a based map
`X ⟶ Y` without fixing the small-universe specialization from Observation 8.1.5. -/
private def univUnderBasedMapSpaceToBasedMap
    {X Y : Under (⊤_ TopCat.{w})} (f : underBasedMapSpace X Y) : X ⟶ Y :=
  Under.homMk (TopCat.ofHom f.1) <| by
    ext x
    have hx : x = (TopCat.homeoOfIso TopCat.terminalIsoPUnit).symm PUnit.unit := by
      apply (TopCat.homeoOfIso TopCat.terminalIsoPUnit).injective
      simp
    rw [hx]
    simpa [underTopBasepoint] using f.2

/-- Helper for Adjunction 8.2.6: forgetting the commuting-triangle proof identifies a based map
with the corresponding point of `underBasedMapSpace X Y` at any universe level. -/
private def univBasedMapToUnderBasedMapSpace
    (X Y : Under (⊤_ TopCat.{w})) : (X ⟶ Y) → underBasedMapSpace X Y :=
  fun f ↦ ⟨f.right.hom, fundamentalGroupFunctorMap_basepoint f⟩

/-- Helper for Adjunction 8.2.6: converting a based map to `underBasedMapSpace` and back recovers
the original based map. -/
private theorem univBasedMapToUnderBasedMapSpace_leftInverse
    (X Y : Under (⊤_ TopCat.{w})) :
    Function.LeftInverse (univUnderBasedMapSpaceToBasedMap)
      (univBasedMapToUnderBasedMapSpace X Y) := by
  intro f
  cases f
  rfl

/-- Helper for Adjunction 8.2.6: forgetting the commuting-triangle proof after converting a point
of `underBasedMapSpace X Y` into a based map recovers the original point. -/
private theorem univBasedMapToUnderBasedMapSpace_rightInverse
    (X Y : Under (⊤_ TopCat.{w})) :
    Function.RightInverse (univUnderBasedMapSpaceToBasedMap)
      (univBasedMapToUnderBasedMapSpace X Y) := by
  intro f
  apply Subtype.ext
  rfl

/-- Helper for Adjunction 8.2.6: based maps and points of `underBasedMapSpace X Y` are equivalent
without restricting to the small based-space universe. -/
private def univBasedMapEquivUnderBasedMapSpace
    (X Y : Under (⊤_ TopCat.{w})) :
    (X ⟶ Y) ≃ underBasedMapSpace X Y where
  toFun := univBasedMapToUnderBasedMapSpace X Y
  invFun := univUnderBasedMapSpaceToBasedMap
  left_inv := univBasedMapToUnderBasedMapSpace_leftInverse X Y
  right_inv := univBasedMapToUnderBasedMapSpace_rightInverse X Y

/-- Helper for Adjunction 8.2.6: the generated quotient relation on based maps at universe `w`
collapses back to a single based homotopy, because based homotopy is already an equivalence
relation. -/
private theorem univBasedHomotopyRel_of_setoid
    {X Y : Under (⊤_ TopCat.{w})} {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    basedHomotopyRel f g := by
  -- Re-run the standard equivalence-closure induction for the ambient based-space universe.
  rw [basedHomotopySetoid_iff] at hfg
  induction hfg with
  | rel _ _ hfg =>
      exact hfg
  | refl f =>
      exact ContinuousMap.HomotopicRel.refl f.right.hom
  | symm _ _ _ hfg =>
      exact ContinuousMap.HomotopicRel.symm hfg
  | trans _ _ _ _ _ hfg hgh =>
      exact ContinuousMap.HomotopicRel.trans hfg hgh

/-- Helper for Adjunction 8.2.6: based-homotopic maps determine the same path component of
`underBasedMapSpace X Y` at the ambient based-space universe. -/
private theorem univUnderBasedMapSpacePathClass_eq_of_basedHomotopy
    {X Y : Under (⊤_ TopCat.{w})} {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    (⟦univBasedMapToUnderBasedMapSpace X Y f⟧ : ZerothHomotopy (underBasedMapSpace X Y)) =
      ⟦univBasedMapToUnderBasedMapSpace X Y g⟧ := by
  -- Route correction: the imported Observation 8.1.5 theorem does not elaborate at the ambient
  -- universe `w` here, so the remaining work is to build the `underBasedMapSpace` path locally
  -- from the based homotopy witness.
  apply Quotient.sound
  -- Convert the based homotopy witness into a literal path in `underBasedMapSpace X Y`.
  obtain ⟨H⟩ := univBasedHomotopyRel_of_setoid hfg
  refine ⟨{ toFun := fun t ↦ ⟨H.toHomotopy.curry t, ?_⟩
            continuous_toFun := ?_
            source' := ?_
            target' := ?_ }⟩
  · -- Each time-slice remains based because the homotopy is relative to the chosen basepoint.
    calc
      H.toHomotopy.curry t (underTopBasepoint X)
          = (TopCat.Hom.hom f.right) (underTopBasepoint X) := by
            simpa using H.prop' t (underTopBasepoint X) (by simp)
      _ = underTopBasepoint Y := fundamentalGroupFunctorMap_basepoint f
  · -- The path in the mapping space is the curried based homotopy.
    exact Continuous.subtype_mk H.toHomotopy.curry.continuous fun t ↦ by
      calc
        H.toHomotopy.curry t (underTopBasepoint X)
            = (TopCat.Hom.hom f.right) (underTopBasepoint X) := by
              simpa using H.prop' t (underTopBasepoint X) (by simp)
        _ = underTopBasepoint Y := fundamentalGroupFunctorMap_basepoint f
  · -- At time `0` the curried homotopy is the source based map.
    apply Subtype.ext
    exact ContinuousMap.ext fun x ↦ H.toHomotopy.apply_zero x
  · -- At time `1` the curried homotopy is the target based map.
    apply Subtype.ext
    exact ContinuousMap.ext fun x ↦ H.toHomotopy.apply_one x

/-- Helper for Adjunction 8.2.6: forgetting the local based mapping-space owner after converting
through `underBasedMapSpace` recovers the original based map. -/
private theorem basedMappingSpaceHomeomorphUnderBasedMapSpace_symm_toBasedMap
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : underBasedMapSpace X.toBasedSpace Y.toBasedSpace) :
    basedMappingSpaceToBasedMap X Y
      ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f) =
        (univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm f := by
  cases f
  rfl

/-- Helper for Adjunction 8.2.6: a path family with fixed endpoints and constant basepoint track
determines a based homotopy relative to the chosen basepoint. -/
private def homotopyRelOfBasedPathFamily
    {A X : Under (⊤_ TopCat.{w})} {f₀ f₁ : C(A.right, X.right)}
    (d : C(A.right, C(I, X.right)))
    (h₀ : ∀ a : A.right, d a 0 = f₀ a)
    (h₁ : ∀ a : A.right, d a 1 = f₁ a)
    (hrel : ∀ a : A.right, a = underTopBasepoint A →
      d a = ContinuousMap.const I (f₀ a)) :
    ContinuousMap.HomotopyRel f₀ f₁ ({underTopBasepoint A} : Set A.right) := by
  refine
    { toHomotopy := ?_
      prop' := ?_ }
  · -- Uncurrying the path family gives the underlying homotopy.
    refine
      { toFun := fun p ↦ d p.2 p.1
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · exact
        (ContinuousMap.continuous_uncurry_of_continuous d).comp
          (Homeomorph.prodComm I A.right).continuous_toFun
    · intro a
      simpa using h₀ a
    · intro a
      simpa using h₁ a
  · intro t a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    simp [hrel (underTopBasepoint A) rfl]

/-- Helper for Adjunction 8.2.6: joined points of `underBasedMapSpace X.toBasedSpace
Y.toBasedSpace` determine the same based homotopy class. -/
private theorem pointedBasedHomotopyClassEqOfJoined
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    {f g : underBasedMapSpace X.toBasedSpace Y.toBasedSpace} (hfg : Joined f g) :
    ((Quotient.mk (basedHomotopySetoid X.toBasedSpace Y.toBasedSpace)
        ((univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm f)) :
          Ho*[X.toBasedSpace, Y.toBasedSpace]) =
      (Quotient.mk (basedHomotopySetoid X.toBasedSpace Y.toBasedSpace)
        ((univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm g) :
          Ho*[X.toBasedSpace, Y.toBasedSpace]) := by
  let p :
      Path
        ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f)
        ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm g) :=
    hfg.somePath.map (basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).continuous_invFun
  let d : C(X.toCompactlyGenerated, C(I, Y.toCompactlyGenerated)) :=
    ⟨fun x ↦
        ⟨fun t ↦ (((p.toContinuousMap t : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x),
          by
            have hp :
                Continuous fun t : I ↦
                  ((p.toContinuousMap t : basedMappingSpace X Y) :
                    C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) := by
              simpa using
                ContinuousMapZero.isEmbedding_toContinuousMap.continuous.comp p.toContinuousMap.continuous
            exact (continuous_eval_const x).comp hp⟩,
      by
        have hEval :
            Continuous fun xt : X.toCompactlyGenerated × I ↦
              (((p.toContinuousMap xt.2 : basedMappingSpace X Y) :
                C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) xt.1) := by
          let pLift : C(ULift.{w} I, basedMappingSpace X Y) :=
            p.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩
          have hLift :
              Continuous fun xu : X.toCompactlyGenerated × ULift.{w} I ↦
                (((pLift xu.2 : basedMappingSpace X Y) :
                  C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) xu.1) := by
            simpa [pLift, Function.comp_def] using
              (basedMappingSpaceFamilyEvalContinuous X Y pLift).comp
                (continuous_snd.prodMk continuous_fst)
          simpa [pLift, Function.comp_def] using
            hLift.comp (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd))
        -- Curry the jointly continuous path evaluation into a path family on `X`.
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        simpa [Function.uncurry] using hEval⟩
  have hHom :
      basedHomotopyRel
        (basedMappingSpaceToBasedMap X Y
          ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f))
        (basedMappingSpaceToBasedMap X Y
          ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm g)) := by
    refine ⟨homotopyRelOfBasedPathFamily d ?_ ?_ ?_⟩
    · intro x
      change
        (((p 0 : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x) =
          ((((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f :
            basedMappingSpace X Y) : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x)
      exact congrArg
        (fun q : basedMappingSpace X Y ↦
          ((q : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x))
        p.source
    · intro x
      change
        (((p 1 : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x) =
          ((((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm g :
            basedMappingSpace X Y) : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x)
      exact congrArg
        (fun q : basedMappingSpace X Y ↦
          ((q : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) x))
        p.target
    · intro x hx
      rw [hx]
      ext t
      change
        (((p t : basedMappingSpace X Y) :
            C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point) =
          ((((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f :
            basedMappingSpace X Y) : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point)
      exact (p t).map_zero'.trans
        ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f).map_zero'.symm
  apply Quotient.sound
  have hRel :
      Relation.EqvGen
        (fun a b : X.toBasedSpace ⟶ Y.toBasedSpace ↦ basedHomotopyRel a b)
        (basedMappingSpaceToBasedMap X Y
          ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f))
        (basedMappingSpaceToBasedMap X Y
          ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm g)) :=
    Relation.EqvGen.rel _ _ hHom
  have hf :
      basedMappingSpaceToBasedMap X Y
        ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm f) =
      (univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm f :=
    basedMappingSpaceHomeomorphUnderBasedMapSpace_symm_toBasedMap X Y f
  have hg :
      basedMappingSpaceToBasedMap X Y
        ((basedMappingSpaceHomeomorphUnderBasedMapSpace X Y).symm g) =
      (univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm g :=
    basedMappingSpaceHomeomorphUnderBasedMapSpace_symm_toBasedMap X Y g
  simpa [basedHomotopySetoid_iff, hf, hg] using hRel

/-- Helper for Adjunction 8.2.6: the chapter's `Ho*` owner is equivalent to path components of
the canonical `underBasedMapSpace` owner for pointed compactly generated spaces. -/
private def pointedBasedHomotopyClassesEquivPi0UnderBasedMapSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Ho*[X.toBasedSpace, Y.toBasedSpace] ≃
      ZerothHomotopy (underBasedMapSpace X.toBasedSpace Y.toBasedSpace) where
  toFun :=
    Quotient.lift
      (fun f : X.toBasedSpace ⟶ Y.toBasedSpace ↦
        (⟦univBasedMapToUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace f⟧ :
          ZerothHomotopy (underBasedMapSpace X.toBasedSpace Y.toBasedSpace)))
      (fun _ _ hfg ↦ univUnderBasedMapSpacePathClass_eq_of_basedHomotopy hfg)
  invFun :=
    Quotient.lift
      (fun f : underBasedMapSpace X.toBasedSpace Y.toBasedSpace ↦
        ((Quotient.mk (basedHomotopySetoid X.toBasedSpace Y.toBasedSpace)
          ((univBasedMapEquivUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace).symm f)) :
            Ho*[X.toBasedSpace, Y.toBasedSpace]))
      (fun _ _ hfg ↦ pointedBasedHomotopyClassEqOfJoined X Y hfg)
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro f
    simpa using congrArg
      (fun g : X.toBasedSpace ⟶ Y.toBasedSpace ↦
        ((Quotient.mk (basedHomotopySetoid X.toBasedSpace Y.toBasedSpace) g) :
          Ho*[X.toBasedSpace, Y.toBasedSpace]))
      (univBasedMapToUnderBasedMapSpace_leftInverse X.toBasedSpace Y.toBasedSpace f)
  right_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro f
    simpa using congrArg
      (fun g : underBasedMapSpace X.toBasedSpace Y.toBasedSpace ↦
        (⟦g⟧ : ZerothHomotopy (underBasedMapSpace X.toBasedSpace Y.toBasedSpace)))
      (univBasedMapToUnderBasedMapSpace_rightInverse X.toBasedSpace Y.toBasedSpace f)

/-- Helper for Adjunction 8.2.6: on representatives, the `Ho* ≃ π₀` comparison for the chapter's
canonical `underBasedMapSpace` owner simply takes the path-component class of the same based map.
-/
@[simp] private theorem pointedBasedHomotopyClassesEquivPi0UnderBasedMapSpace_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : X.toBasedSpace ⟶ Y.toBasedSpace) :
    pointedBasedHomotopyClassesEquivPi0UnderBasedMapSpace X Y
        ((Quotient.mk (basedHomotopySetoid X.toBasedSpace Y.toBasedSpace) f) :
          Ho*[X.toBasedSpace, Y.toBasedSpace]) =
      (⟦univBasedMapToUnderBasedMapSpace X.toBasedSpace Y.toBasedSpace f⟧ :
        ZerothHomotopy (underBasedMapSpace X.toBasedSpace Y.toBasedSpace)) :=
  rfl

/-- Companion equivalence on based homotopy classes
`[Σ X, Y] ≃ [X, Ω Y]` through the chapter's canonical `Ho*` owner. -/
def suspensionLoopAdjunctionBasedHomotopyClassesEquiv
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Ho*[((Σ X).toBasedSpace), Y.toBasedSpace] ≃ Ho*[X.toBasedSpace, (Ω Y).toBasedSpace] :=
  -- Compare `Ho*` to path components through the chapter's canonical `underBasedMapSpace` owner,
  -- then apply the suspension-loop homeomorphism transported to that owner.
  (pointedBasedHomotopyClassesEquivPi0UnderBasedMapSpace (Σ X) Y).trans <|
    (zerothHomotopyEquivOfHomeomorph
      (suspensionLoopAdjunctionUnderBasedMapSpaceHomeomorph X Y)).trans <|
      (pointedBasedHomotopyClassesEquivPi0UnderBasedMapSpace X (Ω Y)).symm

/-- Applying `suspensionLoopAdjunctionBasedHomotopyClassesEquiv` to the class of a based map
`f : ΣX → Y` returns the class of its adjoint based map `X → ΩY`. -/
@[simp]
theorem suspensionLoopAdjunctionBasedHomotopyClassesEquiv_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f : basedMappingSpace (Σ X) Y) :
    suspensionLoopAdjunctionBasedHomotopyClassesEquiv X Y
        ((Quotient.mk (basedHomotopySetoid ((Σ X).toBasedSpace) Y.toBasedSpace)
          (basedMappingSpaceToBasedMap (Σ X) Y f)) :
            Ho*[((Σ X).toBasedSpace), Y.toBasedSpace]) =
      ((Quotient.mk (basedHomotopySetoid X.toBasedSpace ((Ω Y).toBasedSpace))
          (basedMappingSpaceToBasedMap X (Ω Y)
            (suspensionLoopAdjunctionHomeomorph X Y f))) :
        Ho*[X.toBasedSpace, (Ω Y).toBasedSpace]) := by
  -- Expand the `Ho* ≃ π₀ ≃ π₀ ≃ Ho*` composite to the explicit representative-level formula.
  change
    ((Quotient.mk (basedHomotopySetoid X.toBasedSpace ((Ω Y).toBasedSpace))
        ((univBasedMapEquivUnderBasedMapSpace X.toBasedSpace ((Ω Y).toBasedSpace)).symm
          ((suspensionLoopAdjunctionUnderBasedMapSpaceHomeomorph X Y)
            (univBasedMapToUnderBasedMapSpace ((Σ X).toBasedSpace) Y.toBasedSpace
              (basedMappingSpaceToBasedMap (Σ X) Y f))))) :
      Ho*[X.toBasedSpace, (Ω Y).toBasedSpace]) = _
  -- Both sides are definitionally the same based map after unfolding the owner identifications.
  rfl
