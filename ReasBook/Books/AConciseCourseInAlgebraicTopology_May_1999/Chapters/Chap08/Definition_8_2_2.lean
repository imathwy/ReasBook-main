import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2

open CategoryTheory Limits
open Equiv
open scoped unitInterval

universe u v w

noncomputable section

-- Source-facing owner: Definition 8.2.2 keeps the interval-quotient model on `X × I` and records
-- the textbook `X ∧ S^1` meaning through the interval-boundary presentation `S^1 = I/∂I`.

private instance uliftUCompactlyGeneratedSpace
    (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{v} X] :
    UCompactlyGeneratedSpace.{v} (ULift.{w} X) := by
  refine uCompactlyGeneratedSpace_of_coinduced continuous_uliftUp ?_
  change TopologicalSpace.induced ULift.down ‹TopologicalSpace X› =
      TopologicalSpace.coinduced ULift.up ‹TopologicalSpace X›
  exact congrArg (fun t ↦ t ‹TopologicalSpace X›)
    (induced_symm Equiv.ulift.symm)

/-- Helper for Definition 8.2.2: products with the compact interval preserve compact generation.

This is the specific product case needed to show that the raw quotient model of `ΣX` is already
compactly generated before the public `k`-ification is chosen. -/
private theorem uCompactlyGeneratedSpace_prod_unitInterval
    (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (X × I) := by
  -- Prove continuity on `X × I` by currying into the compact-open space `C(I, Y)`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Y tY f hf
  let F : X → C(I, Y) := fun x =>
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

/-- Helper for Definition 8.2.2: the `k`-ification of any topology is compactly generated. -/
private theorem uCompactlyGeneratedSpace_compactlyGenerated
    (X : Type w) [TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{u} X (TopologicalSpace.compactlyGenerated.{u} X) := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun x ↦ x.1.2 x.2
  -- The coinduced presentation of `TopologicalSpace.compactlyGenerated` gives the instance.
  have hf :
      @Continuous ((Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst)) X
        instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{u, _, _}
    ((Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst)) X instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- The endpoint-collapse relation on `I`, identifying the boundary `∂I = {0, 1}` to one point. -/
def intervalBoundaryCircleRel : I → I → Prop :=
  fun s t ↦ s = t ∨ (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)

/-- The interval-endpoint relation presenting `S^1 = I/∂I` is an equivalence relation. -/
theorem intervalBoundaryCircleRel_equivalence :
    Equivalence intervalBoundaryCircleRel := by
  refine ⟨?_, ?_, ?_⟩
  · -- Every point is related to itself by the equality branch.
    intro t
    exact Or.inl rfl
  · -- Swapping the endpoints data preserves the symmetric collapse branch.
    intro s t hst
    rcases hst with rfl | hst
    · exact Or.inl rfl
    · exact Or.inr ⟨hst.2, hst.1⟩
  · -- Two collapse-step relations compose because the boundary condition is shared.
    intro s t u hst htu
    rcases hst with rfl | hst
    · exact htu
    rcases htu with rfl | htu
    · exact Or.inr ⟨hst.1, hst.2⟩
    · exact Or.inr ⟨hst.1, htu.2⟩

/-- The setoid on `I` collapsing the boundary to obtain the interval-quotient circle. -/
def intervalBoundaryCircleSetoid : Setoid I where
  r := intervalBoundaryCircleRel
  iseqv := intervalBoundaryCircleRel_equivalence

/-- The quotient carrier of the interval-boundary presentation `S^1 = I/∂I`, lifted to universe
`w` so it can serve as a smash-product factor for `PointedCompactlyGenerated.{u, w}`. -/
private abbrev intervalBoundaryCircleType :=
  ULift.{w} (Quotient intervalBoundaryCircleSetoid)

/-- The quotient map `I → I/∂I` presenting the interval-boundary circle. -/
private def intervalBoundaryCircleMkRaw : I → intervalBoundaryCircleType :=
  fun t ↦ ULift.up (Quotient.mk intervalBoundaryCircleSetoid t)

/-- The distinguished basepoint of `I/∂I`, represented by the boundary of `I`. -/
private def intervalBoundaryCirclePoint : intervalBoundaryCircleType :=
  intervalBoundaryCircleMkRaw 0

/-- The based compactly generated circle presented as the interval-boundary quotient `I/∂I`. -/
def intervalBoundaryCircle : PointedCompactlyGenerated.{w, w} :=
  PointedCompactlyGenerated.of.{w, w}
    (CompactlyGenerated.of.{w, w} intervalBoundaryCircleType)
    intervalBoundaryCirclePoint

/-- The quotient map `I → I/∂I` presenting the interval-boundary circle. -/
abbrev intervalBoundaryCircleMk : I → intervalBoundaryCircle.toCompactlyGenerated :=
  intervalBoundaryCircleMkRaw

/-- Passing from pointed compactly generated spaces to based spaces preserves the chosen
basepoint. -/
@[simp] private theorem underTopBasepoint_toBasedSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    underTopBasepoint X.toBasedSpace = X.point := by
  rfl

/-- The endpoint `1 : I` represents the same point of `I/∂I` as `0 : I`. -/
@[simp] private theorem intervalBoundaryCircleMk_one :
    intervalBoundaryCircleMk 1 = intervalBoundaryCircle.point := by
  change ULift.up (Quotient.mk intervalBoundaryCircleSetoid 1) =
      ULift.up (Quotient.mk intervalBoundaryCircleSetoid 0)
  exact congrArg ULift.up <|
    Quotient.sound <| Or.inr ⟨Or.inr rfl, Or.inl rfl⟩

/-- A point of `I` represents the basepoint of `intervalBoundaryCircle` exactly when it lies in
the boundary `∂I = {0, 1}`. -/
theorem intervalBoundaryCircleMk_eq_point_iff (t : I) :
    intervalBoundaryCircleMk t = intervalBoundaryCircle.point ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro ht
    -- Strip off the `ULift` wrapper and read equality in the quotient as the defining relation.
    change ULift.up (Quotient.mk intervalBoundaryCircleSetoid t) =
        ULift.up (Quotient.mk intervalBoundaryCircleSetoid 0) at ht
    injection ht with hq
    rw [Quotient.eq] at hq
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · exact hq.1
  · intro ht
    -- Each endpoint is sent to the distinguished quotient class.
    rcases ht with rfl | rfl
    · rfl
    · simpa using intervalBoundaryCircleMk_one

/-- The subset of `X × I` collapsed to the basepoint in the interval model of the reduced
suspension. -/
def reducedSuspensionCollapsedSet (X : PointedCompactlyGenerated.{u, w}) :
    Set (X.toCompactlyGenerated × I) :=
  { p | p.1 = X.point ∨ p.2 = 0 ∨ p.2 = 1 }

/-- The interval-collapse relation used to model the reduced suspension. -/
def reducedSuspensionRel (X : PointedCompactlyGenerated.{u, w}) :
    X.toCompactlyGenerated × I → X.toCompactlyGenerated × I → Prop :=
  fun p q ↦ p = q ∨ (p ∈ reducedSuspensionCollapsedSet X ∧ q ∈ reducedSuspensionCollapsedSet X)

/-- The interval-collapse relation defining the reduced suspension is an equivalence relation. -/
theorem reducedSuspensionRel_equivalence (X : PointedCompactlyGenerated.{u, w}) :
    Equivalence (reducedSuspensionRel X) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Equality makes the relation reflexive on every representative.
    intro p
    exact Or.inl rfl
  · -- The collapsed-subset branch is symmetric by swapping the witnesses.
    intro p q hpq
    rcases hpq with rfl | hpq
    · exact Or.inl rfl
    · exact Or.inr ⟨hpq.2, hpq.1⟩
  · -- Two collapse-step relations compose because the middle representative stays collapsed.
    intro p q r hpq hqr
    rcases hpq with rfl | hpq
    · exact hqr
    rcases hqr with rfl | hqr
    · exact Or.inr ⟨hpq.1, hpq.2⟩
    · exact Or.inr ⟨hpq.1, hqr.2⟩

/-- The setoid on `X × I` whose quotient is the reduced suspension. -/
def reducedSuspensionSetoid (X : PointedCompactlyGenerated.{u, w}) :
    Setoid (X.toCompactlyGenerated × I) where
  r := reducedSuspensionRel X
  iseqv := reducedSuspensionRel_equivalence X

/-- The quotient carrier underlying `reducedSuspension X`. -/
abbrev reducedSuspensionType (X : PointedCompactlyGenerated.{u, w}) :=
  Quotient (reducedSuspensionSetoid X)

/-- The quotient topology on `reducedSuspensionType X` before applying compact generation. -/
abbrev reducedSuspensionTypeQuotTopologicalSpace (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedSuspensionType X) :=
  inferInstance

/-- The compactly generated replacement of the raw quotient topology on `reducedSuspensionType X`.
-/
abbrev reducedSuspensionTypeKTopologicalSpace (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedSuspensionType X) :=
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  TopologicalSpace.compactlyGenerated.{u, w} (reducedSuspensionType X)

/-- Helper for Definition 8.2.2: the raw quotient topology on `reducedSuspensionType X` is
already compactly generated. -/
private theorem reducedSuspensionTypeQuot_eq_kTopologicalSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionTypeQuotTopologicalSpace X = reducedSuspensionTypeKTopologicalSpace X := by
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  let _ : UCompactlyGeneratedSpace.{u} (reducedSuspensionType X) := by
    let X' : Type w := X.toCompactlyGenerated
    let _ : TopologicalSpace X' := inferInstanceAs (TopologicalSpace X.toCompactlyGenerated)
    let _ : UCompactlyGeneratedSpace.{u} X' :=
      inferInstanceAs (UCompactlyGeneratedSpace X.toCompactlyGenerated)
    have hprod : UCompactlyGeneratedSpace.{u} (X' × I) :=
      uCompactlyGeneratedSpace_prod_unitInterval (X := X')
    let _ : UCompactlyGeneratedSpace.{u} (X' × I) := hprod
    infer_instance
  -- The quotient topology is already compactly generated, so it equals its `k`-ification.
  simpa [reducedSuspensionTypeKTopologicalSpace] using
    (eq_compactlyGenerated (X := reducedSuspensionType X))

section ReducedSuspensionKification

variable (X : PointedCompactlyGenerated.{u, w})

local instance reducedSuspensionTypeTopologicalSpace :
    TopologicalSpace (reducedSuspensionType X) :=
  reducedSuspensionTypeKTopologicalSpace X

local instance reducedSuspensionTypeUCompactlyGeneratedSpace :
    UCompactlyGeneratedSpace.{u} (reducedSuspensionType X) := by
  -- The chosen public topology on `reducedSuspensionType X` is a `k`-ification by definition.
  simpa [reducedSuspensionTypeKTopologicalSpace] using
    (@uCompactlyGeneratedSpace_compactlyGenerated
      (reducedSuspensionType X) (reducedSuspensionTypeQuotTopologicalSpace X))

/-- The quotient map `X × I → ΣX` for the interval model of the reduced suspension. -/
def reducedSuspensionMk (X : PointedCompactlyGenerated.{u, w}) :
    X.toCompactlyGenerated × I → reducedSuspensionType X :=
  fun p ↦ Quotient.mk (reducedSuspensionSetoid X) p

/-- The distinguished basepoint of the reduced suspension, represented by the collapsed subset. -/
def reducedSuspensionPoint (X : PointedCompactlyGenerated.{u, w}) : reducedSuspensionType X :=
  reducedSuspensionMk X (X.point, 0)

/-- Definition 8.2.2: for a based compactly generated space `X`, the reduced suspension `ΣX` is
the quotient of `X × I` obtained by collapsing `X × {0}`, `X × {1}`, and the basepoint segment
`{x₀} × I`; equivalently, this is the smash product `X ∧ S^1` with `S^1` viewed as `I/∂I`. -/
def reducedSuspension (X : PointedCompactlyGenerated.{u, w}) : PointedCompactlyGenerated :=
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (reducedSuspensionType X))
    (reducedSuspensionPoint X)

prefix:max "Σ " => reducedSuspension

/-- The reduced suspension is the based compactly generated quotient of `X × I` by
`reducedSuspensionSetoid X`. -/
theorem reducedSuspension_def (X : PointedCompactlyGenerated.{u, w}) :
    Σ X =
      PointedCompactlyGenerated.of
        (CompactlyGenerated.of (reducedSuspensionType X))
        (reducedSuspensionPoint X) := rfl

/-- The interval-collapse locus for `reducedSuspension X` is exactly the wedge locus for the
smash-product description `ΣX = X ∧ S^1`, where `intervalBoundaryCircle` presents `S^1 = I/∂I`. -/
theorem mem_reducedSuspensionCollapsedSet_iff (X : PointedCompactlyGenerated.{u, w})
    (p : X.toCompactlyGenerated × I) :
    p ∈ reducedSuspensionCollapsedSet X ↔
      p.1 = X.point ∨ intervalBoundaryCircleMk p.2 = intervalBoundaryCircle.point := by
  constructor
  · intro hp
    -- The interval endpoint cases become the circle basepoint via the quotient presentation.
    rcases hp with hx | ht | ht
    · exact Or.inl hx
    · exact Or.inr <| by rw [ht]; rfl
    · exact Or.inr <| by rw [ht]; simp
  · intro hp
    -- Rewriting the circle basepoint condition recovers the collapsed interval caps.
    rcases hp with hx | hz
    · exact Or.inl hx
    · rw [intervalBoundaryCircleMk_eq_point_iff] at hz
      rcases hz with ht | ht
      · exact Or.inr <| Or.inl ht
      · exact Or.inr <| Or.inr ht

/-- The chosen basepoint of `reducedSuspension X` is `reducedSuspensionPoint X`. -/
@[simp] theorem reducedSuspension_point (X : PointedCompactlyGenerated.{u, w}) :
    (Σ X).point = reducedSuspensionPoint X := rfl

/-- The quotient map `X × I → ΣX` for the interval model of the reduced suspension is
continuous. -/
theorem continuous_reducedSuspensionMk (X : PointedCompactlyGenerated.{u, w}) :
    Continuous fun p : X.toCompactlyGenerated × I ↦
      (reducedSuspensionMk X p : (Σ X).toCompactlyGenerated) := by
  -- First prove continuity for the raw quotient topology, then transport across the equality
  -- between the raw quotient topology and the chosen `k`-ification.
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  have hraw :
      Continuous fun p : X.toCompactlyGenerated × I ↦ reducedSuspensionMk X p := by
    simpa [reducedSuspensionMk] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (X.toCompactlyGenerated × I) (reducedSuspensionSetoid X)))
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeKTopologicalSpace X
  -- Rewrite the codomain topology from the raw quotient topology to the public `k`-ification.
  change @Continuous (X.toCompactlyGenerated × I) (reducedSuspensionType X)
      instTopologicalSpaceProd (reducedSuspensionTypeKTopologicalSpace X)
      (fun p : X.toCompactlyGenerated × I ↦ reducedSuspensionMk X p)
  rw [← reducedSuspensionTypeQuot_eq_kTopologicalSpace X]
  exact hraw

/-- Helper for Definition 8.2.2: the quotient map `I → I/∂I` is continuous. -/
private theorem continuous_intervalBoundaryCircleMk :
    Continuous intervalBoundaryCircleMk := by
  -- The public circle quotient map is `Quotient.mk'` followed by `ULift.up`.
  simpa [intervalBoundaryCircleMk, intervalBoundaryCircleMkRaw] using
    (continuous_uliftUp.comp (continuous_quotient_mk' :
      Continuous (@Quotient.mk' I intervalBoundaryCircleSetoid)))

/-- Helper for Definition 8.2.2: the interval-boundary quotient map is a quotient map. -/
private theorem intervalBoundaryCircleMkRaw_isQuotientMap :
    Topology.IsQuotientMap intervalBoundaryCircleMkRaw := by
  -- Compose the standard quotient projection with the `ULift` homeomorphism.
  simpa [intervalBoundaryCircleMkRaw, Function.comp] using
    (Topology.IsQuotientMap.comp Homeomorph.ulift.symm.isQuotientMap
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap (@Quotient.mk' I intervalBoundaryCircleSetoid)))

/-- Helper for Definition 8.2.2: a subset of `I` with matching endpoint membership is saturated
for the quotient `I → I/∂I`. -/
private theorem preimage_image_intervalBoundaryCircleMkRaw_eq
    {s : Set I} (hs : (0 : I) ∈ s ↔ (1 : I) ∈ s) :
    intervalBoundaryCircleMkRaw ⁻¹' (intervalBoundaryCircleMkRaw '' s) = s := by
  ext t
  constructor
  · rintro ⟨u, hu, htu⟩
    -- Read quotient equality in the orientation needed to compare `t` with a source witness `u`.
    have hq : Quotient.mk intervalBoundaryCircleSetoid t =
        Quotient.mk intervalBoundaryCircleSetoid u := by
      simpa [intervalBoundaryCircleMkRaw] using htu.symm
    rw [Quotient.eq] at hq
    rcases hq with rfl | htu
    · exact hu
    · rcases htu.1 with ht | ht
      · subst ht
        rcases htu.2 with rfl | rfl
        · exact hu
        · exact hs.mpr hu
      · subst ht
        rcases htu.2 with rfl | rfl
        · exact hs.mp hu
        · exact hu
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- Helper for Definition 8.2.2: saturated open subsets of `I` descend to open subsets of the
interval-boundary circle. -/
private theorem isOpen_image_intervalBoundaryCircleMkRaw
    {s : Set I} (hsOpen : IsOpen s) (hs : (0 : I) ∈ s ↔ (1 : I) ∈ s) :
    IsOpen (intervalBoundaryCircleMkRaw '' s) := by
  -- Quotient openness is checked by showing that the pullback of the image is the original open
  -- saturated set.
  refine intervalBoundaryCircleMkRaw_isQuotientMap.isOpen_preimage.mp ?_
  simpa [preimage_image_intervalBoundaryCircleMkRaw_eq hs] using hsOpen

/-- Helper for Definition 8.2.2: disjoint saturated subsets of `I` have disjoint images in the
interval-boundary quotient. -/
private theorem disjoint_image_intervalBoundaryCircleMkRaw
    {U V : Set I} (hU : (0 : I) ∈ U ↔ (1 : I) ∈ U) (_hV : (0 : I) ∈ V ↔ (1 : I) ∈ V)
    (hUV : Disjoint U V) :
    Disjoint (intervalBoundaryCircleMkRaw '' U) (intervalBoundaryCircleMkRaw '' V) := by
  -- Pull an intersection point back to `V`, then use saturation to show it already lies in `U`.
  refine Set.disjoint_left.2 ?_
  intro z hzU hzV
  rcases hzV with ⟨v, hv, rfl⟩
  have hvU : v ∈ U := by
    have hvImage : v ∈ intervalBoundaryCircleMkRaw ⁻¹' (intervalBoundaryCircleMkRaw '' U) := hzU
    simpa [preimage_image_intervalBoundaryCircleMkRaw_eq hU] using hvImage
  exact hUV.le_bot ⟨hvU, hv⟩

/-- Helper for Definition 8.2.2: distinct classes in `I/∂I` admit disjoint saturated open
neighborhoods in `I`. -/
private theorem intervalBoundaryCircleSeparatedNeighborhoods_endpointInterior
    {a b : I} (ha : a = 0 ∨ a = 1) (hb : ¬ (b = 0 ∨ b = 1)) :
    ∃ U V : Set I,
      IsOpen U ∧ IsOpen V ∧
        a ∈ U ∧ b ∈ V ∧ Disjoint U V ∧
          ((0 : I) ∈ U ↔ (1 : I) ∈ U) ∧ ((0 : I) ∈ V ↔ (1 : I) ∈ V) := by
  let r : ℝ := min (dist b 0) (dist b 1) / 2
  -- Hoist the endpoint-separation facts so the radius estimates can reuse them.
  have hb0_ne : b ≠ 0 := by
    intro hb0
    exact hb (Or.inl hb0)
  have hb1_ne : b ≠ 1 := by
    intro hb1
    exact hb (Or.inr hb1)
  have hb0 : 0 < dist b 0 := dist_pos.mpr hb0_ne
  have hb1 : 0 < dist b 1 := dist_pos.mpr hb1_ne
  have hr_lt_dist0 : r < dist (0 : I) b := by
    have hbound : r ≤ dist b 0 / 2 := by
      dsimp [r]
      nlinarith [min_le_left (dist b 0) (dist b 1)]
    have hhalf : dist b 0 / 2 < dist b 0 := by
      nlinarith
    simpa [dist_comm] using lt_of_le_of_lt hbound hhalf
  have hr_lt_dist1 : r < dist (1 : I) b := by
    have hbound : r ≤ dist b 1 / 2 := by
      dsimp [r]
      nlinarith [min_le_right (dist b 0) (dist b 1)]
    have hhalf : dist b 1 / 2 < dist b 1 := by
      nlinarith
    simpa [dist_comm] using lt_of_le_of_lt hbound hhalf
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨{ t | r < dist t b }, Metric.ball b r, ?_, Metric.isOpen_ball, ?_,
    by simpa [Metric.mem_ball] using hr_pos,
    ?_, ?_, ?_⟩
  · -- The basepoint neighborhood is the complement of the closed radius-`r` ball around `b`.
    simpa [r] using isOpen_lt continuous_const (continuous_id.dist continuous_const)
  · rcases ha with rfl | rfl
    · exact hr_lt_dist0
    · exact hr_lt_dist1
  · -- The two source neighborhoods are disjoint by construction.
    refine Set.disjoint_left.2 ?_
    intro t htU htV
    have htU' : r < dist t b := htU
    have htV' : dist t b < r := by
      simpa [Metric.mem_ball] using htV
    linarith
  · constructor
    · intro _
      exact hr_lt_dist1
    · intro _
      exact hr_lt_dist0
  · constructor
    · intro h0
      have : dist (0 : I) b < r := by
        simpa [Metric.mem_ball] using h0
      have hbound : r ≤ dist b 0 / 2 := by
        dsimp [r]
        nlinarith [min_le_left (dist b 0) (dist b 1)]
      have : dist b 0 < dist b 0 / 2 := by
        simpa [dist_comm] using lt_of_lt_of_le this hbound
      have hnonneg : 0 ≤ dist b 0 := dist_nonneg
      linarith
    · intro h1
      have : dist (1 : I) b < r := by
        simpa [Metric.mem_ball] using h1
      have hbound : r ≤ dist b 1 / 2 := by
        dsimp [r]
        nlinarith [min_le_right (dist b 0) (dist b 1)]
      have : dist b 1 < dist b 1 / 2 := by
        simpa [dist_comm] using lt_of_lt_of_le this hbound
      have hnonneg : 0 ≤ dist b 1 := dist_nonneg
      linarith

/-- Helper for Definition 8.2.2: distinct classes in `I/∂I` admit disjoint saturated open
neighborhoods in `I`. -/
private theorem intervalBoundaryCircleSeparatedNeighborhoods
    {a b : I} (hab : intervalBoundaryCircleMkRaw a ≠ intervalBoundaryCircleMkRaw b) :
    ∃ U V : Set I,
      IsOpen U ∧ IsOpen V ∧
        a ∈ U ∧ b ∈ V ∧ Disjoint U V ∧
          ((0 : I) ∈ U ↔ (1 : I) ∈ U) ∧ ((0 : I) ∈ V ↔ (1 : I) ∈ V) := by
  by_cases ha : a = 0 ∨ a = 1
  · have hb : ¬ (b = 0 ∨ b = 1) := by
      intro hb'
      rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact hab rfl
      · exact hab intervalBoundaryCircleMk_one.symm
      · exact hab intervalBoundaryCircleMk_one
      · exact hab rfl
    exact intervalBoundaryCircleSeparatedNeighborhoods_endpointInterior ha hb
  · by_cases hb : b = 0 ∨ b = 1
    · rcases intervalBoundaryCircleSeparatedNeighborhoods_endpointInterior
          (a := b) (b := a) hb ha with
        ⟨V, U, hVOpen, hUOpen, hbV, haU, hVU, hVEnds, hUEnds⟩
      exact ⟨U, V, hUOpen, hVOpen, haU, hbV, hVU.symm, hUEnds, hVEnds⟩
    · have hab_ne : a ≠ b := by
        intro hab'
        exact hab (by simpa [hab'])
      let ra : ℝ := min (dist a b / 3) (min (dist a 0) (dist a 1)) / 2
      let rb : ℝ := min (dist a b / 3) (min (dist b 0) (dist b 1)) / 2
      have hra_pos : 0 < ra := by
        have hab_dist : 0 < dist a b := dist_pos.mpr hab_ne
        have ha0 : 0 < dist a 0 := dist_pos.mpr (by
          intro ha0'
          exact ha (Or.inl ha0'))
        have ha1 : 0 < dist a 1 := dist_pos.mpr (by
          intro ha1'
          exact ha (Or.inr ha1'))
        dsimp [ra]
        positivity
      have hrb_pos : 0 < rb := by
        have hab_dist : 0 < dist a b := dist_pos.mpr hab_ne
        have hb0 : 0 < dist b 0 := dist_pos.mpr (by
          intro hb0'
          exact hb (Or.inl hb0'))
        have hb1 : 0 < dist b 1 := dist_pos.mpr (by
          intro hb1'
          exact hb (Or.inr hb1'))
        dsimp [rb]
        positivity
      refine ⟨Metric.ball a ra, Metric.ball b rb, Metric.isOpen_ball, Metric.isOpen_ball,
        by simpa [Metric.mem_ball] using hra_pos,
        by simpa [Metric.mem_ball] using hrb_pos, ?_, ?_, ?_⟩
      · -- Small metric balls around distinct interior representatives are disjoint.
        refine Set.disjoint_left.2 ?_
        intro t htU htV
        have htU' : dist a t < ra := by
          simpa [Metric.mem_ball, dist_comm] using htU
        have htV' : dist t b < rb := by
          simpa [Metric.mem_ball] using htV
        have hdist : dist a b < ra + rb := by
          have htriangle := dist_triangle a t b
          linarith
        have hra_bound : ra ≤ dist a b / 6 := by
          dsimp [ra]
          nlinarith [min_le_left (dist a b / 3) (min (dist a 0) (dist a 1))]
        have hrb_bound : rb ≤ dist a b / 6 := by
          dsimp [rb]
          nlinarith [min_le_left (dist a b / 3) (min (dist b 0) (dist b 1))]
        have hsum : ra + rb ≤ dist a b / 3 := by
          nlinarith
        have hdist_nonneg : 0 ≤ dist a b := dist_nonneg
        linarith
      · constructor
        · intro h0
          have : dist (0 : I) a < ra := by
            simpa [Metric.mem_ball] using h0
          have hbound : ra ≤ dist a 0 / 2 := by
            dsimp [ra]
            nlinarith [min_le_right (dist a b / 3) (min (dist a 0) (dist a 1)),
              min_le_left (dist a 0) (dist a 1)]
          have : dist a 0 < dist a 0 / 2 := by
            simpa [dist_comm] using lt_of_lt_of_le this hbound
          have hnonneg : 0 ≤ dist a 0 := dist_nonneg
          linarith
        · intro h1
          have : dist (1 : I) a < ra := by
            simpa [Metric.mem_ball] using h1
          have hbound : ra ≤ dist a 1 / 2 := by
            dsimp [ra]
            nlinarith [min_le_right (dist a b / 3) (min (dist a 0) (dist a 1)),
              min_le_right (dist a 0) (dist a 1)]
          have : dist a 1 < dist a 1 / 2 := by
            simpa [dist_comm] using lt_of_lt_of_le this hbound
          have hnonneg : 0 ≤ dist a 1 := dist_nonneg
          linarith
      · constructor
        · intro h0
          have : dist (0 : I) b < rb := by
            simpa [Metric.mem_ball] using h0
          have hbound : rb ≤ dist b 0 / 2 := by
            dsimp [rb]
            nlinarith [min_le_right (dist a b / 3) (min (dist b 0) (dist b 1)),
              min_le_left (dist b 0) (dist b 1)]
          have : dist b 0 < dist b 0 / 2 := by
            simpa [dist_comm] using lt_of_lt_of_le this hbound
          have hnonneg : 0 ≤ dist b 0 := dist_nonneg
          linarith
        · intro h1
          have : dist (1 : I) b < rb := by
            simpa [Metric.mem_ball] using h1
          have hbound : rb ≤ dist b 1 / 2 := by
            dsimp [rb]
            nlinarith [min_le_right (dist a b / 3) (min (dist b 0) (dist b 1)),
              min_le_right (dist b 0) (dist b 1)]
          have : dist b 1 < dist b 1 / 2 := by
            simpa [dist_comm] using lt_of_lt_of_le this hbound
          have hnonneg : 0 ≤ dist b 1 := dist_nonneg
          linarith

/-- Helper for Definition 8.2.2: the interval-boundary circle is Hausdorff. -/
private instance intervalBoundaryCircleT2Space :
    T2Space intervalBoundaryCircle.toCompactlyGenerated := by
  refine ⟨?_⟩
  intro x y hxy
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  rcases intervalBoundaryCircleSeparatedNeighborhoods hab with
    ⟨U, V, hUOpen, hVOpen, haU, hbV, hUV, hUEnds, hVEnds⟩
  refine ⟨intervalBoundaryCircleMkRaw '' U, intervalBoundaryCircleMkRaw '' V,
    isOpen_image_intervalBoundaryCircleMkRaw hUOpen hUEnds,
    isOpen_image_intervalBoundaryCircleMkRaw hVOpen hVEnds,
    ?_, ?_, disjoint_image_intervalBoundaryCircleMkRaw hUEnds hVEnds hUV⟩
  · exact ⟨a, haU, rfl⟩
  · exact ⟨b, hbV, rfl⟩

/-- Helper for Definition 8.2.2: the interval-boundary circle is locally compact. -/
private instance intervalBoundaryCircleLocallyCompactSpace :
    LocallyCompactSpace intervalBoundaryCircle.toCompactlyGenerated := by
  let _ : CompactSpace intervalBoundaryCircle.toCompactlyGenerated := by
    change CompactSpace intervalBoundaryCircleType
    infer_instance
  let _ : T2Space intervalBoundaryCircle.toCompactlyGenerated := intervalBoundaryCircleT2Space
  infer_instance

/-- Helper for Definition 8.2.2: the quotient map into a smash product is continuous. -/
private theorem continuous_smashProductMk
    (X : BasedSpace.{u}) (Y : BasedSpace.{w}) :
    Continuous (fun p : X.right × Y.right ↦ smashProductMk X Y p) := by
  -- The smash-product constructor is the quotient map for `smashProductRel`.
  simpa [smashProductMk, smashProductType] using
    (continuous_quotient_mk' :
      Continuous (@Quotient.mk' (smashProductPair X Y) (smashProductSetoid X Y)))

/-- For each `x : X`, the meridian `t ↦ reducedSuspensionMk X (x, t)` in `ΣX` is continuous. -/
theorem continuous_reducedSuspensionMk_meridian
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    Continuous fun t : I ↦ (reducedSuspensionMk X (x, t) : (Σ X).toCompactlyGenerated) := by
  simpa using (continuous_reducedSuspensionMk X).comp (Continuous.prodMk_right x)

/-- Any two points in the collapsed subset represent the same point of `ΣX`. -/
theorem reducedSuspensionMk_eq_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p q : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedSuspensionCollapsedSet X) (hq : q ∈ reducedSuspensionCollapsedSet X) :
    reducedSuspensionMk X p = reducedSuspensionMk X q :=
  Quotient.sound <| Or.inr ⟨hp, hq⟩

/-- Any point of the collapsed subset represents the distinguished basepoint of `ΣX`. -/
theorem reducedSuspensionMk_eq_point_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedSuspensionCollapsedSet X) :
    reducedSuspensionMk X p = reducedSuspensionPoint X := by
  simpa [reducedSuspensionPoint] using
    reducedSuspensionMk_eq_of_memCollapsedSet X hp (Or.inl rfl)

/-- Any point on the basepoint segment `{X.point} × I` represents the suspension basepoint. -/
@[simp] theorem reducedSuspensionMk_eq_point_of_fst_eq_point
    (X : PointedCompactlyGenerated.{u, w}) (t : I) :
    reducedSuspensionMk X (X.point, t) = reducedSuspensionPoint X := by
  exact reducedSuspensionMk_eq_point_of_memCollapsedSet X (Or.inl rfl)

/-- Any point on the lower cap `X × {0}` represents the suspension basepoint. -/
@[simp] theorem reducedSuspensionMk_eq_point_of_snd_eq_zero
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    reducedSuspensionMk X (x, 0) = reducedSuspensionPoint X := by
  exact reducedSuspensionMk_eq_point_of_memCollapsedSet X (Or.inr <| Or.inl rfl)

/-- Any point on the upper cap `X × {1}` represents the suspension basepoint. -/
@[simp] theorem reducedSuspensionMk_eq_point_of_snd_eq_one
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    reducedSuspensionMk X (x, 1) = reducedSuspensionPoint X := by
  exact reducedSuspensionMk_eq_point_of_memCollapsedSet X (Or.inr <| Or.inr rfl)

/-- The raw representative map from the interval quotient model of `ΣX` to the smash-product
presentation `X ∧ (I/∂I)`. -/
private def reducedSuspensionToSmashProductRaw (X : PointedCompactlyGenerated.{u, w}) :
    X.toCompactlyGenerated × I →
      (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right
  | p =>
      smashProductMk X.toBasedSpace intervalBoundaryCircle.toBasedSpace
        (p.1, intervalBoundaryCircleMk p.2)

/-- The raw map to `X ∧ (I/∂I)` is constant on the collapsed subset of the suspension quotient. -/
private theorem reducedSuspensionToSmashProductRaw_eq_basepoint_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedSuspensionCollapsedSet X) :
    reducedSuspensionToSmashProductRaw X p =
      smashProductMk X.toBasedSpace intervalBoundaryCircle.toBasedSpace
        (X.point, intervalBoundaryCircle.point) := by
  rcases p with ⟨x, t⟩
  refine smashProductMk_eq_of_rel X.toBasedSpace intervalBoundaryCircle.toBasedSpace ?_
  refine Or.inr ⟨?_, ?_⟩
  · rcases hp with hx | ht | ht
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by subst ht; rfl)
    · exact Or.inr (by subst ht; simp)
  · exact Or.inl (by simp)

/-- The smash-product representative map respects the suspension quotient relation. -/
private theorem reducedSuspensionToSmashProductRaw_respects
    (X : PointedCompactlyGenerated.{u, w}) :
    ∀ ⦃p q : X.toCompactlyGenerated × I⦄,
      reducedSuspensionRel X p q →
        reducedSuspensionToSmashProductRaw X p =
          reducedSuspensionToSmashProductRaw X q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (reducedSuspensionToSmashProductRaw_eq_basepoint_of_memCollapsedSet X hp).trans
        (reducedSuspensionToSmashProductRaw_eq_basepoint_of_memCollapsedSet X hq).symm

/-- Helper for Definition 8.2.2: the forward raw map respects the setoid spelling used by
`Quotient.lift`. -/
private theorem reducedSuspensionToSmashProductRaw_respects_setoid
    (X : PointedCompactlyGenerated.{u, w}) :
    ∀ ⦃p q : X.toCompactlyGenerated × I⦄,
      (reducedSuspensionSetoid X).r p q →
        reducedSuspensionToSmashProductRaw X p =
          reducedSuspensionToSmashProductRaw X q := by
  intro p q hpq
  exact reducedSuspensionToSmashProductRaw_respects X (by simpa [reducedSuspensionSetoid] using hpq)

/-- The raw representative map from `X × (I/∂I)` to the interval quotient model of `ΣX`. -/
private def smashProductToReducedSuspensionRaw (X : PointedCompactlyGenerated.{u, w}) :
    X.toBasedSpace.right × intervalBoundaryCircle.toBasedSpace.right → reducedSuspensionType X
  | (x, z) =>
      Quotient.lift
        (fun t : I ↦ reducedSuspensionMk X (x, t))
        (fun a b hab ↦ by
          rcases hab with rfl | ⟨ha, hb⟩
          · rfl
          · have ha' : reducedSuspensionMk X (x, a) = reducedSuspensionPoint X := by
              rcases ha with rfl | rfl
              · simp
              · simp
            have hb' : reducedSuspensionMk X (x, b) = reducedSuspensionPoint X := by
              rcases hb with rfl | rfl
              · simp
              · simp
            exact ha'.trans hb'.symm)
        z.down

/-- The raw inverse map sends the wedge locus of `X × (I/∂I)` to the suspension basepoint. -/
private theorem smashProductToReducedSuspensionRaw_eq_point_of_mem_smashWedge
    (X : PointedCompactlyGenerated.{u, w})
    {p : X.toBasedSpace.right × intervalBoundaryCircle.toBasedSpace.right}
    (hp : smashWedge X.toBasedSpace intervalBoundaryCircle.toBasedSpace p) :
    smashProductToReducedSuspensionRaw X p = reducedSuspensionPoint X := by
  rcases p with ⟨x, z⟩
  rcases hp with hx | hz
  · have hx' : x = X.point := by
      exact hx
    subst hx'
    rcases z with ⟨z⟩
    refine Quotient.inductionOn z ?_
    intro t
    simp [smashProductToReducedSuspensionRaw]
  · have hz' : z = intervalBoundaryCircle.point := by
      exact hz.trans (underTopBasepoint_toBasedSpace intervalBoundaryCircle)
    subst hz'
    change reducedSuspensionMk X (x, 0) = reducedSuspensionPoint X
    exact reducedSuspensionMk_eq_point_of_snd_eq_zero X x

/-- The map from `X × (I/∂I)` to `ΣX` respects the smash-product relation. -/
private theorem smashProductToReducedSuspensionRaw_respects
    (X : PointedCompactlyGenerated.{u, w}) :
    ∀ ⦃p q : X.toBasedSpace.right × intervalBoundaryCircle.toBasedSpace.right⦄,
      smashProductRel X.toBasedSpace intervalBoundaryCircle.toBasedSpace p q →
        smashProductToReducedSuspensionRaw X p =
          smashProductToReducedSuspensionRaw X q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · rfl
  · exact
      (smashProductToReducedSuspensionRaw_eq_point_of_mem_smashWedge X hp).trans
        (smashProductToReducedSuspensionRaw_eq_point_of_mem_smashWedge X hq).symm

/-- Helper for Definition 8.2.2: the representative map from `ΣX` into `X ∧ (I/∂I)` is
continuous before quotient descent. -/
private theorem continuous_reducedSuspensionToSmashProductRaw
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous (reducedSuspensionToSmashProductRaw X) := by
  -- The forward raw map is the smash-product quotient map after applying the circle quotient map.
  have hsnd :
      Continuous fun p : X.toCompactlyGenerated × I ↦ intervalBoundaryCircleMk p.2 :=
    continuous_intervalBoundaryCircleMk.comp continuous_snd
  exact
    (continuous_smashProductMk X.toBasedSpace intervalBoundaryCircle.toBasedSpace).comp
      (continuous_fst.prodMk hsnd)

/-- Helper for Definition 8.2.2: the representative map from `X × (I/∂I)` into `ΣX` is
continuous before quotient descent. -/
@[simp] private theorem smashProductToReducedSuspensionRaw_comp_intervalBoundaryCircleMkRaw
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) (t : I) :
    smashProductToReducedSuspensionRaw X (x, intervalBoundaryCircleMkRaw t) =
      reducedSuspensionMk X (x, t) := by
  -- On interval representatives, the quotient lift reduces definitionally.
  rfl

/-- Helper for Definition 8.2.2: each descended meridian on `I/∂I` is continuous. -/
private theorem continuous_smashProductToReducedSuspensionSlice
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    Continuous fun z : intervalBoundaryCircle.toCompactlyGenerated =>
      smashProductToReducedSuspensionRaw X (x, z) := by
  -- Reduce continuity on the quotient circle to continuity along interval representatives.
  change Continuous fun z : intervalBoundaryCircleType =>
      smashProductToReducedSuspensionRaw X (x, z)
  refine intervalBoundaryCircleMkRaw_isQuotientMap.continuous_iff.2 ?_
  simpa [Function.comp_def] using continuous_reducedSuspensionMk_meridian X x

/-- Helper for Definition 8.2.2: the descended meridians vary continuously with `x`. -/
private theorem continuous_smashProductToReducedSuspensionFamily
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous fun x : X.toCompactlyGenerated =>
      (⟨fun z : intervalBoundaryCircle.toCompactlyGenerated =>
          smashProductToReducedSuspensionRaw X (x, z),
        continuous_smashProductToReducedSuspensionSlice X x⟩ :
        C(intervalBoundaryCircle.toCompactlyGenerated, reducedSuspensionType X)) := by
  -- Test continuity after precomposing with compact Hausdorff probes on `X`.
  refine continuous_from_uCompactlyGeneratedSpace
    (fun x : X.toCompactlyGenerated =>
      (⟨fun z : intervalBoundaryCircle.toCompactlyGenerated =>
          smashProductToReducedSuspensionRaw X (x, z),
        continuous_smashProductToReducedSuspensionSlice X x⟩ :
        C(intervalBoundaryCircle.toCompactlyGenerated, reducedSuspensionType X))) ?_
  intro S g
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  -- Descend the interval coordinate using the quotient-map API on the compact probe `S`.
  refine intervalBoundaryCircleMkRaw_isQuotientMap.continuous_lift_prod_right ?_
  simpa [Function.comp_def] using
    (continuous_reducedSuspensionMk X).comp
      ((g.continuous.comp continuous_fst).prodMk continuous_snd)

private theorem continuous_smashProductToReducedSuspensionRaw
    (X : PointedCompactlyGenerated.{u, w}) :
    Continuous (smashProductToReducedSuspensionRaw X) := by
  -- Route correction: instead of rebuilding the product topology from scratch, uncurry the
  -- continuous family of descended meridians once the circle quotient is locally compact.
  change Continuous
    (fun p : X.toCompactlyGenerated × intervalBoundaryCircle.toCompactlyGenerated =>
      smashProductToReducedSuspensionRaw X p)
  let F : X.toCompactlyGenerated →
      C(intervalBoundaryCircle.toCompactlyGenerated, reducedSuspensionType X) :=
    fun x =>
      ⟨fun z ↦ smashProductToReducedSuspensionRaw X (x, z),
        continuous_smashProductToReducedSuspensionSlice X x⟩
  have hF : Continuous F := by
    simpa [F] using continuous_smashProductToReducedSuspensionFamily X
  simpa [F, Function.uncurry] using
    (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩)

/-- The quotient model `ΣX` is canonically homeomorphic to the smash product `X ∧ S^1`, with
`S^1` presented by `intervalBoundaryCircle = I/∂I`. -/
noncomputable def reducedSuspensionSmashProductHomeomorph
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionType X ≃ₜ
      (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right where
  toEquiv :=
    { toFun :=
        show reducedSuspensionType X →
            (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right from
          Quotient.lift
            (reducedSuspensionToSmashProductRaw X)
            (fun _ _ h ↦ reducedSuspensionToSmashProductRaw_respects_setoid X h)
      invFun :=
        show (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right →
            reducedSuspensionType X from
          Quotient.lift
            (smashProductToReducedSuspensionRaw X)
            (fun _ _ h ↦ smashProductToReducedSuspensionRaw_respects X h)
      left_inv := by
        intro z
        -- Quotient induction reduces the inverse law to the representative formula.
        refine Quotient.inductionOn z ?_
        intro p
        rfl
      right_inv := by
        intro z
        -- A second quotient induction on the circle factor makes the formula definitional.
        refine Quotient.inductionOn z ?_
        intro p
        rcases p with ⟨x, z⟩
        rcases z with ⟨z⟩
        refine Quotient.inductionOn z ?_
        intro t
        rfl }
  continuous_toFun := by
    -- First descend from representatives for the raw quotient topology, then rewrite to `k`.
    let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
    have hraw :
        Continuous
          (show reducedSuspensionType X →
              (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right from
            Quotient.lift
              (reducedSuspensionToSmashProductRaw X)
              (fun _ _ h ↦ reducedSuspensionToSmashProductRaw_respects_setoid X h)) := by
      exact
        (continuous_reducedSuspensionToSmashProductRaw X).quotient_lift
          (fun a b h ↦ by
            simpa [reducedSuspensionSetoid] using
              reducedSuspensionToSmashProductRaw_respects X h)
    let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeKTopologicalSpace X
    change @Continuous (reducedSuspensionType X)
        (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right
        (reducedSuspensionTypeKTopologicalSpace X) inferInstance
        (show reducedSuspensionType X →
            (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).right from
          Quotient.lift
            (reducedSuspensionToSmashProductRaw X)
            (fun _ _ h ↦ reducedSuspensionToSmashProductRaw_respects_setoid X h))
    rw [← reducedSuspensionTypeQuot_eq_kTopologicalSpace X]
    exact hraw
  continuous_invFun := by
    -- Descend continuity from the representative-level inverse map.
    exact
      (continuous_smashProductToReducedSuspensionRaw X).quotient_lift
        (fun a b h ↦ by
          simpa [smashProductSetoid] using smashProductToReducedSuspensionRaw_respects X h)

/-- On representatives, `reducedSuspensionSmashProductHomeomorph` sends `[(x, t)]` in `ΣX` to the
smash-product class of `(x, [t])` in `X ∧ (I/∂I)`. -/
@[simp] theorem reducedSuspensionSmashProductHomeomorph_apply_mk
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) (t : I) :
    reducedSuspensionSmashProductHomeomorph X (reducedSuspensionMk X (x, t)) =
      smashProductMk X.toBasedSpace intervalBoundaryCircle.toBasedSpace
        (x, intervalBoundaryCircleMk t) := by
  rfl

/-- The homeomorphism identifying `ΣX` with `X ∧ S^1` preserves the distinguished basepoint. -/
@[simp] theorem reducedSuspensionSmashProductHomeomorph_basepoint
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionSmashProductHomeomorph X
        (reducedSuspensionPoint X) =
      smashProductMk X.toBasedSpace intervalBoundaryCircle.toBasedSpace
        (X.point, intervalBoundaryCircle.point) := by
  rfl

/-- The topological isomorphism underlying the suspension-smash identification preserves the
structure maps from the one-point space. -/
theorem reducedSuspensionIsoSmashProduct_w (X : PointedCompactlyGenerated.{u, w}) :
    (reducedSuspension X).toBasedSpace.hom ≫
        (TopCat.isoOfHomeo (reducedSuspensionSmashProductHomeomorph X)).hom =
      (smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace).hom := by
  -- Both structure maps are constant at the common basepoint identified above.
  ext x
  simpa using reducedSuspensionSmashProductHomeomorph_basepoint X

/-- Definition 8.2.2, equivalently: the based-space realization of `ΣX` is canonically identified
with the smash product `X ∧ S^1`, where `intervalBoundaryCircle` presents `S^1 = I/∂I`. -/
noncomputable def reducedSuspensionIsoSmashProduct
    (X : PointedCompactlyGenerated.{u, w}) :
    (reducedSuspension X).toBasedSpace ≅
      smashProduct X.toBasedSpace intervalBoundaryCircle.toBasedSpace :=
  Under.isoMk
    (TopCat.isoOfHomeo (reducedSuspensionSmashProductHomeomorph X))
    (reducedSuspensionIsoSmashProduct_w X)

/-- The forward morphism of `reducedSuspensionIsoSmashProduct` is induced by
`reducedSuspensionSmashProductHomeomorph`. -/
theorem reducedSuspensionIsoSmashProduct_hom_right
    (X : PointedCompactlyGenerated.{u, w}) :
    (reducedSuspensionIsoSmashProduct X).hom.right =
      (TopCat.isoOfHomeo (reducedSuspensionSmashProductHomeomorph X)).hom := by
  rfl

end ReducedSuspensionKification

namespace PointedCompactlyGenerated

/-- The prequotient map on `X × I` induced by a based map `f : X ⟶ Y`. -/
private def reducedSuspensionMapPrequotient
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    X.toCompactlyGenerated × I → Y.toCompactlyGenerated × I :=
  fun p ↦ (ConcreteCategory.hom (Hom.hom f) p.1, p.2)

/-- The prequotient map induced by a based map is continuous. -/
private theorem reducedSuspensionMapPrequotient_continuous
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    Continuous (reducedSuspensionMapPrequotient f) := by
  -- The induced map acts continuously on the space coordinate and leaves the interval unchanged.
  have hfst :
      Continuous fun p : X.toCompactlyGenerated × I ↦
        ConcreteCategory.hom (Hom.hom f) p.1 := by
    exact (Hom.hom f).hom.hom.continuous.comp continuous_fst
  -- Pair the continuous map on the space coordinate with the unchanged interval coordinate.
  change Continuous
    (fun p : X.toCompactlyGenerated × I ↦ (ConcreteCategory.hom (Hom.hom f) p.1, p.2))
  exact hfst.prodMk continuous_snd

/-- The prequotient map induced by a based map respects the reduced-suspension collapse relation. -/
private theorem reducedSuspensionMapPrequotient_respects
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    ∀ p q : X.toCompactlyGenerated × I,
      reducedSuspensionRel X p q →
        reducedSuspensionRel Y
          (reducedSuspensionMapPrequotient f p)
          (reducedSuspensionMapPrequotient f q) := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hp with hx | ht | ht
      · left
        simpa [reducedSuspensionMapPrequotient, hx] using Hom.map_point f
      · right
        left
        simpa [reducedSuspensionMapPrequotient, ht]
      · right
        right
        simpa [reducedSuspensionMapPrequotient, ht]
    · rcases hq with hx | ht | ht
      · left
        simpa [reducedSuspensionMapPrequotient, hx] using Hom.map_point f
      · right
        left
        simpa [reducedSuspensionMapPrequotient, ht]
      · right
        right
        simpa [reducedSuspensionMapPrequotient, ht]

/-- Helper for Definition 8.2.2: the induced prequotient map respects the setoid spelling used by
`Quotient.map'`. -/
private theorem reducedSuspensionMapPrequotient_respects_setoid
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    ∀ a b, (reducedSuspensionSetoid X).r a b →
      (reducedSuspensionSetoid Y).r
        (reducedSuspensionMapPrequotient f a)
        (reducedSuspensionMapPrequotient f b) := by
  intro a b hab
  exact reducedSuspensionMapPrequotient_respects f a b
    (by simpa [reducedSuspensionSetoid] using hab)

/-- The map on reduced-suspension quotients induced by a based map. -/
private def reducedSuspensionMapFun
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    reducedSuspensionType X → reducedSuspensionType Y :=
  Quotient.map'
    (reducedSuspensionMapPrequotient f)
    (reducedSuspensionMapPrequotient_respects_setoid f)

/-- Definitional-equality pin: `reducedSuspensionMapFun f` is continuous for the compactly
generated topologies carried by `(Σ X).toCompactlyGenerated` and `(Σ Y).toCompactlyGenerated`,
not just for the raw quotient topologies on `reducedSuspensionType X` and
`reducedSuspensionType Y`. -/
private instance reducedSuspensionMapTopologicalSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedSuspensionType X) :=
  inferInstanceAs (TopologicalSpace ((Σ X).toCompactlyGenerated))

private instance reducedSuspensionMapUCompactlyGeneratedSpace
    (X : PointedCompactlyGenerated.{u, w}) :
    UCompactlyGeneratedSpace.{u} (reducedSuspensionType X) :=
  inferInstanceAs (UCompactlyGeneratedSpace ((Σ X).toCompactlyGenerated))

/-- The quotient map induced by a based map is continuous on reduced suspensions. -/
private theorem reducedSuspensionMapFun_continuous
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    Continuous (reducedSuspensionMapFun f) := by
  -- Prove continuity for the raw quotient topologies, then transport both sides to `k`.
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeQuotTopologicalSpace X
  let _ : TopologicalSpace (reducedSuspensionType Y) := reducedSuspensionTypeQuotTopologicalSpace Y
  have hraw : Continuous (reducedSuspensionMapFun f) := by
    simpa [reducedSuspensionMapFun] using
      (reducedSuspensionMapPrequotient_continuous f).quotient_map'
        (reducedSuspensionMapPrequotient_respects_setoid f)
  let _ : TopologicalSpace (reducedSuspensionType X) := reducedSuspensionTypeKTopologicalSpace X
  let _ : TopologicalSpace (reducedSuspensionType Y) := reducedSuspensionTypeKTopologicalSpace Y
  change @Continuous (reducedSuspensionType X) (reducedSuspensionType Y)
      (reducedSuspensionTypeKTopologicalSpace X) (reducedSuspensionTypeKTopologicalSpace Y)
      (reducedSuspensionMapFun f)
  rw [← reducedSuspensionTypeQuot_eq_kTopologicalSpace X,
    ← reducedSuspensionTypeQuot_eq_kTopologicalSpace Y]
  exact hraw

/-- The continuous map on reduced suspensions induced by a based map. -/
private def reducedSuspensionMapContinuousMap
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    C((Σ X).toCompactlyGenerated, (Σ Y).toCompactlyGenerated) :=
  { toFun := reducedSuspensionMapFun f
    continuous_toFun := reducedSuspensionMapFun_continuous f }

/-- The reduced-suspension quotient map induced by a based map preserves the distinguished
basepoint. -/
private theorem reducedSuspensionMap_w
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    CategoryTheory.CategoryStruct.comp (reducedSuspension X).hom
        (ConcreteCategory.ofHom (reducedSuspensionMapContinuousMap f)) =
      (reducedSuspension Y).hom := by
  -- Both maps send the unique point to the class represented by `(Y.point, 0)`.
  ext x
  change reducedSuspensionMapFun f (reducedSuspensionPoint X) = reducedSuspensionPoint Y
  change reducedSuspensionMk Y (ConcreteCategory.hom (Hom.hom f) X.point, 0) =
      reducedSuspensionMk Y (Y.point, 0)
  rw [Hom.map_point f]

/-- The based map on reduced suspensions induced by a based map `f : X ⟶ Y`. -/
def reducedSuspensionMap
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    reducedSuspension X ⟶ reducedSuspension Y :=
  Under.homMk
    (ConcreteCategory.ofHom (reducedSuspensionMapContinuousMap f))
    (reducedSuspensionMap_w f)

/-- Evaluating `reducedSuspensionMap f` on a suspension class applies `f` to the space coordinate
and leaves the interval coordinate fixed. -/
@[simp] theorem reducedSuspensionMap_hom_apply
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y)
    (p : X.toCompactlyGenerated × I) :
    Hom.hom (reducedSuspensionMap f) (reducedSuspensionMk X p) =
      reducedSuspensionMk Y (ConcreteCategory.hom (Hom.hom f) p.1, p.2) := by
  rfl

/-- Reduced suspension sends the identity based map to the identity morphism. -/
@[simp] theorem reducedSuspensionMap_id (X : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionMap (𝟙 X) = 𝟙 (reducedSuspension X) := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.ext
  apply ContinuousMap.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change Hom.hom (reducedSuspensionMap (𝟙 X)) (reducedSuspensionMk X p) = reducedSuspensionMk X p
  simp

/-- Reduced suspension sends a composite of based maps to the composite induced map. -/
@[simp] theorem reducedSuspensionMap_comp
    {X Y Z : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    reducedSuspensionMap (f ≫ g) = reducedSuspensionMap f ≫ reducedSuspensionMap g := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.ext
  apply ContinuousMap.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change
    Hom.hom (reducedSuspensionMap (f ≫ g)) (reducedSuspensionMk X p) =
      Hom.hom (reducedSuspensionMap g) (Hom.hom (reducedSuspensionMap f) (reducedSuspensionMk X p))
  simp

/-- Reduced suspension is an endofunctor on pointed compactly generated spaces. -/
def reducedSuspensionFunctor :
    PointedCompactlyGenerated.{u, w} ⥤ PointedCompactlyGenerated.{u, w} where
  obj := reducedSuspension
  map := reducedSuspensionMap
  map_id := reducedSuspensionMap_id
  map_comp := reducedSuspensionMap_comp

end PointedCompactlyGenerated
