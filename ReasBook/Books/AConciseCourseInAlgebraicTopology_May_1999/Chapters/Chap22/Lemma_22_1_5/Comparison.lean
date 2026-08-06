import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_4

universe u v w z

open scoped RestrictedProduct unitInterval Topology Topology.Homotopy

variable {ι : Type v}

-- `Definition_22_1_4.weakProduct` is the source-facing weak-product owner.
-- This file constructs an auxiliary direct-limit model and compares it to that owner.

/-- The degree-`n` homotopy group of the `i`th factor of the family `X`. -/
abbrev weakProductFactorHomotopyGroup
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :=
  π_ (n : ℕ) (X i).toCompactlyGenerated (X i).point

/-- A family of positive-degree homotopy classes has finite support when all but finitely many
coordinates are the identity element. -/
def hasFiniteHomotopySupport
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : ∀ i, weakProductFactorHomotopyGroup n X i) : Prop :=
  { i | f i ≠ 1 }.Finite

/-- The constant identity family has finite homotopy support. -/
theorem hasFiniteHomotopySupport_one
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    hasFiniteHomotopySupport n X (1 : ∀ i, weakProductFactorHomotopyGroup n X i) := by
  simp [hasFiniteHomotopySupport]

/-- The product of two finitely supported families of homotopy classes is finitely supported. -/
theorem hasFiniteHomotopySupport_mul
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    {f g : ∀ i, weakProductFactorHomotopyGroup n X i}
    (hf : hasFiniteHomotopySupport n X f) (hg : hasFiniteHomotopySupport n X g) :
    hasFiniteHomotopySupport n X (f * g) := by
  refine (hf.union hg).subset ?_
  intro i hi
  by_cases hfi : f i = 1
  · right
    intro hgi
    exact hi (by simp [Pi.mul_apply, hfi, hgi])
  · exact Or.inl hfi

/-- The inverse of a finitely supported family of homotopy classes is finitely supported. -/
theorem hasFiniteHomotopySupport_inv
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    {f : ∀ i, weakProductFactorHomotopyGroup n X i}
    (hf : hasFiniteHomotopySupport n X f) :
    hasFiniteHomotopySupport n X f⁻¹ := by
  refine hf.subset ?_
  intro i hi
  simpa using hi

/-- Finite homotopy support is the same as eventual membership in the trivial subgroup. -/
theorem hasFiniteHomotopySupport_iff_eventually
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : ∀ i, weakProductFactorHomotopyGroup n X i) :
    hasFiniteHomotopySupport n X f ↔
      ∀ᶠ i in Filter.cofinite,
        f i ∈ (⊥ : Subgroup (weakProductFactorHomotopyGroup n X i)) := by
  simp [hasFiniteHomotopySupport]

/-- The direct sum of the positive-degree homotopy groups of the factors of `X`, formalized as the
cofinite restricted product with respect to the trivial subgroup in each factor. -/
abbrev weakProductHomotopyGroupDirectSum
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :=
  Πʳ i, [weakProductFactorHomotopyGroup n X i,
    (⊥ : Subgroup (weakProductFactorHomotopyGroup n X i))]

/-- Every element of `weakProductHomotopyGroupDirectSum n X` has finite support. -/
theorem weakProductHomotopyGroupDirectSum_hasFiniteSupport
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    hasFiniteHomotopySupport n X f :=
  (hasFiniteHomotopySupport_iff_eventually n X f).2 <| by
    simpa using f.eventually

/-- A point of a finite stage of the weak direct system is a choice of finitely many coordinates
together with a point in each chosen factor. -/
abbrev weakProductFiniteStage (X : ι → PointedCompactlyGenerated.{u, w}) :=
  Σ s : Finset ι, (i : s) → (X i).toCompactlyGenerated

namespace weakProductFiniteStage

/-- Extend a finite-stage point by the distinguished basepoints outside the chosen stage. -/
noncomputable def extend (X : ι → PointedCompactlyGenerated.{u, w})
    (a : weakProductFiniteStage X) :
    ∀ i, (X i).toCompactlyGenerated :=
  by
    classical
    exact fun i ↦ if hi : i ∈ a.1 then a.2 ⟨i, hi⟩ else (X i).point

@[simp] theorem extend_of_mem
    (X : ι → PointedCompactlyGenerated.{u, w})
    (a : weakProductFiniteStage X) {i : ι} (hi : i ∈ a.1) :
    extend X a i = a.2 ⟨i, hi⟩ := by
  classical
  simp [extend, hi]

@[simp] theorem extend_of_not_mem
    (X : ι → PointedCompactlyGenerated.{u, w})
    (a : weakProductFiniteStage X) {i : ι} (hi : i ∉ a.1) :
    extend X a i = (X i).point := by
  classical
  simp [extend, hi]

/-- Two finite-stage representatives define the same direct-limit point when their extensions to
the full family agree coordinatewise. -/
def setoid (X : ι → PointedCompactlyGenerated.{u, w}) :
    Setoid (weakProductFiniteStage X) where
  r a b := extend X a = extend X b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c hab hbc
      exact hab.trans hbc

end weakProductFiniteStage

/-- The carrier of the direct-limit weak product is the quotient of the disjoint union of finite
stages by the relation identifying representatives with the same padded tuple. -/
abbrev weakProductDirectLimitCarrier (X : ι → PointedCompactlyGenerated.{u, w}) :=
  Quotient (weakProductFiniteStage.setoid X)

/-- The distinguished basepoint of the direct-limit weak product comes from the empty stage. -/
def weakProductDirectLimitPoint (X : ι → PointedCompactlyGenerated.{u, w}) :
    weakProductDirectLimitCarrier X :=
  Quotient.mk _ ⟨∅, fun i ↦ nomatch i.2⟩

/-- The `i`th coordinate of a direct-limit weak-product point. -/
noncomputable def weakProductDirectLimitCoordinate
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    weakProductDirectLimitCarrier X → (X i).toCompactlyGenerated :=
  Quotient.lift
    (fun a ↦ weakProductFiniteStage.extend X a i)
    (by
      intro a b h
      exact congrArg (fun f ↦ f i) h)

@[simp] theorem weakProductDirectLimitCoordinate_mk
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι)
    (a : weakProductFiniteStage X) :
    weakProductDirectLimitCoordinate X i (Quotient.mk _ a) =
      weakProductFiniteStage.extend X a i :=
  rfl

@[simp] theorem weakProductDirectLimitCoordinate_point
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    weakProductDirectLimitCoordinate X i (weakProductDirectLimitPoint X) = (X i).point := by
  classical
  simp [weakProductDirectLimitPoint, weakProductFiniteStage.extend]

/-- Helper: the `k`-ification of any topology is `UCompactlyGeneratedSpace`. -/
private theorem uCompactlyGeneratedSpace_compactlyGenerated
    (Y : Type z) [TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (TopologicalSpace.compactlyGenerated.{u} Y) := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst) → Y := fun y ↦ y.1.2 y.2
  have hf : @Continuous ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y
      instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{u, _, _}
    ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Lemma 22.1.5: a continuous map from a compact Hausdorff source remains continuous
after replacing the codomain by its compactly generated reflection. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators for the compactly generated topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Lemma 22.1.5: a compact Hausdorff source in `Type` can be `ULift`ed into
`CompHaus.{u}` before passing to the codomain's compactly generated reflection. -/
private theorem continuousSmallCompHausToCompactlyGenerated
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let f' : ULift.{u} K → Y := f ∘ ULift.down
  have hf' : Continuous f' := hf.comp continuous_uliftDown
  have hLift :
      @Continuous (ULift.{u} K) Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
        f' :=
    continuousCompHausToCompactlyGenerated hf'
  -- The `ULift` homeomorphism transfers the compact-source continuity back to `K`.
  exact
    @Continuous.comp K (ULift.{u} K) Y ‹TopologicalSpace K› inferInstance
      (TopologicalSpace.compactlyGenerated.{u, w} Y) ULift.up f'
      hLift continuous_uliftUp

/-- Helper for Lemma 22.1.5: a raw continuous map stays continuous after replacing both source and
target by their compactly generated reflections. -/
private theorem continuousCompactlyGeneratedOfContinuous
    {X : Type w} [TopologicalSpace X] {Y : Type w} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) :
    @Continuous X Y (TopologicalSpace.compactlyGenerated.{u, w} X)
      (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  have hprobe :
      ∀ (S : CompHaus.{u}) (g : C(S, X)),
        @Continuous S Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y) (f ∘ g) := by
    intro S g
    -- Each compact probe composite stays continuous after passing to the k-topology.
    simpa [Function.comp] using
      (continuousCompHausToCompactlyGenerated (hf.comp g.continuous) :
        @Continuous S Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y) (f ∘ g))
  -- It is enough to test continuity after precomposing with compact Hausdorff probes.
  exact
    (@continuous_from_compactlyGenerated X Y ‹TopologicalSpace X›
      (TopologicalSpace.compactlyGenerated.{u, w} Y) f hprobe :
      @Continuous X Y (TopologicalSpace.compactlyGenerated.{u, w} X)
        (TopologicalSpace.compactlyGenerated.{u, w} Y) f)

/-- The weak product of `X`, interpreted as the compactly generated direct limit of its finite
subproducts. -/
def weakProductDirectLimit (X : ι → PointedCompactlyGenerated.{u, w}) :
    PointedCompactlyGenerated :=
  let t0 : TopologicalSpace (weakProductDirectLimitCarrier X) := inferInstance
  -- This owner is packaged with the compactly generated reflection.
  -- Local instance justification (defeq pin): the quotient-coordinate API still uses `t0`.
  letI : TopologicalSpace (weakProductDirectLimitCarrier X) :=
    @TopologicalSpace.compactlyGenerated.{u} (weakProductDirectLimitCarrier X) t0
  -- This definition also needs the witness for the switched topology.
  -- Local instance justification (defeq pin): only this local owner should carry that witness.
  letI : UCompactlyGeneratedSpace.{u} (weakProductDirectLimitCarrier X) :=
    @uCompactlyGeneratedSpace_compactlyGenerated (weakProductDirectLimitCarrier X) t0
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (weakProductDirectLimitCarrier X))
    (weakProductDirectLimitPoint X)

/-- The compact-factorization condition needed to compare the subspace-topology weak product
with its finite-stage direct-limit model: every map from a compact Hausdorff source has all of its
coordinates supported on one finite set. The condition applies both to sphere representatives and
to compact cylinders, so it controls surjectivity and injectivity on homotopy classes. -/
class WeakProductHasFiniteStageCompactFactorization
    (X : ι → PointedCompactlyGenerated.{u, w}) : Prop where
  factor :
    ∀ (S : CompHaus.{u})
      (f : C(S, (weakProduct X).toCompactlyGenerated)),
      ∃ s : Finset ι,
        ∃ g : C(S, (i : s) → (X i).toCompactlyGenerated),
          ∀ y,
            (show weakProductType X from f y).1 =
              weakProductFiniteStage.extend X ⟨s, g y⟩

/-- Extending a finite-stage point produces a finite-support point of the source-facing weak
product. -/
private theorem weakProductFiniteStage_extend_hasFiniteNonbasepointSupport
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X) :
    hasFiniteNonbasepointSupport X (weakProductFiniteStage.extend X a) := by
  classical
  refine a.1.finite_toSet.subset ?_
  intro i hi
  by_contra hnot
  exact hi (weakProductFiniteStage.extend_of_not_mem X a hnot)

/-- Interpret a direct-limit weak-product point as the corresponding finite-support tuple in the
source-facing weak-product owner of Definition 22.1.4. -/
private noncomputable def weakProductDirectLimitToWeakProductFun
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    weakProductDirectLimitCarrier X → weakProductType X :=
  Quotient.lift
    (fun a ↦
      ⟨weakProductFiniteStage.extend X a,
        weakProductFiniteStage_extend_hasFiniteNonbasepointSupport X a⟩)
    (by
      intro a b h
      exact Subtype.ext h)

/-- Interpret a finite-support tuple as the corresponding point of the direct-limit weak-product
quotient. -/
private noncomputable def weakProductToWeakProductDirectLimitFun
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    weakProductType X → weakProductDirectLimitCarrier X :=
  fun x ↦
    Quotient.mk _ ⟨x.2.toFinset, fun i ↦ x.1 i⟩

/-- Helper for Lemma 22.1.5: the source-facing weak product embeds into the direct-limit model and
then back without changing the underlying finite-support tuple. -/
private theorem weakProductComparison_leftInverse
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    Function.LeftInverse
      (weakProductDirectLimitToWeakProductFun X)
      (weakProductToWeakProductDirectLimitFun X) := by
  intro x
  -- Compare coordinates with the finite support recovered from `x`.
  apply Subtype.ext
  funext i
  classical
  have hmem : i ∈ x.2.toFinset ↔ x.1 i ≠ (X i).point := by
    simpa [hasFiniteNonbasepointSupport] using (x.2.mem_toFinset i)
  by_cases hx : x.1 i = (X i).point
  · have hi : i ∉ x.2.toFinset := by
      simpa [hx] using (not_congr hmem).2 hx
    simp [weakProductDirectLimitToWeakProductFun, weakProductToWeakProductDirectLimitFun,
      weakProductFiniteStage.extend, hi, hx]
  · have hi : i ∈ x.2.toFinset := by
      exact hmem.2 hx
    simp [weakProductDirectLimitToWeakProductFun, weakProductToWeakProductDirectLimitFun,
      weakProductFiniteStage.extend, hi]

/-- Helper for Lemma 22.1.5: the finite stage cut out by the support of
`weakProductFiniteStage.extend X a` represents the same direct-limit point as `a`. -/
private theorem weakProductFiniteStageSupportQuotientEq
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X) :
    Quotient.mk (weakProductFiniteStage.setoid X)
        ⟨(weakProductFiniteStage_extend_hasFiniteNonbasepointSupport X a).toFinset,
        fun i ↦ weakProductFiniteStage.extend X a i⟩ =
      Quotient.mk (weakProductFiniteStage.setoid X) a := by
  classical
  let b : weakProductFiniteStage X :=
    ⟨(weakProductFiniteStage_extend_hasFiniteNonbasepointSupport X a).toFinset,
      fun i ↦ weakProductFiniteStage.extend X a i⟩
  -- Compare the two quotient representatives coordinatewise after extension.
  apply Quotient.sound
  change weakProductFiniteStage.extend X b = weakProductFiniteStage.extend X a
  funext i
  by_cases hi : i ∈ b.1
  · -- On support coordinates, the support-stage representative reads off the original value.
    rw [weakProductFiniteStage.extend_of_mem X b hi]
  · -- Off the support, both padded tuples are the distinguished basepoint.
    have hbase : weakProductFiniteStage.extend X a i = (X i).point := by
      by_contra hne
      exact hi <|
        (weakProductFiniteStage_extend_hasFiniteNonbasepointSupport X a).mem_toFinset.2 hne
    rw [weakProductFiniteStage.extend_of_not_mem X b hi]
    exact hbase.symm

/-- Helper for Lemma 22.1.5: the direct-limit comparison quotient forgets only redundant
basepoint coordinates, so the round trip back to the direct limit is literally inverse. -/
private theorem weakProductComparison_rightInverse
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    Function.LeftInverse
      (weakProductToWeakProductDirectLimitFun X)
      (weakProductDirectLimitToWeakProductFun X) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  -- Compare the original stage with the stage cut out by the support of its padded tuple.
  simpa [weakProductDirectLimitToWeakProductFun, weakProductToWeakProductDirectLimitFun] using
    weakProductFiniteStageSupportQuotientEq X a

/-- Helper for Lemma 22.1.5: each coordinate map on the raw direct-limit quotient carrier is
continuous before passing to the compactly generated reflection. -/
private theorem weakProductDirectLimitCoordinate_raw_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    @Continuous (weakProductDirectLimitCarrier X) ((X i).toCompactlyGenerated)
      inferInstance inferInstance
      (weakProductDirectLimitCoordinate X i) := by
  let g : weakProductFiniteStage X → (X i).toCompactlyGenerated :=
    fun a ↦ weakProductFiniteStage.extend X a i
  have hg : Continuous g := by
    -- Each finite-stage coordinate map is continuous on its sigma summand.
    rw [continuous_sigma_iff]
    intro s
    by_cases hi : i ∈ s
    · let ii : s := ⟨i, hi⟩
      simpa [g, weakProductFiniteStage.extend, hi, ii] using
        (continuous_apply ii :
          Continuous fun x : (j : s) → (X j).toCompactlyGenerated ↦ x ii)
    · simpa [g, weakProductFiniteStage.extend, hi] using
        (continuous_const :
          Continuous fun _ : (j : s) → (X j).toCompactlyGenerated ↦ (X i).point)
  -- Descend the coordinate evaluation directly through the quotient model.
  simpa [weakProductDirectLimitCoordinate] using
    (hg.quotient_lift (fun a b h ↦ congrArg (fun f ↦ f i) h))

/-- The comparison map from the auxiliary direct-limit model to the source-facing weak-product
owner is continuous. -/
private theorem weakProductDirectLimitToWeakProductFun_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    Continuous fun x : (weakProductDirectLimit X).toCompactlyGenerated ↦
      (show (weakProduct X).toCompactlyGenerated from
        weakProductDirectLimitToWeakProductFun X x) := by
  have hraw :
      @Continuous (weakProductDirectLimitCarrier X) (weakProductType X)
        inferInstance instTopologicalSpaceSubtype
        (weakProductDirectLimitToWeakProductFun X) := by
    -- The raw weak-product topology is induced from the ambient product, so coordinatewise
    -- continuity of the padded tuple map is enough.
    rw [continuous_induced_rng]
    refine continuous_pi ?_
    intro i
    -- On each coordinate, the quotient comparison is exactly the raw coordinate projection.
    have hcoord :
        (fun a : weakProductDirectLimitCarrier X ↦
          (Subtype.val ∘ weakProductDirectLimitToWeakProductFun X) a i) =
          weakProductDirectLimitCoordinate X i := by
      funext a
      refine Quotient.inductionOn a ?_
      intro b
      rfl
    rw [hcoord]
    exact weakProductDirectLimitCoordinate_raw_continuous X i
  -- Once the raw comparison is continuous, both compactly generated owners inherit continuity.
  simpa [weakProductDirectLimit, weakProduct] using
    (continuousCompactlyGeneratedOfContinuous hraw :
      @Continuous (weakProductDirectLimitCarrier X) (weakProductType X)
        (TopologicalSpace.compactlyGenerated.{u} (weakProductDirectLimitCarrier X))
        (TopologicalSpace.compactlyGenerated.{u} (weakProductType X))
        (weakProductDirectLimitToWeakProductFun X))

/-- The comparison map from the source-facing weak-product owner to the auxiliary direct-limit
model is continuous. -/
private theorem weakProductToWeakProductDirectLimitFun_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    Continuous fun x : (weakProduct X).toCompactlyGenerated ↦
      (show (weakProductDirectLimit X).toCompactlyGenerated from
        weakProductToWeakProductDirectLimitFun X x) := by
  -- TODO: show continuity via the direct-limit comparison topology and the pointwise inverse
  -- identities, avoiding the noncontinuous `toFinset` bookkeeping in the main proof.
  sorry

/-- The comparison map from the auxiliary direct-limit model to the source-facing weak-product
owner, packaged as a continuous map. -/
private noncomputable def weakProductDirectLimitToWeakProductMap
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    C((weakProductDirectLimit X).toCompactlyGenerated, (weakProduct X).toCompactlyGenerated) where
  toFun := fun x ↦
    show (weakProduct X).toCompactlyGenerated from weakProductDirectLimitToWeakProductFun X x
  continuous_toFun := weakProductDirectLimitToWeakProductFun_continuous X

/-- The comparison map from the source-facing weak-product owner to the auxiliary direct-limit
model, packaged as a continuous map. -/
private noncomputable def weakProductToWeakProductDirectLimitMap
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    C((weakProduct X).toCompactlyGenerated, (weakProductDirectLimit X).toCompactlyGenerated) where
  toFun := fun x ↦
    show (weakProductDirectLimit X).toCompactlyGenerated from
      weakProductToWeakProductDirectLimitFun X x
  continuous_toFun := weakProductToWeakProductDirectLimitFun_continuous X

/-- The auxiliary direct-limit model is homotopy equivalent to the source-facing weak-product
owner of Definition 22.1.4. -/
private noncomputable def weakProductDirectLimitHomotopyEquivWeakProduct
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    ContinuousMap.HomotopyEquiv
      (weakProductDirectLimit X).toCompactlyGenerated (weakProduct X).toCompactlyGenerated where
  toFun := weakProductDirectLimitToWeakProductMap X
  invFun := weakProductToWeakProductDirectLimitMap X
  left_inv := by
    -- The comparison maps are pointwise inverse on the direct-limit carrier.
    have hcomp :
        (weakProductToWeakProductDirectLimitMap X).comp
            (weakProductDirectLimitToWeakProductMap X) =
          ContinuousMap.id (weakProductDirectLimit X).toCompactlyGenerated := by
      ext q
      exact weakProductComparison_rightInverse X q
    simpa [hcomp] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id (weakProductDirectLimit X).toCompactlyGenerated))
  right_inv := by
    -- The comparison maps are pointwise inverse on the weak-product carrier.
    have hcomp :
        (weakProductDirectLimitToWeakProductMap X).comp
            (weakProductToWeakProductDirectLimitMap X) =
          ContinuousMap.id (weakProduct X).toCompactlyGenerated := by
      ext x
      exact weakProductComparison_leftInverse X x
    simpa [hcomp] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id (weakProduct X).toCompactlyGenerated))

/-- The source-facing weak-product owner is homotopy equivalent to the auxiliary direct-limit
model. -/
private noncomputable def weakProductHomotopyEquivWeakProductDirectLimit
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    ContinuousMap.HomotopyEquiv
      (weakProduct X).toCompactlyGenerated (weakProductDirectLimit X).toCompactlyGenerated :=
  (weakProductDirectLimitHomotopyEquivWeakProduct X).symm

/-- The homotopy-equivalence comparison sends the weak-product basepoint to the direct-limit
basepoint. -/
private theorem weakProductHomotopyEquivWeakProductDirectLimit_basepoint
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    (weakProductHomotopyEquivWeakProductDirectLimit X).toFun (weakProductPoint X) =
      weakProductDirectLimitPoint X := by
  -- The weak-product basepoint has empty support, so it lands in the empty finite stage.
  apply Quotient.sound
  funext i
  simp [weakProductHomotopyEquivWeakProductDirectLimit, weakProductToWeakProductDirectLimitMap,
    weakProductToWeakProductDirectLimitFun, weakProductDirectLimitPoint,
    weakProductFiniteStage.extend, weakProductPoint]

/-- The homotopy-equivalence comparison sends the direct-limit basepoint to the weak-product
basepoint. -/
private theorem weakProductDirectLimitHomotopyEquivWeakProduct_basepoint
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    (weakProductDirectLimitHomotopyEquivWeakProduct X).toFun (weakProductDirectLimitPoint X) =
      weakProductPoint X := by
  -- The empty finite stage extends to the constant basepoint tuple.
  apply Subtype.ext
  funext i
  simp [weakProductDirectLimitHomotopyEquivWeakProduct, weakProductDirectLimitHomotopyEquivWeakProduct,
    weakProductDirectLimitToWeakProductMap, weakProductDirectLimitToWeakProductFun,
    weakProductDirectLimitPoint, weakProductPoint, weakProductFiniteStage.extend]

/-- Helper for Lemma 22.1.5: postcomposition with continuous maps composes on generalized loops. -/
private theorem genLoopMap_comp
    {A : Type u} {B : Type w} {C : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) {q : ℕ} {a : A} (γ : Ω^ (Fin q) A a) :
    genLoopMap g (genLoopMap f γ) = genLoopMap (g.comp f) γ := by
  -- Compare the two postcomposed representatives pointwise.
  ext t
  rfl

/-- Helper for Lemma 22.1.5: `eStarMulHomOverEq` is independent of the chosen endpoint proof. -/
private theorem eStarMulHomOverEq_proofIrrel
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (m : ℕ) (h₁ h₂ : f a = b) :
    f.eStarMulHomOverEq m h₁ = f.eStarMulHomOverEq m h₂ := by
  -- Both endpoint witnesses reduce to the same based map after matching the target basepoint.
  cases h₁
  cases h₂
  rfl

/-- Helper for Lemma 22.1.5: equal continuous maps induce equal successor-degree transport maps
once endpoint witnesses are synchronized. -/
private theorem eStarMulHomOverEq_congr
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)} (hfg : f = g) (m : ℕ)
    (hf : f a = b) (hg : g a = b) :
    f.eStarMulHomOverEq m hf = g.eStarMulHomOverEq m hg := by
  -- After identifying the maps, only endpoint-proof irrelevance remains.
  cases hfg
  exact eStarMulHomOverEq_proofIrrel f m hf hg

/-- Helper for Lemma 22.1.5: composing the successor-degree transport maps equals transporting
along the composite map. -/
private theorem eStarMulHomOverEq_comp
    {A : Type u} {B : Type w} {C : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : A} {b : B} {c : C}
    (f : C(A, B)) (hf : f a = b) (g : C(B, C)) (hg : g b = c) (m : ℕ) :
    (g.eStarMulHomOverEq m hg).comp (f.eStarMulHomOverEq m hf) =
      (g.comp f).eStarMulHomOverEq m
        (by simpa [ContinuousMap.comp_apply, hf] using hg) := by
  -- Normalize the endpoint witnesses first, then compare the two induced maps on loop classes.
  cases hf
  cases hg
  ext x
  refine Quotient.inductionOn x ?_
  intro γ
  -- Both sides are represented by postcomposing `γ` with the same composite map.
  simpa [MonoidHom.comp_apply, ContinuousMap.eStarMulHomOverEq_rfl, homotopyGroupMap_mk] using
    congrArg (fun δ ↦ (⟦δ⟧ : π_ (m + 1) C ((g.comp f) a))) (genLoopMap_comp f g γ)

/-- Helper for Lemma 22.1.5: the identity map induces the identity successor-degree transport. -/
private theorem eStarMulHomOverEq_id
    {Y : Type u} [TopologicalSpace Y] (m : ℕ) (y : Y) :
    (ContinuousMap.id Y).eStarMulHomOverEq m (rfl : (ContinuousMap.id Y) y = y) =
      MonoidHom.id (π_ (m + 1) Y y) := by
  -- Evaluate both monoid homomorphisms on arbitrary homotopy classes and use the identity action.
  rw [ContinuousMap.eStarMulHomOverEq_rfl]
  ext x
  change (ContinuousMap.id Y).eStar (m + 1) y x = x
  simpa [homotopyGroupMap_id] using congrArg (fun f ↦ f x) (homotopyGroupMap_id (m + 1) y)

/-- Helper for Lemma 22.1.5: a basepoint equality packages the positive-degree transport map as a
monoid homomorphism on `π_ (m + 1)`. -/
private noncomputable def homotopyGroupMonoidHomOverEq
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (m : ℕ) :
    π_ (m + 1) A a →* π_ (m + 1) B b :=
  f.eStarMulHomOverEq m hf

/-- Helper for Lemma 22.1.5: equal continuous maps induce the same packaged positive-degree
transport once the endpoint equalities are synchronized. -/
private theorem homotopyGroupMonoidHomOverEq_congr
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)} (hfg : f = g) (m : ℕ)
    (hf : f a = b) (hg : g a = b) :
    homotopyGroupMonoidHomOverEq f hf m = homotopyGroupMonoidHomOverEq g hg m := by
  -- After identifying the two maps, only endpoint-proof irrelevance remains.
  simpa [homotopyGroupMonoidHomOverEq] using eStarMulHomOverEq_congr hfg m hf hg

/-- Helper for Lemma 22.1.5: the packaged positive-degree transport of the identity map is the
identity homomorphism. -/
private theorem homotopyGroupMonoidHomOverEq_id
    {Y : Type u} [TopologicalSpace Y] (m : ℕ) (y : Y) :
    homotopyGroupMonoidHomOverEq (ContinuousMap.id Y) (rfl : (ContinuousMap.id Y) y = y) m =
      MonoidHom.id (π_ (m + 1) Y y) := by
  -- This is the identity specialization of `eStarMulHomOverEq_id`.
  simpa [homotopyGroupMonoidHomOverEq] using eStarMulHomOverEq_id m y

/-- Helper for Lemma 22.1.5: packaged positive-degree transport composes along composites of
continuous maps. -/
private theorem homotopyGroupMonoidHomOverEq_comp
    {A : Type u} {B : Type w} {C : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : A} {b : B} {c : C}
    (f : C(A, B)) (hf : f a = b) (g : C(B, C)) (hg : g b = c) (m : ℕ) :
    (homotopyGroupMonoidHomOverEq g hg m).comp (homotopyGroupMonoidHomOverEq f hf m) =
      homotopyGroupMonoidHomOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) m := by
  -- Normalize the endpoint equality and reuse the composition theorem for `eStarMulHomOverEq`.
  simpa [homotopyGroupMonoidHomOverEq] using eStarMulHomOverEq_comp f hf g hg m

/-- Helper for Lemma 22.1.5: a basepoint equality packages the positive-degree transport map as a
monoid homomorphism on `π_ (n : ℕ)` for `n : ℕ+`. -/
private noncomputable def homotopyGroupMonoidHomOverEqPNat
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ+) :
    π_ (n : ℕ) A a →* π_ (n : ℕ) B b :=
  match n with
  | ⟨Nat.succ m, _⟩ => homotopyGroupMonoidHomOverEq f hf m

/-- Helper for Lemma 22.1.5: continuous inverse maps induce mutually inverse packaged
positive-degree transport maps on homotopy groups. -/
private theorem homotopyGroupMonoidHomOverEq_bijectiveOfInverse
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (g : C(B, A))
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {a : A} {b : B} (h : f a = b) (m : ℕ) :
    Function.Bijective (homotopyGroupMonoidHomOverEq f h m) := by
  let h' : g b = a := by
    simpa [h] using hgf a
  let gfEq : g.comp f = ContinuousMap.id A := by
    ext x
    exact hgf x
  let fgEq : f.comp g = ContinuousMap.id B := by
    ext y
    exact hfg y
  let gHom : π_ (m + 1) B b →* π_ (m + 1) A a := homotopyGroupMonoidHomOverEq g h' m
  have hleft :
      gHom.comp (homotopyGroupMonoidHomOverEq f h m) =
        MonoidHom.id (π_ (m + 1) A a) := by
    have hcomp :
        gHom.comp (homotopyGroupMonoidHomOverEq f h m) =
          homotopyGroupMonoidHomOverEq (g.comp f)
            (by simpa [ContinuousMap.comp_apply, h] using h') m := by
      simpa [gHom] using homotopyGroupMonoidHomOverEq_comp f h g h' m
    have hcongr :
        homotopyGroupMonoidHomOverEq (g.comp f)
            (by simpa [ContinuousMap.comp_apply, h] using h') m =
          homotopyGroupMonoidHomOverEq (ContinuousMap.id A)
            (rfl : (ContinuousMap.id A) a = a) m := by
      exact homotopyGroupMonoidHomOverEq_congr gfEq m _ _
    exact hcomp.trans <| hcongr.trans <| by
      simpa using homotopyGroupMonoidHomOverEq_id m a
  have hright :
      (homotopyGroupMonoidHomOverEq f h m).comp gHom =
        MonoidHom.id (π_ (m + 1) B b) := by
    have hcomp :
        (homotopyGroupMonoidHomOverEq f h m).comp gHom =
          homotopyGroupMonoidHomOverEq (f.comp g)
            (by simpa [ContinuousMap.comp_apply, h'] using h) m := by
      simpa [gHom] using homotopyGroupMonoidHomOverEq_comp g h' f h m
    have hcongr :
        homotopyGroupMonoidHomOverEq (f.comp g)
            (by simpa [ContinuousMap.comp_apply, h'] using h) m =
          homotopyGroupMonoidHomOverEq (ContinuousMap.id B)
            (rfl : (ContinuousMap.id B) b = b) m := by
      exact homotopyGroupMonoidHomOverEq_congr fgEq m _ _
    exact hcomp.trans <| hcongr.trans <| by
      simpa using homotopyGroupMonoidHomOverEq_id m b
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' := congrArg gHom hxy
    change (gHom.comp (homotopyGroupMonoidHomOverEq f h m)) x =
      (gHom.comp (homotopyGroupMonoidHomOverEq f h m)) y at hxy'
    simpa [MonoidHom.comp_apply, hleft] using hxy'
  · intro y
    refine ⟨gHom y, ?_⟩
    have hy :=
      congrArg
        (fun k : π_ (m + 1) B b →* π_ (m + 1) B b ↦ k y)
        hright
    simpa [MonoidHom.comp_apply] using hy

/-- Helper for Lemma 22.1.5: the `ℕ+`-normalized transport map attached to a continuous inverse
pair is bijective. -/
private theorem homotopyGroupMonoidHomOverEqPNat_bijectiveOfInverse
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (g : C(B, A))
    (hgf : Function.LeftInverse g f) (hfg : Function.LeftInverse f g)
    {a : A} {b : B} (h : f a = b) (n : ℕ+) :
    Function.Bijective (homotopyGroupMonoidHomOverEqPNat f h n) := by
  rcases n with ⟨k, hk⟩
  cases k with
  | zero =>
      cases hk
  | succ m =>
      simpa [homotopyGroupMonoidHomOverEqPNat] using
        homotopyGroupMonoidHomOverEq_bijectiveOfInverse f g hgf hfg h m

/-- The source-facing weak-product homotopy group maps to the auxiliary direct-limit model via the
comparison homotopy equivalence. -/
noncomputable def weakProductHomotopyGroupTransportToDirectLimit
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X] :
    π_ (n : ℕ) (weakProduct X).toCompactlyGenerated (weakProductPoint X) →*
      π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
        (weakProductDirectLimitPoint X) :=
  -- Keep the positive-degree normalization behind the dedicated `ℕ+` wrapper.
  homotopyGroupMonoidHomOverEqPNat
    (weakProductHomotopyEquivWeakProductDirectLimit X).toFun
    (weakProductHomotopyEquivWeakProductDirectLimit_basepoint X)
    n

/-- Helper for Lemma 22.1.5: the comparison transport from `weakProduct X` to the direct-limit
model is bijective on positive-degree homotopy groups. -/
private theorem weakProductHomotopyGroupTransportToDirectLimit_bijective
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X] :
    Function.Bijective (weakProductHomotopyGroupTransportToDirectLimit n X) := by
  let f := weakProductToWeakProductDirectLimitMap X
  let g := weakProductDirectLimitToWeakProductMap X
  have hgf : Function.LeftInverse g f := by
    intro x
    exact weakProductComparison_leftInverse X x
  have hfg : Function.LeftInverse f g := by
    intro x
    exact weakProductComparison_rightInverse X x
  -- The comparison maps are literally inverse on points, so the packaged transport map is
  -- bijective in every positive degree.
  simpa [weakProductHomotopyGroupTransportToDirectLimit,
    weakProductHomotopyEquivWeakProductDirectLimit, f, g] using
    homotopyGroupMonoidHomOverEqPNat_bijectiveOfInverse f g hgf hfg
      (weakProductHomotopyEquivWeakProductDirectLimit_basepoint X) n

/-- The comparison between `weakProduct X` and the auxiliary direct-limit model induces a
multiplicative equivalence on positive-degree homotopy groups. -/
noncomputable def weakProductHomotopyGroupTransportMulEquiv
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X] :
    π_ (n : ℕ) (weakProduct X).toCompactlyGenerated (weakProductPoint X) ≃*
      π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
        (weakProductDirectLimitPoint X) :=
  MulEquiv.ofBijective
    (weakProductHomotopyGroupTransportToDirectLimit n X)
    (weakProductHomotopyGroupTransportToDirectLimit_bijective n X)

/-- The coordinate projection from the direct-limit weak product to its `i`th factor. -/
theorem weakProductCoordinateMap_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    Continuous fun x : (weakProductDirectLimit X).toCompactlyGenerated ↦
      weakProductDirectLimitCoordinate X i x := by
  let t0 : TopologicalSpace (weakProductDirectLimitCarrier X) := inferInstance
  have hrawDom :
      @Continuous ((weakProductDirectLimit X).toCompactlyGenerated)
        (weakProductDirectLimitCarrier X)
        inferInstance t0
        (fun x : (weakProductDirectLimit X).toCompactlyGenerated ↦
          (x : weakProductDirectLimitCarrier X)) := by
    -- The direct-limit owner is the compactly generated reflection of the raw quotient topology.
    simpa [weakProductDirectLimit] using
      (continuous_id_compactlyGenerated :
        @Continuous (weakProductDirectLimitCarrier X) (weakProductDirectLimitCarrier X)
          (TopologicalSpace.compactlyGenerated.{u} (weakProductDirectLimitCarrier X))
          t0
          (id : weakProductDirectLimitCarrier X → weakProductDirectLimitCarrier X))
  -- Compose the raw quotient continuity with the identity from the k-ified source.
  exact (weakProductDirectLimitCoordinate_raw_continuous X i).comp hrawDom

/-- The coordinate projection from the direct-limit weak product to its `i`th factor. -/
noncomputable def weakProductCoordinateMap
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    C((weakProductDirectLimit X).toCompactlyGenerated, (X i).toCompactlyGenerated) where
  toFun := weakProductDirectLimitCoordinate X i
  continuous_toFun := weakProductCoordinateMap_continuous X i

/-- Projecting a direct-limit weak-product generalized loop to one coordinate gives a generalized
loop in the corresponding factor. -/
theorem weakProductCoordinateGenLoop_property
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι)
    (p : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    ∀ t ∈ Cube.boundary (Fin (n : ℕ)), ((weakProductCoordinateMap X i).comp p.1) t = (X i).point :=
  by
    intro t ht
    -- Apply the coordinate projection to the boundary value of `p`.
    simpa [weakProductCoordinateMap, weakProductDirectLimitCoordinate_point] using
      congrArg (weakProductDirectLimitCoordinate X i) (p.2 t ht)

/-- The `i`th coordinate of a direct-limit weak-product generalized loop. -/
noncomputable def weakProductCoordinateGenLoop
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι)
    (p : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    GenLoop (Fin (n : ℕ)) (X i).toCompactlyGenerated (X i).point :=
  ⟨(weakProductCoordinateMap X i).comp p.1, weakProductCoordinateGenLoop_property n X i p⟩

/-- Coordinate projection preserves homotopies of generalized loops in the direct-limit weak
product. -/
theorem weakProductCoordinateGenLoop_homotopic
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) {i : ι}
    {p q : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)}
    (hpq : p ≈ q) :
    weakProductCoordinateGenLoop n X i p ≈ weakProductCoordinateGenLoop n X i q := by
  change ((weakProductCoordinateMap X i).comp p.1).HomotopicRel
      ((weakProductCoordinateMap X i).comp q.1) (Cube.boundary (Fin (n : ℕ)))
  simpa [GenLoop.Homotopic, weakProductCoordinateGenLoop] using
    ContinuousMap.HomotopicRel.comp_continuousMap hpq (weakProductCoordinateMap X i)

/-- Helper for Lemma 22.1.5: splitting off an inserted coordinate identifies the corresponding
finite stage with the product of that coordinate and the remaining stage. -/
private noncomputable def finiteStageInsertHomeomorph
    (X : ι → PointedCompactlyGenerated.{u, w}) [DecidableEq ι]
    (s : Finset ι) {a : ι} (ha : a ∉ s) :
    ((i : ↥(insert a s)) → (X i).toCompactlyGenerated) ≃ₜ
      (X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated) where
  toEquiv :=
    { toFun := fun x ↦
        (x (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)),
          fun i ↦ x (⟨i, Finset.mem_insert_of_mem i.2⟩ : ↥(insert a s)))
      invFun := fun y i ↦
        if h : (i : ι) = a then by
          simpa [h] using y.1
        else
          y.2 ⟨i, Finset.mem_of_mem_insert_of_ne i.2 h⟩
      left_inv := by
        intro x
        -- Compare the reconstructed tuple coordinatewise on the inserted finite stage.
        funext i
        by_cases h : (i : ι) = a
        · have hi : i = (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)) := by
            apply Subtype.ext
            simpa using h
          cases hi
          simp
        · simp [h]
      right_inv := by
        intro y
        -- The forward map reads off the distinguished coordinate and the remaining tuple.
        refine Prod.ext ?_ ?_
        · simp
        · funext i
          have hi : (i : ι) ≠ a := by
            intro h
            exact ha (h.symm ▸ i.2)
          simp [hi] }
  continuous_toFun := by
    -- Continuity of the split map is coordinatewise on the finite product.
    refine Continuous.prodMk
      (continuous_apply (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))) ?_
    refine continuous_pi ?_
    intro i
    exact continuous_apply (⟨i, Finset.mem_insert_of_mem i.2⟩ : ↥(insert a s))
  continuous_invFun := by
    -- Reassemble the inserted finite stage coordinatewise from the product data.
    refine continuous_pi ?_
    intro i
    by_cases h : (i : ι) = a
    · have hi : i = (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)) := by
        apply Subtype.ext
        simpa using h
      cases hi
      simpa using
        (continuous_fst :
          Continuous fun y :
            (X a).toCompactlyGenerated × ((j : s) → (X j).toCompactlyGenerated) ↦ y.1)
    · simpa [h] using
        ((continuous_apply (⟨i, Finset.mem_of_mem_insert_of_ne i.2 h⟩ : s)).comp
            continuous_snd :
          Continuous fun y :
            (X a).toCompactlyGenerated × ((j : s) → (X j).toCompactlyGenerated) ↦
              y.2 (⟨i, Finset.mem_of_mem_insert_of_ne i.2 h⟩ : s))

/-- Coordinate projection sends the constant direct-limit weak-product loop to the constant loop in
the corresponding factor. -/
private theorem weakProductCoordinateGenLoop_const
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    weakProductCoordinateGenLoop n X i GenLoop.const = GenLoop.const := by
  -- Coordinate projection of the constant loop is again the constant loop.
  apply Subtype.ext
  ext t
  simp [weakProductCoordinateGenLoop, weakProductCoordinateMap,
    weakProductDirectLimitCoordinate_point]

/-- Coordinate projection commutes with `GenLoop.transAt`. -/
private theorem weakProductCoordinateGenLoop_transAt
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) (j : Fin (n : ℕ))
    (p q : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    weakProductCoordinateGenLoop n X i (GenLoop.transAt j q p) =
      GenLoop.transAt j (weakProductCoordinateGenLoop n X i q)
        (weakProductCoordinateGenLoop n X i p) := by
  -- Route correction: normalize `transAt` at the generalized-loop level before projecting.
  ext t
  dsimp [weakProductCoordinateGenLoop, weakProductCoordinateMap, GenLoop.transAt, GenLoop.copy]
  split_ifs <;> rfl

/-- Helper for Lemma 22.1.5: a generalized loop in a fixed finite stage defines a generalized loop
in the direct-limit weak product by applying the quotient map pointwise. -/
private noncomputable def weakProductFiniteStagePointRaw
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    ((Fin (n : ℕ)) → I) → weakProductDirectLimitCarrier X :=
  fun t ↦ Quotient.mk _ ⟨s, p.1 t⟩

/-- Helper for Lemma 22.1.5: the pointwise quotient map of a fixed finite-stage generalized loop
is continuous for the raw direct-limit quotient topology. -/
private theorem weakProductFiniteStagePoint_rawContinuous
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    @Continuous ((Fin (n : ℕ)) → I) (weakProductDirectLimitCarrier X)
      inferInstance inferInstance
      (weakProductFiniteStagePointRaw n X s p) := by
  -- A fixed finite stage varies continuously before passing to the compactly generated owner.
  simpa [weakProductFiniteStagePointRaw] using
    (continuous_quotient_mk'.comp (continuous_sigmaMk.comp p.1.continuous))

/-- Helper for Lemma 22.1.5: the pointwise quotient map of a fixed finite-stage generalized loop
is continuous after packaging the direct-limit carrier with its compactly generated topology. -/
private theorem weakProductFiniteStagePoint_continuous
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    Continuous fun t : ((Fin (n : ℕ)) → I) ↦
      (show (weakProductDirectLimit X).toCompactlyGenerated from
        weakProductFiniteStagePointRaw n X s p t) := by
  -- The cube source is compact Hausdorff, so raw continuity upgrades to the k-ified codomain.
  simpa [weakProductDirectLimit, weakProductFiniteStagePointRaw] using
    (continuousSmallCompHausToCompactlyGenerated
      (weakProductFiniteStagePoint_rawContinuous n X s p) :
      @Continuous ((Fin (n : ℕ)) → I) (weakProductDirectLimitCarrier X)
        inferInstance
        (TopologicalSpace.compactlyGenerated.{u} (weakProductDirectLimitCarrier X))
        (weakProductFiniteStagePointRaw n X s p))

/-- Helper for Lemma 22.1.5: on the boundary of the cube, a fixed finite-stage generalized loop
maps to the direct-limit basepoint. -/
private theorem weakProductFiniteStagePoint_boundary
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    ∀ t ∈ Cube.boundary (Fin (n : ℕ)),
      weakProductFiniteStagePointRaw n X s p t = weakProductDirectLimitPoint X := by
  let e : weakProductFiniteStage X := ⟨∅, fun i ↦ nomatch i.2⟩
  intro t ht
  -- On the cube boundary, the stage loop is the constant basepoint tuple.
  apply Quotient.sound
  change weakProductFiniteStage.extend X ⟨s, p.1 t⟩ = weakProductFiniteStage.extend X e
  funext i
  by_cases hi : i ∈ s
  · rw [weakProductFiniteStage.extend_of_mem X ⟨s, p.1 t⟩ hi]
    simpa using congrFun (p.2 t ht) ⟨i, hi⟩
  · rw [weakProductFiniteStage.extend_of_not_mem X ⟨s, p.1 t⟩ hi]
    simp [e, weakProductFiniteStage.extend]

/-- Helper for Lemma 22.1.5: a generalized loop in a fixed finite stage defines a generalized loop
in the direct-limit weak product by applying the quotient map pointwise. -/
private noncomputable def weakProductFiniteStageGenLoop
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X) :=
  ⟨{ toFun := fun t ↦
        show (weakProductDirectLimit X).toCompactlyGenerated from
          weakProductFiniteStagePointRaw n X s p t
      , continuous_toFun := weakProductFiniteStagePoint_continuous n X s p }
    , weakProductFiniteStagePoint_boundary n X s p⟩

/-- Helper for Lemma 22.1.5: outside a fixed finite stage, the corresponding coordinate loop is
literally constant. -/
private theorem weakProductCoordinateGenLoop_finiteStage_not_mem
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point))
    {i : ι} (hi : i ∉ s) :
    weakProductCoordinateGenLoop n X i (weakProductFiniteStageGenLoop n X s p) = GenLoop.const := by
  apply Subtype.ext
  ext t
  -- The fixed-stage representative pads every off-stage coordinate by the distinguished basepoint.
  change weakProductDirectLimitCoordinate X i
      (weakProductFiniteStagePointRaw n X s p t) = (X i).point
  simp [weakProductFiniteStagePointRaw, weakProductDirectLimitCoordinate,
    weakProductFiniteStage.extend, hi]

/-- Helper for Lemma 22.1.5: a generalized loop that already lands in one finite stage has finite
coordinate support on homotopy classes. -/
private theorem weakProductCoordinateGenLoop_hasFiniteSupport_of_finiteStage
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (p : GenLoop (Fin (n : ℕ))
      ((i : s) → (X i).toCompactlyGenerated) (fun i ↦ (X i.1).point)) :
    hasFiniteHomotopySupport n X
      (fun i ↦ (⟦weakProductCoordinateGenLoop n X i
        (weakProductFiniteStageGenLoop n X s p)⟧ : weakProductFactorHomotopyGroup n X i)) := by
  refine s.finite_toSet.subset ?_
  intro i hi
  by_contra his
  have hloop :
      weakProductCoordinateGenLoop n X i (weakProductFiniteStageGenLoop n X s p) = GenLoop.const :=
    weakProductCoordinateGenLoop_finiteStage_not_mem n X s p his
  have hclass :
      (⟦weakProductCoordinateGenLoop n X i
          (weakProductFiniteStageGenLoop n X s p)⟧ :
        weakProductFactorHomotopyGroup n X i) = (1 : weakProductFactorHomotopyGroup n X i) := by
    calc
      (⟦weakProductCoordinateGenLoop n X i
          (weakProductFiniteStageGenLoop n X s p)⟧ :
        weakProductFactorHomotopyGroup n X i)
          = (⟦GenLoop.const⟧ : weakProductFactorHomotopyGroup n X i) := by rw [hloop]
      _ = (1 : weakProductFactorHomotopyGroup n X i) := by
        exact HomotopyGroup.one_def.symm
  exact hi hclass

/-- A generalized loop in the direct-limit weak product has only finitely many nontrivial
coordinate classes. -/
theorem weakProductCoordinateGenLoop_hasFiniteSupport
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    hasFiniteHomotopySupport n X
      (fun i ↦ ⟦weakProductCoordinateGenLoop n X i p⟧) := by
  -- TODO: extract a single finite-stage support witness for the compact image of `p`, then show
  -- every coordinate outside that witness is the constant loop and hence has class `1`.
  sorry

private noncomputable def weakProductHomotopyGroupDirectSumProjectionAux
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    weakProductHomotopyGroupDirectSum n X :=
  ⟨fun i ↦ ⟦weakProductCoordinateGenLoop n X i p⟧,
    (hasFiniteHomotopySupport_iff_eventually n X
      (fun i ↦ ⟦weakProductCoordinateGenLoop n X i p⟧)).1
        (weakProductCoordinateGenLoop_hasFiniteSupport n X p)⟩

private theorem weakProductHomotopyGroupDirectSumProjectionAux_respects
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (p q : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X))
    (hpq : p ≈ q) :
    weakProductHomotopyGroupDirectSumProjectionAux n X p =
      weakProductHomotopyGroupDirectSumProjectionAux n X q := by
  ext i
  exact Quotient.sound (weakProductCoordinateGenLoop_homotopic n X hpq)

/-- The coordinatewise projection from the direct-limit weak-product homotopy group to the
finite-support product of the factor homotopy groups. -/
noncomputable def weakProductHomotopyGroupDirectSumProjection
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X) →*
      weakProductHomotopyGroupDirectSum n X where
  toFun :=
    Quotient.lift
      (weakProductHomotopyGroupDirectSumProjectionAux n X)
      (weakProductHomotopyGroupDirectSumProjectionAux_respects n X)
  map_one' := by
    ext i
    let F :
        π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
            (weakProductDirectLimitPoint X) →
          weakProductHomotopyGroupDirectSum n X :=
      Quotient.lift
        (weakProductHomotopyGroupDirectSumProjectionAux n X)
        (weakProductHomotopyGroupDirectSumProjectionAux_respects n X)
    have hF :=
      congrArg
        (fun x ↦
          ((F x : weakProductHomotopyGroupDirectSum n X) i :
            weakProductFactorHomotopyGroup n X i))
        (HomotopyGroup.one_def :
          (1 : π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
            (weakProductDirectLimitPoint X)) = ⟦GenLoop.const⟧)
    simpa [F, weakProductHomotopyGroupDirectSumProjectionAux,
      weakProductCoordinateGenLoop_const] using hF
  map_mul' := by
    intro x y
    ext i
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    let j : Fin (n : ℕ) := 0
    let pClass :
        π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
          (weakProductDirectLimitPoint X) := ⟦p⟧
    let qClass :
        π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
          (weakProductDirectLimitPoint X) := ⟦q⟧
    have hmul :
        pClass * qClass =
          (⟦GenLoop.transAt j q p⟧ :
            π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
              (weakProductDirectLimitPoint X)) := by
      simpa [pClass, qClass] using
        (HomotopyGroup.mul_spec :
          pClass * qClass =
            (⟦GenLoop.transAt j q p⟧ :
              π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated
                (weakProductDirectLimitPoint X)))
    -- Rewrite the direct-limit product to the standard `transAt` representative and then compare
    -- coordinates on the restricted product side.
    rw [hmul]
    change (weakProductHomotopyGroupDirectSumProjectionAux n X (GenLoop.transAt j q p)) i =
      ((weakProductHomotopyGroupDirectSumProjectionAux n X p) *
        (weakProductHomotopyGroupDirectSumProjectionAux n X q)) i
    rw [RestrictedProduct.mul_apply]
    simp [weakProductHomotopyGroupDirectSumProjectionAux, weakProductCoordinateGenLoop_transAt]
    let pCoord : weakProductFactorHomotopyGroup n X i := ⟦weakProductCoordinateGenLoop n X i p⟧
    let qCoord : weakProductFactorHomotopyGroup n X i := ⟦weakProductCoordinateGenLoop n X i q⟧
    have hcoord :
        pCoord * qCoord =
          (⟦GenLoop.transAt j
              (weakProductCoordinateGenLoop n X i q)
              (weakProductCoordinateGenLoop n X i p)⟧ :
            weakProductFactorHomotopyGroup n X i) := by
      simpa [pCoord, qCoord] using
        (HomotopyGroup.mul_spec :
          pCoord * qCoord =
            (⟦GenLoop.transAt j
                (weakProductCoordinateGenLoop n X i q)
                (weakProductCoordinateGenLoop n X i p)⟧ :
              weakProductFactorHomotopyGroup n X i))
    simpa [weakProductHomotopyGroupDirectSumProjectionAux] using hcoord.symm

@[simp] theorem weakProductHomotopyGroupDirectSumProjection_mk
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (p : GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X)) :
    weakProductHomotopyGroupDirectSumProjection n X ⟦p⟧ =
      weakProductHomotopyGroupDirectSumProjectionAux n X p := by
  change Quotient.lift
      (weakProductHomotopyGroupDirectSumProjectionAux n X)
      (weakProductHomotopyGroupDirectSumProjectionAux_respects n X) ⟦p⟧ =
    weakProductHomotopyGroupDirectSumProjectionAux n X p
  rfl

/-- A chosen representative generalized loop for the `i`th coordinate of a finite-support family
of homotopy classes, taken to be the constant loop when the class is the identity. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumRepresentative
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) (i : ι) :
    GenLoop (Fin (n : ℕ)) (X i).toCompactlyGenerated (X i).point :=
  let _ : DecidableEq (weakProductFactorHomotopyGroup n X i) := Classical.decEq _
  if _ : f i = 1 then GenLoop.const else Quotient.out (f i)

/-- The finite set of coordinates supporting a direct-sum family. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumSupport
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) : Finset ι :=
  (weakProductHomotopyGroupDirectSum_hasFiniteSupport n X f).toFinset

/-- Helper for Lemma 22.1.5: the chosen support finset records exactly the non-identity
coordinates of the direct-sum element. -/
private theorem weakProductHomotopyGroupMulEquivDirectSumSupport_mem_iff
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) (i : ι) :
    i ∈ weakProductHomotopyGroupMulEquivDirectSumSupport n X f ↔ f i ≠ 1 := by
  classical
  -- Unpack the support finset back to the finite set of non-identity coordinates.
  simpa [weakProductHomotopyGroupMulEquivDirectSumSupport, hasFiniteHomotopySupport] using
    (weakProductHomotopyGroupDirectSum_hasFiniteSupport n X f).mem_toFinset i

/-- Helper for Lemma 22.1.5: every chosen coordinate representative is based on the cube
boundary. -/
private theorem weakProductHomotopyGroupMulEquivDirectSumRepresentative_boundary
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) (i : ι)
    (t : I^(Fin (n : ℕ))) (ht : t ∈ Cube.boundary (Fin (n : ℕ))) :
    weakProductHomotopyGroupMulEquivDirectSumRepresentative n X f i t = (X i).point := by
  classical
  -- The identity class uses the constant loop; every other class uses its chosen representative.
  by_cases hfi : f i = 1
  · simp [weakProductHomotopyGroupMulEquivDirectSumRepresentative, hfi]
  · simpa [weakProductHomotopyGroupMulEquivDirectSumRepresentative, hfi] using
      (Quotient.out (f i)).2 t ht

/-- The chosen representatives at time `t` determine a point of the finite stage indexed by the
support of `f`. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumInvStage
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) (t : I^(Fin (n : ℕ))) :
    weakProductFiniteStage X :=
  let s := weakProductHomotopyGroupMulEquivDirectSumSupport n X f
  ⟨s, fun i ↦ weakProductHomotopyGroupMulEquivDirectSumRepresentative n X f i t⟩

/-- Evaluating the chosen representatives gives a point of the direct-limit weak product. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumInvPoint
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    (I^(Fin (n : ℕ))) → (weakProductDirectLimit X).toCompactlyGenerated :=
  fun t ↦ Quotient.mk _ (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t)

/-- Helper for Lemma 22.1.5: the assembled inverse point is continuous for the raw quotient
topology on `weakProductDirectLimitCarrier X`. -/
private theorem weakProductHomotopyGroupMulEquivDirectSumInvPoint_rawContinuous
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    @Continuous (I^(Fin (n : ℕ))) (weakProductDirectLimitCarrier X)
      inferInstance inferInstance
      (weakProductHomotopyGroupMulEquivDirectSumInvPoint n X f) := by
  classical
  let s := weakProductHomotopyGroupMulEquivDirectSumSupport n X f
  let g : (I^(Fin (n : ℕ))) → ((i : s) → (X i).toCompactlyGenerated) :=
    fun t i ↦ (weakProductHomotopyGroupMulEquivDirectSumRepresentative n X f i) t
  have hg : Continuous g := by
    -- Each coordinate is one of the chosen generalized-loop representatives.
    refine continuous_pi ?_
    intro i
    exact (weakProductHomotopyGroupMulEquivDirectSumRepresentative n X f i).1.continuous
  have hstage :
      Continuous fun t : I^(Fin (n : ℕ)) ↦
        (⟨s, g t⟩ : weakProductFiniteStage X) := by
    -- The support stage is fixed, so continuity is reduced to the finite tuple of coordinates.
    simpa [g] using (continuous_sigmaMk.comp hg)
  -- Descend the continuous fixed-stage map through the quotient presentation.
  simpa [weakProductHomotopyGroupMulEquivDirectSumInvPoint,
    weakProductHomotopyGroupMulEquivDirectSumInvStage, s, g] using
    (continuous_quotient_mk'.comp hstage)

/-- The coordinatewise assembly map is continuous. -/
private theorem weakProductHomotopyGroup_mulEquiv_directSum_invPoint_continuous
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    Continuous (weakProductHomotopyGroupMulEquivDirectSumInvPoint n X f) := by
  -- Route correction: this is the cheap compact-source bridge, not the real frontier.
  -- The cube source is compact Hausdorff, so the raw quotient continuity upgrades directly to the
  -- compactly generated owner used in `weakProductDirectLimit`.
  have hraw :=
    weakProductHomotopyGroupMulEquivDirectSumInvPoint_rawContinuous n X f
  simpa [weakProductDirectLimit] using
    (continuousSmallCompHausToCompactlyGenerated hraw :
      @Continuous (I^(Fin (n : ℕ))) (weakProductDirectLimitCarrier X)
        inferInstance
        (TopologicalSpace.compactlyGenerated.{u} (weakProductDirectLimitCarrier X))
        (weakProductHomotopyGroupMulEquivDirectSumInvPoint n X f))

/-- The coordinatewise assembly map sends the boundary cube to the direct-limit weak-product
basepoint. -/
private theorem weakProductHomotopyGroup_mulEquiv_directSum_invPoint_boundary
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    ∀ t ∈ Cube.boundary (Fin (n : ℕ)),
      weakProductHomotopyGroupMulEquivDirectSumInvPoint n X f t =
        weakProductDirectLimitPoint X := by
  intro t ht
  classical
  let e : weakProductFiniteStage X := ⟨∅, fun i ↦ nomatch i.2⟩
  -- Compare the assembled boundary point with the empty stage coordinatewise after extension.
  apply Quotient.sound
  change weakProductFiniteStage.extend X
      (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t) =
    weakProductFiniteStage.extend X e
  funext i
  have he : weakProductFiniteStage.extend X e i = (X i).point := by
    simp [e, weakProductFiniteStage.extend]
  by_cases hi : i ∈ weakProductHomotopyGroupMulEquivDirectSumSupport n X f
  · have hleft :
        weakProductFiniteStage.extend X
            (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t) i =
          (X i).point := by
      rw [weakProductFiniteStage.extend_of_mem X
        (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t) hi]
      -- On support coordinates, the chosen loop representative is based on the boundary.
      simpa [weakProductHomotopyGroupMulEquivDirectSumInvStage] using
        weakProductHomotopyGroupMulEquivDirectSumRepresentative_boundary n X f i t ht
    exact hleft.trans he.symm
  · have hleft :
        weakProductFiniteStage.extend X
            (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t) i =
          (X i).point := by
      rw [weakProductFiniteStage.extend_of_not_mem X
        (weakProductHomotopyGroupMulEquivDirectSumInvStage n X f t) hi]
    exact hleft.trans he.symm

/-- The chosen representatives assemble to a generalized loop in the direct-limit weak product. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumInvLoop
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) :
    GenLoop (Fin (n : ℕ))
      (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X) :=
  ⟨{ toFun := weakProductHomotopyGroupMulEquivDirectSumInvPoint n X f
      ,
      continuous_toFun := weakProductHomotopyGroup_mulEquiv_directSum_invPoint_continuous n X f }
    , weakProductHomotopyGroup_mulEquiv_directSum_invPoint_boundary n X f⟩

/-- The homotopy class in the direct-limit weak product assembled from chosen finite-support
representatives. -/
private noncomputable def weakProductHomotopyGroupMulEquivDirectSumInvFun
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    weakProductHomotopyGroupDirectSum n X →
      π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X) :=
  fun f ↦ ⟦weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f⟧

/-- Helper for Lemma 22.1.5: projecting the assembled loop to one coordinate recovers the chosen
direct-sum coordinate class. -/
private theorem assembledLoop_coordinateClass
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    (f : weakProductHomotopyGroupDirectSum n X) (i : ι) :
    (⟦weakProductCoordinateGenLoop n X i
        (weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f)⟧ :
      weakProductFactorHomotopyGroup n X i) = f i := by
  classical
  by_cases hfi : f i = 1
  · have hi :
        i ∉ weakProductHomotopyGroupMulEquivDirectSumSupport n X f := by
      intro hi
      exact (weakProductHomotopyGroupMulEquivDirectSumSupport_mem_iff n X f i).1 hi hfi
    have hloop :
        weakProductCoordinateGenLoop n X i
            (weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f) = GenLoop.const := by
      apply Subtype.ext
      ext t
      -- Outside the support, the assembled loop is literally constant in the `i`th coordinate.
      simp [weakProductCoordinateGenLoop, weakProductCoordinateMap,
        weakProductHomotopyGroupMulEquivDirectSumInvLoop,
        weakProductHomotopyGroupMulEquivDirectSumInvPoint,
        weakProductHomotopyGroupMulEquivDirectSumInvStage,
        weakProductDirectLimitCoordinate, weakProductFiniteStage.extend, hi,
        weakProductHomotopyGroupMulEquivDirectSumRepresentative, hfi]
    calc
      (⟦weakProductCoordinateGenLoop n X i
          (weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f)⟧ :
        weakProductFactorHomotopyGroup n X i)
          = ⟦GenLoop.const⟧ := by rw [hloop]
      _ = (1 : weakProductFactorHomotopyGroup n X i) := by
        exact
          (HomotopyGroup.one_def :
            (1 : weakProductFactorHomotopyGroup n X i) = ⟦GenLoop.const⟧).symm
      _ = f i := hfi.symm
  · have hi :
        i ∈ weakProductHomotopyGroupMulEquivDirectSumSupport n X f :=
      (weakProductHomotopyGroupMulEquivDirectSumSupport_mem_iff n X f i).2 hfi
    have hloop :
        weakProductCoordinateGenLoop n X i
            (weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f) =
          Quotient.out (f i) := by
      apply Subtype.ext
      ext t
      -- On support coordinates, projection reads off the chosen representative loop verbatim.
      simp [weakProductCoordinateGenLoop, weakProductCoordinateMap,
        weakProductHomotopyGroupMulEquivDirectSumInvLoop,
        weakProductHomotopyGroupMulEquivDirectSumInvPoint,
        weakProductHomotopyGroupMulEquivDirectSumInvStage,
        weakProductDirectLimitCoordinate, weakProductFiniteStage.extend, hi,
        weakProductHomotopyGroupMulEquivDirectSumRepresentative, hfi]
    calc
      (⟦weakProductCoordinateGenLoop n X i
          (weakProductHomotopyGroupMulEquivDirectSumInvLoop n X f)⟧ :
        weakProductFactorHomotopyGroup n X i)
          = ⟦Quotient.out (f i)⟧ := by rw [hloop]
      _ = f i := Quotient.out_eq (f i)

/-- The assembled direct-limit weak-product class is inverse to coordinate projection on homotopy
groups. -/
private theorem weakProductHomotopyGroup_mulEquiv_directSum_left_inv
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    Function.LeftInverse
      (weakProductHomotopyGroupMulEquivDirectSumInvFun n X)
      (weakProductHomotopyGroupDirectSumProjection n X) := by
  -- TODO: compare a loop class with the loop reassembled from its coordinate classes by first
  -- reducing the original loop to a single finite stage and then checking the assembled loop has
  -- the same coordinate classes on that stage.
  sorry

/-- Coordinate projection is inverse to the assembled direct-limit weak-product class. -/
private theorem weakProductHomotopyGroup_mulEquiv_directSum_right_inv
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    Function.RightInverse
      (weakProductHomotopyGroupMulEquivDirectSumInvFun n X)
      (weakProductHomotopyGroupDirectSumProjection n X) := by
  intro f
  -- The inverse assembly was built coordinatewise, so the right inverse is proved coordinatewise.
  ext i
  simpa [weakProductHomotopyGroupMulEquivDirectSumInvFun,
    weakProductHomotopyGroupDirectSumProjection_mk] using
    assembledLoop_coordinateClass n X f i

/-- The coordinatewise projection on direct-limit weak-product homotopy groups is bijective. -/
theorem weakProductDirectLimitHomotopyGroup_mulEquiv_directSum_bijective
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    Function.Bijective (weakProductHomotopyGroupDirectSumProjection n X) :=
  ⟨(weakProductHomotopyGroup_mulEquiv_directSum_left_inv n X).injective,
    (weakProductHomotopyGroup_mulEquiv_directSum_right_inv n X).surjective⟩

/-- Auxiliary direct-limit form of Lemma 22.1.5, used to transport the result back to the
source-facing weak-product owner of Definition 22.1.4. -/
noncomputable def weakProductDirectLimitHomotopyGroup_mulEquiv_directSum
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w}) :
    π_ (n : ℕ) (weakProductDirectLimit X).toCompactlyGenerated (weakProductDirectLimitPoint X) ≃*
      weakProductHomotopyGroupDirectSum n X :=
  { toFun := weakProductHomotopyGroupDirectSumProjection n X
    invFun := weakProductHomotopyGroupMulEquivDirectSumInvFun n X
    left_inv := weakProductHomotopyGroup_mulEquiv_directSum_left_inv n X
    right_inv := weakProductHomotopyGroup_mulEquiv_directSum_right_inv n X
    map_mul' := map_mul (weakProductHomotopyGroupDirectSumProjection n X) }
