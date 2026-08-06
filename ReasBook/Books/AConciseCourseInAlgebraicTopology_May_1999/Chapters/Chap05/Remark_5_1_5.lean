import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.SeparatedMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4

universe u v

open Set Filter

/- Remark 5.1.5 (1): `isCompact_range` is the canonical theorem stating that the image of a
continuous map from a compact space is compact. -/
#check isCompact_range

/-- Helper for Remark 5.1.5: a weak Hausdorff space is `T1`. -/
lemma weaklyHausdorff_t1 (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X] :
    T1Space X := by
  -- Reduce `T1` to closed singletons coming from compact Hausdorff one-point sources.
  refine ⟨fun x ↦ ?_⟩
  simpa [Set.range_const] using
    (show IsClosed (Set.range (fun _ : ULift.{v} Unit ↦ x)) from
      (show Continuous (fun _ : ULift.{v} Unit ↦ x) from continuous_const).isClosed_range)

/-- Helper for Remark 5.1.5: a surjective closed map from a compact Hausdorff space to a `T1`
space has Hausdorff codomain. -/
lemma t2Space_of_surjective_closedMap_from_compactHausdorff
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] [T1Space X]
    {f : K → X} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) : T2Space X := by
  rw [t2Space_iff]
  intro x y hxy
  let A : Set K := f ⁻¹' {x}
  let B : Set K := f ⁻¹' {y}
  have hAClosed : IsClosed A := by simpa [A] using isClosed_singleton.preimage hf_cont
  have hBClosed : IsClosed B := by simpa [B] using isClosed_singleton.preimage hf_cont
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
    rw [mem_compl_iff]
    intro hxU
    rcases hxU with ⟨a, haU, hfa⟩
    exact haU <| hAU <| by simp [A, hfa]
  · -- The whole fiber over `y` lies in `V`, so `y` avoids the image of `Vᶜ`.
    rw [mem_compl_iff]
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

/-- Helper for Remark 5.1.5: a closed equivalence relation has closed equivalence classes. -/
lemma isClosed_setOf_related_left
    {A : Type u} [TopologicalSpace A] (S : Setoid A)
    (hS : IsClosed ({p : A × A | S.r p.1 p.2} : Set (A × A))) (x : A) :
    IsClosed ({y : A | S.r y x} : Set A) := by
  let classMap : A → A × A := fun y ↦ (y, x)
  have hClassMap : Continuous classMap := continuous_id.prodMk continuous_const
  -- Fixing the second coordinate turns the left equivalence class into a closed pullback.
  simpa [classMap] using hS.preimage hClassMap

/-- Helper for Remark 5.1.5: a quotient by a closed relation is `T1`. -/
lemma t1Space_quotient_of_isClosedRelation
    {A : Type u} [TopologicalSpace A] (S : Setoid A)
    (hS : IsClosed ({p : A × A | S.r p.1 p.2} : Set (A × A))) :
    T1Space (Quotient S) := by
  let q : A → Quotient S := Quotient.mk'
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  refine ⟨?_⟩
  intro z
  refine Quotient.inductionOn' z fun x ↦ ?_
  have hClass : IsClosed ({y : A | S.r y x} : Set A) :=
    isClosed_setOf_related_left (A := A) S hS x
  have hPreimageEq :
      q ⁻¹' ({(Quotient.mk' x : Quotient S)} : Set (Quotient S)) =
        ({y : A | S.r y x} : Set A) := by
    -- The fiber of a quotient point is exactly its equivalence class upstairs.
    ext y
    change ((Quotient.mk' y : Quotient S) = Quotient.mk' x) ↔ S.r y x
    simpa using (Quotient.eq'' : (Quotient.mk' y : Quotient S) = Quotient.mk' x ↔ S.r y x)
  have hPreimage :
      IsClosed (q ⁻¹' ({(Quotient.mk' x : Quotient S)} : Set (Quotient S))) := by
    rw [hPreimageEq]
    exact hClass
  exact (hq.isClosed_preimage (s := ({(Quotient.mk' x : Quotient S)} : Set (Quotient S)))).1
    hPreimage

/-- Helper for Remark 5.1.5: the quotient map from a compact Hausdorff space by a closed
equivalence relation is closed. -/
lemma isClosedMapQuotientMkOfClosedRelation
    {A : Type u} [TopologicalSpace A] [CompactSpace A] [T2Space A] (S : Setoid A)
    (hS : IsClosed ({p : A × A | S.r p.1 p.2} : Set (A × A))) :
    IsClosedMap (Quotient.mk' : A → Quotient S) := by
  let q : A → Quotient S := Quotient.mk'
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  intro C hC
  let witnessSet : Set (A × A) := {p : A × A | S.r p.1 p.2} ∩ Prod.snd ⁻¹' C
  have hWitnessClosed : IsClosed witnessSet := by
    -- Intersect the closed relation with the closed cylinder over the source subset.
    exact hS.inter (hC.preimage continuous_snd)
  have hWitnessCompact : IsCompact witnessSet :=
    isCompact_univ.of_isClosed_subset hWitnessClosed (by simp [witnessSet])
  have hImageClosed : IsClosed (Prod.fst '' witnessSet : Set A) :=
    hWitnessCompact.image continuous_fst |>.isClosed
  have hPreimageEq :
      q ⁻¹' (q '' C) = (Prod.fst '' witnessSet : Set A) := by
    -- A point maps into `q '' C` exactly when it is related to some point of `C`.
    ext y
    constructor
    · rintro ⟨x, hxC, hxy⟩
      have hRel : S.r y x := by
        have hRel' : S.r x y := by
          simpa [q] using
            (Quotient.eq'' : (Quotient.mk' x : Quotient S) = Quotient.mk' y ↔ S.r x y).mp hxy
        exact S.symm hRel'
      exact ⟨(y, x), ⟨hRel, hxC⟩, rfl⟩
    · rintro ⟨⟨y', x⟩, ⟨hyx, hxC⟩, hy'⟩
      have hy'' : y' = y := by simpa using hy'
      exact ⟨x, hxC, by
        have hEq : (Quotient.mk' y' : Quotient S) = Quotient.mk' x := by
          exact (Quotient.eq'').2 hyx
        simpa [q, hy''] using hEq.symm⟩
  have hPreimageClosed : IsClosed (q ⁻¹' (q '' C)) := by
    rw [hPreimageEq]
    exact hImageClosed
  exact (hq.isClosed_preimage (s := q '' C)).1 hPreimageClosed

/-- Helper for Remark 5.1.5: a quotient of a compact Hausdorff space by a closed equivalence
relation is Hausdorff. -/
lemma t2SpaceQuotientOfClosedRelation
    {A : Type u} [TopologicalSpace A] [CompactSpace A] [T2Space A] (S : Setoid A)
    (hS : IsClosed ({p : A × A | S.r p.1 p.2} : Set (A × A))) :
    T2Space (Quotient S) := by
  let q : A → Quotient S := Quotient.mk'
  have hqCont : Continuous q := continuous_quotient_mk'
  have hqSurj : Function.Surjective q := Quotient.mk'_surjective
  have hqClosed : IsClosedMap q := isClosedMapQuotientMkOfClosedRelation (A := A) S hS
  let _ : T1Space (Quotient S) := t1Space_quotient_of_isClosedRelation (A := A) S hS
  -- A closed surjection from a compact Hausdorff source upgrades the quotient to Hausdorff.
  exact t2Space_of_surjective_closedMap_from_compactHausdorff hqCont hqSurj hqClosed

/-- Helper for Remark 5.1.5: a continuous map from a compact Hausdorff space into a weak
Hausdorff space is a closed map. -/
lemma isClosedMap_of_continuous_to_weaklyHausdorff
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] [WeaklyHausdorffSpace.{v, u} X]
    {f : K → X} (hf : Continuous f) : IsClosedMap f := by
  intro s hs
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  -- Closed subsets of a compact Hausdorff source are compact Hausdorff, so their images are
  -- closed by weak Hausdorffness.
  let hX : WeaklyHausdorffSpace X := inferInstance
  simpa [Set.range_restrict] using
    (show IsClosed (Set.range (s.restrict f)) from
      hX.isClosed_range (s.restrict f) (show Continuous (s.restrict f) from
        hf.comp continuous_subtype_val))

/-- Helper for Remark 5.1.5: the image of a compact Hausdorff source map into a weak Hausdorff
space is Hausdorff as a subspace. -/
lemma range_t2Space_of_compactHausdorffMap
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X] {g : K → X}
    (hg : Continuous g) : T2Space (Set.range g) := by
  let gRange : K → Set.range g := fun k ↦ ⟨g k, ⟨k, rfl⟩⟩
  have hgRange : Continuous gRange := hg.subtype_mk fun k ↦ ⟨k, rfl⟩
  have hgRange_surj : Function.Surjective gRange := by
    -- Every point of the range subtype comes from its chosen source witness.
    rintro ⟨x, ⟨k, rfl⟩⟩
    exact ⟨k, rfl⟩
  let _ : WeaklyHausdorffSpace (Set.range g) := inferInstance
  have hgRange_closed : IsClosedMap gRange :=
    isClosedMap_of_continuous_to_weaklyHausdorff hgRange
  let _ : T1Space (Set.range g) := weaklyHausdorff_t1 (Set.range g)
  -- The range factorization is a closed surjection from a compact Hausdorff source.
  exact
    t2Space_of_surjective_closedMap_from_compactHausdorff
      hgRange hgRange_surj hgRange_closed

/-- Helper for Remark 5.1.5: products of weak Hausdorff spaces are weak Hausdorff. -/
lemma weaklyHausdorffSpaceProd_direct
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyHausdorffSpace.{u, max u v} X] [WeaklyHausdorffSpace.{v, max u v} Y] :
    WeaklyHausdorffSpace.{max u v, max u v} (X × Y) := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  let gLeft : K → X := fun k ↦ (g k).1
  let gRight : K → Y := fun k ↦ (g k).2
  have hgLeft : Continuous gLeft := hg.fst
  have hgRight : Continuous gRight := hg.snd
  let rectangle : Set (X × Y) := Set.range gLeft ×ˢ Set.range gRight
  let _ : T2Space (Set.range gLeft) :=
    range_t2Space_of_compactHausdorffMap (X := X) hgLeft
  let _ : T2Space (Set.range gRight) :=
    range_t2Space_of_compactHausdorffMap (X := Y) hgRight
  have hLeftClosed : IsClosed (Set.range gLeft) := Continuous.isClosed_range hgLeft
  have hRightClosed : IsClosed (Set.range gRight) := Continuous.isClosed_range hgRight
  have hRectangleClosed : IsClosed rectangle := hLeftClosed.prod hRightClosed
  let rectangleMap : K → rectangle := fun k ↦ ⟨g k, ⟨⟨k, rfl⟩, ⟨k, rfl⟩⟩⟩
  let rectangleHomeomorph : Set.range gLeft × Set.range gRight ≃ₜ rectangle :=
    (Homeomorph.Set.prod (Set.range gLeft) (Set.range gRight)).symm
  let _ : T2Space rectangle := rectangleHomeomorph.t2Space
  have hRectangleMap : Continuous rectangleMap := by
    -- The compact-source map lands in the coordinate rectangle by construction.
    exact hg.subtype_mk fun k ↦ ⟨⟨k, rfl⟩, ⟨k, rfl⟩⟩
  have hClosedRangeRectangle : IsClosed (Set.range rectangleMap) :=
    Continuous.isClosed_range hRectangleMap
  have hClosedImage :
      IsClosed (((↑) : rectangle → X × Y) '' Set.range rectangleMap) :=
    hRectangleClosed.isClosedMap_subtype_val _ hClosedRangeRectangle
  have hRangeEq : ((↑) : rectangle → X × Y) '' Set.range rectangleMap = Set.range g := by
    -- Forgetting the rectangle subtype recovers exactly the original image in the ambient product.
    ext p
    constructor
    · rintro ⟨q, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨rectangleMap k, ⟨k, rfl⟩, rfl⟩
  simpa [hRangeEq] using hClosedImage

/-- Helper for Remark 5.1.5: the canonical compactness limit of a principal ultrafilter is the
underlying point in a compact weak Hausdorff space. -/
lemma ultrafilterLim_pure
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, v} X]
    (x : X) : (pure x : Ultrafilter X).lim = x := by
  let _ : T1Space X := weaklyHausdorff_t1 X
  -- A principal ultrafilter already converges to its generating point.
  have hlim : (pure x : Filter X) ≤ nhds ((pure x : Ultrafilter X).lim) :=
    Ultrafilter.le_nhds_lim (pure x)
  -- In a `T1` space, a principal ultrafilter has only one possible limit.
  exact (pure_le_nhds_iff.mp hlim).symm

/-- Helper for Remark 5.1.5: the compactness limit map `Ultrafilter X → X` is surjective on a
compact weak Hausdorff space. -/
lemma ultrafilterLim_surjective
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, v} X] :
    Function.Surjective (Ultrafilter.lim : Ultrafilter X → X) := by
  -- Principal ultrafilters witness every point in the codomain.
  intro x
  refine ⟨pure x, ?_⟩
  simpa using ultrafilterLim_pure (X := X) x

/-- Helper for Remark 5.1.5: after applying `T2Quotient.mk`, the compactness limit map agrees
with the Stone-Cech extension of `T2Quotient.mk`. -/
lemma t2Quotient_mk_ultrafilterLim
    {X : Type u} [TopologicalSpace X] [CompactSpace X] (F : Ultrafilter X) :
    T2Quotient.mk F.lim = Ultrafilter.extend T2Quotient.mk F := by
  -- Local instance justification (quotient compactness): `T2Quotient X` is definitionally a
  -- quotient of the compact space `X`, but typeclass search does not unfold `T2Quotient` here.
  let _ : CompactSpace (T2Quotient X) := by
    change CompactSpace (Quotient (t2Setoid X))
    infer_instance
  -- The quotient image of a chosen limit is characterized by the usual Stone-Cech extension API.
  symm
  apply (ultrafilter_extend_eq_iff (f := T2Quotient.mk) (b := F) (c := T2Quotient.mk F.lim)).2
  exact (T2Quotient.continuous_mk X).tendsto F.lim |>.mono_left (Ultrafilter.le_nhds_lim F)

/-- Helper for Remark 5.1.5: an ultrafilter converging to `x` has quotient-image limit
`T2Quotient.mk x`. -/
lemma t2QuotientMk_eq_of_ultrafilterLeNhds
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {F : Ultrafilter X} {x : X} (hx : (F : Filter X) ≤ nhds x) :
    T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F := by
  -- Local instance justification (quotient compactness): `ultrafilter_extend_eq_iff` needs
  -- compactness of the Hausdorff quotient, and typeclass search does not unfold the quotient here.
  let _ : CompactSpace (T2Quotient X) := by
    change CompactSpace (Quotient (t2Setoid X))
    infer_instance
  -- Turn convergence in `X` into the Stone-Cech characterization of the quotient extension.
  symm
  exact (ultrafilter_extend_eq_iff (f := T2Quotient.mk) (b := F) (c := T2Quotient.mk x)).2 <|
    (T2Quotient.continuous_mk X).tendsto x |>.mono_left hx

/-- Helper for Remark 5.1.5: equality in the Hausdorff quotient forces equality of the
Stone-Cech unit images. -/
lemma stoneCechUnit_eq_of_t2QuotientEq
    {X : Type u} [TopologicalSpace X] {x y : X}
    (h : T2Quotient.mk x = T2Quotient.mk y) :
    stoneCechUnit x = stoneCechUnit y := by
  -- Transport the quotient equality through the universal property of `T2Quotient`.
  have hxy : t2Setoid X x y := Quotient.exact h
  simpa using
    (T2Quotient.compatible
      (f := stoneCechUnit)
      continuous_stoneCechUnit x y hxy)

/-- Helper for Remark 5.1.5: the quotient equality determining an ultrafilter fiber also
identifies the Stone-Cech unit images of the point and the chosen compactness limit. -/
lemma stoneCechUnit_eq_of_ultrafilterLimitFiber
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {F : Ultrafilter X} {x : X}
    (hx : T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F) :
    stoneCechUnit x = stoneCechUnit F.lim := by
  -- Normalize the quotient equality using the chosen compactness limit of `F`.
  apply stoneCechUnit_eq_of_t2QuotientEq (X := X)
  exact hx.trans (t2Quotient_mk_ultrafilterLim (X := X) F).symm

/-- Helper for Remark 5.1.5: in an `R1Space`, equality in the Hausdorff quotient already means
the two points are inseparable. -/
lemma inseparable_of_t2QuotientEq_of_r1
    {X : Type u} [TopologicalSpace X] [R1Space X] {x y : X}
    (h : T2Quotient.mk x = T2Quotient.mk y) :
    Inseparable x y := by
  -- Instantiate the universal property of `T2Quotient` with the inseparability quotient.
  have hxy : (inseparableSetoid X) x y := by
    have hT2 : T2Space (Quotient (inseparableSetoid X)) := by
      -- Rewrite to the owner API `SeparationQuotient X` before applying the `R1 ↔ T2` bridge.
      change T2Space (SeparationQuotient X)
      simpa using
        (SeparationQuotient.t2Space_iff.mpr (inferInstance : R1Space X))
    exact (T2Quotient.mk_eq.mp h) (inseparableSetoid X) hT2
  -- Read the quotient relation back as the original inseparability predicate.
  simpa using hxy

/-- Helper for Remark 5.1.5: the Stone-Cech unit is constant on inseparable classes. -/
lemma stoneCechUnit_eq_of_inseparable
    {X : Type u} [TopologicalSpace X] {x y : X} (h : Inseparable x y) :
    stoneCechUnit x = stoneCechUnit y := by
  -- Continuous maps into Hausdorff targets identify inseparable source points.
  exact (h.map continuous_stoneCechUnit).eq

/-- Helper for Remark 5.1.5: the canonical comparison from the separation quotient to the
Stone-Cech compactification. -/
def separationQuotientToStoneCech
    (X : Type u) [TopologicalSpace X] : SeparationQuotient X → StoneCech X :=
  SeparationQuotient.lift
    (fun x : X ↦ stoneCechUnit x)
    (fun _ _ h ↦ stoneCechUnit_eq_of_inseparable h)

/-- Helper for Remark 5.1.5: the comparison map agrees with `stoneCechUnit` on quotient
representatives. -/
lemma separationQuotientToStoneCech_mk
    {X : Type u} [TopologicalSpace X] (x : X) :
    separationQuotientToStoneCech X (SeparationQuotient.mk x) = stoneCechUnit x := by
  -- Unpack the quotient lift on a chosen representative.
  simpa [separationQuotientToStoneCech] using
    (SeparationQuotient.lift_mk
      (f := fun y : X ↦ stoneCechUnit y)
      (hf := fun _ _ h ↦ stoneCechUnit_eq_of_inseparable h) x)

/-- Helper for Remark 5.1.5: the comparison map from the separation quotient to `StoneCech X`
is continuous. -/
lemma continuous_separationQuotientToStoneCech
    {X : Type u} [TopologicalSpace X] :
    Continuous (separationQuotientToStoneCech X) := by
  -- Continuity descends directly from the Stone-Cech unit through the quotient lift.
  simpa [separationQuotientToStoneCech] using
    (SeparationQuotient.continuous_lift
      (f := fun x : X ↦ stoneCechUnit x)
      (hf := fun _ _ h ↦ stoneCechUnit_eq_of_inseparable h)).2 continuous_stoneCechUnit

/-- Helper for Remark 5.1.5: the pushforward of ultrafilters is continuous. -/
lemma ultrafilterMap_continuous {α : Type*} {β : Type*} (m : α → β) :
    Continuous (Ultrafilter.map m) := by
  -- Use the Stone-Cech characterization of convergence of ultrafilters.
  rw [continuous_iff_ultrafilter]
  intro b F hF
  rw [Tendsto, ← Ultrafilter.coe_map, ultrafilter_converges_iff]
  rw [ultrafilter_converges_iff.mp hF]
  ext s
  change m ⁻¹' s ∈ joinM F ↔ {t : Ultrafilter α | m ⁻¹' s ∈ t} ∈ F
  rfl

/-- Helper for Remark 5.1.5: a map into a compact space is continuous once its graph is closed. -/
lemma continuous_of_isClosedGraph_compactCompact
    {K : Type u} [TopologicalSpace K]
    {Y : Type v} [TopologicalSpace Y] [CompactSpace Y]
    {f : K → Y} (hgraph : IsClosed (Set.range fun x => (x, f x))) : Continuous f := by
  -- Project the closed graph intersected with `K × s` to recover `f ⁻¹' s`.
  rw [continuous_iff_isClosed]
  intro s hs
  let graph : Set (K × Y) := Set.range fun x => (x, f x)
  have hclosed : IsClosed (graph ∩ Prod.snd ⁻¹' s) := by
    exact hgraph.inter (hs.preimage continuous_snd)
  have himage : Prod.fst '' (graph ∩ Prod.snd ⁻¹' s) = f ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨a, rfl⟩, hy⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨(x, f x), ⟨⟨x, rfl⟩, hx⟩, rfl⟩
  rw [← himage]
  exact isClosedMap_fst_of_compactSpace _ hclosed

/-- Helper for Remark 5.1.5: the convergence relation on `Ultrafilter X × X` is closed. -/
lemma ultrafilterConvergenceRelation_isClosed
    {X : Type u} [TopologicalSpace X] :
    IsClosed {p : Ultrafilter X × X | ((p.1 : Ultrafilter X) : Filter X) ≤ nhds p.2} := by
  -- A failed convergence inequality is witnessed by an open neighborhood missed by the ultrafilter.
  let C : Set (Ultrafilter X × X) := {p | ((p.1 : Ultrafilter X) : Filter X) ≤ nhds p.2}
  have hOpen : IsOpen Cᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hp' : ¬ ((p.1 : Ultrafilter X) : Filter X) ≤ nhds p.2 := by
      simpa [C] using hp
    rw [Filter.le_def] at hp'
    push Not at hp'
    rcases hp' with ⟨s, hsNhd, hsNotMem⟩
    rcases mem_nhds_iff.mp hsNhd with ⟨U, hUsub, hUopen, hpU⟩
    have hUNotMem : U ∉ (p.1 : Filter X) := by
      intro hU
      exact hsNotMem (mem_of_superset hU hUsub)
    let A : Set (Ultrafilter X) := {F | Uᶜ ∈ (F : Filter X)}
    have hAOpen : IsOpen A := by
      simpa [A, Ultrafilter.compl_mem_iff_notMem] using ultrafilter_isOpen_basic (Uᶜ)
    have hpA : p.1 ∈ A := by
      simpa [A, Ultrafilter.compl_mem_iff_notMem] using hUNotMem
    refine mem_of_superset ((hAOpen.prod hUopen).mem_nhds ⟨hpA, hpU⟩) ?_
    rintro ⟨F, x⟩ ⟨hFA, hxU⟩
    change ¬ ((F : Filter X) ≤ nhds x)
    intro hconv
    have hU : U ∈ (F : Filter X) := hconv (hUopen.mem_nhds hxU)
    have hUCompl : Uᶜ ∈ (F : Filter X) := hFA
    have hEmpty : (∅ : Set X) ∈ (F : Filter X) := by
      simpa using inter_mem hU hUCompl
    exact F.neBot.ne (empty_mem_iff_bot.mp hEmpty)
  simpa [C] using isOpen_compl_iff.mp hOpen

/-- Helper for Remark 5.1.5: two ultrafilters are related when they share a common limit. -/
def ultrafilterCommonLimitRel
    {X : Type u} [TopologicalSpace X] (F G : Ultrafilter X) : Prop :=
  ∃ x, ((F : Filter X) ≤ nhds x) ∧ ((G : Filter X) ≤ nhds x)

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, the common-limit relation on
ultrafilters is closed. -/
lemma ultrafilterCommonLimitRelation_isClosed
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    IsClosed
      {p : Ultrafilter X × Ultrafilter X | ultrafilterCommonLimitRel p.1 p.2} := by
  let conv : Set (Ultrafilter X × X) := {p | ((p.1 : Ultrafilter X) : Filter X) ≤ nhds p.2}
  have hConv : IsClosed conv := ultrafilterConvergenceRelation_isClosed (X := X)
  let leftMap : (Ultrafilter X × Ultrafilter X) × X → Ultrafilter X × X := fun p ↦ (p.1.1, p.2)
  let rightMap : (Ultrafilter X × Ultrafilter X) × X → Ultrafilter X × X := fun p ↦ (p.1.2, p.2)
  let witnessSet : Set ((Ultrafilter X × Ultrafilter X) × X) :=
    leftMap ⁻¹' conv ∩ rightMap ⁻¹' conv
  have hWitnessClosed : IsClosed witnessSet := by
    -- A common-limit witness is exactly a simultaneous membership condition in the closed
    -- convergence relation for the two coordinate ultrafilters.
    exact
      (hConv.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
        (hConv.preimage (continuous_fst.snd.prodMk continuous_snd))
  have hWitnessCompact : IsCompact witnessSet :=
    isCompact_univ.of_isClosed_subset hWitnessClosed (by simp [witnessSet])
  have hImageClosed :
      IsClosed (Prod.fst '' witnessSet : Set (Ultrafilter X × Ultrafilter X)) :=
    hWitnessCompact.image continuous_fst |>.isClosed
  have hImageEq :
      Prod.fst '' witnessSet =
        {p : Ultrafilter X × Ultrafilter X | ultrafilterCommonLimitRel p.1 p.2} := by
    -- Forgetting the witness coordinate recovers exactly the common-limit relation.
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq.1, hq.2⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨((p.1, p.2), x), ⟨hx, hy⟩, rfl⟩
  simpa [hImageEq] using hImageClosed

/-- Helper for Remark 5.1.5: on a compact source, the canonical map to the Hausdorff quotient is
a closed map. -/
lemma isClosedMap_t2QuotientMk_of_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    IsClosedMap (T2Quotient.mk : X → T2Quotient X) := by
  intro s hs
  -- Closed subsets of a compact space are compact, and compact subsets of the Hausdorff quotient
  -- are closed.
  have hCompact : IsCompact s := isCompact_univ.of_isClosed_subset hs (by simp)
  exact hCompact.image (T2Quotient.continuous_mk X) |>.isClosed

/-- Helper for Remark 5.1.5: each fiber of `T2Quotient.mk` is compact when the source is compact.
-/
lemma compactSpace_t2QuotientFiber
    {X : Type u} [TopologicalSpace X] [CompactSpace X] (q : T2Quotient X) :
    CompactSpace {x : X // T2Quotient.mk x = q} := by
  let fiberSet : Set X := {x | T2Quotient.mk x = q}
  have hClosed : IsClosed fiberSet := by
    -- The fiber is the preimage of a singleton under the continuous quotient map.
    exact isClosed_singleton.preimage (T2Quotient.continuous_mk X)
  exact isCompact_iff_compactSpace.mp <|
    isCompact_univ.of_isClosed_subset hClosed (by simp)

/-- Helper for Remark 5.1.5: equality in `PreStoneCech X` already forces equality in the largest
Hausdorff quotient of `X`. -/
lemma t2QuotientEq_of_preStoneCechUnitEq
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {x y : X} (h : preStoneCechUnit x = preStoneCechUnit y) :
    T2Quotient.mk x = T2Quotient.mk y := by
  -- Evaluate the `PreStoneCech` universal property on the compact Hausdorff target `T2Quotient X`.
  let _ : CompactSpace (T2Quotient X) := by
    change CompactSpace (Quotient (t2Setoid X))
    infer_instance
  exact eq_if_preStoneCechUnit_eq (g := T2Quotient.mk) (T2Quotient.continuous_mk X) h

/-- Helper for Remark 5.1.5: Stone-Cech equality already forces equality in the largest Hausdorff
quotient of `X`. -/
lemma t2QuotientEq_of_stoneCechUnitEq
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {x y : X} (h : stoneCechUnit x = stoneCechUnit y) :
    T2Quotient.mk x = T2Quotient.mk y := by
  -- Evaluate the `StoneCech` universal property on the compact Hausdorff target `T2Quotient X`.
  let _ : CompactSpace (T2Quotient X) := by
    change CompactSpace (Quotient (t2Setoid X))
    infer_instance
  exact eq_if_stoneCechUnit_eq (f := T2Quotient.mk) (T2Quotient.continuous_mk X) h

/-- Helper for Remark 5.1.5: the union of two compact Hausdorff images in a weak Hausdorff space
is Hausdorff. This local copy is placed before the quotient-kernel argument because the diagonal
pullback bridge needs compact-source equalizers first. -/
lemma unionRange_t2Space_of_compactHausdorffMaps_local
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → X} (hf : Continuous f) (hg : Continuous g) :
    T2Space ((Set.range f ∪ Set.range g : Set X)) := by
  let h : K ⊕ K → (Set.range f ∪ Set.range g : Set X) :=
    Sum.elim
      (fun x ↦ ⟨f x, Or.inl ⟨x, rfl⟩⟩)
      (fun x ↦ ⟨g x, Or.inr ⟨x, rfl⟩⟩)
  -- The copair map is continuous because each branch lands in the union subtype.
  have hh_cont : Continuous h := by
    rw [continuous_sumElim]
    constructor
    · exact Continuous.subtype_mk hf fun x ↦ Or.inl ⟨x, rfl⟩
    · exact Continuous.subtype_mk hg fun x ↦ Or.inr ⟨x, rfl⟩
  let _ : WeaklyHausdorffSpace ((Set.range f ∪ Set.range g : Set X)) := inferInstance
  let _ : T1Space ((Set.range f ∪ Set.range g : Set X)) :=
    weaklyHausdorff_t1 ((Set.range f ∪ Set.range g : Set X))
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

/-- Helper for Remark 5.1.5: equalizers of compact-Hausdorff source maps into a weak Hausdorff
space are closed. -/
lemma isClosed_eqLocus_of_continuous_compHaus_local
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed {k : K | f k = g k} := by
  let U : Set X := Set.range f ∪ Set.range g
  let f' : K → U := fun k ↦ ⟨f k, Or.inl ⟨k, rfl⟩⟩
  let g' : K → U := fun k ↦ ⟨g k, Or.inr ⟨k, rfl⟩⟩
  have hf' : Continuous f' := Continuous.subtype_mk hf fun k ↦ Or.inl ⟨k, rfl⟩
  have hg' : Continuous g' := Continuous.subtype_mk hg fun k ↦ Or.inr ⟨k, rfl⟩
  let _ : T2Space U := unionRange_t2Space_of_compactHausdorffMaps_local hf hg
  -- Move the equalizer into the Hausdorff union-range subtype and apply `isClosed_eq`.
  simpa [U, f', g'] using isClosed_eq hf' hg'

/-- Helper for Remark 5.1.5: compact-Hausdorff probes pull the diagonal back to a closed
equalizer. -/
lemma preimage_diagonal_isClosed_of_continuous_compHaus_local
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g : K → X × X} (hg : Continuous g) :
    IsClosed (g ⁻¹' diagonal X) := by
  -- Pulling back the diagonal is exactly the equalizer of the coordinate projections of `g`.
  simpa [Set.diagonal, Set.preimage, Prod.mk.eta] using
    (isClosed_eqLocus_of_continuous_compHaus_local
      (X := X) (f := fun k ↦ (g k).1) (g := fun k ↦ (g k).2) hg.fst hg.snd)

/-- Helper for Remark 5.1.5: a compact Hausdorff source map stays continuous after replacing the
codomain by its compactly generated topology. -/
lemma continuousCompHausToCompactlyGenerated_local
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type u} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K›
      (TopologicalSpace.compactlyGenerated.{u, u} Z) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators defining the compactly generated
  -- topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Z),
        @Continuous j.fst Z inferInstance (TopologicalSpace.compactlyGenerated.{u, u} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Remark 5.1.5: a set is closed in the compactly generated topology once every
compact Hausdorff probe pulls it back to a closed set. -/
lemma isClosed_compactlyGenerated_of_compHausClosed_local
    {Z : Type u} [TopologicalSpace Z] {A : Set Z}
    (hA : ∀ (S : CompHaus.{u}) (f : C(S, Z)), IsClosed (f ⁻¹' A)) :
    @IsClosed Z (TopologicalSpace.compactlyGenerated.{u, u} Z) A := by
  -- Unfold the coinduced owner and check closedness on each compact Hausdorff generator.
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  rintro ⟨S, f⟩
  exact hA S f

/-- Helper for Remark 5.1.5: on a `T1` space, the identity factors continuously through the
separation quotient. -/
lemma continuousSeparationQuotientLiftId_of_t1_local
    {X : Type u} [TopologicalSpace X] [T1Space X] :
    Continuous
      (SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq) :
        SeparationQuotient X → X) := by
  let _ : T0Space X := inferInstance
  -- In a `T1` space, inseparable points are equal, so the quotient lift of `id` is continuous.
  simpa only using
    (SeparationQuotient.continuous_lift
      (f := fun x : X ↦ x)
      (hf := fun _ _ h ↦ h.eq)).2 continuous_id

/-- Helper for Remark 5.1.5: on a `T1` space, the quotient map followed by the identity lift is
the identity on the separation quotient. -/
lemma separationQuotient_mk_comp_liftId_of_t1_local
    {X : Type u} [TopologicalSpace X] [T1Space X] :
    SeparationQuotient.mk ∘
        (SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq) :
          SeparationQuotient X → X) =
      id := by
  -- Check the quotient identity on representatives and then descend through quotient induction.
  ext q
  refine Quotient.inductionOn' q fun x ↦ ?_
  -- Rewrite the representative to the public quotient-map spelling before simplifying the lift.
  change
    SeparationQuotient.mk
        ((SeparationQuotient.lift (fun y : X ↦ y) (fun _ _ h ↦ h.eq))
          (SeparationQuotient.mk x)) =
      SeparationQuotient.mk x
  -- On representatives the identity lift evaluates to the original point.
  simpa using
    congrArg SeparationQuotient.mk
      (SeparationQuotient.lift_mk (f := fun y : X ↦ y) (hf := fun _ _ h ↦ h.eq) x)

/-- Helper for Remark 5.1.5: the separation quotient of a weak Hausdorff space is weak Hausdorff.
This local bridge is needed before the closed-kernel step can specialize the quotient-diagonal
criterion. -/
lemma weaklyHausdorffSpace_separationQuotient_local
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    WeaklyHausdorffSpace.{u, u} (SeparationQuotient X) := by
  let _ : T1Space X := weaklyHausdorff_t1 X
  let liftId : SeparationQuotient X → X :=
    SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq)
  have hLiftId : Continuous liftId := continuousSeparationQuotientLiftId_of_t1_local (X := X)
  have hMkLiftId :
      SeparationQuotient.mk ∘ liftId = id :=
    separationQuotient_mk_comp_liftId_of_t1_local (X := X)
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  have hClosedRangeLift :
      IsClosed (Set.range (liftId ∘ g)) :=
    Continuous.isClosed_range (hLiftId.comp hg)
  have hClosedMk : IsClosedMap (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.isClosedMap_mk
  have hRangeEq :
      SeparationQuotient.mk '' Set.range (liftId ∘ g) = Set.range g := by
    -- Apply the quotient map after the lift; the right-inverse identity recovers the original map.
    ext q
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, hx⟩
      exact ⟨k, (congr_fun hMkLiftId (g k)).symm.trans hx⟩
    · rintro ⟨k, rfl⟩
      exact ⟨liftId (g k), ⟨k, rfl⟩, congr_fun hMkLiftId (g k)⟩
  -- Closedness of the lifted range descends through the closed quotient map.
  simpa [hRangeEq] using hClosedMk _ hClosedRangeLift

/-- Helper for Remark 5.1.5: if the codomain of a quotient map is weak Hausdorff, then the
pullback of its diagonal along the square map is closed in the source product. -/
lemma isClosed_preimageDiagonal_of_isQuotientMap_local
    {A : Type u} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [CompactlyGeneratedSpace (A × A)] [WeaklyHausdorffSpace.{u, u} B]
    (π : A → B) (hπ : Topology.IsQuotientMap π) :
    IsClosed ((Prod.map π π) ⁻¹' diagonal B) := by
  have hDiagonalCG :
      @IsClosed (B × B) (TopologicalSpace.compactlyGenerated.{u, u} (B × B)) (diagonal B) := by
    -- Check diagonal closedness against compact Hausdorff probes into `B × B`.
    refine isClosed_compactlyGenerated_of_compHausClosed_local ?_
    intro S f
    exact preimage_diagonal_isClosed_of_continuous_compHaus_local (X := B) f.continuous
  have hProdCG :
      @Continuous (A × A) (B × B) instTopologicalSpaceProd
        (TopologicalSpace.compactlyGenerated.{u, u} (B × B)) (Prod.map π π) := by
    -- Test continuity of the square map on compact Hausdorff probes into `A × A`.
    let _ : UCompactlyGeneratedSpace.{u} (A × A) :=
      inferInstanceAs (CompactlyGeneratedSpace (A × A))
    let squareMap : A × A → B × B := Prod.map π π
    refine
      @continuous_from_uCompactlyGeneratedSpace (A × A) (B × B)
        instTopologicalSpaceProd
        (TopologicalSpace.compactlyGenerated.{u, u} (B × B))
        ‹UCompactlyGeneratedSpace.{u} (A × A)›
        squareMap
        ?_
    intro K g
    have hCompOrdinary : Continuous (squareMap ∘ g) := by
      have hLeft : Continuous fun k : K ↦ π (g k).1 := hπ.continuous.comp g.continuous.fst
      have hRight : Continuous fun k : K ↦ π (g k).2 := hπ.continuous.comp g.continuous.snd
      change Continuous fun k : K ↦ (π (g k).1, π (g k).2)
      exact hLeft.prodMk hRight
    simpa [Function.comp] using
      (continuousCompHausToCompactlyGenerated_local
        (K := K) (Z := B × B) (f := squareMap ∘ g) hCompOrdinary)
  -- Pull back the closed diagonal in the compactly generated codomain product.
  have hPreimage :
      @IsClosed (A × A) instTopologicalSpaceProd
        ((Prod.map π π) ⁻¹' diagonal B) :=
    @IsClosed.preimage (A × A) (B × B) instTopologicalSpaceProd
      (TopologicalSpace.compactlyGenerated.{u, u} (B × B))
      (Prod.map π π) hProdCG (diagonal B) hDiagonalCG
  exact hPreimage

/-- Helper for Remark 5.1.5: the separation-quotient kernel is exactly the inseparability
relation. -/
lemma separationQuotientKernel_eq_inseparableRelation
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    ({p : X × X | SeparationQuotient.mk p.1 = SeparationQuotient.mk p.2} : Set (X × X)) =
      ({p : X × X | Inseparable p.1 p.2} : Set (X × X)) := by
  -- Rewrite the quotient equality pointwise using the owner API for `SeparationQuotient`.
  ext p
  simp [SeparationQuotient.mk_eq_mk]

/-- Helper for Remark 5.1.5: for a fixed point `x`, the ultrafilters whose `T2Quotient`-image
limit is `T2Quotient.mk x` form a closed subset of `Ultrafilter X`. -/
lemma isClosed_t2QuotientLimitFiber
    {X : Type u} [TopologicalSpace X] [CompactSpace X] (x : X) :
    IsClosed {F : Ultrafilter X | Ultrafilter.extend T2Quotient.mk F = T2Quotient.mk x} := by
  -- Local instance justification (quotient compactness): the Stone-Cech extension API for
  -- `Ultrafilter.extend` needs compactness of `T2Quotient X`, and typeclass search does not
  -- unfold the quotient definition here.
  let _ : CompactSpace (T2Quotient X) := by
    change CompactSpace (Quotient (t2Setoid X))
    infer_instance
  -- The fiber is the singleton preimage of the continuous quotient-limit map.
  simpa using
    (isClosed_singleton.preimage (continuous_ultrafilter_extend (f := T2Quotient.mk)))

/-- Helper for Remark 5.1.5: equality in the Hausdorff quotient reflects actual equality once the
source is already Hausdorff. -/
lemma eq_of_t2QuotientEq_of_t2
    {X : Type u} [TopologicalSpace X] [T2Space X] {x y : X}
    (h : T2Quotient.mk x = T2Quotient.mk y) :
    x = y := by
  -- Apply the universal property of `T2Quotient` to the identity map on the Hausdorff source.
  exact
    T2Quotient.compatible
      (X := X) (Y := X) (f := id) continuous_id x y (Quotient.exact h)

/-- Helper for Remark 5.1.5: in a Hausdorff compact space, the `T2Quotient`-fiber identity for an
ultrafilter already forces the point to be the chosen compactness limit. -/
lemma ultrafilterLimit_eq_of_t2QuotientEq_of_t2
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F : Ultrafilter X} {x : X} (hx : T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F) :
    x = F.lim := by
  -- Normalize the fiber equation to equality of quotient-images of the two candidate limits.
  exact eq_of_t2QuotientEq_of_t2 <| hx.trans (t2Quotient_mk_ultrafilterLim (X := X) F).symm

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, equality of the quotient-images of
`x` and the chosen compactness limit of `F` forces `x = F.lim`. -/
lemma ultrafilterLimit_eq_of_t2QuotientEq
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {F : Ultrafilter X} {x : X} (hx : T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F) :
    x = F.lim := by
  let _ : T1Space X := weaklyHausdorff_t1 X
  -- Route correction: the downstream inseparability lemmas now sit after
  -- `compactWeaklyHausdorff_t2Space`, so the only remaining blocker is the noncircular pointwise
  -- uniqueness bridge from a `T2Quotient`-fiber equality to an actual equality in `X`.
  -- TODO: use `isClosed_t2QuotientLimitFiber` to turn the quotient-fiber condition into a direct
  -- common-limit witness for `pure x` and `F`; after that, `ultrafilterLimit_eq_of_t2QuotientEq_of_t2`
  -- shows the final equality once the noncircular Hausdorff bridge is in place.
  sorry

/-- Helper for Remark 5.1.5: convergence of an ultrafilter to `x` is equivalent to the equality
`T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F` once the compact weak Hausdorff uniqueness
bridge is available. -/
lemma ultrafilterConvergenceRelation_eq_t2QuotientEqLocus
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {F : Ultrafilter X} {x : X} :
    ((F : Filter X) ≤ nhds x) ↔ T2Quotient.mk x = Ultrafilter.extend T2Quotient.mk F := by
  constructor
  · -- Normalize actual convergence to an equality in the Hausdorff quotient.
    intro hx
    exact t2QuotientMk_eq_of_ultrafilterLeNhds (F := F) hx
  · intro hx
    -- The reverse direction reduces to uniqueness of limits in the compact weak Hausdorff target.
    have hEq : x = F.lim := ultrafilterLimit_eq_of_t2QuotientEq (F := F) hx
    simpa [hEq] using (Ultrafilter.le_nhds_lim F)

/-- Helper for Remark 5.1.5: the union of two compact Hausdorff images in a weak Hausdorff space
is Hausdorff. -/
lemma unionRange_t2Space_of_compactHausdorffMaps
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → X} (hf : Continuous f) (hg : Continuous g) :
    T2Space ((Set.range f ∪ Set.range g : Set X)) := by
  let h : K ⊕ K → (Set.range f ∪ Set.range g : Set X) :=
    Sum.elim
      (fun x ↦ ⟨f x, Or.inl ⟨x, rfl⟩⟩)
      (fun x ↦ ⟨g x, Or.inr ⟨x, rfl⟩⟩)
  -- The copair map is continuous because each branch lands in the union subtype.
  have hh_cont : Continuous h := by
    rw [continuous_sumElim]
    constructor
    · exact Continuous.subtype_mk hf fun x ↦ Or.inl ⟨x, rfl⟩
    · exact Continuous.subtype_mk hg fun x ↦ Or.inr ⟨x, rfl⟩
  let _ : WeaklyHausdorffSpace ((Set.range f ∪ Set.range g : Set X)) := inferInstance
  let _ : T1Space ((Set.range f ∪ Set.range g : Set X)) :=
    weaklyHausdorff_t1 ((Set.range f ∪ Set.range g : Set X))
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

/-- Helper for Remark 5.1.5: equalizers of maps from a compact Hausdorff space into a weak
Hausdorff space are closed. -/
lemma isClosed_eqLocus_of_continuous_compHaus
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f g : K → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed {k : K | f k = g k} := by
  let U : Set X := Set.range f ∪ Set.range g
  let f' : K → U := fun k ↦ ⟨f k, Or.inl ⟨k, rfl⟩⟩
  let g' : K → U := fun k ↦ ⟨g k, Or.inr ⟨k, rfl⟩⟩
  have hf' : Continuous f' := Continuous.subtype_mk hf fun k ↦ Or.inl ⟨k, rfl⟩
  have hg' : Continuous g' := Continuous.subtype_mk hg fun k ↦ Or.inr ⟨k, rfl⟩
  let _ : T2Space U := unionRange_t2Space_of_compactHausdorffMaps hf hg
  -- Move the equalizer into the Hausdorff union-range subtype and apply `isClosed_eq`.
  simpa [U, f', g'] using isClosed_eq hf' hg'

/-- Helper for Remark 5.1.5: a compact Hausdorff probe into `X × X` pulls the diagonal back to the
equalizer of its two coordinate maps. -/
lemma preimage_diagonal_isClosed_of_continuous_compHaus
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g : K → X × X} (hg : Continuous g) :
    IsClosed (g ⁻¹' diagonal X) := by
  -- Pulling back the diagonal is exactly the equalizer of the coordinate projections of `g`.
  simpa [Set.diagonal, Set.preimage, Prod.mk.eta] using
    (isClosed_eqLocus_of_continuous_compHaus
      (X := X) (f := fun k ↦ (g k).1) (g := fun k ↦ (g k).2) hg.fst hg.snd)

/-- Helper for Remark 5.1.5: a continuous retraction of `pure : X → Ultrafilter X` from the
compact Hausdorff ultrafilter space forces a compact weak Hausdorff space to be Hausdorff. -/
lemma t2Space_of_continuousUltrafilterRetraction
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {e : Ultrafilter X → X} (he_cont : Continuous e) (he_pure : e ∘ pure = id) :
    T2Space X := by
  let _ : T1Space X := weaklyHausdorff_t1 X
  have he_surj : Function.Surjective e := by
    -- Principal ultrafilters witness surjectivity because `e` retracts `pure`.
    intro x
    refine ⟨pure x, ?_⟩
    simpa [Function.comp_apply] using congr_fun he_pure x
  have he_closed : IsClosedMap e := isClosedMap_of_continuous_to_weaklyHausdorff he_cont
  -- The compact Hausdorff ultrafilter space now gives the closed-surjection criterion.
  exact t2Space_of_surjective_closedMap_from_compactHausdorff he_cont he_surj he_closed

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, the graph of the chosen
compactness-limit map `Ultrafilter.lim` is closed. -/
lemma ultrafilterLim_graph_isClosed
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    IsClosed (Set.range fun F : Ultrafilter X ↦ (F, F.lim)) := by
  -- Identify the graph with the already-closed convergence relation.
  have hEq :
      {p : Ultrafilter X × X | ((p.1 : Ultrafilter X) : Filter X) ≤ nhds p.2} =
        Set.range (fun F : Ultrafilter X ↦ (F, F.lim)) := by
    ext p
    rcases p with ⟨F, x⟩
    constructor
    · intro hx
      -- Use the quotient normalization to recover the actual chosen limit.
      have hEqLimit : x = F.lim := ultrafilterLimit_eq_of_t2QuotientEq (F := F) <|
        t2QuotientMk_eq_of_ultrafilterLeNhds (F := F) hx
      refine ⟨F, ?_⟩
      simp [hEqLimit]
    · rintro ⟨F, hF⟩
      rcases Prod.mk.inj hF with ⟨rfl, rfl⟩
      -- Every ultrafilter converges to its compactness limit.
      exact Ultrafilter.le_nhds_lim F
  -- Transfer closedness from the raw convergence relation.
  rw [← hEq]
  exact ultrafilterConvergenceRelation_isClosed (X := X)

/-- Helper for Remark 5.1.5: the compactness-limit map on `Ultrafilter X` is continuous for a
compact weak Hausdorff space `X`. -/
lemma ultrafilterLim_continuous_of_compactWeaklyHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    Continuous (Ultrafilter.lim : Ultrafilter X → X) := by
  -- A closed graph into a compact codomain gives continuity.
  exact
    continuous_of_isClosedGraph_compactCompact (f := Ultrafilter.lim)
      (ultrafilterLim_graph_isClosed (X := X))

/-- Helper for Remark 5.1.5: a compact weak Hausdorff space is Hausdorff. -/
lemma compactWeaklyHausdorff_t2Space
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    T2Space X := by
  -- Route correction: abandon the stalled diagonal descent and instead build a continuous
  -- retraction `Ultrafilter X → X` using the compactness-limit map.
  refine
    t2Space_of_continuousUltrafilterRetraction
      (X := X)
      (e := Ultrafilter.lim)
      (ultrafilterLim_continuous_of_compactWeaklyHausdorff (X := X))
      ?_
  -- Principal ultrafilters are fixed by the compactness-limit retraction.
  funext x
  simpa using ultrafilterLim_pure (X := X) x

/-- Helper for Remark 5.1.5: the diagonal of a compact weak Hausdorff space is closed. -/
lemma isClosed_diagonal_of_compactWeaklyHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    IsClosed (diagonal X) := by
  let _ : T2Space X := compactWeaklyHausdorff_t2Space (X := X)
  -- Once compact weak Hausdorff spaces are Hausdorff, diagonal closedness is the owner API.
  exact isClosed_diagonal

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, the inseparability relation is
closed in `X × X`. -/
lemma isClosed_inseparableRelation_of_compactWeaklyHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    IsClosed ({p : X × X | Inseparable p.1 p.2} : Set (X × X)) := by
  let _ : T2Space X := compactWeaklyHausdorff_t2Space (X := X)
  -- Route correction: once compact weak Hausdorff spaces are known Hausdorff, inseparability is
  -- just equality, so the relation is the diagonal.
  have hEq :
      ({p : X × X | Inseparable p.1 p.2} : Set (X × X)) = diagonal X := by
    ext p
    simp [Set.diagonal, inseparable_iff_eq]
  rw [hEq]
  -- The diagonal is closed in every Hausdorff space.
  exact isClosed_diagonal

/-- Helper for Remark 5.1.5: the separation quotient of a compact weak Hausdorff space is
Hausdorff. -/
lemma separationQuotient_t2Space_of_compactWeaklyHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    T2Space (SeparationQuotient X) := by
  let _ : T2Space X := compactWeaklyHausdorff_t2Space (X := X)
  -- The separation quotient of a Hausdorff space is automatically Hausdorff.
  infer_instance

/-- Helper for Remark 5.1.5: a compact weak Hausdorff space is preregular. -/
lemma compactWeaklyHausdorff_r1Space
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    R1Space X := by
  let _ : T2Space X := compactWeaklyHausdorff_t2Space (X := X)
  -- Every Hausdorff space is preregular.
  infer_instance

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, equality in the Hausdorff quotient
forces inseparability. -/
lemma inseparable_of_t2QuotientEq
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {x y : X} (h : T2Quotient.mk x = T2Quotient.mk y) :
    Inseparable x y := by
  let _ : T2Space X := compactWeaklyHausdorff_t2Space (X := X)
  -- In a Hausdorff space, the universal quotient map is injective.
  have hxy : x = y := eq_of_t2QuotientEq_of_t2 h
  simpa [hxy]

/-- Helper for Remark 5.1.5: in a compact weak Hausdorff space, Stone-Cech equality forces
inseparability. -/
lemma inseparable_of_stoneCechUnit_eq_of_compactWeaklyHausdorff
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {x y : X} (h : stoneCechUnit x = stoneCechUnit y) :
    Inseparable x y := by
  -- Route correction: normalize Stone-Cech equality to the Hausdorff quotient after the main
  -- compact weak Hausdorff -> Hausdorff bridge is established.
  exact inseparable_of_t2QuotientEq (X := X) <|
    t2QuotientEq_of_stoneCechUnitEq (X := X) h

/-- Helper for Remark 5.1.5: Stone-Cech equality forces inseparability once compact weak
Hausdorff spaces have already been upgraded to Hausdorff. -/
lemma stoneCechUnit_eq_imp_inseparable
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {x y : X} (h : stoneCechUnit x = stoneCechUnit y) :
    Inseparable x y := by
  -- Reuse the pointwise compact weak Hausdorff bridge isolated above.
  exact inseparable_of_stoneCechUnit_eq_of_compactWeaklyHausdorff (X := X) h

/-- Helper for Remark 5.1.5: the quotient comparison map into `StoneCech X` is injective for a
compact weak Hausdorff source. -/
lemma separationQuotientToStoneCech_injective
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    Function.Injective (separationQuotientToStoneCech X) := by
  -- Once Stone-Cech equality collapses to inseparability, injectivity is a quotient calculation.
  intro a b hab
  refine Quotient.inductionOn₂' a b (fun x y hxy ↦ ?_) hab
  exact SeparationQuotient.mk_eq_mk.mpr <|
    stoneCechUnit_eq_imp_inseparable (X := X) hxy

/-- Helper for Remark 5.1.5: on a `T1` space, the identity factors continuously through the
separation quotient. -/
lemma continuousSeparationQuotientLiftId_of_t1
    {X : Type u} [TopologicalSpace X] [T1Space X] :
    Continuous
      (SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq) :
        SeparationQuotient X → X) := by
  let _ : T0Space X := inferInstance
  -- In a `T1` space, inseparable points are equal, so the quotient lift of `id` is continuous.
  simpa only using
    (SeparationQuotient.continuous_lift
      (f := fun x : X ↦ x)
      (hf := fun _ _ h ↦ h.eq)).2 continuous_id

/-- Helper for Remark 5.1.5: the factorization of `id_X` through the separation quotient is
surjective. -/
lemma surjectiveSeparationQuotientLiftId_of_t1
    {X : Type u} [TopologicalSpace X] [T1Space X] :
    Function.Surjective
      (SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq) :
        SeparationQuotient X → X) := by
  let _ : T0Space X := inferInstance
  -- Each point is hit by its own separation-quotient class.
  intro x
  refine ⟨SeparationQuotient.mk x, ?_⟩
  simpa only using
    (SeparationQuotient.lift_mk
      (f := fun y : X ↦ y)
      (hf := fun _ _ h ↦ h.eq) x)

/-- Helper for Remark 5.1.5: in a `T1` space, the identity lift is also a right inverse to the
separation-quotient map. -/
lemma separationQuotient_mk_comp_liftId_of_t1
    {X : Type u} [TopologicalSpace X] [T1Space X] :
    SeparationQuotient.mk ∘
        (SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq) :
          SeparationQuotient X → X) =
      id := by
  -- Check the quotient identity on representatives and then descend through quotient induction.
  ext q
  refine Quotient.inductionOn' q fun x ↦ ?_
  -- Rewrite the representative to the public quotient-map spelling before simplifying the lift.
  change
    SeparationQuotient.mk
        ((SeparationQuotient.lift (fun y : X ↦ y) (fun _ _ h ↦ h.eq))
          (SeparationQuotient.mk x)) =
      SeparationQuotient.mk x
  -- On representatives the identity lift evaluates to the original point.
  simpa using
    congrArg SeparationQuotient.mk
      (SeparationQuotient.lift_mk (f := fun y : X ↦ y) (hf := fun _ _ h ↦ h.eq) x)

/-- Helper for Remark 5.1.5: the separation quotient of a weak Hausdorff space is weak Hausdorff.
-/
lemma weaklyHausdorffSpace_separationQuotient
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    WeaklyHausdorffSpace.{u, u} (SeparationQuotient X) := by
  let _ : T1Space X := weaklyHausdorff_t1 X
  let liftId : SeparationQuotient X → X :=
    SeparationQuotient.lift (fun x : X ↦ x) (fun _ _ h ↦ h.eq)
  have hLiftId : Continuous liftId := continuousSeparationQuotientLiftId_of_t1 (X := X)
  have hMkLiftId :
      SeparationQuotient.mk ∘ liftId = id :=
    separationQuotient_mk_comp_liftId_of_t1 (X := X)
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  have hClosedRangeLift :
      IsClosed (Set.range (liftId ∘ g)) :=
    Continuous.isClosed_range (hLiftId.comp hg)
  have hClosedMk : IsClosedMap (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.isClosedMap_mk
  have hRangeEq :
      SeparationQuotient.mk '' Set.range (liftId ∘ g) = Set.range g := by
    -- Apply the quotient map after the lift; the right-inverse identity recovers the original map.
    ext q
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, hx⟩
      exact ⟨k, (congr_fun hMkLiftId (g k)).symm.trans hx⟩
    · rintro ⟨k, rfl⟩
      exact ⟨liftId (g k), ⟨k, rfl⟩, congr_fun hMkLiftId (g k)⟩
  -- Closedness of the lifted range descends through the closed quotient map.
  simpa [hRangeEq] using hClosedMk _ hClosedRangeLift

/-- Helper for Remark 5.1.5: the comparison map from the separation quotient to `StoneCech X` is
surjective when `X` is compact. -/
lemma separationQuotientToStoneCech_surjective
    {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    Function.Surjective (separationQuotientToStoneCech X) := by
  -- Local instance justification (quotient compactness): `SeparationQuotient X` is a quotient of
  -- the ambient compact space `X`, but typeclass search does not unfold that quotient here.
  let _ : CompactSpace (SeparationQuotient X) := by
    change CompactSpace (Quotient (inseparableSetoid X))
    infer_instance
  let hDenseRange : DenseRange (stoneCechUnit : X → StoneCech X) := denseRange_stoneCechUnit
  have hRangeSubset :
      Set.range (stoneCechUnit : X → StoneCech X) ⊆
        Set.range (separationQuotientToStoneCech X) := by
    rintro z ⟨x, rfl⟩
    exact ⟨SeparationQuotient.mk x, separationQuotientToStoneCech_mk (X := X) x⟩
  have hClosedRange :
      IsClosed (Set.range (separationQuotientToStoneCech X)) :=
    (isCompact_range (continuous_separationQuotientToStoneCech (X := X))).isClosed
  have hRangeUniv :
      Set.range (separationQuotientToStoneCech X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ closure (Set.range (stoneCechUnit : X → StoneCech X)) := by
      simpa [hDenseRange.closure_eq] using Set.mem_univ z
    exact closure_minimal hRangeSubset hClosedRange hz
  intro z
  have hz : z ∈ Set.range (separationQuotientToStoneCech X) := by
    simpa [hRangeUniv] using Set.mem_univ z
  exact hz

/-- A compact weak Hausdorff space is Hausdorff. -/
instance CompactSpace.toT2Space_of_weaklyHausdorffSpace
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [WeaklyHausdorffSpace.{u, u} X] :
    T2Space X := by
  -- Route correction: the proof now funnels through the local compact weak Hausdorff -> Hausdorff
  -- bridge, rather than the earlier quotient-shadow route.
  exact compactWeaklyHausdorff_t2Space (X := X)

/-- Remark 5.1.5 (2): If `X` is weak Hausdorff, then for every continuous map `g : K → X` from a
compact space `K`, the image `Set.range g` is Hausdorff as a subspace of `X`. -/
instance range_t2Space_of_weaklyHausdorffSpace
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace.{u, u} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (g : K → X) (hg : Continuous g) : T2Space (Set.range g) := by
  let _ : CompactSpace (Set.range g) := isCompact_iff_compactSpace.mp (isCompact_range hg)
  let _ : WeaklyHausdorffSpace.{u, u} (Set.range g) := inferInstance
  exact CompactSpace.toT2Space_of_weaklyHausdorffSpace (Set.range g)
