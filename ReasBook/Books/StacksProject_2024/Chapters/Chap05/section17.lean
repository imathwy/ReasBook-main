import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Compactness.Compact

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_17_1_Tube_lemma (from Chap05) -/
/-
Domain-style sampling in topology/compactness:
- owner abstraction inspected first: `IsCompact`
- relevant core/product API: `IsCompact.nhdsSet_prod_eq`
- relevant source-facing theorem: `generalized_tube_lemma`
- relevant bridge/view theorem: `generalized_tube_lemma'`

Layer triage:
- `source-facing`: an open neighborhood of `A ×ˢ B` with `A` and `B` quasi-compact contains a
  product neighborhood `U ×ˢ V`
- `core/canonical`: compact subsets together with the neighborhood identity
  `IsCompact.nhdsSet_prod_eq`
- `bridge/view`: the relative `nhdsSetWithin` formulation `generalized_tube_lemma'`

Primitive data are only the compact subsets and the ambient open neighborhood in the product.
The sets `U` and `V` are derived output from the canonical theorem, so this file should recall
that source-facing theorem directly rather than rebuild a parallel local wrapper.
-/

/- Lemma 5.17.1 (Tube lemma): let `A ⊆ X` and `B ⊆ Y` be quasi-compact subsets and let
`A ×ˢ B ⊆ W ⊆ X × Y` with `W` open. Then there exist open neighborhoods `U` of `A` and `V` of
`B` such that `U ×ˢ V ⊆ W`. This is exactly the canonical mathlib theorem
`generalized_tube_lemma`, so the source-facing item should recall that theorem directly rather
than add a parallel local wrapper. -/
recall generalized_tube_lemma

/-! ### Definition_5_17_2 (from Chap05) -/
universe u v

/- Domain-style sampling for proper-map notions:
- sampled owner declarations:
  `IsProperMap`,
  `IsProperMap.universally_closed`,
  `isProperMap_iff_universally_closed`,
  `IsSeparatedMap`;
- `source-facing`: `IsQuasiProperMap`, `IsUniversallyClosedMap`, `IsStacksProperMap`;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: the conversion API between `IsUniversallyClosedMap` and `IsProperMap`.

The Stacks notion of universal closedness is the pullback-projection formulation, but the owner API
for closedness under base change lives on `IsProperMap` through closed product maps. The file
should therefore keep the source-facing pullback predicate while deriving its bridge to
`IsProperMap` from mathlib, rather than re-proving a parallel owner theorem. -/

/- Definition 5.17.2 (1): the Stacks phrase "closed map" is the canonical predicate
`IsClosedMap`. -/
recall IsClosedMap

/- Definition 5.17.2 (2): the Stacks phrase "Bourbaki-proper" is the canonical mathlib notion
`IsProperMap`. -/
recall IsProperMap

/- Companion recall: the separatedness condition in Stacks properness is the canonical predicate
`IsSeparatedMap`. -/
recall IsSeparatedMap

/- Companion recall: Bourbaki properness is characterized in mathlib by closedness of the product
maps `Prod.map f id`. -/
recall isProperMap_iff_universally_closed

section

open Function Pullback Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/-- Definition 5.17.2 (1): a map is quasi-proper if inverse images of quasi-compact subsets are
quasi-compact. In mathlib, quasi-compactness of subsets is expressed by `IsCompact`. -/
def IsQuasiProperMap (f : X → Y) : Prop :=
  Continuous f ∧ ∀ V : Set Y, IsCompact V → IsCompact (f ⁻¹' V)

theorem IsQuasiProperMap.continuous (hf : IsQuasiProperMap f) : Continuous f := hf.1

theorem IsQuasiProperMap.isCompactPreimage (hf : IsQuasiProperMap f)
    {V : Set Y} (hV : IsCompact V) : IsCompact (f ⁻¹' V) :=
  hf.2 V hV

theorem isQuasiProperMap_id : IsQuasiProperMap (id : X → X) :=
  ⟨continuous_id, fun _ hV ↦ by simpa using hV⟩

/-- Definition 5.17.2 (2): a map is universally closed if every pullback projection `X ×_Y Z → Z`
along a continuous map `Z → Y` is a closed map. -/
def IsUniversallyClosedMap (f : X → Y) : Prop :=
  Continuous f ∧ ∀ (Z : Type (max u v)) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (@Function.Pullback.snd X Y Z f g)

private noncomputable def pullbackFstHomeomorph {Z : Type u} [TopologicalSpace Z]
    (hf : Continuous f) : X × Z ≃ₜ f.Pullback (Prod.fst : Y × Z → Y) where
  toEquiv :=
    { toFun := fun xz ↦ ⟨(xz.1, (f xz.1, xz.2)), rfl⟩
      invFun := fun p ↦ (p.1.1, p.1.2.2)
      left_inv := by
        intro xz
        rfl
      right_inv := by
        rintro ⟨⟨x, y, z⟩, hxy⟩
        simp [hxy] }
  continuous_toFun := by
    let h : Continuous (fun xz : X × Z ↦ (xz.1, (f xz.1, xz.2)) : X × Z → X × (Y × Z)) :=
      continuous_fst.prodMk ((hf.comp continuous_fst).prodMk continuous_snd)
    exact h.subtype_mk (fun xz ↦ rfl)
  continuous_invFun := by
    let h₁ : Continuous (fun p : f.Pullback (Prod.fst : Y × Z → Y) ↦ p.1.1) :=
      continuous_fst.comp continuous_subtype_val
    let h₂ : Continuous (fun p : f.Pullback (Prod.fst : Y × Z → Y) ↦ p.1.2.2) :=
      continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
    exact h₁.prodMk h₂

private theorem isClosedMap_prodMap_of_isUniversallyClosedMap
    (hf : IsUniversallyClosedMap f) (Z : Type u) [TopologicalSpace Z] :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) := by
  let e : X × Z ≃ₜ f.Pullback (Prod.fst : Y × Z → Y) := pullbackFstHomeomorph hf.1
  have hsnd : IsClosedMap (@snd X Y (Y × Z) f Prod.fst) :=
    hf.2 (Y × Z) Prod.fst continuous_fst
  simpa [e, pullbackFstHomeomorph, Function.comp_def] using hsnd.comp e.isClosedMap

theorem IsProperMap.isUniversallyClosedMap (hf : IsProperMap f) :
    IsUniversallyClosedMap f :=
  ⟨hf.continuous, fun Z _ g hg ↦ by
    intro s hs
    rcases isClosed_induced_iff.mp hs with ⟨t, ht, rfl⟩
    let k : Z → Y × Z := fun z ↦ (g z, z)
    have hk : Continuous k := hg.prodMk continuous_id
    have hclosed : IsClosed ((Prod.map f (id : Z → Z)) '' t) :=
      (hf.universally_closed Z) t ht
    have hsnd : snd '' (Subtype.val ⁻¹' t : Set (f.Pullback g)) =
        k ⁻¹' ((Prod.map f (id : Z → Z)) '' t) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(p.fst, p.snd), hp, Prod.ext p.2 rfl⟩
      · rintro ⟨xz, hxt, hxz⟩
        have hx₁ : f xz.1 = g z := congrArg Prod.fst hxz
        have hx₂ : xz.2 = z := congrArg Prod.snd hxz
        let p : f.Pullback g := ⟨xz, by simpa [hx₂] using hx₁⟩
        refine ⟨p, hxt, ?_⟩
        simpa [p] using hx₂
    rw [hsnd]
    exact hclosed.preimage hk⟩

theorem IsUniversallyClosedMap.continuous (hf : IsUniversallyClosedMap f) :
  Continuous f :=
  hf.1

theorem IsUniversallyClosedMap.isClosedMap_snd (hf : IsUniversallyClosedMap f)
    {Z : Type (max u v)} [TopologicalSpace Z] (g : Z → Y) (hg : Continuous g) :
    IsClosedMap (@snd X Y Z f g) :=
  hf.2 Z g hg

theorem IsUniversallyClosedMap.isClosedMap_prodMap (hf : IsUniversallyClosedMap f)
    (Z : Type u) [TopologicalSpace Z] :
    IsClosedMap (Prod.map f (id : Z → Z) : X × Z → Y × Z) :=
  isClosedMap_prodMap_of_isUniversallyClosedMap hf Z

theorem IsUniversallyClosedMap.isProperMap (hf : IsUniversallyClosedMap f) :
    IsProperMap f := by
  rw [isProperMap_iff_universally_closed]
  exact ⟨hf.continuous, fun Z ↦ hf.isClosedMap_prodMap Z⟩

theorem isProperMap_iff_isUniversallyClosedMap :
    IsProperMap f ↔ IsUniversallyClosedMap f :=
  ⟨IsProperMap.isUniversallyClosedMap, IsUniversallyClosedMap.isProperMap⟩

theorem isUniversallyClosedMap_id : IsUniversallyClosedMap (id : X → X) :=
  isProperMap_id.isUniversallyClosedMap

/-- Definition 5.17.2 (3): a map is proper in the Stacks sense if it is separated and universally
closed. -/
def IsStacksProperMap (f : X → Y) : Prop :=
  IsSeparatedMap f ∧ IsUniversallyClosedMap f

theorem IsStacksProperMap.separated (hf : IsStacksProperMap f) : IsSeparatedMap f :=
  hf.1

theorem IsStacksProperMap.proper (hf : IsStacksProperMap f) : IsProperMap f :=
  hf.2.isProperMap

theorem IsStacksProperMap.universallyClosed (hf : IsStacksProperMap f) :
    IsUniversallyClosedMap f :=
  hf.2

theorem isStacksProperMap_id : IsStacksProperMap (id : X → X) :=
  ⟨Function.Injective.isSeparatedMap fun _ _ h ↦ h, isUniversallyClosedMap_id⟩

end

/-! ### Lemma_5_17_3 (from Chap05) -/
universe u v

open Homeomorph

/- Domain-style sampling for compactness via closed product projections:
- sampled owner declarations in this domain:
  `CompactSpace`,
  `isClosedMap_fst_of_compactSpace`,
  `IsProperMap.universally_closed`,
  `isProperMap_const_iff`
- owner abstraction: `CompactSpace`, with `IsProperMap` as the canonical bridge from compactness to
  closedness of product projections

Layer triage:
- `source-facing`: `compactSpace_iff_forall_isClosedMap_fst`
- `core/canonical`: compactness and properness
- `bridge/view`: closedness of `Prod.fst`

Primitive data is just compactness of `X`. Closedness of the projections and properness of the
constant map are derived API, so this file should keep the source-facing criterion and reuse the
canonical owner theorems instead of introducing any parallel wrapper notion.
-/

/-- Lemma 5.17.3: a topological space `X` is quasi-compact if and only if for every
topological space `Z`, the projection `Z × X → Z` is a closed map. -/
theorem compactSpace_iff_forall_isClosedMap_fst
    (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔ ∀ (Z : Type (max u v)) [TopologicalSpace Z],
      IsClosedMap (Prod.fst : Z × X → Z) := by
  constructor
  · intro hX Z _
    letI := hX
    simpa using
      (isClosedMap_fst_of_compactSpace : IsClosedMap (Prod.fst : Z × X → Z))
  · intro h
    have hsame : ∀ (Z : Type u) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z) := by
      intro Z _
      let e : Z × X ≃ₜ ULift.{v, u} Z × X :=
        ulift.symm.prodCongr (Homeomorph.refl X)
      have hpre :
          IsClosedMap ((Prod.fst : ULift.{v, u} Z × X → ULift.{v, u} Z) ∘ e) :=
        (h (ULift.{v, u} Z)).comp e.isClosedMap
      simpa [e, Function.comp] using ulift.isClosedMap.comp hpre
    have hproper : IsProperMap (fun _ : X ↦ (PUnit.unit : PUnit.{u + 1})) := by
      refine (isProperMap_iff_universally_closed).2 ?_
      refine ⟨continuous_const, fun Z _ ↦ by
        have hsnd : IsClosedMap (Prod.snd : X × Z → Z) := by
          simpa [Function.comp] using
            (hsame Z).comp (prodComm X Z).isClosedMap
        simpa [Function.comp] using
          (punitProd Z).symm.isClosedMap.comp hsnd⟩
    simpa using (isProperMap_const_iff (PUnit.unit : PUnit.{u + 1})).mp hproper

/-! ### Remark_5_17_4 (from Chap05) -/
/- Domain-style sampling for compactness via closed product projections:
- owner predicates in this domain: `IsClosedMap`, `IsProperMap`
- relevant mathlib bridge theorems:
  `isClosedMap_fst_of_compactSpace`,
  `isProperMap_const_iff`,
  `isProperMap_iff_universally_closed`
- source-facing chapter theorem: `compactSpace_iff_forall_isClosedMap_fst`

Layer triage:
- `source-facing`: `compactSpace_iff_forall_isClosedMap_fst`
- `core/canonical`: proper maps and their universally-closed product characterization
- `bridge/view`: the compactness criterion phrased through closedness of `Prod.fst`

Primitive data belongs to the owner layer: compactness, properness, and closedness of the product
projection. The Stacks remark itself is only bibliographic, pointing to Bourbaki as the proof
source for the already-formalized criterion. So this file should stay a direct recall of the
chapter theorem rather than introduce any parallel wrapper or proof-packaging declaration.
-/

/- Remark 5.17.4 is bibliographic: it says that the proof of Lemma 5.17.3 is a combination of
[Bou71, I, p. 75, Lemme 1] and [Bou71, I, p. 76, Corollaire 1]. The formal mathematical content
of the surrounding discussion is already the source-facing theorem
`compactSpace_iff_forall_isClosedMap_fst`. -/
recall compactSpace_iff_forall_isClosedMap_fst

/-! ### Theorem_5_17_5 (from Chap05) -/
universe u v

/- Domain-style sampling for characterizations of proper maps:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_universally_closed`,
  and the chapter bridge `isProperMap_iff_isUniversallyClosedMap`;
- source-facing: `IsQuasiProperMap`;
- core/canonical: `IsProperMap`;
- bridge/view: `IsUniversallyClosedMap`. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- The source-facing condition that a map is both quasi-proper and closed. -/
def IsQuasiProperClosedMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

/-- The source-facing condition that a map is closed and has compact fibers. -/
def IsClosedMapWithCompactFibers (f : X → Y) : Prop :=
  IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y})

/-- Helper for Theorem 5.17.5: a proper map is quasi-proper because proper maps send compact
subsets of the target to compact inverse images. -/
theorem IsProperMap.isQuasiProperMap (hproper : IsProperMap f) : IsQuasiProperMap f := by
  -- Proper maps are continuous and preserve compactness under inverse image.
  refine ⟨hproper.continuous, ?_⟩
  intro V hV
  exact hproper.isCompact_preimage hV

/-- Bourbaki properness is equivalent to being both quasi-proper and closed. -/
-- Proof sketch: use `isProperMap_iff_isClosedMap_and_compact_fibers`; compact fibers come from
-- quasi-properness on singletons, and quasi-properness follows from properness by compact
-- preimages.
theorem isQuasiProperClosedMap_iff_isProperMap (hf : Continuous f) :
    IsQuasiProperClosedMap f ↔ IsProperMap f := by
  constructor
  · intro hsource
    rcases hsource with ⟨hquasi, hclosed⟩
    -- Route correction: identify the source-facing condition with the owner theorem
    -- `isProperMap_iff_isClosedMap_and_compact_fibers` instead of replaying the base-change proof.
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hf, hclosed, ?_⟩
    -- Quasi-properness supplies compactness of each singleton fiber.
    intro y
    simpa using hquasi.isCompactPreimage isCompact_singleton
  · intro hproper
    -- The reverse implication is the structural bridge from properness to quasi-properness,
    -- together with the standard closedness of proper maps.
    exact ⟨hproper.isQuasiProperMap, hproper.isClosedMap⟩

/-- Helper for Theorem 5.17.5: the source condition "closed with compact fibers" is exactly the
owner-level properness criterion. -/
theorem isClosedMapWithCompactFibers_iff_isProperMap (hf : Continuous f) :
    IsClosedMapWithCompactFibers f ↔ IsProperMap f := by
  constructor
  · intro hsource
    rcases hsource with ⟨hclosed, hcompact⟩
    -- This is exactly the backward direction of the standard proper-map characterization.
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    exact ⟨hf, hclosed, hcompact⟩
  · intro hproper
    -- Properness gives both closedness and compact singleton fibers.
    exact ⟨hproper.isClosedMap, fun y ↦ hproper.isCompact_preimage isCompact_singleton⟩

/-- Theorem 5.17.5: for a continuous map of topological spaces, the Stacks conditions
"quasi-proper and closed", "Bourbaki-proper", "universally closed", and "closed with
quasi-compact fibers" are equivalent. Here Bourbaki-proper is expressed by mathlib's
`IsProperMap`, Stacks universal closedness by the chapter's bridge predicate
`IsUniversallyClosedMap`, and quasi-compactness by `IsCompact`. -/
-- Proof sketch: combine the equivalence between quasi-proper closed maps and `IsProperMap`,
-- the chapter bridge `isProperMap_iff_isUniversallyClosedMap`, and the standard compact-fiber
-- characterization of proper maps.
theorem proper_map_characterization_tfae (hf : Continuous f) :
    List.TFAE
      [ IsQuasiProperClosedMap f,
        IsProperMap f,
        IsUniversallyClosedMap f,
        IsClosedMapWithCompactFibers f ] := by
  -- Package the four source clauses by using `IsProperMap f` as the central owner notion.
  tfae_have 1 ↔ 2 := isQuasiProperClosedMap_iff_isProperMap hf
  tfae_have 2 ↔ 3 := isProperMap_iff_isUniversallyClosedMap
  tfae_have 2 ↔ 4 := (isClosedMapWithCompactFibers_iff_isProperMap hf).symm
  tfae_finish

end

/-! ### Remark_5_17_6 (from Chap05) -/
universe u v

/- Domain-style sampling for proper-map characterizations:
- sampled owner declarations:
  `IsProperMap`,
  `isProperMap_iff_isClosedMap_and_compact_fibers`,
  `isProperMap_iff_isUniversallyClosedMap`,
  `proper_map_characterization_tfae`;
- `source-facing`: the three-clause equivalence from Remark 5.17.6;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: `IsUniversallyClosedMap`.

Primitive data belongs to the owner layer: continuity, closedness, and compact fibers. The target
remark only extracts the clauses `(1)`, `(2)`, and `(4)` from the chapter's four-way
characterization, so the file should keep only that source-facing projection and reuse the chapter
owner theorem directly rather than rebuilding any of its component equivalences locally. -/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- A map is quasi-proper, moreover closed. -/
def IsClosedQuasiProperMap (f : X → Y) : Prop :=
  IsQuasiProperMap f ∧ IsClosedMap f

-- Proof sketch: specialize Theorem `5.17.5` to clauses `(1)`, `(2)`, `(4)`, then rewrite the
-- first plus third clauses using the two semantic helper predicates above.
/-- Remark 5.17.6: for a continuous map, the quasi-proper closed condition, Bourbaki properness,
together with the closed compact-fiber condition from Theorem 5.17.5, are equivalent. -/
theorem proper_map_characterization_124_tfae (hf : Continuous f) :
    List.TFAE
      [ IsClosedQuasiProperMap f,
        IsProperMap f,
        IsClosedMapWithCompactFibers f ] := by
  -- Use `IsProperMap f` as the owner clause and import the two pairwise bridges from
  -- Theorem 5.17.5 instead of rebuilding the characterization locally.
  tfae_have 1 ↔ 2 := by
    -- The local clause `(1)` is definitionally the same as the source-facing clause `(1)`
    -- from Theorem 5.17.5.
    simpa [IsClosedQuasiProperMap, IsQuasiProperClosedMap] using
      (isQuasiProperClosedMap_iff_isProperMap (f := f) hf)
  tfae_have 2 ↔ 3 := by
    -- The local clause `(3)` is exactly the compact-fiber clause already related to
    -- properness in Theorem 5.17.5.
    simpa using (isClosedMapWithCompactFibers_iff_isProperMap (f := f) hf).symm
  tfae_finish

end

/-! ### Lemma_5_17_7 (from Chap05) -/
universe u v

/- Domain-style sampling for proper maps:
- sampled owner declarations:
  `IsProperMap`,
  `Continuous.isProperMap`,
  `IsProperMap.isUniversallyClosedMap`;
- `source-facing`: the conclusion `IsUniversallyClosedMap`;
- `core/canonical`: `IsProperMap`;
- `bridge/view`: `IsProperMap.isUniversallyClosedMap`.

Primitive data is only the continuous map `f` together with compactness of the source and
Hausdorffness of the target, which feed the canonical owner theorem `Continuous.isProperMap`.
Universal closedness here is derived bridge API, so this file should reuse that owner theorem
directly rather than importing the broader chapter characterization theorem.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

-- Proof sketch: `Continuous.isProperMap` gives the canonical owner theorem, and
-- `IsProperMap.isUniversallyClosedMap` is the chapter bridge to universal closedness.
/-- Lemma 5.17.7: a continuous map from a quasi-compact space to a Hausdorff space is universally
closed. In this chapter this is expressed by the bridge predicate `IsUniversallyClosedMap`. -/
theorem Continuous.isUniversallyClosed [CompactSpace X] [T2Space Y] (hf : Continuous f) :
    IsUniversallyClosedMap f := by
  -- First package the compact-source and Hausdorff-target hypotheses as properness.
  have hproper : IsProperMap f := hf.isProperMap
  -- Then pass from properness to universal closedness via the chapter bridge theorem.
  exact hproper.isUniversallyClosedMap

end

/-! ### Lemma_5_17_8 (from Chap05) -/
universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for compact-to-Hausdorff homeomorphism criteria:
- owner abstraction: `isHomeomorph_iff_continuous_bijective`
- same-domain declarations inspected:
  `isHomeomorph_iff_isEmbedding_surjective`,
  `isHomeomorph_iff_continuous_isClosedMap_bijective`,
  `isHomeomorph_iff_continuous_bijective`,
  `Lemma_5_26_4.isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed`

Layer triage:
- `source-facing`: the Stacks criterion that a continuous bijection from a quasi-compact space to a
  Hausdorff space is a homeomorphism
- `core/canonical`: mathlib's owner theorem `isHomeomorph_iff_continuous_bijective`
- `bridge/view`: downstream arguments that supply bijectivity or closed-map data and then invoke
  the owner theorem

Primitive data is exactly continuity and bijectivity, with compactness of the source and
Hausdorffness of the target carried canonically by `[CompactSpace X]` and `[T2Space Y]`. The
closed-map package is derived by the owner theorem, so this file should keep the source-facing
forward implication as its public item and use the stronger canonical `↔` theorem only as
justification or companion recall.
-/

/-- Helper for Lemma 5.17.8: a continuous map from a compact space to a Hausdorff space is a
closed map. -/
lemma continuous_isClosedMap_of_compact_t2 [CompactSpace X] [T2Space Y] (hf : Continuous f) :
    IsClosedMap f := by
  intro s hs
  -- Closed subsets of a compact space remain compact.
  have hs_compact : IsCompact s := hs.isCompact
  -- Continuous images of compact sets are compact.
  have himage_compact : IsCompact (f '' s) := hs_compact.image hf
  -- Compact subsets of a Hausdorff space are closed.
  exact himage_compact.isClosed

/-- Lemma 5.17.8: if `f : X → Y` is continuous and bijective, `X` is quasi-compact, and `Y` is
Hausdorff, then `f` is a homeomorphism. -/
theorem isHomeomorph_of_continuous_bijective [CompactSpace X] [T2Space Y]
    (hf : Continuous f) (hbij : Function.Bijective f) :
    IsHomeomorph f := by
  -- Follow the source proof: first show that `f` is a closed map.
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  -- The canonical criterion now reduces the claim to continuity, closedness, and bijectivity.
  exact ⟨hf, continuous_isClosedMap_of_compact_t2 (f := f) hf, hbij⟩

/- Companion recall: the stronger canonical compact-to-Hausdorff criterion packages this lemma as
an `iff`, with the reverse implication supplied by every homeomorphism. -/
recall isHomeomorph_iff_continuous_bijective

end
