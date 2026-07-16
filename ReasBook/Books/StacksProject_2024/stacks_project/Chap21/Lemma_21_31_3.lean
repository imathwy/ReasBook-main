import StacksProject_2024.stacks_project.Chap07.Definition_7_12_1
import StacksProject_2024.stacks_project.Chap21.Definition_21_31_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_31_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open Topology

/-
Domain-style sampling for Lemma 21.31.3:
- primary domain: qc-covering families in `LC`, together with their stability under isomorphism,
  refinement, and pullback;
- inspected declarations:
  `SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `SemiRepresentableFamily.Over.IsQcCoveringOne.exists_finite_compact_image_neighborhood`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `SemiRepresentableFamily.Over.baseChange`,
  `SemiRepresentableFamily.Over.baseChange_eq_map_pullback`,
  `compactSpace_pullback`,
  `isCompact_univ_pullback_of_compact`;
- best owner abstraction: the source-facing owner is the predicate
  `SemiRepresentableFamily.Over.IsQcCoveringOne`; the present file should contribute only closure
  lemmas for that owner rather than parallel wrapper APIs;
- primitive vs derived:
  primitive data are only the fixed-target owner object `𝒰 : SemiRepresentableFamily.Over X`
  together with the finite compact-image neighborhood condition from `IsQcCoveringOne`;
  the indexed-arrow presentation `ofArrows X_ f` is only a bridge/view of that owner;
  isomorphism, composition, and base change are derived closure properties, not new packaged data.

Source/core/bridge triage:
- `source-facing`: qc coverings in `LC` and their stability properties from the Stacks text;
- `core/canonical`: the owner predicate `SemiRepresentableFamily.Over.IsQcCoveringOne` together
  with the owner-level family pullback `SemiRepresentableFamily.Over.baseChange`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows` for the indexed-arrow presentation, while
  the pullback object and its compactness API stay internal to the proof route for base change. -/

section

variable {I : Type v} {J : I → Type w}
variable {X X' : LCCat.{u}} {X_ : I → LCCat.{u}}
variable {f : ∀ i, X_ i ⟶ X}
variable {𝒰 : SemiRepresentableFamily.Over X}

namespace CategoryTheory.SemiRepresentableFamily.Over.IsQcCoveringOne

-- Proof sketch: an isomorphism is a homeomorphism on the underlying spaces, so every point of `X`
-- has a neighborhood equal to the image of the singleton finite family indexed by `PUnit`; take the
-- whole source space, which is quasi-compact in a neighborhood of every point because `X'` lies in
-- `LC`.
/-- Lemma 21.31.3 (1): a singleton family consisting of an isomorphism in `LC` is a qc covering. -/
@[stacks 09X1]
theorem singleton_of_isIso (f : X' ⟶ X) [IsIso f] :
    (ofArrows (fun _ : PUnit ↦ X') (fun _ : PUnit ↦ f)).IsQcCoveringOne := by
  classical
  rw [ofArrows_isQcCoveringOne_iff]
  intro x
  let e : X'.obj ≃ₜ X.obj :=
    TopCat.homeoOfIso (HausdorffLocallyCompactObject.ι.mapIso (asIso f))
  -- Choose a compact neighborhood of `x` and pull it back along the homeomorphism.
  obtain ⟨K, hKbasis, _⟩ :=
    (compact_basis_nhds x).mem_iff.mp (by exact Filter.univ_mem)
  rcases hKbasis with ⟨hKnhds, hKcompact⟩
  refine ⟨{PUnit.unit}, fun _ ↦ e ⁻¹' K, ?_, ?_⟩
  · intro i
    simpa using (Homeomorph.isCompact_preimage e).2 hKcompact
  · have hf_eq : (ConcreteCategory.hom f : X'.obj → X.obj) = e := rfl
    have hunion :
        (⋃ i : ({PUnit.unit} : Finset PUnit), (ConcreteCategory.hom f) '' (e ⁻¹' K)) = K := by
          ext y
          constructor
          · intro hy
            rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
            rcases hi with ⟨z, hz, rfl⟩
            simpa [hf_eq] using hz
          · intro hy
            refine Set.mem_iUnion.mpr ⟨⟨PUnit.unit, by simp⟩, ?_⟩
            refine ⟨e.symm y, ?_, ?_⟩
            · simpa using hy
            · simpa [hf_eq] using e.apply_symm_apply y
    rw [hunion]
    exact hKnhds

/-- Helper for Lemma 21.31.3: a qc covering refines any compact subset of the target by finitely
many compact image pieces. -/
private lemma exists_finite_compact_image_cover_of_isCompact_subset
    {K : Type w} {Y : LCCat.{u}} {Y_ : K → LCCat.{u}} (g : ∀ k, Y_ k ⟶ Y)
    (hg : (ofArrows Y_ g).IsQcCoveringOne) {E : Set Y.obj} (hE : IsCompact E) :
    ∃ t : Finset K, ∃ F : ∀ j : t, Set ((Y_ j.1).obj),
      (∀ j : t, IsCompact (F j)) ∧ E ⊆ ⋃ j : t, g j.1 '' F j := by
  classical
  -- Around each point of the compact set, choose one qc-neighborhood witness.
  have hpoint :
      ∀ e : E, ∃ s : Finset K, ∃ F : ∀ j : s, Set ((Y_ j.1).obj),
        (∀ j : s, IsCompact (F j)) ∧ (⋃ j : s, g j.1 '' F j) ∈ 𝓝 e.1 := by
    intro e
    exact exists_finite_compact_image_neighborhood hg e.1
  choose T U hUcompact hUnhds using hpoint
  -- Replace neighborhood-filter membership by an open set contained in the chosen finite image
  -- union, so compactness can reduce the cover to finitely many points of `E`.
  have hopenPoint :
      ∀ e : E, ∃ V : Set Y.obj, V ⊆ ⋃ j : T e, g j.1 '' U e j ∧ IsOpen V ∧ e.1 ∈ V := by
    intro e
    rcases mem_nhds_iff.mp (hUnhds e) with ⟨V, hVsubset, hVopen, heV⟩
    exact ⟨V, hVsubset, hVopen, heV⟩
  choose V hVsubset hVopen heV using hopenPoint
  have hcover : E ⊆ ⋃ e : E, V e := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, heV ⟨x, hx⟩⟩
  -- Compactness of `E` gives a finite set of witness points.
  obtain ⟨a, ha⟩ := hE.elim_finite_subcover V hVopen hcover
  let t : Finset K := a.biUnion T
  let W : ∀ j : t, E → Set ((Y_ j.1).obj) := fun j e ↦
    if h : j.1 ∈ T e then U e ⟨j.1, h⟩ else ∅
  let F : ∀ j : t, Set ((Y_ j.1).obj) := fun j ↦ ⋃ e ∈ (a : Set E), W j e
  refine ⟨t, F, ?_, ?_⟩
  · intro j
    -- Each `F j` is a finite union of compact sets indexed by the finite chosen subcover.
    have hcompact :
        IsCompact (⋃ e ∈ (a : Set E), W j e) :=
      (Finset.finite_toSet a).isCompact_biUnion fun e he ↦ by
        by_cases hje : j.1 ∈ T e
        · simpa [W, hje] using hUcompact e ⟨j.1, hje⟩
        · simpa [W, hje]
    simpa [F] using hcompact
  · intro x hx
    have hxV : x ∈ ⋃ e ∈ (a : Set E), V e := ha hx
    rcases Set.mem_iUnion₂.mp hxV with ⟨e, he, hxVe⟩
    have hxU : x ∈ ⋃ j : T e, g j.1 '' U e j := hVsubset e hxVe
    rcases Set.mem_iUnion.mp hxU with ⟨j, hxUj⟩
    rcases hxUj with ⟨y, hy, rfl⟩
    let j' : t := ⟨j.1, Finset.mem_biUnion.mpr ⟨e, he, j.2⟩⟩
    have hyW : y ∈ W j' e := by
      have hje : j'.1 ∈ T e := by
        simpa [j'] using j.2
      simpa [W, j', hje] using hy
    have hyF : y ∈ F j' := by
      exact Set.mem_iUnion₂.mpr ⟨e, he, hyW⟩
    refine Set.mem_iUnion.mpr ⟨j', ?_⟩
    exact ⟨y, hyF, rfl⟩

-- Proof sketch: for a point of `X`, start with finitely many compact subsets witnessing that
-- `fᵢ : Xᵢ ⟶ X` is a qc covering near that point. Then refine each compact subset using the qc
-- covering on `Xᵢ`, extract finite subcovers by compactness, and compose the corresponding maps.
/-- Lemma 21.31.3 (2): a family obtained by refining each member of a qc covering by another qc
covering is again a qc covering. -/
@[stacks 09X1]
theorem comp
    {X__ : ∀ i, J i → LCCat.{u}} (g : ∀ i j, X__ i j ⟶ X_ i)
    (hf : (ofArrows X_ f).IsQcCoveringOne)
    (hg : ∀ i, (ofArrows (X__ i) (g i)).IsQcCoveringOne) :
    (ofArrows
      (fun ij : Sigma J ↦ X__ ij.1 ij.2)
      (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1)).IsQcCoveringOne := by
  classical
  rw [ofArrows_isQcCoveringOne_iff] at hf ⊢
  intro x
  -- Start with the finite compact-image neighborhood on `X`.
  obtain ⟨s, E, hEcompact, hEnhds⟩ := hf x
  -- Refine each compact source piece by the qc covering on that source.
  have hrefine :
      ∀ i : s, ∃ t : Finset (J i.1), ∃ F : ∀ j : t, Set ((X__ i.1 j.1).obj),
        (∀ j : t, IsCompact (F j)) ∧ E i ⊆ ⋃ j : t, g i.1 j.1 '' F j := by
    intro i
    exact exists_finite_compact_image_cover_of_isCompact_subset
      (g i.1) (hg i.1) (hEcompact i)
  choose T₀ F₀ hFcompact hFcover using hrefine
  let T : ∀ i : I, Finset (J i) := fun i ↦
    if hi : i ∈ s then T₀ ⟨i, hi⟩ else ∅
  let G : ∀ ij : s.sigma T, Set ((X__ ij.1.1 ij.1.2).obj) := fun ij ↦
    if hi : ij.1.1 ∈ s then
      F₀ ⟨ij.1.1, hi⟩
        ⟨ij.1.2, by
          simpa [T, hi] using (Finset.mem_sigma.mp ij.2).2⟩
    else ∅
  refine ⟨s.sigma T, G, ?_, ?_⟩
  · intro ij
    -- Each flattened component inherits compactness from the corresponding refined witness.
    by_cases hi : ij.1.1 ∈ s
    · simpa [G, hi, T] using
        hFcompact ⟨ij.1.1, hi⟩
          ⟨ij.1.2, by simpa [T, hi] using (Finset.mem_sigma.mp ij.2).2⟩
    · have : False := by
        exact hi (Finset.mem_sigma.mp ij.2).1
      exact False.elim this
  · -- The original neighborhood union is contained in the flattened composed-image union.
    refine Filter.mem_of_superset hEnhds ?_
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    rcases hyi with ⟨z, hzE, rfl⟩
    have hzCover : z ∈ ⋃ j : T₀ i, g i.1 j.1 '' F₀ i j := hFcover i hzE
    rcases Set.mem_iUnion.mp hzCover with ⟨j, hzj⟩
    rcases hzj with ⟨w, hw, rfl⟩
    let ij : s.sigma T := ⟨⟨i.1, j.1⟩, by
      exact Finset.mem_sigma.mpr ⟨i.2, by simpa [T, i.2] using j.2⟩⟩
    have hwG : w ∈ G ij := by
      have hi : ij.1.1 ∈ s := by
        simpa [ij] using i.2
      simpa [G, ij, hi, T, i.2] using hw
    refine Set.mem_iUnion.mpr ⟨ij, ?_⟩
    exact ⟨w, hwG, rfl⟩

/-- Helper for Lemma 21.31.3: a compact subspace of an `LC` object is again an object of `LC`. -/
private lemma compact_subset_is_hausdorff_locally_compact
    {Y : LCCat.{u}} {S : Set Y.obj} (hS : IsCompact S) :
    HausdorffLocallyCompactObject (TopCat.of S) := by
  haveI : T2Space S := inferInstance
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  haveI : LocallyCompactSpace S := inferInstance
  -- A compact Hausdorff subspace is locally compact, so it defines another `LC` object.
  change T2Space S ∧ LocallyCompactSpace S
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 21.31.3: the subtype inclusion is a canonical morphism in `TopCat`. -/
private def subtype_val_hom {Y : LCCat.{u}} (S : Set Y.obj) : TopCat.of S ⟶ Y.obj :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Lemma 21.31.3: compatible points in two `LC` objects lift to a point of their
categorical pullback. -/
private lemma exists_pullback_point_of_eq
    {A B X : LCCat.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (y : A.obj) (z : B.obj) (h : a y = b z) :
    ∃ p : (Limits.pullback a b).obj, Limits.pullback.fst a b p = y ∧
      Limits.pullback.snd a b p = z := by
  let T : LCCat.{u} := ⟨TopCat.of PUnit.{u + 1}, ⟨inferInstance, inferInstance⟩⟩
  let yMap : T ⟶ A := ObjectProperty.homMk <| TopCat.ofHom ⟨fun _ ↦ y, continuous_const⟩
  let zMap : T ⟶ B := ObjectProperty.homMk <| TopCat.ofHom ⟨fun _ ↦ z, continuous_const⟩
  have hcomm : yMap ≫ a = zMap ≫ b := by
    -- Both constant maps become equal after composing to `X` because they hit the same point.
    apply ObjectProperty.hom_ext
    ext t
    cases t
    simpa [yMap, zMap] using h
  let q : T ⟶ Limits.pullback a b := Limits.pullback.lift yMap zMap hcomm
  refine ⟨q PUnit.unit, ?_, ?_⟩
  · -- The first projection of the lifted pullback point is the chosen point `y`.
    have hfst := ConcreteCategory.congr_hom (Limits.pullback.lift_fst yMap zMap hcomm) PUnit.unit
    simpa [q, yMap] using hfst
  · -- The second projection of the lifted pullback point is the chosen point `z`.
    have hsnd := ConcreteCategory.congr_hom (Limits.pullback.lift_snd yMap zMap hcomm) PUnit.unit
    simpa [q, zMap] using hsnd

/-- Helper for Lemma 21.31.3: compact sets in the source and in the base-change target determine a
compact subset of the pullback whose second projection covers the expected pullback rectangle. -/
private lemma exists_compact_pullback_cover_of_compact_images
    (φ : X' ⟶ X) (i : 𝒰.index) {E : Set ((𝒰.obj i).left.obj)} (hE : IsCompact E)
    {F : Set X'.obj} (hF : IsCompact F) :
    ∃ P : Set (Limits.pullback (𝒰.obj i).hom φ).obj, IsCompact P ∧
      F ∩ φ ⁻¹' ((𝒰.obj i).hom '' E) ⊆ Limits.pullback.snd (𝒰.obj i).hom φ '' P := by
  letI : CompactSpace E := isCompact_iff_compactSpace.mp hE
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let EObj : LCCat.{u} := ⟨TopCat.of E, compact_subset_is_hausdorff_locally_compact hE⟩
  let FObj : LCCat.{u} := ⟨TopCat.of F, compact_subset_is_hausdorff_locally_compact hF⟩
  let eInc : EObj ⟶ (𝒰.obj i).left := ObjectProperty.homMk (subtype_val_hom E)
  let fInc : FObj ⟶ X' := ObjectProperty.homMk (subtype_val_hom F)
  let eMap : EObj ⟶ X := eInc ≫ (𝒰.obj i).hom
  let fMap : FObj ⟶ X := fInc ≫ φ
  let toAmbient : Limits.pullback eMap fMap ⟶ Limits.pullback (𝒰.obj i).hom φ :=
    Limits.pullback.map eMap fMap (𝒰.obj i).hom φ eInc fInc (𝟙 X)
      (by simp [eMap])
      (by simp [fMap])
  let P : Set (Limits.pullback (𝒰.obj i).hom φ).obj := toAmbient '' Set.univ
  refine ⟨P, ?_, ?_⟩
  · -- The compact pullback of the compact source pieces stays compact, and its image is compact.
    have hCompactImage :
        IsCompact (toAmbient '' (Set.univ : Set (Limits.pullback eMap fMap).obj)) :=
      isCompact_univ.image (ConcreteCategory.hom toAmbient).continuous
    simpa [P] using hCompactImage
  · intro x hx
    rcases hx with ⟨hxF, hxImage⟩
    rcases hxImage with ⟨y, hyE, hyEq⟩
    have hcompat : eMap ⟨y, hyE⟩ = fMap ⟨x, hxF⟩ := by
      -- The chosen points in the compact source pieces map to the same point of `X`.
      simpa [eMap, fMap, eInc, fInc, subtype_val_hom] using hyEq
    obtain ⟨p, hpfst, hpsnd⟩ :=
      exists_pullback_point_of_eq eMap fMap ⟨y, hyE⟩ ⟨x, hxF⟩ hcompat
    refine ⟨toAmbient p, ?_, ?_⟩
    · exact Set.mem_image_of_mem toAmbient (Set.mem_univ p)
    · -- The second projection of the ambient image is the original point `x`.
      have hmapComm :
          Limits.pullback.fst eMap fMap ≫ eInc ≫ (𝒰.obj i).hom =
            Limits.pullback.snd eMap fMap ≫ fInc ≫ φ := by
        simpa [Category.assoc, eMap, fMap] using
          (Limits.pullback.condition :
            Limits.pullback.fst eMap fMap ≫ eMap = Limits.pullback.snd eMap fMap ≫ fMap)
      calc
        Limits.pullback.snd (𝒰.obj i).hom φ (toAmbient p)
            = fInc (Limits.pullback.snd eMap fMap p) := by
                simpa [toAmbient] using
                  ConcreteCategory.congr_hom
                    (Limits.pullback.lift_snd
                      (Limits.pullback.fst eMap fMap ≫ eInc)
                      (Limits.pullback.snd eMap fMap ≫ fInc)
                      hmapComm)
                    p
        _ = fInc ⟨x, hxF⟩ := by rw [hpsnd]
        _ = x := rfl

-- Proof sketch: let `x' ∈ X'` map to `x ∈ X`. Choose finitely many compact subsets upstairs over
-- `X` witnessing the qc covering near `x`, then intersect them with a compact neighborhood of `x'`
-- after base change. The pullbacks of compact subsets remain compact by Lemma `21.31.1`, and their
-- images cover a neighborhood of `x'`.
/-- Lemma 21.31.3 (3): qc coverings in `LC` are stable under base change. -/
@[stacks 09X1]
theorem baseChange (h𝒰 : 𝒰.IsQcCoveringOne) (φ : X' ⟶ X) :
    (baseChange 𝒰 φ).IsQcCoveringOne := by
  classical
  intro x'
  change ∃ s : Finset 𝒰.index, ∃ E' : ∀ i : s, Set (Limits.pullback (𝒰.obj i.1).hom φ).obj,
    (∀ i : s, IsCompact (E' i)) ∧
      (⋃ i : s, Limits.pullback.snd (𝒰.obj i.1).hom φ '' E' i) ∈ 𝓝 x'
  -- Start from the qc-cover witness around the image point `φ x'`.
  have hneigh := exists_finite_compact_image_neighborhood h𝒰 (φ x')
  obtain ⟨s, E, hEcompact, hUnhds⟩ := hneigh
  have hPreNhds :
      φ ⁻¹' (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x' := by
    exact
      (ContinuousMap.continuous (TopCat.Hom.hom φ.hom)).continuousAt.preimage_mem_nhds hUnhds
  -- Shrink to a compact neighborhood inside that preimage.
  obtain ⟨F, hFbasis, hFsubset⟩ :=
    (compact_basis_nhds x').mem_iff.mp hPreNhds
  rcases hFbasis with ⟨hFnhds, hFcompact⟩
  have hPullbackPieces :
      ∀ i : s, ∃ P : Set (Limits.pullback (𝒰.obj i.1).hom φ).obj, IsCompact (P) ∧
        F ∩ φ ⁻¹' ((𝒰.obj i.1).hom '' E i) ⊆ Limits.pullback.snd (𝒰.obj i.1).hom φ '' P := by
    intro i
    -- Apply the compact pullback helper to each compact source piece selected around `φ x'`.
    exact exists_compact_pullback_cover_of_compact_images
      φ i.1 (hEcompact i) hFcompact
  choose E' hE'compact hE'cover using hPullbackPieces
  refine ⟨s, E', hE'compact, ?_⟩
  -- It is enough to cover the chosen compact neighborhood `F`, since `F` is a neighborhood of `x'`.
  refine Filter.mem_of_superset hFnhds ?_
  intro y hyF
  have hyPreimage : y ∈ φ ⁻¹' (⋃ i : s, (𝒰.obj i.1).hom '' E i) := hFsubset hyF
  rcases Set.mem_iUnion.mp hyPreimage with ⟨i, hyi⟩
  have hyRect : y ∈ F ∩ φ ⁻¹' ((𝒰.obj i.1).hom '' E i) := ⟨hyF, hyi⟩
  have hyCover : y ∈ Limits.pullback.snd (𝒰.obj i.1).hom φ '' E' i := hE'cover i hyRect
  exact Set.mem_iUnion.mpr ⟨i, hyCover⟩

/-- Source-facing bridge for Lemma 21.31.3 (3): any indexed family presenting the pullbacks of a
qc covering family is again a qc covering. This translates the owner-level `baseChange` theorem
back to the textbook `ofArrows` presentation. -/
theorem of_pullbackFamily
    {I : Type v} {Y : LCCat.{u}} {X_ : I → LCCat.{u}}
    (f : ∀ i, X_ i ⟶ X)
    (hf : (ofArrows X_ f).IsQcCoveringOne)
    (g : Y ⟶ X)
    {P : I → LCCat.{u}} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X_ i)
    (hpb : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    (ofArrows P p₁).IsQcCoveringOne := by
  classical
  have hcanon :
      (ofArrows
        (fun i ↦ pullback (f i) g)
        (fun i ↦ pullback.snd (f i) g)).IsQcCoveringOne := by
    simpa [baseChange_eq_map_pullback] using
      (baseChange hf g)
  rw [ofArrows_isQcCoveringOne_iff] at hcanon ⊢
  intro y
  obtain ⟨s, E, hEcompact, hEnhds⟩ := hcanon y
  let eIso : ∀ i : s, P i.1 ≅ pullback (f i.1) g := fun i ↦
    (hpb i.1).isoPullback ≪≫ pullbackSymmetry g (f i.1)
  let e : ∀ i : s, (P i.1).obj ≃ₜ (pullback (f i.1) g).obj := fun i ↦
    TopCat.homeoOfIso
      (HausdorffLocallyCompactObject.ι.mapIso (eIso i))
  let F : ∀ i : s, Set ((P i.1).obj) := fun i ↦ (e i) ⁻¹' E i
  refine ⟨s, F, ?_, ?_⟩
  · intro i
    simpa [F] using (Homeomorph.isCompact_preimage (e i)).2 (hEcompact i)
  · have hcomponent :
        ∀ i : s, p₁ i.1 '' F i = pullback.snd (f i.1) g '' E i := by
      intro i
      have he_hom :
          (eIso i).hom ≫ pullback.snd (f i.1) g = p₁ i.1 := by
        calc
          (eIso i).hom ≫ pullback.snd (f i.1) g =
              (hpb i.1).isoPullback.hom ≫
                (pullbackSymmetry g (f i.1)).hom ≫ pullback.snd (f i.1) g := by
                  simp [eIso, Category.assoc]
          _ = (hpb i.1).isoPullback.hom ≫ pullback.fst g (f i.1) := by
                rw [pullbackSymmetry_hom_comp_snd]
          _ = p₁ i.1 := IsPullback.isoPullback_hom_fst (hpb i.1)
      ext z
      constructor
      · intro hz
        rcases hz with ⟨x, hx, rfl⟩
        refine ⟨(e i) x, hx, ?_⟩
        simpa [F, e] using ConcreteCategory.congr_hom he_hom x
      · intro hz
        rcases hz with ⟨w, hw, rfl⟩
        refine ⟨(e i).symm w, ?_, ?_⟩
        · simpa [F] using hw
        · have hpoint := ConcreteCategory.congr_hom he_hom ((e i).symm w)
          have happly :
              (ConcreteCategory.hom (eIso i).hom)
                ((e i).symm w) = w := by
            simpa [e] using (e i).apply_symm_apply w
          calc
            (ConcreteCategory.hom (p₁ i.1)) ((e i).symm w) =
                (ConcreteCategory.hom (pullback.snd (f i.1) g))
                  ((ConcreteCategory.hom (eIso i).hom)
                    ((e i).symm w)) := by
                      simpa using hpoint.symm
            _ = (ConcreteCategory.hom (pullback.snd (f i.1) g)) w := by
                  rw [happly]
    have hunion :
        (⋃ i : s, p₁ i.1 '' F i) =
          ⋃ i : s, pullback.snd (f i.1) g '' E i := by
      ext z
      simp [hcomponent]
    simpa [F, hunion] using hEnhds

end CategoryTheory.SemiRepresentableFamily.Over.IsQcCoveringOne

end
