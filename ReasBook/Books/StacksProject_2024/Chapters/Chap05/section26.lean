import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.ExtremallyDisconnected

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_26_1 (from Chap05) -/
/- Domain-style sampling for extremal disconnectedness:
- primary domain: extremally disconnected spaces in general topology
- owner declarations sampled: `ExtremallyDisconnected`,
  `ExtremallyDisconnected.open_closure`,
  `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`,
  `CompactT2.projective_iff_extremallyDisconnected`
- canonical owner abstraction: `ExtremallyDisconnected`
- primitive data: the class field `open_closure`
- derived API: consequences such as
  `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen` and
  `CompactT2.projective_iff_extremallyDisconnected`

Layer triage:
- `source-facing`: the Stacks definition that the closure of every open subset is open
- `core/canonical`: the mathlib predicate `ExtremallyDisconnected`
- `bridge/view`: field projection `ExtremallyDisconnected.open_closure`

This item is a direct recall of the canonical owner. Keeping a separate theorem of the form
`ExtremallyDisconnected X ↔ ∀ U, IsOpen U → IsOpen (closure U)` would only restate the class field
and create an unnecessary parallel API surface.
-/

/- Definition 5.26.1: a topological space is extremally disconnected if the closure of every open
subset is open; this is the canonical mathlib predicate `ExtremallyDisconnected`. -/
recall ExtremallyDisconnected

/-! ### Lemma_5_26_2 (from Chap05) -/
/- Domain-style sampling for Lemma 5.26.2:
- primary domain: Gleason's Zorn-subset-condition lemmas in general topology
- sampled owner declarations:
  `ExtremallyDisconnected`,
  `CompactT2.Projective.extremallyDisconnected`,
  `exists_compact_surjective_zorn_subset`,
  `image_subset_closure_compl_image_compl_of_isOpen`
- best owner abstraction for this item: the theorem
  `image_subset_closure_compl_image_compl_of_isOpen` itself
- primitive data: a continuous surjection `ρ` and the Zorn-subset condition on proper closed
  subsets of the source
- derived API: the closure containment `ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ)` for open `G`

Layer triage:
- `source-facing`: the closure statement under the Zorn-subset condition
- `core/canonical`: `image_subset_closure_compl_image_compl_of_isOpen`
- `bridge/view`: downstream uses of this theorem inside the extremally disconnected/projective
  compact Hausdorff development

This item is already owned canonically by mathlib, so the refined file should recall that theorem
directly rather than keep any parallel local alias or wrapper.
-/

/- Lemma 5.26.2: if `ρ` is a continuous surjection satisfying the Zorn-subset condition, then
for any open `G`, the image `ρ '' G` is contained in the closure of the complement of
`ρ '' Gᶜ`. This is exactly the canonical mathlib theorem
`image_subset_closure_compl_image_compl_of_isOpen`. -/
recall image_subset_closure_compl_image_compl_of_isOpen

/-! ### Lemma_5_26_3 (from Chap05) -/
/- Domain-style sampling for extremal disconnectedness:
- primary domain: extremally disconnected spaces in general topology
- owner declarations sampled: `ExtremallyDisconnected`,
  `ExtremallyDisconnected.open_closure`,
  `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`,
  `CompactT2.projective_iff_extremallyDisconnected`
- canonical owner abstraction: `ExtremallyDisconnected`
- primitive data: the class field `open_closure`
- derived API: the disjoint-closure lemma recalled below

Layer triage:
- `source-facing`: the Stacks lemma that disjoint open subsets have disjoint closures
- `core/canonical`: the mathlib owner predicate `ExtremallyDisconnected`
- `bridge/view`: the owner field `ExtremallyDisconnected.open_closure`

This item should remain a direct recall of the canonical derived theorem rather than a parallel
local lemma reproving the same statement from `open_closure`.
-/

/- Lemma 5.26.3: let `X` be an extremally disconnected space. If `U, V ⊆ X` are disjoint open
subsets, then `closure U` and `closure V` are disjoint too. This is exactly the canonical mathlib
theorem `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`. -/
recall ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen

/-! ### Lemma_5_26_4 (from Chap05) -/
universe u v

open Set Homeomorph

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [ExtremallyDisconnected Y] {f : X → Y}

/-- Helper for Lemma 5.26.4: a continuous map from a compact space to a Hausdorff space is a
closed map. -/
lemma isClosedMap_of_continuous_compact_t2 (hf : Continuous f) : IsClosedMap f := by
  intro Z hZ
  -- Closed subsets of a compact space are compact.
  have hcompact : IsCompact Z := hZ.isCompact
  -- Continuous images of compact sets are compact, hence closed in a Hausdorff space.
  exact (hcompact.image hf).isClosed

/-- Helper for Lemma 5.26.4: the image of the complement of an open set is closed. -/
lemma isClosed_image_compl_of_isOpen (hf : Continuous f) {U : Set X} (hU : IsOpen U) :
    IsClosed (f '' Uᶜ) := by
  -- Apply the closed-map package to the closed set `Uᶜ`.
  exact isClosedMap_of_continuous_compact_t2 (f := f) hf _ hU.isClosed_compl

/-- Helper for Lemma 5.26.4: Lemma 5.26.2 places the image of a point in an open set inside the
closure of the complement of the image of the complementary closed set. -/
lemma mem_closure_compl_image_compl_of_mem_open
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y))
    {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U) :
    f x ∈ closure ((f '' Uᶜ)ᶜ) := by
  -- This is the pointwise form of Lemma 5.26.2, proved directly to avoid the universe mismatch
  -- in the owner theorem's same-universe statement.
  rw [mem_closure_iff]
  intro N hN hxN
  have hnonempty : (U ∩ f ⁻¹' N).Nonempty :=
    ⟨x, mem_inter hx (mem_preimage.mpr hxN)⟩
  have hOpen : IsOpen (U ∩ f ⁻¹' N) := hU.inter (hN.preimage hf)
  have hne_univ : f '' (U ∩ f ⁻¹' N)ᶜ ≠ (univ : Set Y) :=
    hproper _ (compl_ne_univ.mpr hnonempty) hOpen.isClosed_compl
  rcases nonempty_compl.mpr hne_univ with ⟨y, hy⟩
  have hy_compl : y ∈ (f '' Uᶜ)ᶜ := by
    intro hyU
    have hsubset : Uᶜ ⊆ (U ∩ f ⁻¹' N)ᶜ := by
      intro z hz
      simp only [mem_compl_iff, mem_inter_iff, mem_preimage]
      exact fun hz' ↦ hz hz'.1
    exact hy <| image_mono hsubset hyU
  rcases hsurj y with ⟨z, rfl⟩
  have hz_mem : z ∈ U ∩ f ⁻¹' N := by
    have hz_not : z ∉ (U ∩ f ⁻¹' N)ᶜ := by
      intro hz_compl
      exact hy ⟨z, hz_compl, rfl⟩
    simpa only [mem_compl_iff, mem_inter_iff, mem_preimage, not_not] using hz_not
  exact ⟨f z, mem_inter (mem_preimage.mp hz_mem.2) hy_compl⟩

/-- Helper for Lemma 5.26.4: in an extremally disconnected space, if two closed sets cover the
space, then the closures of their open complements are disjoint. -/
lemma disjoint_closure_compl_of_closed_cover {A B : Set Y}
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ) :
    Disjoint (closure Aᶜ) (closure Bᶜ) := by
  have hdisj : Disjoint Aᶜ Bᶜ := by
    -- The complements are disjoint because `A` and `B` already cover the space.
    rw [disjoint_iff_inter_eq_empty, ← compl_union, hcover, compl_univ]
  -- Lemma 5.26.3 upgrades disjoint open sets to disjoint closures.
  exact
    ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen hdisj hA.isOpen_compl
      hB.isOpen_compl

/-- Helper for Lemma 5.26.4: the proper-image condition on closed subsets forces injectivity. -/
lemma injective_of_surjective_of_image_proper_closed
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) :
    Function.Injective f := by
  intro x x' hfx
  by_contra hxx'
  -- Separate the two distinct source points by disjoint open neighborhoods.
  rcases t2_separation hxx' with ⟨U, V, hU, hV, hxU, hx'V, hUV⟩
  let T : Set Y := f '' Uᶜ
  let T' : Set Y := f '' Vᶜ
  have hTclosed : IsClosed T := by
    -- The closed-map argument shows `f (X \ U)` is closed.
    simpa [T] using isClosed_image_compl_of_isOpen (f := f) hf hU
  have hT'closed : IsClosed T' := by
    -- The same argument applies to `f (X \ V)`.
    simpa [T'] using isClosed_image_compl_of_isOpen (f := f) hf hV
  have hcover : T ∪ T' = univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      rcases hsurj y with ⟨z, rfl⟩
      have hz : z ∈ Uᶜ ∪ Vᶜ := by
        by_cases hzU : z ∈ U
        · have hzV : z ∉ V := by
            intro hzV
            exact hUV.le_bot ⟨hzU, hzV⟩
          exact Or.inr hzV
        · exact Or.inl hzU
      rcases hz with hzU | hzV
      · exact Or.inl ⟨z, hzU, rfl⟩
      · exact Or.inr ⟨z, hzV, rfl⟩
  have hdisj : Disjoint (closure Tᶜ) (closure T'ᶜ) := by
    -- Since `T` and `T'` cover `Y`, the extremally disconnected lemma makes these closures disjoint.
    exact disjoint_closure_compl_of_closed_cover (A := T) (B := T') hTclosed hT'closed hcover
  have hxT : f x ∈ closure Tᶜ := by
    -- Lemma 5.26.2 applied to the open neighborhood `U`.
    simpa [T] using
      mem_closure_compl_image_compl_of_mem_open (f := f) hf hsurj hproper hU hxU
  have hx'T' : f x' ∈ closure T'ᶜ := by
    -- Lemma 5.26.2 applied to the open neighborhood `V`.
    simpa [T'] using
      mem_closure_compl_image_compl_of_mem_open (f := f) hf hsurj hproper hV hx'V
  exact hdisj.ne_of_mem hxT hx'T' hfx

/-- Lemma 5.26.4: a surjective continuous map from a Hausdorff quasi-compact space to an
extremally disconnected Hausdorff space is a homeomorphism if the image of every proper closed
subset of the source is a proper subset of the target. The target's quasi-compactness is automatic
from surjectivity and compactness of the source, so it is omitted from the Lean hypotheses. -/
theorem isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) :
    IsHomeomorph f := by
  -- Follow Lemma 5.17.8: once surjectivity is given, it remains to prove injectivity.
  have hinj : Function.Injective f :=
    injective_of_surjective_of_image_proper_closed (f := f) hf hsurj hproper
  -- The compact-to-Hausdorff criterion now turns continuity and bijectivity into a homeomorphism.
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨hf, ⟨hinj, hsurj⟩⟩

end

/-! ### Lemma_5_26_5 (from Chap05) -/
/- Domain-style sampling for Gleason's minimal compact surjective subsets:
- primary domain: compactness/Zorn-minimality for continuous surjections in general topology
- sampled owner declarations:
  `exists_compact_surjective_zorn_subset`,
  `image_subset_closure_compl_image_compl_of_isOpen`,
  `ExtremallyDisconnected.homeoCompactToT2`
- best owner abstraction for this item: the theorem
  `exists_compact_surjective_zorn_subset`

Layer triage:
- `source-facing`: the Stacks formulation using a compact subset `E ⊆ X`
- `core/canonical`: mathlib's owner theorem `exists_compact_surjective_zorn_subset`, phrased with
  `CompactSpace E` for the subtype
- `bridge/view`: the equivalent `IsCompact E` restatement, which should stay companion-only if
  needed downstream

Primitive data is only the continuous surjection. The compactness of the chosen subset is derived
from the owner theorem. A local theorem obtained only by rewriting `CompactSpace E` as
`IsCompact (E : Set X)` would be a duplicate wrapper around the canonical owner rather than new
source-level mathematics, so this item should refine to direct recall/use of the owner theorem.
-/

/- Lemma 5.26.5: the canonical owner theorem
`exists_compact_surjective_zorn_subset` already gives exactly the Stacks minimal-surjective-subset
construction, packaging the chosen subset through the compact subtype `E`. Keeping a second theorem
that only rewrites this as `IsCompact (E : Set X)` would create redundant API. -/
recall exists_compact_surjective_zorn_subset

/-! ### Proposition_5_26_6 (from Chap05) -/
universe u

open Function

/- Domain-style sampling for Proposition 5.26.6:
- primary domain: projective compact Hausdorff spaces and extremal disconnectedness
- sampled owner declarations:
  `CompactT2.Projective`,
  `CompactT2.Projective.extremallyDisconnected`,
  `CompactT2.ExtremallyDisconnected.projective`,
  `CompactT2.projective_iff_extremallyDisconnected`
- best owner abstraction: `CompactT2.Projective`
- primitive data: the lifting property against surjective maps in compact Hausdorff spaces
- derived API: the special section property for surjections onto `X`, and the equivalence with
  `ExtremallyDisconnected`

Layer triage:
- `source-facing`: the three-way equivalence in Proposition 5.26.6
- `core/canonical`: `CompactT2.Projective`
- `bridge/view`: the section-property reformulation below

The section clause is not a second owner. It is the `Z = X`, `f = id` specialization of
projectivity, and the converse is recovered from the pullback projection `X ×_Z Y → X`.
-/

-- Proof sketch: use `CompactT2.projective_iff_extremallyDisconnected` for the equivalence of
-- `(1)` and `(3)`. Condition `(2)` is the special case of projectivity obtained by taking
-- `Z = X` and `f = id`, while conversely a lifting problem against a surjection `Y → Z` is
-- converted into a section problem for the pullback projection `X ×_Z Y → X`.
/-- For a compact Hausdorff space, projectivity is equivalent to the section property for
surjective maps onto `X`. This isolates condition `(2)` of Proposition 5.26.6 in the canonical
language of `CompactT2.Projective`. -/
theorem compactT2_projective_iff_surjective_has_section
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    CompactT2.Projective X ↔
      ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
        Continuous f → Surjective f →
          ∃ s : X → Y, Continuous s ∧ RightInverse s f := by
  constructor
  · intro h Y _ _ _ f hf hsurj
    rcases h continuous_id hf hsurj with ⟨s, hs, hsf⟩
    exact ⟨s, hs, fun x ↦ congr_fun hsf x⟩
  · intro h Y Z _ _ _ _ _ _ f g hf hg hsurj
    let E := { p : X × Y // f p.1 = g p.2 }
    have hE_closed : IsClosed { p : X × Y | f p.1 = g p.2 } :=
      isClosed_fiberProduct_subset hf hg
    haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE_closed.isCompact
    haveI : T2Space E := inferInstance
    let fst : E → X := fun p ↦ p.1.1
    have hfst : Continuous fst := continuous_fst.comp continuous_subtype_val
    have hfst_surj : Surjective fst := by
      intro x
      rcases hsurj (f x) with ⟨y, hy⟩
      refine ⟨⟨(x, y), ?_⟩, rfl⟩
      simp [hy]
    rcases h hfst hfst_surj with ⟨s, hs, hsfst⟩
    refine ⟨fun x ↦ (s x).1.2, continuous_snd.comp <| continuous_subtype_val.comp hs, ?_⟩
    ext x
    have hs_mem : f (s x).1.1 = g (s x).1.2 := (s x).2
    simpa [fst, hsfst x] using hs_mem.symm

/-- Proposition 5.26.6: for a compact Hausdorff space `X`, the following are equivalent:
`X` is extremally disconnected; every surjective continuous map `f : Y → X` from a compact
Hausdorff space admits a continuous section; and `X` is projective in the category of compact
Hausdorff spaces. The canonical projectivity clause is `CompactT2.Projective X`. -/
theorem compactT2_extremallyDisconnected_tfae
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    List.TFAE
      [ ExtremallyDisconnected X,
        ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
          Continuous f → Surjective f →
            ∃ s : X → Y, Continuous s ∧ RightInverse s f,
        CompactT2.Projective X ] := by
  tfae_have 1 ↔ 3 := CompactT2.projective_iff_extremallyDisconnected.symm
  tfae_have 2 ↔ 3 := compactT2_projective_iff_surjective_has_section.symm
  tfae_finish

/-! ### Lemma_5_26_7 (from Chap05) -/
universe u

open Function Set

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Domain-style sampling for Lemma 5.26.7:
- primary domain: separation properties of Hausdorff spaces and continuous self-maps
- sampled owner declarations:
  `t2_separation`,
  `Disjoint.notMem_of_mem_left`,
  `Set.image_union_image_compl_eq_range`,
  `Function.Surjective.range_eq`
- best owner abstraction: this item is `source-facing`; its ambient canonical owner data are the
  Hausdorff separation theorem `t2_separation` together with the standard `Set` image/complement
  cover theorem, but there is no upstream project or mathlib theorem with the exact Stacks
  conclusion
- primitive data: a continuous surjective self-map `f : X → X`, the nonidentity witness
  `hne : f ≠ id`, and Hausdorff separation for two distinct points
- derived API: the constructed proper closed set `E = (U ∩ f ⁻¹' V)ᶜ` and the cover
  `E ∪ f '' E = univ`

Layer triage:
- `source-facing`: the existence of the proper closed set `E`
- `core/canonical`: `T2Space`, `t2_separation`, and standard image/preimage lemmas
- `bridge/view`: none needed here, since the full statement is not already owned upstream
-/

/-- A set is a proper closed image-cover for `f` if it is closed, proper, and together with its
image under `f` covers the whole space. -/
structure IsProperClosedImageCover (f : X → X) (E : Set X) : Prop where
  isClosed : IsClosed E
  ne_univ : E ≠ univ
  union_image_eq_univ : E ∪ f '' E = univ

-- Proof sketch: choose `p` with `f p ≠ p`, separate `p` and `f p` by disjoint open sets `U` and
-- `V`, and define `E = (U ∩ f ⁻¹' V)ᶜ`. This set is closed and proper since `p ∉ E`. For any
-- `x ∉ E`, surjectivity gives `x = f y`; if `y ∉ E` as well, then `y ∈ U ∩ f ⁻¹' V`, forcing
-- `x ∈ U ∩ V`, a contradiction. Hence `y ∈ E`, so `x ∈ f '' E`.
/-- Lemma 5.26.7: a surjective continuous nonidentity self-map of a Hausdorff space admits a
proper closed subset whose union with its image is all of `X`. -/
theorem exists_proper_closed_set_union_image_eq_univ
    {f : X → X} (hf : Continuous f) (hsurj : Surjective f) (hne : f ≠ id) :
    ∃ E : Set X, IsProperClosedImageCover f E := by
  -- First extract a point moved by `f`; otherwise `f = id` by function extensionality.
  obtain ⟨p, hp_ne⟩ : ∃ p : X, f p ≠ p := by
    by_contra h
    apply hne
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  -- Separate the two distinct points `p` and `f p` by disjoint open neighborhoods.
  obtain ⟨U, V, hU, hV, hpU, hfpV, hUV⟩ := t2_separation hp_ne.symm
  let E : Set X := (U ∩ f ⁻¹' V)ᶜ
  refine ⟨E, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The complement of the open separator region is closed.
    exact (hU.inter (hV.preimage hf)).isClosed_compl
  · -- The point `p` lies in the separator region, so `E` is proper.
    intro hE
    have hp_mem : p ∈ E := by
      simp [hE]
    have hp_not_mem : p ∉ E := by
      simpa [E] using ⟨hpU, hfpV⟩
    exact hp_not_mem hp_mem
  · -- Any point is either already in `E`, or it is the image of a point of `E`.
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · right
      rcases hsurj x with ⟨y, rfl⟩
      have hyE : y ∈ E := by
        -- If `y` were also in the separator region, then `f y` would lie in `U ∩ V`.
        by_contra hyNotE
        have hyUV : y ∈ U ∩ f ⁻¹' V := by
          simpa [E] using hyNotE
        have hfyV : f y ∈ V := hyUV.2
        have hfyU : f y ∈ U := by
          have hxUV : f y ∈ U ∩ f ⁻¹' V := by
            simpa [E] using hxE
          exact hxUV.1
        exact (hUV.notMem_of_mem_left hfyU) hfyV
      exact ⟨y, hyE, rfl⟩

end

/-! ### Example_5_26_8 (from Chap05) -/
universe u

section

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/- Domain-style sampling for Example 5.26.8:
- primary domain: Stone-Cech compactification of discrete spaces inside compact Hausdorff
  projectivity and extremal disconnectedness;
- inspected owner declarations:
  `StoneCech.projective`,
  `CompactT2.Projective.extremallyDisconnected`,
  `CompactT2.projective_iff_extremallyDisconnected`;
- best owner abstraction: `StoneCech.projective`, with extremal disconnectedness as derived API;
- primitive-vs-derived split: the discrete topology on `X` is the only input needed to invoke the
  canonical owner theorem `StoneCech.projective`, while the conclusion
  `ExtremallyDisconnected (StoneCech X)` is derived via the canonical bridge
  `CompactT2.Projective.extremallyDisconnected`.

Layer triage:
- `source-facing`: the textbook example that the Stone-Cech compactification of a discrete space is
  extremally disconnected;
- `core/canonical`: the owner theorem `StoneCech.projective`;
- `bridge/view`: the specialization `StoneCech.extremallyDisconnected` below.

The source item is not a new owner and should not introduce an ad hoc global wrapper instance.
The natural public surface is the owner-prefixed theorem obtained by applying the canonical bridge
from projectivity to extremal disconnectedness.
-/

namespace StoneCech

-- Proof sketch: apply the canonical projectivity theorem for the Stone-Cech compactification of a
-- discrete space, then pass to the derived extremal-disconnectedness API.
/-- Example 5.26.8: the Stone-Cech compactification of a discrete space is extremally
disconnected. -/
theorem extremallyDisconnected : ExtremallyDisconnected (StoneCech X) :=
  CompactT2.Projective.extremallyDisconnected projective

end StoneCech

end

/-! ### Lemma_5_26_9 (from Chap05) -/
open CategoryTheory Set
open scoped Topology

universe u

/- Domain-style sampling for Stonean presentations and minimal Stonean covers:
- primary domain: Stonean presentations and uniqueness of minimal Stonean surjections in `CompHaus`
- sampled owner declarations:
  `CompHaus.presentation`,
  `CompHaus.presentation.π`,
  `CompHaus.lift`,
  `isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed`
- best owner abstractions: `CompHaus.presentation` for the existence statement, and the chapter
  owner theorem
  `isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed` for uniqueness
- primitive data: the canonical presentation map, and a morphism over `X` together with
  surjectivity and the proper-closed-image minimality condition
- derived API: the textbook existential restatements and the resulting homeomorphism over `X`

Layer triage:
- `source-facing`: existence of a Stonean surjection onto `X`, and uniqueness up to homeomorphism
  among minimal Stonean surjections onto `X`
- `core/canonical`: `CompHaus.presentation`, `CompHaus.lift`, and the owner homeomorphism
  criterion from `Lemma_5_26_4`
- `bridge/view`: the existential and over-`X` restatements below

The minimality hypothesis is theorem-level data, not a new owner structure. This file should
therefore reuse the existing chapter owner theorem for the homeomorphism criterion rather than
re-proving a Stonean-specialized version through `ExtremallyDisconnected.homeoCompactToT2`.
-/

section

variable (X : CompHaus.{u})

-- Proof sketch: use the canonical Stonean presentation `CompHaus.presentation X`, whose structure
-- map to `X` is already an epimorphism in `CompHaus`; for compact Hausdorff spaces, epimorphisms
-- are exactly surjections.
/-- Lemma 5.26.9 (1): every quasi-compact Hausdorff space admits a continuous surjection from an
extremally disconnected quasi-compact Hausdorff space. The canonical bundled witness is the
presentation map `CompHaus.presentation.π X : X.presentation.compHaus ⟶ X`. -/
theorem presentation_pi_surjective :
    Function.Surjective (CompHaus.presentation.π X) := by
  simpa using (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp inferInstance

/-- Textbook existential restatement of Lemma 5.26.9 (1). -/
theorem exists_stonean_surjection :
    ∃ Y : Stonean.{u}, ∃ f : Y.compHaus ⟶ X, Function.Surjective f := by
  exact ⟨CompHaus.presentation X, CompHaus.presentation.π X, presentation_pi_surjective X⟩

end

section

variable {X : CompHaus.{u}} {Y Z : Stonean.{u}}
variable {f : Y.compHaus ⟶ X} {g : Z.compHaus ⟶ X}

-- Proof sketch: if `h : Y.compHaus ⟶ Z.compHaus` satisfies `h ≫ g = f`, then its image is closed
-- in `Z` because `Y` is compact and `Z` is Hausdorff, and it still surjects onto `X`, so
-- minimality of `g` makes `h` surjective. The same commutative-square relation shows that the
-- image of every proper closed subset of `Y` remains proper in `Z`, and the earlier chapter owner
-- theorem upgrades this to a homeomorphism.
/-- Lemma 5.26.9 (2): any morphism over `X` between two minimal Stonean surjections is a
homeomorphism. -/
theorem isHomeomorph_of_minimal_stonean_morphism_over
    (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g)
    (hf_min : ∀ E : Set Y, E ≠ (Set.univ : Set Y) → IsClosed E → f '' E ≠ (Set.univ : Set X))
    (hg_min : ∀ E : Set Z, E ≠ (Set.univ : Set Z) → IsClosed E → g '' E ≠ (Set.univ : Set X))
    {h : Y.compHaus ⟶ Z.compHaus} (hh : h ≫ g = f) :
    IsHomeomorph h := by
  let hTop : C(Y, Z) := TopCat.Hom.hom h.hom
  have hh_cont : Continuous h := by
    simpa [hTop] using hTop.continuous
  have hh_range_closed : IsClosed (Set.range h) := by
    rw [← Set.image_univ]
    exact (CompHausLike.isClosedMap h) _ isClosed_univ
  have hh_surj : Function.Surjective h := by
    rw [← Set.range_eq_univ]
    by_contra hnot
    have himage : g '' Set.range h = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
      rcases hf_surj x with ⟨y, rfl⟩
      refine ⟨h y, ⟨y, rfl⟩, ?_⟩
      change g (h y) = f y
      simpa using ConcreteCategory.congr_hom hh y
    exact (hg_min (Set.range h) (by simpa [Set.range_eq_univ] using hnot) hh_range_closed) himage
  refine isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed
    hh_cont hh_surj ?_
  intro E hE hE_closed h_image_univ
  have h_image : f '' E = g '' (h '' E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, ⟨y, hy, rfl⟩, by simpa using ConcreteCategory.congr_hom hh y⟩
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simpa using (ConcreteCategory.congr_hom hh y).symm⟩
  have : f '' E = Set.univ := by
    rw [h_image, h_image_univ]
    exact Set.image_univ_of_surjective hg_surj
  exact hf_min E hE hE_closed this

/-- Textbook restatement of Lemma 5.26.9 (2): two minimal Stonean surjections onto `X` are
homeomorphic over `X`. -/
theorem exists_homeomorph_over_of_minimal_stonean_surjections
    (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g)
    (hf_min : ∀ E : Set Y, E ≠ (Set.univ : Set Y) → IsClosed E → f '' E ≠ (Set.univ : Set X))
    (hg_min : ∀ E : Set Z, E ≠ (Set.univ : Set Z) → IsClosed E → g '' E ≠ (Set.univ : Set X)) :
    ∃ e : Y ≃ₜ Z, g ∘ e = f := by
  letI : Epi g := (CompHaus.epi_iff_surjective g).2 hg_surj
  rcases isHomeomorph_iff_exists_homeomorph.mp
      (isHomeomorph_of_minimal_stonean_morphism_over hf_surj hg_surj hf_min hg_min
        (CompHaus.lift_lifts f g)) with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  ext y
  calc
    g (e y) = g ((CompHaus.lift f g) y) := by simp [he]
    _ = f y := by
      change ((CompHaus.lift f g) ≫ g) y = f y
      exact ConcreteCategory.congr_hom (CompHaus.lift_lifts f g) y

end

/-! ### Remark_5_26_10 (from Chap05) -/
universe u v

open Cardinal Function Set

/- Domain-style sampling for Remark 5.26.10:
- primary domain: dense sections of minimal surjections and the resulting Hausdorff cardinal bounds
- sampled owner declarations:
  `Function.surjInv`
  `Function.rightInverse_surjInv`
  `DenseRange`
  `cardinalMk_le_powerpower_of_denseRange`
- best owner abstraction: the section data already has the canonical owner `Function.surjInv`;
  dense range and the cardinal estimate are derived API on top of that owner
- primitive data: a surjective map `f : X' → X` together with the proper-closed-image minimality
  condition on subsets of `X'`
- derived API: the canonical section `surjInv hsurj` has dense range, and for Hausdorff `X'` this
  feeds into `cardinalMk_le_powerpower_of_denseRange`

Layer triage:
- `source-facing`: the cardinal estimate of Remark 5.26.10
- `core/canonical`: `Function.surjInv`, `Function.rightInverse_surjInv`, and `DenseRange`
- `bridge/view`: `denseRange_surjInv_of_minimal_surjective`

The existential helper is duplicate wheel API: once `hsurj` is fixed, the relevant section already
has the canonical owner `surjInv hsurj`, so the refined file should prove properties of that owner
directly and derive the cardinal bound from the chapter owner
`cardinalMk_le_powerpower_of_denseRange`.
-/

section

variable {X : Type u} {X' : Type v} [TopologicalSpace X']

/-- The canonical right inverse of a minimal surjection has dense range. -/
theorem denseRange_surjInv_of_minimal_surjective
    (f : X' → X) (hsurj : Surjective f)
    (hminimal :
      ∀ Z : Set X', Z ≠ (Set.univ : Set X') → IsClosed Z → f '' Z ≠ (Set.univ : Set X)) :
    DenseRange (surjInv hsurj) := by
  rw [denseRange_iff_closure_range]
  by_contra hclosure
  have hproper : closure (range (surjInv hsurj)) ≠ (univ : Set X') := by
    simpa using hclosure
  have himage : f '' closure (range (surjInv hsurj)) = (univ : Set X) := by
    refine eq_univ_iff_forall.mpr fun x ↦ ?_
    refine ⟨surjInv hsurj x, subset_closure ?_, surjInv_eq hsurj x⟩
    exact ⟨x, rfl⟩
  exact hminimal _ hproper isClosed_closure himage

end

section

variable {X : Type u} {X' : Type v} [TopologicalSpace X'] [T2Space X']

-- Proof sketch: the minimality hypothesis forces the canonical section `surjInv hsurj : X → X'`
-- to have dense range. Apply the chapter owner theorem
-- `cardinalMk_le_powerpower_of_denseRange` to that section and then use monotonicity in `κ`.
/-- Remark 5.26.10: if `|X| ≤ κ` and `f : X' → X` is a minimal surjection, then
`|X'| ≤ 2 ^ (2 ^ κ)`. The compactness, Hausdorff, and extremal-disconnectedness assumptions from
the textbook are not needed for this cardinal estimate once the minimality hypothesis is given. -/
theorem cardinalMk_le_powerpower_of_minimal_surjective
    (f : X' → X) (hsurj : Surjective f)
    (hminimal :
      ∀ Z : Set X', Z ≠ (Set.univ : Set X') → IsClosed Z → f '' Z ≠ (Set.univ : Set X))
    (κ : Cardinal.{max u v}) (hκX : Cardinal.lift (Cardinal.mk X) ≤ κ) :
    Cardinal.lift (Cardinal.mk X') ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := by
  calc
    Cardinal.lift (Cardinal.mk X') ≤
        (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.lift (Cardinal.mk X)) := by
      simpa using
        (cardinalMk_le_powerpower_of_denseRange
          (denseRange_surjInv_of_minimal_surjective f hsurj hminimal))
    _ ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := by
      exact power_le_power_left two_ne_zero (power_le_power_left two_ne_zero hκX)

end
