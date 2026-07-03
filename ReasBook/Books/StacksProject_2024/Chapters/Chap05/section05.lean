import Mathlib.Tactic.Recall
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_5_1 (from Chap05) -/
/- Domain-style sampling for topological bases:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.isTopologicalBasis_opens`,
  `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `isTopologicalBasis_generateFrom`

Layer triage:
- `source-facing`: the textbook notion that a family of subsets is a basis for the topology
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: nearby chapter lemmas such as `isTopologicalBasis_generateFrom` and
  `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Primitive data is exactly the owner structure fields
`exists_subset_inter`, `sUnion_eq`, and `eq_generateFrom`. The openness and local-refinement
formulations are derived API, so this file should recall the canonical owner directly rather than
introducing a parallel local predicate or a large specification theorem.
-/

/- Definition 5.5.1: a collection of subsets of a topological space is a basis for the topology
if every basis element is open and every open set is locally refined by a basis element; this is
the canonical mathlib predicate `TopologicalSpace.IsTopologicalBasis`. -/
recall TopologicalSpace.IsTopologicalBasis

/-! ### Lemma_5_5_2 (from Chap05) -/
open Set TopologicalSpace

universe u

section

variable {X : Type u}

/-
Domain-style sampling for generated topologies from basis data:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis`,
  `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`,
  `TopologicalSpace.IsTopologicalBasis.exists_subset_inter`,
  `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`,
  `Definition_5_5_1`

Layer triage:
- `source-facing`: a family covering `X` and admitting local intersection refinements generates a
  topology for which it is a basis
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: the generated-topology basis construction and the ensuing uniqueness statement

Primitive data is exactly the owner fields `exists_subset_inter`, `sUnion_eq`, and
`eq_generateFrom`. The existence-and-uniqueness theorem is derived API from `eq_generateFrom`, so
this file should construct the canonical owner directly rather than introducing a parallel local
predicate or a large specification theorem.
-/

-- Proof sketch: the hypotheses are exactly the non-topological fields of
-- `TopologicalSpace.IsTopologicalBasis`, and the remaining field is witnessed by the generated
-- topology `generateFrom B`.
/-- Lemma 5.5.2: if `B` covers `X` and is stable under basis refinement of pairwise
intersections, then `B` is a topological basis for the generated topology `generateFrom B`. -/
theorem isTopologicalBasis_generateFrom (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V)
    : let _ : TopologicalSpace X := generateFrom B
      IsTopologicalBasis B := by
  let _ : TopologicalSpace X := generateFrom B
  refine ⟨fun U hU V hV x hx ↦ hinter hU hV hx, hcover, rfl⟩

-- Proof sketch: existence is provided by `generateFrom B`, and uniqueness follows from the
-- `eq_generateFrom` field of a topological basis.
/-- Lemma 5.5.2, existence-and-uniqueness form: there exists a unique topology on `X` for which `B`
is a topological basis. -/
theorem existsUnique_topology_with_basis (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V)
    : ∃! t : TopologicalSpace X, let _ : TopologicalSpace X := t
      IsTopologicalBasis B := by
  refine ⟨generateFrom B, isTopologicalBasis_generateFrom B hcover hinter, ?_⟩
  intro t ht
  simpa using ht.eq_generateFrom

end

/-! ### Lemma_5_5_3 (from Chap05) -/
open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for basis refinements:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_iUnion`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `Definition_5_5_1`

Layer triage:
- `source-facing`: a refinement statement for an indexed open cover of an open subset
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: the resulting indexed refining family of opens, each carried by a basis member

Primitive data is the basis owner `hB` together with the indexed open family `Ui` covering `U`.
The refining family should therefore be returned directly as basis members `V j ∈ B`, obtained by
applying the owner theorem `hB.open_eq_iUnion` to each member of the cover. The openness of each
`V j` is derived from `hB.isOpen`, so bundling those sets again as `Opens X` would only duplicate
owner data instead of exposing the source-facing refinement.
-/

/-- Helper for Lemma 5.5.3: every member of the given cover is contained in the set being
covered. -/
lemma cover_piece_subset_target
    {ι : Type v} (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∀ i, (Ui i : Set X) ⊆ (U : Set X) := by
  intro i
  -- Rewrite the covering equality so each `Ui i` becomes an explicit branch of the union.
  simpa [hUi] using Set.subset_iUnion (fun j => (Ui j : Set X)) i

/-- Helper for Lemma 5.5.3: every point of `U` lies in a basis member refining one cover
piece. -/
lemma point_has_basis_refining_cover_piece
    {ι : Type v} (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∀ x ∈ (U : Set X), ∃ i, ∃ V : {V : Set X // V ∈ B}, x ∈ (V : Set X) ∧
      (V : Set X) ⊆ (Ui i : Set X) := by
  intro x hx
  -- The cover equality provides a cover piece containing the chosen point.
  have hx' : x ∈ ⋃ i, (Ui i : Set X) := by
    simpa [hUi] using hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx'
  -- The basis axiom now refines that open neighborhood by a basis element.
  obtain ⟨V, hVB, hxV, hVUi⟩ := hB.exists_subset_of_mem_open hxi (Ui i).isOpen
  exact ⟨i, ⟨V, hVB⟩, hxV, hVUi⟩

/-- Helper for Lemma 5.5.3: a family of basis members indexed by points of `U` covers `U` once
each point belongs to its chosen basis member and each basis member refines the original cover. -/
lemma point_indexed_basis_refinement_covers
    {ι : Type v} (B : Set (Set X)) (U : Opens X) (Ui : ι → Opens X)
    (hUi : (U : Set X) = ⋃ i, (Ui i : Set X))
    (V : ULift.{v} U → {V : Set X // V ∈ B})
    (hmem : ∀ j : ULift.{v} U, ((j.down : U) : X) ∈ (V j : Set X))
    (href : ∀ j : ULift.{v} U, ∃ i, (V j : Set X) ⊆ (Ui i : Set X)) :
    (U : Set X) = ⋃ j, (V j : Set X) := by
  ext x
  constructor
  · intro hx
    -- Index the covering family by the point itself to obtain the forward inclusion.
    have hxV : x ∈ (V (ULift.up ⟨x, hx⟩) : Set X) := by
      simpa using hmem (ULift.up ⟨x, hx⟩)
    exact Set.mem_iUnion.mpr ⟨ULift.up ⟨x, hx⟩, hxV⟩
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hVUi⟩ := href j
    -- Refinement into one `Ui i` and the original cover put the point back inside `U`.
    exact cover_piece_subset_target U Ui hUi i (hVUi hxj)

/-- Lemma 5.5.3: every indexed open cover `U = ⋃ i Ui i` admits a refinement by members of the
basis `B`. -/
-- Proof sketch: index the refinement by points of `U`, choose for each point a basis neighborhood
-- refining one member of the cover, and then verify that these chosen basis members still cover `U`.
theorem exists_basis_refinement_of_cover
    {ι : Type v} (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∃ (J : Type (max u v)) (V : J → {V : Set X // V ∈ B}),
      (U : Set X) = ⋃ j, (V j : Set X) ∧ ∀ j, ∃ i, (V j : Set X) ⊆ Ui i := by
  classical
  -- Choose a refining basis member for each point of `U` using the pointwise basis argument.
  have hpoint :
      ∀ j : U, ∃ i, ∃ V : {V : Set X // V ∈ B}, (j : X) ∈ (V : Set X) ∧
        (V : Set X) ⊆ (Ui i : Set X) := by
    intro j
    exact point_has_basis_refining_cover_piece B hB U Ui hUi j j.property
  choose iOf VOf hmem hsub using hpoint
  refine ⟨ULift.{v} U, fun j ↦ VOf j.down, ?_⟩
  constructor
  · -- The chosen basis members cover `U` because each point indexes one of them.
    exact point_indexed_basis_refinement_covers B U Ui hUi (fun j ↦ VOf j.down)
      (fun j ↦ hmem j.down) (fun j ↦ ⟨iOf j.down, hsub j.down⟩)
  · -- The refinement property is exactly the containment chosen at each point.
    intro j
    exact ⟨iOf j.down, hsub j.down⟩

end

/-! ### Definition_5_5_4 (from Chap05) -/
open FiniteInter

namespace TopologicalSpace

universe u

variable {X : Type u}

/- Domain-style sampling for subbases:
- owner abstraction: `TopologicalSpace.generateFrom`
- same-domain declarations inspected:
  `TopologicalSpace.isTopologicalBasis_of_subbasis`,
  `TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter`,
  `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`,
  `FiniteInter.finiteInterClosure_finiteInter`

Layer triage:
- `source-facing`: a collection of subsets is a subbasis for the topology exactly when the
  topology is `generateFrom` that collection
- `core/canonical`: `TopologicalSpace.generateFrom`
- `bridge/view`: `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Primitive data is only the family `B : Set (Set X)` and the generated topology `generateFrom B`.
The finite-intersection basis is derived API coming from `finiteInterClosure B`, so this file
should recall `generateFrom` as the main declaration and keep the basis criterion as a companion
bridge theorem rather than introducing a parallel wrapper notion.
-/

/- Definition 5.5.4: a collection of subsets of `X` is a subbasis for the topology on `X`
exactly when the topology is `generateFrom` that collection. -/
recall generateFrom

private theorem generateFrom_finiteInterClosure (B : Set (Set X)) :
    generateFrom (finiteInterClosure B) = generateFrom B := by
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · intro U hU
    exact finiteInterClosure.basic hU
  · letI : TopologicalSpace X := generateFrom B
    intro U hU
    induction hU with
    | basic hU => exact GenerateOpen.basic _ hU
    | univ => simp
    | inter _ _ hU hV => exact hU.inter hV

section

variable [t : TopologicalSpace X]

/-- A collection generates the topology exactly when the finite intersections of its members form
a topological basis. -/
theorem eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure {B : Set (Set X)} :
    t = generateFrom B ↔ IsTopologicalBasis (finiteInterClosure B) := by
  constructor
  · intro hB
    have hfinite : t = generateFrom (finiteInterClosure B) := by
      simpa [generateFrom_finiteInterClosure B] using hB
    exact isTopologicalBasis_of_subbasis_of_finiteInter hfinite
      (finiteInterClosure_finiteInter B)
  · intro hB
    simpa [generateFrom_finiteInterClosure B] using hB.eq_generateFrom

end

end TopologicalSpace

/-! ### Lemma_5_5_5 (from Chap05) -/
open TopologicalSpace

universe u

/-
Domain-style sampling for subbases:
- owner abstraction: `TopologicalSpace.generateFrom`
- same-domain declarations inspected:
  `TopologicalSpace.generateFrom`,
  `FiniteInter.finiteInterClosure`,
  `TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter`,
  `TopologicalSpace.eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Layer triage:
- `source-facing`: a family is a subbasis for a topology
- `core/canonical`: `TopologicalSpace.generateFrom`
- `bridge/view`: the finite-intersection basis criterion from
  `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Primitive data is only the family `B`. The basis on `finiteInterClosure B` is derived API from the
canonical owner `generateFrom B`. The finite-intersection basis criterion belongs to the companion
bridge theorem `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`, while this lemma should
keep the source-facing subbasis semantics centered in the main statement.
-/

/- Companion recall: `generateFrom` is the canonical owner of the topology generated by a
subbasis. -/
recall generateFrom

/-- Lemma 5.5.5: for any family `B` of subsets of `X`, there is a unique topology on `X`, namely
`generateFrom B`, for which `B` is a subbasis. The equivalent finite-intersection-basis criterion
is the companion bridge theorem
`TopologicalSpace.eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`. -/
theorem existsUnique_topology_with_subbasis {X : Type u} (B : Set (Set X)) :
    ∃! t : TopologicalSpace X, t = generateFrom B := by
  -- Use the canonical generated topology as the witness from the subbasis data `B`.
  refine ⟨generateFrom B, rfl, ?_⟩
  -- Any other topology satisfying the same characterization is equal to this witness.
  intro t ht
  exact ht

/-! ### Lemma_5_5_6 (from Chap05) -/
open Set TopologicalSpace

universe u

section

variable {X : Type u}

/- Domain-style sampling for basis images under a quotient:
- primary domain: general topology of generated topologies, quotient maps, and topological bases
- owner abstractions:
  `TopologicalSpace.IsTopologicalBasis`,
  `TopologicalSpace.generateFrom`,
  `Topology.IsQuotientMap`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.continuous_iff`,
  `TopologicalSpace.IsTopologicalBasis.isQuotientMap`,
  `Topology.isQuotientMap_quotient_mk'`,
  `Lemma_5_5_2.isTopologicalBasis_generateFrom`

Layer triage:
- `source-facing`: existence of a target space whose basis is formed by the images of `B`
- `core/canonical`: the quotient type `Quotient` and the basis owner `IsTopologicalBasis`
- `bridge/view`: the quotient map equipped with the generated topology on image-basis sets

Primitive data is the quotient relation “same membership pattern on `B`” together with the image
family on the quotient. Openness of the image family and continuity of the quotient map are derived
from the canonical generated-topology basis API, so there is no need for a parallel public wrapper.
-/

/-- Helper for Lemma 5.5.6: the quotient relation identifying points with the same membership
pattern in all members of `B`. -/
private def basisPatternSetoid (B : Set (Set X)) : Setoid X where
  r x y := ∀ U ∈ B, x ∈ U ↔ y ∈ U
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x U hU
      rfl
    · intro x y hxy U hU
      exact (hxy U hU).symm
    · intro x y z hxy hyz U hU
      exact (hxy U hU).trans (hyz U hU)

/-- Helper for Lemma 5.5.6: the quotient map has exactly the expected preimage on each basis
member. -/
private theorem preimage_image_quotientMk_eq (B : Set (Set X)) {U : Set X} (hU : U ∈ B) :
    let q : X → Quotient (basisPatternSetoid B) := @Quotient.mk' X (basisPatternSetoid B)
    q ⁻¹' (q '' U) = U := by
  let q : X → Quotient (basisPatternSetoid B) := @Quotient.mk' X (basisPatternSetoid B)
  ext x
  constructor
  · rintro ⟨y, hyU, hyx⟩
    exact (Quotient.eq'.1 hyx U hU).1 hyU
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Lemma 5.5.6, canonical form: if a family of open sets covers `X` and every pairwise
intersection is the union of members of the family contained in it, then there exists a continuous
map whose image family has exactly the prescribed preimages and is a topological basis on the
target. Openness of the image family is derived from the basis owner. -/
theorem exists_continuousMap_with_basis_images
    {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hopen : ∀ U ∈ B, IsOpen U) (hcover : sUnion B = univ)
    (hinter : ∀ ⦃U V : Set X⦄, U ∈ B → V ∈ B →
      U ∩ V = ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U ∩ V }) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)),
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      IsTopologicalBasis (image (f : X → Y) '' B) := by
  -- Route correction: construct the target as the quotient by basis-membership patterns, then put
  -- the generated topology from the image family on that quotient.
  let R := basisPatternSetoid B
  let q : X → Quotient R := Quotient.mk'
  let 𝓑 : Set (Set (Quotient R)) := image q '' B
  -- The image family covers the quotient because every class has a representative in some `U ∈ B`.
  have hcover_𝓑 : sUnion 𝓑 = univ := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      rcases Quotient.mk'_surjective y with ⟨x, rfl⟩
      have hx : x ∈ sUnion B := by
        rw [hcover]
        trivial
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      exact mem_sUnion.2 ⟨q '' U, mem_image_of_mem _ hU, mem_image_of_mem _ hxU⟩
  -- Intersections of image-basis sets refine by pushing the source refinement through the quotient.
  have hinter_𝓑 :
      ∀ ⦃y : Quotient R⦄ ⦃U : Set (Quotient R)⦄, U ∈ 𝓑 →
        ∀ ⦃V : Set (Quotient R)⦄, V ∈ 𝓑 →
          y ∈ U ∩ V → ∃ W ∈ 𝓑, y ∈ W ∧ W ⊆ U ∩ V := by
    intro y U hU V hV hy
    rcases hU with ⟨U₀, hU₀, rfl⟩
    rcases hV with ⟨V₀, hV₀, rfl⟩
    rcases hy.1 with ⟨x, hxU₀, hxy⟩
    rcases hy.2 with ⟨z, hzV₀, hzy⟩
    have hxz : Quotient.mk' x = Quotient.mk' z := hxy.trans hzy.symm
    have hzU₀ : z ∈ U₀ := (Quotient.eq'.1 hxz U₀ hU₀).1 hxU₀
    have hzUV : z ∈ U₀ ∩ V₀ := ⟨hzU₀, hzV₀⟩
    have hzUnion : z ∈ ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U₀ ∩ V₀ } := by
      rw [← hinter hU₀ hV₀]
      exact hzUV
    rcases mem_sUnion.1 hzUnion with ⟨W, hW, hzW⟩
    refine ⟨q '' W, mem_image_of_mem _ hW.1, ⟨z, hzW, hzy⟩, ?_⟩
    intro t ht
    rcases ht with ⟨w, hwW, rfl⟩
    exact ⟨⟨w, (hW.2 hwW).1, rfl⟩, ⟨w, (hW.2 hwW).2, rfl⟩⟩
  let _ : TopologicalSpace (Quotient R) := generateFrom 𝓑
  have hBasis : IsTopologicalBasis 𝓑 := isTopologicalBasis_generateFrom 𝓑 hcover_𝓑 hinter_𝓑
  -- Continuity is checked on basis opens, whose preimages are exactly the original open sets in `B`.
  have hcontinuous : Continuous q := hBasis.continuous_iff.2 fun U hU ↦ by
    rcases hU with ⟨V, hV, rfl⟩
    have hqV : q ⁻¹' (q '' V) = V := by
      simpa [R, q] using (preimage_image_quotientMk_eq B hV)
    simpa [hqV] using (hopen V hV)
  refine ⟨Quotient R, inferInstance, ⟨q, hcontinuous⟩, ?_, hBasis⟩
  intro U hU
  simpa [R, q] using (preimage_image_quotientMk_eq B hU)

/-- Lemma 5.5.6, source-facing form: the image family in the target can be stated explicitly as
open, but this is derived from `IsTopologicalBasis`. -/
theorem exists_continuousMap_with_open_basis_images
    {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hopen : ∀ U ∈ B, IsOpen U) (hcover : sUnion B = univ)
    (hinter : ∀ ⦃U V : Set X⦄, U ∈ B → V ∈ B →
      U ∩ V = ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U ∩ V }) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)),
      (∀ U ∈ B, IsOpen (f '' U)) ∧
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      IsTopologicalBasis (image (f : X → Y) '' B) := by
  obtain ⟨Y, _, f, hpreimage, hBasis⟩ :=
    exists_continuousMap_with_basis_images B hopen hcover hinter
  refine ⟨Y, inferInstance, f, ?_, hpreimage, hBasis⟩
  intro U hU
  exact hBasis.isOpen (mem_image_of_mem _ hU)

end
