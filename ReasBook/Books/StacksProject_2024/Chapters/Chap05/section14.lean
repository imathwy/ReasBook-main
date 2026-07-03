import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Konig

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_14_1 (from Chap05) -/
/- Domain-style sampling for limits in `TopCat`:
- primary domain: categorical limits of topological spaces and the forgetful functor to types;
- inspected owner declarations:
  `TopCat.topCat_hasLimitsOfSize`,
  `TopCat.topCat_hasLimits`,
  `TopCat.forget_preservesLimitsOfSize`,
  `TopCat.forget_preservesLimits`.
- best owner abstraction: `HasLimits TopCat`.

Primitive-vs-derived split:
- primitive data: the size-level instance `TopCat.topCat_hasLimitsOfSize`, from which the global
  `HasLimits TopCat` instance is obtained;
- derived API: the exposed global instance `TopCat.topCat_hasLimits` and the companion forgetful
  preservation instance `TopCat.forget_preservesLimits`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the category of topological spaces has all limits;
- `core/canonical`: the owner instance `TopCat.topCat_hasLimits : HasLimits TopCat`;
- `bridge/view`: the forgetful-functor companion `TopCat.forget_preservesLimits`, while the
  concrete cone/topology descriptions are handled downstream by Lemmas `5.14.2` and `5.14.3`.

This item is recall-only: there is no additional source-defined data to package, so the refined
file should reuse the canonical owner instances directly rather than introduce a local alias or a
wrapper theorem.
-/

/- Lemma 5.14.1: the category of topological spaces has all limits. This is exactly the canonical
mathlib instance `TopCat.topCat_hasLimits`. -/
recall TopCat.topCat_hasLimits

/- Companion recall: the forgetful functor from topological spaces to types preserves limits. This
is exactly the canonical mathlib instance `TopCat.forget_preservesLimits`. -/
recall TopCat.forget_preservesLimits

/-! ### Lemma_5_14_2 (from Chap05) -/
universe u v w

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v u}} {C : Cone F}

/-
Domain-style sampling for cofiltered limits in `TopCat`:
- owner abstraction for the limit topology:
  `TopCat.isTopologicalBasis_cofiltered_limit`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`,
  `IsCompact.elim_finite_subcover`

Source/core/bridge triage:
- `source-facing`: the Stacks statements that opens in a cofiltered limit are unions of stagewise
  pullbacks, and that quasi-compact opens descend to a single stage;
- `core/canonical`: the basis owner
  `TopCat.isTopologicalBasis_cofiltered_limit`, specialized here to the basis of all open subsets
  on each stage;
- `bridge/view`: the resulting stagewise union and single-stage pullback descriptions.

Primitive data is only the canonical basis on the limiting cone point. The displayed union and
single-stage descent statements are derived API from that owner and from compactness, so the file
should reuse the owner basis directly rather than introducing a parallel public wrapper.
-/

private def projectionPreimageBasis (C : Cone F) : Set (Set C.pt) :=
  {W : Set C.pt | ∃ (j : J) (U : Opens (F.obj j)), W = C.π.app j ⁻¹' (U : Set (F.obj j))}

private theorem isTopologicalBasis_projectionPreimageBasis (hC : IsLimit C) :
    IsTopologicalBasis (projectionPreimageBasis C) := by
  rw [show projectionPreimageBasis C =
      {W : Set C.pt | ∃ (j : J) (U : Set (F.obj j)), IsOpen U ∧ W = C.π.app j ⁻¹' U} by
      ext W
      constructor
      · rintro ⟨j, U, rfl⟩
        exact ⟨j, (U : Set (F.obj j)), U.isOpen, rfl⟩
      · rintro ⟨j, U, hU, rfl⟩
        exact ⟨j, ⟨U, hU⟩, rfl⟩]
  simpa using
    (TopCat.isTopologicalBasis_cofiltered_limit.{u, v, w} F C hC
      (fun j ↦ {U : Set (F.obj j) | IsOpen U})
      (fun _ ↦ isTopologicalBasis_opens)
      (fun _ ↦ isOpen_univ)
      (fun _ _ _ hU₁ hU₂ ↦ hU₁.inter hU₂)
      (fun _ _ f _ hU ↦ hU.preimage (F.map f).hom.continuous))

-- Proof sketch: apply `TopCat.isTopologicalBasis_cofiltered_limit` with the basis of all open sets
-- on each `F.obj j`; then use `IsTopologicalBasis.open_eq_sUnion` to write an open subset of the
-- limit as a union of basic opens, each of which is the preimage of an open subset from one stage.
/-- Lemma 5.14.2 (1): every open subset of a cofiltered limit of topological spaces is a union of
preimages of open subsets from the spaces in the diagram. -/
theorem open_eq_iUnion_preimage_of_isLimit (hC : IsLimit C) (W : Opens C.pt) :
    ∃ U : ∀ j, Opens (F.obj j), (W : Set C.pt) = ⋃ j, C.π.app j ⁻¹' (U j : Set (F.obj j)) := by
  let hBasis := isTopologicalBasis_projectionPreimageBasis hC
  let U : ∀ j, Opens (F.obj j) := fun j ↦
    ⟨⋃₀ {V : Set (F.obj j) | IsOpen V ∧ C.π.app j ⁻¹' V ⊆ (W : Set C.pt)},
      isOpen_sUnion fun V hV ↦ hV.1⟩
  refine ⟨U, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨B, hB, hxB, hBW⟩ := hBasis.exists_subset_of_mem_open hx W.isOpen
      rcases hB with ⟨j, V, rfl⟩
      refine mem_iUnion.2 ⟨j, ?_⟩
      exact mem_preimage.2 <| mem_sUnion.2 ⟨V, ⟨V.isOpen, hBW⟩, mem_preimage.1 hxB⟩
    · intro hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨j, hx⟩
      rcases mem_sUnion.1 (mem_preimage.1 hx) with ⟨V, hV, hxV⟩
      exact hV.2 (show x ∈ C.π.app j ⁻¹' V from hxV)

-- Proof sketch: use the canonical preimage basis on the limit together with
-- `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open` to write the quasi-compact open as a
-- finite union of projection-pullback basic opens; then use cofilteredness to dominate the
-- finitely many stages and pull everything back to a single open subset upstairs.
/-- Lemma 5.14.2 (2): every quasi-compact open subset of a cofiltered limit of topological spaces
is the preimage of an open subset from a single space in the diagram. -/
theorem compact_open_eq_preimage_of_isLimit (hC : IsLimit C) (W : CompactOpens C.pt) :
    ∃ (j : J) (U : Opens (F.obj j)), (W : Set C.pt) = C.π.app j ⁻¹' (U : Set (F.obj j)) := by
  classical
  have hBasis : IsTopologicalBasis (projectionPreimageBasis C) :=
    isTopologicalBasis_projectionPreimageBasis hC
  obtain ⟨s, hsW⟩ :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open
      (projectionPreimageBasis C) hBasis
      (W : Set C.pt) W.isCompact W.isOpen
  choose j U hU_eq using fun V : s ↦ V.1.2
  let G : Finset J := Finset.univ.image j
  obtain ⟨j₀, hj₀⟩ := IsCofiltered.inf_objs_exists G
  have hj : ∀ V : s, j V ∈ G := fun V ↦ Finset.mem_image.mpr ⟨V, Finset.mem_univ _, rfl⟩
  let g : ∀ V : s, j₀ ⟶ j V := fun V ↦ (hj₀ (hj V)).some
  let U₀ : Opens (F.obj j₀) := ⨆ V : s, (Opens.map (F.map (g V))).obj (U V)
  have hπ {i j : J} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  refine ⟨j₀, U₀, ?_⟩
  ext x
  constructor
  · intro hx
    rw [hsW] at hx
    rcases mem_sUnion.1 hx with ⟨V, hVs, hxV⟩
    rcases hVs with ⟨V', hV's, rfl⟩
    let V'' : s := ⟨V', hV's⟩
    rw [hU_eq V''] at hxV
    refine mem_preimage.2 <| Opens.mem_iSup.2 ⟨V'', ?_⟩
    change F.map (g V'') (C.π.app j₀ x) ∈ U V''
    rw [← hπ (g V'') x]
    exact mem_preimage.1 hxV
  · intro hx
    have hxU₀ : C.π.app j₀ x ∈ U₀ := mem_preimage.1 hx
    rw [Opens.mem_iSup] at hxU₀
    rcases hxU₀ with ⟨V, hxV⟩
    rw [hsW]
    refine mem_sUnion.2 ⟨V.1.1, ⟨V.1, V.2, rfl⟩, ?_⟩
    rw [hU_eq V]
    refine mem_preimage.2 ?_
    change F.map (g V) (C.π.app j₀ x) ∈ U V at hxV
    exact (hπ (g V) x).symm ▸ hxV

/-! ### Lemma_5_14_3 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u w

namespace TopCat

section

variable {J : Type v} [Category.{w} J]
variable {F : J ⥤ TopCat.{max v u}} (c : Cone F)
variable [IsCofiltered J]

/-
Domain-style sampling for cofiltered limits in `TopCat`:
- primary domain: categorical limits of topological spaces built from set-level limits and induced
  topologies;
- inspected owner declarations:
  `TopCat.nonempty_isLimit_iff_eq_induced`,
  `TopCat.isTopologicalBasis_cofiltered_limit`,
  `TopCat.isLimitConeOfForget`.
- best owner abstraction: `IsLimit c` in `TopCat`, with the induced-topology criterion as the
  canonical bridge from the underlying limit in `Type`.

Primitive-vs-derived split:
- primitive data: the set-level limit cone together with the equality identifying the topology on
  `c.pt` with the canonical infimum topology;
- derived API: the resulting `TopCat` limit proof and the preimage-basis presentation used to prove
  that topology equality.

Source/core/bridge triage:
- `source-facing`: Lemma 5.14.3, asserting that a cone in `TopCat` is limiting once the underlying
  cone of sets is limiting and the pulled-back opens form a basis;
- `core/canonical`: `TopCat.nonempty_isLimit_iff_eq_induced`;
- `bridge/view`: `TopCat.isTopologicalBasis_cofiltered_limit`, specialized to the basis of all
  open subsets upstairs.
-/

private def preimageBasis (c : Cone F) : Set (Set c.pt) :=
  {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}

private lemma topology_eq_iInf_induced_of_preimage_basis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis (preimageBasis c)) :
    c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  let c' : Cone F := TopCat.coneOfConeForget ((forget TopCat).mapCone c)
  let T : ∀ j, Set (Set (F.obj j)) := fun j ↦ {V : Set (F.obj j) | IsOpen V}
  have h_basis' :=
    TopCat.isTopologicalBasis_cofiltered_limit F c'
      (TopCat.isLimitConeOfForget ((forget TopCat).mapCone c) h_limit)
      T (fun _ ↦ TopologicalSpace.isTopologicalBasis_opens)
      (fun i ↦ by
        change Set.univ ∈ T i
        simp [T])
      (fun i U₁ U₂ hU₁ hU₂ ↦ by
        simpa [T] using hU₁.inter hU₂)
      (fun i j f V hV ↦ by
        simpa [T] using hV.preimage (F.map f).hom.continuous)
  have h_eq₁ : c.pt.str = TopologicalSpace.generateFrom (preimageBasis c) := h_basis.eq_generateFrom
  have h_eq₂ :
      c'.pt.str = TopologicalSpace.generateFrom (preimageBasis c') :=
    h_basis'.eq_generateFrom
  have hB : preimageBasis c = preimageBasis c' := by
    ext U
    constructor <;> rintro ⟨j, V, hV, rfl⟩ <;> exact ⟨j, V, hV, rfl⟩
  have h_eq : c.pt.str = c'.pt.str := by
    rw [h_eq₁, h_eq₂, hB]
    rfl
  simpa [c', TopCat.topologicalSpaceConePtOfConeForget] using h_eq

/-- Lemma 5.14.3: if the underlying cone of sets is limiting and the pulled-back open subsets from
the cone projections form a topological basis on the cone point, then the cone is limiting in
`TopCat`. The cofiltered hypothesis is retained to match the Stacks Project statement.

The canonical `TopCat` limit cone on the underlying set-level limit is
`TopCat.coneOfConeForget ((forget TopCat).mapCone c)`. The basis hypothesis identifies its
induced topology with the given topology on `c.pt`, so the standard `TopCat` limit criterion
applies. -/
noncomputable def isLimit_of_underlying_limit_of_preimage_basis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}) :
    IsLimit c := by
  classical
  exact Classical.choice <|
    (TopCat.nonempty_isLimit_iff_eq_induced c h_limit).2
      (topology_eq_iInf_induced_of_preimage_basis c h_limit h_basis)

-- Proof sketch: apply the `fac` field of the limit proof produced by
-- `isLimit_of_underlying_limit_of_preimage_basis`.
/-- The limiting cone supplied by the preimage-basis criterion has the expected projection
factorization property. -/
theorem isLimit_of_underlying_limit_of_preimage_basis_fac
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V})
    (s : Cone F) (j : J) :
    (isLimit_of_underlying_limit_of_preimage_basis c h_limit h_basis).lift s ≫ c.π.app j =
      s.π.app j := by
  -- The constructed limiting cone already carries the universal factorization identities.
  exact (isLimit_of_underlying_limit_of_preimage_basis c h_limit h_basis).fac s j

end

end TopCat

/-! ### Theorem_5_14_4_Tychonov (from Chap05) -/
universe u v

section

variable {ι : Type u} {X : ι → Type v}
variable [∀ i, TopologicalSpace (X i)]

/- Domain-style sampling for Tychonoff compactness in topological spaces:
- whole-space owner: `CompactSpace`
- product-space whole-space instance: `Pi.compactSpace`
- set-level product compactness theorem: `isCompact_univ_pi`
- chapter canonicalization of quasi-compact spaces: Definition 5.12.1 identifies them with
  `CompactSpace`

Layer triage:
- `source-facing`: quasi-compactness of the product space
- `core/canonical`: `CompactSpace`
- `bridge/view`: `isCompact_univ_pi`, whose whole-space specialization gives `Pi.compactSpace`

Primitive data here is only the ambient product topology together with compactness of the factors.
No local wrapper or parallel Tychonoff declaration should be kept, because the owner instance
already has the exact source-facing meaning.
-/

/- Theorem 5.14.4 (Tychonov): if each factor `X i` is quasi-compact, then the product space
`∀ i, X i` is quasi-compact. Via Definition 5.12.1, quasi-compactness is `CompactSpace`, so this
is exactly the canonical product-space compactness instance `Pi.compactSpace`. -/
recall Pi.compactSpace

/- Companion recall: mathlib also provides the set-level Tychonoff theorem `isCompact_univ_pi`,
from which the whole-space instance `Pi.compactSpace` is derived. -/
recall isCompact_univ_pi

end

/-! ### Lemma_5_14_5 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits
open CompHausLike

universe u v

section

variable {J : Type v} [Category.{v} J]
variable (F : J ⥤ TopCat.{max u v})

/- Domain-style sampling for compact Hausdorff limits:
- inspected owner-level declarations:
  `CompHaus.limitCone`,
  `CompHaus.limitConeIsLimit`,
  `compHausToTop.createsLimits`,
  `CategoryTheory.Limits.isLimitOfPreserves`
- `source-facing`: compactness of the `TopCat` limit of a diagram with compact Hausdorff objects
- `core/canonical`: the compact-Hausdorff limit owner `CompHaus.limitCone`
- `bridge/view`: the internal lift of the original `TopCat` diagram to `CompHaus`, then the
  forgetful image of `CompHaus.limitCone` together with `isLimitOfPreserves compHausToTop`
  and the comparison homeomorphism from that owner cone point to `limit F`

Primitive data is only the original `TopCat` diagram together with the objectwise
`CompactSpace`/`T2Space` instances. The compactness argument itself already belongs to the owner
`CompHaus.limitCone`, so the local proof should only build the minimal bridge into that owner and
transport the resulting instance back to `TopCat.limit F`.
-/

/- Companion recall: `CompHaus.limitCone` is the canonical compact-Hausdorff limit model for a
diagram whose objects are already compact Hausdorff. -/
recall CompHaus.limitCone

-- Proof sketch: pass to the canonical `CompHaus`-valued diagram provided by the objectwise
-- compact Hausdorff hypotheses. The owner limit is `CompHaus.limitCone`; map it back to `TopCat`
-- via `compHausToTop`, use `isLimitOfPreserves` to see that this mapped cone is limiting for `F`,
-- and transport compactness across the canonical isomorphism to `limit F`.
/-- Lemma 5.14.5: if every space in a diagram of topological spaces is quasi-compact and
Hausdorff, then the limit space is quasi-compact. -/
theorem compactSpace_limit_of_compactSpace_t2Space
    [∀ j, CompactSpace ↥(F.obj j)] [∀ j, T2Space ↥(F.obj j)] :
    CompactSpace ↥(limit F) := by
  let G : J ⥤ CompHaus.{max u v} := {
    obj := fun j ↦ CompHaus.of (F.obj j)
    map := fun f ↦ ofHom (fun _ ↦ True) (F.map f).hom
    map_id := by
      intro j
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (F.map_id j)
    map_comp := by
      intro i j k f g
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (F.map_comp f g) }
  let hG : IsLimit (compHausToTop.mapCone (CompHaus.limitCone G)) :=
    by simpa using isLimitOfPreserves compHausToTop (CompHaus.limitConeIsLimit G)
  have : CompactSpace ↥(compHausToTop.mapCone (CompHaus.limitCone G)).pt := by
    change CompactSpace ↥(CompHaus.limitCone G).pt
    infer_instance
  simpa [G] using
    (TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso hG (limit.isLimit (G ⋙ compHausToTop)))).compactSpace

instance
    [∀ j, CompactSpace ↥(F.obj j)] [∀ j, T2Space ↥(F.obj j)] :
    CompactSpace ↥(limit F) :=
  compactSpace_limit_of_compactSpace_t2Space F

end

/-! ### Lemma_5_14_6 (from Chap05) -/
/- Domain-style sampling for cofiltered limits of compact Hausdorff spaces in `TopCat`:
- primary domain: categorical limits in `TopCat` and nonemptiness of cofiltered limits of compact
  Hausdorff spaces;
- inspected owner declarations:
  `TopCat.topCat_hasLimits`,
  `TopCat.limitCone`,
  `TopCat.limitConeIsLimit`,
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- best owner abstraction: the chosen limit cone `TopCat.limitCone F`, with nonemptiness expressed
  by the canonical theorem `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`.

Primitive-vs-derived split:
- primitive data: the diagram `F : J ⥤ TopCat`, the chosen limit cone `TopCat.limitCone F`, and
  the typeclass assumptions `[IsCofilteredOrEmpty J]`, `[∀ j, Nonempty (F.obj j)]`,
  `[∀ j, CompactSpace (F.obj j)]`, `[∀ j, T2Space (F.obj j)]`;
- derived API: the theorem that the cone point `(TopCat.limitCone F).pt` is nonempty.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a cofiltered limit of nonempty quasi-compact
  Hausdorff spaces is nonempty;
- `core/canonical`: the theorem
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- `bridge/view`: downstream specializations such as
  `CategoryTheory.nonempty_sections_of_finite_cofiltered_system.init`.

This item is recall-only: the source introduces no new object beyond the canonical `TopCat`
limit cone, so refining the file means reusing the owner theorem directly rather than packaging a
parallel local statement.
-/

/- Lemma 5.14.6: a cofiltered limit of nonempty quasi-compact Hausdorff spaces is nonempty.
This is exactly the canonical mathlib theorem
`TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`, where quasi-compact Hausdorff is
expressed by the typeclasses `CompactSpace` and `T2Space`. -/
recall TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
