import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Irreducible
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_8_1 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Definition 5.8.1:
- primary domain: irreducibility in point-set topology
- owner abstractions:
  `IrreducibleSpace` for irreducible spaces,
  `irreducibleComponents` for irreducible components
- same-domain declarations inspected:
  `irreducibleSpace_def`,
  `irreducibleComponents`,
  `isClosed_of_mem_irreducibleComponents`,
  `irreducibleComponents_eq_maximals_closed`

Layer triage:
- `source-facing`: the Stacks notions of an irreducible topological space and its irreducible
  components
- `core/canonical`: `IrreducibleSpace` and `irreducibleComponents X`
- `bridge/view`: `irreducibleSpace_def` and `irreducibleComponents_eq_maximals_closed`, which
  expose the textbook-form predicates without introducing a second owner

Primitive data lives at the owner level. The nonempty-univ characterization and the maximal closed
irreducible characterization are derived API and should remain companion recalls rather than
parallel local definitions.
-/

/- Canonical recall: the Stacks notion that a topological space is irreducible is the canonical
mathlib class `IrreducibleSpace`. -/
recall IrreducibleSpace

/- Companion recall: the textbook-form set-level characterization of an irreducible space is the
canonical theorem `irreducibleSpace_def`. -/
recall irreducibleSpace_def

/-
Definition 5.8.1 (2): the canonical mathlib object for irreducible components is the set
`irreducibleComponents X` of maximal irreducible subsets of `X`.
-/
recall irreducibleComponents

/- Companion recall: the source-facing maximal closed irreducible description of irreducible
components is already the canonical theorem `irreducibleComponents_eq_maximals_closed`. -/
recall irreducibleComponents_eq_maximals_closed

/-! ### Lemma_5_8_2 (from Chap05) -/
/- 
Domain-style sampling for irreducible subsets in point-set topology:
- best owner abstraction: the predicate `IsIrreducible` and its owner-level API in
  `Mathlib/Topology/Irreducible.lean`
- same-domain declarations inspected:
  `IsIrreducible.image`,
  `IsIrreducible.closure`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `irreducibleComponent_mem_irreducibleComponents`

Layer triage:
- `source-facing`: irreducibility of a subset and its behavior under continuous maps
- `core/canonical`: the existing mathlib irreducibility API
- `bridge/view`: irreducible components as canonical maximal irreducible supersets

Primitive data here is just the owner predicate `IsIrreducible`; there is no additional local data
or wrapper structure to package. Since Lemma 5.8.2 is exactly the owner theorem for images, the
correct refinement is a direct canonical recall rather than a parallel local theorem shell.
-/

/- Lemma 5.8.2: the image of an irreducible subset under a continuous map is irreducible.
This is exactly the canonical theorem `IsIrreducible.image`. -/
recall IsIrreducible.image

/-! ### Lemma_5_8_3 (from Chap05) -/
/-
Domain-style sampling for irreducible subsets and irreducible components:
- owner abstraction: `irreducibleComponents X` and `irreducibleComponent x`, with supporting
  owner-level lemmas in `Mathlib/Topology/Irreducible.lean`
- same-domain declarations inspected:
  `IsIrreducible.closure`,
  `isClosed_of_mem_irreducibleComponents`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`

Layer triage:
- `source-facing`: closure of irreducible sets, irreducible components, and the canonical
  irreducible component through a point
- `core/canonical`: the existing topological irreducibility API in mathlib
- `bridge/view`: `irreducibleComponent_mem_irreducibleComponents` and
  `sUnion_irreducibleComponents`

Primitive data already belongs to the owner objects `irreducibleComponents` and
`irreducibleComponent`. The statements in this file are derived owner-level API, so the correct
refinement is direct canonical recall rather than introducing any local wrapper or parallel alias.
-/

universe u

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.8.3 (1): the closure of an irreducible subset of `X` is irreducible. -/
recall IsIrreducible.closure

/- Lemma 5.8.3 (2): every irreducible component of `X` is closed. -/
recall isClosed_of_mem_irreducibleComponents

/- Lemma 5.8.3 (3): every irreducible subset of `X` is contained in an irreducible component of
`X`. -/
recall exists_mem_irreducibleComponents_subset_of_isIrreducible

/-
Lemma 5.8.3 (4): every point `x` of `X` lies in the canonical irreducible component
`irreducibleComponent x` through `x`.
-/
recall mem_irreducibleComponent

/- Companion recall: the canonical set `irreducibleComponent x` is indeed an irreducible
component of `X`. -/
recall irreducibleComponent_mem_irreducibleComponents

/-
Companion reformulation of Lemma 5.8.3 (4): `X` is the union of its irreducible
components.
-/
recall sUnion_irreducibleComponents

/-! ### Lemma_5_8_4 (from Chap05) -/
universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.4:
- primary domain: irreducible components of a topological space
- inspected owner declarations:
  `irreducibleComponents`,
  `irreducibleComponents_eq_maximals_closed`,
  `isIrreducible_iff_sUnion_isClosed`,
  `mem_of_subset_sUnion_irreducibleComponents`
- best owner abstraction: `irreducibleComponents X` is the core/canonical owner; the present lemma
  is a `bridge/view` statement identifying a finite irredundant closed irreducible cover with that
  canonical set of components
- primitive-vs-derived split: the primitive data here are the finite family `S`, the cover
  equality, and the closedness/irreducibility/irredundancy hypotheses on its members; membership in
  `irreducibleComponents X` is derived from the owner maximality and finite-cover membership API
  rather than from a local duplicate notion of component
-/

/-- Helper for Lemma 5.8.4: an irreducible component in a finite closed irreducible cover must be
one of the covering members. -/
lemma irreducible_component_mem_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    {Y : Set X} (hY : Y ∈ irreducibleComponents X) :
    Y ∈ S := by
  classical
  -- Rewrite component membership into the maximal closed-irreducible formulation.
  rw [irreducibleComponents_eq_maximals_closed] at hY
  change Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Y at hY
  -- Irreducibility of `Y` forces it to lie in one closed member of the finite cover.
  obtain ⟨W, hW, hYW⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hY.1.2 hS.toFinset
      (fun W hW ↦ hclosed W (hS.mem_toFinset.mp hW))
      (by simp [hcover])
  have hWS : W ∈ S := hS.mem_toFinset.mp hW
  -- Maximality of the irreducible component upgrades inclusion to equality.
  have hWY : W ⊆ Y := hY.2 ⟨hclosed W hWS, hirr W hWS⟩ hYW
  have hYW_eq : Y = W := Subset.antisymm hYW hWY
  simpa [hYW_eq] using hWS

/-- Helper for Lemma 5.8.4: irredundancy forces one cover member contained in another to be equal
to it. -/
lemma subset_eq_of_irredundant_members
    (S : Set (Set X))
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z}))
    {Z W : Set X} (hZ : Z ∈ S) (hW : W ∈ S) (hZW : Z ⊆ W) :
    Z = W := by
  -- If `W ≠ Z`, then every point of `Z` already lies in the union of the other members.
  by_contra hne
  have hZsubset : Z ⊆ ⋃₀ (S \ {Z}) := by
    intro x hx
    refine mem_sUnion.2 ?_
    exact ⟨W, ⟨hW, by simpa [Set.mem_singleton_iff, eq_comm] using hne⟩, hZW hx⟩
  exact hirredundant Z hZ hZsubset

/-- Helper for Lemma 5.8.4: each member of the finite irredundant closed irreducible cover is an
irreducible component. -/
lemma cover_member_mem_irreducibleComponents
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z}))
    {Z : Set X} (hZ : Z ∈ S) :
    Z ∈ irreducibleComponents X := by
  -- Place `Z` inside an irreducible component, following Lemma 5.8.3's route.
  obtain ⟨Y, hY, hZY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible Z (hirr Z hZ)
  have hYS : Y ∈ S := irreducible_component_mem_cover S hS hcover hclosed hirr hY
  -- Irredundancy identifies that component with the original cover member.
  have hZY_eq : Z = Y := subset_eq_of_irredundant_members S hirredundant hZ hYS hZY
  simpa [hZY_eq] using hY

/-- Lemma 5.8.4: if a topological space is covered by finitely many irreducible closed subsets and
none of them is contained in the union of the others, then the irreducible components are exactly
those subsets. A finite family of closed irreducible subsets is represented canonically by a
finite set `S : Set (Set X)`, and the conclusion is equality with `irreducibleComponents X`. -/
theorem irreducibleComponents_eq_of_finite_irreducible_closed_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z})) :
    irreducibleComponents X = S := by
  classical
  -- Follow the source proof: first show every component belongs to the cover.
  refine Set.Subset.antisymm ?_ ?_
  · intro Y hY
    exact irreducible_component_mem_cover S hS hcover hclosed hirr hY
  · intro Z hZ
    -- Then show each cover member is itself a component by placing it inside one.
    exact cover_member_mem_irreducibleComponents S hS hcover hclosed hirr hirredundant hZ

/-! ### Lemma_5_8_5 (from Chap05) -/
open Set

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for Lemma 5.8.5:
- primary domain: irreducible components under continuous surjective maps
- inspected owner declarations:
  `irreducibleComponents`,
  `irreducibleComponent`,
  `sUnion_irreducibleComponents`,
  `isIrreducible_iff_sUnion_isClosed`
- best owner abstraction: `irreducibleComponents X` is the core/canonical owner; the Stacks lemma
  is a `bridge/view` cardinality consequence of the fact that, when `X` has finitely many
  irreducible components, every irreducible component of `Y` is the closure of the image of some
  irreducible component of `X`
- primitive-vs-derived split: the primitive data are the continuous surjection `f` and the
  canonical owner sets `irreducibleComponents X` and `irreducibleComponents Y`; the finite-cardinal
  inequality is derived from the inclusion of `irreducibleComponents Y` into the finite closure-image
  family `{closure (f '' Z) | Z ∈ irreducibleComponents X}`, not from a separate local wrapper or
  chosen embedding of components
-/

/-- For a continuous surjection with finitely many irreducible components upstairs, every
irreducible component downstairs is the closure of the image of some irreducible component
upstairs. -/
theorem exists_irreducibleComponent_closure_image_eq_of_surjective_continuous
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f)
    (hXfin : (irreducibleComponents X).Finite) (W : irreducibleComponents Y) :
    ∃ Z : irreducibleComponents X, closure (f '' (Z : Set X)) = (W : Set Y) := by
  classical
  let S : Set (Set Y) := Set.range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  letI : Finite (irreducibleComponents X) := hXfin.to_subtype
  have hS : S.Finite := by
    simpa [S] using
      Set.finite_range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  have hcover : (W : Set Y) ⊆ ⋃₀ S := by
    intro y hy
    obtain ⟨x, rfl⟩ := hf_surj y
    refine mem_sUnion.2 ⟨closure (f '' irreducibleComponent x), ?_, ?_⟩
    · exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, rfl⟩
    · simpa using
        (subset_closure ⟨x, mem_irreducibleComponent, rfl⟩ :
          f x ∈ closure (f '' irreducibleComponent x))
  obtain ⟨Z, hZS, hWZ⟩ := isIrreducible_iff_sUnion_isClosed.mp W.2.1 hS.toFinset
    (fun Z hZ ↦ by
      rcases hS.mem_toFinset.mp hZ with ⟨Z', -, rfl⟩
      simp)
    (hS.coe_toFinset.symm ▸ hcover)
  rcases hS.mem_toFinset.mp hZS with ⟨Z, -, rfl⟩
  exact ⟨Z, Set.Subset.antisymm (W.2.2 ((Z.2.1.image f hf_cont.continuousOn).closure) hWZ) hWZ⟩

/-- Lemma 5.8.5: a surjective continuous map sends a space with exactly `n` irreducible
components to a space with at most `n` irreducible components. -/
theorem irreducibleComponents_encard_le_of_surjective_continuous
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f) {n : ℕ}
    (hX : (irreducibleComponents X).encard = n) :
    (irreducibleComponents Y).encard ≤ n := by
  classical
  let S : Set (Set Y) := Set.range (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
  have hXfin : (irreducibleComponents X).Finite := Set.finite_of_encard_eq_coe hX
  have hYS : irreducibleComponents Y ⊆ S := by
    intro W hW
    obtain ⟨Z, hZ⟩ :=
      exists_irreducibleComponent_closure_image_eq_of_surjective_continuous hf_surj hf_cont hXfin
        ⟨W, hW⟩
    have hZS : closure (f '' (Z : Set X)) ∈ S := by
      exact ⟨Z, by simp⟩
    simpa [hZ] using hZS
  have hS : S.encard ≤ (irreducibleComponents X).encard := by
    simpa [S] using
      (Set.encard_image_le (fun Z : irreducibleComponents X ↦ closure (f '' (Z : Set X)))
        (univ : Set (irreducibleComponents X)))
  calc
    (irreducibleComponents Y).encard ≤ S.encard := Set.encard_le_encard hYS
    _ ≤ (irreducibleComponents X).encard := hS
    _ = n := hX

end

/-! ### Definition_5_8_6 (from Chap05) -/
universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for generic points and sober spaces:
- primary domain: generic points, `T₀` separation, quasi-sobriety, and sobriety in topology;
- sampled canonical declarations:
  `IsGenericPoint`,
  `isGenericPoint_def`,
  `QuasiSober`,
  `quasiSober_iff`,
  `irreducibleSetEquivPoints`,
  `TopologicalSpace.IrreducibleCloseds`,
  `t0Space_iff_exists_isOpen_xor'_mem`;
- best owner abstraction: `IsGenericPoint` owns generic points, `QuasiSober` owns quasi-sobriety,
  and `irreducibleSetEquivPoints` is the canonical sober-space bridge on
  `IrreducibleCloseds X`; the chapter-level owner form of sobriety is the pair
  `[T0Space X] [QuasiSober X]`;
- primitive-vs-derived split: the primitive owner data is the field `QuasiSober.sober`; the
  bundled `IrreducibleCloseds` restatements, `irreducibleSetEquivPoints`, and the
  unique-generic-point reformulations are derived bridge API.

Layer triage:
- `source-facing`: the Stacks definitions phrased using generic points of irreducible closed sets;
- `core/canonical`: `IsGenericPoint`, `T0Space`, `QuasiSober`, and `IrreducibleCloseds`;
- `bridge/view`: the bundled `IrreducibleCloseds` companion theorems and the sober
  unique-generic-point characterization.
-/

/- Canonical recall: for an irreducible closed subset `Z` of `X`, a generic point is
expressed by the canonical predicate `IsGenericPoint`. -/
recall IsGenericPoint

/- Companion recall: the defining equation for a generic point is the canonical theorem
`isGenericPoint_def`. -/
recall isGenericPoint_def

/- Canonical recall: the Stacks notion of a Kolmogorov space is the canonical separation axiom
`T0Space`. -/
recall T0Space

-- Proof sketch: translate the open-set formulation of `T0Space` into the equivalent closed-set
-- separation statement by taking complements, and conversely recover the open-set separation of
-- two distinct points from the complement of a closed separator.
/-- Definition 5.8.6 (1): a topological space is Kolmogorov if any two distinct points are
separated by a closed subset containing exactly one of them. -/
theorem t0Space_iff_forall_ne_exists_closed_separating :
    T0Space X ↔
      ∀ ⦃x x' : X⦄ (_ : x ≠ x'),
        ∃ Z : Set X, IsClosed Z ∧ Xor' (x ∈ Z) (x' ∈ Z) := by
  constructor
  · intro hX x x' hxx'
    obtain ⟨U, hU, hxor⟩ := (t0Space_iff_exists_isOpen_xor'_mem X).1 hX hxx'
    refine ⟨Uᶜ, hU.isClosed_compl, ?_⟩
    simpa [Xor', and_comm, and_left_comm, and_assoc, or_comm, not_not] using hxor
  · intro hX
    rw [t0Space_iff_exists_isOpen_xor'_mem]
    intro x x' hxx'
    obtain ⟨Z, hZ, hxor⟩ := hX hxx'
    refine ⟨Zᶜ, hZ.isOpen_compl, ?_⟩
    simpa [Xor', and_comm, and_left_comm, and_assoc, or_comm, not_not] using hxor

/- Canonical recall: the Stacks notion of a quasi-sober space is the canonical mathlib class
`QuasiSober`. -/
recall QuasiSober

/- Companion recall: the canonical owner theorem `quasiSober_iff` unpacks quasi-sobriety on raw
irreducible closed subsets. -/
recall quasiSober_iff

-- Proof sketch: one direction unwraps `QuasiSober.sober` on the carrier of an
-- `IrreducibleCloseds X`; the converse repackages the irreducible and closed hypotheses into an
-- element of `IrreducibleCloseds X`.
/-- Companion bridge for Definition 5.8.6 (3), restated on bundled irreducible closed subsets. -/
theorem quasiSober_iff_forall_irreducibleCloseds_exists_genericPoint :
    QuasiSober X ↔
      ∀ Z : IrreducibleCloseds X, ∃ ξ : X, IsGenericPoint ξ (Z : Set X) := by
  rw [quasiSober_iff X]
  constructor
  · intro hX Z
    exact hX Z.isIrreducible Z.isClosed
  · intro hX S hS hSclosed
    simpa using hX ⟨S, hS, hSclosed⟩

/-
Canonical recall: the Stacks notion of a sober space is expressed canonically by the pair of
typeclasses `[T0Space X] [QuasiSober X]`. The source-facing unique-generic-point formulation
remains as the companion theorem below.
-/
#check (T0Space X ∧ QuasiSober X)

/- Companion recall: in a sober space, the canonical bundled bridge identifying irreducible closed
subsets with points is `irreducibleSetEquivPoints`. -/
recall irreducibleSetEquivPoints

-- Proof sketch: the forward implication combines the two canonical sober ingredients, namely
-- quasi-sobriety and the `T₀` uniqueness of generic points. Conversely, existence of generic
-- points gives `QuasiSober`, and uniqueness recovers the `T₀` condition from singleton closures.
/-- Definition 5.8.6 (2): a topological space is sober if every irreducible closed subset has a
unique generic point. -/
theorem sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint :
    (T0Space X ∧ QuasiSober X) ↔
      ∀ Z : IrreducibleCloseds X, ∃! ξ : X, IsGenericPoint ξ (Z : Set X) := by
  constructor
  · intro hX
    letI : T0Space X := hX.1
    letI : QuasiSober X := hX.2
    intro Z
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
    exact ⟨ξ, hξ, fun η hη ↦ IsGenericPoint.eq hη hξ⟩
  · intro hX
    have hT0 : T0Space X := by
      rw [t0Space_iff_inseparable]
      intro x y hxy
      let Z : IrreducibleCloseds X :=
        ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
      obtain ⟨ξ, hξ, huniq⟩ := hX Z
      have hx : IsGenericPoint x (Z : Set X) := by
        simpa [Z] using (isGenericPoint_closure : IsGenericPoint x (closure ({x} : Set X)))
      have hy : IsGenericPoint y (Z : Set X) := by
        simpa [Z, isGenericPoint_def] using (inseparable_iff_closure_eq.mp hxy).symm
      exact (huniq x hx).trans (huniq y hy).symm
    have hQuasiSober : QuasiSober X := by
      rw [quasiSober_iff X]
      intro S hS hSclosed
      obtain ⟨ξ, hξ, _⟩ := hX ⟨S, hS, hSclosed⟩
      exact ⟨ξ, hξ⟩
    exact ⟨hT0, hQuasiSober⟩

/-! ### Lemma_5_8_7 (from Chap05) -/
open Set Topology

universe u

section

variable {X : Type u} [TopologicalSpace X] {Y : Set X}

/- Domain-style sampling for locally closed subspaces in sober topology:
- primary domain: separation and sobriety properties of subtype spaces
- sampled canonical declarations:
  `Subtype.t0Space`
  `IsLocallyClosed.isOpen_preimage_val_closure`
  `Topology.IsClosedEmbedding.quasiSober`
  `Topology.IsOpenEmbedding.quasiSober`

Layer triage:
- `source-facing`: Lemma 5.8.7, asserting that locally closed subspaces inherit Kolmogorov,
  quasi-sober, and sober structure
- `core/canonical`: `T0Space` and `QuasiSober`
- `bridge/view`: a locally closed subset as an open subspace of its closure

Primitive data are just the subset `Y` and the proof `hY : IsLocallyClosed Y`. The induced
`T0Space` and `QuasiSober` structures are derived from the owner abstractions above, so this file
should expose bridge theorems on `IsLocallyClosed`, not parallel wrapper APIs around subtype
spaces.
-/

/- Every subspace of a Kolmogorov space is Kolmogorov. This is the canonical
subtype instance `Subtype.t0Space`. -/
recall Subtype.t0Space

/-- Lemma 5.8.7 (1): a locally closed subspace of a quasi-sober space is quasi-sober. -/
-- Proof sketch: a locally closed subset is open in its closure. The closure subtype is
-- quasi-sober because it is a closed subspace of `X`, and the inclusion `Y ↪ closure Y`
-- is an open embedding, so `Y` is quasi-sober.
protected theorem IsLocallyClosed.quasiSober
    [QuasiSober X] (hY : IsLocallyClosed Y) : QuasiSober Y := by
  letI : QuasiSober (closure Y) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  exact (IsOpenEmbedding.inclusion (subset_closure : Y ⊆ closure Y)
    hY.isOpen_preimage_val_closure).quasiSober

/-- Lemma 5.8.7 (2): a locally closed subspace of a sober space is sober, expressed in the
canonical owner form `T0Space ∧ QuasiSober`. -/
-- Proof sketch: sobriety is owned by the pair `T₀ +` quasi-sobriety. The subtype inherits
-- `T0Space` from `X`, and clause `(1)` supplies the quasi-sober part.
protected theorem IsLocallyClosed.sober
    [T0Space X] [QuasiSober X] (hY : IsLocallyClosed Y) : T0Space Y ∧ QuasiSober Y :=
  ⟨inferInstance, hY.quasiSober⟩

end

/-! ### Lemma_5_8_8 (from Chap05) -/
universe u v

open Set Topology TopologicalSpace

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.8:
- primary domain: local behavior of `T₀`, quasi-sobriety, and sobriety under covers of a
  topological space;
- sampled owner declarations:
  `T0Space.of_cover`,
  `T0Space.of_open_cover`,
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`,
  `IsLocallyClosed.sober`;
- best owner abstractions: `T0Space` for the separation axiom, `QuasiSober` for generic-point
  existence, and `TopologicalSpace.IsOpenCover` for the canonical open-cover descent API, with
  `IsLocallyClosed.sober` as the chapter bridge for open pieces;
- primitive-vs-derived split: the primitive input is only a cover together with local-closed/open
  hypotheses on its pieces. The local `T₀`, quasi-sober, and sober conclusions are derived from
  the owner abstractions above, so this file should expose only the minimal bridge statements and
  direct recalls.

Source/core/bridge triage:
- `source-facing`: Lemma 5.8.8, asserting that `T₀`, quasi-sobriety, and sobriety are local on the
  covers described in the source;
- `core/canonical`: `T0Space.of_cover`, `T0Space.of_open_cover`, and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`;
- `bridge/view`: the locally closed cover statement for `T₀`, and the owner-level open-cover
  sobriety theorem obtained from `T0Space.of_open_cover`, `TopologicalSpace.IsOpenCover.quasiSober`,
  and the earlier locally closed bridge `IsLocallyClosed.sober`.
-/

/-- Helper for Lemma 5.8.8: inseparable points have the same membership in a locally closed
subset. -/
theorem Inseparable.mem_iff_of_isLocallyClosed {x y : X} {s : Set X}
    (hxy : Inseparable x y) (hs : IsLocallyClosed s) : x ∈ s ↔ y ∈ s := by
  -- Unpack the locally closed set into an open part and a closed part.
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  constructor
  · intro hx
    rcases hx with ⟨hxU, hxZ⟩
    -- Inseparable points agree on membership in open and closed sets separately.
    exact ⟨(hxy.mem_open_iff hU).1 hxU, (hxy.mem_closed_iff hZ).1 hxZ⟩
  · intro hy
    rcases hy with ⟨hyU, hyZ⟩
    -- Reversing the same argument gives the converse implication.
    exact ⟨(hxy.mem_open_iff hU).2 hyU, (hxy.mem_closed_iff hZ).2 hyZ⟩

/-- Lemma 5.8.8 (1): for a cover of `X` by locally closed subsets, `X` is Kolmogorov if and only
if every member of the cover is Kolmogorov. -/
-- Proof sketch: for the forward implication, each subtype inherits `T0Space`. For the reverse
-- implication, use the canonical descent theorem `T0Space.of_cover` and the locally closed
-- decomposition to show any pair of topologically indistinguishable points lies in a common
-- `T₀` cover piece.
theorem t0Space_iff_forall_of_locallyClosed_cover
    (S : ι → Set X) (hcover : ⋃ i, S i = univ) (hloc : ∀ i, IsLocallyClosed (S i)) :
    T0Space X ↔ ∀ i, T0Space (S i) := by
  constructor
  · intro hX i
    -- Each cover piece is a subspace, so it inherits `T₀`.
    letI : T0Space X := hX
    infer_instance
  · intro hS
    -- Apply the canonical cover descent theorem and force inseparable points into one `T₀` piece.
    refine T0Space.of_cover ?_
    intro x y hxy
    have hxcover : x ∈ ⋃ i, S i := by
      simp [hcover]
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hxcover
    have hyi : y ∈ S i := (hxy.mem_iff_of_isLocallyClosed (hloc i)).1 hxi
    exact ⟨S i, hxi, hyi, hS i⟩

/- Open-cover quasi-sobriety descent is provided canonically by
`TopologicalSpace.IsOpenCover.quasiSober_iff_forall`. -/
recall IsOpenCover.quasiSober_iff_forall

namespace TopologicalSpace.IsOpenCover

/- The `T₀` half of sober descent along an open cover is the canonical theorem
`T0Space.of_open_cover` together with the subtype instance on each `U i`. -/
/-- Helper for Lemma 5.8.8: `T₀` is local on an open cover. -/
theorem t0Space_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    T0Space X ↔ ∀ i, T0Space (U i) := by
  constructor
  · intro hX i
    -- Each open piece is a subspace of `X`, hence inherits `T₀`.
    letI : T0Space X := hX
    infer_instance
  · intro hUi
    -- The owner theorem `T0Space.of_open_cover` reduces the proof to one open `T₀` neighborhood
    -- through each point.
    refine T0Space.of_open_cover ?_
    intro x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact ⟨U i, hi, (U i).2, hUi i⟩

/-- Lemma 5.8.8 (2): for an open cover `U` of `X`, sobriety is local on the cover, expressed via
the canonical `T0Space` and `QuasiSober` components. -/
-- Proof sketch: the `T₀` component descends by `T0Space.of_open_cover`, and the quasi-sober
-- component is exactly `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`.
theorem sober_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    (T0Space X ↔ ∀ i, T0Space (U i)) ∧ (QuasiSober X ↔ ∀ i, QuasiSober (U i)) := by
  -- The two source clauses are exactly the canonical `T₀` and quasi-sober descent theorems.
  exact ⟨hU.t0Space_iff_forall, hU.quasiSober_iff_forall⟩

end TopologicalSpace.IsOpenCover

/-! ### Example_5_8_9 (from Chap05) -/
open Set

universe u

/-
Domain-style sampling for Example 5.8.9:
- primary domain: separation axioms and quasi-sobriety of topological spaces
- inspected owner declarations:
  `R1Space`,
  `R1Space.quasiSober`,
  `Set.iUnion_of_singleton`,
  `Subtype.t0Space`
- best owner abstraction: `R1Space` is the canonical owner for the indiscrete-space argument,
  while the singleton cover is already owned by `Set.iUnion_of_singleton`
- primitive-vs-derived split: the only primitive ingredient not already packaged upstream is the
  bridge instance `[IndiscreteTopology X] → [R1Space X]`; quasi-sobriety is then derived by the
  canonical owner instance `R1Space.quasiSober`, and the singleton-cover/subspace facts remain
  direct canonical recalls or instance consequences

Source/core/bridge triage:
- `source-facing`: indiscrete spaces are quasi-sober but, when nontrivial, not Kolmogorov; the
  singleton subsets cover the ambient set and their subspaces are discrete and `T₀`
- `core/canonical`: `R1Space`, `R1Space.quasiSober`, `Set.iUnion_of_singleton`
- `bridge/view`: the instance `[IndiscreteTopology X] → [R1Space X]` is a thin canonical bridge to
  the owner abstraction; it is not a second owner abstraction
-/

section IndiscreteSpace

variable {X : Type u} [TopologicalSpace X]

instance [IndiscreteTopology X] : R1Space X where
  specializes_or_disjoint_nhds x y := Or.inl (Inseparable.all x y).specializes

-- Proof sketch: an indiscrete space is `R₁` by the bridge instance above, and the canonical
-- instance `R1Space.quasiSober` then yields quasi-sobriety.
/-- Example 5.8.9 (1): an indiscrete space is quasi-sober. -/
theorem indiscrete_quasiSober [IndiscreteTopology X] : QuasiSober X := by
  -- The local `R₁` bridge instance upgrades directly to quasi-sobriety.
  infer_instance

-- Proof sketch: if the topology is indiscrete, any two points are inseparable. In a nontrivial
-- space this contradicts the `T0` separation condition, so the space is not Kolmogorov.
/-- Example 5.8.9 (2): a nontrivial indiscrete space is not Kolmogorov. -/
theorem indiscrete_not_kolmogorov [IndiscreteTopology X] [Nontrivial X] : ¬ T0Space X := by
  intro hT0
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  -- In an indiscrete space, no two points can be separated by neighborhoods.
  have hInsep : Inseparable x y := Inseparable.all x y
  -- A `T₀` space forces inseparable points to coincide, contradicting `x ≠ y`.
  exact hxy ((t0Space_iff_inseparable X).1 hT0 x y hInsep)

end IndiscreteSpace

section SingletonSubspaces

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: `Set.iUnion_of_singleton` gives the cover, and each singleton subtype is a
-- subsingleton topological space, hence discrete.
/-- Example 5.8.9 (3): the family of singleton subsets covers `X`, and each singleton subspace is
discrete, hence Kolmogorov. -/
theorem singletons_cover_by_discrete_subspaces :
    (⋃ x : X, ({x} : Set X)) = univ ∧ ∀ x : X, DiscreteTopology ({x} : Set X) := by
  constructor
  · -- The ambient space is the union of its singleton subsets.
    simpa using Set.iUnion_of_singleton X
  · intro x
    -- A singleton subtype is subsingleton, so its topology is automatically discrete.
    infer_instance

end SingletonSubspaces

/-! ### Example_5_8_10 (from Chap05) -/
open Set

universe u

/- Domain-style sampling for Example 5.8.10:
- primary domain: separation and quasi-sober topological spaces for the cofinite topology;
- inspected owner declarations: `T0Space`, `QuasiSober`, `genericPoint`, `genericPoint_closure`,
  the `T1Space (CofiniteTopology Y)` instance, and the irreducibility instance on
  `CofiniteTopology`;
- best owner abstraction: `T0Space` is the core owner for the Kolmogorov clause, `QuasiSober` is
  the core owner for the quasi-sober clause, and `genericPoint` is the canonical derived API for
  the irreducible closed subset `univ` in an irreducible space;
- primitive-vs-derived split: the primitive data is only the cofinite topology on a type, with
  infinitude needed only for the non-quasi-sober clause; the ambient `T₀` statement,
  irreducibility of the ambient space, and the closure of its generic point are derived from the
  canonical owner API.

Source/core/bridge triage:
- `source-facing`: the infinite cofinite space is Kolmogorov but fails to be quasi-sober, even
  though it is covered by singleton subspaces that are closed, irreducible, and sober;
- `core/canonical`: `T0Space`, `QuasiSober`, `genericPoint`, `genericPoint_closure`, and the
  instance `IrreducibleSpace (CofiniteTopology Y)`;
- `bridge/view`: the singleton-subspace examples are companion views of the source cover; they do
  not introduce a second owner abstraction, and the ambient `T₀` clause is read off from the
  stronger upstream `T1Space (CofiniteTopology Y)` instance. -/

section Ambient

variable {Y : Type u}

local notation "X" => CofiniteTopology Y

/- The cofinite topology on any set is `T₁`, hence in particular Kolmogorov (`T₀`). The
source-facing ambient separation clause is therefore the canonical owner `T0Space X`. -/
example : T0Space X := inferInstance

/-
The singleton subsets cover the underlying set of `X`. This is the canonical theorem
`Set.iUnion_of_singleton`.
-/
recall Set.iUnion_of_singleton

/- The singleton subsets provide the local irreducible closed pieces discussed in the source. In
the infinite case they are not irreducible components of the ambient cofinite space, since that
ambient space is itself irreducible. -/
example (y : X) : IsIrreducible ({y} : Set X) := isIrreducible_singleton

example (y : X) : IsClosed ({y} : Set X) := isClosed_singleton

-- Proof sketch: a singleton subtype is a subsingleton type, hence carries the discrete topology.
/-- Each singleton subspace of the cofinite space is discrete. -/
theorem singleton_discreteTopology (y : X) : DiscreteTopology ({y} : Set X) := by
  -- A singleton subtype is subsingleton, so its subspace topology is automatically discrete.
  infer_instance

-- Proof sketch: a discrete singleton space is Hausdorff, hence in particular `T₀` and
-- quasi-sober.
/-- Each singleton subspace is sober, expressed canonically as `T0Space` plus `QuasiSober`. -/
theorem singleton_t0Space_and_quasiSober (y : X) :
    T0Space ({y} : Set X) ∧ QuasiSober ({y} : Set X) := by
  -- First record the discrete topology, then read off the canonical separation and sobriety
  -- instances on the singleton subtype.
  have hDiscrete : DiscreteTopology ({y} : Set X) := singleton_discreteTopology y
  constructor <;> infer_instance

end Ambient

section Infinite

variable {Y : Type u} [Infinite Y]

local notation "X" => CofiniteTopology Y

/-- Helper for Example 5.8.10: quasi-sobriety would force the generic point singleton to fill the
entire infinite cofinite space. -/
lemma genericPoint_singleton_eq_univ [QuasiSober X] : ({genericPoint X} : Set X) = univ := by
  -- In the irreducible cofinite space, the generic point is dense.
  have hclosure : closure ({genericPoint X} : Set X) = (univ : Set X) := genericPoint_closure X
  -- Singletons are closed in a `T₁` space, so their closure is the singleton itself.
  have hclosed : IsClosed ({genericPoint X} : Set X) := isClosed_singleton
  simpa [hclosed.closure_eq] using hclosure

-- Proof sketch: in an irreducible quasi-sober space, `genericPoint_closure` gives
-- `closure {genericPoint} = univ`. In the infinite cofinite topology every singleton is closed, so
-- this forces `univ` to be a singleton, contradicting infinitude.
/-- Example 5.8.10: the cofinite topology on an infinite set is not quasi-sober. -/
theorem infinite_cofiniteTopology_not_quasiSober : ¬ QuasiSober X := by
  intro hQuasi
  letI : QuasiSober X := hQuasi
  -- Quasi-sobriety gives a generic point for the irreducible ambient space.
  have hsingleton : ({genericPoint X} : Set X) = (univ : Set X) := genericPoint_singleton_eq_univ
  -- If the whole space is a singleton, then the cofinite type synonym itself is subsingleton.
  have hSubsingleton : Subsingleton X := by
    refine ⟨fun x z => ?_⟩
    have hxmem : x ∈ ({genericPoint X} : Set X) := by
      simp [hsingleton]
    have hzmem : z ∈ ({genericPoint X} : Set X) := by
      simp [hsingleton]
    have hx : x = genericPoint X := by
      simpa using hxmem
    have hz : z = genericPoint X := by
      simpa using hzmem
    exact hx.trans hz.symm
  -- Transport subsingletonity back along the identity equivalence to contradict infinitude of `Y`.
  have hSubsingletonY : Subsingleton Y := by
    refine ⟨fun y z => ?_⟩
    simpa using hSubsingleton.elim (CofiniteTopology.of y) (CofiniteTopology.of z)
  exact not_subsingleton Y hSubsingletonY

end Infinite

/-! ### Example_5_8_11 (from Chap05) -/
universe u v

open Topology

section

variable (X : Type u) [TopologicalSpace X]
variable (Y : Type v)

local notation "S" => X ⊕ CofiniteTopology Y

/- Domain-style sampling for Example 5.8.11:
- primary domain: separation and quasi-sobriety behavior under coproduct inclusions;
- inspected owner declarations:
  `Topology.IsEmbedding.t0Space`,
  `Topology.IsOpenEmbedding.quasiSober`,
  `indiscrete_not_kolmogorov`,
  `infinite_cofiniteTopology_not_quasiSober`;
- best owner abstraction: `T0Space` and `QuasiSober` remain the ambient owners, while the coproduct
  maps `Sum.inl` and `Sum.inr` are the canonical bridge/view API transporting those properties to
  the summands;
- primitive-vs-derived split: the only primitive input here is the left indiscrete/nontrivial
  hypothesis and the right infinite cofinite space. The contradiction arguments are entirely
  derived from the canonical inclusion APIs, so this file should not keep extra local wrapper maps
  or redundant left-side assumptions on the quasi-sober clause.

Source/core/bridge triage:
- `source-facing`: the disjoint union in the source example is neither Kolmogorov nor quasi-sober;
- `core/canonical`: `T0Space`, `QuasiSober`, `indiscrete_not_kolmogorov`,
  `infinite_cofiniteTopology_not_quasiSober`;
- `bridge/view`: `IsEmbedding.inl` and `IsOpenEmbedding.inr` transfer those owner properties to the
  coproduct summands. -/

/-- Example 5.8.11 (1): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is not a
Kolmogorov (`T₀`) space. -/
theorem sum_not_kolmogorov_of_indiscrete_left
    [IndiscreteTopology X] [Nontrivial X] :
    ¬ T0Space S := by
  intro hS
  letI : T0Space S := hS
  letI : T0Space X :=
    (IsEmbedding.inl : IsEmbedding (Sum.inl : X → S)).t0Space
  have hX : ¬ T0Space X := indiscrete_not_kolmogorov
  exact hX inferInstance

/-- Example 5.8.11 (2): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is not
quasi-sober. -/
theorem sum_not_quasiSober_of_infinite_cofinite_right
    [Infinite Y] :
    ¬ QuasiSober S := by
  intro hS
  letI : QuasiSober S := hS
  letI : QuasiSober (CofiniteTopology Y) :=
    (IsOpenEmbedding.inr :
      IsOpenEmbedding (Sum.inr : CofiniteTopology Y → S)).quasiSober
  have hY : ¬ QuasiSober (CofiniteTopology Y) := infinite_cofiniteTopology_not_quasiSober
  exact hY inferInstance

/-- Example 5.8.11 (3): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is
neither Kolmogorov nor quasi-sober. -/
theorem sum_not_kolmogorov_not_quasiSober_of_indiscrete_left_infinite_cofinite_right
    [IndiscreteTopology X] [Nontrivial X] [Infinite Y] :
    ¬ T0Space S ∧ ¬ QuasiSober S :=
  ⟨sum_not_kolmogorov_of_indiscrete_left X Y,
    sum_not_quasiSober_of_infinite_cofinite_right X Y⟩

end

/-! ### Example_5_8_12 (from Chap05) -/
open Set Topology

universe u

section

variable {Z : Type u}
variable (z : Z)

/- Domain-style sampling for Example 5.8.12:
- primary domain: topologies defined by closed sets, quasi-sobriety, and the cofinite topology on
  the punctured subspace;
- inspected owner declarations:
  `TopologicalSpace.ofClosed`,
  `CofiniteTopology.isClosed_iff`,
  `QuasiSober`,
  `infinite_cofiniteTopology_not_quasiSober`;
- best owner abstraction: the source-facing owner is the topology
  `finiteClosedAwayFromPointTopology z`, while the type synonym `FiniteClosedAwayFromPoint z` is
  only the thin bridge needed to attach that topology to the original carrier, in the same style as
  `CofiniteTopology`;
- primitive-vs-derived split: the primitive data is only the closed-set presentation of
  `finiteClosedAwayFromPointTopology z`; the type synonym, the `T₀` and quasi-sober structure, and the
  punctured cofinite comparison are derived bridge/API on `FiniteClosedAwayFromPoint z`.

Source/core/bridge triage:
- `source-facing`: the topology whose closed sets are `Z` and the finite subsets of `Z \ {z}`;
- `core/canonical`: `TopologicalSpace.ofClosed`, `T0Space`, `QuasiSober`, and
  `CofiniteTopology`;
- `bridge/view`: the owner type synonym `FiniteClosedAwayFromPoint z`, the punctured-subspace comparison
  theorem, and the source-facing closed-set characterization theorem.
-/

/-- The family of closed sets for the topology in Example 5.8.12: either all of `Z`, or a finite
subset of `Z \ {z}`. -/
private def finiteClosedAwayFromPointClosedSets : Set (Set Z) :=
  { s | s = univ ∨ s.Finite ∧ s ⊆ ({z} : Set Z)ᶜ }

/-- The empty set is closed in the topology of Example 5.8.12. -/
-- Proof sketch: `∅` is finite and is contained in `Z \ {z}`.
private theorem finiteClosedAwayFromPointClosedSets_empty_mem :
    ∅ ∈ finiteClosedAwayFromPointClosedSets z := by
  right
  exact ⟨finite_empty, by simp⟩

/-- Arbitrary intersections of closed sets remain closed for the topology of Example 5.8.12. -/
-- Proof sketch: if every set in the family is `univ`, then the intersection is `univ`. Otherwise
-- pick one finite member; the full intersection is contained in that finite set and still avoids
-- `z`.
private theorem finiteClosedAwayFromPointClosedSets_sInter_mem {A : Set (Set Z)}
    (hA : A ⊆ finiteClosedAwayFromPointClosedSets z) :
    ⋂₀ A ∈ finiteClosedAwayFromPointClosedSets z := by
  classical
  by_cases hAll : ∀ s ∈ A, s = univ
  · left
    apply eq_univ_of_forall
    intro x
    exact mem_sInter.2 fun t ht ↦ by simp [hAll t ht]
  · obtain ⟨s, hs⟩ := not_forall.mp hAll
    obtain ⟨hsA, hs_ne⟩ := not_forall.mp hs
    rcases hA hsA with rfl | ⟨hsFinite, hsSubset⟩
    · exact (hs_ne rfl).elim
    right
    refine ⟨hsFinite.subset <| sInter_subset_of_mem hsA, ?_⟩
    exact (sInter_subset_of_mem hsA).trans hsSubset

/-- Finite unions of closed sets remain closed for the topology of Example 5.8.12. -/
-- Proof sketch: the union of two finite subsets of `Z \ {z}` is again finite and still avoids
-- `z`, while `univ` is absorbing for unions.
private theorem finiteClosedAwayFromPointClosedSets_union_mem {A B : Set Z}
    (hA : A ∈ finiteClosedAwayFromPointClosedSets z)
    (hB : B ∈ finiteClosedAwayFromPointClosedSets z) :
    A ∪ B ∈ finiteClosedAwayFromPointClosedSets z := by
  rcases hA with rfl | ⟨hAFinite, hASubset⟩
  · left
    simp
  rcases hB with rfl | ⟨hBFinite, hBSubset⟩
  · left
    simp
  right
  exact ⟨hAFinite.union hBFinite, union_subset hASubset hBSubset⟩

/-- The topology from Example 5.8.12 whose closed sets are `Z` and the finite subsets of
`Z \ {z}`. -/
@[reducible] def finiteClosedAwayFromPointTopology : TopologicalSpace Z :=
  TopologicalSpace.ofClosed (finiteClosedAwayFromPointClosedSets z)
    (finiteClosedAwayFromPointClosedSets_empty_mem z)
    (fun _ hA ↦ finiteClosedAwayFromPointClosedSets_sInter_mem z hA)
    (fun _ hA _ hB ↦ finiteClosedAwayFromPointClosedSets_union_mem z hA hB)

/-- The point set `Z` equipped with the topology from Example 5.8.12. -/
def FiniteClosedAwayFromPoint (_ : Z) := Z

instance : TopologicalSpace (FiniteClosedAwayFromPoint z) :=
  finiteClosedAwayFromPointTopology z

namespace FiniteClosedAwayFromPoint

local notation "X" => FiniteClosedAwayFromPoint z
local notation "U" => {x : X // x ≠ z}

/-- The closed subsets of `FiniteClosedAwayFromPoint z` are exactly `univ` and the finite subsets
of `Z \ {z}`. -/
theorem isClosed_iff {s : Set X} :
    IsClosed s ↔ s = univ ∨ s.Finite ∧ s ⊆ ({z} : Set X)ᶜ := by
  constructor
  · intro hs
    have hs' : sᶜᶜ ∈ finiteClosedAwayFromPointClosedSets z := hs.1
    simpa [finiteClosedAwayFromPointClosedSets, Set.subset_def] using hs'
  · intro hs
    rw [← isOpen_compl_iff]
    change sᶜᶜ ∈ finiteClosedAwayFromPointClosedSets z
    simpa [finiteClosedAwayFromPointClosedSets, Set.subset_def] using hs

private theorem isClosed_singleton_of_ne {x : X} (hx : x ≠ z) :
    IsClosed ({x} : Set X) := by
  rw [isClosed_iff]
  right
  refine ⟨finite_singleton x, ?_⟩
  intro y hy
  simp only [mem_singleton_iff] at hy
  simpa [hy] using hx

private theorem closure_singleton_eq_univ :
    closure ({z} : Set X) = univ := by
  rcases (isClosed_iff z).1 isClosed_closure with h | ⟨_, h⟩
  · exact h
  · exfalso
    have hz : (show X from z) ∈ closure ({show X from z} : Set X) :=
      subset_closure (by simp)
    have hz' : (show X from z) ∈ ({show X from z} : Set X)ᶜ := h hz
    exact hz' (by simp)

private theorem closure_singleton_eq_of_ne {x : X} (hx : x ≠ z) :
    closure ({x} : Set X) = ({x} : Set X) :=
  (isClosed_singleton_of_ne z hx).closure_eq

/-- The punctured subspace of `FiniteClosedAwayFromPoint z` agrees with the canonical cofinite
topology on `Z \ {z}`. -/
theorem punctured_eq_cofiniteTopology :
    (inferInstance : TopologicalSpace U) =
      (inferInstance : TopologicalSpace (CofiniteTopology U)) := by
  apply TopologicalSpace.ext_isClosed
  intro s
  constructor
  · intro hs
    rcases isClosed_induced_iff.mp hs with ⟨t, ht, rfl⟩
    rw [isClosed_iff] at ht
    rcases ht with rfl | ⟨ht, _⟩
    · exact CofiniteTopology.isClosed_iff.2 <| Or.inl rfl
    · exact CofiniteTopology.isClosed_iff.2 <| Or.inr <|
        Finite.preimage_embedding ⟨Subtype.val, Subtype.val_injective⟩ ht
  · intro hs
    rcases (CofiniteTopology.isClosed_iff).1 hs with rfl | hs
    · exact isClosed_univ
    · refine isClosed_induced_iff.2 ?_
      refine ⟨(↑) '' s, ?_, preimage_image_eq _ Subtype.val_injective⟩
      rw [isClosed_iff]
      right
      refine ⟨Finite.image (Subtype.val : U → X) hs, ?_⟩
      rintro x ⟨y, hy, rfl⟩
      exact y.2

/-- The space `FiniteClosedAwayFromPoint z` is Kolmogorov. -/
instance : T0Space X := by
  rw [t0Space_iff_or_notMem_closure]
  intro x y hxy
  by_cases hx : x = z
  · have hy : y ≠ z := by
      simpa [hx] using hxy.symm
    left
    rw [closure_singleton_eq_of_ne z hy]
    simpa [hx] using hxy
  · right
    rw [closure_singleton_eq_of_ne z hx]
    simpa using hxy.symm

/-- The space `FiniteClosedAwayFromPoint z` is quasi-sober. -/
instance : QuasiSober X where
  sober {S} hS hSClosed := by
    rcases (isClosed_iff z).1 hSClosed with rfl | ⟨hSFinite, hSAway⟩
    · exact ⟨show X from z, by
        simpa [isGenericPoint_def] using closure_singleton_eq_univ z⟩
    · obtain ⟨x, hxS⟩ := hS.nonempty
      have hxz : x ≠ z := by
        simpa using hSAway hxS
      have hSDiffClosed : IsClosed (S \ {x}) := by
        rw [isClosed_iff]
        right
        refine ⟨hSFinite.subset diff_subset, ?_⟩
        exact diff_subset.trans hSAway
      have hSSubset : S ⊆ ({x} : Set X) ∪ (S \ {x}) := by
        intro y hyS
        by_cases hyx : y = x
        · simp [hyx]
        · right
          exact ⟨hyS, hyx⟩
      have hSingle : S ⊆ ({x} : Set X) := by
        rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hS.isPreirreducible)
            ({x} : Set X) (S \ {x})
            (isClosed_singleton_of_ne z hxz) hSDiffClosed hSSubset with h | h
        · exact h
        · exact (h hxS).2.elim rfl
      have hEq : S = ({x} : Set X) :=
        subset_antisymm hSingle (singleton_subset_iff.2 hxS)
      exact ⟨x, by rw [isGenericPoint_def, hEq, closure_singleton_eq_of_ne z hxz]⟩

/-- Example 5.8.12 (1): the topology whose closed sets are `Z` and the finite subsets of
`Z \ {z}` is sober, expressed canonically by `T₀` and quasi-sobriety. In particular, this
recovers the source statement for infinite `Z`. -/
-- Proof sketch: show first that the topology is `T₀`, with `z` topologically distinguished from
-- every other point. Then classify irreducible closed subsets: they are either `univ`, with
-- generic point `z`, or singletons away from `z`, whose unique point is generic.
theorem sober :
    T0Space X ∧ QuasiSober X :=
  ⟨inferInstance, inferInstance⟩

section Infinite

variable [Infinite Z]

/-- Example 5.8.12 (2): the induced topology on the subspace `Z \ {z}` is not quasi-sober. -/
-- Proof sketch: after removing `z`, the induced topology is the cofinite topology on an infinite
-- set. The whole space is irreducible and closed, but in a cofinite `T₁` space every singleton is
-- closed, so no point has dense singleton closure and hence `univ` has no generic point.
theorem punctured_not_quasiSober :
    ¬ QuasiSober U := by
  haveI : Infinite U := by
    simpa using (finite_singleton z).infinite_compl.to_subtype
  change ¬ @QuasiSober U (inferInstance : TopologicalSpace U)
  rw [punctured_eq_cofiniteTopology]
  change ¬ QuasiSober (CofiniteTopology U)
  exact infinite_cofiniteTopology_not_quasiSober

end Infinite

end FiniteClosedAwayFromPoint

end

/-! ### Example_5_8_13 (from Chap05) -/
universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Example 5.8.13:
- primary domain: Hausdorff separation and sobriety of topological spaces;
- inspected owner declarations:
  `TopologicalSpace.IrreducibleCloseds`,
  `isIrreducible_iff_singleton`,
  `sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint`,
  `T2Space.r1Space`,
  `R1Space.quasiSober`;
- best owner abstraction: the chapter owner for sobriety is the canonical pair
  `T0Space X ∧ QuasiSober X`, while irreducible closed subsets are owned by the bundled type
  `IrreducibleCloseds X`;
- primitive-vs-derived split: this file adds no primitive data; it only records source-facing
  consequences derived from the owner theorem `isIrreducible_iff_singleton` and the canonical
  instance chain `T2Space ⟶ T0Space`, `T2Space ⟶ R1Space ⟶ QuasiSober`. -/

/- Source/core/bridge triage for Example 5.8.13:
- `source-facing`: irreducible closed subsets of a Hausdorff space are singletons, and Hausdorff
  spaces are sober;
- `core/canonical`: `isIrreducible_iff_singleton`, `T2Space.r1Space`, `R1Space.quasiSober`, and
  the chapter sobriety owner `T0Space X ∧ QuasiSober X`;
- `bridge/view`: the bundled singleton theorem on `IrreducibleCloseds X` is a thin source-facing
  restatement of `isIrreducible_iff_singleton`, while the sobriety clause is direct owner use. -/

section Hausdorff

variable [T2Space X]

-- Proof sketch: the bundled irreducible closed subset `Z` is in particular an irreducible subset
-- of `X`, so the stronger canonical theorem `isIrreducible_iff_singleton` applies directly.
/-- Example 5.8.13 (1): every irreducible closed subset of a Hausdorff space is a singleton. -/
theorem IrreducibleCloseds.exists_eq_singleton (Z : IrreducibleCloseds X) :
    ∃ x : X, Z = {x} := by
  rcases isIrreducible_iff_singleton.mp Z.isIrreducible with ⟨x, hx⟩
  exact ⟨x, IrreducibleCloseds.ext hx⟩

/- Companion recall: in a Hausdorff space, the stronger canonical theorem
`isIrreducible_iff_singleton` characterizes all irreducible subsets, not just irreducible closed
subsets. Applied to `univ`, it also gives the ambient-space statement from the source text. -/
recall isIrreducible_iff_singleton

-- Proof sketch: combine the canonical separation-instance chain `T2Space ⟶ T1Space ⟶ T0Space`
-- with the sober-instance chain `T2Space ⟶ R1Space ⟶ QuasiSober`. As in Definition 5.8.6, the
-- public sober owner here is the pair `T0Space X ∧ QuasiSober X`, so no extra wrapper theorem is
-- needed.
/-- Example 5.8.13 (2): every Hausdorff space is sober, expressed canonically by `T₀` and quasi-sobriety. -/
theorem t2Space_sober : T0Space X ∧ QuasiSober X :=
  ⟨inferInstance, inferInstance⟩

end Hausdorff

/-! ### Lemma_5_8_14 (from Chap05) -/
universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for irreducibility under open maps:
- owner abstraction: `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`
- same-domain declarations inspected:
  `IrreducibleSpace.isIrreducible_univ`,
  `irreducibleSpace_def`,
  `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`,
  `IsIrreducible.preimage_of_isPreirreducible_fiber`

Layer triage:
- `source-facing`: the space-level irreducibility criterion in the Stacks lemma
- `core/canonical`: the set-level owner theorem
  `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`
- `bridge/view`: the `IsOpenMap`-owner theorem below together with `irreducibleSpace_def`,
  turning irreducibility of `univ` into `IrreducibleSpace`

Primitive data is the open-map hypothesis together with dense irreducibility information on the
fibers. The space-level conclusion is derived API, so this file should stay a thin bridge to the
owner theorem rather than repackage a parallel local irreducibility API.
-/

section

variable {f : X → Y}

namespace IsOpenMap

-- Proof sketch: use the dense set of points with irreducible fibers to get a point of `X`,
-- then apply the canonical set-level owner theorem
-- `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber` to `univ ⊆ Y`.
/-- Lemma 5.8.14: if `f : X → Y` is open, `Y` is irreducible, and the points of
`Y` with irreducible fiber form a dense subset, then `X` is irreducible. -/
theorem irreducibleSpace_of_dense_irreducible_fiber
    (hf : IsOpenMap f) (hY : IrreducibleSpace Y)
    (hdense : Dense { y : Y | IsIrreducible (f ⁻¹' {y}) }) : IrreducibleSpace X := by
  letI : IrreducibleSpace Y := hY
  have hdensePre : Dense { y : Y | IsPreirreducible (f ⁻¹' {y}) } :=
    hdense.mono fun y hy ↦ hy.isPreirreducible
  have hnonempty : (univ : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hdense.nonempty
    exact hy.nonempty.mono (subset_univ _)
  refine (irreducibleSpace_def X).2 ⟨hnonempty, ?_⟩
  simpa [inter_univ] using
    IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
      (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible f hf
      (by simpa [inter_univ] using hdensePre.closure_eq)

end IsOpenMap

end

/-! ### Lemma_5_8_15 (from Chap05) -/
universe u v

section

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for irreducible components under open maps:
- primary domain: irreducible subsets and irreducible components in point-set topology
- owner abstraction: `irreducibleComponentsEquivOfIsPreirreducibleFiber`
- same-domain declarations inspected:
  `irreducibleComponents`,
  `preimage_mem_irreducibleComponents_of_isPreirreducible_fiber`,
  `image_mem_irreducibleComponents_of_isPreirreducible_fiber`,
  `irreducibleComponentsEquivOfIsPreirreducibleFiber`

Layer triage:
- `source-facing`: Lemma 5.8.15, stated with irreducible fibers
- `core/canonical`: the owner equivalence
  `irreducibleComponentsEquivOfIsPreirreducibleFiber`
- `bridge/view`: the specialization from irreducible fibers to preirreducible fibers together
  with the induced surjectivity witness

Primitive data for the owner theorem is continuity, openness, preirreducible fibers, and
surjectivity. The stronger source hypothesis that every fiber is irreducible supplies the last two
inputs, so this file should recall the owner and keep only that thin source-facing specialization.
-/

/- Canonical recall: the owner theorem for irreducible components under a continuous open map is
`irreducibleComponentsEquivOfIsPreirreducibleFiber`. -/
recall irreducibleComponentsEquivOfIsPreirreducibleFiber

omit [TopologicalSpace Y] in
/-- If every fiber of `f` over a point of `Y` is irreducible, then `f` is surjective. -/
-- Proof sketch: any irreducible fiber is nonempty, so for each `y` one extracts a point in
-- `f ⁻¹' {y}` and hence a preimage of `y`.
theorem surjective_of_isIrreducible_fibers
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) : Function.Surjective f := by
  intro y
  -- Convert nonemptiness of the singleton fiber into membership of `y` in the range of `f`.
  have hy_mem_range : y ∈ Set.range f := by
    exact Set.preimage_singleton_nonempty.mp (hfibers y).nonempty
  -- Unpack range membership to obtain the required preimage witness.
  exact Set.mem_range.mp hy_mem_range

/-- Lemma 5.8.15: a continuous open map whose fibers are irreducible induces a bijection between
the irreducible components of `Y` and those of `X`; equivalently, it induces a canonical order
isomorphism between them. -/
def irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) :
    irreducibleComponents Y ≃o irreducibleComponents X :=
  irreducibleComponentsEquivOfIsPreirreducibleFiber f hcont hopen
    (fun y ↦ (hfibers y).isPreirreducible) (surjective_of_isIrreducible_fibers hfibers)

/-- This specialization is definitionally the canonical equivalence coming from preirreducible
fibers and surjectivity. -/
-- Proof sketch: unfold the specialized definition and compare it with the recalled owner
-- equivalence.
theorem irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers_def
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) :
    irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers hcont hopen hfibers =
      irreducibleComponentsEquivOfIsPreirreducibleFiber f hcont hopen
        (fun y ↦ (hfibers y).isPreirreducible)
        (surjective_of_isIrreducible_fibers hfibers) := by
  -- The specialized definition is exactly the recalled owner equivalence.
  rfl

end
