import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_22_1 (from Chap05) -/
open CategoryTheory Limits
open CompHausLike

universe u

/- Domain-style sampling for profinite spaces and their finite-discrete limit presentation:
- primary domain: profinite topological spaces
- inspected owner declarations:
  `Profinite`,
  `FintypeCat.toProfinite`,
  `Profinite.diagram`,
  `Profinite.lim`

Layer triage:
- `source-facing`: the cofiltered-limit presentation by finite discrete spaces
- `core/canonical`: the bundled owner `Profinite`
- `bridge/view`: the equivalence between an arbitrary space and a profinite limit presentation

Primitive data belongs to the owner `Profinite`; the finite-discrete presentation data are derived
from `P.fintypeDiagram`, `P.diagram`, and `P.lim`. Since Lean packages existential
homeomorphisms propositionally via `Nonempty`, the source-facing bridge below keeps the bundled
profinite witness explicit and uses only the standard proposition wrapper for the homeomorphism
witness. -/

/- Definition 5.22.1: the canonical mathlib owner abstraction for profinite spaces is the bundled
type `Profinite`. Its objects are precisely the compact Hausdorff totally disconnected spaces, and
the source-text cofiltered limit presentation below recovers the same notion. -/
recall Profinite

/- Canonical finite-discrete inclusion used in the profinite limit presentation. -/
recall FintypeCat.toProfinite

/- Canonical profinite presentation by finite discrete quotients. -/
recall Profinite.fintypeDiagram

/- Canonical profinite-valued diagram attached to a profinite space. -/
recall Profinite.diagram

/- Bundled limit cone for the canonical finite-discrete presentation of a profinite space. -/
recall Profinite.lim

/-- Source-text form of Definition 5.22.1, expressed through the canonical bundled profinite-space
interface and the standard cofiltered limit presentation by finite discrete spaces. -/
theorem exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete
    (X : Type u) [TopologicalSpace X] :
    (∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) ↔
      ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FintypeCat.{u}),
        Nonempty (X ≃ₜ (limit (F ⋙ FintypeCat.toProfinite) : Profinite.{u})) := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    refine ⟨DiscreteQuotient P, inferInstance, inferInstance, P.fintypeDiagram, ?_⟩
    change Nonempty (X ≃ₜ (limit P.diagram : Profinite.{u}))
    exact ⟨e.trans (homeoOfIso (limit.isoLimitCone P.lim).symm)⟩
  · rintro ⟨J, _, _, F, ⟨e⟩⟩
    exact ⟨limit (F ⋙ FintypeCat.toProfinite), ⟨e⟩⟩

/-! ### Lemma_5_22_2 (from Chap05) -/
open CategoryTheory Limits

universe u

/- Domain-style sampling for profinite topological spaces:
- owner abstraction: `Profinite`
- same-domain declarations inspected:
  `Profinite`,
  `Profinite.of`,
  `exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete`,
  `FintypeCat.toProfinite`

Layer triage:
- `source-facing`: the Stacks characterization of profinite spaces by separation, compactness, and
  total disconnectedness
- `core/canonical`: the bundled owner `Profinite`
- `bridge/view`: the equivalence between the source-facing conjunction and existence of a
  homeomorphism to a profinite space, together with the derived cofiltered-limit presentation

Primitive data is exactly the ambient topology plus the three typeclass fields
`T2Space X`, `CompactSpace X`, and `TotallyDisconnectedSpace X`, which are precisely what
construct `Profinite.of X`. The cofiltered-limit presentation is derived API owned upstream by
`exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete`, so this file should keep only
the thin bridge from the source conjunction to that owner theorem and reuse it for the derived
cofiltered-limit presentation.
-/

section

variable (X : Type u) [TopologicalSpace X]

-- Proof sketch: transport the Hausdorff instance across a homeomorphism from `X` to a profinite
-- space.
/-- Lemma 5.22.2 (1): if a topological space is homeomorphic to a profinite space, then it is
Hausdorff. -/
theorem exists_profinite_implies_t2Space
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : T2Space X := by
  -- Unpack the profinite model and transport Hausdorffness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.t2Space

-- Proof sketch: transport compactness across a homeomorphism from `X` to a profinite space.
/-- Lemma 5.22.2 (2): if a topological space is homeomorphic to a profinite space, then it is
quasi-compact. -/
theorem exists_profinite_implies_compactSpace
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : CompactSpace X := by
  -- Unpack the profinite model and transport compactness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.compactSpace

-- Proof sketch: transport total disconnectedness across a homeomorphism from `X` to a profinite
-- space.
/-- Lemma 5.22.2 (3): if a topological space is homeomorphic to a profinite space, then it is
totally disconnected. -/
theorem exists_profinite_implies_totallyDisconnectedSpace
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : TotallyDisconnectedSpace X := by
  -- Unpack the profinite model and transport total disconnectedness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.totallyDisconnectedSpace

-- Proof sketch: use the canonical bundled profinite space `Profinite.of X` once the Hausdorff,
-- compact, and totally disconnected instances are available.
/-- Lemma 5.22.2 (4): a Hausdorff, quasi-compact, and totally disconnected space is homeomorphic
to a profinite space. -/
theorem t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P) := by
  -- Package the given structure into the canonical bundled profinite owner.
  exact ⟨Profinite.of X, ⟨Homeomorph.refl _⟩⟩

-- Proof sketch: first obtain a profinite model from the Hausdorff, compact, and totally
-- disconnected hypotheses, then apply the cofiltered-limit presentation of profinite spaces from
-- `Definition 5.22.1`.
/-- Lemma 5.22.2 (5): a Hausdorff, quasi-compact, and totally disconnected space is a cofiltered
limit of finite discrete spaces. -/
theorem hausdorff_compact_totallyDisconnected_has_cofiltered_limit_presentation
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FintypeCat.{u}),
      Nonempty (X ≃ₜ (limit (F ⋙ FintypeCat.toProfinite) : Profinite.{u})) := by
  -- First realize `X` as a profinite space, then invoke the canonical finite-discrete presentation.
  exact
    (exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete X).1
      (t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite (X := X))

end

/-! ### Lemma_5_22_3 (from Chap05) -/
open CategoryTheory Limits

universe u

/- Domain-style sampling for limits in `Profinite`:
- primary domain: categorical limits in the bundled category of profinite spaces;
- inspected owner declarations:
  `Profinite.limitCone`,
  `Profinite.limitConeIsLimit`,
  `Profinite.hasLimits`,
  `Profinite.toTopCat.createsLimits`.
- best owner abstraction: the global instance `Profinite.hasLimits : HasLimits Profinite`.

Primitive-vs-derived split:
- primitive data: for each diagram `F`, the chosen cone `Profinite.limitCone F` and the proof
  `Profinite.limitConeIsLimit F`;
- derived API: the diagramwise instance `HasLimit F`, obtained from the owner instance
  `Profinite.hasLimits`.

Source/core/bridge triage:
- `source-facing`: a limit of profinite spaces is profinite;
- `core/canonical`: the owner instance `Profinite.hasLimits`;
- `bridge/view`: the diagram-specific specialization `HasLimit F`.

This item is recall-only: the file should reuse the canonical owner instance rather than keep a
parallel theorem with the exact same interface as the derived specialization.
-/

/- Lemma 5.22.3: the category of profinite spaces has limits. This is exactly the canonical owner
instance `Profinite.hasLimits`. -/
recall Profinite.hasLimits

section

variable {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u})

/- Companion specialization: for any profinite-valued diagram `F`, the source statement "a limit
of profinite spaces is profinite" is the canonical derived instance `HasLimit F`. -/
#check (inferInstance : HasLimit F)

end

/-! ### Lemma_5_22_4 (from Chap05) -/
open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TotallyDisconnectedSpace X]
  {ι : Type v} {U : ι → Opens X}

/-
Domain-style sampling for profinite open-cover refinements:
- primary domain: refinement of open covers in profinite spaces
- inspected owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `TopologicalSpace.IsOpenCover.exists_finite_clopen_cover`,
  `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`,
  `Profinite`
- best owner abstraction: `TopologicalSpace.IsOpenCover`

Layer triage:
- `source-facing`: Lemma 5.22.4, for a fixed open cover of a profinite space
- `core/canonical`: `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`
- `bridge/view`: none, since the source statement is exactly the canonical owner theorem

Primitive data is only the fixed open cover `U` together with `IsOpenCover U`; the finite disjoint
clopen refinement is derived output of the owner theorem. This file should therefore recall that
canonical theorem directly rather than keep a parallel local alias.
-/

/- Lemma 5.22.4: every open cover of a profinite space admits a refinement by a finite cover by
pairwise disjoint nonempty clopen subsets. This is exactly the canonical owner theorem
`TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`. -/
recall TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover

end

/-! ### Lemma_5_22_5 (from Chap05) -/
universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

/- Domain-style sampling for connected components and profinite quotients:
- primary domain: connected components of compact spaces and the profinite owner `Profinite`;
- same-domain owner declarations inspected:
  `ConnectedComponents.t2`,
  `ConnectedComponents.totallyDisconnectedSpace`,
  `connectedComponent_eq_iInter_isClopen`,
  `exists_profinite_iff_t2Space_compactSpace_totallyDisconnectedSpace`;
- best owner abstraction: the public owner object is `ConnectedComponents X`, with profiniteness
  derived canonically through `Profinite` once the Hausdorff instance on the quotient is supplied.

Layer triage:
- `source-facing`: the Hausdorff criterion on `ConnectedComponents X` under the Stacks hypothesis
  that each connected component is the intersection of the clopen neighborhoods of its points;
- `core/canonical`: `ConnectedComponents`, `T2Space`, and the chapter owner theorem
  `exists_profinite_iff_t2Space_compactSpace_totallyDisconnectedSpace`;
- `bridge/view`: the profinite existence statement, which should be a thin specialization of the
  canonical profinite criterion rather than a second hand-built witness construction.

Primitive data is only the quotient owner `ConnectedComponents X` and the source hypothesis
`hcomponents`; compactness and total disconnectedness of the quotient are already owned upstream by
canonical instances. The profinite statement is therefore derived API and should reuse the chapter
owner theorem directly.
-/

-- Proof sketch: compactness makes `ConnectedComponents X` quasi-compact, and it is totally
-- disconnected by the canonical quotient construction. For Hausdorffness, take distinct connected
-- components `C` and `D`; write `D` as the intersection of the clopen neighborhoods of a point
-- `b ∈ D`, use compactness of `C` and the finite-intersection argument to find one clopen
-- neighborhood of `b` disjoint from `C`, then descend that clopen set to the quotient by
-- connected components.
/-- Supporting Hausdorff criterion for Lemma 5.22.5. Compactness and total disconnectedness of
`ConnectedComponents X` are already canonical, so the remaining nontrivial input for profiniteness
is Hausdorffness. -/
instance ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z)
    :
    T2Space (ConnectedComponents X) := by
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b hne ↦ ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at hne
  have hdisj := connectedComponent_disjoint hne
  rw [hcomponents b, disjoint_iff_inter_eq_empty] at hdisj
  obtain ⟨U, V, hU, hUa, hUb, rfl⟩ : ∃ (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧ (↑) ⁻¹' V = U := by
    have hfinite :=
      isClosed_connectedComponent.isCompact.elim_finite_subfamily_closed
        _ (fun Z : { Z : Set X // IsClopen Z ∧ b ∈ Z } ↦ Z.2.1.1) hdisj
    obtain ⟨s, hs⟩ := hfinite
    set U : Set X := ⋂ Z ∈ s, (Z : Set X)
    have hU : IsClopen U := isClopen_biInter_finset fun Z _ ↦ Z.2.1
    exact ⟨U, (↑) '' U, hU, hs,
      subset_iInter₂ fun Z _ ↦ Z.2.1.connectedComponent_subset Z.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hUb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h ↦ flip Set.Nonempty.ne_empty hUa ⟨a, mem_connectedComponent, h⟩

/-- Lemma 5.22.5 (Stacks tag `0900`): if `X` is quasi-compact and for every point `x`, the
connected component `connectedComponent x` is the intersection of the clopen neighborhoods of `x`,
then `π₀(X)` is profinite. The
canonical Lean model of `π₀(X)` is `ConnectedComponents X`, and the bundled profinite space is
therefore `Profinite.of (ConnectedComponents X)`. -/
theorem connectedComponents_exists_profinite
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z)
    :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := by
  let _ : T2Space (ConnectedComponents X) :=
    ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen hcomponents
  exact ⟨Profinite.of (ConnectedComponents X), ⟨Homeomorph.refl _⟩⟩

end
