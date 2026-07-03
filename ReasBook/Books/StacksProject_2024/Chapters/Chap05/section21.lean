import Mathlib.Tactic.Recall
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.OpenQuotient

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_21_1 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

/- 
Domain-style sampling for interior and nowhere dense subsets:
- owner declarations: `interior`, `IsNowhereDense`
- same-domain declarations inspected: `interior_subset`, `interior_maximal`,
  `IsNowhereDense`

Layer triage:
- `source-facing`: the interior of a subset and the nowhere dense predicate on a subset
- `core/canonical`: `interior`, `IsNowhereDense`
- `bridge/view`: the largest-open-subset characterization via `interior_subset` and
  `interior_maximal`

Primitive data is only the subset `T`. The maximality property of the interior is derived API from
the owner operator `interior`, so this file should directly recall the canonical owners and their
built-in companion theorems rather than introducing any local wrapper definitions or aliases.
-/

/- Definition 5.21.1 (1): for a subset `T ⊆ X`, its interior is the canonical set `interior T`. -/
recall interior

/- Companion recall: `interior T` is contained in `T`. -/
recall interior_subset

/- Companion recall: every open subset of `T` is contained in `interior T`, so `interior T` is the
largest open subset of `X` contained in `T`. -/
recall interior_maximal

/- Definition 5.21.1 (2): the Stacks notion of a nowhere dense subset is the canonical predicate
`IsNowhereDense`, defined by `interior (closure T) = ∅`. -/
recall IsNowhereDense

/-! ### Lemma_5_21_2 (from Chap05) -/
open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for finite unions of nowhere dense subsets:
- primary domain: general topology of nowhere dense subsets
- sampled owner-level declarations:
  `isNowhereDense_empty`,
  `IsNowhereDense`,
  `IsNowhereDense.closure`,
  `isClosed_isNowhereDense_iff_compl`
- best owner abstraction: `IsNowhereDense`, with finite-union API living in its namespace
- primitive data: a finite family of subsets together with pointwise `IsNowhereDense` hypotheses
- derived API: the finite `sUnion` theorem below; the closed/dense-complement reformulation is a
  proof tool, not primitive public data

Layer triage:
- `source-facing`: finite unions of nowhere dense subsets
- `core/canonical`: `IsNowhereDense`
- `bridge/view`: the dense-open-complement reformulation used in the proof
-/

namespace IsNowhereDense

/-- The union of two nowhere dense subsets is nowhere dense. -/
theorem union {s t : Set X} (hs : IsNowhereDense s) (ht : IsNowhereDense t) :
    IsNowhereDense (s ∪ t) := by
  -- Reinterpret the closures of `s` and `t` via dense open complements.
  have hs' := (isClosed_isNowhereDense_iff_compl).mp ⟨isClosed_closure, hs.closure⟩
  have ht' := (isClosed_isNowhereDense_iff_compl).mp ⟨isClosed_closure, ht.closure⟩
  -- It is enough to prove nowhere denseness for the union of the closures.
  refine (((isClosed_isNowhereDense_iff_compl).mpr ?_).2).mono
    (union_subset_union subset_closure subset_closure)
  -- The complement of the union is the intersection of the two dense open complements.
  rw [compl_union]
  exact ⟨hs'.1.inter ht'.1, hs'.2.inter_of_isOpen_right ht'.2 ht'.1⟩

/-- Lemma 5.21.2: the union of finitely many nowhere dense subsets of a topological space is
nowhere dense. -/
-- Proof sketch: induct on the finite family of subsets; the empty union is nowhere dense, and the
-- inductive step reduces to the binary union theorem.
theorem sUnion {S : Set (Set X)} (hS : S.Finite)
    (h : ∀ s ∈ S, IsNowhereDense s) :
    IsNowhereDense (⋃₀ S) := by
  -- Induct on the finite family and reduce the insert step to the binary union theorem.
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp
  | insert _ _ ih =>
      simp only [forall_mem_insert, sUnion_insert] at h ⊢
      exact h.1.union (ih h.2)

end IsNowhereDense

/-! ### Lemma_5_21_3 (from Chap05) -/
/- Domain-style sampling for nowhere dense subsets and subspace inclusions:
- owner declaration: `IsNowhereDense.image_val`
- same-domain declarations inspected:
  `IsNowhereDense`,
  `Topology.IsInducing.isNowhereDense_image`,
  `IsOpenMap.isNowhereDense_preimage`
- target layer here: `bridge/view`, since Lemma 5.21.3 is just the open-subspace specialization of
  the owner theorem for the subtype map `Subtype.val : U → X`

Primitive data is only the nowhere dense subset of the subspace. The openness of `U` from the
textbook wording is derived, not used by the canonical theorem, so it should not remain as public
API data here.
-/

/- Lemma 5.21.3: this is the open-subspace specialization of the canonical theorem
`IsNowhereDense.image_val`, whose statement is stronger because it applies to an arbitrary
subspace. -/
recall IsNowhereDense.image_val

/-! ### Lemma_5_21_4 (from Chap05) -/
open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for nowhere dense locality on open covers:
- primary domain: general topology of nowhere dense subsets and open-cover locality
- owner abstraction for a fixed cover: `TopologicalSpace.IsOpenCover`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_mem`,
  `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`,
  `Opens.isOpenEmbedding'`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`

Layer triage:
- `source-facing`: `isNowhereDense_of_isOpenCover`
- `core/canonical`: `IsNowhereDense`
- `bridge/view`: restriction to the open subspaces `U i`

Primitive data is only the subset `T`; the local subspace statements are derived from the owner
predicate by restricting along the subtype maps of the cover members. The owner-level theorem on
`TopologicalSpace.IsOpenCover` should therefore remain the main API, and the textbook one-way
statement should be a thin consequence.
-/

namespace TopologicalSpace.IsOpenCover

/-- Helper for Lemma 5.21.4: restricting `interior (closure T)` to an open subspace matches the
interior of the closure of the restricted set. -/
private theorem preimage_interior_closure_eq {U : Opens X} {T : Set X} :
    (((Subtype.val) : U → X) ⁻¹' interior (closure T) : Set U) =
      interior (closure (((Subtype.val) : U → X) ⁻¹' T)) := by
  let hopen : IsOpenMap ((↑) : U → X) := U.isOpenEmbedding'.isOpenMap
  -- Pull interior and closure through the subtype map of the open subspace.
  calc
    Subtype.val ⁻¹' interior (closure T)
        = interior (Subtype.val ⁻¹' closure T) := by
            simpa using
              hopen.preimage_interior_eq_interior_preimage continuous_subtype_val (closure T)
    _ = interior (closure (Subtype.val ⁻¹' T)) := by
          simpa using congrArg interior
            (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val T)

variable {ι : Type v} {U : ι → Opens X} {T : Set X}

/-- Nowhere density is local on an open cover. -/
theorem isNowhereDense_iff_coe_preimage (hU : IsOpenCover U) :
    IsNowhereDense T ↔ ∀ i, IsNowhereDense (((Subtype.val) : U i → X) ⁻¹' T) := by
  constructor
  · intro hT i
    -- Restrict the global empty-interior statement to each open member of the cover.
    simpa [IsNowhereDense, preimage_interior_closure_eq] using
      congrArg (preimage ((Subtype.val) : U i → X)) hT
  · intro hT
    -- If a point lay in `interior (closure T)`, some cover member would inherit a contradiction.
    rw [IsNowhereDense]
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have hTi : (((Subtype.val) : U i → X) ⁻¹' interior (closure T) : Set (U i)) = ∅ := by
      rw [preimage_interior_closure_eq]
      simpa [IsNowhereDense] using hT i
    have hx' : (⟨x, hi⟩ : U i) ∈
        (((Subtype.val) : U i → X) ⁻¹' interior (closure T) : Set (U i)) := by
      simpa using hx
    rw [hTi] at hx'
    exact hx'

end TopologicalSpace.IsOpenCover

-- Proof sketch: if `interior (closure T)` were nonempty, some cover member `U i` would meet it.
-- Intersecting with that open set identifies the resulting open subset with an open subset of the
-- closure of `Subtype.val ⁻¹' T` inside the subspace `U i`, contradicting the nowhere denseness
-- assumption there.
/-- Lemma 5.21.4: if an open cover of `X` restricts a subset `T` to a nowhere dense subset on
each member, then `T` is nowhere dense in `X`. -/
theorem isNowhereDense_of_isOpenCover
    {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) {T : Set X}
    (hT : ∀ i, IsNowhereDense (((↑) : U i → X) ⁻¹' T)) :
    IsNowhereDense T :=
  -- The owner-level equivalence already identifies global nowhere density with local nowhere
  -- density on each member of the open cover.
  (hU.isNowhereDense_iff_coe_preimage).2 hT

/-! ### Lemma_5_21_5 (from Chap05) -/
universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for nowhere dense images:
- primary domain: general topology of nowhere dense subsets under inducing maps
- sampled owner-level declarations:
  `Topology.IsInducing.isNowhereDense_image`,
  `Topology.IsClosedEmbedding.isInducing`,
  `IsNowhereDense.image_val`,
  `IsHomeomorph.isClosedEmbedding`
- best owner abstraction: `Topology.IsInducing.isNowhereDense_image`
- primitive data: a map together with the owner hypothesis `IsInducing`, and a nowhere dense
  subset of the source
- derived API: closed-embedding and subtype specializations obtained by passing to inducing maps

Layer triage:
- `source-facing`: nowhere dense images under a homeomorphism onto a closed subset
- `core/canonical`: `Topology.IsInducing.isNowhereDense_image`
- `bridge/view`: `Topology.IsClosedEmbedding.isInducing`
-/

/- Lemma 5.21.5 is exactly the canonical owner theorem that nowhere dense subsets have nowhere
dense image under an inducing map. The stronger closed-embedding wording from the source is a
derived specialization, so this file recalls the owner result directly. -/
recall Topology.IsInducing.isNowhereDense_image

/-! ### Lemma_5_21_6 (from Chap05) -/
open Set Topology

universe u v

/-
Domain-style sampling for nowhere dense subsets under open and open quotient maps:
- primary domain: general topology of nowhere dense subsets and quotient/open maps
- sampled owner-level declarations:
  `isClosed_isNowhereDense_iff_compl`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`,
  `IsOpenMap.preimage_interior_eq_interior_preimage`,
  `IsOpenQuotientMap.dense_preimage_iff`
- best owner abstractions: `IsOpenMap` for backward preservation of nowhere denseness, and
  `IsOpenQuotientMap` for the quotient-level equivalence
- primitive data: a map with the owner hypothesis and a subset `T`
- derived API: the bundled `IsClosed ∧ IsNowhereDense` forms, since closedness comes from
  `Continuous.preimage` and nowhere denseness is transported either by the owner-level
  closure/interior formulas or, for quotient maps, by dense complements

Layer triage:
- `core/canonical`: the owner-namespace theorems below on `IsOpenMap` and `IsOpenQuotientMap`
- `bridge/view`: the final surjective-open-continuous restatement, which packages the owner
  hypothesis in the source wording from earlier chapter items
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace IsOpenMap

variable {T : Set Y}

/-- Canonical owner-level form: for a continuous open map, the preimage of a nowhere dense subset
is nowhere dense. -/
theorem isNowhereDense_preimage
    (hf : IsOpenMap f) (hcont : Continuous f) (hT : IsNowhereDense T) :
    IsNowhereDense (f ⁻¹' T) := by
  rw [IsNowhereDense]
  calc
    interior (closure (f ⁻¹' T))
        = interior (f ⁻¹' closure T) := by
            rw [hf.preimage_closure_eq_closure_preimage hcont]
    _ = f ⁻¹' interior (closure T) := by
          rw [hf.preimage_interior_eq_interior_preimage hcont]
    _ = ∅ := by simpa [IsNowhereDense] using congrArg (preimage f) hT

/-- Owner-level closedness transport for preimages of continuous maps. -/
theorem isClosed_preimage (hcont : Continuous f) (hT : IsClosed T) :
    IsClosed (f ⁻¹' T) :=
  hT.preimage hcont

end IsOpenMap

namespace IsOpenQuotientMap

variable {T : Set Y}

/-- Canonical owner-level form: for an open quotient map, a subset of the target is nowhere dense
if and only if its preimage is nowhere dense. -/
theorem isNowhereDense_iff_preimage
    (hf : IsOpenQuotientMap f) :
    IsNowhereDense T ↔ IsNowhereDense (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hf.isOpenMap.isNowhereDense_preimage hf.continuous hT
  · intro hT
    have hpreimage_closure :
        f ⁻¹' closure T = closure (f ⁻¹' T) :=
      hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous T
    have hDensePreimage : Dense (f ⁻¹' (closure T)ᶜ) := by
      simpa [preimage_compl, hpreimage_closure]
        using
          (isClosed_isNowhereDense_iff_compl.mp
            ⟨isClosed_closure, hT.closure⟩).2
    have hDense : Dense (closure T)ᶜ :=
      (hf.dense_preimage_iff).1 hDensePreimage
    exact
      ((isClosed_isNowhereDense_iff_compl.mpr ⟨isClosed_closure.isOpen_compl, hDense⟩).2).mono
        subset_closure

/-- Owner-level closedness equivalence for open quotient maps. -/
theorem isClosed_iff_preimage (hf : IsOpenQuotientMap f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := by
  let hq : IsQuotientMap f := hf.isQuotientMap
  rw [hq.isClosed_preimage.symm]

end IsOpenQuotientMap

/-- Lemma 5.21.6 (1): for a surjective continuous open map, a subset is closed if and only if its
preimage is closed. -/
theorem isClosed_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsClosed T ↔ IsClosed (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isClosed_iff_preimage

/-- Lemma 5.21.6 (2): for a surjective continuous open map, a subset is nowhere dense if and only
if its preimage is nowhere dense. -/
theorem isNowhereDense_iff_preimage_of_surjective_open
    (hcont : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) {T : Set Y} :
    IsNowhereDense T ↔ IsNowhereDense (f ⁻¹' T) :=
  (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap f).isNowhereDense_iff_preimage

end
