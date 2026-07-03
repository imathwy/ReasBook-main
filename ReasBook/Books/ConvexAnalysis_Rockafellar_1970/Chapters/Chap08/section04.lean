import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_4_1 (from Chap02) -/
section

universe u v

open scoped Affine
open Bornology

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.4.1 says that for a closed convex set `C`, boundedness of the
  section `M ∩ C` depends only on the parallel class of the affine set `M`.
- `core/canonical`: the owner abstractions are the chapter recession-cone owner `recessionCone`,
  the affine-set object `AffineSubspace 𝕜 E`, its parallelism relation
  `AffineSubspace.Parallel`, and the bornological boundedness predicate `IsBounded`.
- `bridge/view`: the core owner theorem here is the recession-cone identity for affine sections,
  proved directly via `Set.mem_recessionCone_iff`, affine-direction lemmas, and the owner-level
  positive-ray bridge `Convex.mem_recessionCone_of_pos_ray`. The boundedness corollary is then a
  thin specialization through `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- Domain-style sampling used here: `Set.mem_recessionCone_iff`,
  `Convex.mem_recessionCone_of_pos_ray`,
  `AffineSubspace.vadd_mem_iff_mem_direction`,
  `AffineSubspace.vadd_mem_of_mem_direction`, and
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- Primitive data vs derived API: the primitive inputs are the closed convex set `C` and the affine
  subspaces `M` and `M'`; the triviality of the recession cone of a section and the resulting
  boundedness are derived API.
- Layer target: the recession-cone owner theorem is moved to the weaker ordered topological vector
  space layer (`𝕜`, `E`), while the boundedness transfer is stated at the primitive closed-section
  layer (`IsClosed (M : Set E)`, `IsClosed (M' : Set E)`) over the proper normed scalar/ambient
  assumptions forced by the upstream theorem
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
-/

namespace AffineSubspace

local notation:70 M " ∩ₛ " C => ((M : Set E) ∩ C)

private lemma recessionCone_inter_eq_direction_inter_of_nonempty
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (N : AffineSubspace 𝕜 E)
    (hNC_nonempty : (N ∩ₛ C).Nonempty) :
    0⁺[𝕜] (N ∩ₛ C) = (N.direction : Set E) ∩ 0⁺[𝕜] C := by
  ext y
  constructor
  · intro hy
    rcases hNC_nonempty with ⟨x, hx⟩
    have hxN : x ∈ N := hx.1
    rw [Set.mem_recessionCone_iff] at hy
    have hy_dir : y ∈ N.direction := by
      have hxyN : x + (1 : 𝕜) • y ∈ N := (hy x hx 1 zero_le_one).1
      have hxyv : y +ᵥ x ∈ N := by
        simpa [vadd_eq_add, add_comm, one_smul] using hxyN
      exact (N.vadd_mem_iff_mem_direction y hxN).1 hxyv
    have hy_recession_C : y ∈ 0⁺[𝕜] C := by
      exact hC_convex.mem_recessionCone_of_pos_ray (x := x) hC_closed hx.2
        (fun a ha ↦ (hy x hx a ha.le).2)
    exact ⟨hy_dir, hy_recession_C⟩
  · rintro ⟨hy_dir, hy_recession_C⟩
    rw [Set.mem_recessionCone_iff] at hy_recession_C ⊢
    intro x hx a ha
    have hxyN : x + a • y ∈ N := by
      have hsmul_dir : a • y ∈ N.direction := N.direction.smul_mem a hy_dir
      have hxyv : (a • y) +ᵥ x ∈ N := N.vadd_mem_of_mem_direction hsmul_dir hx.1
      simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxyv
    exact ⟨hxyN, hy_recession_C x hx.2 a ha⟩

/-- For a closed convex set `C`, nonempty parallel affine sections have equal recession cones. -/
theorem recessionCone_inter_eq_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_nonempty : (M ∩ₛ C).Nonempty)
    (hM'C_nonempty : (M' ∩ₛ C).Nonempty)
    (hparallel : M' ∥ M) :
    0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) := by
  calc
    0⁺[𝕜] (M' ∩ₛ C) = (M'.direction : Set E) ∩ 0⁺[𝕜] C :=
      recessionCone_inter_eq_direction_inter_of_nonempty C hC_closed hC_convex M' hM'C_nonempty
    _ = (M.direction : Set E) ∩ 0⁺[𝕜] C := by
      simp [hparallel.direction_eq]
    _ = 0⁺[𝕜] (M ∩ₛ C) := by
      symm
      exact recessionCone_inter_eq_direction_inter_of_nonempty C hC_closed hC_convex M hMC_nonempty

end AffineSubspace

end

section

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]

open scoped Affine
open Bornology

namespace AffineSubspace

local notation:70 M " ∩ₛ " C => ((M : Set E) ∩ C)

/-- For a closed convex set `C`, nonempty parallel closed affine sections are bounded
simultaneously. -/
theorem isBounded_inter_iff_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_closed : IsClosed (M ∩ₛ C)) (hM'C_closed : IsClosed (M' ∩ₛ C))
    (hMC_nonempty : (M ∩ₛ C).Nonempty) (hM'C_nonempty : (M' ∩ₛ C).Nonempty)
    (hparallel : M' ∥ M) :
    IsBounded (M' ∩ₛ C) ↔ IsBounded (M ∩ₛ C) := by
  have hM_recession :
      IsBounded (M ∩ₛ C) ↔ 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) :=
    (M.convex.inter hC_convex).isBounded_iff_recessionCone_eq_singleton_zero
      hMC_closed hMC_nonempty
  have hM'_recession :
      IsBounded (M' ∩ₛ C) ↔ 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) :=
    (M'.convex.inter hC_convex).isBounded_iff_recessionCone_eq_singleton_zero
      hM'C_closed hM'C_nonempty
  have hparallel_recession :
      0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) :=
    AffineSubspace.recessionCone_inter_eq_of_parallel C hC_closed hC_convex M M'
      hMC_nonempty hM'C_nonempty hparallel
  constructor
  · intro hM'_bounded
    have hM'_recession_zero : 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) := hM'_recession.mp hM'_bounded
    have hM_recession_zero : 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) := by
      calc
        0⁺[𝕜] (M ∩ₛ C) = 0⁺[𝕜] (M' ∩ₛ C) := hparallel_recession.symm
        _ = ({0} : Set E) := hM'_recession_zero
    exact hM_recession.mpr hM_recession_zero
  · intro hM_bounded
    have hM_recession_zero : 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) := hM_recession.mp hM_bounded
    have hM'_recession_zero : 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) := by
      calc
        0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) := hparallel_recession
        _ = ({0} : Set E) := hM_recession_zero
    exact hM'_recession.mpr hM'_recession_zero

-- Proof sketch: if `M' ∩ C` is empty, it is bounded. Otherwise Theorem 8.4 reduces boundedness of
-- both sections to triviality of their recession cones. The owner theorem
-- `AffineSubspace.recessionCone_inter_eq_of_parallel` identifies these two recession cones under
-- parallelism, so boundedness of `M ∩ C` forces boundedness of `M' ∩ C`.
/-- Corollary 8.4.1 (owner form): if `C` is a closed convex set, `M ∩ C` is nonempty and bounded,
and `M'` is parallel to `M`, then `M' ∩ C` is bounded as soon as both affine sections are closed.
The textbook finite-dimensional `ℝ^n` statement is recovered by specializing to that ambient
layer, where affine subspaces are automatically closed. -/
theorem isBounded_inter_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_closed : IsClosed (M ∩ₛ C)) (hM'C_closed : IsClosed (M' ∩ₛ C))
    (hMC_nonempty : (M ∩ₛ C).Nonempty)
    (hMC_bdd : IsBounded (M ∩ₛ C)) (hparallel : M' ∥ M) :
    IsBounded (M' ∩ₛ C) := by
  by_cases hM'C_nonempty : (M' ∩ₛ C).Nonempty
  · exact
      (isBounded_inter_iff_of_parallel C hC_closed hC_convex M M' hMC_closed hM'C_closed
        hMC_nonempty hM'C_nonempty hparallel).2 hMC_bdd
  · have hM'C_empty : (M' ∩ₛ C) = ∅ := Set.not_nonempty_iff_eq_empty.mp hM'C_nonempty
    simp [hM'C_empty]

end AffineSubspace

end

/-! ### Definition_8_4_2 (from Chap02) -/
section

universe u v w

open scoped Pointwise

variable {P : Type u} {E : Type v} [Neg E]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.2 introduces the lineality space of a set `C`, namely the
  symmetric recession-direction set `(-0⁺[𝕜] C) ∩ 0⁺[𝕜] C`.
- `core/canonical`: the chapter owner abstraction in this domain is the generic scalar-parameterized
  recession cone `0⁺[𝕜] C`; the lineality space is therefore defined directly from that primitive
  owner in canonical conjunction order `0⁺[𝕜] C ∩ -0⁺[𝕜] C`.
- `bridge/view`: the companion theorems `mem_lineal_iff`,
  `mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`, and
  `mem_lineal_iff_forall` unpack the source-facing owner into symmetric recession membership and
  then into the textbook ray
  quantifiers.
- Primitive data vs derived API: the primitive owner data are exactly the two recession conditions
  encoded by `0⁺[𝕜] C ∩ -0⁺[𝕜] C`; the quantifier expansion is derived API. No convexity,
  nonemptiness, or bundled-cone structure is primitive here.
- Layer target: this file provides the `source-facing` owner object on `Set`, not a second bundled
  cone abstraction.

Domain-style sampling used here:
- the owner declaration `Set.recessionCone` from Definition 8.0.2;
- the owner-side membership bridge `Set.mem_recessionCone_iff`.
-/

namespace Set

/-- Definition 8.4.2: the lineality set of `C`, i.e. the symmetric recession-direction set
`0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
def lineal (𝕜 : Type w) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P] (C : Set P) : Set E :=
  0⁺[𝕜] C ∩ -0⁺[𝕜] C

scoped[Rockafellar] notation "lin[" 𝕜 "](" C ")" => Set.lineal 𝕜 C

open scoped Rockafellar

variable {𝕜 : Type w} [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P]

/-- Canonical membership bridge: `y ∈ lin[𝕜](C)` iff both `y` and `-y` are recession directions
of `C`. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone_and_mem_neg_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ y ∈ -0⁺[𝕜] C := by
  simp [Set.lineal]

/-- Compatibility bridge from owner-level negated-cone membership to element-level negation. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ -y ∈ 0⁺[𝕜] C := by
  simp [Set.mem_neg, mem_lineal_iff_mem_recessionCone_and_mem_neg_recessionCone]

/-- Canonical membership bridge: conjunction order follows
`lin[𝕜](C) = 0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
@[simp] theorem mem_lineal_iff {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ -y ∈ 0⁺[𝕜] C :=
  mem_lineal_iff_mem_recessionCone

/-- Unfolding bridge: `lin[𝕜](C)` is definitionally the canonical owner expression
`0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
theorem lineal_eq_recessionCone_inter_neg_recessionCone (C : Set P) :
    lin[𝕜](C) = ((0⁺[𝕜] C) ∩ (-0⁺[𝕜] C) : Set E) :=
  rfl

/-- Canonicalization bridge: the raw owner expression `0⁺[𝕜] C ∩ -0⁺[𝕜] C` rewrites to
`lin[𝕜](C)`. -/
theorem recessionCone_inter_neg_recessionCone_eq_lineal (C : Set P) :
    ((0⁺[𝕜] C) ∩ (-0⁺[𝕜] C) : Set E) = lin[𝕜](C) :=
  rfl

/-- Source-order compatibility bridge with the source-facing `(−y, y)` conjunction order. -/
theorem mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ -y ∈ 0⁺[𝕜] C ∧ y ∈ 0⁺[𝕜] C := by
  rw [mem_lineal_iff, and_comm]

/-- The source-facing textbook formula for the lineality space is the intersection of the negative
and positive recession cones. -/
theorem lineal_eq_neg_recessionCone_inter_recessionCone (C : Set P) :
    lin[𝕜](C) = (-0⁺[𝕜] C ∩ 0⁺[𝕜] C : Set E) :=
  by
    ext y
    simp [Set.lineal, and_comm]

/-- Membership in `lin[𝕜](C)` means that both `y` and `-y` are recession directions of `C`,
expanded into the textbook ray-preservation quantifiers. -/
theorem mem_lineal_iff_forall {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔
      (∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • (-y) ∈ C) ∧
        ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C := by
  simpa [Set.mem_recessionCone_iff] using
    (mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone (𝕜 := 𝕜) (C := C) (y := y))

end Set

end

/-! ### Definition_8_4_3 (from Chap02) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.3 gives textbook terminology for vectors lying in the lineality
  space of `C`.
- `core/canonical`: in this chapter's local API, the owner object is the short canonical
  scalar-parameterized set owner `Set.lineal 𝕜 C`, written on theorem surfaces as `lin[𝕜](C)`.
- `bridge/view`: the relevant companion APIs are the canonical owner-membership bridge
  `Set.mem_lineal_iff_mem_recessionCone`, the canonical
  element-level compatibility bridge `Set.mem_lineal_iff`, its source-order compatibility view
  `Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`, and the textbook quantifier
  form `Set.mem_lineal_iff_forall`.
- Primitive data vs derived API: this item adds no new primitive data beyond the owner set from
  Definition 8.4.2, so it should be a direct recall/use of that owner rather than a parallel
  predicate alias.
- Layer target: this file stays `source-facing`, but only as terminology attached to the existing
  owner declaration.

Domain-style sampling used here:
- the immediately upstream owner `Set.lineal` from Definition 8.4.2;
- its canonical element-level membership bridge `Set.mem_lineal_iff_mem_recessionCone`;
- its canonical membership bridge `Set.mem_lineal_iff`;
- its source-order compatibility bridge
  `Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`;
- the textbook quantifier expansion `Set.mem_lineal_iff_forall`.
- this numbered item only recalls owner terminology from Definition 8.4.2, so its canonical
  surface lives on the minimal scalar-parameterized additive layer.
-/

/- Definition 8.4.3: a vector is a direction in which `C` is linear precisely when it belongs to
the previously defined owner set `lin[𝕜](C)` (that is, `Set.lineal 𝕜 C`). -/
recall Set.lineal

/- The canonical element-level membership bridge: membership in `lin[𝕜](C)` means both `y`
and `-y` are recession directions of `C`. -/
recall Set.mem_lineal_iff_mem_recessionCone

/- The textbook wording is unpacked by the standard canonical membership characterization of
`lin[𝕜](C)`. -/
recall Set.mem_lineal_iff

/- Source-order compatibility view used in nearby source-facing statements. -/
recall Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone

/- The fully unpacked source wording is the quantifier form of lineality membership. -/
recall Set.mem_lineal_iff_forall

/-! ### Definition_8_4_4 (from Chap02) -/
noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.4 names the lineality of a set as the dimension of its
  lineality space.
- `core/canonical`: the owner abstractions already present upstream are `Set.lineal` (written as
  `lin[𝕜](C)`) from
  Definition 8.4.2 and the affine-dimension owner `Set.affineDim` from Definition 2.4.10.
- `bridge/view`: lineality is only the numerical composite of those two owners, so it should be a
  thin abbreviation rather than a new wrapper structure or a second set-side lineality package.
- `primitive data`: the primitive owner remains the scalar-parameterized set
  `Set.lineal 𝕜 C`.
- `derived API`: the scalar invariant `Set.lineality 𝕜 C`.

Domain-style sampling used here:
- `Set.lineal` / `lin[𝕜](C)` from Definition 8.4.2;
- `Set.affineDim` from Definition 2.4.10;
- the parallel function-side invariant `ConvexERealFunction.lineality` from Definition 8.9.2,
  which is likewise a thin affine-dimension composite.

Primitive data vs derived API:
- primitive owner data: the set `Set.lineal 𝕜 C`;
- derived API: its affine dimension, exposed as `Set.lineality 𝕜 C`.

Layer target: `bridge/view`, reusing the existing owner abstractions directly.
-/

namespace Set

open scoped Rockafellar

variable (𝕜 : Type*) [DivisionRing 𝕜] [LE 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {P : Type*} [HAdd P E P]

/-- Definition 8.4.4: the lineality of a set is the affine dimension of its lineality space. -/
abbrev lineality (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] : ℤ :=
  dim[𝕜](Set.lineal (E := E) 𝕜 C)

scoped[Rockafellar] notation (name := setLinealityNotation_8_4_4)
    "lineality[" 𝕜 "](" C ")" => Set.lineality 𝕜 C
scoped[Rockafellar] notation (name := setLinealityNotationAmbient_8_4_4)
    "lineality[" 𝕜 "," ambient "](" C ")" => Set.lineality (E := ambient) 𝕜 C

/-- The lineality of a set is the affine dimension of its lineality space. -/
theorem lineality_eq (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    Set.lineality (E := E) 𝕜 C = dim[𝕜](Set.lineal (E := E) 𝕜 C) :=
  rfl

/-- Owner-level expansion: lineality is the affine dimension of the affine span of `lin[𝕜](C)`. -/
theorem lineality_eq_affineSpan_affineDim (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).direction] :
    Set.lineality (E := E) 𝕜 C = (affineSpan 𝕜 (Set.lineal (E := E) 𝕜 C)).affineDim :=
  rfl

end Set

/-! ### Theorem_8_4 (from Chap02) -/
section

universe u

open Bornology Filter Topology

/-
Source/core/bridge triage:
- `source-facing`: Theorem 8.4 states that a nonempty closed convex set `C` is bounded if
  and only if its recession cone `0⁺[𝕜] C` is trivial.
- `core/canonical`: the canonical owner-side boundedness API is `Bornology.IsBounded C`, and
  mathlib's direct boundedness criterion is stated on `asymptoticCone ℝ C`.
- `bridge/view`: this file exposes that canonical real asymptotic-cone criterion directly and
  then promotes the nonempty closed-convex statement to the scalar-`𝕜` asymptotic-cone owner
  before deriving the source-facing recession-cone bridge surface.
- Domain-style sampling: `recessionCone`,
  `isBounded_iff_asymptoticCone_subset_singleton`, `asymptoticCone_nonempty`,
  `Set.mem_recessionCone_iff`, and
  `Set.Nonempty.subset_singleton_iff`.
- Primitive data vs derived API: the primitive inputs are the set `C` and the source hypotheses
  that `C` is nonempty, closed, and convex; boundedness and triviality of the recession cone are
  the two equivalent derived properties.
- Abstraction-check answers:
  - codomain/ambient: no `EReal`-style codomain owner appears in this item; the ambient owner
    for the canonical boundedness criterion is `asymptoticCone ℝ`.
  - owner choice: the canonical owner theorem is exposed directly at the asymptotic-cone layer,
    and the source owner `0⁺[𝕜] C` is kept as a chapter-facing bridge surface.
  - intrinsic/relative topology: the source statement is not an ambient-vs-relative closure
    theorem; ambient `IsClosed C` remains part of the source-facing bridge surface.
- Layer target: expose the canonical asymptotic-cone subset criterion and its nonempty equality
  corollary at the owner layer, keep the recession-cone subset theorem as its source-facing bridge,
  and expose the source-facing equality as a thin corollary.
-/

namespace Convex

section Canonical

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- Canonical owner form for Theorem 8.4 at mathlib's asymptotic-cone layer.

This boundedness criterion is currently available in mathlib on the real asymptotic-cone API. -/
theorem isBounded_iff_asymptoticCone_subset_singleton_zero (C : Set P) :
    IsBounded C ↔ asymptoticCone ℝ C ⊆ ({0} : Set V) := by
  simpa using (isBounded_iff_asymptoticCone_subset_singleton (s := C))

/-- Nonempty-set equality corollary of the canonical asymptotic-cone owner criterion. -/
theorem isBounded_iff_asymptoticCone_eq_singleton_zero (C : Set P) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone ℝ C = ({0} : Set V) := by
  have hcone_nonempty : (asymptoticCone ℝ C).Nonempty :=
    (asymptoticCone_nonempty (k := ℝ) (s := C)).2 hC_nonempty
  exact (isBounded_iff_asymptoticCone_subset_singleton_zero (C := C)).trans
    hcone_nonempty.subset_singleton_iff

end Canonical

section SourceFacing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [ProperSpace E]
variable {C : Set E}

/-- Nonempty-case helper for the scalar-`𝕜` asymptotic-cone boundedness criterion. -/
private theorem isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex_nonempty
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  have not_isBounded_range_add_natCast_smul (x y : E) (hy : y ≠ 0) :
      ¬ IsBounded (Set.range fun n : ℕ => x + (n : 𝕜) • y) := by
    intro hbounded
    obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
    have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
    have hnorm : ‖x + (n : 𝕜) • y‖ ≤ R := by
      have hxR : x + (n : 𝕜) • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
    have hny : ‖(n : 𝕜)‖ * ‖y‖ ≤ R + ‖x‖ := by
      calc
        ‖(n : 𝕜)‖ * ‖y‖ = ‖(n : 𝕜) • y‖ := by
          simpa using (norm_smul (n : 𝕜) y).symm
        _ = ‖(x + (n : 𝕜) • y) - x‖ := by simp
        _ ≤ ‖x + (n : 𝕜) • y‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
    have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
    have hgt : R + ‖x‖ < ‖(n : 𝕜)‖ * ‖y‖ := by
      calc
        R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
        _ = ‖(n : 𝕜)‖ * ‖y‖ := by simp [norm_natCast]
    exact not_lt_of_ge hny hgt
  constructor
  · intro hC_bounded
    intro v hv
    by_contra hv0
    have hv_recession : v ∈ (0⁺[𝕜] C : Set E) := by
      simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using hv
    rcases hC_nonempty with ⟨x0, hx0⟩
    have hrange_subset : Set.range (fun n : ℕ => x0 + (n : 𝕜) • v) ⊆ C := by
      rintro _ ⟨n, rfl⟩
      exact (Set.mem_recessionCone_iff.mp hv_recession) x0 hx0 (n : 𝕜) (Nat.cast_nonneg n)
    exact
      not_isBounded_range_add_natCast_smul x0 v hv0
        (hC_bounded.subset hrange_subset)
  · intro hC_asymptotic_trivial
    by_contra hC_unbounded
    rcases hC_nonempty with ⟨x0, hx0⟩
    have h_unbounded_from_x0 : ∀ R : ℝ, ∃ x ∈ C, R < ‖x - x0‖ := by
      intro R
      by_contra hR
      push Not at hR
      apply hC_unbounded
      refine (isBounded_iff_forall_norm_le).2 ?_
      refine ⟨R + ‖x0‖, ?_⟩
      intro x hx
      calc
        ‖x‖ = ‖(x - x0) + x0‖ := by abel_nf
        _ ≤ ‖x - x0‖ + ‖x0‖ := norm_add_le _ _
        _ ≤ R + ‖x0‖ := add_le_add (hR x hx) le_rfl
    have hw : ∀ n : ℕ, ∃ x ∈ C, (n : ℝ) + 1 < ‖x - x0‖ := by
      intro n
      simpa using h_unbounded_from_x0 ((n : ℝ) + 1)
    choose w hwC hwgt using hw
    let r : ℕ → ℝ := fun n => ‖w n - x0‖ / ((n : ℝ) + 1)
    let m : ℕ → ℕ := fun n => Nat.floor (r n)
    let t : ℕ → 𝕜 := fun n => ((m n + 1 : ℕ) : 𝕜)⁻¹
    let y : ℕ → E := fun n => x0 + t n • (w n - x0)
    let a : ℕ → 𝕜 := fun n => ((n + 1 : ℕ) : 𝕜)
    let u : ℕ → E := fun n => (a n)⁻¹ • (y n - x0)
    have ht_nonneg : ∀ n : ℕ, 0 ≤ t n := by
      intro n
      dsimp [t]
      have hm1_pos : (0 : 𝕜) < (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_pos (m n)
      exact (inv_nonneg).2 hm1_pos.le
    have ht_le_one : ∀ n : ℕ, t n ≤ 1 := by
      intro n
      dsimp [t]
      have hm1_pos : (0 : 𝕜) < (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_pos (m n)
      have hcast_ge_one : (1 : 𝕜) ≤ (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m n))
      have h := (one_div_le_one_div hm1_pos zero_lt_one).2 hcast_ge_one
      simpa [one_div] using h
    have hy_mem : ∀ n : ℕ, y n ∈ C := by
      intro n
      have hy_combo : y n = (1 - t n) • x0 + t n • w n := by
        dsimp [y]
        calc
          x0 + t n • (w n - x0) = x0 + (t n • w n - t n • x0) := by
            simp [smul_sub]
          _ = (1 - t n) • x0 + t n • w n := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_smul, one_smul, smul_add]
      have hconv :
          (1 - t n) • x0 + t n • w n ∈ C :=
        hC_convex hx0 (hwC n) (sub_nonneg.mpr (ht_le_one n)) (ht_nonneg n) (by ring)
      simpa [hy_combo] using hconv
    have ha_nonzero : ∀ n : ℕ, a n ≠ 0 := by
      intro n
      dsimp [a]
      exact_mod_cast Nat.succ_ne_zero n
    have ha_norm : ∀ n : ℕ, ‖a n‖ = (n : ℝ) + 1 := by
      intro n
      dsimp [a]
      simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (n + 1))
    have hu_mem : ∀ n : ℕ, a n • u n +ᵥ x0 ∈ C := by
      intro n
      have ha_ne : a n ≠ 0 := ha_nonzero n
      have hu_eq_smul : a n • u n = y n - x0 := by
        dsimp [u]
        calc
          a n • ((a n)⁻¹ • (y n - x0)) = (a n * (a n)⁻¹) • (y n - x0) := by
            simp [smul_smul]
          _ = (1 : 𝕜) • (y n - x0) := by rw [mul_inv_cancel₀ ha_ne]
          _ = y n - x0 := by simp
      have hu_eq : a n • u n +ᵥ x0 = y n := by
        calc
          a n • u n +ᵥ x0 = (y n - x0) +ᵥ x0 := by simpa [hu_eq_smul]
          _ = y n := by simpa [vadd_eq_add, sub_eq_add_neg, add_assoc]
      exact hu_eq ▸ hy_mem n
    have hu_lower : ∀ n : ℕ, (1 / 2 : ℝ) ≤ ‖u n‖ := by
      intro n
      have hden_pos : 0 < (n : ℝ) + 1 := by positivity
      have hr_gt_one : 1 < r n := by
        dsimp [r]
        exact (lt_div_iff₀ hden_pos).2 (by simpa using hwgt n)
      have hr_nonneg : 0 ≤ r n := le_of_lt (lt_trans zero_lt_one hr_gt_one)
      have hm_le : (m n : ℝ) ≤ r n := Nat.floor_le hr_nonneg
      have hm1_pos : 0 < (m n : ℝ) + 1 := by positivity
      have hm1_lt_2r : (m n : ℝ) + 1 < 2 * r n := by
        have hm1_le_r1 : (m n : ℝ) + 1 ≤ r n + 1 := by linarith [hm_le]
        linarith [hm1_le_r1, hr_gt_one]
      have hhalf_lt_r : ((m n : ℝ) + 1) / 2 < r n := by
        linarith [hm1_lt_2r]
      have hhalf_mul_lt : (((m n : ℝ) + 1) / 2) * ((n : ℝ) + 1) < ‖w n - x0‖ := by
        have : (((m n : ℝ) + 1) / 2) < ‖w n - x0‖ / ((n : ℝ) + 1) := by
          simpa [r] using hhalf_lt_r
        exact (lt_div_iff₀ hden_pos).1 this
      have hdist_lower : ((n : ℝ) + 1) / 2 < ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have hhalf_mul_lt' : (((n : ℝ) + 1) / 2) * ((m n : ℝ) + 1) < ‖w n - x0‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hhalf_mul_lt
        exact (lt_div_iff₀ hm1_pos).2 hhalf_mul_lt'
      have hy_sub : y n - x0 = t n • (w n - x0) := by
        dsimp [y]
        simp
      have hy_norm :
          ‖y n - x0‖ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have ht_norm : ‖t n‖ = (((m n : ℝ) + 1)⁻¹) := by
          have hm1_norm : ‖((m n : 𝕜) + (1 : 𝕜))‖ = ((m n : ℝ) + 1) := by
            simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (m n + 1))
          calc
            ‖t n‖ = ‖((m n : 𝕜) + (1 : 𝕜))⁻¹‖ := by simp [t, Nat.cast_add]
            _ = ‖((m n : 𝕜) + (1 : 𝕜))‖⁻¹ := norm_inv _
            _ = (((m n : ℝ) + 1)⁻¹) := by rw [hm1_norm]
        calc
          ‖y n - x0‖ = ‖t n • (w n - x0)‖ := by simpa [hy_sub]
          _ = ‖t n‖ * ‖w n - x0‖ := norm_smul _ _
          _ = (((m n : ℝ) + 1)⁻¹) * ‖w n - x0‖ := by simpa [ht_norm]
          _ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by ring
      have hu_norm :
          ‖u n‖ = ‖y n - x0‖ / ((n : ℝ) + 1) := by
        calc
          ‖u n‖ = ‖(a n)⁻¹ • (y n - x0)‖ := by rfl
          _ = ‖(a n)⁻¹‖ * ‖y n - x0‖ := norm_smul _ _
          _ = ‖a n‖⁻¹ * ‖y n - x0‖ := by simp [norm_inv]
          _ = ‖y n - x0‖ / ‖a n‖ := by ring
          _ = ‖y n - x0‖ / ((n : ℝ) + 1) := by simp [ha_norm n]
      have hy_lower_le : ((n : ℝ) + 1) / 2 ≤ ‖y n - x0‖ := by
        exact le_of_lt (by simpa [hy_norm] using hdist_lower)
      have : (1 / 2 : ℝ) * ((n : ℝ) + 1) ≤ ‖y n - x0‖ := by
        nlinarith [hy_lower_le]
      have hfinal : (1 / 2 : ℝ) ≤ ‖y n - x0‖ / ((n : ℝ) + 1) := by
        exact (le_div_iff₀ hden_pos).2 this
      simpa [hu_norm] using hfinal
    have hu_upper : ∀ n : ℕ, ‖u n‖ < 1 := by
      intro n
      have hden_pos : 0 < (n : ℝ) + 1 := by positivity
      have hm1_pos : 0 < (m n : ℝ) + 1 := by positivity
      have hr_lt : r n < (m n : ℝ) + 1 := by
        simpa [m] using Nat.lt_floor_add_one (r n)
      have hmul : ‖w n - x0‖ < ((m n : ℝ) + 1) * ((n : ℝ) + 1) := by
        have : ‖w n - x0‖ / ((n : ℝ) + 1) < (m n : ℝ) + 1 := by
          simpa [r] using hr_lt
        exact (div_lt_iff₀ hden_pos).1 this
      have hdist_upper : ‖w n - x0‖ / ((m n : ℝ) + 1) < (n : ℝ) + 1 := by
        exact (div_lt_iff₀ hm1_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      have hy_sub : y n - x0 = t n • (w n - x0) := by
        dsimp [y]
        simp
      have hy_norm :
          ‖y n - x0‖ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have ht_norm : ‖t n‖ = (((m n : ℝ) + 1)⁻¹) := by
          have hm1_norm : ‖((m n : 𝕜) + (1 : 𝕜))‖ = ((m n : ℝ) + 1) := by
            simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (m n + 1))
          calc
            ‖t n‖ = ‖((m n : 𝕜) + (1 : 𝕜))⁻¹‖ := by simp [t, Nat.cast_add]
            _ = ‖((m n : 𝕜) + (1 : 𝕜))‖⁻¹ := norm_inv _
            _ = (((m n : ℝ) + 1)⁻¹) := by rw [hm1_norm]
        calc
          ‖y n - x0‖ = ‖t n • (w n - x0)‖ := by simpa [hy_sub]
          _ = ‖t n‖ * ‖w n - x0‖ := norm_smul _ _
          _ = (((m n : ℝ) + 1)⁻¹) * ‖w n - x0‖ := by simpa [ht_norm]
          _ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by ring
      have hu_norm :
          ‖u n‖ = ‖y n - x0‖ / ((n : ℝ) + 1) := by
        calc
          ‖u n‖ = ‖(a n)⁻¹ • (y n - x0)‖ := by rfl
          _ = ‖(a n)⁻¹‖ * ‖y n - x0‖ := norm_smul _ _
          _ = ‖a n‖⁻¹ * ‖y n - x0‖ := by simp [norm_inv]
          _ = ‖y n - x0‖ / ‖a n‖ := by ring
          _ = ‖y n - x0‖ / ((n : ℝ) + 1) := by simp [ha_norm n]
      have hy_lt : ‖y n - x0‖ < (n : ℝ) + 1 := by
        simpa [hy_norm] using hdist_upper
      have hfinal : ‖y n - x0‖ / ((n : ℝ) + 1) < 1 := by
        exact (div_lt_iff₀ hden_pos).2 (by simpa using hy_lt)
      simpa [hu_norm] using hfinal
    have hu_eventually_ball1 : ∀ᶠ n : ℕ in Filter.atTop, u n ∈ Metric.closedBall (0 : E) 1 := by
      exact Filter.Eventually.of_forall fun n ↦ by
        have hu_le : ‖u n‖ ≤ 1 := le_of_lt (hu_upper n)
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_le
    have hu_frequently_ball1 :
        ∃ᶠ n : ℕ in Filter.atTop, u n ∈ Metric.closedBall (0 : E) 1 :=
      hu_eventually_ball1.frequently
    obtain ⟨v, hv_ball2, hv_cluster⟩ :=
      (ProperSpace.isCompact_closedBall (x := (0 : E)) (r := 1)).exists_mapClusterPt_of_frequently
        hu_frequently_ball1
    have hu_eventually_half : ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) ≤ ‖u n‖ := by
      exact Filter.Eventually.of_forall hu_lower
    let S : Set E := {z : E | (1 / 2 : ℝ) ≤ ‖z‖}
    have hS_closed : IsClosed S := isClosed_le continuous_const continuous_norm
    have hv_memS : v ∈ S := by
      exact hS_closed.mem_of_mapClusterPt hv_cluster hu_eventually_half
    have hv_nonzero : v ≠ 0 := by
      have hv_norm_pos : 0 < ‖v‖ := by
        have hv_half : (1 / 2 : ℝ) ≤ ‖v‖ := hv_memS
        linarith
      exact norm_pos_iff.mp hv_norm_pos
    let l : Filter ℕ := Filter.atTop ⊓ Filter.comap u (𝓝 v)
    have hl_nebot : l.NeBot := by
      refine (Filter.neBot_inf_comap_iff_map).2 ?_
      simpa [l, MapClusterPt, ClusterPt, inf_comm] using hv_cluster
    haveI : l.NeBot := hl_nebot
    have ha_tendsto_atTop : Tendsto a Filter.atTop Filter.atTop := by
      simpa [a, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (tendsto_atTop_add_const_right Filter.atTop (1 : 𝕜)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : 𝕜)) Filter.atTop Filter.atTop))
    have h_a_tendsto : Tendsto a l Filter.atTop := ha_tendsto_atTop.mono_left inf_le_left
    have hu_tendsto : Tendsto u l (𝓝 v) := by
      show Filter.map u l ≤ 𝓝 v
      exact (Filter.map_le_iff_le_comap).2 inf_le_right
    have h_tendsto_asymptotic :
        Tendsto (fun n : ℕ => a n • u n +ᵥ x0) l (AffineSpace.asymptoticNhds 𝕜 E v) := by
      exact
        (h_a_tendsto.atTop_smul_nhds_tendsto_asymptoticNhds hu_tendsto).asymptoticNhds_vadd_const x0
    have hu_eventually_memC : ∀ᶠ n : ℕ in l, a n • u n +ᵥ x0 ∈ C := by
      exact Filter.Eventually.of_forall hu_mem
    have hv_asymptotic_mem : v ∈ asymptoticCone 𝕜 C := by
      rw [mem_asymptoticCone_iff]
      exact h_tendsto_asymptotic.frequently hu_eventually_memC.frequently
    have hv_zero : v = 0 := by
      exact Set.mem_singleton_iff.mp (hC_asymptotic_trivial hv_asymptotic_mem)
    exact hv_nonzero hv_zero

/-- Canonical owner form for Theorem 8.4 at the scalar-`𝕜` asymptotic-cone layer for closed
convex sets. -/
theorem isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  by_cases hC_nonempty : C.Nonempty
  · simpa using
      isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex_nonempty
        (C := C) hC_convex hC_closed hC_nonempty
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    simp [hCempty, asymptoticCone_empty]

/-- Nonempty-case canonical owner corollary: under the source hypotheses, boundedness is
equivalent to singleton equality for the asymptotic cone. -/
theorem isBounded_iff_asymptoticCone_eq_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone 𝕜 C = ({0} : Set E) := by
  have hcone_nonempty : (asymptoticCone 𝕜 C).Nonempty :=
    (asymptoticCone_nonempty (k := 𝕜) (s := C)).2 hC_nonempty
  exact (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
    hC_closed).trans hcone_nonempty.subset_singleton_iff

/-- Canonical source-owner bridge for Theorem 8.4: boundedness of `C` is equivalent to the
singleton-subset form `0⁺[𝕜] C ⊆ {0}`. -/
theorem isBounded_iff_recessionCone_subset_singleton_zero
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
      hC_closed)

/-- Theorem 8.4: a nonempty closed convex set `C` in a finite-dimensional normed `𝕜`-space is
bounded if and only if its recession cone consists of the zero vector alone. -/
theorem isBounded_iff_recessionCone_eq_singleton_zero
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C = {0} := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    (hC_convex.isBounded_iff_asymptoticCone_eq_singleton_zero_of_closed_convex
      hC_closed hC_nonempty)

end SourceFacing

end Convex

end

/-! ### Theorem_8_4_5 (from Chap02) -/
section

universe u v w

variable {𝕜 : Type v} [Zero 𝕜] [LE 𝕜]
variable {E : Type u} [AddGroup E] [SMul 𝕜 E]
variable {P : Type w} [AddAction E P] [HAdd P E P]

open scoped Pointwise
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.5 identifies the lineality set of a set `C` with the set
  of translation vectors that leave `C` invariant under the intrinsic translation owner
  `Set.vaddSet`, i.e. `y +ᵥ C = C`. The public owner in this file is `Set.lineal 𝕜 C`,
  rendered as `lin[𝕜](C)`.
- `bridge/view`: the chapter recession theorem is stated in singleton-addition form
  `C + {y} ⊆ C`. The core theorems here are parameterized by the primitive bridge hypothesis
  `hrec : ∀ z, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C`; this keeps Theorem 8.4.5 at the weakest owner layer.
  The convex specializations are downstream bridge corollaries using
  `Convex.mem_recessionCone_iff_vadd_subset_self`.
- Primitive data vs derived API: the owner data remains the set `Set.lineal 𝕜 C`; the
  translation-invariance criteria are derived API, with the `vadd` theorem as source-facing and
  the singleton-addition theorem as its bridge view.
- Domain-style sampling used here: `Set.lineal`,
  `Set.lineal_eq_neg_recessionCone_inter_recessionCone`, `Set.mem_lineal_iff`, and
  `Convex.mem_recessionCone_iff_vadd_subset_self`.
- Layer target: this remains a direct source-facing set equality, not a bundled cone statement.
- Scalar-strength note: the stronger assumptions
  `[Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]` are needed only for the
  convex bridge theorem from Theorem 8.1 (its converse direction uses floor/interpolation over
  scalar intervals), not for the lineality-via-bridge argument itself.
--/

namespace Set

/-- Core owner-layer form of Theorem 8.4.5: if recession membership is characterized by
translation inclusion (`hrec`), then `y ∈ lin[𝕜](C)` exactly when translation by `y` fixes `C`. -/
-- Proof sketch: rewrite `y ∈ lin[𝕜](C)` by `Set.mem_lineal_iff` into recession conditions for `y`
-- and `-y`, then use the bridge hypothesis `hrec` in each direction.
theorem mem_lineal_iff_vadd_eq_self {C : Set P}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) {y : E} :
    y ∈ lin[𝕜](C) ↔ y +ᵥ C = C := by
  rw [mem_lineal_iff]
  constructor
  · rintro ⟨hypos, hyneg⟩
    have hypos' : y +ᵥ C ⊆ C := (hrec y).1 hypos
    have hyneg' : (-y) +ᵥ C ⊆ C := (hrec (-y)).1 hyneg
    refine Set.Subset.antisymm hypos' ?_
    intro x hx
    have hxneg : (-y) +ᵥ x ∈ C :=
      hyneg' <| Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
    exact Set.mem_vadd_set.mpr ⟨(-y) +ᵥ x, hxneg, by
      simp [vadd_neg_vadd]⟩
  · intro hy
    have hypos : y ∈ 0⁺[𝕜] C := (hrec y).2 hy.le
    have hyneg : (-y) +ᵥ C ⊆ C := by
      intro x hx
      rcases Set.mem_vadd_set.mp hx with ⟨z, hz, rfl⟩
      have hz' : z ∈ y +ᵥ C := hy.ge hz
      rcases Set.mem_vadd_set.mp hz' with ⟨w, hw, hwz⟩
      have hcancel : (-y) +ᵥ z = w := by
        rw [← hwz]
        simp [neg_vadd_vadd]
      exact hcancel ▸ hw
    exact ⟨hypos, (hrec (-y)).2 hyneg⟩

/-- Theorem 8.4.5 (source-facing form): under the recession/translation bridge hypothesis `hrec`,
`lin[𝕜](C)` is exactly the set of vectors `y` such that translating `C` by `y` leaves `C`
unchanged. -/
theorem lineal_eq_setOf_vadd_eq_self {C : Set P}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) :
    lin[𝕜](C) = {y : E | y +ᵥ C = C} := by
  ext y
  rw [Set.mem_setOf_eq, mem_lineal_iff_vadd_eq_self hrec]

end Set

end

section

universe u v

variable {𝕜 : Type v} [Zero 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [SMul 𝕜 E]

open scoped Pointwise
open scoped Rockafellar

private theorem add_singleton_eq_vaddSet (a : E) (A : Set E) :
    A + {a} = a +ᵥ A := by
  rw [Set.add_singleton, ← Set.image_vadd]
  ext x
  simp [vadd_eq_add, add_comm]

namespace Set

/-- Bridge view in singleton-addition form. -/
theorem mem_lineal_iff_add_singleton_eq_self {C : Set E}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) {y : E} :
    y ∈ lin[𝕜](C) ↔ C + {y} = C := by
  rw [mem_lineal_iff_vadd_eq_self hrec]
  constructor <;> intro hy
  · calc
      C + {y} = y +ᵥ C := add_singleton_eq_vaddSet y C
      _ = C := hy
  · calc
      y +ᵥ C = C + {y} := (add_singleton_eq_vaddSet y C).symm
      _ = C := hy

/-- Singleton-addition bridge view of Theorem 8.4.5 under the same bridge hypothesis `hrec`. -/
theorem lineal_eq_setOf_add_singleton_eq_self {C : Set E}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) :
    lin[𝕜](C) = {y : E | C + {y} = C} := by
  ext y
  rw [Set.mem_setOf_eq, mem_lineal_iff_add_singleton_eq_self hrec]

end Set

end

section

universe u v

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

open scoped Pointwise
open scoped Rockafellar

namespace Convex

/-- Convex owner-prefix specialization of `Set.mem_lineal_iff_vadd_eq_self`, instantiated with
Theorem 8.1's recession/translation bridge. -/
theorem mem_lineal_iff_vadd_eq_self {C : Set E} (hC : Convex 𝕜 C) {y : E} :
    y ∈ lin[𝕜](C) ↔ y +ᵥ C = C := by
  exact Set.mem_lineal_iff_vadd_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex singleton-addition specialization. -/
theorem mem_lineal_iff_add_singleton_eq_self {C : Set E} (hC : Convex 𝕜 C) {y : E} :
    y ∈ lin[𝕜](C) ↔ C + {y} = C := by
  exact Set.mem_lineal_iff_add_singleton_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex set-equality specialization of Theorem 8.4.5 in intrinsic translation form. -/
theorem lineal_eq_setOf_vadd_eq_self {C : Set E} (hC : Convex 𝕜 C) :
    lin[𝕜](C) = {y : E | y +ᵥ C = C} := by
  exact Set.lineal_eq_setOf_vadd_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex set-equality specialization in singleton-addition form. -/
theorem lineal_eq_setOf_add_singleton_eq_self {C : Set E} (hC : Convex 𝕜 C) :
    lin[𝕜](C) = {y : E | C + {y} = C} := by
  exact Set.lineal_eq_setOf_add_singleton_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

end Convex

end

/-! ### Theorem_8_4_7 (from Chap02) -/
section

universe u

open Bornology

namespace Convex

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.7 re-uses the Chapter 2 boundedness criterion for nonempty closed
  convex sets.
- `core/canonical`: the primary owner surface is asymptotic-cone triviality
  `asymptoticCone 𝕜 C ⊆ {0}`.
- `bridge/view`: the recession-cone surface `0⁺[𝕜] C ⊆ {0}` is exposed as a bridge corollary.
- Primitive data vs derived API: primitive inputs are exactly `Convex 𝕜 C`, `IsClosed C`, and
  `C.Nonempty`; the equality form `0⁺[𝕜] C = {0}` is derived from nonemptiness of the cone.
- Ambient/scalar layer: this node keeps the scalar/ambient assumptions inherited from the upstream
  bridge `recessionCone_eq_asymptoticCone`; no extra codomain or model-specific owner is added.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
variable {C : Set E}

/-- Canonical owner form used at this node: boundedness is equivalent to trivial asymptotic cone
for closed convex sets. -/
theorem isBounded_iff_asymptoticCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  simpa using
    (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
      hC_closed)

/-- Source-facing bridge form: boundedness is equivalent to `0⁺[𝕜] C ⊆ {0}`. -/
theorem isBounded_iff_recessionCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  simpa using
    (hC_convex.isBounded_iff_recessionCone_subset_singleton_zero hC_closed hC_nonempty)

/-- Canonical/source bridge at the same abstraction layer: under the source hypotheses, asymptotic
and recession cone triviality are equivalent. -/
theorem asymptoticCone_trivial_iff_recessionCone_trivial_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    asymptoticCone 𝕜 C ⊆ ({0} : Set E) ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  exact
    (isBounded_iff_asymptoticCone_trivial_of_closed_convex
      (hC_convex := hC_convex) (hC_closed := hC_closed)).symm.trans
      (isBounded_iff_recessionCone_trivial_of_closed_convex
        (hC_convex := hC_convex) (hC_closed := hC_closed) (hC_nonempty := hC_nonempty))

/-- Textbook-equality corollary: this remains downstream from the subset-owner bridge. -/
theorem isBounded_iff_recessionCone_eq_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C = ({0} : Set E) := by
  have hcone_nonempty : (0⁺[𝕜] C).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  exact
    (isBounded_iff_recessionCone_trivial_of_closed_convex
      (hC_convex := hC_convex) (hC_closed := hC_closed) (hC_nonempty := hC_nonempty)).trans
      hcone_nonempty.subset_singleton_iff

end Convex

end

/-! ### Theorem_8_4_8 (from Chap02) -/
noncomputable section

open scoped Rockafellar

section

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.8 says that for a closed convex set, the rank equals the dimension
  exactly when the set contains no affine line.
- `core/canonical`: the owner abstractions already present upstream are `Set.rank`, `Set.affineDim`,
  and `Set.lineal` (written as `lin[𝕜](C)`), together with the source-facing set owner
  `Set.HasAffineLine 𝕜 C`.
- `bridge/view`: the source phrase "contains no lines" is rendered in the chapter's existing
  owner `Set.HasAffineLine 𝕜 C`, while the proof bridges that formulation to the existing Chapter
  2 owner `lin[𝕜](C)` via
  `Convex.mem_recessionCone_of_nonneg_ray`.

Domain-style sampling used here:
- `Set.rank` from `Definiton_8_4_6`;
- `Set.lineality` from `Definition_8_4_4`;
- `Set.lineal` / `Set.mem_lineal_iff_forall` from `Definition_8_4_2`;
- the later source-facing no-line surface reused in `Theorem_18_5`;
- `Convex.mem_recessionCone_of_nonneg_ray` from `Theorem_8_3`.

Primitive data vs derived API:
- primitive source inputs: the nonempty set `C`, together with `IsClosed C` and `Convex 𝕜 C`;
- derived owner bridge: vanishing lineality versus absence of a nonzero vector in `lin[𝕜](C)`;
- source-facing output: the rank/dimension criterion formulated through excluded affine-line
  parametrizations.

Layer target: `source-facing`, stated directly on the intrinsic set-side owners rather than on the
older Euclidean-coordinate model. The only finite-dimensional hypotheses retained are the owner
instances already attached to `Set.rank` and `Set.lineality`.
-/

namespace Set

/-- Source-facing owner: `HasAffineLine 𝕜 C` means `C` contains a nontrivial affine line
`x + t • y` for some nonzero direction `y`. -/
def HasAffineLine (𝕜 : Type v) [Add E] [SMul 𝕜 E] (C : Set E) : Prop :=
  ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C

end Set

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem zero_mem_lineal (C : Set E) : (0 : E) ∈ lin[𝕜](C) := by
  rw [Set.mem_lineal_iff]
  constructor <;> (rw [Set.mem_recessionCone_iff]; intro x hx a ha; simpa)

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem lineality_nonneg (C : Set E)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction] :
    0 ≤ lineality[𝕜](C) := by
  let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
  have h0A : (0 : E) ∈ A :=
    (subset_affineSpan 𝕜 (lin[𝕜](C))) (zero_mem_lineal C)
  have hAne : A ≠ ⊥ := by
    intro hbot
    have : (0 : E) ∉ (A : Set E) := by
      simp [hbot]
    exact this h0A
  have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
    simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
  rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne]
  exact_mod_cast Nat.zero_le (Module.finrank 𝕜 A.direction)

/- The owner invariant `Set.lineality 𝕜 C` vanishes exactly when `lin[𝕜](C)` has no nonzero
vector. This is the atomic set-side bridge from the lineality dimension to the intrinsic lineality
space owner. -/
omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
theorem Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction] :
    lineality[𝕜](C) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  constructor
  · intro hC hy
    rcases hy with ⟨y, hyne, hy⟩
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
    have h0A : (0 : E) ∈ A :=
      (subset_affineSpan 𝕜 (lin[𝕜](C))) (zero_mem_lineal C)
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
      simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
    have hfin : Module.finrank 𝕜 A.direction = 0 := by
      rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne] at hC
      exact_mod_cast hC
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hyA : y ∈ A := by
      exact (subset_affineSpan 𝕜 (lin[𝕜](C))) hy
    have hydir : y ∈ A.direction := by
      simpa using A.vsub_mem_direction hyA h0A
    have hy0 : y = 0 := by
      simpa [hdir] using hydir
    exact hyne hy0
  · intro hC
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
    have h0 : (0 : E) ∈ lin[𝕜](C) := zero_mem_lineal C
    have h0A : (0 : E) ∈ A := by
      exact (subset_affineSpan 𝕜 (lin[𝕜](C))) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hsubset : lin[𝕜](C) ⊆ ({0} : Set E) := by
      intro y hy
      by_contra hy0
      exact hC ⟨y, by simpa using hy0, hy⟩
    have hsubset0 : ({0} : Set E) ⊆ lin[𝕜](C) := by
      intro y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      simpa [hy0] using h0
    have hspan : affineSpan 𝕜 (lin[𝕜](C)) = affineSpan 𝕜 ({0} : Set E) :=
      le_antisymm (affineSpan_mono 𝕜 hsubset) (affineSpan_mono 𝕜 hsubset0)
    have hdir : A.direction = ⊥ := by
      calc
        A.direction = (affineSpan 𝕜 ({0} : Set E)).direction := by
          simp [A, hspan]
        _ = vectorSpan 𝕜 ({0} : Set E) := by
          rw [direction_affineSpan 𝕜 ({0} : Set E)]
        _ = ⊥ := by
          rw [vectorSpan_singleton 𝕜 (0 : E)]
    have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
      simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
    rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne, hdir]
    norm_num

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
theorem Set.hasAffineLine_of_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hlin : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    Set.HasAffineLine 𝕜 C := by
  rcases hCne with ⟨x, hx⟩
  rcases hlin with ⟨y, hyne, hy⟩
  refine ⟨x, y, hyne, ?_⟩
  have hy_forall := Set.mem_lineal_iff_forall.mp hy
  intro t
  by_cases ht : 0 ≤ t
  · exact hy_forall.2 x hx t ht
  · have ht' : 0 ≤ -t := by linarith
    have hneg : x + (-t) • (-y) ∈ C := hy_forall.1 x hx (-t) ht'
    simpa [smul_neg, neg_smul] using hneg

theorem Set.exists_ne_zero_mem_lineal_of_hasAffineLine {C : Set E}
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C)
    (hline : Set.HasAffineLine 𝕜 C) :
    ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  rcases hline with ⟨x, y, hyne, hline⟩
  have hRay : ∀ t : 𝕜, 0 ≤ t → x + t • y ∈ C := by
    intro t ht
    exact hline t
  have hNegRay : ∀ t : 𝕜, 0 ≤ t → x + t • (-y) ∈ C := by
    intro t ht
    simpa [smul_neg, neg_smul] using hline (-t)
  refine ⟨y, hyne, ?_⟩
  rw [Set.mem_lineal_iff]
  constructor
  · exact hCconv.mem_recessionCone_of_nonneg_ray hCclosed hRay
  · exact hCconv.mem_recessionCone_of_nonneg_ray hCclosed hNegRay

/- A nontrivial affine line in `C` is equivalent to a nonzero vector in the lineality space
`lin[𝕜](C)`. -/
theorem Set.hasAffineLine_iff_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    Set.HasAffineLine 𝕜 C ↔ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  constructor
  · exact Set.exists_ne_zero_mem_lineal_of_hasAffineLine hCclosed hCconv
  · exact Set.hasAffineLine_of_exists_ne_zero_mem_lineal hCne

/- Source-facing quantifier view of `Set.hasAffineLine_iff_exists_ne_zero_mem_lineal`. -/
theorem Set.exists_affineLine_iff_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    (∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C) ↔ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  simpa [Set.HasAffineLine] using
    (Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hCne hCclosed hCconv)

/- For a nonempty closed convex set, vanishing lineality is equivalent to exclusion of nontrivial
affine-line parametrizations contained in the set. This is the set-side analogue of the
function-side lineality/no-affine-line bridge from Chapter 2. -/
theorem Set.lineality_eq_zero_iff_not_hasAffineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    lineality[𝕜](C) = 0 ↔ ¬ Set.HasAffineLine 𝕜 C := by
  have hline :
      Set.HasAffineLine 𝕜 C ↔
        ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) :=
    Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hCne hCclosed hCconv
  exact Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal.trans
    (not_congr hline.symm)

/- Source-facing quantifier view of `Set.lineality_eq_zero_iff_not_hasAffineLine`. -/
theorem Set.lineality_eq_zero_iff_not_exists_affineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    lineality[𝕜](C) = 0 ↔ ¬ ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C := by
  simpa [Set.HasAffineLine] using
    (Set.lineality_eq_zero_iff_not_hasAffineLine hCne hCclosed hCconv)

/-- Theorem 8.4.8, owner form: for a nonempty closed convex set, once the canonical owner
instances for `Set.affineDim 𝕜 C` and `Set.lineality 𝕜 C` are available, the rank equals the
affine dimension exactly when `C` has no affine-line owner witness. -/
-- Proof sketch: rewrite `rank = affDim` as vanishing of the lineality invariant. Vanishing
-- lineality is equivalent to the absence of nonzero vectors in `lin[𝕜](C)`. A nonzero lineality
-- direction gives a full affine-line parametrization through any point of `C`, while such a
-- parametrization contributes a nonzero direction to `lin[𝕜](C)` by Theorem 8.3 applied to the
-- two ray directions `y` and `-y`.
theorem Set.rank_eq_affineDim_iff_not_hasAffineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    rank[𝕜](C) = dim[𝕜](C) ↔ ¬ Set.HasAffineLine 𝕜 C := by
  have hlineality : lineality[𝕜](C) = 0 ↔ ¬ Set.HasAffineLine 𝕜 C :=
    Set.lineality_eq_zero_iff_not_hasAffineLine hCne hCclosed hCconv
  constructor
  · intro h
    have hlin0 : lineality[𝕜](C) = 0 := by
      rw [Set.rank_eq] at h
      have hnonneg : 0 ≤ lineality[𝕜](C) := lineality_nonneg C
      omega
    exact hlineality.mp hlin0
  · intro h
    have hlin0 : lineality[𝕜](C) = 0 := hlineality.mpr h
    rw [Set.rank_eq, hlin0]
    omega

/-- Theorem 8.4.8, textbook bridge: for a nonempty closed convex set, the rank equals the affine
dimension exactly when the set contains no nontrivial affine-line parametrization. -/
theorem rank_eq_affineDim_iff_no_lines {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    rank[𝕜](C) = dim[𝕜](C) ↔ ¬ ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C := by
  simpa [Set.HasAffineLine] using
    (Set.rank_eq_affineDim_iff_not_hasAffineLine hCne hCclosed hCconv)

end
