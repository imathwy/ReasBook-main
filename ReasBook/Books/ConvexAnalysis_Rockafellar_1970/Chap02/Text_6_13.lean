import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11

-- Declarations for this item will be appended below by the statement pipeline.

/- Rockafellar's scalar-annotated notation for intrinsic closure. -/
scoped[Rockafellar] notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

section

open scoped Rockafellar

variable {𝕜 V : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable {P : Type*} [TopologicalSpace P] [AddTorsor V P]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.13 records two basic topological properties of an affine set, stated in
  concrete finite-dimensional affine language: its carrier is relatively open in its affine hull,
  and it is closed in finite-dimensional ambient affine spaces.
- `core/canonical`: the owner theorem for clause (1) is the scalar-generic
  equality `intrinsicInterior 𝕜 (A : Set P) = A`; in stronger topological-module contexts this is
  subsumed by the chapter owner theorem `Convex.intrinsicInterior`, but that owner would
  strengthen the assumptions of this file. The intrinsic-closure companion
  `cl[𝕜]((A : Set P)) = A` is likewise scalar-generic; ambient closedness is then the
  finite-dimensional corollary `AffineSubspace.isClosed_of_finiteDimensional` of the primitive
  owner bridge `AffineSubspace.isClosed_direction_iff`.
- `bridge/view`: the chapter predicate `IsRelativelyOpen` is the source-facing restatement of
  clause (1); this file exposes that bridge directly for affine subspaces while keeping the weaker
  scalar-generic interior/closure equalities as companions. Clause (2) is stated directly at the
  intrinsic affine-subspace owner layer.
- Primitive data vs derived API: the affine set itself is the owner object `AffineSubspace 𝕜 P`;
  `intrinsicInterior 𝕜`, and ambient closedness are derived topological
  properties of its carrier.
- Domain-style sampling used here: `intrinsicInterior`, `Convex.intrinsicInterior`,
  `AffineSubspace.affineSpan_coe`, `AffineSubspace.isClosed_direction_iff`,
  `Submodule.closed_of_finiteDimensional`, and the chapter bridge predicate
  `IsRelativelyOpen`.
- Layer target: clause (1) is `source-facing` through the bridge
  `AffineSubspace.isRelativelyOpen`, with
  `AffineSubspace.intrinsicInterior_coe` and `AffineSubspace.intrinsicClosure_coe` retained as the
  weaker-assumption companions; clause (2) stays on the intrinsic owner layer with weak ambient
  assumptions.
-/

namespace AffineSubspace

/- Core companion for Text 6.13 (1): the intrinsic interior of an affine set is the affine set
itself. This keeps the weaker scalar-generic hypothesis layer of the source-facing affine item,
rather than importing the stronger topological-module assumptions of `Convex.intrinsicInterior`. -/
@[simp] theorem intrinsicInterior_coe (A : AffineSubspace 𝕜 P) :
    ri[𝕜]((A : Set P)) = A := by
  rw [intrinsicInterior, A.affineSpan_coe]
  have hpre : (Subtype.val ⁻¹' (A : Set P) : Set A) = Set.univ := by
    simp
  rw [hpre, interior_univ, Set.image_univ]
  exact Subtype.range_coe_subtype

/- Intrinsic-closure companion for affine sets: unlike ambient closedness, this statement needs no
finite-dimensional or normed hypotheses. -/
@[simp] theorem intrinsicClosure_coe (A : AffineSubspace 𝕜 P) :
    cl[𝕜]((A : Set P)) = A := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan, A.affineSpan_coe]
  exact Set.inter_eq_right.2 (subset_closure : (A : Set P) ⊆ closure (A : Set P))

/- Text 6.13 (1): the carrier of an affine subspace is relatively open in its affine hull. The
source states this in a concrete scalar setting; the owner bridge is scalar-generic. -/
theorem isRelativelyOpen (A : AffineSubspace 𝕜 P) : IsRelativelyOpen 𝕜 (A : Set P) := by
  change ri[𝕜]((A : Set P)) = (A : Set P)
  exact A.intrinsicInterior_coe
end AffineSubspace

end

section

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T1Space V]
variable {P : Type*} [TopologicalSpace P] [AddTorsor V P] [IsTopologicalAddTorsor P]

/- Text 6.13 (2): every affine set whose direction is finite-dimensional over a complete
nontrivially normed field is closed in the ambient topology.
This clause is stated at the intrinsic affine-subspace owner layer and avoids the stronger
metric/normed-torsor specialization. -/
theorem AffineSubspace.isClosed_of_finiteDimensional (A : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 A.direction] : IsClosed (A : Set P) := by
  exact (AffineSubspace.isClosed_direction_iff (s := A)).1
    (Submodule.closed_of_finiteDimensional A.direction)

end
