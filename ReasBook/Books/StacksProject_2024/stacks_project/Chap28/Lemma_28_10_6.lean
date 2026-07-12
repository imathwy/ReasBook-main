import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` exposed the canonical scheme-side separation owners
`QuasiSeparatedSpace`, `Scheme.IsSeparated`, and `IsAffineOpen`; this file packages the source
"dimension zero" hypothesis as the explicit affine-open section-ring property
`X.AffineKrullDimLEZero`. -/

/-- A scheme has affine Krull dimension at most `0` if every affine open has section ring of
Krull dimension at most `0`. -/
def AffineKrullDimLEZero (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → Ring.KrullDimLE 0 Γ(X, U)

section

variable {X : Scheme.{u}}

/-- Companion form of `AffineKrullDimLEZero`, packaged over `X.affineOpens`. -/
theorem affineKrullDimLEZero_iff_forall_affineOpens :
    X.AffineKrullDimLEZero ↔ ∀ U : X.affineOpens, Ring.KrullDimLE 0 Γ(X, U) := by
  constructor
  · intro hzero U
    exact hzero U U.2
  · intro hzero U hU
    exact hzero ⟨U, hU⟩

variable (hzero : X.AffineKrullDimLEZero)

/-- Lemma 28.10.6 (1): for a scheme whose affine open section rings all have Krull dimension at
most `0`, quasi-separatedness is equivalent to separatedness. -/
@[stacks 0CKV]
theorem quasiSeparatedSpace_iff_isSeparated_of_affineKrullDimLEZero
    : QuasiSeparatedSpace X ↔ X.IsSeparated := sorry

/-- Lemma 28.10.6 (2): for a scheme whose affine open section rings all have Krull dimension at
most `0`, quasi-separatedness is equivalent to the underlying topological space being Hausdorff. -/
@[stacks 0CKV]
theorem quasiSeparatedSpace_iff_t2Space_of_affineKrullDimLEZero
    : QuasiSeparatedSpace X ↔ T2Space X := sorry

/-- Under the hypotheses of Lemma 28.10.6, separatedness is equivalent to the underlying
topological space being Hausdorff. -/
@[stacks 0CKV]
theorem isSeparated_iff_t2Space_of_affineKrullDimLEZero :
    X.IsSeparated ↔ T2Space X := by
  have hsep : QuasiSeparatedSpace X ↔ X.IsSeparated :=
    quasiSeparatedSpace_iff_isSeparated_of_affineKrullDimLEZero hzero
  have hT2 : QuasiSeparatedSpace X ↔ T2Space X :=
    quasiSeparatedSpace_iff_t2Space_of_affineKrullDimLEZero hzero
  exact hsep.symm.trans hT2

/-- Lemma 28.10.6 (3): for a scheme whose affine open section rings all have Krull dimension at
most `0`, quasi-separatedness is equivalent to every affine open being closed. -/
@[stacks 0CKV]
theorem quasiSeparatedSpace_iff_affineOpensClosed_of_affineKrullDimLEZero
    : QuasiSeparatedSpace X ↔ ∀ U : X.Opens, IsAffineOpen U → IsClosed (U : Set X) := sorry

/-- Companion form of `quasiSeparatedSpace_iff_affineOpensClosed_of_affineKrullDimLEZero` with a
bundled affine-open binder. -/
theorem quasiSeparatedSpace_iff_forall_affineOpens_isClosed_of_affineKrullDimLEZero :
    QuasiSeparatedSpace X ↔ ∀ U : X.affineOpens, IsClosed (U : Set X) := by
  constructor
  · intro hqs U
    exact
      quasiSeparatedSpace_iff_affineOpensClosed_of_affineKrullDimLEZero.mp hqs U U.2
  · intro hclosed
    refine
      quasiSeparatedSpace_iff_affineOpensClosed_of_affineKrullDimLEZero.mpr ?_
    intro U hU
    exact hclosed ⟨U, hU⟩

/-- Lemma 28.10.6 (4): under the equivalent hypotheses, the connected components of the scheme are
points; canonically, the underlying topological space is totally disconnected. -/
@[stacks 0CKV]
theorem totallyDisconnectedSpace_of_quasiSeparatedSpace_of_affineKrullDimLEZero
    (hqs : QuasiSeparatedSpace X) :
    TotallyDisconnectedSpace X := sorry

/-- Lemma 28.10.6 (5): under the equivalent hypotheses, every quasi-compact open subset of the
scheme is affine. -/
@[stacks 0CKV]
theorem isAffineOpen_of_compactSpace_of_quasiSeparatedSpace_of_affineKrullDimLEZero
    (hqs : QuasiSeparatedSpace X) {U : X.Opens} [CompactSpace U] :
    IsAffineOpen U := sorry

/-- Companion form of `isAffineOpen_of_compactSpace_of_quasiSeparatedSpace_of_affineKrullDimLEZero`
with an explicit quasi-compactness hypothesis on the open subset. -/
theorem isAffineOpen_of_isCompact_of_quasiSeparatedSpace_of_affineKrullDimLEZero
    (hqs : QuasiSeparatedSpace X) {U : X.Opens} (hU : IsCompact (U : Set X)) :
    IsAffineOpen U := by
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hU
  exact
    isAffineOpen_of_compactSpace_of_quasiSeparatedSpace_of_affineKrullDimLEZero hqs

/-- Lemma 28.10.6 (6): in particular, a quasi-compact scheme satisfying the equivalent conditions
is affine. -/
@[stacks 0CKV]
theorem isAffine_of_compactSpace_of_quasiSeparatedSpace_of_affineKrullDimLEZero
    [CompactSpace X] (hqs : QuasiSeparatedSpace X) :
    IsAffine X := sorry

end

end AlgebraicGeometry.Scheme
