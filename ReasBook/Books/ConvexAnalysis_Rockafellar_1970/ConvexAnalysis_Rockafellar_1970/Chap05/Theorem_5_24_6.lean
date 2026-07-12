import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_4

noncomputable section

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.6 says that if a subset `Γ ⊆ ℝ × ℝ` is a complete
  non-decreasing curve, then the coordinate-swapped subset
  `Γ* = {(x⋆, x) | (x, x⋆) ∈ Γ}` is again a complete non-decreasing curve.
- `core/canonical`: the chapter owner `SetRel.IsCompleteNondecreasingCurve` is already intrinsic
  on relations `Γ : SetRel ι α`, so this item should live at that owner level rather than being
  fixed to `ℝ × ℝ`.
- `bridge/view`: the coordinate swap is exactly mathlib's canonical relation inverse `Γ.inv`;
  no second transpose owner or set-builder wrapper is needed.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`;
- `SetRel.inv` from `.lake/packages/mathlib/Mathlib/Data/Rel.lean`, the canonical owner for
  swapping the two coordinates of a relation;
- `IsMaxChain` and `IsMaxChain.image` from
  `Mathlib/Order/Preorder/Chain.lean`, transporting maximal-chain structure along a relation
  isomorphism.

Primitive data vs derived API:
- primitive owner input: a relation `Γ : SetRel ι α`;
- primitive source-facing hypothesis: `Γ.IsCompleteNondecreasingCurve`;
- derived bridge operation: `Γ.inv`, representing the source transpose `Γ*`.

Layer target: `bridge/view`.
-/

section

variable {ι : Type*} [LE ι]
variable {α : Type*} [LE α]

private def prodSwapRelIso : ((· ≤ ·) : (ι × α) → (ι × α) → Prop) ≃r
    ((· ≤ ·) : (α × ι) → (α × ι) → Prop) where
  toEquiv := Equiv.prodComm ι α
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩

private theorem image_prodSwapRelIso_eq_inv (Γ : SetRel ι α) :
    prodSwapRelIso (ι := ι) (α := α) '' Γ = Γ.inv := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.swap.swap ∈ Γ
    simpa using hq
  · intro hp
    refine ⟨p.swap, ?_, ?_⟩
    · change p.swap ∈ Γ at hp
      exact hp
    · cases p
      rfl

-- Proof sketch: identify complete non-decreasing curves with maximal chains in the coordinatewise
-- order; the coordinate-swap map on `ι × α` is a relation isomorphism to `α × ι`, so maximal
-- chains are preserved under image. Rewriting that image as `Γ.inv` yields the theorem.
/-- Theorem 5.24.6 at the canonical owner layer: if `Γ` is a complete non-decreasing curve, then
its coordinate-swapped relation `Γ.inv = {(x⋆, x) | (x, x⋆) ∈ Γ}` is also a complete
non-decreasing curve. Specializing `ι = α = ℝ` recovers the source statement. -/
theorem IsCompleteNondecreasingCurve.inv {Γ : SetRel ι α}
    (hΓ : Γ.IsCompleteNondecreasingCurve) :
    Γ.inv.IsCompleteNondecreasingCurve := by
  have hmax : IsMaxChain (· ≤ ·) Γ := hΓ
  have hmaxSwap : IsMaxChain (· ≤ ·) (prodSwapRelIso (ι := ι) (α := α) '' Γ) :=
    hmax.image (prodSwapRelIso (ι := ι) (α := α))
  simpa [image_prodSwapRelIso_eq_inv (ι := ι) (α := α) Γ] using hmaxSwap

end

end SetRel
