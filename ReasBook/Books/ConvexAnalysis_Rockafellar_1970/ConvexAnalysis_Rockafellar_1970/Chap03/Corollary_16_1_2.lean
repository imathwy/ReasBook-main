import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [ConditionallyCompleteLattice 𝕜] [One 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.1.2 states that the polar of a positive dilate `λ C` is the
  inverse dilate `λ⁻¹ Cᵒ`.
- `core/canonical`: the owner abstractions are the chapter polar operator `Set.polar` and
  pointwise scalar multiplication of sets on a pairing space, best exposed through the
  invertible-scalar action `𝕜ˣ`.
- `bridge/view`: Rockafellar's notation `Cᵒ[𝕜]` is the chapter postfix notation for `Set.polar`,
  while positive-scalar source formulations are thin specializations via `Units.mk0`.

Domain-style sampling used here:
- `Set.polar`, `Set.mem_polar_iff_swap` from `Text_14_0_5`;
- the generic pointwise-set owner lemma `Set.mem_smul_set_iff_inv_smul_mem`.

Primitive data vs derived API:
- primitive inputs: a set `C : Set X` and an invertible scalar `α : 𝕜ˣ`;
- derived API: the polar-scaling equality and its positive-scalar specialization.

Layer target: `source-facing`, stated directly as an equality of polar sets.

Semantic note: this identity only uses invertibility of the scalar, not positivity, so the main
declaration is phrased on `𝕜ˣ`. The source's convexity and nonemptiness hypotheses are redundant
for this owner-level identity and are omitted from the public statement.
-/

-- Proof sketch: rewrite membership in `(α • C)ᵒ` and `α⁻¹ • Cᵒ` using
-- `Set.mem_polar_iff_swap` and
-- `Set.mem_smul_set_iff_inv_smul_mem`. The forward direction evaluates the polar inequality on
-- `α • y`; the reverse direction evaluates it on `α⁻¹ • x`. In both directions the scalar factors
-- cancel by the unit action, so the two membership conditions become equivalent pointwise.
/-- Corollary 16.1.2 at the pairing owner layer: for an invertible scalar `α : 𝕜ˣ`, the polar of
`α • C` is the inverse dilate `α⁻¹ • Cᵒ[𝕜]`. -/
theorem polar_smul_eq_inv_smul_polar
    (C : Set X) (α : 𝕜ˣ) :
    ((α • C)ᵒ[𝕜] : Set Y) = α⁻¹ • (Cᵒ[𝕜] : Set Y) := by
  ext yStar
  rw [Set.mem_polar_iff_swap, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_polar_iff_swap]
  constructor
  · intro hy x hx
    simpa [Units.smul_def, HasLinearPairing.pairing_eq_pairingLinear] using
      hy (α • x) ⟨x, hx, rfl⟩
  · intro hy x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    simpa [Units.smul_def, HasLinearPairing.pairing_eq_pairingLinear] using
      hy (α⁻¹ • x) hx

end

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-- Corollary 16.1.2, textbook specialization: for a positive scalar `λ`, the polar of the dilate
`λ C` is the inverse dilate `λ⁻¹ Cᵒ[𝕜]`. This is the source-facing view of
`polar_smul_eq_inv_smul_polar`. -/
theorem polar_pos_smul_eq_inv_smul_polar
    (C : Set X) (α : Set.Ioi (0 : 𝕜)) :
    (((α : 𝕜) • C)ᵒ[𝕜] : Set Y) = ((α : 𝕜)⁻¹) • (Cᵒ[𝕜] : Set Y) := by
  simpa [Units.smul_def, Units.val_inv_eq_inv_val] using
    polar_smul_eq_inv_smul_polar C (Units.mk0 (α : 𝕜) α.2.ne')

end
