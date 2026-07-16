import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

noncomputable section

/-!
Abstraction checks:
- codomain/ambient layer: the bridge only needs a distinguished off-domain value, so `[Top L]`
  is the exact ambient requirement; no order, scalar, topological, or additive structure is used.
- scalar/ambient structure: no scalar field/module data is part of the owner.
- owner choice: the primitive bridge is the canonical `Function.extend` owner specialized to
  `Subtype.val`, with the off-domain branch fixed at `⊤`.
- topology/intrinsic language: not applicable in this owner file.
- naming/notation: the canonical chapter conjugate owner/notation is reused directly via
  `convexConjugate` and `f⋆`; this file adds only the extension-by-`⊤` bridge owner.

Source/core/bridge triage for this item.

- `source-facing`: Defn 12.4 identifies a monotone conjugate defined on a constrained domain with
  the chapter Fenchel conjugate on the corresponding subtype.
- `core/canonical`: the same-kind owner is `convexConjugate` from Definition 12.2, used directly
  on subtype domains through the inherited pairing instances.
- `bridge/view`: extension by `⊤` is the direct subtype-domain specialization of
  `Function.extend`.

Domain-style sampling used here:
- `convexConjugate` and the chapter notation `f⋆` from Defn 12.2;
- the companion formula theorem `convexConjugate_eq_iSup_pairing_sub`;
- the canonical owner `Function.extend` together with `extend_val_apply` /
  `extend_val_apply'`.

Primitive data vs derived API:
- primitive input: a subset `s : Set X` and a function `g : s → L`;
- primitive bridge: `Function.extend Subtype.val g (fun _ ↦ ⊤)`;
- source-facing owner: `Function.extendByTop` for subtype domains;
- derived API: the on-domain and off-range evaluation lemmas.

Layer target: this file keeps the owner at the primitive subtype-extension layer given by
`Function.extend`; concrete models such as orthants are downstream specializations rather than the
raw owner here.
-/

namespace Function

/-- Extend a function on a subtype to the ambient type by `⊤` off the subtype. -/
def extendByTop {X : Type*} {s : Set X} {L : Type*} [Top L] (g : s → L) : X → L :=
  Function.extend Subtype.val g (fun _ ↦ ⊤)

/-- On the subtype, `extendByTop g` evaluates to `g` on the corresponding subtype point. -/
@[simp] theorem extendByTop_apply_of_mem
    {X : Type*} {s : Set X} {L : Type*} [Top L] (g : s → L) {x : X}
    (hx : x ∈ s) :
    extendByTop g x = g ⟨x, hx⟩ := by
  simpa [extendByTop] using
    (Function.extend_val_apply (g := g) (j := fun _ : X ↦ (⊤ : L)) hx)

/-- Off the subtype, `extendByTop g` takes the value `⊤`. -/
@[simp] theorem extendByTop_apply_of_notMem
    {X : Type*} {s : Set X} {L : Type*} [Top L] (g : s → L) {x : X}
    (hx : x ∉ s) :
    extendByTop g x = ⊤ := by
  simpa [extendByTop] using
    (Function.extend_val_apply' (g := g) (j := fun _ : X ↦ (⊤ : L)) hx)

/-- On the subtype domain, `extendByTop g` agrees with `g`. -/
@[simp] theorem extendByTop_apply
    {X : Type*} {s : Set X} {L : Type*} [Top L] (g : s → L) (x : s) :
    extendByTop g x = g x := by
  simp [extendByTop]

/-- Restricting `extendByTop g` back to the subtype recovers `g` as a function equality. -/
@[simp] theorem extendByTop_comp_subtype_val
    {X : Type*} {s : Set X} {L : Type*} [Top L] (g : s → L) :
    extendByTop g ∘ (Subtype.val : s → X) = g := by
  funext x
  simp [extendByTop]

end Function

/- Defn 12.4: on a subtype domain, the monotone conjugate is direct reuse of the chapter owner
`convexConjugate` with inherited subtype pairing. The ambient presentation is recovered through
`Function.extendByTop`; no parallel model-specific conjugate owner is introduced here. -/
recall convexConjugate

/- The subtype pointwise supremum formula is the direct owner theorem
`convexConjugate_eq_iSup_pairing_sub`, specialized downstream to concrete subtype models. -/
recall convexConjugate_eq_iSup_pairing_sub

end
