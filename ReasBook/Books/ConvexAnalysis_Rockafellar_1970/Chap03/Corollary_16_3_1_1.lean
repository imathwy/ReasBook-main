import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w z s

section

open scoped Rockafellar

variable {α : Type s} [ConditionallyCompleteLattice α]
variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable [HasPairing FStar F α] [HasPairing EStar E α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.1 identifies the support function of the image `AC`
  with the support function of `C` precomposed with the transpose/dual map `A*`.
- `core/canonical`: the owner abstractions are the chapter support function `δᵛ(· | C)` and an
  explicit dual-side map `Astar` related to `A` by a pairing-compatibility identity.
- `bridge/view`: the source's transpose `A*` is represented abstractly by `Astar` at the pairing
  layer.

Domain-style sampling used here:
- `supportFunction` and `supportFunction_def`;
- `iSup_le` and `le_iSup` on the support-function supremum;
- a dual-map pairing compatibility hypothesis.

Primitive data vs derived API:
- primitive inputs: `A`, `Astar`, the pairing compatibility relation, and the set `C`;
- derived API: the support-function identity, obtained by rewriting the defining supremum along
  the set image and then replacing the pairing term using compatibility.

Layer target: `source-facing`, stated at the pairing owner layer.

Semantic note: the displayed identity already holds for arbitrary subsets `C`; the textbook's
convexity hypothesis is redundant and is therefore omitted.

Codomain note: the support-function statement is exposed at the codomain-general
`WithTopBot α` layer rather than hard-wiring `EReal` in the primary owner theorem.
-/

-- Proof sketch: unfold both support functions. For fixed `yStar`, reindex the supremum over
-- `A '' C` through `Set.image`; then rewrite each pairing value `⟪yStar, A x⟫` as
-- `⟪Astar yStar, x⟫` by the compatibility hypothesis.
/-- Corollary 16.3.1.1 at the pairing owner layer: if `A` and `Astar` satisfy
`⟪yStar, A x⟫ = ⟪Astar yStar, x⟫`, then the support function of `A '' C` equals the support
function of `C` precomposed with `Astar`. -/
theorem supportFunction_image_eq_supportFunction_comp
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x : E, ∀ yStar : FStar, (⟪yStar, A x⟫ₚ : α) = ⟪Astar yStar, x⟫ₚ)
    (C : Set E) :
    supportFunction (L := WithTopBot α) (A '' C) =
      supportFunction (L := WithTopBot α) C ∘ Astar := by
  ext yStar
  rw [Function.comp_apply, supportFunction_def, supportFunction_def]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, hxC, rfl⟩
    calc
      (⟪yStar, A x⟫ₚ : WithTopBot α) = ⟪Astar yStar, x⟫ₚ := by
        exact congrArg (fun r : α ↦ (r : WithTopBot α)) (hA x yStar)
      _ ≤ ⨆ z : C, (⟪Astar yStar, (z : E)⟫ₚ : WithTopBot α) :=
        le_iSup (fun z : C ↦ (⟪Astar yStar, (z : E)⟫ₚ : WithTopBot α)) ⟨x, hxC⟩
  · refine iSup_le ?_
    intro x
    calc
      (⟪Astar yStar, (x : E)⟫ₚ : WithTopBot α) = ⟪yStar, A (x : E)⟫ₚ := by
        exact congrArg (fun r : α ↦ (r : WithTopBot α)) (hA (x : E) yStar).symm
      _ ≤ ⨆ y : A '' C, (⟪yStar, (y : F)⟫ₚ : WithTopBot α) :=
        le_iSup (fun y : A '' C ↦ (⟪yStar, (y : F)⟫ₚ : WithTopBot α))
          ⟨A (x : E), ⟨(x : E), x.2, rfl⟩⟩

end
