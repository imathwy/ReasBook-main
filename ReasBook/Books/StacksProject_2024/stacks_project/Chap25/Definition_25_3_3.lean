import Mathlib.Tactic.Recall
import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (X : C)

/- Source/core/bridge triage for Definition 25.3.3:
- `source-facing`: a hypercovering of `X`;
- `core/canonical`: `CategoryTheory.Hypercovering (J := J) X`;
- `bridge/view`: `matchingMap`, `Hypercovering.zero_isCovering`, and
  `Hypercovering.succ_isCovering`.

The source introduces no owner beyond the Chapter 25 `Hypercovering` structure, so this file keeps
the direct recall surface instead of adding a redundant wrapper. -/

/- Definition 25.3.3: a hypercovering of `X` is the canonical structure
`CategoryTheory.Hypercovering (J := J) X`, i.e. a simplicial object of `SR(C, X)` whose degree-`0`
term is covering and whose canonical maps `K_{n + 1} ⟶ (cosk_n sk_n K)_{n + 1}` are covering for
all `n ≥ 0`. -/
recall Hypercovering

/- Companion recall: the source's canonical morphism
`K_{n + 1} ⟶ (cosk_n sk_n K)_{n + 1}` is formalized by `CategoryTheory.matchingMap`. -/
recall matchingMap

/- Companion check: the degree-`0` covering condition is the canonical field
`Hypercovering.zero_isCovering`. -/
recall Hypercovering.zero_isCovering

/- Companion check: the higher matching-map covering conditions are the canonical field family
`Hypercovering.succ_isCovering`. -/
recall Hypercovering.succ_isCovering

namespace Hypercovering

variable {X : C}

/-- A hypercovering of `X` is determined by its simplicial object together with the degree-`0`
covering condition and the higher matching-map covering conditions. -/
abbrev ofSimplicial (K : SimplicialObject (SR(C, X)))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Hom.IsCovering J (matchingMap K n)) :
    Hypercovering J X where
  toSimplicialObject := K
  zero_isCovering := zero_isCovering
  succ_isCovering := succ_isCovering

/-- `Hypercovering.ofSimplicial` has the expected underlying simplicial object. -/
@[simp] theorem ofSimplicial_toSimplicialObject (K : SimplicialObject (SR(C, X)))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Hom.IsCovering J (matchingMap K n)) :
    (ofSimplicial K zero_isCovering succ_isCovering).toSimplicialObject = K :=
  rfl

/-- `Hypercovering.ofSimplicial` stores the given degree-`0` covering hypothesis. -/
@[simp] theorem ofSimplicial_zero_isCovering (K : SimplicialObject (SR(C, X)))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Hom.IsCovering J (matchingMap K n)) :
    (ofSimplicial K zero_isCovering succ_isCovering).zero_isCovering = zero_isCovering :=
  rfl

/-- `Hypercovering.ofSimplicial` stores the given higher matching-map covering hypotheses. -/
@[simp] theorem ofSimplicial_succ_isCovering (K : SimplicialObject (SR(C, X)))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Hom.IsCovering J (matchingMap K n))
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    (ofSimplicial K zero_isCovering succ_isCovering).succ_isCovering n =
      succ_isCovering n :=
  rfl

end Hypercovering

end CategoryTheory
