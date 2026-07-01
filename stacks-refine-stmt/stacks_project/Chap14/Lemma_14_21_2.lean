import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory
open SimplexCategory.Truncated
open scoped SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.21.2:
- primary domain: pointwise colimit formulas for truncated simplicial objects, expressed through
  costructured-arrow indexing categories with a terminal object;
- sampled owner declarations:
  `CostructuredArrow.proj`,
  `CostructuredArrow.mkIdTerminal`,
  `coconeOfDiagramTerminal`,
  `colimitOfDiagramTerminal`;
- best owner abstraction: the canonical terminal-diagram colimit API applied to
  `CostructuredArrow.proj (inclusion m).op (op (mk n)) ⋙ U`;
- primitive data: the truncated simplicial object `U`, the degree `n`, the source-facing
  indexing diagram on `([n]/Δ)≤mᵒᵖ`, and the identity costructured arrow over `[n]`;
- derived API: the terminality witness from `mkIdTerminal`, together with the induced colimit
  witness and its `desc` formula.

Source/core/bridge triage:
- `source-facing`: the cocone computing the degree-`n` value of an `m`-truncated simplicial object
  from the costructured-arrow indexing category;
- `core/canonical`: `CostructuredArrow.mkIdTerminal`, `coconeOfDiagramTerminal`,
  `colimitOfDiagramTerminal`;
- `bridge/view`: the specialization below, with no extra public wrapper around the canonical
  terminal-diagram colimit API. -/

variable {m n : ℕ} (hn : n ≤ m) (U : SimplicialObject.Truncated C m)

/- The identity costructured arrow is terminal. -/
recall CostructuredArrow.mkIdTerminal

/- The terminal-indexed cocone and its colimit witness are the owner declarations. -/
recall coconeOfDiagramTerminal
recall colimitOfDiagramTerminal

/- Lemma 14.21.2: the cocone with vertex `U_n` induced by the identity simplex `[n] ⟶ [n]` is
the canonical specialization of `colimitOfDiagramTerminal` for the terminal object in the
costructured-arrow indexing category. -/
#check
  (by
    let Δ := (Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let D := CostructuredArrow.proj (Truncated.inclusion m).op Δ ⋙ U
    let T :
        IsTerminal
          (CostructuredArrow.mk (𝟙 Δ) : CostructuredArrow (Truncated.inclusion m).op Δ) :=
      CostructuredArrow.mkIdTerminal
    exact
      (colimitOfDiagramTerminal T D :
        IsColimit (coconeOfDiagramTerminal T D)))

variable
    (s :
      Cocone
        (CostructuredArrow.proj (Truncated.inclusion m).op
          ((Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)) ⋙ U))

/- Companion recall: the `desc` morphism is definitionally evaluation at the identity simplex. -/
#check
  (by
    let Δ := (Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let D := CostructuredArrow.proj (Truncated.inclusion m).op Δ ⋙ U
    let T :
        IsTerminal
          (CostructuredArrow.mk (𝟙 Δ) : CostructuredArrow (Truncated.inclusion m).op Δ) :=
      CostructuredArrow.mkIdTerminal
    change
      (colimitOfDiagramTerminal T D).desc s =
        s.ι.app (CostructuredArrow.mk (𝟙 Δ))
    rfl)

end

end CategoryTheory
