import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject

universe u v

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

/-
Domain-style sampling for 14.27.0.1:
- primary domain: simplicial homotopies and the induced chain homotopies on alternating face map
  complexes;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom`,
  `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq`,
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`;
- best owner abstraction: the canonical owner is mathlib's
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`;
- primitive data: a simplicial homotopy `H : Homotopy f g`;
- derived API: the degreewise description of the induced chain homotopy components.

Source/core/bridge triage:
- `core/canonical`: `Homotopy.toChainHomotopy` and its component formula
  `Homotopy.ToChainHomotopy.hom_eq`;
- `bridge/view`: the source-facing sign-rewritten formula below, matching the textbook convention
  `(-1)^(i + 1)` instead of `-(-1)^i`.
-/

/-
14.27.0.1 identifies the textbook operator `s(h)` with the canonical chain-homotopy owner
attached to a simplicial homotopy.
-/
recall Homotopy.toChainHomotopy

/- The canonical component formula is the owner theorem `Homotopy.ToChainHomotopy.hom_eq`. -/
recall Homotopy.ToChainHomotopy.hom_eq

/- The source-facing textbook sign convention rewrites the canonical formula
`-(-1)^i` as `(-1)^(i + 1)`. -/
/-- 14.27.0.1: for a simplicial homotopy `H : Homotopy f g`, the degree-`n` component of the
induced chain homotopy `s(h)` is the alternating sum
`∑_{i=0}^n (-1)^{i+1} (h_{n+1,i+1} ∘ s_i^n)`, which in the canonical simplicial-homotopy API is
the sum of the operators `H.h i` with the same signs. -/
@[stacks 019R]
theorem toChainHomotopy_hom_eq_alternating_sum_succ_sign (H : Homotopy f g) (n : ℕ) :
    H.toChainHomotopy.hom n (n + 1) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) • H.h i := by
  calc
    H.toChainHomotopy.hom n (n + 1)
        = -∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • H.h i := by
            simp [Homotopy.toChainHomotopy]
    _ = ∑ i : Fin (n + 1), -((((-1 : ℤ) ^ (i : ℕ)) • H.h i)) := by
          simp [Finset.sum_neg_distrib]
    _ = ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) • H.h i := by
          refine Finset.sum_congr rfl (fun i _ ↦ ?_)
          simp [pow_succ, mul_comm]

end CategoryTheory.SimplicialObject.Homotopy
