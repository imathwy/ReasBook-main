import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

section

variable {C : Type u} [Category.{v} C]
variable {X Y : SimplicialObject C} {a b : X ⟶ Y}

/- Domain-style sampling for Lemma 14.26.2:
- primary domain: simplicial homotopies between morphisms of simplicial objects;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopy`,
  `Homotopy.h`,
  `Homotopy.mk`,
  `Homotopy.whiskerRight`;
- best owner abstraction: the canonical owner is `CategoryTheory.SimplicialObject.Homotopy`;
- primitive data: the degreewise maps `h_{n,i} : X _⦋n⦌ ⟶ Y _⦋n + 1⦌` together with the endpoint,
  face, and degeneracy relations bundled as the structure fields of `Homotopy`;
- derived API: the constructor `Homotopy.mk`, functoriality such as `Homotopy.whiskerRight`, and
  the zigzag relation `Homotopic` from Definition 14.26.1.

Source/core/bridge triage:
- `source-facing`: the textbook combinatorial description of a simplicial homotopy by maps
  `h_{n,i}` with endpoint and simplicial identities;
- `core/canonical`: the mathlib owner `CategoryTheory.SimplicialObject.Homotopy`;
- `bridge/view`: the constructor `Homotopy.mk`, which packages source-style component data into the
  canonical owner, and the downstream relation `Homotopic` generated from directed homotopies.
-/

/- Lemma 14.26.2: the textbook description of a simplicial homotopy from `a` to `b` by maps
`h_{n,i} : X_n ⟶ Y_{n + 1}` satisfying endpoint, face, and degeneracy relations is formalized by
the canonical mathlib structure `Homotopy a b`; the companion recalls below isolate the degreewise
maps, the listed relations, and the constructor that packages such data into a homotopy. -/
recall Homotopy

/- Companion recall: a simplicial homotopy carries degreewise maps
`h_{n,i} : X _⦋n⦌ ⟶ Y _⦋n + 1⦌`. -/
recall Homotopy.h (H : Homotopy a b) {n : ℕ} (i : Fin (n + 1)) :
  X _⦋n⦌ ⟶ Y _⦋n + 1⦌

/- Companion recall: the `i = 0` component recovers the morphism `b` in degree `n`. -/
recall Homotopy.h_zero_comp_δ_zero (H : Homotopy a b) (n : ℕ) :
  H.h 0 ≫ Y.δ 0 = b.app (op ⦋n⦌)

/- Companion recall: the last component recovers the morphism `a` in degree `n`. -/
recall Homotopy.h_last_comp_δ_last (H : Homotopy a b) (n : ℕ) :
  H.h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = a.app (op ⦋n⦌)

/- Companion recall: if the homotopy index lies strictly above the face index, then the
corresponding face map commutes past `h_{n,i}` in the usual simplicial-homotopy way. -/
recall Homotopy.h_succ_comp_δ_castSucc_of_lt
    (H : Homotopy a b) {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
  H.h j.succ ≫ Y.δ i.castSucc = X.δ i ≫ H.h j

/- Companion recall: the adjacent face terms in the canonical formulation agree. -/
recall Homotopy.h_succ_comp_δ_castSucc_succ
    (H : Homotopy a b) {n : ℕ} (j : Fin (n + 1)) :
  H.h j.succ ≫ Y.δ j.castSucc.succ = H.h j.castSucc ≫ Y.δ j.castSucc.succ

/- Companion recall: if the homotopy index lies at most the face index, then the corresponding
face map commutes past `h_{n,i}` in the complementary simplicial-homotopy case. -/
recall Homotopy.h_castSucc_comp_δ_succ_of_lt
    (H : Homotopy a b) {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
  H.h j.castSucc ≫ Y.δ i.succ = X.δ i ≫ H.h j

/- Companion recall: if the homotopy index lies above the degeneracy index, then the
corresponding degeneracy map commutes past `h_{n,i}`. -/
recall Homotopy.h_comp_σ_castSucc_of_le
    (H : Homotopy a b) {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
  H.h j ≫ Y.σ i.castSucc = X.σ i ≫ H.h j.succ

/- Companion recall: if the homotopy index lies at most the degeneracy index, then the
corresponding degeneracy map commutes past `h_{n,i}` in the complementary case. -/
recall Homotopy.h_comp_σ_succ_of_lt
    (H : Homotopy a b) {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
  H.h j ≫ Y.σ i.succ = X.σ i ≫ H.h j.castSucc

/- Companion recall: conversely, the constructor `Homotopy.mk` packages such degreewise maps and
relations into a simplicial homotopy from `a` to `b`. -/
recall Homotopy.mk

end

end CategoryTheory.SimplicialObject
