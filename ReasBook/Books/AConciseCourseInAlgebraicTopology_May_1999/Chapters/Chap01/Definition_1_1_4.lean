import Mathlib.Tactic.Recall
import Mathlib.Topology.Homotopy.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped unitInterval

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 1.1.4: a homotopy between continuous maps `p q : C(X, Y)` is a continuous map
`I × X → Y` whose values at the endpoints `0` and `1` recover `p` and `q`; this is equivalent to
the textbook `X × I → Y` formulation by swapping the factors. -/
recall ContinuousMap.Homotopy (p q : C(X, Y)) : Type (max u v)

namespace ContinuousMap.Homotopy

/-- The underlying map of a homotopy, written in the textbook factor order `X × I`. -/
abbrev prodSwap {p q : C(X, Y)} (H : ContinuousMap.Homotopy p q) : C(X × I, Y) :=
  H.toContinuousMap.comp ContinuousMap.prodSwap

/-- A map `X × I → Y` with the textbook endpoint conditions determines a homotopy. -/
def ofProdSwap {p q : C(X, Y)} (F : C(X × I, Y))
    (map_zero_right : ∀ x, F (x, 0) = p x) (map_one_right : ∀ x, F (x, 1) = q x) :
    ContinuousMap.Homotopy p q where
  toContinuousMap := F.comp ContinuousMap.prodSwap
  map_zero_left := map_zero_right
  map_one_left := map_one_right

/-- Evaluating `H.prodSwap` at `(x, t)` recovers the homotopy value `H (t, x)`. -/
@[simp] theorem prodSwap_apply {p q : C(X, Y)} (H : ContinuousMap.Homotopy p q) (x : X) (t : I) :
    H.prodSwap (x, t) = H (t, x) :=
  rfl

@[simp] theorem prodSwap_apply_zero {p q : C(X, Y)} (H : ContinuousMap.Homotopy p q) (x : X) :
    H.prodSwap (x, 0) = p x :=
  H.apply_zero x

@[simp] theorem prodSwap_apply_one {p q : C(X, Y)} (H : ContinuousMap.Homotopy p q) (x : X) :
    H.prodSwap (x, 1) = q x :=
  H.apply_one x

@[simp] theorem ofProdSwap_apply {p q : C(X, Y)} (F : C(X × I, Y))
    (map_zero_right : ∀ x, F (x, 0) = p x) (map_one_right : ∀ x, F (x, 1) = q x)
    (t : I) (x : X) :
    ofProdSwap F map_zero_right map_one_right (t, x) = F (x, t) :=
  rfl

@[simp] theorem prodSwap_ofProdSwap {p q : C(X, Y)} (F : C(X × I, Y))
    (map_zero_right : ∀ x, F (x, 0) = p x) (map_one_right : ∀ x, F (x, 1) = q x) :
    (ofProdSwap F map_zero_right map_one_right).prodSwap = F := by
  ext ⟨x, t⟩
  rfl

@[simp] theorem ofProdSwap_prodSwap {p q : C(X, Y)} (H : ContinuousMap.Homotopy p q) :
    ofProdSwap H.prodSwap H.prodSwap_apply_zero H.prodSwap_apply_one = H := by
  ext ⟨t, x⟩
  rfl

end ContinuousMap.Homotopy
