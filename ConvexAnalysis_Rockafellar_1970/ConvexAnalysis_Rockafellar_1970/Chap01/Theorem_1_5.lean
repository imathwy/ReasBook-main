import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Theorem 1.5 says an affine transformation has the form
  "linear map plus constant term"; textbook finite-coordinate presentations are special cases.
- `core/canonical`: mathlib owns affine-map primitive transport as `AffineMap.map_vadd`, and in
  vector-space coordinates as `AffineMap.decomp`.
- `bridge/view`: the intrinsic affine-space identity
  `T ((x -ᵥ p) +ᵥ p) = T.linear (x -ᵥ p) +ᵥ T p` and its specialization `p = 0`
  are both canonical consequences of these existing owners.
- Primitive data vs derived API: the owner object is an affine map `T : P1 →ᵃ[k] P2`,
  and the vector-space formula is a derived specialization of the intrinsic owner bridge.
- Domain-style sampling: `AffineMap.map_vadd`, `AffineMap.decomp`, `AffineMap.decomp'`,
  `AffineMap.mk'`, and `AffineMap.apply_lineMap`.
- Layer target: keep canonical owners directly on theorem surfaces; avoid parallel wrapper
  vocabulary when existing owners already express the mathematics.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no ordered-extended codomain owner is present in this item.
- Scalar/ambient-structure check: the reused affine-map APIs already sit at the generic
  `[Ring k]` + module + torsor layer; no `ℝ`/Euclidean specialization is needed.
- Owner check: keep the theorem surface on intrinsic affine-map owners
  (`map_vadd`, `mk'`, `apply_lineMap`) and expose vector-space decomposition owners
  (`decomp`, `decomp'`) only as canonical bridges.
- Topology check: this item is not topology-facing.
- Owner-name/notation check: reuse existing canonical owner names and textbook notation
  (`+ᵥ`, affine-map application) directly, with no wrapper definition.
-/

universe u v w

namespace AffineMap

section Intrinsic

variable {k : Type u} {V1 : Type v} {P1 : Type w} {V2 : Type*} {P2 : Type*}
variable [Ring k] [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1]
variable [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2]

recall AffineMap.map_vadd
recall AffineMap.mk'
recall AffineMap.coe_mk'
recall AffineMap.mk'_linear
recall AffineMap.apply_lineMap

/-- Theorem 1.5 at the intrinsic affine-space owner layer:
an affine map is determined by its linear part and one base-point value. -/
@[simp] theorem apply_eq_linear_vsub_vadd (T : P1 →ᵃ[k] P2) (p x : P1) :
    T x = T.linear (x -ᵥ p) +ᵥ T p := by
  calc
    T x = T ((x -ᵥ p) +ᵥ p) := by simp [vsub_vadd]
    _ = T.linear (x -ᵥ p) +ᵥ T p := T.map_vadd p (x -ᵥ p)

/-- Reconstruction form of Theorem 1.5 at the `mk'` owner:
rebuilding from the linear part and one base point gives back the same affine map. -/
@[simp] theorem mk'_self_linear (T : P1 →ᵃ[k] P2) (p : P1) :
    AffineMap.mk' T T.linear p (fun x ↦ T.apply_eq_linear_vsub_vadd p x) = T := by
  ext x
  simp

/-- Relative-basepoint subtraction form at the intrinsic affine-space owner layer:
subtracting two affine-map values cancels the translation part. -/
theorem linear_vsub_eq_vsub_apply (T : P1 →ᵃ[k] P2) (p x : P1) :
    T.linear (x -ᵥ p) = T x -ᵥ T p := by
  exact T.linearMap_vsub x p

end Intrinsic

section VectorSpace

variable {k : Type u} {V1 : Type v} {V2 : Type w}
variable [Ring k] [AddCommGroup V1] [Module k V1]
variable [AddCommGroup V2] [Module k V2]

recall AffineMap.decomp
recall AffineMap.decomp'

/-- Relative-basepoint coordinate form in a vector-space ambient model:
the decomposition can be anchored at any base point `p`, not only at `0`. -/
theorem apply_eq_linear_sub_add_apply (f : V1 →ᵃ[k] V2) (p x : V1) :
    f x = f.linear (x - p) + f p := by
  simpa using (f.apply_eq_linear_vsub_vadd p x)

/-- Relative-basepoint subtraction form:
subtracting two affine-map values cancels the translation part. -/
theorem linear_sub_eq_sub_apply (f : V1 →ᵃ[k] V2) (p x : V1) :
    f.linear (x - p) = f x - f p := by
  simpa [vsub_eq_sub] using (f.linear_vsub_eq_vsub_apply p x)

theorem coe_eq_linear_add_const (f : V1 →ᵃ[k] V2) :
    (f : V1 → V2) = fun x ↦ f.linear x + f 0 := by
  simpa using f.decomp

/-- Helper for Theorem 1.5: every affine map admits a source-facing
linear-plus-constant presentation. -/
theorem exists_linear_add_const (f : V1 →ᵃ[k] V2) :
    ∃ A : V1 →ₗ[k] V2, ∃ a : V2, (f : V1 → V2) = fun x ↦ A x + a := by
  -- Choose the canonical linear part and the image of the origin.
  refine ⟨f.linear, f 0, ?_⟩
  simpa using f.coe_eq_linear_add_const

/-- Helper for Theorem 1.5: a linear map plus a constant term is realized by a canonical affine
map. -/
theorem exists_affineMap_with_linear_add_const (A : V1 →ₗ[k] V2) (a : V2) :
    ∃ f : V1 →ᵃ[k] V2, (f : V1 → V2) = fun x ↦ A x + a := by
  refine ⟨(A.toAffineMap : V1 →ᵃ[k] V2) + AffineMap.const k V1 a, ?_⟩
  -- The affine-map sum reduces pointwise to the textbook expression.
  ext x
  simp

/-- Theorem 1.5, source-facing model-space form: a map `T : V1 → V2` is an affine
transformation exactly when it has the form `x ↦ A x + a` for some linear map `A` and constant
term `a`. -/
theorem exists_affineMap_eq_iff_exists_linear_add_const (T : V1 → V2) :
    (∃ f : V1 →ᵃ[k] V2, (f : V1 → V2) = T) ↔
      ∃ A : V1 →ₗ[k] V2, ∃ a : V2, T = fun x ↦ A x + a := by
  constructor
  · rintro ⟨f, rfl⟩
    -- The canonical linear part and the image of the origin give the textbook form.
    exact f.exists_linear_add_const
  · rintro ⟨A, a, rfl⟩
    -- Conversely, a linear map plus a constant term is a canonical affine map.
    exact exists_affineMap_with_linear_add_const (A := A) (a := a)

/-- Pointwise specialization of `AffineMap.decomp`:
in module coordinates, every affine map has the form `x ↦ A x + b`. -/
theorem apply_eq_linear_add_const (f : V1 →ᵃ[k] V2) (x : V1) :
    f x = f.linear x + f 0 := by
  simpa using f.apply_eq_linear_sub_add_apply (p := 0) x

/-- Pointwise specialization of `AffineMap.decomp'`:
the linear part is the affine map with its constant term removed. -/
theorem linear_apply_eq_sub_const (f : V1 →ᵃ[k] V2) (x : V1) :
    f.linear x = f x - f 0 := by
  simpa using f.linear_sub_eq_sub_apply (p := 0) x

end VectorSpace

end AffineMap
