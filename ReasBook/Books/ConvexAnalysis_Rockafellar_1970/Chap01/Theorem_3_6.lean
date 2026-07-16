import Mathlib.Analysis.Convex.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.6 forms, from convex sets `C₁` and `C₂` in a product space, the set of
  pairs `(y, z)` for which `z` decomposes as `z₁ + z₂` with `(y, z₁) ∈ C₁` and `(y, z₂) ∈ C₂`.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜` on subsets of the product
  space `E × F`.
- `bridge/view`: the textbook coordinates `R^(m+p) = R^m × R^p` are modeled by an arbitrary pair of
  additive `𝕜`-spaces `E` and `F`; no additional wrapper object is needed.
- Primitive data vs derived API: the sets `C₁` and `C₂` are primitive, and the source-facing owner
  is the displayed existentially defined subset of `E × F`; the convexity proof closes directly by
  combining witnesses through convex combinations.
- Domain-style sampling: this item aligns with `Convex 𝕜` in its primitive combination form, plus
  product-coordinate arithmetic (`Prod.smul_mk`, `Prod.mk_add_mk`) and distributive scalar action
  on the second coordinate.
- Ambient minimization: the proof uses no order-topological or real-specific facts, so the main
  convexity theorem should live over the scalar-generic mathlib layer
  `[Semiring 𝕜] [PartialOrder 𝕜]` with only the `SMul`/`DistribSMul` structure actually used by
  the owner proof.

Abstraction checks:
1. Codomain/ambient layer over-concrete? `No`: owners live on `Set (E × F)`.
2. Scalar/ambient structure too strong? `No`: `Convex` itself fixes `[Semiring 𝕜] [PartialOrder 𝕜]`.
3. Owner tied to concrete model? `No`: no `ℝ^n`/`Fin`/`EuclideanSpace` model is exposed.
4. Better intrinsic/relative topology surface? `N/A`: this item is non-topological.
5. Owner name too concrete/heavy? `No`: canonical short owner is `+ᶠ`.
6. Notation needed and used? `Yes`: theorem surfaces use `+ᶠ` directly.
-/

section

variable {E : Type u} {F : Type v}

section

variable [Add F]

/-- The fiberwise sum of two subsets of `E × F`, formed by keeping the same first coordinate and
adding compatible second-coordinate witnesses. -/
def Set.fiberwiseSum (C₁ C₂ : Set (E × F)) : Set (E × F) :=
  {x | ∃ z₁ z₂ : F, (x.1, z₁) ∈ C₁ ∧ (x.1, z₂) ∈ C₂ ∧ z₁ + z₂ = x.2}

scoped[Rockafellar] infixl:65 " +ᶠ " => Set.fiberwiseSum

open scoped Rockafellar

/-- Membership in `Set.fiberwiseSum C₁ C₂` means that the second coordinate splits as a sum of
two witnesses coming from `C₁` and `C₂` over the same first coordinate. -/
@[simp]
theorem Set.mem_fiberwiseSum {C₁ C₂ : Set (E × F)} {x : E × F} :
    x ∈ (C₁ +ᶠ C₂) ↔ ∃ z₁ z₂ : F, (x.1, z₁) ∈ C₁ ∧ (x.1, z₂) ∈ C₂ ∧ z₁ + z₂ = x.2 := by
  rfl

/-- Coordinate-surface view of membership in `C₁ +ᶠ C₂`: the second coordinate decomposes as a
sum while the first coordinate is fixed. -/
@[simp]
theorem Set.mem_fiberwiseSum_mk_iff (C₁ C₂ : Set (E × F)) (y : E) (z : F) :
    (y, z) ∈ (C₁ +ᶠ C₂) ↔ ∃ z₁ z₂ : F, (y, z₁) ∈ C₁ ∧ (y, z₂) ∈ C₂ ∧ z₁ + z₂ = z := by
  exact Set.mem_fiberwiseSum (C₁ := C₁) (C₂ := C₂) (x := (y, z))

end

open scoped Rockafellar

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E] [AddCommMonoid F] [DistribSMul 𝕜 F]

section

variable [PartialOrder 𝕜]

/-- Theorem 3.6: if `C₁` and `C₂` are convex subsets of `E × F`, then the set of pairs `(y, z)`
for which there exist `z₁` and `z₂` with `(y, z₁) ∈ C₁`, `(y, z₂) ∈ C₂`, and `z₁ + z₂ = z` is
convex. -/
-- Proof sketch: combine membership witnesses from `C₁` and `C₂` using convexity, then use
-- distributivity on the second coordinate to recover the required sum decomposition.
theorem Convex.fiberwiseSum {C₁ C₂ : Set (E × F)}
    (hC₁ : Convex 𝕜 C₁) (hC₂ : Convex 𝕜 C₂) :
    Convex 𝕜 (C₁ +ᶠ C₂) := by
  rintro x hx y hy a b ha hb hab
  rcases (Set.mem_fiberwiseSum (C₁ := C₁) (C₂ := C₂)).1 hx with ⟨z₁, z₂, hz₁, hz₂, hsum₁⟩
  rcases (Set.mem_fiberwiseSum (C₁ := C₁) (C₂ := C₂)).1 hy with ⟨w₁, w₂, hw₁, hw₂, hsum₂⟩
  refine (Set.mem_fiberwiseSum (C₁ := C₁) (C₂ := C₂)).2 ?_
  refine ⟨a • z₁ + b • w₁, a • z₂ + b • w₂, ?_, ?_, ?_⟩
  · simpa [Prod.smul_mk, Prod.mk_add_mk] using hC₁ hz₁ hw₁ ha hb hab
  · simpa [Prod.smul_mk, Prod.mk_add_mk] using hC₂ hz₂ hw₂ ha hb hab
  · calc
      (a • z₁ + b • w₁) + (a • z₂ + b • w₂)
          = (a • z₁ + a • z₂) + (b • w₁ + b • w₂) := by ac_rfl
      _ = a • (z₁ + z₂) + b • (w₁ + w₂) := by simp [smul_add]
      _ = a • x.2 + b • y.2 := by simp [hsum₁, hsum₂]

end

end

end
