import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.2 fixes convex sets `C₁` and `C₂` in a product space and forms the set
  of pairs `(y, z)` for which the first coordinate `y` decomposes as `y₁ + y₂` with
  `(y₁, z) ∈ C₁` and `(y₂, z) ∈ C₂`.
- `core/canonical`: the owner abstractions are the chapter binary operator `+ᶠ` from
  `Theorem_3_6`, transport along `Prod.swap`, and `Convex 𝕜` on subsets of a product `𝕜`-module.
- `bridge/view`: the argument follows the same witness-combination bridge used for `+ᶠ` in
  `Theorem_3_6`, with first/second coordinates exchanged.
- Primitive data vs derived API: the two convex sets are primitive, while the source-facing
  notation `C₁ +ᶠ₁ C₂` is a transported view of the canonical owner `+ᶠ`; no extra owner
  definition is introduced, and the whole content is convexity of that owner-level set.
- Domain-style sampling: this item aligns with mathlib's owner-side convexity declarations
  `Convex.prod` together with the project theorem `Convex.fiberwiseSum` from
  `Theorem_3_6`.
- Layer target: `bridge/view`; the public theorem should therefore live on the same scalar-generic
  owner layer as `Convex.fiberwiseSum`, not on an unnecessary real-specific
  specialization.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `No`: owner is intrinsic on `Set (E × F)`.
  - Scalar/ambient structure over-concrete? `No`: convexity uses the canonical
    `[Semiring 𝕜] [PartialOrder 𝕜]` layer.
  - Owner tied to concrete model? `No`: no `R^n` wrapper is used.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: statement is convexity-only.
  - Owner/notation surface too heavy? `Yes`: expose a short operator notation mirroring `+ᶠ`.
-/

section

variable {E : Type u} {F : Type v}

section

variable [Add E]

/-- Helper for Text 3.6.2: notation for the first-coordinate fiberwise sum, expressed by
transporting the chapter owner `+ᶠ` along `Prod.swap`. -/
scoped[Rockafellar] notation : 65 C₁ " +ᶠ₁ " C₂ =>
  Prod.swap ⁻¹' ((Prod.swap '' C₁) +ᶠ (Prod.swap '' C₂))

open scoped Rockafellar

/-- Helper for Text 3.6.2: membership in `C₁ +ᶠ₁ C₂` means that the first coordinate splits as a
sum of two witnesses coming from `C₁` and `C₂` over the same second coordinate. -/
@[simp]
theorem Set.mem_fiberwiseFirstSum (C₁ C₂ : Set (E × F)) {x : E × F} :
    x ∈ (C₁ +ᶠ₁ C₂) ↔
      ∃ y₁ y₂ : E, (y₁, x.2) ∈ C₁ ∧ (y₂, x.2) ∈ C₂ ∧ y₁ + y₂ = x.1 := by
  -- Unfold the transported owner and read membership through the swapped canonical owner `+ᶠ`.
  simp [Set.mem_fiberwiseSum]

/-- Helper for Text 3.6.2: coordinate-surface view of membership in `C₁ +ᶠ₁ C₂`, where the first
coordinate decomposes as a sum while the second coordinate is fixed. -/
@[simp]
theorem Set.mem_fiberwiseFirstSum_mk_iff (C₁ C₂ : Set (E × F)) (y : E) (z : F) :
    (y, z) ∈ (C₁ +ᶠ₁ C₂) ↔
      ∃ y₁ y₂ : E, (y₁, z) ∈ C₁ ∧ (y₂, z) ∈ C₂ ∧ y₁ + y₂ = y := by
  -- Specialize the general membership rewrite to the product point `(y, z)`.
  exact Set.mem_fiberwiseFirstSum C₁ C₂ (x := (y, z))

end

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [DistribSMul 𝕜 E] [AddCommMonoid F] [SMul 𝕜 F]

/-- Helper for Text 3.6.2: swapping the two product coordinates preserves convexity. -/
theorem Convex.prod_swap_image {C : Set (E × F)} (hC : Convex 𝕜 C) :
    Convex 𝕜 (Prod.swap '' C) := by
  -- Pull both image points back to `C`, then push the convex combination forward through `swap`.
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ a b ha hb hab
  refine ⟨a • x' + b • y', hC hx' hy' ha hb hab, ?_⟩
  -- Swapping commutes definitionally with product addition and scalar multiplication.
  ext <;> rfl

/-- Text 3.6.2: if `C₁` and `C₂` are convex subsets of `E × F`, then the set of pairs `(y, z)` for
which there exist `y₁` and `y₂` with `(y₁, z) ∈ C₁`, `(y₂, z) ∈ C₂`, and `y₁ + y₂ = y` is convex.
-/
-- Proof sketch: combine witnesses exactly as in `Convex.fiberwiseSum`, but with first and second
-- product coordinates interchanged.
theorem Convex.fiberwiseFirstSum {C₁ C₂ : Set (E × F)}
    (hC₁ : Convex 𝕜 C₁) (hC₂ : Convex 𝕜 C₂) :
    Convex 𝕜 (C₁ +ᶠ₁ C₂) := by
  -- Route correction: transport the first-coordinate statement to the canonical owner `+ᶠ`.
  have hsum : Convex 𝕜 ((Prod.swap '' C₁) +ᶠ (Prod.swap '' C₂)) :=
    (Convex.prod_swap_image hC₁).fiberwiseSum (Convex.prod_swap_image hC₂)
  -- After transport, the target is exactly the convex-combination clause for `hsum`.
  rintro x hx y hy a b ha hb hab
  change Prod.swap (a • x + b • y) ∈ ((Prod.swap '' C₁) +ᶠ (Prod.swap '' C₂))
  simpa [Prod.smul_mk, Prod.mk_add_mk] using hsum hx hy ha hb hab

/-- Helper for Text 3.6.2: explicit-argument wrapper around `Convex.fiberwiseFirstSum`. -/
theorem convex_fiberwise_first_coordinate_sum_of_convex
    (C₁ C₂ : Set (E × F)) (hC₁ : Convex 𝕜 C₁) (hC₂ : Convex 𝕜 C₂) :
    Convex 𝕜 (C₁ +ᶠ₁ C₂) := by
  -- Repackage the namespaced theorem with explicit set arguments.
  exact hC₁.fiberwiseFirstSum hC₂

end
