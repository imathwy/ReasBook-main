import Mathlib
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_6_1 (from Chap01) -/
universe u

open scoped Pointwise
open Set

section

variable (R : Type*)
variable [Zero R] [One R] [Add R] [LT R]
variable {E : Type u}
variable [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.1 describes inverse addition by strict positive coefficients whose
  sum is `1`, equivalently by the one-parameter surface
  `(1 - λ) • C₁ ∩ λ • C₂` for `0 < λ < 1`.
- `core/canonical`: the owner abstraction is `Set E` with pointwise scalar action,
  strict positivity on two coefficients `t₁,t₂`, and the primitive normalization
  equation `t₁ + t₂ = 1`.
- `bridge/view`: the one-parameter textbook form is a derived bridge obtained by writing
  `t₂ = λ` and `t₁ = 1 - λ`; this bridge belongs at theorem level rather than in the owner.
- Primitive data vs derived API: the subsets and normalized coefficients are primitive data;
  one-parameter `(1 - t, t)` statements are derived API.
- Domain-style sampling: this aligns with pointwise scalar-action owners on sets and the
  strict-coefficient normalization patterns used in neighboring chapter bridge files.
- Ambient minimization: the owner only needs
  `[Zero R] [One R] [Add R] [LT R] [SMul R E]`.
- Layer target: `source-facing`; this file owns the operation and a minimal bridge theorem.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `No`: owner is intrinsic on `Set E`.
  - Scalar/ambient structure over-concrete? `No`: owner keeps only additive/ordered scalar data
    used by strict-coefficient normalization.
  - Owner tied to a concrete model? `No`: no Euclidean/coordinate owner is used.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topological statement here.
  - Owner/notation surface too heavy? `No`: short owner `Set.inverseAddition` and textbook
    notation `#[R]` are both present and used on theorem surfaces.
-/

/-- Text 3.6.1: inverse addition `C₁ # C₂` consists of points in `t₁ • C₁ ∩ t₂ • C₂`
for some strict positive coefficients `t₁,t₂` with `t₁ + t₂ = 1`. -/
def Set.inverseAddition (C₁ C₂ : Set E) : Set E :=
  {x | ∃ t₁ t₂, 0 < t₁ ∧ 0 < t₂ ∧ t₁ + t₂ = (1 : R) ∧ x ∈ t₁ • C₁ ∩ t₂ • C₂}

end

/-- Canonical textbook surface for inverse addition. -/
scoped[Rockafellar] notation:65 C₁ " #[" R "] " C₂ =>
  Set.inverseAddition R C₁ C₂

open scoped Rockafellar

section

variable {R : Type*}
variable [Zero R] [One R] [Add R] [LT R]
variable {E : Type u}
variable [SMul R E]

/-- Primitive membership form for inverse addition: strict positive normalized coefficients. -/
@[simp] theorem Set.mem_inverseAddition_primitive_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t₁ t₂ : R, 0 < t₁ ∧ 0 < t₂ ∧ t₁ + t₂ = (1 : R) ∧ x ∈ t₁ • C₁ ∩ t₂ • C₂ := by
  rfl

end

section

variable {R : Type*}
variable [AddGroup R] [Preorder R] [AddRightStrictMono R] [One R]
variable {E : Type u}
variable [SMul R E]

/-- Membership bridge to the one-parameter textbook surface `(1 - λ) • C₁ ∩ λ • C₂`
for `0 < λ < 1`, in primitive inequality form. -/
theorem Set.mem_inverseAddition_iff_exists_pos_lt (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t : R, 0 < t ∧ t < (1 : R) ∧ x ∈ (1 - t) • C₁ ∩ t • C₂ := by
  rw [Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨t₁, t₂, ht₁, ht₂, hsum, hx⟩
    have ht₂_lt_one : t₂ < (1 : R) := by
      have : t₂ < t₁ + t₂ := lt_add_of_pos_left t₂ ht₁
      simpa [hsum] using this
    have ht₁_eq : t₁ = 1 - t₂ :=
      (eq_sub_iff_add_eq).2 hsum
    refine ⟨t₂, ht₂, ht₂_lt_one, ?_⟩
    exact ⟨by simpa [ht₁_eq] using hx.1, hx.2⟩
  · rintro ⟨t, ht0, ht1, hx⟩
    refine ⟨1 - t, t, sub_pos.2 ht1, ht0, sub_add_cancel (1 : R) t, hx⟩

/-- Membership bridge to the one-parameter textbook surface `(1 - λ) • C₁ ∩ λ • C₂`
for `0 < λ < 1`, packaged through interval notation. -/
@[simp] theorem Set.mem_inverseAddition_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t, t ∈ Set.Ioo (0 : R) (1 : R) ∧ x ∈ (1 - t) • C₁ ∩ t • C₂ := by
  simpa [Set.Ioo, and_assoc] using
    (Set.mem_inverseAddition_iff_exists_pos_lt C₁ C₂ x)

end

/-! ### Text_3_6_2 (from Chap01) -/
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

/-! ### Text_3_6_3 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.3 states closure of convex sets under pointwise addition in a product
  ambient additive space.
- `core/canonical`: the owner abstraction is the scalar-generic predicate `Convex 𝕜` on sets, and
  the chapter-level canonical bridge is `Convex.add_set`.
- `bridge/view`: in any product ambient type, the displayed coordinatewise-sum set is exactly the
  pointwise sum `C₁ + C₂`.
- Primitive data vs derived API: the sets `C₁` and `C₂` are primitive; convexity of their
  pointwise sum is the whole statement, so no local wrapper theorem is needed.
- Domain-style sampling: this item reuses the upstream weak-layer owner bridge in `Theorem_3_1`,
  then follows nearby exact-reuse items such as `Theorem_3_5` (`Convex.prod`) and
  `Text_3_6_4` (`Convex.inter`).
- Layer target: `core/canonical`; this text is exact owner reuse, so the public entry should stay
  as a direct `recall` of the upstream weak-layer owner bridge rather than a local wrapper.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `Yes` in the textbook coordinate wording, but `No` in
    the owner theorem: `Convex.add_set` lives on intrinsic set convexity.
  - Scalar structure over-concrete? `No`: the theorem surface now reuses the weaker canonical
    layer from `Theorem_3_1` (`[DistribSMul 𝕜 E]`, not a forced module-level bridge).
  - Owner tied to a concrete model? `No`: the public owner is intrinsic `Convex 𝕜` on `Set E`.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is convexity closure, not
    a topological closure/interior statement.
  - Owner name/notation too heavy or too concrete? `No`: `Convex.add_set` and
    pointwise set addition notation `C₁ + C₂` are canonical here.
-/

/- Text 3.6.3: the displayed set of coordinatewise sums is exactly the pointwise sum `C₁ + C₂`, so
its convexity is given by the canonical weak-layer chapter bridge
`Convex.add_set`. -/
recall Convex.add_set

/-! ### Text_3_6_4 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.4 says that the intersection of two convex sets is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜` on subsets of an ambient type carrying
  `[AddCommMonoid E] [SMul 𝕜 E]` with scalar assumptions `[Semiring 𝕜] [PartialOrder 𝕜]`, and
  the exact canonical closure theorem is `Convex.inter`.
- `bridge/view`: any concrete ambient model is a specialization of this owner theorem, so no extra
  wrapper or coordinate-specific bridge layer is needed.
- Primitive data vs derived API: the sets and their convexity proofs are primitive; convexity of
  the intersection is the whole statement.
- Domain-style sampling: the relevant owner-side declarations here are `Convex.inter`,
  `convex_sInter`, `convex_iInter`, and the nearby closure theorem `Convex.prod`.
- Layer target: `core/canonical`; this item is exact owner reuse, so the public entry should stay
  a direct `recall` of `Convex.inter` rather than a parallel local wrapper.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `No`: the owner already lives on intrinsic sets
    `Set E` in a scalar-generic ambient module-like type.
  - Scalar/ambient structure over-concrete? `No`: `Convex.inter` already sits at
    `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]`.
  - Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜`, not a coordinate wrapper.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: this is convexity, not a topology
    statement.
  - Owner name too long/concrete? `No`: `Convex.inter` is the short canonical owner theorem.
  - Missing theorem-surface notation? `No`: the theorem surface is already the primary notation
    `C₁ ∩ C₂`.
-/

/- Text 3.6.4: if `C₁` and `C₂` are convex sets, then `C₁ ∩ C₂` is convex; this is exactly the
canonical theorem `Convex.inter`. -/
recall Convex.inter

/-! ### Text_3_6_5 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.5 states that if `C₁` and `C₂` are convex subsets of an ambient
  product space, then their common part is convex.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜 s` on sets in a
  `𝕜`-module-like ambient space (at the weak layer used by mathlib's owner theorem), and the
  matching canonical theorem is `Convex.inter`.
- `bridge/view`: the displayed membership condition "belongs to both sets" is exactly set
  intersection `C₁ ∩ C₂`, so no additional bridge layer is needed.
- Primitive data vs derived API: the sets `C₁` and `C₂` and their convexity are primitive; the
  conclusion is the direct closure theorem for intersections, so no local wrapper or surrogate
  definition should be introduced.
- Domain-style sampling: this item aligns with mathlib's owner declarations `Convex.inter`,
  `convex_sInter`, and `Convex.prod`, together with the chapter's earlier exact-reuse intersection
  recall `Text_3_6_4`.
- Layer target: `core/canonical`; this numbered text is just the product-space presentation of the
  owner theorem `Convex.inter`, so the main entry should remain a direct `recall` rather than a
  parallel local theorem specialized to pairs.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `Yes` in the textbook wording (`R^(m+p)`), but `No` in
    the owner theorem: `Convex.inter` already lives at the scalar-generic module layer.
  - Scalar structure over-concrete? `No`: the owner theorem already uses the weaker canonical
    assumptions from mathlib (`[Semiring 𝕜] [PartialOrder 𝕜]` plus module-like ambient data).
  - Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on `Set E`.
  - Ambient-vs-intrinsic topology issue? `Not applicable`: this item is order-convexity, not a
    topology statement.
  - Owner name too long/concrete? `No`: `Convex.inter` is the short canonical owner theorem.
  - Missing theorem-surface notation? `No`: the primary textbook surface is set intersection, and
    the canonical notation `C₁ ∩ C₂` is already the theorem surface of `Convex.inter`.
-/

/- Text 3.6.5: if `C₁` and `C₂` are convex subsets of a product ambient space, then their
intersection is convex. This is exactly the canonical theorem `Convex.inter`; the textbook
coordinate wording is a concrete specialization of that owner-level statement. -/
recall Convex.inter

/-! ### Text_3_6_6 (from Chap01) -/
section

universe u

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}
variable [One R] [Add E]

/-- Helper for Text 3.6.6: taking the height-`1` section commutes with the chapter
fiberwise-sum owner `+ᶠ`. -/
@[simp] theorem unitSection_fiberwiseSum_eq (S₁ S₂ : Set (R × E)) :
    U[R | S₁ +ᶠ S₂] = U[R | S₁] + U[R | S₂] := by
  ext x
  simp [Set.mem_fiberwiseSum, Set.mem_add]

/-- Helper for Text 3.6.6: pointwise form of `unitSection_fiberwiseSum_eq`. -/
@[simp] theorem mem_unitSection_fiberwiseSum_iff (S₁ S₂ : Set (R × E)) (x : E) :
    x ∈ U[R | S₁ +ᶠ S₂] ↔ x ∈ U[R | S₁] + U[R | S₂] := by
  simp [unitSection_fiberwiseSum_eq (R := R) (S₁ := S₁) (S₂ := S₂)]

/-- Helper for Text 3.6.6: ambient membership in a fiberwise sum at height `1` is the same as
membership in the Minkowski sum of the two height-`1` sections. -/
@[simp] theorem mem_fiberwiseSum_mk_one_iff (S₁ S₂ : Set (R × E)) (x : E) :
    ((1 : R), x) ∈ S₁ +ᶠ S₂ ↔ x ∈ U[R | S₁] + U[R | S₂] := by
  -- Rewrite the ambient pair membership as unit-section membership at height `1`.
  rw [← mem_unitSection_iff (R := R) (S := S₁ +ᶠ S₂) (x := x)]
  -- The generic unit-section/fiberwise-sum bridge now closes the goal.
  exact mem_unitSection_fiberwiseSum_iff (R := R) (S₁ := S₁) (S₂ := S₂) x

end

section

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}
variable [Monoid R] [Zero R] [LE R] [ZeroLEOneClass R]
variable [Add E] [MulAction R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.6 fixes subsets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then considers the set `K` of pairs
  `(λ, x)` for which `x = x₁ + x₂` with `(λ, x₁) ∈ K₁` and `(λ, x₂) ∈ K₂`.
- `core/canonical`: the owner abstractions are the existing chapter declarations
  `homogenizationSet` and the binary operator `+ᶠ`; no second public set-level wrapper is needed.
- `bridge/view`: the textbook set `K` is exactly
  `homogenizationSet C₁ +ᶠ homogenizationSet C₂`, and the main content is the
  identification of its unit section with the Minkowski sum `C₁ + C₂`.
- Primitive data vs derived API: the homogenization sets and their fiberwise sum are primitive
  owner data; the unit-section equality and its pointwise membership reformulation are the needed
  derived API.
- Domain-style sampling: this item follows `homogenizationSet`,
  `mem_homogenizationSet_iff`, `unitSection`, `(+ᶠ)`, and
  `Set.mem_fiberwiseSum`.
- Layer target: `bridge/view`.
- Ambient minimization: beyond the scalar-action structure required by `homogenizationSet`, the
  only extra ambient data are the additive structure on `E` needed by the owners `+ᶠ` and
  `C₁ + C₂`, so the file should live over that owner layer rather than the concrete model
  `EuclideanSpace ℝ (Fin n)`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `Yes` before normalization: this bridge can be stated first
     for arbitrary `S₁, S₂ : Set (R × E)` and only then specialized to homogenization sets.
  2. Scalar/ambient structure too strong? `Yes` before normalization: the owner-level bridge needs
     only `[One R] [Add E]`; order and scalar-action assumptions belong only to the
     homogenization specialization.
  3. Owner tied to concrete model? `No`: owners are `unitSection`, `+ᶠ`, and `homogenizationSet`.
  4. Better intrinsic/relative topology formulation? `N/A` (non-topological statement).
  5. Owner names too concrete/heavy? `Yes` before normalization at theorem-surface spelling:
     use `fiberwiseSum` (matching owner naming) rather than mixed `fiberwise_sum`.
  6. Notation needed and used? `Yes`; theorem surfaces use `U[R | _]`, `K[R | _]`, and `+ᶠ`.
-/

/-- Helper for Text 3.6.6: the section at height `1` of the fiberwise sum of the homogenization
sets of `C₁` and `C₂` is exactly the Minkowski sum `C₁ + C₂`. -/
-- Proof sketch: unfold the fiberwise-sum owner only at height `1`. Then each witness
-- in the two section factors rewrites by the height-`1` homogenization-section bridge.
@[simp] theorem unitSection_fiberwiseSum_homogenizationSet_eq (C₁ C₂ : Set E) :
    U[R | K[R | C₁] +ᶠ K[R | C₂]] = C₁ + C₂ := by
  calc
    U[R | K[R | C₁] +ᶠ K[R | C₂]]
        = U[R | K[R | C₁]] + U[R | K[R | C₂]] :=
          unitSection_fiberwiseSum_eq (S₁ := K[R | C₁]) (S₂ := K[R | C₂])
    _ = C₁ + C₂ := by
      simp

/-- Membership in the unit section of the fiberwise sum of the homogenization sets of `C₁` and
`C₂` is equivalent to membership in the Minkowski sum `C₁ + C₂`. -/
-- Proof sketch: this is the pointwise form of
-- `unitSection_fiberwiseSum_homogenizationSet_eq`.
@[simp] theorem mem_unitSection_fiberwiseSum_homogenizationSet_iff
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] +ᶠ K[R | C₂]] ↔ x ∈ C₁ + C₂ := by
  simp [unitSection_fiberwiseSum_homogenizationSet_eq (C₁ := C₁) (C₂ := C₂)]

/-- Text 3.6.6: ambient membership at height `1` in the fiberwise sum of the homogenization sets
of `C₁` and `C₂` is equivalent to membership in the Minkowski sum `C₁ + C₂`. -/
theorem mem_fiberwiseSum_homogenizationSet_mk_one_iff
    (C₁ C₂ : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C₁] +ᶠ K[R | C₂] ↔ x ∈ C₁ + C₂ := by
  -- Rewrite the ambient pair-membership statement as a unit-section statement, and
  -- then apply the unit-section membership theorem already proved above.
  -- Pass through the generic height-`1` ambient-membership bridge for fiberwise sums.
  calc
    ((1 : R), x) ∈ K[R | C₁] +ᶠ K[R | C₂]
        ↔ x ∈ U[R | K[R | C₁]] + U[R | K[R | C₂]] :=
          mem_fiberwiseSum_mk_one_iff (R := R) (S₁ := K[R | C₁]) (S₂ := K[R | C₂]) x
    _ ↔ x ∈ C₁ + C₂ := by
      -- Each height-`1` section of a homogenization set collapses to the original set.
      simp

end

/-! ### Theorem_3_6 (from Chap01) -/
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

/-! ### Text_3_6_7 (from Chap01) -/
section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.7 starts from convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization
  sets `K₁, K₂ ⊆ R × E`, then forms the set `K` of pairs `(λ, x)` whose second coordinate
  decomposes fiberwise as `x = x₁ + x₂` with `(λ, x₁) ∈ K₁` and `(λ, x₂) ∈ K₂`.
- `core/canonical`: the chapter owners are `homogenizationSet` and `+ᶠ`, with
  convexity expressed by the canonical predicate `Convex R`.
- `bridge/view`: `K₁` and `K₂` are exactly `homogenizationSet C₁` and `homogenizationSet C₂`,
  while `K` is exactly their fiberwise sum `+ᶠ` from Theorem 3.6.
- Primitive data vs derived API: the sets `C₁`, `C₂` are primitive, and the displayed convexity
  conclusion for their fiberwise homogenized sum is the direct theorem.
- Domain-style sampling: this item reuses the source-facing set constructor
  `homogenizationSet`, the owner theorem `Convex.homogenizationSet`, and the fiberwise-sum
  convexity theorem `Convex.fiberwiseSum`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `No`.
  2. Scalar/ambient structure too strong in this source-facing theorem? `No`; no additional
     strengthening is introduced beyond the upstream owner theorem `Convex.homogenizationSet`.
  3. Owner tied to concrete model? `No`; theorem is over generic module `E`.
  4. Better intrinsic/relative topology surface? `N/A` (non-topological statement).
  5. Owner name too concrete/heavy? `No`; uses short owner `Convex` and chapter notation `K[...]`.
  6. Needed notation used on theorem surface? `Yes`; both `K[R | C]` and `+ᶠ` are used directly.
- Layer target: `bridge/view`.
-/

/-- Text 3.6.7: for convex sets `C₁` and `C₂` in `R^n`, the set of pairs `(λ, x)` admitting a
decomposition `x = x₁ + x₂` with `(λ, x₁)` in the homogenization set of `C₁` and `(λ, x₂)` in the
homogenization set of `C₂` is convex. This formulation over `R` specializes to `R^n`
without changing the mathematics. -/
-- Proof sketch: the owner theorem `Convex.homogenizationSet` gives convexity of
-- `homogenizationSet C₁` and `homogenizationSet C₂`. Theorem 3.6 then applies directly to their
-- fiberwise sum set.
theorem Convex.homogenizationSet_fiberwiseSum {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] +ᶠ K[R | C₂]) := by
  exact (hC₁.homogenizationSet).fiberwiseSum hC₂.homogenizationSet

end

/-! ### Text_3_6_8 (from Chap01) -/
section

universe u

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}

section

variable [Zero R] [LT R]
variable [SMul R E]

set_option quotPrecheck false in
scoped[Rockafellar] notation "K⁺[" R " | " C "]" =>
  ({p : R × E | 0 < p.1 ∧ p.2 ∈ p.1 • C} : Set (R × E))

@[simp] theorem Set.mem_posHomogenizationSet_iff (C : Set E) (p : R × E) :
    p ∈ K⁺[R | C] ↔ 0 < p.1 ∧ p.2 ∈ p.1 • C :=
  Iff.rfl

end

section

variable [Zero R] [Preorder R]
variable [SMul R E]

/-- Under a preorder, `K⁺[R | C]` is exactly the strict-positive-height part of `K[R | C]`. -/
theorem Set.mem_posHomogenizationSet_iff_mem_homogenizationSet_and_pos
    (C : Set E) (p : R × E) :
    p ∈ K⁺[R | C] ↔ p ∈ K[R | C] ∧ 0 < p.1 := by
  rw [Set.mem_posHomogenizationSet_iff, mem_homogenizationSet_iff R C]
  constructor
  · rintro ⟨hp_pos, hp_mem⟩
    exact ⟨⟨le_of_lt hp_pos, hp_mem⟩, hp_pos⟩
  · rintro ⟨hpK, hp_pos⟩
    exact ⟨hp_pos, hpK.2⟩

end

section

variable [Zero R] [One R] [Add R] [LT R]
variable [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.8 fixes convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then defines `K` as the set of
  pairs `(λ, x)` for which the first coordinate decomposes as `λ = λ₁ + λ₂` with
  `0 < λ₁`, `0 < λ₂`, `(λ₁, x) ∈ K₁`, and `(λ₂, x) ∈ K₂`.
- `core/canonical`: the owner abstractions used here are `homogenizationSet`,
  the first-coordinate fiberwise-sum owner `+ᶠ₁`, and `inverseAddition`.
- `bridge/view`: the theorem is the direct coefficient comparison between the unit slice of the
  first-coordinate fiberwise sum of the positivity-filtered homogenization sets and the owner
  operation `inverseAddition C₁ C₂` from Text 3.6.1.
- Primitive data vs derived API: the primitive strict surface here is the direct notation
  `K⁺[R | C] = {p | 0 < p.1 ∧ p.2 ∈ p.1 • C}`, while the connection to
  `K[R | C] ∩ {p | 0 < p.1}` is a bridge theorem valid under a preorder.
- Domain-style sampling: this statement reuses `Set.mem_fiberwiseFirstSum_mk_iff`,
  `inverseAddition`, and `Set.mem_inverseAddition_primitive_iff`.
- Ambient minimization: both public theorems use only the pointwise scalar action on `E`,
  together with additive height arithmetic on `R` (`0`, `1`, `+`, `<`), so
  the file should live over the same scalar-action owner layer as `inverseAddition` rather than
  over unnecessary multiplicative ring structure on the scalar side.
-/

/-- Membership in the unit slice from Text 3.6.8 is equivalent to membership in the inverse
addition `C₁ #[R] C₂`, in its primitive two-coefficient owner form. -/
-- Proof sketch: rewrite the first-coordinate fiberwise sum using
-- `Set.mem_fiberwiseFirstSum_mk_iff`, then rewrite inverse addition via
-- `Set.mem_inverseAddition_primitive_iff`.
@[simp] theorem
    mem_unitSection_fiberwiseFirstSum_pos_homogenizationSet_iff
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | (K⁺[R | C₁] +ᶠ₁ K⁺[R | C₂])] ↔
      x ∈ C₁ #[R] C₂ := by
  rw [mem_unitSection_iff, Set.mem_fiberwiseFirstSum_mk_iff, Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨a₁, a₂, ha₁, ha₂, hsum⟩
    exact ⟨a₁, a₂, ha₁.1, ha₂.1, hsum, ⟨ha₁.2, ha₂.2⟩⟩
  · rintro ⟨a₁, a₂, ha₁_pos, ha₂_pos, hsum, hx⟩
    exact ⟨a₁, a₂, ⟨ha₁_pos, hx.1⟩, ⟨ha₂_pos, hx.2⟩, hsum⟩

/-- Text 3.6.8: if `K₁` and `K₂` are the homogenization sets of `C₁` and `C₂`, then the unit slice
of the first-coordinate fiberwise sum of their strict-positive-height parts is exactly the
inverse addition `C₁ #[R] C₂`. This statement is valid for arbitrary subsets, so the convex case
from the text is immediate. -/
theorem unitSection_fiberwiseFirstSum_pos_homogenizationSet_eq_inverseAddition
    (C₁ C₂ : Set E) :
    U[R | (K⁺[R | C₁] +ᶠ₁ K⁺[R | C₂])] = C₁ #[R] C₂ := by
  ext x
  simpa using
    (mem_unitSection_fiberwiseFirstSum_pos_homogenizationSet_iff C₁ C₂ x)

end

end

/-! ### Text_3_6_9 (from Chap01) -/
section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.9 fixes convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁` and `K₂`, then forms the set of pairs `(λ, x)` for which the first coordinate decomposes as
  `λ = λ₁ + λ₂` with `(λ₁, x) ∈ K₁` and `(λ₂, x) ∈ K₂`.
- `core/canonical`: the owner abstractions are the first-coordinate fiberwise-sum operator `+ᶠ₁`
  from Text 3.6.2 and `Convex R` on subsets of `R × E`.
- `bridge/view`: Text 3.6.2 supplies the source-facing convexity theorem for this displayed
  first-coordinate existential set, proved there by bridging to `+ᶠ` after
  swapping the two product coordinates.
- Primitive data vs derived API: the theorem is a direct convexity statement about that explicit
  subset of `R × E`; the surface notation `+ᶠ₁` packages that subset without changing the
  mathematics.
- Domain-style sampling: this item reuses the owner `homogenizationSet`, the owner-side convexity
  theorem `Convex.homogenizationSet`, and the canonical bridge theorem
  `Convex.fiberwiseFirstSum`.
- Ambient minimization: the theorem uses only the ordered semifield module structure required by
  `homogenizationSet`, so the owner-level statement lives over an arbitrary module over `R`
  rather than the concrete coordinate model `EuclideanSpace ℝ (Fin n)`.
- Layer target: `source-facing`, implemented as a thin specialization of upstream owner bridges.
-/

/-- Text 3.6.9: for convex sets `C₁` and `C₂`, if `K₁` and `K₂` are their homogenization sets,
then the set of pairs `(λ, x)` for which there exist `λ₁` and `λ₂` with
`λ = λ₁ + λ₂`, `(λ₁, x) ∈ K₁`, and `(λ₂, x) ∈ K₂` is convex. Specializing `R = ℝ` recovers the
textbook statement. -/
-- Proof sketch: `Convex.homogenizationSet` gives convexity of each owner set
-- `homogenizationSet Cᵢ`, then the canonical owner theorem `Convex.fiberwiseFirstSum`
-- applies directly.
theorem Convex.homogenizationSet_fiberwiseFirstSum {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] +ᶠ₁ K[R | C₂]) := by
  exact (hC₁.homogenizationSet).fiberwiseFirstSum hC₂.homogenizationSet

end

/-! ### Text_3_6_10 (from Chap01) -/
section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Semiring R] [PartialOrder R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.10 fixes convex sets `C₁` and `C₂`, forms their homogenization sets
  `K₁` and `K₂`, then defines `K` as the set of sums of one point from each and identifies the
  slice of `K` at height `1` with `conv[R] (C₁ ∪ C₂)`.
- `core/canonical`: the owner abstraction for this unit slice is mathlib's `convexJoin R C₁ C₂`,
  whose elements are the convex combinations of one point of `C₁` and one point of `C₂`.
- `bridge/view`: the unit slice of `homogenizationSet C₁ + homogenizationSet C₂` is exactly
  `convexJoin R C₁ C₂`, and for convex nonempty sets `C₁`, `C₂` the owner theorem
  `Convex.convexHull_union` identifies this join with the chapter convex-hull surface
  `conv[R] (C₁ ∪ C₂)`.
- Primitive data vs derived API: `homogenizationSet` remains the primitive source-facing data for
  `K₁` and `K₂`; `convexJoin` and `Convex.convexHull_union` are the derived canonical bridge API.
- Domain-style sampling: this item is guided by `homogenizationSet`, `mem_homogenizationSet_iff`,
  `Set.mem_smul_set`, `mem_convexJoin`, and `Convex.convexHull_union`.
- Layer target: `bridge/view`.
-/

/-- Helper for Text 3.6.10: a point lies in the unit slice of the pointwise sum of the
homogenization sets of `C₁` and `C₂` exactly when it lies in the canonical convex join
`convexJoin R C₁ C₂`. -/
theorem mem_unitSection_homogenizationSet_add_iff_mem_convexJoin
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | (K[R | C₁]) + (K[R | C₂])] ↔
      x ∈ convexJoin R C₁ C₂ := by
  rw [mem_convexJoin]
  constructor
  · intro hx
    -- Unpack the source-facing sum witness into two homogenized summands.
    rcases mem_add.mp hx with ⟨⟨a, x₁⟩, hx₁, ⟨b, x₂⟩, hx₂, hsum⟩
    rw [mem_homogenizationSet_iff R C₁] at hx₁
    rw [mem_homogenizationSet_iff R C₂] at hx₂
    rcases mem_smul_set.mp (by simpa using hx₁.2) with ⟨c₁, hc₁, hc₁eq⟩
    rcases mem_smul_set.mp (by simpa using hx₂.2) with ⟨c₂, hc₂, hc₂eq⟩
    -- Repackage the same witnesses in the canonical `convexJoin` normal form.
    refine ⟨c₁, hc₁, c₂, hc₂, a, b, hx₁.1, hx₂.1, ?_, ?_⟩
    · simpa using congrArg (fun p ↦ p.1) hsum
    · simpa [hc₁eq, hc₂eq] using congrArg (fun p ↦ p.2) hsum
  · rintro ⟨c₁, hc₁, c₂, hc₂, a, b, ha, hb, hab, rfl⟩
    -- Build the two homogenized points and then combine them in the pointwise sum.
    refine mem_add.mpr ⟨(a, a • c₁), ?_, (b, b • c₂), ?_, ?_⟩
    · exact (mem_homogenizationSet_iff R C₁ _).2 ⟨ha, mem_smul_set.mpr ⟨c₁, hc₁, rfl⟩⟩
    · exact (mem_homogenizationSet_iff R C₂ _).2 ⟨hb, mem_smul_set.mpr ⟨c₂, hc₂, rfl⟩⟩
    · ext <;> simp [hab]

/-- Helper for Text 3.6.10: the unit slice of the pointwise sum of the homogenization sets of
`C₁` and `C₂` is exactly the canonical convex join `convexJoin R C₁ C₂`. -/
theorem unitSection_homogenizationSet_add_eq_convexJoin
    (C₁ C₂ : Set E) :
    U[R | (K[R | C₁]) + (K[R | C₂])] =
      convexJoin R C₁ C₂ := by
  -- Extensionality reduces the set equality to the pointwise bridge above.
  ext x
  exact mem_unitSection_homogenizationSet_add_iff_mem_convexJoin C₁ C₂ x

/-- Helper for Text 3.6.10: the unit slice of the pointwise sum of homogenization sets is always
contained in the convex hull of the union. This is the primitive owner-level containment before
imposing convex/nonempty hypotheses that upgrade containment to equality. -/
theorem unitSection_homogenizationSet_add_subset_convexHull_union
    (C₁ C₂ : Set E) :
    U[R | (K[R | C₁]) + (K[R | C₂])] ⊆
      conv[R] (C₁ ∪ C₂) := by
  intro x hx
  -- First move from the homogenization slice to the canonical convex join.
  have hx_join : x ∈ convexJoin R C₁ C₂ :=
    (mem_unitSection_homogenizationSet_add_iff_mem_convexJoin C₁ C₂ x).1 hx
  exact convexJoin_subset_convexHull C₁ C₂ hx_join

end

section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-- Helper for Text 3.6.10: at the closure layer, nonemptiness already identifies the convex hull
of the unit slice of `K[C₁] + K[C₂]` with the convex hull of `C₁ ∪ C₂`. This keeps `convexJoin`
as the primitive owner and treats `conv[R] (C₁ ∪ C₂)` as the derived hull-level bridge. -/
theorem convexHull_unitSection_homogenizationSet_add_eq_convexHull_union
    (C₁ C₂ : Set E) (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) :
    (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) =
      conv[R] (C₁ ∪ C₂) := by
  -- Nonempty sets embed into their convex join, so the union already sits in the owner object.
  have h_union_subset_join : C₁ ∪ C₂ ⊆ convexJoin R C₁ C₂ := by
    exact union_subset
      (subset_convexJoin_left (s := C₁) (t := C₂) hC₂_nonempty)
      (subset_convexJoin_right (s := C₁) (t := C₂) hC₁_nonempty)
  calc
    (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) = conv[R] (convexJoin R C₁ C₂) := by
      simp [unitSection_homogenizationSet_add_eq_convexJoin C₁ C₂]
    _ = conv[R] (C₁ ∪ C₂) := by
      -- The join is contained in the hull of the union, and conversely the union sits in the join.
      apply le_antisymm
      · exact convexHull_min (convexJoin_subset_convexHull C₁ C₂) (convex_convexHull R (C₁ ∪ C₂))
      · exact convexHull_mono h_union_subset_join

end

section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type u}
variable [AddCommGroup E] [Module R E]

/-- Text 3.6.10: for nonempty convex sets `C₁` and `C₂`, the unit slice of the pointwise sum of
their homogenization sets is exactly `conv[R] (C₁ ∪ C₂)`. -/
-- Proof sketch: first derive the closure-level bridge
-- `conv[R] (U[R | K[C₁] + K[C₂]]) = conv[R] (C₁ ∪ C₂)` from the canonical owner
-- `unitSection_homogenizationSet_add_eq_convexJoin`; then upgrade to equality without hull on the
-- left using convexity of the unit slice (`Convex.convexJoin`) under the convexity assumptions.
theorem unitSection_homogenizationSet_add_eq_convexHull_union
    (C₁ C₂ : Set E) (hC₁ : Convex R C₁) (hC₂ : Convex R C₂)
    (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) :
    U[R | (K[R | C₁]) + (K[R | C₂])] =
      conv[R] (C₁ ∪ C₂) := by
  have hconv_unit :
      Convex R (U[R | (K[R | C₁]) + (K[R | C₂])]) := by
    simpa [unitSection_homogenizationSet_add_eq_convexJoin C₁ C₂] using hC₁.convexJoin hC₂
  have hconv_unit_hull :
      (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) =
        U[R | (K[R | C₁]) + (K[R | C₂])] :=
    hconv_unit.convexHull_eq
  calc
    U[R | (K[R | C₁]) + (K[R | C₂])] =
        conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])]) := by
      simpa [eq_comm] using hconv_unit_hull
    _ = conv[R] (C₁ ∪ C₂) :=
      convexHull_unitSection_homogenizationSet_add_eq_convexHull_union
        (R := R) C₁ C₂ hC₁_nonempty hC₂_nonempty

/-- A point `x` lies in the unit slice of the pointwise sum of the homogenization sets of `C₁` and
`C₂` exactly when it lies in `conv[R] (C₁ ∪ C₂)`. -/
theorem mem_unitSection_homogenizationSet_add_iff_mem_convexHull_union
    (C₁ C₂ : Set E) (hC₁ : Convex R C₁) (hC₂ : Convex R C₂)
    (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) (x : E) :
    x ∈ U[R | (K[R | C₁]) + (K[R | C₂])] ↔
      x ∈ conv[R] (C₁ ∪ C₂) := by
  -- Evaluate the established set equality at the point `x`.
  simpa using congrArg (fun s : Set E ↦ x ∈ s)
    (unitSection_homogenizationSet_add_eq_convexHull_union
      C₁ C₂ hC₁ hC₂ hC₁_nonempty hC₂_nonempty)

end

/-! ### Text_3_6_11 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.11 states that for convex sets `C₁, C₂`, the pointwise sum of their
  homogenization sets is convex.
- `core/canonical`: this is exactly the owner theorem `Convex.homogenizationSet_add` on
  `homogenizationSet` and set addition.
- `bridge/view`: the textbook set `K` is the notation-level surface `K[R | C₁] + K[R | C₂]`.
- Primitive data vs derived API: no new owner is introduced here; this text item is direct reuse of
  the canonical derived API on `homogenizationSet`.
- Layer target: `core/canonical`; expose the existing owner theorem by recall.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this item is a set-convexity statement
  and reuses the canonical owner `Convex R`.
- Scalar or ambient structure too concrete? `No` in this file: no extra assumptions are introduced
  beyond those of the upstream owner theorem `Convex.homogenizationSet_add`.
- Owner tied to a concrete model? `No`: the surface is intrinsic (`homogenizationSet` and set
  addition), not a coordinate model shadow owner.
- Ambient vs intrinsic topology issue? `Not applicable`: no topology primitives occur here.
- Owner naming too concrete/long? `No`: the theorem surface is the short owner theorem itself.
- Notation needed on theorem surface? `Yes`, and already satisfied via `K[R | _]`.
-/

/- Text 3.6.11: for convex sets `C₁` and `C₂`, the pointwise sum
`K[R | C₁] + K[R | C₂]` is convex. This item is exact reuse of
`Convex.homogenizationSet_add`. -/
recall Convex.homogenizationSet_add

/-! ### Text_3_6_12 (from Chap01) -/
section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Monoid R]
variable {E : Type u}

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.12 forms the sets `K₁`, `K₂` attached to `C₁`, `C₂` by the rule
  `Kᵢ = {(λ, x) | 0 ≤ λ, x ∈ λ • Cᵢ}`, then defines `K = K₁ ∩ K₂` and identifies the height-`1`
  section of `K`. The source uses `R^n`, but the statement itself only depends on the scalar-action
  structure carried by the chapter owner `homogenizationSet`.
- `core/canonical`: the owner object is the chapter-level source-facing set
  `homogenizationSet C : Set (R × E)` from Text 3.5.5 together with the chapter-level section
  owner `unitSection` (notation `U[R | S]`).
- `bridge/view`: the displayed `K` is exactly `homogenizationSet C₁ ∩ homogenizationSet C₂`, and
  the conclusion is the equality between the height-`1` section of that intersection and
  `C₁ ∩ C₂`, with pointwise membership as the thin companion view. The key owner lemma is the
  upstream unit-section theorem `mem_unitSection_homogenizationSet_iff`.
- Primitive data vs derived API: the homogenization sets are already the primitive source-facing
  data from Text 3.5.5; this item contributes only the section-at-height-`1` characterization.
- Domain-style sampling: this reuses `homogenizationSet`,
  `mem_unitSection_homogenizationSet_iff`, `unitSection`, ordinary set intersection, and
  `Set.mem_inter_iff`.
- Layer target: `bridge/view`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `No` (`Set (R × E)` and `Set E` are already canonical).
  2. Scalar/ambient structure too strong? `No` for this bridge (it reuses
     `mem_unitSection_homogenizationSet_iff` at its native scalar-action layer).
  3. Owner tied to concrete model? `No`; owners are `K`/`U` only.
  4. Better intrinsic/relative topology surface? `N/A` (non-topological statement).
  5. Owner names too concrete/heavy? `No`; owner names are short and canonical.
  6. Notation needed and used? `Yes`; theorem surfaces use `K[R | _]` / `U[R | _]`,
     including the set-family image form `((fun C => K[R | C]) '' 𝒞)`.
  7. Concrete arity over-specialization? `Yes` before normalization: this bridge naturally
     extends from binary intersections to indexed intersections.
-/

variable [Zero R] [LE R] [ZeroLEOneClass R]
variable [MulAction R E]

/-- The height-`1` section of an indexed intersection of homogenization sets is the indexed
intersection of the underlying sets. -/
@[simp] theorem unitSection_iInter_homogenizationSet_eq {ι : Sort*} (C : ι → Set E) :
    U[R | ⋂ i, K[R | C i]] = ⋂ i, C i := by
  ext x
  simp

/-- Membership in the height-`1` section of an indexed intersection of homogenization sets is
equivalent to membership in the indexed intersection of the underlying sets. -/
@[simp] theorem mem_unitSection_iInter_homogenizationSet_iff {ι : Sort*}
    (C : ι → Set E) (x : E) :
    x ∈ U[R | ⋂ i, K[R | C i]] ↔ x ∈ ⋂ i, C i := by
  simp

/-- The height-`1` section of an intrinsic family intersection of homogenization sets, indexed by
elements of a set of sets, is the corresponding intrinsic family intersection. -/
@[simp] theorem unitSection_iInter_subtype_homogenizationSet_eq (𝒞 : Set (Set E)) :
    U[R | ⋂ C ∈ 𝒞, K[R | C]] = ⋂ C ∈ 𝒞, C := by
  ext x
  simp

/-- Membership in the height-`1` section of an intrinsic family intersection of homogenization
sets, indexed by elements of a set of sets, is equivalent to membership in the corresponding
intrinsic family intersection. -/
@[simp] theorem mem_unitSection_iInter_subtype_homogenizationSet_iff (𝒞 : Set (Set E)) (x : E) :
    x ∈ U[R | ⋂ C ∈ 𝒞, K[R | C]] ↔ x ∈ ⋂ C ∈ 𝒞, C := by
  simp

/-- The height-`1` section of the intersection of a family of homogenization sets indexed by a set
of sets is the intersection of that family. -/
@[simp] theorem unitSection_sInter_homogenizationSet_eq (𝒞 : Set (Set E)) :
    U[R | ⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)] = ⋂₀ 𝒞 := by
  ext x
  simp [Set.mem_sInter]

/-- Membership in the height-`1` section of the intersection of a family of homogenization sets
indexed by a set of sets is equivalent to membership in that family intersection. -/
@[simp] theorem mem_unitSection_sInter_homogenizationSet_iff (𝒞 : Set (Set E)) (x : E) :
    x ∈ U[R | ⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)] ↔ x ∈ ⋂₀ 𝒞 := by
  simp [Set.mem_sInter]

/-- Helper for Text 3.6.12: a point belongs to the height-`1` section of the intersection of two
homogenization sets exactly when it belongs to both underlying sets. -/
theorem mem_unitSection_inter_homogenizationSet_and_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] ↔ x ∈ C₁ ∧ x ∈ C₂ := by
  -- Rewrite the section of the ambient intersection into the two height-`1` membership tests.
  -- Each factor then collapses by the single-set homogenization bridge.
  simp [Set.mem_inter_iff]

/-- Helper for Text 3.6.12: the height-`1` section of the intersection of the homogenization sets
of `C₁` and `C₂` is exactly `C₁ ∩ C₂`. -/
@[simp] theorem unitSection_inter_homogenizationSet_eq (C₁ C₂ : Set E) :
    U[R | K[R | C₁] ∩ K[R | C₂]] = C₁ ∩ C₂ := by
  -- First evaluate the source-facing intersection at a point, then use the helper that turns
  -- the height-`1` condition into the two underlying membership conditions.
  -- Reduce the set equality to the pointwise membership statement provided by the helper.
  ext x
  rw [Set.mem_inter_iff]
  exact mem_unitSection_inter_homogenizationSet_and_iff C₁ C₂ x

/-- Membership in the height-`1` section of the intersection of the homogenization sets of
`C₁` and `C₂` is equivalent to membership in `C₁ ∩ C₂`. -/
@[simp] theorem mem_unitSection_inter_homogenizationSet_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] ↔ x ∈ C₁ ∩ C₂ := by
  -- Repackage the conjunction description of the helper as ordinary set-intersection membership.
  rw [Set.mem_inter_iff]
  exact mem_unitSection_inter_homogenizationSet_and_iff C₁ C₂ x

/-- Text 3.6.12: ambient membership at height `1` in the intersection of the homogenization sets
of `C₁` and `C₂` is equivalent to membership in `C₁ ∩ C₂`. -/
theorem mem_inter_homogenizationSet_mk_one_iff (C₁ C₂ : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C₁] ∩ K[R | C₂] ↔ x ∈ C₁ ∩ C₂ := by
  -- Rewrite the ambient pair-membership statement as membership in the height-`1` section.
  -- The unit-section bridge for the intersection then closes the source-facing statement.
  calc
    ((1 : R), x) ∈ K[R | C₁] ∩ K[R | C₂]
        ↔ x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] :=
          (mem_unitSection_iff (S := K[R | C₁] ∩ K[R | C₂]) (x := x)).symm
    _ ↔ x ∈ C₁ ∩ C₂ :=
      mem_unitSection_inter_homogenizationSet_iff C₁ C₂ x

end

/-! ### Text_3_6_13 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.13 fixes convex sets `C₁` and `C₂`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then defines `K` as the set of
  points lying in both and asserts that `K` is convex.
- `core/canonical`: the owner theorem is `Convex.homogenizationSet_inter`, now upstream in
  Proposition 2.6.12 next to `Convex.homogenizationSet`.
- `bridge/view`: the displayed set `K` is exactly `homogenizationSet C₁ ∩ homogenizationSet C₂`;
  this text item is exact owner reuse.
- Primitive data vs derived API: the source-facing construction `homogenizationSet` is already
  available from Text 3.5.5; this item adds only the derived convexity statement for the
  intersection of two such sets.
- Domain-style sampling: this item reuses the existing owner/data split given by
  `homogenizationSet`, `mem_homogenizationSet_iff`, `Convex.homogenizationSet`, and
  `Convex.inter`.
- Layer target: `core/canonical`; this numbered text is exact reuse of an owner theorem, so the
  entry point should be `recall` rather than a parallel local declaration.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this is already an intrinsic set-convexity
  statement over `Set (R × E)`.
- Scalar or ambient structure really essential? `Partially`: this file introduces no stronger local
  assumptions; it reuses exactly the upstream assumptions of `Convex.homogenizationSet`.
- Owner tied to a concrete model? `No`: owner surfaces are `Convex` and `homogenizationSet`.
- Ambient vs intrinsic topology language? `N/A` (non-topological item).
- Owner naming too concrete/long? `No`: owner-facing names are short and canonical.
- Notation needed on theorem surfaces? `Yes`; this file uses and extends the `K[R | _]` surface.
- Concrete arity over-specialization? `Yes` before normalization: binary intersection is the
  textbook instance, but the API should expose indexed-family convexity as the intrinsic layer.
-/

open scoped Rockafellar

section

universe u

variable {R : Type*} {E : Type u}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
  [AddCommMonoid E] [Module R E]

namespace Convex

/-- Indexed-family canonical form: if each `C i` is convex, then the intersection of their
homogenization sets is convex. The binary Text 3.6.13 statement is the arity-2 specialization. -/
theorem iInter_homogenizationSet {ι : Sort*} {C : ι → Set E}
    (hC : ∀ i, Convex R (C i)) :
    Convex R (⋂ i, K[R | C i]) := by
  exact convex_iInter fun i => (hC i).homogenizationSet

/-- Intrinsic-family set form: for a set of convex sets `𝒞`, the intersection of the image family
`{K[R | C] | C ∈ 𝒞}` is convex. -/
theorem sInter_image_homogenizationSet {𝒞 : Set (Set E)}
    (h𝒞 : ∀ C ∈ 𝒞, Convex R C) :
    Convex R (⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)) := by
  refine convex_sInter ?_
  intro S hS
  rcases hS with ⟨C, hC, rfl⟩
  exact (h𝒞 C hC).homogenizationSet

end Convex

end

/-- Text 3.6.13: for convex sets `C₁` and `C₂`, the set of pairs `(λ, x)` belonging to both
homogenization sets is convex at the canonical scalar/module layer, with concrete coordinate
specializations handled downstream as needed. -/
recall Convex.homogenizationSet_inter
