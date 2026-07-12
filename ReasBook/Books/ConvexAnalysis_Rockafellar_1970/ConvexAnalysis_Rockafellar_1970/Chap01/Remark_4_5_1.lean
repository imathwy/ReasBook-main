import Mathlib.Algebra.Order.Ring.Defs
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v
universe w

section

variable {𝕜 : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u}
variable [AddCommMonoid E] [SMul 𝕜 E]
variable {F : Type v}
variable [AddCommMonoid F] [SMul 𝕜 F] [PartialOrder F]

namespace Function

/-- Helper for Remark 4.5.1: local owner alias for convexity of the restricted finite-height
epigraph. This keeps the remark dependency-closed while the chapter wrapper file is unavailable. -/
abbrev IsConvexOn (𝕜 : Type w) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {F : Type v} [AddCommMonoid F] [SMul 𝕜 F] [PartialOrder F]
    (S : Set E) (f : E → WithTopBot F) : Prop :=
  Convex 𝕜 (epi[S] f)

end Function

/-
Source/core/bridge triage:
- `source-facing`: Remark 4.5.1 rewrites convexity of a restricted epigraph as the textbook
  condition that from `f x ≤ μ`, `f y ≤ ν`, and `0 ≤ t ≤ 1`, one gets both membership of the
  convex combination `(1 - t) • x + t • y` in `S` and the corresponding upper bound.
- `core/canonical`: for a `WithTopBot F`-valued function on a fixed subset, the chapter owner is
  `Function.IsConvexOn 𝕜 S f`; its primitive unfolding is `Convex 𝕜 (epi[S] f)`, and the set-level
  owner theorem `convex_iff_add_mem` applies at that unfolded layer.
- `bridge/view`: `mem_epi_restrict_iff` translates membership in `epi[S] f` into the source-facing
  pair consisting of domain membership and the ambient upper-bound inequality. The nearby
  real-valued bridge `convexOn_iff_convex_epigraph` was inspected only as a domain analogue; it
  is not the owner here because it uses an epigraph with codomain heights in the function
  codomain rather than the source-facing height coordinate of this remark.

Primitive data vs derived API:
- primitive data: the subset `S` and the ambient function `f : E → WithTopBot F`;
- derived API: the convex-combination upper-bound criterion below.

Domain-style sampling used here:
- `epigraph` and `mem_epi_restrict_iff` from Definition 4.1;
- `Convex`;
- `convex_iff_add_mem`.
- `convexOn_iff_convex_epigraph` from mathlib, checked only as the nearby codomain-level
  analogue.

Layer target: `bridge/view`; the theorem below keeps the textbook convex-combination criterion as
the source-facing companion to the owner `Function.IsConvexOn 𝕜 S f`.
-/

-- Proof sketch: combine the epigraph-membership formulation with `mem_epi_restrict_iff`. Membership
-- of the displayed convex-combination pair in `epi[S] f` is exactly the existence of a proof
-- that `(1 - t) • x + t • y` lies in `S`, together with the corresponding upper-bound inequality
-- for `f` at that point.
namespace Function

/-- Remark 4.5.1: `Function.IsConvexOn` is equivalent to the convex-combination upper-bound
criterion in the chosen height ambient. -/
theorem isConvexOn_iff_affineCombination_upper_bound
    {S : Set E} {f : E → WithTopBot F} :
    IsConvexOn 𝕜 S f ↔
      ∀ {x y : E}, x ∈ S → y ∈ S → ∀ (μ ν : F) (a b : 𝕜),
        f x ≤ μ → f y ≤ ν → 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • x + b • y ∈ S ∧
          f (a • x + b • y) ≤ (a • μ + b • ν : F) := by
  -- Route correction: unfold the local owner alias directly, since the upstream wrapper file is
  -- currently unavailable; the proof route remains the textbook restricted-epigraph argument.
  rw [IsConvexOn, convex_iff_add_mem]
  refine ⟨?_, ?_⟩
  · intro h x y hx hy μ ν a b hμ hν ha hb hab
    -- Insert the two source points into the restricted epigraph and propagate them by convexity.
    have hz : (a • x + b • y, a • μ + b • ν) ∈ epi[S] f :=
      h (x := (x, μ)) (y := (y, ν))
        (mem_epi_restrict_iff.mpr ⟨hx, hμ⟩) (mem_epi_restrict_iff.mpr ⟨hy, hν⟩)
        ha hb hab
    -- Translate epigraph membership back to the domain-membership and upper-bound conjunction.
    simpa [mem_epi_restrict_iff] using hz
  · intro h p hp q hq a b ha hb hab
    -- Unpack arbitrary epigraph points into coordinates before applying the source-facing criterion.
    rcases p with ⟨x, μ⟩
    rcases q with ⟨y, ν⟩
    rcases mem_epi_restrict_iff.mp hp with ⟨hx, hμ⟩
    rcases mem_epi_restrict_iff.mp hq with ⟨hy, hν⟩
    rcases h hx hy μ ν a b hμ hν ha hb hab with ⟨hxy, hxyμ⟩
    -- Repackage the propagated bound as membership in the restricted epigraph.
    simpa using
      (mem_epi_restrict_iff.mpr ⟨hxy, hxyμ⟩ :
        (a • x + b • y, a • μ + b • ν) ∈ epi[S] f)

/-- Owner-to-source projection: from convexity on `S`, every valid affine-weight upper bounds
at two points propagate to the affine combination. -/
theorem IsConvexOn.affineCombination_upper_bound
    {S : Set E} {f : E → WithTopBot F}
    (hf : IsConvexOn 𝕜 S f) :
    ∀ {x y : E}, x ∈ S → y ∈ S → ∀ (μ ν : F) (a b : 𝕜),
      f x ≤ μ → f y ≤ ν → 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ S ∧
        f (a • x + b • y) ≤ (a • μ + b • ν : F) :=
  (isConvexOn_iff_affineCombination_upper_bound (𝕜 := 𝕜) (S := S) (f := f)).1 hf

end Function

section

variable {𝕜 : Type w}
variable [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u}
variable [AddCommMonoid E] [SMul 𝕜 E]
variable {F : Type v}
variable [AddCommMonoid F] [SMul 𝕜 F] [PartialOrder F]

namespace Function

/-- Source-facing `t`-parameter version of Remark 4.5.1, derived from the primitive
`a,b`-weight owner criterion. -/
theorem isConvexOn_iff_convexCombination_upper_bound
    {S : Set E} {f : E → WithTopBot F} :
    IsConvexOn 𝕜 S f ↔
      ∀ {x y : E}, x ∈ S → y ∈ S → ∀ (μ ν : F) (t : 𝕜),
        f x ≤ μ → f y ≤ ν → 0 ≤ t → t ≤ 1 →
        (1 - t) • x + t • y ∈ S ∧
          f ((1 - t) • x + t • y) ≤ ((1 - t) • μ + t • ν : F) := by
  rw [isConvexOn_iff_affineCombination_upper_bound]
  refine ⟨?_, ?_⟩
  · intro h x y hx hy μ ν t hμ hν ht₀ ht₁
    -- Specialize the affine-weight criterion to `a = 1 - t` and `b = t`.
    exact h hx hy μ ν (1 - t) t hμ hν (sub_nonneg.mpr ht₁) ht₀ (sub_add_cancel 1 t)
  · intro h x y hx hy μ ν a b hμ hν ha hb hab
    -- Recover the one-parameter form by rewriting `a` as `1 - b`.
    have ha' : a = 1 - b := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hab
    have hb' : b ≤ 1 := by
      have : b ≤ a + b := by
        simpa [zero_add] using add_le_add_right ha b
      simpa [hab] using this
    rcases h hx hy μ ν b hμ hν hb hb' with ⟨hxy, hxyμ⟩
    -- Substitute the normalized left weight back into the target affine combination.
    simpa [ha'] using ⟨hxy, hxyμ⟩

/-- Owner-to-source projection in the textbook `t`-parameter form. -/
theorem IsConvexOn.convexCombination_upper_bound
    {S : Set E} {f : E → WithTopBot F}
    (hf : IsConvexOn 𝕜 S f) :
    ∀ {x y : E}, x ∈ S → y ∈ S → ∀ (μ ν : F) (t : 𝕜),
      f x ≤ μ → f y ≤ ν → 0 ≤ t → t ≤ 1 →
      (1 - t) • x + t • y ∈ S ∧
        f ((1 - t) • x + t • y) ≤ ((1 - t) • μ + t • ν : F) :=
  (isConvexOn_iff_convexCombination_upper_bound (𝕜 := 𝕜) (S := S) (f := f)).1 hf

end Function

end

end
