import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_4_5_0 (from Chap01) -/
open AffineMap
open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Remark 4.5.0 says that an affine scalar-valued function has an
  inner-product-plus-constant normal form; concrete coordinate models are downstream
  specializations.
- `core/canonical`: the owner object is `AffineMap 𝕜 E 𝕜`, with the companion owner predicate
  `affOn[𝕜](f, (Set.univ : Set E))`; the canonical affine decomposition is `AffineMap.decomp`.
- `bridge/view`: the source formula uses the Euclidean inner product, so the bridge from the
  affine-map decomposition to the displayed formula is the Riesz identification of linear
  functionals on `E` with vectors via `InnerProductSpace.toDual`.
- Primitive data vs derived API: the owner datum is an affine map `E →ᵃ[𝕜] 𝕜`; the convex and
  concave predicates on `Set.univ` are derived owner-side views, and the textbook inner-product
  formula is the source-facing normal form.
- Domain-style sampling: this item is guided by `AffineMap.decomp`, `LinearMap.convexOn`,
  `AffineMap.ofLineMap`, and `InnerProductSpace.toDual`.
- Layer target: `bridge/view`; the owner-facing normal-form theorem belongs on `AffineMap`, and
  the source wording via convexity plus concavity is kept as a derived companion.
-/

section AffineMapBridge

variable {𝕜 V β : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β]

namespace AffineMap

/-- An affine map is convex on all of its domain. -/
theorem convexOn_univ (f : V →ᵃ[𝕜] β) :
    ConvexOn 𝕜 Set.univ f := by
  rw [f.decomp]
  exact (f.linear.convexOn convex_univ).add (convexOn_const _ convex_univ)

/-- An affine map is concave on all of its domain. -/
theorem concaveOn_univ (f : V →ᵃ[𝕜] β) :
    ConcaveOn 𝕜 Set.univ f := by
  rw [f.decomp]
  exact (f.linear.concaveOn convex_univ).add (concaveOn_const _ convex_univ)

end AffineMap

end AffineMapBridge

section

variable {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace AffineMap

/-- On the primitive pairing layer, an affine scalar-valued map is a linear functional plus a
constant, expressed at the affine-map owner layer. -/
theorem exists_eq_dual_toAffineMap_add_const (f : E →ᵃ[𝕜] 𝕜) :
    ∃ (ℓ : Module.Dual 𝕜 E) (α : 𝕜), f = ℓ.toAffineMap + AffineMap.const 𝕜 E α := by
  refine ⟨f.linear, f 0, ?_⟩
  ext x
  rw [f.decomp]
  simp

/-- Source-facing bridge of `exists_eq_dual_toAffineMap_add_const`: an affine scalar-valued map
is pointwise a linear functional plus a constant. -/
theorem exists_eq_dual_apply_add_const (f : E →ᵃ[𝕜] 𝕜) :
    ∃ (ℓ : Module.Dual 𝕜 E) (α : 𝕜), (f : E → 𝕜) = fun x ↦ ℓ x + α := by
  rcases exists_eq_dual_toAffineMap_add_const (f := f) with ⟨ℓ, α, hℓ⟩
  refine ⟨ℓ, α, ?_⟩
  ext x
  simpa [hℓ]

end AffineMap

end

section

variable {𝕜 E Y : Type*} [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

namespace AffineMap

/-- On the pairing owner layer, if the pairing-side parameters represent all linear functionals
on `E`, then an affine scalar-valued map is a pairing functional plus a constant at the
affine-map owner layer. -/
theorem exists_eq_pairing_toAffineMap_add_const
    (hpair : Function.Surjective
      (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 E))
    (f : E →ᵃ[𝕜] 𝕜) :
    ∃ (y : Y) (α : 𝕜),
      f = (HasLinearPairing.pairingLinear.flip y).toAffineMap + AffineMap.const 𝕜 E α := by
  rcases exists_eq_dual_toAffineMap_add_const (f := f) with ⟨ℓ, α, hℓ⟩
  rcases hpair ℓ with ⟨y, hy⟩
  rw [← hy] at hℓ
  exact ⟨y, α, hℓ⟩

/-- Source-facing bridge of `exists_eq_pairing_toAffineMap_add_const`: when the pairing-side
parameters represent all linear functionals on `E`, an affine scalar-valued map is pointwise a
pairing functional plus a constant. -/
theorem exists_eq_pairing_add_const
    (hpair : Function.Surjective
      (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 E))
    (f : E →ᵃ[𝕜] 𝕜) :
    ∃ (y : Y) (α : 𝕜), (f : E → 𝕜) = fun x ↦ ⟪x, y⟫ₚ + α := by
  rcases exists_eq_pairing_toAffineMap_add_const (hpair := hpair) (f := f) with ⟨y, α, hy⟩
  refine ⟨y, α, ?_⟩
  ext x
  simpa [hy, HasLinearPairing.pairing_eq_pairingLinear]

end AffineMap

end

section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
variable [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace AffineMap

/-- On the inner-product bridge layer, an affine scalar-valued map on a finite-dimensional
inner-product space is an inner-product functional plus a constant at the affine-map owner
layer. -/
theorem exists_eq_inner_toAffineMap_add_const (f : E →ᵃ[𝕜] 𝕜) :
    ∃ a α,
      f = ((innerSL 𝕜 a).toLinearMap).toAffineMap +
        AffineMap.const 𝕜 E α := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rcases exists_eq_dual_toAffineMap_add_const (f := f) with ⟨ℓ, α, hℓ⟩
  let ℓc : StrongDual 𝕜 E := LinearMap.toContinuousLinearMap ℓ
  refine ⟨(InnerProductSpace.toDual 𝕜 E).symm ℓc, α, ?_⟩
  rw [hℓ]
  ext x
  have hinner :
      ℓ x = inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm ℓc) x := by
    change ℓc x = inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm ℓc) x
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (E := E) (x := x) (y := ℓc)).symm
  simp [hinner]

/-- Source-facing bridge of `exists_eq_inner_toAffineMap_add_const`: an affine scalar-valued map
on a finite-dimensional inner-product space is pointwise an inner-product functional plus a
constant. -/
theorem exists_eq_inner_add_const (f : E →ᵃ[𝕜] 𝕜) :
    ∃ a α, (f : E → 𝕜) = fun x ↦ inner 𝕜 a x + α := by
  rcases exists_eq_inner_toAffineMap_add_const (f := f) with ⟨a, α, ha⟩
  refine ⟨a, α, ?_⟩
  ext x
  simp [ha]

end AffineMap

end

section

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- Canonical owner bridge on `univ`: a source-facing affine function is exactly the
underlying function of an affine-map owner. -/
theorem affineOn_univ_iff_exists_affineMap (f : E → 𝕜) :
    affOn[𝕜](f, Set.univ) ↔
      ∃ g : E →ᵃ[𝕜] 𝕜, f = g := by
  constructor
  · intro hf_affine
    have h_affine := (affOn_eq_affineCombination (𝕜 := 𝕜) hf_affine)
    have hsegment :
        ∀ x y {t : 𝕜}, 0 ≤ t → t ≤ 1 → f (lineMap x y t) = lineMap (f x) (f y) t := by
      intro x y t ht0 ht1
      simpa [lineMap_apply_module, lineMap_apply_ring] using
        h_affine (by simp) (by simp) (sub_nonneg.mpr ht1) ht0 (by ring)
    have solve_gt_one {a b c t : 𝕜} (ht : t ≠ 0)
        (h : b = lineMap a c (1 / t)) : c = lineMap a b t := by
      rw [lineMap_apply_ring] at h ⊢
      field_simp [ht] at h ⊢
      nlinarith
    have solve_lt_zero {a b c t : 𝕜} (hden : 1 - t ≠ 0)
        (h : a = lineMap c b (-t / (1 - t))) : c = lineMap a b t := by
      rw [lineMap_apply_ring] at h ⊢
      field_simp [hden] at h ⊢
      nlinarith
    have hline :
        ∀ x y (t : 𝕜), f (lineMap x y t) = lineMap (f x) (f y) t := by
      intro x y t
      by_cases ht0 : 0 ≤ t
      · by_cases ht1 : t ≤ 1
        · exact hsegment x y ht0 ht1
        · have ht' : 0 < t := by linarith
          have ht0' : t ≠ 0 := ne_of_gt ht'
          have hu0 : 0 ≤ 1 / t := one_div_nonneg.mpr (le_of_lt ht')
          have hu1 : 1 / t ≤ 1 := by
            exact (div_le_iff₀ ht').2 (by linarith)
          have hy : f y = lineMap (f x) (f (lineMap x y t)) (1 / t) := by
            have hy' := hsegment x (lineMap x y t) hu0 hu1
            rw [lineMap_lineMap_right] at hy'
            have hunit : 1 / t * t = 1 := by
              field_simp [ht0']
            rw [hunit, lineMap_apply_one] at hy'
            exact hy'
          exact solve_gt_one ht0' hy
      · have hden : 1 - t ≠ 0 := by linarith
        let u : 𝕜 := -t / (1 - t)
        have hu0 : 0 ≤ u := by
          dsimp [u]
          exact div_nonneg (by linarith) (by linarith)
        have hu1 : u ≤ 1 := by
          have hden' : 0 < 1 - t := by linarith
          dsimp [u]
          field_simp [hden'.ne']
          linarith
        have hx : f x = lineMap (f (lineMap x y t)) (f y) u := by
          have hu := hsegment (lineMap x y t) y hu0 hu1
          have hzero : 1 - (1 - u) * (1 - t) = 0 := by
            dsimp [u]
            field_simp [hden]
            ring
          simpa [u, hzero] using hu
        exact solve_lt_zero hden hx
    exact ⟨AffineMap.ofLineMap f hline, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.convexOn_univ, g.concaveOn_univ⟩

/-- On the pairing owner layer, an affine scalar-valued map on `univ` over an ordered
field is exactly a linear functional plus a constant. -/
theorem affineOn_univ_iff_exists_dual_apply_add_const (f : E → 𝕜) :
    affOn[𝕜](f, Set.univ) ↔
      ∃ (ℓ : Module.Dual 𝕜 E) (α : 𝕜), f = fun x ↦ ℓ x + α := by
  constructor
  · intro hf_affine
    rcases (affineOn_univ_iff_exists_affineMap (f := f)).1 hf_affine with ⟨g, rfl⟩
    simpa using (AffineMap.exists_eq_dual_apply_add_const (f := g))
  · rintro ⟨ℓ, α, hrepr⟩
    let g : E →ᵃ[𝕜] 𝕜 := ℓ.toAffineMap + AffineMap.const 𝕜 E α
    refine (affineOn_univ_iff_exists_affineMap (f := f)).2 ?_
    refine ⟨g, ?_⟩
    calc
      f = fun x ↦ ℓ x + α := hrepr
      _ = g := by
        ext x
        simp [g]

/-- Pairing-owner form of Remark 4.5.0 on `univ`: when the pairing-side parameters represent all
linear functionals on `E`, `affOn[𝕜](f, Set.univ)` is equivalent to a pairing-plus-constant
formula. -/
theorem affineOn_univ_iff_exists_pairing_add_const
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    (hpair : Function.Surjective
      (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 E))
    (f : E → 𝕜) :
    affOn[𝕜](f, Set.univ) ↔
      ∃ (y : Y) (α : 𝕜), f = fun x ↦ ⟪x, y⟫ₚ + α := by
  constructor
  · intro hf_affine
    rcases (affineOn_univ_iff_exists_affineMap (f := f)).1 hf_affine with ⟨g, rfl⟩
    simpa using (AffineMap.exists_eq_pairing_add_const (hpair := hpair) (f := g))
  · rintro ⟨y, α, hrepr⟩
    let g : E →ᵃ[𝕜] 𝕜 :=
      (HasLinearPairing.pairingLinear.flip y).toAffineMap + AffineMap.const 𝕜 E α
    refine (affineOn_univ_iff_exists_affineMap (f := f)).2 ?_
    refine ⟨g, ?_⟩
    calc
      f = fun x ↦ ⟪x, y⟫ₚ + α := hrepr
      _ = fun x ↦ (HasLinearPairing.pairingLinear.flip y : Module.Dual 𝕜 E) x + α := by
        funext x
        simp [HasLinearPairing.pairing_eq_pairingLinear]
      _ = g := by
        ext x
        simp [g]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Remark 4.5.0 in the source-facing function language from Definition 4.3: on a
finite-dimensional real inner-product space, a scalar-valued
function is affine on `univ` exactly when it has the textbook form `x ↦ inner ℝ a x + α`.

This is obtained in two steps: first recover the affine-map owner from the convex/concave
hypotheses, then apply the inner-product normal form for affine maps. -/
theorem affineOn_univ_iff_exists_inner_add_const (f : E → ℝ) :
    affOn[ℝ](f, Set.univ) ↔
      ∃ a α, f = fun x ↦ inner ℝ a x + α := by
  constructor
  · intro hf_affine
    rcases (affineOn_univ_iff_exists_affineMap (f := f)).1 hf_affine with ⟨g, rfl⟩
    simpa using (AffineMap.exists_eq_inner_add_const (f := g))
  · rintro ⟨a, α, hrepr⟩
    let g : E →ᵃ[ℝ] ℝ :=
      ((innerSL ℝ a).toLinearMap).toAffineMap + AffineMap.const ℝ E α
    refine (affineOn_univ_iff_exists_affineMap (f := f)).2 ?_
    refine ⟨g, ?_⟩
    calc
      f = fun x ↦ inner ℝ a x + α := hrepr
      _ = g := by
        ext x
        simp [g]

end

/-! ### Remark_4_5_1 (from Chap01) -/
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

/-! ### Remark_4_5_2 (from Chap01) -/
noncomputable section

open scoped BigOperators
open scoped Rockafellar

attribute [local instance] Classical.propDecidable

section

variable {ι : Type*} [Fintype ι]

local notation "E" => (ι → ℝ)

/-
Source/core/bridge triage:
- `source-facing`: Remark 4.5.2 is the globally defined function that equals the negative
  geometric mean on the nonnegative orthant and `+∞` outside, for a finite coordinate family.
  The textbook statement is the specialization `ι = Fin n` with `n ≥ 1`.
- `core/canonical`: the chapter owner layer for such an extension is the ambient
  `WithBotTop ℝ`-valued function `Function.toWithBotTopOn` on the canonical set owner
  `orthant[ℝ](E)`.
- `bridge/view`: the source coordinatewise nonnegativity condition is the pointwise description of
  membership in `orthant[ℝ](E)`, and
  `Function.toWithBotTopOn_eq_add_indicator` /
  `isConvex_toWithBotTop_add_indicator_iff` are chapter bridges between the real branch
  and the ambient owner function.
- Primitive data vs derived API: the primitive datum is the real-valued branch
  `x ↦ - (∏ i, x i)^(1 / card ι)` on the ambient finite product; the global `WithBotTop ℝ`
  owner `negativeGeometricMean ι` and its pointwise formulas are derived owner-level API.
- Domain-style sampling used here: `Function.toWithBotTopOn`, `orthant[ℝ](E)`,
  `indicator`, the canonical owner identity
  `Function.toWithBotTopOn_eq_add_indicator`, and the convexity bridge
  `isConvex_toWithBotTop_add_indicator_iff`.
- Layer target: `source-facing`, but on the chapter's canonical ambient `WithBotTop ℝ` owner
  rather than through a separate `WithTop ℝ` wrapper.
- Ambient owner check: the carrier is the intrinsic finite product `ι → ℝ`; no Euclidean or
  inner-product model is required for this coordinatewise statement.
-/

/-- Real-valued finite branch of Remark 4.5.2.
The scalar layer is intrinsically `ℝ`: the geometric mean uses a generally nonintegral
exponent `1 / card ι`, whose canonical primitive owner in this project is `Real.rpow`. -/
def negativeGeometricMeanBranch : E → ℝ :=
  fun x ↦ -(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ)))

/-- Remark 4.5.2: for any finite coordinate family, the ambient extended-real-valued
function that equals the negative geometric mean on the nonnegative orthant and `+∞` outside it.
The textbook `R^n` function is the specialization `ι = Fin n` with `n ≥ 1`. -/
def negativeGeometricMean : E → WithBotTop ℝ :=
  Function.toWithBotTopOn negativeGeometricMeanBranch
    orthant[ℝ](E)

/-- Source-facing bridge form: `negativeGeometricMean` equals the branch plus the orthant
indicator. -/
theorem negativeGeometricMean_eq_add_indicator :
    negativeGeometricMean =
      negativeGeometricMeanBranch.toWithBotTop +
        (fun x : E ↦ δ[ℝ](x | orthant[ℝ](E))) := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_eq_add_indicator
      negativeGeometricMeanBranch
      (orthant[ℝ](E)))

/-- Outside the nonnegative orthant, `negativeGeometricMean` is `+∞`. -/
@[simp] theorem negativeGeometricMean_apply_of_not_mem_orthant {x : E}
    (hx : x ∉ orthant[ℝ](E)) :
    negativeGeometricMean x = ⊤ := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_of_notMem
      (f := negativeGeometricMeanBranch)
      (C := orthant[ℝ](E)) hx)

/-- On the nonnegative orthant, the ambient owner agrees with the real branch owner. -/
@[simp] theorem negativeGeometricMean_apply_of_mem_orthant_eq_branch {x : E}
    (hx : x ∈ orthant[ℝ](E)) :
    negativeGeometricMean x = negativeGeometricMeanBranch.toWithBotTop x := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_of_mem
      (f := negativeGeometricMeanBranch)
      (C := orthant[ℝ](E)) hx)

/-- On the nonnegative orthant, `negativeGeometricMean` is given by the negative
geometric-mean formula. -/
theorem negativeGeometricMean_apply_of_mem_orthant {x : E}
    (hx : x ∈ orthant[ℝ](E)) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  simpa [negativeGeometricMeanBranch, Function.toWithBotTop] using
    (negativeGeometricMean_apply_of_mem_orthant_eq_branch (x := x) hx)

/-- Intrinsic-order view: `0 ≤ x` is exactly membership in `orthant[ℝ](E)`. -/
theorem negativeGeometricMean_apply_of_nonneg {x : E} (hx : (0 : E) ≤ x) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  exact negativeGeometricMean_apply_of_mem_orthant <|
    (mem_orthant_iff).2 hx

/-- Coordinatewise bridge view of `negativeGeometricMean_apply_of_nonneg`. -/
theorem negativeGeometricMean_apply_of_coordwise_nonneg {x : E}
    (hx : ∀ i : ι, 0 ≤ x i) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  exact negativeGeometricMean_apply_of_nonneg (x := x) (by simpa using hx)

-- Proof sketch: rewrite the ambient function as the chapter owner
-- `Function.toWithBotTopOn negativeGeometricMeanBranch
-- (orthant[ℝ](E))`, equivalently the
-- bridge form from `negativeGeometricMean_eq_add_indicator`;
-- then apply the extension-by-`+∞`
-- bridge `isConvex_toWithBotTop_add_indicator_iff`, and prove convexity of the finite
-- branch on the nonnegative orthant by the Hessian argument from Theorem 4.5. The textbook
-- statement is the nonempty specialization `ι = Fin n` with `n ≥ 1`.
/-- Remark 4.5.2: the function that equals the negative geometric mean on the nonnegative orthant
and `+∞` otherwise is convex. -/
theorem negativeGeometricMean_isConvex :
    (negativeGeometricMean : E → WithBotTop ℝ).IsConvex ℝ := sorry

end

/-! ### Remark_4_5_3 (from Chap01) -/
section

/- 
Source/core/bridge triage:
- `source-facing`: Remark 4.5.3 says the norm on `ℝⁿ` is convex, with the one-dimensional case
  giving convexity of `abs`.
- `core/canonical`: the intrinsic owner theorem is mathlib's `convexOn_univ_norm` on an arbitrary
  real normed space.
- `bridge/view`: first pass to the chapter owner theorem for `‖·‖` through
  `Function.isConvex_coe_of_convexOn_univ`, then specialize to dimension one and rewrite
  `‖x‖ = |x|` using `Real.norm_eq_abs`.
- Primitive data vs derived API: the primitive object is the canonical norm function `‖·‖`; the
  one-dimensional `abs` statement is a downstream bridge specialization.
- Domain-style sampling used here: `convexOn_univ_norm`, `ConvexOn.convex_epigraph`,
  `Function.IsConvex`, `Function.isConvex_coe_of_convexOn_univ`, `Function.isConvex_norm`,
  and `Real.norm_eq_abs`.
- Layer target: `core/canonical` for the owner theorem `Function.isConvex_norm`; the
  one-dimensional bridge is intentionally downstream.
-/

/- Remark 4.5.3: the intrinsic owner fact is the canonical theorem `convexOn_univ_norm`; the
textbook `ℝⁿ` statement is an exact specialization, so the main entry remains a direct recall
rather than a parallel local wrapper theorem. -/
recall convexOn_univ_norm

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: pass from `convexOn_univ_norm` to the chapter owner predicate
-- `Function.IsConvex` through the canonical coercion bridge.
/-- Remark 4.5.3 on the chapter owner surface: the norm is globally convex as a
`WithTopBot ℝ`-valued function on any real normed space. -/
theorem Function.isConvex_norm :
    ((norm : E → ℝ).toWithTopBot).IsConvex ℝ := by
  exact Function.isConvex_coe_of_convexOn_univ convexOn_univ_norm

end

end

/-! ### Definition_4_5 (from Chap01) -/
/- 
Source/core/bridge triage:
- `source-facing`: Definition 4.5 names the dimension of a function as the dimension of its
  effective domain; concrete coordinate statements are downstream specializations.
- `core/canonical`: the owner abstractions are `effectiveDomain` from Definition 4.4 and the
  chapter declaration `Set.affineDim` from Definition 2.4.10.
- `bridge/view`: the effective domain is expressed directly by the canonical notation `dom(f)`, so
  the source reading belongs on the composite owner expression `dim[𝕜](dom(f))`; no
  separate function-side owner is needed.
- Domain-style sampling: the relevant declarations in this domain are the owner
  `AffineSubspace.affineDim` from Theorem 1.3, the chapter bridge `Set.affineDim` from
  Definition 2.4.10, and the primitive set-valued bridge `effectiveDomain` from Definition 4.4.
- Primitive data vs derived API: the effective domain formula is the primitive set-valued bridge;
  the function dimension is the derived owner-side reading `Set.affineDim (dom(f))`, not a new
  packaged owner.
- Layer target: `bridge/view`, by direct recall/use of the intrinsic affine-space owner level
  instead of a parallel function wrapper.
-/

/- Definition 4.5 is a direct composite of existing owners:
`effectiveDomain` (`dom(f)`) and `Set.affineDim` (`dim[𝕜](·)`).
No function-side alias theorem is introduced. -/
recall effectiveDomain
recall Set.affineDim

/-! ### Theorem_4_5 (from Chap01) -/
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {C : Set 𝕜} {f : 𝕜 → 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 4.5 is the Hessian characterization of convexity for a twice
  differentiable scalar-valued function on a convex domain.
- `core/canonical`: the statement owner is `ConvexOn 𝕜 C f`, and the second-order owner is the
  canonical set-local bilinear second derivative `bilinearIteratedFDerivWithinTwo 𝕜 f C`.
- `bridge/view`: the primary statement is intrinsic/relative, using `intrinsicInterior 𝕜 C`;
  the ambient-open textbook form is a derived corollary.

Scalar/ambient note:
- The intrinsic-owner shift is kept on theorem surfaces.
- The scalar/ambient layer is one-dimensional over an ordered normed field `𝕜`; the theorem is
  expressed on the intrinsic owner route through `IsOpen.convexOn_iff_nonneg_deriv2` from
  Theorem 4.4.
-/

lemma differentiableOn_deriv_of_differentiableOn_fderivWithin
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    DifferentiableOn 𝕜 (deriv f) C := by
  intro x hx
  have hc : DifferentiableAt 𝕜 (fderivWithin 𝕜 f C) x :=
    (hf' x hx).differentiableAt (hC_open.mem_nhds hx)
  have hfun : (fun y : 𝕜 ↦ (fderivWithin 𝕜 f C y) 1) = derivWithin f C := by
    funext y
    exact fderivWithin_derivWithin (𝕜 := 𝕜) (f := f) (s := C) (x := y)
  have hdwAt : DifferentiableAt 𝕜 (derivWithin f C) x := by
    simpa [hfun] using hc.clm_apply (differentiableAt_const (1 : 𝕜))
  have hdw_eq : derivWithin f C =ᶠ[nhds x] deriv f := by
    filter_upwards [hC_open.mem_nhds hx] with y hy
    exact derivWithin_of_isOpen hC_open hy
  exact ((hdw_eq.differentiableAt_iff).1 hdwAt).differentiableWithinAt

lemma bilinForm_eq_mul_mul (B : LinearMap.BilinForm 𝕜 𝕜) (x y : 𝕜) :
    B x y = x * y * B 1 1 := by
  calc
    B x y = B (x • (1 : 𝕜)) (y • (1 : 𝕜)) := by simp
    _ = x * B 1 (y • (1 : 𝕜)) := by simpa using B.smul_left x (1 : 𝕜) (y • (1 : 𝕜))
    _ = x * (y * B 1 1) := by
      have hy1 : B 1 (y • (1 : 𝕜)) = y * B 1 1 := by
        simpa using B.smul_right y (1 : 𝕜) (1 : 𝕜)
      rw [hy1]
    _ = x * y * B 1 1 := by ring

lemma bilinForm_isSymm (B : LinearMap.BilinForm 𝕜 𝕜) : B.IsSymm := by
  refine ⟨?_⟩
  intro x y
  calc
    B x y = x * y * B 1 1 := bilinForm_eq_mul_mul B x y
    _ = y * x * B 1 1 := by ring
    _ = B y x := by
      symm
      exact bilinForm_eq_mul_mul B y x

lemma hessianWithin_apply_one_one_eq_derivWithin2
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    (bilinearIteratedFDerivWithinTwo 𝕜 f C x) 1 1 = derivWithin (derivWithin f C) C x := by
  have hc : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f C) C x := hf' x hx
  unfold bilinearIteratedFDerivWithinTwo
  change ((fderivWithin 𝕜 (fderivWithin 𝕜 f C) C x) 1) 1 = derivWithin (derivWithin f C) C x
  rw [fderivWithin_derivWithin (𝕜 := 𝕜) (f := fderivWithin 𝕜 f C) (s := C) (x := x)]
  have hfun : (fun y : 𝕜 ↦ (fderivWithin 𝕜 f C y) 1) = derivWithin f C := by
    funext y
    exact fderivWithin_derivWithin (𝕜 := 𝕜) (f := f) (s := C) (x := y)
  have happlyWithin :=
    derivWithin_clm_apply (s := C) (c := fun y : 𝕜 ↦ fderivWithin 𝕜 f C y)
      (u := fun _ : 𝕜 ↦ (1 : 𝕜)) (x := x) hc
      (differentiableWithinAt_const (s := C) (c := (1 : 𝕜)))
  have happlyWithin' :
      derivWithin (derivWithin f C) C x =
        (derivWithin (fun y : 𝕜 ↦ fderivWithin 𝕜 f C y) C x) 1 := by
    simpa [hfun] using happlyWithin
  simp [happlyWithin']

lemma hessianWithin_apply_one_one_eq_deriv2
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    (bilinearIteratedFDerivWithinTwo 𝕜 f C x) 1 1 = deriv^[2] f x := by
  rw [hessianWithin_apply_one_one_eq_derivWithin2 (hf' := hf') hx]
  simpa using hC_open.derivWithin2_eq_deriv2 (f := f) hx

section Ordered

variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]

omit [OrderTopology 𝕜] [DenselyOrdered 𝕜] in
lemma hessianWithin_posSemidef_iff_nonneg_derivWithin2
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef ↔
      0 ≤ derivWithin (derivWithin f C) C x := by
  let B : LinearMap.BilinForm 𝕜 𝕜 := bilinearIteratedFDerivWithinTwo 𝕜 f C x
  have hB11 : B 1 1 = derivWithin (derivWithin f C) C x := by
    simpa [B] using hessianWithin_apply_one_one_eq_derivWithin2
      (hf' := hf') hx
  constructor
  · intro hpos
    have h11_nonneg : 0 ≤ B 1 1 := hpos.isNonneg.nonneg 1
    simpa [hB11] using h11_nonneg
  · intro hderivWithin2_nonneg
    have h11_nonneg : 0 ≤ B 1 1 := by simpa [hB11] using hderivWithin2_nonneg
    have hnonneg : B.IsNonneg := by
      refine ⟨?_⟩
      intro z
      have hzdiag : B z z = z * z * B 1 1 := bilinForm_eq_mul_mul B z z
      have hzsq_nonneg : 0 ≤ z * z := by nlinarith [sq_nonneg z]
      have : 0 ≤ z * z * B 1 1 := mul_nonneg hzsq_nonneg h11_nonneg
      simpa [hzdiag] using this
    have hpsdB : LinearMap.IsPosSemidef B :=
      (LinearMap.BilinForm.isPosSemidef_iff).1 ⟨bilinForm_isSymm B, hnonneg⟩
    simpa [B] using hpsdB

omit [OrderTopology 𝕜] [DenselyOrdered 𝕜] in
lemma hessianWithin_posSemidef_iff_nonneg_deriv2
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef ↔
      0 ≤ deriv^[2] f x := by
  rw [hessianWithin_posSemidef_iff_nonneg_derivWithin2 (hf' := hf') hx]
  simp [hC_open.derivWithin2_eq_deriv2 (f := f) hx]

/-- Textbook open-set bridge for Theorem 4.5 on the scalar-generic reusable layer (`𝕜 → 𝕜`):
on an open convex domain, convexity is equivalent to set-local Hessian positive semidefiniteness
at every point of the domain. -/
theorem convexOn_iff_hessianWithin_posSemidef_of_isOpen
    {C : Set 𝕜} {f : 𝕜 → 𝕜}
    (hC_open : IsOpen C) (hC_convex : Convex 𝕜 C) (hf : DifferentiableOn 𝕜 f C)
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    ConvexOn 𝕜 C f ↔
      ∀ x ∈ C,
        ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef := by
  have hderiv : DifferentiableOn 𝕜 (deriv f) C :=
    differentiableOn_deriv_of_differentiableOn_fderivWithin hC_open hf'
  have hconv_iff_nonneg : ConvexOn 𝕜 C f ↔
      ∀ x ∈ C, 0 ≤ derivWithin (derivWithin f C) C x := by
    simpa using hC_open.convexOn_iff_nonneg_derivWithin2
      (s := C) (f := f) hC_convex hf hderiv
  constructor
  · intro hconv x hx
    exact (hessianWithin_posSemidef_iff_nonneg_derivWithin2
      (hf' := hf') hx).2 ((hconv_iff_nonneg.mp hconv) x hx)
  · intro hpsd
    refine hconv_iff_nonneg.mpr ?_
    intro x hx
    exact (hessianWithin_posSemidef_iff_nonneg_derivWithin2
      (hf' := hf') hx).1 (hpsd x hx)

/-- Theorem 4.5 at the intrinsic/relative-topology owner layer (on the currently available
upstream scalar/ambient layer `𝕜 → 𝕜`): on an open convex domain, convexity is equivalent to
set-local Hessian positive semidefiniteness on `intrinsicInterior 𝕜 C`. -/
theorem convexOn_iff_hessianWithin_posSemidef
    {C : Set 𝕜} {f : 𝕜 → 𝕜}
    (hC_open : IsOpen C) (hC_convex : Convex 𝕜 C) (hf : DifferentiableOn 𝕜 f C)
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    ConvexOn 𝕜 C f ↔
      ∀ x ∈ intrinsicInterior 𝕜 C,
        ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef := by
  have hC_intrinsicInterior : intrinsicInterior 𝕜 C = C := by
    refine subset_antisymm intrinsicInterior_subset ?_
    simpa [hC_open.interior_eq] using
      (interior_subset_intrinsicInterior : interior C ⊆ intrinsicInterior 𝕜 C)
  simpa [hC_intrinsicInterior] using
    (convexOn_iff_hessianWithin_posSemidef_of_isOpen
      hC_open hC_convex hf hf')

end Ordered

end
