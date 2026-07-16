import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_3
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_10

-- Declarations for this item will be appended below by the statement pipeline.

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
