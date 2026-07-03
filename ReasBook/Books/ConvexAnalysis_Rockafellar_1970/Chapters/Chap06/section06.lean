import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_6_1 (from Chap02) -/
open scoped Pointwise Rockafellar

section IntrinsicInteriorUnit

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Unit-scalar dilation commutes with relative interior for any set in a topological
`𝕜`-module. This is the primitive owner theorem behind nonzero-scalar transport, obtained by
transport along the continuous affine equivalence `x ↦ u • x`. -/
@[simp] theorem intrinsicInterior_smul_unit (C : Set E) (u : 𝕜ˣ) :
    ri[𝕜]((u : 𝕜) • C) = (u : 𝕜) • ri[𝕜](C) := by
  let e : E ≃ᴬ[𝕜] E :=
    (ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := E) u).toContinuousAffineEquiv
  simpa [e, Units.smul_def] using ContinuousAffineEquiv.image_intrinsicInterior e C

/-- Unit scalar dilation in `IsUnit` form: this keeps the owner at ring level and avoids
division-ring hypotheses when invertibility is provided directly. -/
@[simp] theorem intrinsicInterior_smul_of_isUnit (C : Set E) (a : 𝕜) (ha : IsUnit a) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases ha with ⟨u, rfl⟩
  exact intrinsicInterior_smul_unit (C := C) (u := u)

end Set

end IntrinsicInteriorUnit

section IntrinsicInteriorZero

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

namespace Set

/-- Zero scalar dilation commutes with relative interior as soon as the relative interior is
nonempty. This is the primitive zero-scalar owner theorem used to build the all-scalar bridge. -/
theorem intrinsicInterior_zero_smul (C : Set E) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜]((0 : 𝕜) • C) = (0 : 𝕜) • ri[𝕜](C) := by
  have hCne : C.Nonempty := hri.mono intrinsicInterior_subset
  rw [Set.zero_smul_set hCne, Set.zero_smul_set hri]
  exact intrinsicInterior_singleton (x := (0 : E))

attribute [simp] intrinsicInterior_zero_smul

end Set

end IntrinsicInteriorZero

section IntrinsicInteriorNonzero

variable
    {𝕜 E : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Nonzero scalar dilation commutes with relative interior for any set in a topological
`𝕜`-module. This is the division-ring bridge obtained from the unit-scalar owner theorem. -/
@[simp] theorem intrinsicInterior_smul_of_ne_zero (C : Set E) (a : 𝕜) (ha : a ≠ 0) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  exact intrinsicInterior_smul_of_isUnit C a (isUnit_iff_ne_zero.mpr ha)

end Set

end IntrinsicInteriorNonzero

section IntrinsicInteriorScalar

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Scalar dilation commutes with relative interior from primitive scalar data:
either `a = 0` or `a` is a unit, together with nonemptiness of `ri[𝕜](C)`. -/
@[simp] theorem intrinsicInterior_smul (C : Set E) (a : 𝕜)
    (ha : a = 0 ∨ IsUnit a) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases ha with rfl | ha
  · simpa using intrinsicInterior_zero_smul (C := C) hri
  · simpa using intrinsicInterior_smul_of_isUnit C a ha

end Set

end IntrinsicInteriorScalar

section IntrinsicInterior

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 6.6.1 states that dilating a convex subset of a finite-dimensional
  normed space over `𝕜` by a scalar dilates its relative interior by the same scalar.
- `core/canonical`: the owner theorem is `Set.intrinsicInterior_smul`, whose primitive input is
  the set `C`, the scalar `a`, the witness `a = 0 ∨ IsUnit a`, and nonemptiness of `ri[𝕜](C)`.
- `bridge/view`: the source all-scalar convex corollary recovers that primitive nonemptiness in
  finite-dimensional spaces via `Convex.intrinsicInterior_nonempty`.
- Primitive data vs derived API: transport needs only `a = 0 ∨ IsUnit a` and
  `Nonempty (ri[𝕜](C))`; convexity and finite-dimensional ambient structure are source-facing
  bridge data used to produce these owner inputs.
- Domain-style sampling: the relevant declarations are `ContinuousLinearEquiv.smulLeft`,
  `ContinuousAffineEquiv.image_intrinsicInterior`,
  `Convex.intrinsicInterior_nonempty`, and `Set.zero_smul_set`.
- Layer target: this item exposes both layers explicitly: the canonical all-scalar owner theorem on
  `Set`, and the source-facing convex bridge in `namespace Convex`.
-/

namespace Convex

/-- Corollary 6.6.1: for a convex subset `C` of a finite-dimensional normed space over `𝕜` and any
scalar `λ : 𝕜`, the relative interior of the dilate `λ • C` is the dilate of the relative
interior of `C`. This is the source-facing all-scalar bridge over the nonzero owner theorem and
the zero-scalar singleton/nonempty-relative-interior bridge at `λ = 0`. -/
@[simp] theorem intrinsicInterior_smul {C : Set E} (hC : Convex 𝕜 C) (a : 𝕜) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · simp
  · have ha : a = 0 ∨ IsUnit a := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · exact Or.inl ha0
      · exact Or.inr (isUnit_iff_ne_zero.mpr ha0)
    simpa using Set.intrinsicInterior_smul C a ha (hC.intrinsicInterior_nonempty hCne)

end Convex

end IntrinsicInterior

/-! ### Corollary_6_6_2 (from Chap02) -/
open scoped Pointwise Rockafellar

section IntrinsicInterior

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.6.2 states the relative-interior and closure formulas for the
  Minkowski sum `C₁ + C₂` of two convex subsets of a finite-dimensional normed space over `𝕜`,
  with a specialization to the textbook `ℝ^n` model.
- `core/canonical`: the owner abstractions are `Convex.intrinsicInterior_linear_image` for
  relative interior under linear images, `ri_prod_eq` for products,
  `add_image_prod` for the addition-map image of a product, and `vadd_set_closure_subset` for
  the closure inclusion under continuous additive actions.
- `bridge/view`: Rockafellar's `ri` and `cl` are represented by `intrinsicInterior 𝕜` and
  `closure`, while the proof route factors the Minkowski sum through the linear addition map
  applied to the product set `C₁ ×ˢ C₂`; clause (2) is then rewritten from `+ᵥ` to the textbook
  pointwise-addition notation `+`.
- Domain-style sampling used here: `Convex.intrinsicInterior_linear_image`,
  `ri_prod_eq`, `add_image_prod`, and `vadd_set_closure_subset`.
- Best owner abstraction: there is no exact upstream additive theorem with the target interface, so
  the canonical owner remains `Convex.intrinsicInterior_linear_image`; clause (1) is therefore the
  minimal source-facing additive bridge obtained from that owner plus `ri_prod_eq`,
  while clause (2) is the minimal source-facing additive specialization of
  `vadd_set_closure_subset`, not a parallel replacement owner.
- Primitive data vs derived API: in clause (1), the primitive data are the two convexity proofs,
  so the Minkowski-sum relative-interior identity is derived API on the `Convex` owner; clause (2)
  adds no new primitive data and is the derived additive surface form of the canonical action
  theorem.
- Layer target: both clauses stay `source-facing`; clause (1) is a thin bridge on the chapter
  owner theorem, and clause (2) is a thin additive bridge on the canonical action theorem.
- Semantic note: the closure inclusion is valid without convexity assumptions, so those source
  adjectives are removed from clause (2) as mathematically redundant.
-/

namespace Convex

/-- Corollary 6.6.2 (1): for convex sets `C₁` and `C₂` in a finite-dimensional normed space over
`𝕜`, the relative interior of their Minkowski sum is the Minkowski sum of their relative
interiors.
Specializing to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. This is the
source-facing additive bridge built from `Convex.intrinsicInterior_linear_image`. -/
-- Proof sketch: apply the linear-image theorem from Theorem 6.6 to the addition map
-- `(x₁, x₂) ↦ x₁ + x₂` on `E × E`, then simplify the source and target images with the product
-- formula from Text 6.18 and `Set.add_image_prod`.
@[simp] theorem intrinsicInterior_add {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hC₂ : Convex 𝕜 C₂) :
    ri[𝕜](C₁ + C₂) = ri[𝕜](C₁) + ri[𝕜](C₂) := by
  simpa [ri_prod_eq, Set.add_image_prod] using
    (hC₁.prod hC₂).intrinsicInterior_linear_image
      (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E)

end Convex

end IntrinsicInterior

section Closure

variable {E : Type*} [TopologicalSpace E] [Add E] [ContinuousAdd E]

namespace Set

/- Corollary 6.6.2 (2): for subsets `C₁` and `C₂` of a topological additive space, the sum of
their closures is contained in the closure of their Minkowski sum. Equivalently,
`closure C₁ + closure C₂ ⊆ closure (C₁ + C₂)`. This is the additive specialization of the
canonical theorem `vadd_set_closure_subset`; specializing further to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
theorem closure_add_subset (C₁ C₂ : Set E) :
    closure C₁ + closure C₂ ⊆ closure (C₁ + C₂) := by
  simpa [vadd_eq_add] using (vadd_set_closure_subset C₁ C₂)

end Set

end Closure

/-! ### Text_6_6 (from Chap02) -/
open Metric
open scoped Pointwise Rockafellar

section

variable {P : Type*} [PseudoMetricSpace P]

/-- The witness-set neighborhood `{x | ∃ y ∈ C, dist x y ≤ ε}` is exactly the union of the
closed balls of radius `ε` centered at points of `C`. -/
theorem points_within_distance_le_eq_iUnion_closedBall (C : Set P) (ε : ℝ) :
    {x : P | ∃ y ∈ C, dist x y ≤ ε} = ⋃ y ∈ C, closedBall y ε := by
  ext x
  simp [mem_closedBall]

end

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.6 identifies the radius-`ε` neighborhood of a set `C` with a
  pointwise-set sum.
- `core/canonical`: before introducing any normed-space-specific bridge, the intrinsic owner level
  is metric witness neighborhoods and translated closed balls:
  `{x | ∃ y ∈ C, dist x y ≤ ε} = C +ᵥ closedBall 0 ε`.
- `bridge/view`: in real normed spaces, Text 6.5 upgrades `closedBall 0 ε` to `ε • B`,
  giving the textbook `C + ε • B` surface.
- `bridge/view` sampled but not adopted as the main owner: `Metric.cthickening ε C` and the
  compact/proper-space bridges `Metric.IsCompact.cthickening_eq_biUnion_closedBall` and
  `Metric.cthickening_eq_biUnion_closedBall`. They describe closed thickenings via
  infimum distance, which is stronger than the source-facing existential witness set when the
  nearest point need not be attained.
- Primitive data vs derived API: the primitive data are the set `C`, radius `ε`, and the additive
  action/translation structure; `C + closedBall 0 ε` and `C + ε • B` are derived additive views.
- Domain-style sampling: `closedBall_eq_vadd_closedBall_zero` and `Metric.mem_closedBall`.
- Layer target: expose the intrinsic owner theorem
  `points_within_distance_le_eq_vadd_closedBall_zero` first, then derive additive surfaces.
-/

/-- Intrinsic owner theorem for Text 6.6: the union of radius-`ε` closed balls centered at points
of `C` is exactly the additive-action translate `C +ᵥ closedBall 0 ε`. -/
theorem iUnion_closedBall_eq_vadd_closedBall_zero (C : Set E) (ε : ℝ) :
    (⋃ y ∈ C, closedBall y ε) = C +ᵥ closedBall (0 : E) ε := by
  calc
    (⋃ y ∈ C, closedBall y ε) = ⋃ y ∈ C, y +ᵥ closedBall (0 : E) ε := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion₂.mp hx with ⟨y, hyC, hxBall⟩
        have hxVadd : x ∈ y +ᵥ closedBall (0 : E) ε := by
          rw [← closedBall_eq_vadd_closedBall_zero (a := y) (ε := ε)]
          exact hxBall
        exact Set.mem_iUnion₂.mpr ⟨y, hyC, hxVadd⟩
      · intro hx
        rcases Set.mem_iUnion₂.mp hx with ⟨y, hyC, hxVadd⟩
        have hxBall : x ∈ closedBall y ε := by
          rw [← closedBall_eq_vadd_closedBall_zero (a := y) (ε := ε)] at hxVadd
          exact hxVadd
        exact Set.mem_iUnion₂.mpr ⟨y, hyC, hxBall⟩
    _ = Set.image2 (fun y z : E ↦ y +ᵥ z) C (closedBall (0 : E) ε) := by
      simpa using
        (Set.iUnion_image_left
          (f := fun y z : E ↦ y +ᵥ z)
          (s := C) (t := closedBall (0 : E) ε))
    _ = C +ᵥ closedBall (0 : E) ε := by
      simp

/-- Additive bridge for Text 6.6: rewriting the intrinsic `+ᵥ` owner gives the pointwise-set sum
surface `C + closedBall 0 ε`. -/
theorem iUnion_closedBall_eq_add_closedBall_zero (C : Set E) (ε : ℝ) :
    (⋃ y ∈ C, closedBall y ε) = C + closedBall (0 : E) ε := by
  simpa [vadd_eq_add] using iUnion_closedBall_eq_vadd_closedBall_zero (C := C) ε

/-- Intrinsic Text 6.6 statement: points within distance `ε` from `C` form
`C +ᵥ closedBall 0 ε`. -/
theorem points_within_distance_le_eq_vadd_closedBall_zero (C : Set E) (ε : ℝ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = C +ᵥ closedBall (0 : E) ε := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = ⋃ y ∈ C, closedBall y ε := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ε
    _ = C +ᵥ closedBall (0 : E) ε := by
      simpa using iUnion_closedBall_eq_vadd_closedBall_zero (C := C) ε

/-- Additive bridge for Text 6.6: points within distance `ε` from `C` form
`C + closedBall 0 ε`. -/
theorem points_within_distance_le_eq_add_closedBall_zero (C : Set E) (ε : ℝ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = C + closedBall (0 : E) ε := by
  simpa [vadd_eq_add] using points_within_distance_le_eq_vadd_closedBall_zero (C := C) ε

end

section

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
the union of closed balls centered at points of `C` with radius `‖u‖` is `C + u • B`,
with invertibility carried intrinsically by the unit `u : 𝕜ˣ`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit
    (C : Set E) (u : 𝕜ˣ) :
    (⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖) = C + (u : 𝕜) • B := by
  calc
    (⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖) = C + closedBall (0 : E) ‖(u : 𝕜)‖ := by
      simpa using iUnion_closedBall_eq_add_closedBall_zero (C := C) ‖(u : 𝕜)‖
    _ = C + (u : 𝕜) • B := by
      have hball : closedBall (0 : E) ‖(u : 𝕜)‖ = (u : 𝕜) • B := by
        simpa using
          (closedBall_eq_add_smul_unitClosedBall_unit (a := (0 : E)) (u := u))
      simp [hball]

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
the union of closed balls centered at points of `C` with radius `‖c‖` is `C + c • B`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall_of_ne_zero
    (C : Set E) (c : 𝕜) (hc : c ≠ 0) :
    (⋃ y ∈ C, closedBall y ‖c‖) = C + c • B := by
  let u : 𝕜ˣ := ⟨c, c⁻¹, by simp [hc], by simp [hc]⟩
  simpa [u] using iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
points lying within distance at most `‖u‖` of `C` are exactly `C + u • B`,
with invertibility carried intrinsically by the unit `u : 𝕜ˣ`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall_unit
    (C : Set E) (u : 𝕜ˣ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖(u : 𝕜)‖} = C + (u : 𝕜) • B := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ‖(u : 𝕜)‖} = ⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖ := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ‖(u : 𝕜)‖
    _ = C + (u : 𝕜) • B := by
      simpa using iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
points lying within distance at most `‖c‖` of `C` are exactly `C + c • B`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall_of_ne_zero
    (C : Set E) (c : 𝕜) (hc : c ≠ 0) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = C + c • B := by
  let u : 𝕜ˣ := ⟨c, c⁻¹, by simp [hc], by simp [hc]⟩
  simpa [u] using points_within_distance_le_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner):
the union of closed balls centered at points of `C` with radius `‖c‖` is exactly `C + c • B`;
the endpoint `c = 0` uses `T1Space`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall
    [T1Space E] (C : Set E) (c : 𝕜) :
    (⋃ y ∈ C, closedBall y ‖c‖) = C + c • B := by
  by_cases hc : c = 0
  · subst hc
    ext x
    simp [Metric.closedBall_zero']
  · exact iUnion_closedBall_norm_eq_add_smul_unitClosedBall_of_ne_zero (C := C) c hc

/-- Text 6.6 (canonical scalar-generic owner):
points lying within distance at most `‖c‖` of `C` are exactly `C + c • B`;
the endpoint `c = 0` uses `T1Space`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall
    [T1Space E] (C : Set E) (c : 𝕜) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = C + c • B := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = ⋃ y ∈ C, closedBall y ‖c‖ := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ‖c‖
    _ = C + c • B := by
      simpa using iUnion_closedBall_norm_eq_add_smul_unitClosedBall (C := C) c

end

/-! ### Theorem_6_6 (from Chap02) -/
section

open AffineSubspace Submodule
open scoped Rockafellar

section RelativeInterior

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 6.6 (1) states how relative interiors behave under a linear
  transformation of a convex subset of a finite-dimensional normed space over `𝕜` into a normed
  space over the same scalar field.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, `intrinsicInterior 𝕜` (surface notation
  `ri[𝕜](·)`), `closure`,
  the set image `A '' C` of a `LinearMap`, and the general continuity theorem
  `image_closure_subset_closure_image`.
- `bridge/view`: Rockafellar's `ri C` is represented by the canonical chapter notation
  `ri[𝕜](C)`, and the
  textbook notation `AC` is represented by the set image `A '' C`.
- Domain-style sampling used here: `Convex.linear_image`,
  `LinearMap.finiteDimensional_range`, `LinearMap.surjective_rangeRestrict`,
  `AffineIsometry.image_intrinsicInterior`, and
  `image_closure_subset_closure_image`.
- Primitive data vs derived API: the primitive owner data is `hC : Convex 𝕜 C`; the
  relative-interior identity is derived API on that owner. By contrast, the closure inclusion is
  already owned upstream by `image_closure_subset_closure_image`, so keeping a second local theorem
  would be duplicate wheel.
- Redundant-assumption cleanup: the codomain `F` need not be finite-dimensional; only the source
  space `E` needs the finite-dimensional hypothesis to support the chapter's relative-interior
  machinery and continuity of linear maps out of `E`.
- Layer target: clause (1) remains `source-facing` but is expressed as owner-style `Convex` API;
  clause (2) is a direct `core/canonical` recall.
-/

namespace Convex

/-- Theorem 6.6 (1): for a convex set `C` in a finite-dimensional normed space over `𝕜` and a
linear map `A` into a normed space over the same scalar field, the relative interior of the image
`A '' C` is exactly the image of the relative interior of `C`. -/
-- Proof sketch: factor `A` through its finite-dimensional range `LinearMap.range A`. The induced
-- map `E → LinearMap.range A` has the same set image as `A`, while the subtype
-- `LinearMap.range A → F` is an affine isometry, so `AffineIsometry.image_intrinsicInterior`
-- transfers relative interiors between the range and the ambient codomain. This reduces the
-- statement to the finite-dimensional codomain case, where `A '' intrinsicInterior 𝕜 C` and
-- `A '' C` have the same closure by `Convex.closure_intrinsicInterior_eq_closure` together with
-- `image_closure_subset_closure_image`, and the relative-interior identity follows inside the
-- finite-dimensional range model.
@[simp] theorem intrinsicInterior_linear_image {C : Set E} (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F) :
    ri[𝕜](A '' C) = A '' ri[𝕜](C) := by
  let A' := A.rangeRestrict
  have himage_subset :
      A' '' ri[𝕜](C) ⊆ ri[𝕜](A' '' C) := by
    let S : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    let T : AffineSubspace 𝕜 A.range := affineSpan 𝕜 (A' '' C)
    have hmap : S.map A'.toAffineMap = T := by
      simpa [S, T] using AffineSubspace.map_span A'.toAffineMap C
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨xS, hxS, rfl⟩
    haveI : Nonempty S := ⟨xS⟩
    haveI : Nonempty T := by
      rw [← hmap]
      infer_instance
    let φ : S →ᵃ[𝕜] T := A'.toAffineMap.restrict (by
      simp [hmap])
    have hφ_surj : Function.Surjective φ := by
      simpa [φ] using AffineMap.restrict.surjective A'.toAffineMap hmap
    have hφlin_surj : Function.Surjective φ.linear :=
      (AffineMap.linear_surjective_iff φ).2 hφ_surj
    have hφ_open : IsOpenMap φ :=
      (AffineMap.isOpenMap_linear_iff).1
        (LinearMap.isOpenMap_of_finiteDimensional φ.linear hφlin_surj)
    have hφ_image :
        φ '' (((↑) : S → E) ⁻¹' C) = ((↑) : T → A.range) ⁻¹' (A' '' C) := by
      ext z
      constructor
      · rintro ⟨w, hwC, rfl⟩
        exact ⟨(w : E), hwC, by simp [φ, AffineMap.restrict.coe_apply]⟩
      · rintro ⟨w, hwC, hwz⟩
        refine ⟨⟨w, subset_affineSpan 𝕜 C hwC⟩, hwC, ?_⟩
        apply Subtype.ext
        simpa [φ, AffineMap.restrict.coe_apply] using hwz
    refine ⟨φ xS, ?_, by simp [φ, AffineMap.restrict.coe_apply]⟩
    have hφ_mem :
        φ xS ∈ interior (φ '' (((↑) : S → E) ⁻¹' C : Set S)) :=
      hφ_open.image_interior_subset (((↑) : S → E) ⁻¹' C) ⟨xS, hxS, rfl⟩
    simpa [intrinsicInterior, T, hφ_image] using hφ_mem
  have hclosure :
      closure (A' '' C) = closure (A' '' ri[𝕜](C)) := by
    apply subset_antisymm
    · refine closure_minimal ?_ isClosed_closure
      rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ closure (ri[𝕜](C)) := by
        simpa [hC.closure_intrinsicInterior_eq_closure] using (subset_closure hx : x ∈ closure C)
      exact image_closure_subset_closure_image (LinearMap.continuous_of_finiteDimensional A')
        ⟨x, hx', rfl⟩
    · exact closure_mono (Set.image_mono intrinsicInterior_subset)
  have h_image_convex : Convex 𝕜 (A' '' ri[𝕜](C)) :=
    (hC.intrinsicInterior).linear_image A'
  have hri :
      ri[𝕜](A' '' C) = ri[𝕜](A' '' ri[𝕜](C)) := by
    calc
      ri[𝕜](A' '' C) = ri[𝕜](closure (A' '' C)) := by
        simpa using (hC.linear_image A').intrinsicInterior_closure_eq_intrinsicInterior.symm
      _ = ri[𝕜](closure (A' '' ri[𝕜](C))) := by
        simp [hclosure]
      _ = ri[𝕜](A' '' ri[𝕜](C)) := by
        simpa using h_image_convex.intrinsicInterior_closure_eq_intrinsicInterior
  have hself :
      ri[𝕜](A' '' ri[𝕜](C)) = A' '' ri[𝕜](C) := by
    apply subset_antisymm intrinsicInterior_subset
    intro y hy
    have : y ∈ ri[𝕜](A' '' C) := himage_subset hy
    rw [hri] at this
    exact this
  letI : NormedAddTorsor A.range A.range := SeminormedAddCommGroup.toNormedAddTorsor
  let ι : A.range →ᵃⁱ[𝕜] F := (subtypeₗᵢ A.range).toAffineIsometry
  have himage_eq (s : Set E) : ι '' (A' '' s) = A '' s := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A' x, ⟨x, hx, rfl⟩, rfl⟩
  calc
    ri[𝕜](A '' C) = ri[𝕜](ι '' (A' '' C)) := by
      rw [himage_eq C]
    _ = ι '' ri[𝕜](A' '' C) := by
      exact ι.image_intrinsicInterior (A' '' C)
    _ = ι '' (A' '' ri[𝕜](C)) := by
      simp [hri, hself]
    _ = A '' ri[𝕜](C) := himage_eq (ri[𝕜](C))

end Convex

end RelativeInterior

section ClosureImage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- Theorem 6.6 (2): for any set `C` in a finite-dimensional normed space over `𝕜` and linear map
`A : E →ₗ[𝕜] F`, the image of the closure of `C` is contained in the closure of `A '' C`.
Equivalently, `cl (A C) ⊇ A (cl C)`. This is the canonical owner theorem
`image_closure_subset_closure_image`, with continuity of `A` supplied automatically by
finite-dimensionality of the source through `LinearMap.continuous_of_finiteDimensional`. -/
recall image_closure_subset_closure_image

end ClosureImage

end
