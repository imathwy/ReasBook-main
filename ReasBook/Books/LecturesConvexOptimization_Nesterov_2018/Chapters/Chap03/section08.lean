import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_8 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.8 is a `bridge/view` item in the chapter's Fenchel-conjugacy domain.

Primary domain:
- Fenchel duals of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `fenchelDual` in `Definition_3_1_2_1`, the chapter's source-facing Fenchel-dual owner;
- `fenchelDual_apply` in `Definition_3_1_2_1`, the canonical inner-product-space supremum
  expansion;
- `withTopEffectiveDomain` and the notation `dom f` in `Definition_3_3`, the chapter owner for the
  effective domain `{x | f x < +∞}`;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the core dual-space owner from which
  `fenchelDual` is derived.

Best owner abstraction:
- source-facing: `fenchelDual`, written `φ⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the effective-domain restriction of the supremum formula from `fenchelDual_apply`.

Primitive data:
- `φ : E → WithTop ℝ`.

Derived API:
- the recalled owner `fenchelDual` with notation `φ⋆`;
- the recalled evaluation theorem `fenchelDual_apply`;
- the source-faithful effective-domain expansion theorem below.

Source/core/bridge triage:
- source-facing: the textbook Fenchel dual `φ*`;
- core/canonical: `fenchelConjugate`;
- bridge/view: rewriting the supremum over all `x` as the same supremum over `dom φ`.

The source-facing owner is already present in the chapter as `fenchelDual`, so this file should
not keep a parallel low-level surface phrased directly in terms of
`fenchelConjugate ... (innerₗ _ _)`. The only extra mathematical content here is the textbook
observation that points with value `φ x = +∞` contribute `⊥`, so the supremum may be restricted to
the effective domain `dom φ`.
-/

section

variable (φ : E → WithTop ℝ)

/- Definition 3.8: the textbook Fenchel dual is the chapter owner `fenchelDual`, written `φ⋆`. -/
#check fenchelDual

/- The defining supremum formula is recalled through the canonical companion theorem
`fenchelDual_apply`. -/
#check fenchelDual_apply

variable (s : E)

/-- Helper for Definition 3.8: points outside the effective domain contribute `⊥` to the
Fenchel-dual maximand. -/
lemma fenchelDual_maximand_eq_bot_of_not_mem_dom
    {x : E} (hx : x ∉ dom φ) :
    ((inner ℝ s x : EReal) - withTopToEReal (φ x)) = ⊥ := by
  -- Outside `dom φ`, the function value is `⊤`, so the affine term becomes `x - ⊤ = ⊥`.
  have hx_top : φ x = ⊤ := by
    rw [mem_withTopEffectiveDomain_iff, not_lt_top_iff] at hx
    exact hx
  rw [hx_top]
  exact EReal.sub_top _

/-- Helper for Definition 3.8: removing the `⊥` terms outside `dom φ` does not change the
Fenchel-dual supremum. -/
lemma iSup_fenchelDual_maximand_eq_iSup_dom :
    (⨆ x : E, ((inner ℝ s x : EReal) - withTopToEReal (φ x))) =
      ⨆ x : dom φ, ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1)) := by
  refine le_antisymm ?_ ?_
  · -- Every unrestricted term is either indexed by a domain point, or is `⊥` outside the domain.
    refine iSup_le ?_
    intro x
    by_cases hx : x ∈ dom φ
    · exact le_iSup
        (fun y : dom φ ↦ ((inner ℝ s y.1 : EReal) - withTopToEReal (φ y.1)))
        ⟨x, hx⟩
    · rw [fenchelDual_maximand_eq_bot_of_not_mem_dom (φ := φ) (s := s) hx]
      exact bot_le
  · -- Any domain point is also an index for the unrestricted supremum.
    refine iSup_le ?_
    intro x
    exact le_iSup (fun y : E ↦ ((inner ℝ s y : EReal) - withTopToEReal (φ y))) x.1

-- Proof sketch: expand `fenchelDual_apply`; if `φ x = ⊤`, then
-- `(inner ℝ s x : EReal) - withTopToEReal (φ x) = ⊥`, so those points do not affect the
-- supremum. The remaining points are exactly `dom φ`.
/-- Expanding the Fenchel dual gives the textbook supremum formula over the effective
domain `{x | φ x < +∞}`, written canonically as `dom φ`. -/
theorem fenchelDual_apply_eq_sSup_image_dom :
    (φ⋆) s =
      sSup ((fun x : E ↦ (inner ℝ s x : EReal) - withTopToEReal (φ x)) '' dom φ) := by
  calc
    (φ⋆) s = ⨆ x : E, ((inner ℝ s x : EReal) - withTopToEReal (φ x)) := by
      -- Start from the owner formula for `fenchelDual`.
      rw [fenchelDual_apply]
    _ = ⨆ x : dom φ, ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1)) := by
      -- Restrict the supremum to the effective domain because the complementary terms are `⊥`.
      rw [iSup_fenchelDual_maximand_eq_iSup_dom (φ := φ) (s := s)]
    _ = sSup (Set.range fun x : dom φ ↦
        ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1))) := by
      -- Convert the subtype-indexed `iSup` into the supremum over its range.
      rw [sSup_range]
    _ = sSup ((fun x : E ↦ (inner ℝ s x : EReal) - withTopToEReal (φ x)) '' dom φ) := by
      -- Identify the subtype range with the image of the maximand on `dom φ`.
      congr 1
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩

end

end

/-! ### Lemma_3_8 (from Chap03) -/
noncomputable section

open scoped Pointwise WithTopConvexAnalysis

open Set

universe u

/- Lemma 3.8 lies in the chapter's extended-valued convex-composition / subdifferential-calculus
domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain
- `withTopRealPart` in `Definition_3_3`, the owner finite-value representative
- `ConvexOn.comp` in mathlib, the canonical monotone convex-composition owner on an image set
- `subdifferential` in `Definition_3_1_5`, the owner subgradient-set API

Best owner abstraction:
- source-facing: `monotoneConvexComp`
- core/canonical ambient owners: `withTopEffectiveDomain`, `withTopRealPart`, `ConvexOn.comp`,
  `subdifferential`
- bridge/view: `monotoneConvexComp_apply_of_mem_effectiveDomain`

Primitive data:
- the source-facing composition `monotoneConvexComp φ ψ`

Derived API:
- `monotoneConvexComp_apply_of_mem_effectiveDomain`
- `monotoneConvexComp_convexOn`
- `subdifferential_monotoneConvexComp_eq_convexHull`

The previous file duplicated the chapter owners for effective domains, finite real parts,
convexity, and subdifferentials. Those notions already live upstream, so this file now keeps only
the composition-specific source-facing object and states its monotonicity and subdifferential
conclusions as two atomic theorems directly on the canonical image-set and pointwise-set-operation
surfaces. The convexity clause therefore lives at the weak module layer inherited from
`ConvexOn.comp`, while the subdifferential clause stays on the real inner-product-space layer
required by `∂`, rather than re-specializing either statement to Euclidean coordinates.
-/

/-- The composition used in Lemma 3.8: inside the effective domain of `ψ` it is `φ ∘ ψ`, and
outside that domain it is `+∞`. -/
def monotoneConvexComp {V : Type u} (φ : ℝ → WithTop ℝ) (ψ : V → WithTop ℝ) : V → WithTop ℝ :=
  fun x ↦ if x ∈ dom ψ then φ (withTopRealPart ψ x) else ⊤

/-- On the effective domain of `ψ`, the composition `monotoneConvexComp φ ψ` evaluates as the
outer function `φ` applied to the finite value of `ψ`. -/
@[simp] theorem monotoneConvexComp_apply_of_mem_effectiveDomain {V : Type u} {φ : ℝ → WithTop ℝ}
    {ψ : V → WithTop ℝ} {x : V} (hx : x ∈ dom ψ) :
    monotoneConvexComp φ ψ x = φ (withTopRealPart ψ x) := by
  simp [monotoneConvexComp, hx]

/-- Helper for Lemma 3.8: a point belongs to the effective domain of the monotone convex
composition exactly when it belongs to the effective domain of `ψ` and the resulting finite scalar
lies in the effective domain of `φ`. -/
theorem monotoneConvexComp_dom_iff {V : Type u} {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ}
    {x : V} :
    x ∈ dom (monotoneConvexComp φ ψ) ↔ x ∈ dom ψ ∧ withTopRealPart ψ x ∈ dom φ := by
  constructor
  · intro hx
    by_cases hψx : x ∈ dom ψ
    · -- Inside `dom ψ`, the composition is literally `φ` evaluated at the finite real part of `ψ`.
      refine ⟨hψx, ?_⟩
      rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx] at hx
      simpa [mem_withTopEffectiveDomain_iff] using hx
    · -- Outside `dom ψ`, the composition is `+∞`, so it cannot lie in its own effective domain.
      have htop : monotoneConvexComp φ ψ x = ⊤ := by
        simp [monotoneConvexComp, hψx]
      rw [mem_withTopEffectiveDomain_iff, htop] at hx
      simp at hx
  · rintro ⟨hψx, hφx⟩
    -- Once both finiteness conditions are available, the composition is finite by direct
    -- evaluation on `dom ψ`.
    rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx]
    simpa [mem_withTopEffectiveDomain_iff] using hφx

/-- Helper for Lemma 3.8: on the effective domain of the composition, its finite real part is the
ordinary scalar composition of the finite real parts of `φ` and `ψ`. -/
@[simp] theorem withTopRealPart_monotoneConvexComp_of_mem_dom {V : Type u}
    {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ} {x : V}
    (hx : x ∈ dom (monotoneConvexComp φ ψ)) :
    withTopRealPart (monotoneConvexComp φ ψ) x = withTopRealPart φ (withTopRealPart ψ x) := by
  rcases monotoneConvexComp_dom_iff.mp hx with ⟨hψx, hφx⟩
  -- Compare the two real values after coercing them back to `WithTop ℝ`.
  apply WithTop.coe_injective
  rw [coe_withTopRealPart hx, monotoneConvexComp_apply_of_mem_effectiveDomain hψx,
    coe_withTopRealPart hφx]

section Convexity

variable {V : Type u} [AddCommMonoid V] [Module ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Lemma 3.8, convexity clause: if `ψ : V → ℝ ∪ {+∞}` and `φ : ℝ → ℝ ∪ {+∞}` are convex and
`φ` is nondecreasing on the effective image of `ψ`, then the extended-value composition equal to
`φ ∘ ψ` on `dom ψ` and `+∞` outside that domain is convex. -/
-- Proof sketch: convexity comes from `ConvexOn.comp` applied to the finite real parts, using the
-- monotonicity of `φ` on the effective image of `ψ`.
theorem monotoneConvexComp_convexOn
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ)) :
    ConvexOn ℝ (dom (monotoneConvexComp φ ψ)) (withTopRealPart (monotoneConvexComp φ ψ)) := by
  -- Route correction: the naive `ConvexOn.comp` proof only works once the scalar image
  -- `withTopRealPart ψ '' dom ψ` is known to be convex. In this generalized owner signature that
  -- image-convexity bridge is not yet available from earlier dependencies.
  -- TODO: either prove the earlier segmentwise image-convexity bridge locally or import the exact
  -- earlier prerequisite that upgrades monotonicity on `withTopRealPart ψ '' dom ψ` to a valid
  -- composition theorem on the effective domain.
  sorry

end Convexity

section Subdifferential

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Lemma 3.8, subdifferential clause: at each `x ∈ interior (dom ψ)`, the subdifferential of
the monotone convex composition is the convex hull of the products `λ • g` with
`λ ∈ ∂ φ(withTopRealPart ψ x)` and `g ∈ ∂ ψ(x)`. -/
-- Proof sketch: combine the convex chain rule for directional derivatives at interior points of
-- `dom ψ` with the support-function descriptions of the one-dimensional and vector-valued
-- subdifferentials, then identify the resulting support function with the convex hull of the
-- scalar-vector product set.
theorem subdifferential_monotoneConvexComp_eq_convexHull {x : V}
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ))
    (hx : x ∈ interior (dom ψ)) :
    ∂ (monotoneConvexComp φ ψ)(x) =
      convexHull ℝ (∂ φ((withTopRealPart ψ x)) • ∂ ψ(x)) := by
  -- Route correction: the source proof identifies both sides by a directional-derivative/support
  -- function calculation. This file currently imports only the primitive owner `∂`, so the needed
  -- earlier chain-rule and support-function uniqueness bridges are not yet in scope.
  -- TODO: add the dependency-closed bridges for (i) the directional derivative of the monotone
  -- convex composition and (ii) equality of closed convex sets from equality of support pairings.
  have _hψ_convex := hψ_convex
  have _hφ_convex := hφ_convex
  have _hφ_mono := hφ_mono
  have _hx := hx
  sorry

end Subdifferential

/-! ### Proposition_3_8 (from Chap03) -/
noncomputable section

open scoped Topology WithTopConvexAnalysis

universe u

section Ambient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "S" => Metric.sphere (0 : E) 1
local notation "B" => Metric.closedBall (0 : E) 1

/- Proposition 3.8 lies in the chapter's source-facing unit-disk boundary-extension domain,
generalized from the textbook display model `ℝ²` to the intrinsic owner level of a real normed
space.

Sampled owner-style declarations:
- mathlib `Metric.sphere` and `Metric.closedBall`, the canonical owners of the unit boundary and
  unit closed ball;
- chapter `dom` and `withTopRealPart` from `Definition_3_3`;
- chapter `WithTopConvexAnalysis.effectiveEpigraph` from `Definition_3_3`;
- mathlib `ConvexOn`, the canonical convexity owner on the effective domain;
- mathlib `LowerSemicontinuous`.

Best owner abstraction:
- source-facing: `unitDiskBoundaryExtension`, the textbook unit-disk construction viewed through
  the intrinsic unit-ball owner;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`, `dom f`, and
  `LowerSemicontinuous f`, together with the canonical unit sphere and closed unit ball;
- bridge/view: the effective-epigraph formulation of convexity and the specialization
  `E = EuclideanSpace ℝ (Fin 2)` recovering the textbook unit disk and unit circle.

Primitive data:
- the ambient real normed space `E`;
- the boundary datum `φ : S → ℝ`;
- the source-facing extension `unitDiskBoundaryExtension φ`.

Derived API:
- the open-disk value theorem below;
- the canonical convexity-plus-domain theorem below;
- the lower-semicontinuity criterion below.

The previous theorem surface stated convexity via `constrainedEpigraph Set.univ`, which duplicates
the chapter owner view. This file now uses the canonical `ConvexOn` surface on `dom` directly and
keeps the domain identification as the companion part of the same source-facing proposition. -/

/-- The textbook unit-disk boundary extension, stated at the intrinsic owner level of a real
normed space: it is `0` on the open unit ball, equal to `φ` on the unit sphere, and `⊤` outside
the closed unit ball. Specializing `E = EuclideanSpace ℝ (Fin 2)` recovers the source statement
on the unit disk and unit circle. -/
def unitDiskBoundaryExtension (φ : S → ℝ) : E → WithTop ℝ :=
  let _ : DecidablePred fun x : E ↦ x ∈ S := Classical.decPred _
  fun x ↦
    if _hx : ‖x‖ < 1 then
      (0 : WithTop ℝ)
    else if hs : x ∈ S then
      (φ ⟨x, hs⟩ : WithTop ℝ)
    else
      ⊤

/-- On the open unit ball, `unitDiskBoundaryExtension φ` takes the value `0`. -/
-- Proof sketch: unfold `unitDiskBoundaryExtension` and simplify the first `if` with the strict
-- inequality hypothesis.
theorem unitDiskBoundaryExtension_eq_zero_of_norm_lt_one
    {φ : S → ℝ} {x : E} (hx : ‖x‖ < 1) :
    unitDiskBoundaryExtension φ x = 0 := sorry

/-- Proposition 3.8 at the intrinsic owner level: for a nonnegative function on the unit sphere,
the associated extended-real-valued unit-ball boundary extension is convex in the chapter owner
sense, and its effective domain is exactly the closed unit ball. Specializing to
`EuclideanSpace ℝ (Fin 2)` recovers the textbook unit-disk statement. -/
-- Proof sketch: compute `dom (unitDiskBoundaryExtension φ)` as the closed unit ball. Then verify
-- Jensen's inequality for `withTopRealPart (unitDiskBoundaryExtension φ)` on that domain, using
-- that the interior value is `0` while the boundary datum is nonnegative.
theorem unitDiskBoundaryExtension_convex_and_effectiveDomain
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    ConvexOn ℝ (dom (unitDiskBoundaryExtension φ))
      (withTopRealPart (unitDiskBoundaryExtension φ)) ∧
      dom (unitDiskBoundaryExtension φ) = B := sorry

/-- The unit-ball boundary extension is lower semicontinuous exactly when the boundary datum
vanishes identically on the unit sphere. Specializing to `EuclideanSpace ℝ (Fin 2)` recovers the
textbook unit-disk criterion. -/
-- Proof sketch: if `φ = 0`, the function is the indicator of the closed unit ball. Conversely,
-- approach a boundary point by points from the open unit ball where the function is `0`, and use
-- semicontinuity plus the nonnegativity of `φ`.
theorem unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    LowerSemicontinuous (unitDiskBoundaryExtension φ) ↔ ∀ z : S, φ z = 0 := sorry

end Ambient

end

/-! ### Theorem_3_8 (from Chap03) -/
noncomputable section

universe u v

open scoped ConvexAnalysis WithTopConvexAnalysis

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/- Theorem 3.8 lies in the chapter's `WithTop`-to-`EReal` partial-infimal-projection domain.

Primary mathematical domain:
- constrained fiberwise infima of `WithTop ℝ`-valued convex objectives, expressed on the chapter's
  canonical `EReal` owner.

Relevant owner-style declarations sampled before refinement:
- `partialInfProjection` and `partialInfProjection_convexOn` in `Theorem_3_1_2_3`, the source
  owner and its canonical convexity theorem for real-valued fibers;
- `withTopToEReal`, `dom`, and `withTopRealPart` in `Definition_3_3`, the chapter bridge from
  `WithTop ℝ` data to the owner surface used by convexity statements;
- `extendedRealRealPart` in `Definition_3_1_1_3`, the finite-value bridge on the `EReal` owner;
- mathlib `ConvexOn`, the ambient canonical convexity owner.

Best owner abstraction:
- source-facing: the `WithTop` specialization of convexity for the canonical owner
  `partialInfProjection Q (withTopToEReal ∘ φ)`;
- core/canonical: `partialInfProjection_convexOn`;
- bridge/view: restricting the feasible set to `Q ∩ dom φ` and replacing `withTopToEReal ∘ φ` by
  `Real.toEReal ∘ withTopRealPart φ` on that intrinsic finite-value locus.

Primitive data:
- a convex feasible set `Q : Set (X × Y)`;
- a `WithTop ℝ`-valued objective `φ : X × Y → WithTop ℝ`;
- the convexity witness `ConvexOn ℝ (dom φ) (withTopRealPart φ)`.

Derived API:
- the theorem below, transporting the canonical real-valued infimal-projection convexity theorem
  to the chapter's `WithTop` surface.

Source/core/bridge triage:
- source-facing: Theorem 3.8's `WithTop`-valued partial-infimum convexity statement;
- core/canonical: `partialInfProjection_convexOn`;
- bridge/view: `withTopToEReal`, `withTopRealPart`, and the finite-locus restriction `Q ∩ dom φ`.

The source mathematics adds genuine `WithTop` bridge content, so this file should not collapse to
a pure recall of `partialInfProjection_convexOn`. The refinement instead keeps the source-facing
statement and removes the ad hoc proof gap by proving that points with value `⊤` do not alter the
fiber infimum, so the owner theorem applies directly on the intrinsic finite-value restriction.
-/

/-- Theorem 3.8: if `Q ⊆ X × Y` is convex and `φ : X × Y → ℝ ∪ {+∞}` is convex on its
effective domain, then the constrained partial infimum of the canonical `EReal` view
`withTopToEReal ∘ φ` is convex in the chapter's `EReal` sense. Internally one restricts to
`Q ∩ dom φ` to reuse the real-valued owner theorem, but that restriction is a proof device rather
than a public hypothesis. -/
theorem partialInfProjection_convexOn_of_convexWithTop
    {Q : Set (X × Y)} {φ : X × Y → WithTop ℝ}
    (hQ : Convex ℝ Q)
    (hφ : ConvexOn ℝ (dom φ) (withTopRealPart φ)) :
    ConvexOn ℝ (dom (partialInfProjection Q (withTopToEReal ∘ φ)))
      (extendedRealRealPart (partialInfProjection Q (withTopToEReal ∘ φ))) := by
  let Q' : Set (X × Y) := Q ∩ dom φ
  have hQ' : Convex ℝ Q' := hQ.inter hφ.1
  have hφ' : ConvexOn ℝ Q' (withTopRealPart φ) := by
    refine ⟨hQ', ?_⟩
    intro x hx y hy a b ha hb hab
    exact hφ.2 hx.2 hy.2 ha hb hab
  have hconv : ConvexOn ℝ (dom (partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ)))
      (extendedRealRealPart (partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ))) :=
    partialInfProjection_convexOn hQ' hφ'
  have hproj :
      partialInfProjection Q (withTopToEReal ∘ φ) =
        partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ) := by
    funext x
    let S : Set EReal := (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Q ∧ z.1 = x}
    let T : Set EReal := (Real.toEReal ∘ withTopRealPart φ) '' {z : X × Y | z ∈ Q' ∧ z.1 = x}
    have hTS : T ⊆ S := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz.1.1, hz.2⟩, ?_⟩
      simpa [withTopToEReal] using
        (congrArg withTopToEReal (coe_withTopRealPart hz.1.2)).symm
    have hSinsert : S ⊆ insert ⊤ T := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      by_cases hzdom : z ∈ dom φ
      · right
        refine ⟨z, ⟨⟨hz.1, hzdom⟩, hz.2⟩, ?_⟩
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart hzdom)
      · left
        rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzdom
        have hztop : φ z = ⊤ := by
          simpa using hzdom
        simpa [withTopToEReal] using congrArg withTopToEReal hztop
    change sInf S = sInf T
    refine le_antisymm (sInf_le_sInf hTS) ?_
    simpa using (sInf_le_sInf hSinsert : sInf (insert ⊤ T) ≤ sInf S)
  simpa [hproj] using hconv

end
