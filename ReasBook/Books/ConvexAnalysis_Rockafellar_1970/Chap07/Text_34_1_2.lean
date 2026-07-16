import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1

noncomputable section

open scoped Rockafellar

namespace Bifunction

open Function

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.2 gives a concrete Chapter 34 counterexample for the iterated partial
  closures of a saddle-function built from the kernel `(u, v) ↦ u / v` on the positive quadrant.
- `core/canonical`: the ambient example is the Chapter 33 bridge owner
  `Bifunction.saddleExtension` applied to the ratio kernel and the positive-quadrant domain sets;
  iterated closures use the Chapter 34 owners `lowerClosure` / `upperClosure`.
- `bridge/view`: Text 34.1.2's pointwise formulas are exposed as formula owners, and the effective
  domain consequences are recorded in hypothesis-parameterized bridge form.

Domain-style sampling used here:
- `Bifunction.saddleExtension` from `Definition33_0_2`;
- `Bifunction.lowerClosure` and `Bifunction.upperClosure` from `Chap07.Defn_34_1`;
- `Function.uncurry` from mathlib as the canonical bridge from a bifunction to an ordinary
  function on `𝕜 × 𝕜`;
- `effectiveDomain` from `Chap01.Definition_4_4`, written in theorem surfaces as `dom(·)`.

Primitive data vs derived API:
- primitive source data: the ratio kernel `(u, v) ↦ u / v` on `𝕜 × 𝕜` together with the domain
  sets `(Ici 0)` and `(Ioi 0)`;
- derived API: the thin saddle-function bridge `saddleExtension`, formula owners for the displayed
  iterated closures, and hypothesis-parameterized effective-domain counterexample consequences.
- scalar/ambient layer: this item is stated over an ordered field-type scalar `𝕜`, because the
  source counterexample only uses ratio and sign/zero boundary behavior at `(0, 0)`.

Layer target: `source-facing`.
-/

section BasicLayer

variable (𝕜 : Type*)

attribute [local instance] Classical.propDecidable

/-- The ratio kernel `(u, v) ↦ u / v` underlying Text 34.1.2. -/
def positiveQuadrantRatio [Div 𝕜] (u v : 𝕜) : 𝕜 :=
  u / v

variable [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]

/-- The Chapter 34 counterexample saddle-function, represented canonically by the Chapter 33
bridge owner `saddleExtension` for the ratio kernel on the positive quadrant. -/
abbrev positiveQuadrantRatioSaddle :
    𝕜 → 𝕜 → WithBotTop 𝕜 :=
  K₁[positiveQuadrantRatio 𝕜 | Set.Ici 0, Set.Ioi 0]

-- Proof sketch: rewrite to the canonical owner `saddleExtension`; on the positive quadrant,
-- the owner-side branch lemma returns the finite value `u / v`.
/-- On the positive quadrant branch, `positiveQuadrantRatioSaddle` agrees with the finite kernel
`u / v`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_nonneg_pos
    {u v : 𝕜} (hu : 0 ≤ u) (hv : 0 < v) :
    positiveQuadrantRatioSaddle 𝕜 u v = ((u / v : 𝕜) : WithBotTop 𝕜) := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v =
    ((u / v : 𝕜) : WithBotTop 𝕜)
  simpa [positiveQuadrantRatio] using
    (saddleExtension_apply_of_mem
      (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜)) hu hv)

-- Proof sketch: rewrite to `saddleExtension`; outside the first-coordinate domain `Ici 0`,
-- the owner-side branch lemma gives the constant value `-∞`.
/-- On the negative first-variable half-plane, `positiveQuadrantRatioSaddle` takes the value
`-∞`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_neg
    {u v : 𝕜} (hu : u < 0) :
    positiveQuadrantRatioSaddle 𝕜 u v = ⊥ := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v = ⊥
  exact saddleExtension_apply_of_not_mem_left
    (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜))
    (show u ∉ Set.Ici (0 : 𝕜) from by simpa using not_le_of_gt hu)

-- Proof sketch: rewrite to `saddleExtension`; once `u ∈ Ici 0` and `v ∉ Ioi 0`, the owner-side
-- branch lemma gives the constant value `+∞`.
/-- On the nonpositive second-variable half-plane over `u ≥ 0`, `positiveQuadrantRatioSaddle`
takes the value `+∞`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_nonneg_nonpos
    {u v : 𝕜} (hu : 0 ≤ u) (hv : v ≤ 0) :
    positiveQuadrantRatioSaddle 𝕜 u v = ⊤ := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v = ⊤
  exact saddleExtension_apply_of_mem_left_of_not_mem_right
    (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜))
    (show u ∈ Set.Ici (0 : 𝕜) from hu)
    (show v ∉ Set.Ioi (0 : 𝕜) from by simpa using not_lt_of_ge hv)

/-! Formula owners used for the two displayed piecewise expressions of Text 34.1.2. -/

/-- The displayed piecewise formula in Text 34.1.2 for the upper iterated closure
`cl₁ (cl₂ K)` of `positiveQuadrantRatioSaddle`. It equals
`u / v` on `u ≥ 0, v > 0`, equals `-∞` on `u < 0, v > 0`, and equals `+∞` on `v ≤ 0`. -/
def positiveQuadrantRatioSaddleUpperClosureFormula
    [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]
    (u v : 𝕜) :
    WithBotTop 𝕜 :=
  if 0 < v then
    if 0 ≤ u then
      ((u / v : 𝕜) : WithBotTop 𝕜)
    else
      ⊥
  else
    ⊤

/-- The displayed piecewise formula in Text 34.1.2 for the lower iterated closure
`cl₂ (cl₁ K)` of `positiveQuadrantRatioSaddle`. It equals
`u / v` on `u ≥ 0, v > 0`, equals `0` at the origin, equals `+∞` on the remaining points with
`u ≥ 0, v ≤ 0`, and equals `-∞` on `u < 0`. -/
def positiveQuadrantRatioSaddleLowerClosureFormula
    [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]
    (u v : 𝕜) :
    WithBotTop 𝕜 :=
  if u < 0 then
    ⊥
  else if 0 < v then
    ((u / v : 𝕜) : WithBotTop 𝕜)
  else if u = 0 ∧ v = 0 then
    0
  else
    ⊤

end BasicLayer

section EffectiveDomainLayer

variable (𝕜 : Type*) [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜]

-- Proof sketch: `lowerClosure positiveQuadrantRatioSaddle` and
-- `upperClosure positiveQuadrantRatioSaddle` take different values at the origin (`0` vs `+∞`);
-- therefore their effective domains cannot coincide.
/-- Text 34.1.2 (3): the effective domains of the lower and upper closures of this counterexample
are different, assuming the two displayed closure formulas. -/
theorem effectiveDomain_lowerClosure_ne_upperClosure_positiveQuadrantRatioSaddle :
    (positiveQuadrantRatioSaddle 𝕜)̲ =
      positiveQuadrantRatioSaddleLowerClosureFormula 𝕜 →
    (positiveQuadrantRatioSaddle 𝕜)̅ =
      positiveQuadrantRatioSaddleUpperClosureFormula 𝕜 →
    dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) ≠
      dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̅)) := by
  intro hLowerFormula hUpperFormula hdom
  have hOriginLower :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    simpa [Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula] using
      (WithBotTop.coe_lt_top (0 : 𝕜))
  have hOriginUpper :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̅)) := by
    simpa [hdom] using hOriginLower
  rw [hUpperFormula] at hOriginUpper
  simp [effectiveDomain, Function.uncurry, positiveQuadrantRatioSaddleUpperClosureFormula]
    at hOriginUpper

-- Proof sketch: by the lower-closure formula, points `(0,0)` and `(1,1)` lie in the effective
-- domain, while `(1,0)` does not. A product decomposition `A ×ˢ B` would force `(1,0)` to belong
-- once `(1,1)` and `(0,0)` do, giving a contradiction.
/-- Text 34.1.2 (4): the effective domain of the lower closure of this counterexample is not a
product set, assuming the displayed lower-closure formula. -/
theorem effectiveDomain_lowerClosure_not_prod_positiveQuadrantRatioSaddle
    [IsOrderedRing 𝕜] :
    (positiveQuadrantRatioSaddle 𝕜)̲ =
      positiveQuadrantRatioSaddleLowerClosureFormula 𝕜 →
    ¬ ∃ A B : Set 𝕜,
      dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) = A ×ˢ B := by
  intro hLowerFormula
  rintro ⟨A, B, hAB⟩
  have h00 :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    simpa [Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula] using
      (WithBotTop.coe_lt_top (0 : 𝕜))
  have h11 :
      ((1 : 𝕜), (1 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    have hnot : ¬ (1 : 𝕜) < 0 := not_lt.mpr zero_le_one
    have hpos : (0 : 𝕜) < 1 := zero_lt_one
    simp only [Set.mem_setOf_eq, uncurry_apply_pair, positiveQuadrantRatioSaddleLowerClosureFormula,
      hnot, hpos, reduceIte, gt_iff_lt]
    exact WithBotTop.coe_lt_top ((1 : 𝕜) / 1)
  have h10 :
      ((1 : 𝕜), (0 : 𝕜)) ∉ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    simp [effectiveDomain, Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula]
  have hB0 : (0 : 𝕜) ∈ B := by
    have hPair : ((0 : 𝕜), (0 : 𝕜)) ∈ A ×ˢ B := by
      simpa [hAB] using h00
    exact hPair.2
  have hA1 : (1 : 𝕜) ∈ A := by
    have hPair : ((1 : 𝕜), (1 : 𝕜)) ∈ A ×ˢ B := by
      simpa [hAB] using h11
    exact hPair.1
  have h10In :
      ((1 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    have hPair : ((1 : 𝕜), (0 : 𝕜)) ∈ A ×ˢ B := ⟨hA1, hB0⟩
    simpa [hAB] using hPair
  exact h10 h10In

end EffectiveDomainLayer

end Bifunction
