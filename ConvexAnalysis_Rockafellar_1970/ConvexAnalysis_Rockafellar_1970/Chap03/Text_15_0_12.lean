import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

attribute [local instance] Function.instDecidableLT

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.12 defines when a gauge on `R^n` is a norm by adding everywhere
  finiteness, symmetry, and strict positivity away from the origin. The owner is stated on a
  scalar-generic additive group, since the reused gauge, convexity, and symmetry ingredients
  already live there; specializing to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the
  source ambient.
- `core/canonical`: the owner predicate already present in the chapter is the imported gauge class
  `IsGauge`, while the symmetry clause is the canonical mathlib predicate `Function.Even`.
- `bridge/view`: the equivalent clause list is most naturally rendered by companion theorems giving
  subadditivity, reconstruction from clauses (a)–(d), and absolute homogeneity.

Domain-style sampling used here:
- `Function.IsConvex` from `Theorem_4_2`, reused through the imported gauge owner `IsGauge`;
- `Function.PositivelyHomogeneous` from `Definition_4_8`, again reused through `IsGauge`;
- `IsGauge` from `Text_15_0_1`;
- `Function.Even` from the even-function API;
- the chapter's pointwise scalar-valued finiteness layer `k x < ⊤`, with the `EReal`/`toReal`
  bridge kept as a real-specialized downstream theorem;
- mathlib's seminorm/norm API as a comparison point confirming that subadditivity belongs to the
  gauge owner while symmetry plus positive definiteness is downstream structure rather than a
  second owner abstraction here.

Primitive data vs derived API:
- primitive owner: being a norm-gauge;
- derived bridge: the clause-based reconstruction theorem, and the absolute-value homogeneity
  consequence `IsGaugeNorm.map_smul_eq_abs`.

Layer target: `source-facing`, because the source is refining the chapter's gauge notion rather
than replacing it by a bundled norm.
-/

/-- Text 15.0.12: a gauge is a norm when it is finite everywhere, symmetric, and strictly positive
away from the origin. Here finiteness is recorded as `k x < ⊤`. Specializing `𝕜 = ℝ` and
`E = EuclideanSpace ℝ (Fin n)` recovers the source statement. -/
class IsGaugeNorm (k : E → WithBotTop 𝕜) : Prop extends IsGauge k where
  finite : ∀ x : E, k x < ⊤
  symmetric : Function.Even k
  pos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < k x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm, viewed as a `WithBotTop ℝ`-valued gauge, is a canonical norm-gauge. -/
instance : IsGaugeNorm (fun x : E ↦ (‖x‖ : WithBotTop ℝ)) where
  toIsGauge :=
    { convex := by
        exact Function.isConvex_coe_of_convexOn_univ convexOn_univ_norm
      nonneg := by
        intro x
        exact WithBotTop.coe_le_coe.mpr (norm_nonneg x)
      homogeneous := by
        intro a x
        change ((‖((a : ℝ) • x)‖ : ℝ) : WithBotTop ℝ) =
          ((((a : ℝ) * ‖x‖ : ℝ)) : WithBotTop ℝ)
        simp [norm_smul, Real.norm_of_nonneg a.2.le]
      map_zero := by
        change ((‖(0 : E)‖ : ℝ) : WithBotTop ℝ) = (0 : WithBotTop ℝ)
        simp }
  finite x := by
    exact lt_top_iff_ne_top.mpr (by simp)
  symmetric := by
    intro x
    simp
  pos := by
    intro x hx
    exact WithBotTop.coe_lt_coe.mpr (norm_pos_iff.mpr hx)

end

section

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: split on the sign of `λ`. For `λ > 0`, use positive homogeneity. For `λ < 0`,
-- rewrite `λ • x = (-λ) • (-x)` and use evenness. For `λ = 0`, both sides vanish.
private theorem map_smul_eq_abs_of_even {k : E → WithBotTop 𝕜}
    (hhom : k.PositivelyHomogeneous 𝕜) (hzero : k 0 = 0) (heven : Function.Even k)
    (a : 𝕜) (x : E) :
    k (a • x) = |a| • k x := by
  by_cases hpos : 0 < a
  · calc
      k (a • x) = a • k x := hhom.map_smul hpos x
      _ = |a| • k x := by rw [abs_of_pos hpos]
  · by_cases hneg : a < 0
    · have hneg' : 0 < -a := neg_pos.mpr hneg
      calc
        k (a • x) = k ((-a) • (-x)) := by simp
        _ = (-a) • k (-x) := hhom.map_smul hneg' (-x)
        _ = (-a) • k x := by rw [heven x]
        _ = |a| • k x := by rw [abs_of_neg hneg]
    · have ha : a = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [ha, hzero]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: combine the inherited positive homogeneity from `IsGauge` with the symmetry field
-- of `IsGaugeNorm`, then apply the generic absolute-homogeneity bridge above.
/-- A norm-gauge is absolutely homogeneous. -/
theorem map_smul_eq_abs (a : 𝕜) (x : E) :
    k (a • x) = |a| • k x :=
  map_smul_eq_abs_of_even hk.toIsGauge.homogeneous hk.toIsGauge.map_zero hk.symmetric a x

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜] [PosMulMono 𝕜] [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: a norm-gauge is in particular a gauge, so Theorem 4.7 recovers subadditivity
-- from the inherited convexity and positive homogeneity once `⊥` is excluded by nonnegativity.
/-- A norm-gauge is subadditive. -/
theorem subadditive (x y : E) :
    k (x + y) ≤ k x + k y :=
  (Function.isConvex_iff_subadditive_of_positivelyHomogeneous
    hk.toIsGauge.homogeneous (fun z ↦ by
      have hnonneg : (0 : WithBotTop 𝕜) ≤ k z := hk.toIsGauge.nonneg z
      intro hz
      simp [hz] at hnonneg)).1 hk.toIsGauge.convex x y

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: strict positivity away from the origin gives one direction, while the inherited
-- gauge axiom `k 0 = 0` gives the reverse implication.
/-- A norm-gauge vanishes exactly at the origin. -/
theorem eq_zero_iff {x : E} :
    k x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hneq
    have hpos : (0 : WithBotTop 𝕜) < k x := hk.pos hneq
    simp [hx] at hpos
  · intro hx
    subst hx
    exact hk.toIsGauge.map_zero

/-- A norm-gauge never takes the value `⊤`. -/
theorem ne_top (x : E) :
    k x ≠ ⊤ :=
  ne_of_lt (hk.finite x)

/-- A norm-gauge never takes the value `⊥`. -/
theorem ne_bot (x : E) :
    k x ≠ ⊥ := by
  intro hx
  have hnonneg : (0 : WithBotTop 𝕜) ≤ k x := hk.toIsGauge.nonneg x
  simp [hx] at hnonneg

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

-- Proof sketch: the hypotheses are exactly clauses (a) through (d) together with everywhere
-- scalar-valuedness, encoded by membership in the coercion range of `WithBotTop 𝕜`.
-- Theorem 4.7 gives convexity from subadditivity and positive homogeneity; the
-- scalar-valued hypothesis rules out `⊥`, so symmetry and positivity recover nonnegativity and the
-- zero value needed to build the inherited gauge structure before packaging the norm-gauge fields.
/-- A scalar-valued function satisfying clauses (a) through (d) is a norm-gauge. -/
theorem of_coe_subadditive_homogeneous_even_pos {k : E → WithBotTop 𝕜}
    (hfinite : ∀ x : E, ∃ r : 𝕜, k x = (r : WithBotTop 𝕜))
    (hsubadd : ∀ x₁ x₂ : E, k (x₁ + x₂) ≤ k x₁ + k x₂)
    (hhom : k.PositivelyHomogeneous 𝕜)
    (heven : Function.Even k)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < k x) :
    IsGaugeNorm k := by
  have hk_ne_bot : ∀ x : E, k x ≠ ⊥ := by
    intro x
    rcases hfinite x with ⟨r, hr⟩
    simp [hr]
  have hk_top : ∀ x : E, k x < ⊤ := by
    intro x
    rcases hfinite x with ⟨r, hr⟩
    exact lt_top_iff_ne_top.mpr (by simp [hr])
  have hzero : k 0 = 0 := by
    rcases hfinite 0 with ⟨r, hr⟩
    have hscale : k ((2 : 𝕜) • (0 : E)) = (2 : 𝕜) • k 0 :=
      hhom.map_smul (by norm_num : 0 < (2 : 𝕜)) (0 : E)
    have hscale' : (r : WithBotTop 𝕜) = ((2 * r : 𝕜) : WithBotTop 𝕜) := by
      simpa [hr, smul_eq_mul] using hscale
    have hreal : r = 2 * r := by
      exact WithBotTop.coe_eq_coe_iff.mp hscale'
    have hr_zero : r = 0 := by linarith
    simp [hr, hr_zero]
  refine
    { toIsGauge := ?_, finite := hk_top, symmetric := heven, pos := hpos }
  refine
    { convex :=
        (Function.isConvex_iff_subadditive_of_positivelyHomogeneous hhom hk_ne_bot).2 hsubadd
      nonneg := ?_
      homogeneous := hhom
      map_zero := by simp [hzero] }
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [hzero]
  · exact le_of_lt (hpos hx)

end IsGaugeNorm

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

namespace IsGaugeNorm

variable {k : E → WithBotTop ℝ} [hk : IsGaugeNorm k]

/-- The real value underlying a norm-gauge vanishes exactly at the origin. -/
theorem toReal_eq_zero_iff {x : E} :
    EReal.toReal (k x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    rcases (EReal.toReal_eq_zero_iff).1 hx with hzero | htop | hbot
    · exact eq_zero_iff.1 hzero
    · exact (ne_top x htop).elim
    · exact (ne_bot x hbot).elim
  · intro hx
    exact (EReal.toReal_eq_zero_iff).2 (Or.inl (eq_zero_iff.2 hx))

end IsGaugeNorm

end
