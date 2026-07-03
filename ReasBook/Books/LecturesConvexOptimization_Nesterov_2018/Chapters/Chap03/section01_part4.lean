import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1_2_5 (from Chap03) -/
universe u v w x

open Set

/- Theorem 3.1.2.5 lies in the convex-composition domain.

Sampled owner-style declarations in this domain:
- mathlib `ConvexOn`
- mathlib `ConvexOn.comp`
- mathlib `ConvexOn.subset`
- mathlib `Set.MapsTo`

Best owner abstraction:
- source-facing: convexity of `φ ∘ ψ` on `domψ` when `φ` is convex and monotone on a convex set
  containing the range of `ψ`
- core/canonical: `ConvexOn.comp`
- bridge/view: the range-containment hypothesis `MapsTo ψ domψ I`

Primitive data:
- the domain `domψ`
- the inner map `ψ`
- the outer map `φ`
- the ambient convex set `I`
- convexity of `ψ` on `domψ`
- convexity of `φ` on `I`
- monotonicity of `φ` on `I`
- range containment `MapsTo ψ domψ I`

Derived API:
- convexity of `φ ∘ ψ` on `domψ`

Source/core/bridge triage:
- source-facing: the range-containment composition theorem
- core/canonical: `ConvexOn.comp`
- bridge/view: passing from the source interval hypothesis to the canonical owner-style proof
  pattern through `MapsTo ψ domψ I`

The previous revision fixed the theorem to `ℝ`, but the proof only uses the generic ordered-module
interface already present in mathlib’s convex-function owners. This file therefore keeps the
source-facing range-containment bridge theorem, while lifting it to the same ambient owner level as
`ConvexOn.comp` and `Theorem_3_1_9`. The textbook real-interval statement is recovered by
specialization.
-/

namespace ConvexOn

section

variable {𝕜 : Type u} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {Y : Type w} [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
variable {Z : Type x} [AddCommMonoid Z] [PartialOrder Z] [SMul 𝕜 Z]
variable {domψ : Set X} {I : Set Y} {ψ : X → Y} {φ : Y → Z}

/-- Theorem 3.1.2.5, at the generic owner level: if `ψ` is convex on `domψ`, `φ` is convex and
nondecreasing on a convex set `I` containing `ψ(domψ)`, then `φ ∘ ψ` is convex on `domψ`. The
textbook real-interval statement is the specialization `𝕜 = ℝ`, `Y = Z = ℝ`. -/
theorem comp_of_monotoneOn
    (hφ : ConvexOn 𝕜 I φ) (hψ : ConvexOn 𝕜 domψ ψ)
    (hφ_mono : MonotoneOn φ I) (hψ_maps : MapsTo ψ domψ I) :
    ConvexOn 𝕜 domψ (φ ∘ ψ) := by
  refine ⟨hψ.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First place the convex combination back in the domain of `ψ`.
  have hcombo_dom : a • x + b • y ∈ domψ := hψ.1 hx hy ha hb hab
  -- Next record that every value of `ψ` we use lies in the convex domain of `φ`.
  have hxI : ψ x ∈ I := hψ_maps hx
  have hyI : ψ y ∈ I := hψ_maps hy
  have hcomboψI : ψ (a • x + b • y) ∈ I := hψ_maps hcombo_dom
  -- Apply convexity of `ψ` to obtain the inner Jensen inequality.
  have hψ_le : ψ (a • x + b • y) ≤ a • ψ x + b • ψ y := hψ.2 hx hy ha hb hab
  -- The convexity set of `φ` also contains the convex combination of `ψ x` and `ψ y`.
  have hcomboI : a • ψ x + b • ψ y ∈ I := hφ.1 hxI hyI ha hb hab
  -- Monotonicity of `φ` transfers the inner inequality to the outer function.
  exact (hφ_mono hcomboψI hcomboI hψ_le).trans <|
    -- Convexity of `φ` yields the final Jensen inequality for the composition.
    hφ.2 hxI hyI ha hb hab

end

end ConvexOn

/-! ### Theorem_3_1_2_6 (from Chap03) -/
noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

namespace ClosedConvexOn

/-- Helper for Theorem 3.1.2.6: a closed convex `WithTop ℝ`-valued function has closed
constrained real sublevel sets. -/
theorem isClosed_constrainedSublevelSet
    {Q : Set E} {f : E → WithTop ℝ} (hf : ClosedConvexOn Q f) (β : ℝ) :
    IsClosed (constrainedSublevelSet Q f β) := by
  -- The constrained sublevel set is the preimage of the constrained epigraph along the graph map
  -- `x ↦ (x, β)`.
  have hcont : Continuous fun x : E ↦ (x, β) :=
    by fun_prop
  simpa [constrainedSublevelSet, constrainedEpigraph] using
    hf.isClosed_constrainedEpigraph.preimage hcont

/-- Helper for Theorem 3.1.2.6: a closed convex `WithTop ℝ`-valued function has convex
constrained real sublevel sets. -/
theorem convex_constrainedSublevelSet
    {Q : Set E} {f : E → WithTop ℝ} (hf : ClosedConvexOn Q f) (β : ℝ) :
    Convex ℝ (constrainedSublevelSet Q f β) := by
  -- Convexity is inherited from the convexity of the feasible set and the convexity inequality
  -- for the finite real part.
  intro x hx y hy a b ha hb hab
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
  rcases mem_constrainedSublevelSet_iff.mp hy with ⟨hyQ, hyβ⟩
  have hzQ : a • x + b • y ∈ Q :=
    hf.convex hxQ hyQ ha hb hab
  have hxdom : x ∈ dom f :=
    hf.subset_withTopEffectiveDomain hxQ
  have hydom : y ∈ dom f :=
    hf.subset_withTopEffectiveDomain hyQ
  have hzdom : a • x + b • y ∈ dom f :=
    hf.subset_withTopEffectiveDomain hzQ
  have hconv :
      withTopRealPart f (a • x + b • y) ≤
        a * withTopRealPart f x + b * withTopRealPart f y :=
    hf.convexOn_withTopRealPart.2 hxQ hyQ ha hb hab
  have hxβ' : withTopRealPart f x ≤ β :=
    (withTopRealPart_le_iff hxdom).2 hxβ
  have hyβ' : withTopRealPart f y ≤ β :=
    (withTopRealPart_le_iff hydom).2 hyβ
  have hcomb :
      a * withTopRealPart f x + b * withTopRealPart f y ≤ a * β + b * β := by
    gcongr
  have hzβ' : withTopRealPart f (a • x + b • y) ≤ β := by
    calc
      withTopRealPart f (a • x + b • y)
          ≤ a * withTopRealPart f x + b * withTopRealPart f y := hconv
      _ ≤ a * β + b * β := hcomb
      _ = β := by
        calc
          a * β + b * β = (a + b) * β := by ring
          _ = β := by rw [hab, one_mul]
  exact mem_constrainedSublevelSet_iff.2
    ⟨hzQ, (withTopRealPart_le_iff hzdom).1 hzβ'⟩

/-- Helper for Theorem 3.1.2.6: the real-valued representative of a closed convex real lift is
lower semicontinuous on any closed feasible set. -/
theorem lowerSemicontinuousOn_real
    {Q : Set E} {f : E → ℝ} (hQ : IsClosed Q)
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ))) :
    LowerSemicontinuousOn f Q := by
  -- Rewrite the real epigraph as the chapter's constrained epigraph for the lifted function.
  rw [lowerSemicontinuousOn_iff_isClosed_epigraph hQ]
  have hEq :
      {p : E × ℝ | p.1 ∈ Q ∧ f p.1 ≤ p.2} =
        constrainedEpigraph Q (fun x ↦ (f x : WithTop ℝ)) := by
    ext p
    constructor
    · rintro ⟨hpQ, hp₂⟩
      exact mem_constrainedEpigraph_iff.2 ⟨hpQ, by exact_mod_cast hp₂⟩
    · rintro ⟨hpQ, hp₂⟩
      have hp₂' : ((f p.1 : ℝ) : WithTop ℝ) ≤ (p.2 : WithTop ℝ) := hp₂
      exact ⟨hpQ, by exact_mod_cast hp₂'⟩
  simpa [hEq] using hf.isClosed_constrainedEpigraph

/-- Helper for Theorem 3.1.2.6: the lifted closed-convex hypothesis recovers the ordinary
real-valued convexity of the underlying function. -/
theorem convexOn_real
    {Q : Set E} {f : E → ℝ}
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ))) :
    ConvexOn ℝ Q f := by
  -- For real lifts, the finite real part is just the original function.
  simpa [withTopRealPart] using hf.convexOn_withTopRealPart

end ClosedConvexOn

/-- Helper for Theorem 3.1.2.6: a continuous linear functional on `ℝ × ℝ` is determined by its
values on the two coordinate vectors. -/
theorem strongDual_apply_prod
    (f : StrongDual ℝ (ℝ × ℝ)) (u v : ℝ) :
    f (u, v) = u * f ((1 : ℝ), (0 : ℝ)) + v * f ((0 : ℝ), (1 : ℝ)) := by
  -- Expand `(u, v)` in the standard basis and use linearity.
  have hpair :
      (u, v) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc
    f (u, v) = f (u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ))) := by rw [hpair]
    _ = f (u • ((1 : ℝ), (0 : ℝ))) + f (v • ((0 : ℝ), (1 : ℝ))) := by rw [map_add]
    _ = u • f ((1 : ℝ), (0 : ℝ)) + v • f ((0 : ℝ), (1 : ℝ)) := by
      rw [map_smul, map_smul]
    _ = u * f ((1 : ℝ), (0 : ℝ)) + v * f ((0 : ℝ), (1 : ℝ)) := by
      simp [smul_eq_mul]

/- Theorem 3.1.2.6 lies in the chapter's two-function minimax-linearization domain on a proper
real normed space, with the textbook finite-dimensional `ℝⁿ` statement recovered by the canonical
bridge `FiniteDimensional.proper_real`.

Sampled owner-style declarations:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a
  feasible set
- `constrainedSublevelSet` from `Definition_3_3`, the owner real-sublevel-set construction on a
  feasible set
- `IsMinimaxLinearizationParameter` from `Definition_3_1_2_3`, the source-facing owner predicate
  for the minimax equality on two functions
- `StrongConvexOn.existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn` in `Theorem_3_45`, the
  nearby Chapter 3 proper-space owner theorem showing that bounded sublevel sets feed attainment
  through `ProperSpace` rather than through a frozen finite-dimensional hypothesis

Best owner abstraction:
- source-facing/core owner:
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`

Primitive data:
- a feasible set `Q : Set E`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of their canonical `WithTop` lifts on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- a parameter `lam : unitInterval`
- the owner conclusion
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: this two-function bounded-sublevel-set minimax existence theorem
- core/canonical: `ClosedConvexOn`, `constrainedSublevelSet`, and
  `IsMinimaxLinearizationParameter`
- bridge/view: the coercion of real-valued objectives to `WithTop ℝ`, used only in the
  closed-convex and sublevel-set hypotheses

This file is therefore the owner theorem for the two-function case. The refinement keeps the
source semantics unchanged, reuses the existing chapter owners directly, and removes the
nonessential finite-dimensional proof-route specialization from the public surface. -/

/-- Theorem 3.1.2.6: if `f₁` and `f₂` are real-valued functions whose `WithTop` lifts are closed
and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise maximum
`x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists some `λ* ∈ [0, 1]` for which the
minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals the minimum value of the convex
combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; in Lean this minimum equality is recorded by the owner
predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. The textbook finite-dimensional
`ℝⁿ` statement is recovered by equipping `E = EuclideanSpace ℝ (Fin n)` with the canonical
`ProperSpace` instance. -/
-- Proof sketch: consider the auxiliary value function
-- `φ(λ) = inf_{x ∈ Q} (λ f₁(x) + (1 - λ) f₂(x))`. Closed convexity and bounded constrained
-- sublevel sets of the maximum objective are the source-facing hypotheses, while the proper-space
-- compactness bridge turns the closed bounded feasible sublevel slices needed in the chapter's
-- minimizer-existence argument into compact ones. The pointwise maximum of the two functions is
-- again closed and convex, and the textbook monotonicity argument for the minimizing selections
-- then shows that a maximizer `λ* ∈ [0, 1]` of `φ` gives the desired minimax equality.
theorem exists_minimax_parameter_of_bounded_constrainedSublevelSets
    {Q : Set E} {f₁ f₂ : E → ℝ}
    (hf₁ : ClosedConvexOn Q (fun x ↦ (f₁ x : WithTop ℝ)))
    (hf₂ : ClosedConvexOn Q (fun x ↦ (f₂ x : WithTop ℝ)))
    (hbounded :
    ∀ β : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q
            (fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : WithTop ℝ)) β)) :
    ∃ lam : unitInterval,
      IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam :=
  by
  rcases Q.eq_empty_or_nonempty with rfl | hQ_nonempty
  · -- On the empty feasible set, both infima are over an empty range and therefore agree.
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    let lam : unitInterval := ⟨0, hzero_mem⟩
    have hrange_max :
        Set.range (fun x : (∅ : Set E) ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    have hrange_line :
        Set.range
            (fun x : (∅ : Set E) ↦
              ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    refine ⟨lam, ?_⟩
    rw [isMinimaxLinearizationParameter_iff, hrange_max, hrange_line]
  · -- Route correction: the source's global `λ`-slice minimizer route is not valid under the
    -- actual hypotheses, so the proof works through a compact primal minimizer and a supporting
    -- functional on the convex upper image in `ℝ²`.
    let β₀ : ℝ := max (f₁ hQ_nonempty.some) (f₂ hQ_nonempty.some)
    let S : Set E :=
      constrainedSublevelSet Q
        (fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : WithTop ℝ)) β₀
    have hsome_memS : hQ_nonempty.some ∈ S := by
      -- The chosen reference point lies in the corresponding max-sublevel slice by definition.
      refine mem_constrainedSublevelSet_iff.2 ?_
      exact ⟨hQ_nonempty.some_mem, le_rfl⟩
    have hS_closed : IsClosed S := by
      -- The max-sublevel slice is the intersection of the two individual closed sublevel sets.
      have hEq :
          S =
            constrainedSublevelSet Q (fun x ↦ (f₁ x : WithTop ℝ)) β₀ ∩
              constrainedSublevelSet Q (fun x ↦ (f₂ x : WithTop ℝ)) β₀ := by
        ext x
        constructor
        · intro hx
          rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
          have hxβ' : max (f₁ x) (f₂ x) ≤ β₀ := by
            exact_mod_cast hxβ
          exact ⟨mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_left (f₁ x) (f₂ x)) hxβ'⟩,
            mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_right (f₁ x) (f₂ x)) hxβ'⟩⟩
        · intro hx
          rcases hx with ⟨hx₁, hx₂⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₁ with ⟨hxQ, hx₁β⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₂ with ⟨_, hx₂β⟩
          refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
          exact_mod_cast (max_le hx₁β hx₂β)
      rw [hEq]
      exact
        (hf₁.isClosed_constrainedSublevelSet β₀).inter
          (hf₂.isClosed_constrainedSublevelSet β₀)
    have hS_convex : Convex ℝ S := by
      -- The same max-sublevel identity reduces convexity to the two scalar sublevel slices.
      have hEq :
          S =
            constrainedSublevelSet Q (fun x ↦ (f₁ x : WithTop ℝ)) β₀ ∩
              constrainedSublevelSet Q (fun x ↦ (f₂ x : WithTop ℝ)) β₀ := by
        ext x
        constructor
        · intro hx
          rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
          have hxβ' : max (f₁ x) (f₂ x) ≤ β₀ := by
            exact_mod_cast hxβ
          exact ⟨mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_left (f₁ x) (f₂ x)) hxβ'⟩,
            mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_right (f₁ x) (f₂ x)) hxβ'⟩⟩
        · intro hx
          rcases hx with ⟨hx₁, hx₂⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₁ with ⟨hxQ, hx₁β⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₂ with ⟨_, hx₂β⟩
          refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
          exact_mod_cast (max_le hx₁β hx₂β)
      rw [hEq]
      exact
        (hf₁.convex_constrainedSublevelSet β₀).inter
          (hf₂.convex_constrainedSublevelSet β₀)
    have hS_bounded : Bornology.IsBounded S := by
      simpa [S, β₀] using hbounded β₀
    have hS_compact : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
    have hS_nonempty : S.Nonempty :=
      ⟨hQ_nonempty.some, hsome_memS⟩
    have hS_subset : S ⊆ Q := by
      intro x hx
      exact (mem_constrainedSublevelSet_iff.mp hx).1
    have hf₁S : ClosedConvexOn S (fun x ↦ (f₁ x : WithTop ℝ)) :=
      hf₁.restrict hS_closed hS_convex hS_subset
    have hf₂S : ClosedConvexOn S (fun x ↦ (f₂ x : WithTop ℝ)) :=
      hf₂.restrict hS_closed hS_convex hS_subset
    have hlsc₁S : LowerSemicontinuousOn f₁ S :=
      hf₁S.lowerSemicontinuousOn_real hS_closed
    have hlsc₂S : LowerSemicontinuousOn f₂ S :=
      hf₂S.lowerSemicontinuousOn_real hS_closed
    have hlscMaxS : LowerSemicontinuousOn (fun x ↦ max (f₁ x) (f₂ x)) S :=
      hlsc₁S.sup hlsc₂S
    obtain ⟨xStar, hxStarS, hxStarMinS⟩ :=
      hlscMaxS.exists_isMinOn hS_nonempty hS_compact
    have hxStarQ : xStar ∈ Q :=
      hS_subset hxStarS
    have hxStar_beta : max (f₁ xStar) (f₂ xStar) ≤ β₀ :=
      by
        exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxStarS).2
    have hxStarMinQ : IsMinOn (fun x ↦ max (f₁ x) (f₂ x)) Q xStar := by
      -- Any feasible point either lies in the compact slice `S`, where `xStar` is minimizing, or
      -- has larger max-value than `β₀`, which still dominates the value at `xStar`.
      intro y hyQ
      by_cases hyS : y ∈ S
      · exact hxStarMinS hyS
      · have hy_not_le : ¬ max (f₁ y) (f₂ y) ≤ β₀ := by
          intro hyβ
          exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
        have hyβ_lt : β₀ < max (f₁ y) (f₂ y) :=
          lt_of_not_ge hy_not_le
        exact (le_trans hxStar_beta hyβ_lt.le)
    let fStar : ℝ := max (f₁ xStar) (f₂ xStar)
    let U : Set (ℝ × ℝ) :=
      {p | ∃ x ∈ Q, f₁ x ≤ p.1 ∧ f₂ x ≤ p.2}
    have hconv₁ : ConvexOn ℝ Q f₁ :=
      hf₁.convexOn_real
    have hconv₂ : ConvexOn ℝ Q f₂ :=
      hf₂.convexOn_real
    have hU_convex : Convex ℝ U := by
      -- The upper image is stable under convex combinations because `Q` is convex and both
      -- coordinates obey the convexity inequality.
      intro p hp q hq a b ha hb hab
      rcases hp with ⟨x, hxQ, hx₁, hx₂⟩
      rcases hq with ⟨y, hyQ, hy₁, hy₂⟩
      refine ⟨a • x + b • y, hf₁.convex hxQ hyQ ha hb hab, ?_, ?_⟩
      · calc
          f₁ (a • x + b • y) ≤ a * f₁ x + b * f₁ y := hconv₁.2 hxQ hyQ ha hb hab
          _ ≤ a * p.1 + b * q.1 := by gcongr
      · calc
          f₂ (a • x + b • y) ≤ a * f₂ x + b * f₂ y := hconv₂.2 hxQ hyQ ha hb hab
          _ ≤ a * p.2 + b * q.2 := by gcongr
    have hdStar_memU : (fStar, fStar) ∈ U := by
      -- The primal minimizer provides the diagonal upper-image point.
      refine ⟨xStar, hxStarQ, le_max_left _ _, le_max_right _ _⟩
    have hU_int_nonempty : (interior U).Nonempty := by
      -- Any feasible point contributes an open upper-right quadrant contained in `U`.
      let p0 : ℝ × ℝ := (f₁ hQ_nonempty.some + 1, f₂ hQ_nonempty.some + 1)
      let V : Set (ℝ × ℝ) := Set.Ioi (f₁ hQ_nonempty.some) ×ˢ Set.Ioi (f₂ hQ_nonempty.some)
      have hp0_memV : p0 ∈ V := by
        simp [p0, V]
      have hV_open : IsOpen V :=
        isOpen_Ioi.prod isOpen_Ioi
      have hV_subset : V ⊆ U := by
        intro p hp
        rcases hp with ⟨hp₁, hp₂⟩
        exact ⟨hQ_nonempty.some, hQ_nonempty.some_mem, hp₁.le, hp₂.le⟩
      refine ⟨p0, mem_interior_iff_mem_nhds.2 ?_⟩
      exact Filter.mem_of_superset (hV_open.mem_nhds hp0_memV) hV_subset
    have hdStar_not_mem_interior : (fStar, fStar) ∉ interior U := by
      -- A neighborhood of `(fStar, fStar)` inside `U` would contain a strictly smaller diagonal
      -- point, contradicting the minimality of `xStar`.
      intro hdStar_int
      rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hdStar_int) with
        ⟨ε, hε, hεball⟩
      let pDown : ℝ × ℝ := (fStar - ε / 2, fStar - ε / 2)
      have hpDown_dist : dist pDown (fStar, fStar) < ε := by
        rw [dist_eq_norm, Prod.norm_def]
        simpa [pDown, abs_of_pos hε] using half_lt_self hε
      have hpDown_memU : pDown ∈ U :=
        interior_subset (hεball hpDown_dist)
      rcases hpDown_memU with ⟨x, hxQ, hx₁, hx₂⟩
      have hxlt : max (f₁ x) (f₂ x) < fStar := by
        apply lt_of_le_of_lt (max_le_iff.mpr ⟨hx₁, hx₂⟩)
        simp [pDown, hε]
      rw [isMinOn_iff] at hxStarMinQ
      exact (not_lt_of_ge (hxStarMinQ x hxQ)) hxlt
    obtain ⟨f, hf_ne, hf_support⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hU_convex hdStar_not_mem_interior
        hU_int_nonempty
    let g : StrongDual ℝ (ℝ × ℝ) := -f
    have hg_support : ∀ p ∈ U, g (fStar, fStar) ≤ g p := by
      -- Negating the separating functional turns the upper bound on `U` into the lower bound we
      -- need for convex combinations.
      intro p hp
      simpa [g] using neg_le_neg (hf_support p hp)
    let α : ℝ := g (1, 0)
    let β : ℝ := g (0, 1)
    have hα_nonneg : 0 ≤ α := by
      have hstep : (fStar + 1, fStar) ∈ U := by
        exact ⟨xStar, hxStarQ, by linarith [le_max_left (f₁ xStar) (f₂ xStar)], le_max_right _ _⟩
      have hineq := hg_support (fStar + 1, fStar) hstep
      rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g (fStar + 1) fStar] at hineq
      have hineq' : fStar * α + fStar * β ≤ (fStar + 1) * α + fStar * β := by
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc] using hineq
      linarith
    have hβ_nonneg : 0 ≤ β := by
      have hstep : (fStar, fStar + 1) ∈ U := by
        exact ⟨xStar, hxStarQ, le_max_left _ _, by linarith [le_max_right (f₁ xStar) (f₂ xStar)]⟩
      have hineq := hg_support (fStar, fStar + 1) hstep
      rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g fStar (fStar + 1)] at hineq
      have hineq' : fStar * α + fStar * β ≤ fStar * α + (fStar + 1) * β := by
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc] using hineq
      linarith
    have hαβ_pos : 0 < α + β := by
      have hαβ_nonneg : 0 ≤ α + β := add_nonneg hα_nonneg hβ_nonneg
      have hαβ_ne : α + β ≠ 0 := by
        intro hsum
        have hα_zero : α = 0 := by linarith
        have hβ_zero : β = 0 := by linarith
        have hg_zero : g = 0 := by
          apply ContinuousLinearMap.ext
          intro z
          rcases z with ⟨u, v⟩
          rw [strongDual_apply_prod]
          simp [α, β, hα_zero, hβ_zero]
        exact hf_ne (by simpa [g] using hg_zero)
      exact lt_of_le_of_ne hαβ_nonneg hαβ_ne.symm
    let lamReal : ℝ := α / (α + β)
    have hlam_nonneg : 0 ≤ lamReal := by
      dsimp [lamReal]
      exact div_nonneg hα_nonneg hαβ_pos.le
    have hlam_le_one : lamReal ≤ 1 := by
      dsimp [lamReal]
      exact (div_le_iff₀ hαβ_pos).2 (by linarith)
    have hlam_mem : lamReal ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hlam_nonneg, hlam_le_one⟩
    let lam : unitInterval := ⟨lamReal, hlam_mem⟩
    have hline_lower :
        ∀ x ∈ Q, fStar ≤ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := by
      -- The supporting inequality on `U` yields a global lower bound for the normalized convex
      -- combination.
      intro x hxQ
      have hxU : (f₁ x, f₂ x) ∈ U := by
        exact ⟨x, hxQ, le_rfl, le_rfl⟩
      have hineq := hg_support (f₁ x, f₂ x) hxU
      have hineq' : fStar * α + fStar * β ≤ f₁ x * α + f₂ x * β := by
        rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g (f₁ x) (f₂ x)] at hineq
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
          hineq
      have hineq'' : (α + β) * fStar ≤ β * f₂ x + α * f₁ x := by
        nlinarith [hineq']
      have hmul :
          (α + β) * fStar ≤ (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := by
        have hline_mul :
            (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) =
              β * f₂ x + α * f₁ x := by
          dsimp [lam, lamReal]
          rw [AffineMap.lineMap_apply_ring]
          have hβ_div :
              1 - α / (α + β) = β / (α + β) := by
            field_simp [show α + β ≠ 0 by linarith [hαβ_pos]]
            ring
          rw [hβ_div]
          field_simp [show α + β ≠ 0 by linarith [hαβ_pos]]
        calc
          (α + β) * fStar ≤ β * f₂ x + α * f₁ x := hineq''
          _ = (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := hline_mul.symm
      nlinarith [hαβ_pos, hmul]
    have hline_xStar_le : AffineMap.lineMap (f₂ xStar) (f₁ xStar) (lam : ℝ) ≤ fStar := by
      -- At the primal minimizer, the convex combination cannot exceed the pointwise maximum.
      rw [AffineMap.lineMap_apply_ring]
      have h₁ :
          (1 - (lam : ℝ)) * f₂ xStar ≤ (1 - (lam : ℝ)) * fStar := by
        exact mul_le_mul_of_nonneg_left (le_max_right (f₁ xStar) (f₂ xStar))
          (sub_nonneg.mpr lam.2.2)
      have h₂ : (lam : ℝ) * f₁ xStar ≤ (lam : ℝ) * fStar := by
        exact mul_le_mul_of_nonneg_left (le_max_left (f₁ xStar) (f₂ xStar)) lam.2.1
      nlinarith [h₁, h₂]
    have hline_xStar_eq : AffineMap.lineMap (f₂ xStar) (f₁ xStar) (lam : ℝ) = fStar := by
      exact le_antisymm hline_xStar_le (hline_lower xStar hxStarQ)
    let xStarQ : Q := ⟨xStar, hxStarQ⟩
    have hmax_min_subtype :
        IsMinOn (fun x : Q ↦ max (f₁ x) (f₂ x)) Set.univ xStarQ := by
      -- Restrict the primal minimizer from `Q` to the subtype `Q`.
      rw [isMinOn_univ_iff]
      rw [isMinOn_iff] at hxStarMinQ
      intro x
      exact hxStarMinQ x x.property
    have hline_min_subtype :
        IsMinOn (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ)) Set.univ xStarQ := by
      -- The supporting inequality gives the lower bound everywhere, and the minimizer attains it.
      rw [isMinOn_univ_iff]
      intro x
      simpa [xStarQ, hline_xStar_eq] using hline_lower x x.property
    have hsInf_max :
        sInf (Set.range fun x : Q ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) = (fStar : EReal) := by
      -- The subtype minimizer rewrites the infimum of the max objective to the attained value.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ max (f₁ x) (f₂ x))).optimalValue = (fStar : EReal) := by
        simpa [fStar] using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
          (problem := SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ max (f₁ x) (f₂ x)))
          (x := xStarQ) (by simp) hmax_min_subtype)
      simpa [SetConstrainedMinimizationProblem.optimalValue] using hopt
    have hsInf_line :
        sInf (Set.range fun x : Q ↦
          ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) = (fStar : EReal) := by
      -- The same argument applies to the supported convex combination.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ))).optimalValue =
              (((AffineMap.lineMap (f₂ xStarQ) (f₁ xStarQ) (lam : ℝ) : ℝ) : EReal)) := by
        simpa using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
          (problem := SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ)))
          (x := xStarQ) (by simp) hline_min_subtype)
      calc
        sInf (Set.range fun x : Q ↦
          ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal))
            = (SetConstrainedMinimizationProblem.unconstrained
                (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ))).optimalValue := by
                  simp [SetConstrainedMinimizationProblem.optimalValue]
        _ = (((AffineMap.lineMap (f₂ xStarQ) (f₁ xStarQ) (lam : ℝ) : ℝ) : EReal)) := hopt
        _ = (fStar : EReal) := by exact_mod_cast hline_xStar_eq
    refine ⟨lam, ?_⟩
    -- Both infima equal the common attained value `fStar`.
    rw [isMinimaxLinearizationParameter_iff]
    exact hsInf_max.trans hsInf_line.symm

end

/-! ### Corollary_3_1_3 (from Chap03) -/
/-
Corollary 3.1.3 is a recall-only item in the chapter's convex-analysis/minimax-linearization
domain.

Primary domain:
- finite pointwise maxima of closed convex functions and bounded constrained sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `maxTypeObjective`
- `constrainedSublevelSet`
- `exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`

Best owner abstraction:
- source-facing: the bounded-level-set minimax-linearization corollary
- core/canonical: `maxTypeObjective fs`, the bounded feasible sublevel owner
  `constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and the
  simplex coefficient owner `StdSimplex ℝ ι`
- bridge/view: the weighted-sum expression `∑ i, coeffs.weights i * fs i x`, derived from the
  canonical simplex data

Primitive data:
- a nonempty finite family `fs : ι → E → ℝ`
- closed convexity of each component on `Q`
- boundedness of the constrained sublevel sets of `maxTypeObjective fs`

Derived API:
- the simplex coefficient vector `coeffs : StdSimplex ℝ ι`
- the equality of constrained `EReal` infima between the finite maximum and the weighted sum

The upstream max-sublevel-set theorem already has the exact interface needed here. This file
therefore imports that owner theorem directly and recalls its canonical name rather than routing
through a later recall surface or keeping a duplicate local wrapper. The textbook `Fin m`
specialization is recovered by instantiating the recalled theorem at `ι = Fin m`; it does not
need a separate local declaration here.
-/

recall exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets

/-! ### Definition_3_1_3 (from Chap03) -/
/- Definition 3.1.3 belongs to the chapter's canonical one-sided directional-derivative API in
`LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_3_1`.

Primary domain:
- one-sided directional derivatives of extended-real-valued functions on real modules.

Relevant owner-style declarations sampled before refinement:
- `extendedRealEffectiveDomain`
- `HasDerivWithinAt`
- `HasDirectionalDerivAt`
- `DirectionallyDifferentiableAt`

Owner abstraction:
- `HasDirectionalDerivAt`

Primitive data:
- `extendedRealEffectiveDomain f`, the finite-value condition at the base point and along the ray.
- the scalar slice `fun α ↦ extendedRealRealPart f (x + α • p)`, organized canonically by the
  one-sided derivative owner `HasDerivWithinAt ... (Set.Ici 0) 0`.

Derived API:
- `HasDirectionalDerivAt` is the owner predicate for the one-sided directional derivative in every
  direction, including `p = 0` via the constant ray.
- `DirectionallyDifferentiableAt` is the existential wrapper around `HasDirectionalDerivAt`.
- `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt` is the companion specification
  theorem.

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: `HasDerivWithinAt` on the scalar slice
  `fun α ↦ extendedRealRealPart f (x + α • p)`
- bridge/view: the secant-slope presentation of that scalar slice

The support vocabulary is already owned upstream, so this file recalls only the source-facing
owner surface and its thin specification theorem. As in the owner file, the source prose is
Euclidean, but the declaration surface itself needs only the real-module structure used to form
the ray `x + α • p`. -/
recall HasDirectionalDerivAt

recall DirectionallyDifferentiableAt

recall directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt

/-! ### Definition_3_1_3_1 (from Chap03) -/
universe u

noncomputable section

open Filter Set
open scoped ConvexAnalysis Topology

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-
Definition 3.1.3.1 is source-facing in the chapter's one-sided directional-derivative API.

Relevant owner-style declarations sampled before refinement:
- mathlib `HasDerivWithinAt`
- mathlib `HasLineDerivWithinAt`
- mathlib `LineDifferentiableWithinAt`
- chapter `hasDerivWithinAt_directionalSlice_of_differentiableAt` in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_11`
- chapter notation `dom f` for the effective domain owner in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_2`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0`

Primitive data:
- the finite base-point condition `x ∈ dom f`
- eventual finiteness of the ray `α ↦ x + α • p` for `α ↓ 0`
- the owner derivative of the finite real slice on `Ici 0`

Derived API:
- `DirectionallyDifferentiableAt`
- the accessor lemmas on `HasDirectionalDerivAt`
- uniqueness of the finite directional derivative
- the zero-direction specialization

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: `HasDerivWithinAt` on the directional slice
- bridge/view: the existential wrapper
  `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

The more general line-derivative owner `HasLineDerivWithinAt` is not used as the main entry here:
the textbook notion is explicitly one-sided (`α ↓ 0`), so `HasDerivWithinAt ... (Ici 0) 0` is the
faithful core, while the extra finiteness hypotheses stay as source-facing domain guards.

As in earlier chapter owner files, the source prose is written on `ℝⁿ`, but these declarations use
only the additive and scalar-action structure needed to form the ray `x + α • p`. The ambient
owner therefore lives over an arbitrary real module instead of the concrete Euclidean model.
-/
/-- Definition 3.1.3.1: an extended-real-valued function has directional derivative `d` at
`x` in direction `p` when `x` has finite value, the nearby values along the ray `x + α • p`
are finite for `α ↓ 0`, and the directional slice
`α ↦ extendedRealRealPart f (x + α • p)` has right derivative `d` at `0`. This includes the zero
direction, whose ray is constant and whose derivative is therefore `0`. -/
def HasDirectionalDerivAt (f : E → EReal) (x p : E) (d : ℝ) : Prop :=
  x ∈ dom f ∧
    (∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
    HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0

variable {f : E → EReal} {x p : E} {d : ℝ}

/-- A directional derivative can only be taken at a point of `dom f`. -/
theorem HasDirectionalDerivAt.mem_dom
    (h : HasDirectionalDerivAt f x p d) :
    x ∈ dom f := by
  exact h.1

/-- A directional derivative forces the ray to stay in the finite-value domain for sufficiently
small positive steps. -/
theorem HasDirectionalDerivAt.eventually_mem_dom
    (h : HasDirectionalDerivAt f x p d) :
    ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
  exact h.2.1

/-- The source-facing directional derivative owns the one-variable right derivative of the
directional slice. -/
theorem HasDirectionalDerivAt.hasDerivWithinAt
    (h : HasDirectionalDerivAt f x p d) :
    HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0 := by
  exact h.2.2

/-- A function is directionally differentiable at `x` along `p` if it has some finite one-sided
directional derivative there. -/
def DirectionallyDifferentiableAt (f : E → EReal) (x p : E) : Prop :=
  ∃ d : ℝ, HasDirectionalDerivAt f x p d

/-- Directional differentiability means existence of a finite directional derivative. -/
theorem directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt
    {f : E → EReal} {x p : E} :
    DirectionallyDifferentiableAt f x p ↔ ∃ d : ℝ, HasDirectionalDerivAt f x p d :=
  Iff.rfl

/-- The finite directional derivative at a fixed point and direction is unique when it exists. -/
theorem HasDirectionalDerivAt.unique
    {d₁ d₂ : ℝ}
    (h₁ : HasDirectionalDerivAt f x p d₁) (h₂ : HasDirectionalDerivAt f x p d₂) :
    d₁ = d₂ := by
  simpa using
    (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
      h₁.hasDerivWithinAt
      h₂.hasDerivWithinAt

/-- The zero direction is the constant ray, so every finite base point has directional derivative
`0` along `0`. -/
theorem HasDirectionalDerivAt.zero
    {x : E} (hx : x ∈ dom f) :
    HasDirectionalDerivAt f x 0 0 := by
  refine ⟨hx, ?_, ?_⟩
  · exact .of_forall fun α ↦ by simpa using hx
  · simpa using
      (hasDerivWithinAt_const (0 : ℝ) (Ici (0 : ℝ)) (extendedRealRealPart f x))

end

/-! ### Lemma_3_1_3 (from Chap03) -/
/- Lemma 3.1.3 lies in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space and their behavior under convex hulls
  of two-set unions.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`
- the recall-only downstream use in `Lemma_3_1_2_1`

Best owner abstraction:
- the exact upstream theorem `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`, stated at
  the same ambient owner level as `supportFunction`

Primitive data:
- two sets `Q₁ Q₂ : Set E`
- a direction `x : E`

Derived API:
- the support function of `convexHull ℝ (Q₁ ∪ Q₂)`
- its identification with the pointwise maximum of the two support functions

Source/core/bridge triage:
- source-facing: this two-set convex-hull support-function identity
- core/canonical: the exact upstream theorem `supportFunction_convexHull_union_eq_max`
- bridge/view: none needed; the target interface already exists upstream

This file previously repeated the exact theorem already owned by `Lemma_3_3`. Since the chapter
already has the precise owner interface, this numbered item is refined to direct canonical
recall/use instead of keeping a parallel local theorem shell. The textbook `ℝⁿ` statement is a
specialization of that generalized owner theorem.
-/
recall supportFunction_convexHull_union_eq_max

/-! ### Lemma_3_1_3_1 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis Topology WithTopConvexAnalysis

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/- Lemma 3.1.3.1 is source-facing in the chapter's convex directional-derivative domain.

Primary domain:
- finite directional derivatives of convex `ℝ ∪ {+∞}`-valued functions at interior points.

Sampled owner-style declarations:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative at a finite base point;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the owner
  convexity theorem for the theorem-level finite directional-derivative view on all directions;
- `withTopEffectiveDomain`, `withTopRealPart`, and
  `ConvexOn ℝ (dom f) (withTopRealPart f)` in `Definition_3_3`;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity.

Best owner abstraction:
- the theorem-level finite `toReal` view of the chapter owner
  `convexDirectionalDerivative f x (interior_subset hx)`, identified upstream with
  `HasDirectionalDerivAt`.

Primitive data:
- none in this file; the secant-slope and `EReal` infimum construction are already owned upstream
  by `Theorem_3_21`.

Derived API:
- the owner-level convexity recall on all directions;
- the positive-homogeneity theorem for the finite directional-derivative owner;
- the affine-support inequality in real form on the same topological-module owner layer.

Source/core/bridge triage:
- source-facing: the real-valued directional derivative at an interior point, together with its
  convexity, degree-one positive homogeneity, and affine support inequality;
- core/canonical: `convexDirectionalDerivative` and `HasDirectionalDerivAt`;
- bridge/view: the upstream direct `toReal` expansion against
  `convexDirectionalDerivative f x (interior_subset hx)`.

This file therefore stops re-owning the directional derivative as a global real-valued definition.
The `EReal` infimum-of-slopes object remains the upstream core owner, while the public surface
here uses only the explicit theorem-level finite view supplied by the chapter
directional-derivative API. The convexity, positive-homogeneity, and affine-support surface all
live in the same topological-module layer.
-/

section Core

variable {f : E → WithTop ℝ}

/- Lemma 3.1.3.1 (1): for a convex `ℝ ∪ {+∞}`-valued function and an interior point `x` of its
effective domain, the finite directional derivative given by the explicit `toReal` view of
`convexDirectionalDerivative` is convex on all directions. -/
recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

/-- Helper for Lemma 3.1.3.1: a finite `WithTop ℝ` value stays finite after coercion to `EReal`.
-/
theorem mem_dom_withTopToEReal_comp_of_mem_dom
    {y : E} (hy : y ∈ dom f) :
    y ∈ dom (withTopToEReal ∘ f) := by
  change withTopToEReal (f y) ≠ ⊤ ∧ withTopToEReal (f y) ≠ ⊥
  constructor
  · intro htop
    exact (ne_of_lt hy) (WithBot.coe_eq_top.mp htop)
  · exact WithBot.coe_ne_bot

/-- Helper for Lemma 3.1.3.1: reading a `WithTop ℝ` value through `EReal.toReal` gives the same
finite real part as `withTopRealPart`. -/
theorem withTopToEReal_toReal_eq_withTopRealPart
    {z : E} :
    (withTopToEReal (f z)).toReal = withTopRealPart f z := by
  cases hfz : f z with
  | top =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_top
  | coe a =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_coe a

/-- Helper for Lemma 3.1.3.1: the finite directional derivative at an interior point vanishes in
the zero direction. -/
theorem convexDirectionalDerivativeReal_zero_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) :
    f′[hx] (0 : E) = 0 := by
  -- Compare the owner directional derivative with the constant-ray zero-direction derivative.
  have howner :
      HasDirectionalDerivAt (withTopToEReal ∘ f) x (0 : E) (f′[hx] (0 : E)) :=
    convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx 0
  have hzero :
      HasDirectionalDerivAt (withTopToEReal ∘ f) x (0 : E) 0 :=
    HasDirectionalDerivAt.zero (f := withTopToEReal ∘ f) (x := x)
      (mem_dom_withTopToEReal_comp_of_mem_dom (f := f) (interior_subset hx))
  exact HasDirectionalDerivAt.unique howner hzero

/-- Helper for Lemma 3.1.3.1: the finite directional derivative scales linearly under positive
real dilation of the direction variable. -/
theorem convexDirectionalDerivativeReal_smul_of_pos
    {x p : E} (_hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) {τ : ℝ} (hτ : 0 < τ) :
    f′[hx] (τ • p) = τ * f′[hx] p := by
  -- Pass the extended-valued positive-scaling law through the finite `toReal` owner surface.
  rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
  rw [convexDirectionalDerivative_smul (f := f) (hx := interior_subset hx) hτ p]
  simp [EReal.toReal_mul]

/-- Lemma 3.1.3.1 (1): for a convex `ℝ ∪ {+∞}`-valued function and an interior point `x` of its
effective domain, the finite directional derivative is positively homogeneous of degree one on all
directions. Its canonical pointwise rescaling API is the owner projection `map_smul` with bundled
nonnegative scalars `τ : NNReal`. -/
-- Proof sketch: the interior-point directional derivative is the finite theorem-surface view of
-- the canonical owner `convexDirectionalDerivative`; positive homogeneity is obtained by passing
-- the extended-valued positive-scaling law to this finite owner.
theorem convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) :
    IsPositivelyHomogeneousOn 1 Set.univ (f′[hx]) := by
  refine ⟨?_, ?_⟩
  · -- The domain is all of `E`, so nonnegative rescaling stays in the domain automatically.
    intro p _ τ
    simp
  · intro p _ τ
    by_cases hτ : τ = 0
    · -- The zero scalar branch reduces to the zero-direction value.
      rw [hτ, zero_smul]
      simpa [Real.rpow_one] using
        convexDirectionalDerivativeReal_zero_of_mem_interior (f := f) hf hx
    · -- For positive scalars, transfer the owner scaling identity to the real-valued view.
      have hτ_pos : 0 < (τ : ℝ) := by
        exact_mod_cast (show 0 < τ from pos_iff_ne_zero.mpr hτ)
      simpa [Real.rpow_one, smul_eq_mul] using
        convexDirectionalDerivativeReal_smul_of_pos (f := f) (x := x) (p := p) hf hx hτ_pos

/-- Every point `y` in the effective domain lies above the affine lower support determined by the
finite directional derivative at an interior point `x`. -/
-- Proof sketch: rewrite the supporting inequality for the directional derivative in the finite
-- real-valued owner surface `convexDirectionalDerivativeReal`, without reintroducing an
-- inner-product-only subgradient detour.
theorem convexDirectionalDerivativeReal_affine_support_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f))
    {y : E} (hy : y ∈ dom f) :
    withTopRealPart f y ≥
      withTopRealPart f x + f′[hx] (y - x) := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let g : ℝ → ℝ := withTopRealPart f ∘ line
  have hline_apply (α : ℝ) : line α = x + α • (y - x) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict the convex function to the affine line through `x` and `y`.
    simpa [S, g] using hf.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply] using hy
  have hslice :
      (fun α : ℝ ↦ (withTopToEReal (f (x + α • (y - x)))).toReal) = g := by
    -- The `EReal.toReal` slice is exactly the `withTopRealPart` slice on the same affine line.
    funext α
    change (withTopToEReal (f (x + α • (y - x)))).toReal = withTopRealPart f (line α)
    rw [hline_apply]
    simpa using
      (withTopToEReal_toReal_eq_withTopRealPart (f := f) (z := x + α • (y - x)))
  have hderiv_Ici : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ici (0 : ℝ)) 0 := by
    -- The directional-derivative owner theorem gives the right derivative of the scalar slice.
    simpa [extendedRealRealPart_eq_toReal, Function.comp, hslice] using
      (convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx (y - x)).hasDerivWithinAt
  have hderiv_Ioi : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ioi (0 : ℝ)) 0 :=
    hderiv_Ici.Ioi_of_Ici
  have hslope :
      f′[hx] (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
    -- A convex scalar slice lies above its right derivative at the left endpoint.
    simpa [g, slope_def_field, hline_apply] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
  linarith

end Core

end

/-! ### Theorem_3_1_3 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → EReal)

/- Theorem 3.1.3 is a recall-only item in the chapter's extended-real convex-analysis domain.

Primary domain:
- convex sublevel sets for `EReal`-valued convex functions on an `ℝ`-module.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- project `mem_levelSet_iff`
- chapter `extendedRealRealPart`

Best owner abstraction:
- the owner theorem `ConvexOn.convex_le`

Primitive data:
- `dom f`
- `extendedRealRealPart f`
- the owner sublevel set `{x ∈ dom f | extendedRealRealPart f x ≤ β}`

Derived API:
- the convexity conclusion for that owner sublevel set

The previous file recalled a chapter-local wrapper around the owner theorem. Since
`Theorem_3_1_1_3` now keeps only direct owner reuse and no parallel sublevel-set alias, this file
checks the specialized owner theorem itself at the canonical owner surface. -/

#check
  (show ConvexOn ℝ (dom f) (extendedRealRealPart f) →
      ∀ β : ℝ, Convex ℝ {x | x ∈ dom f ∧ extendedRealRealPart f x ≤ β} from
    ConvexOn.convex_le)

end

/-! ### Theorem_3_1_3_1 (from Chap03) -/
noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis
open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace ConvexOn

/-- Helper for Theorem 3.1.3.1: an interior effective-domain point admits a metric ball on which
the finite-value representative is Lipschitz and which stays inside the effective domain. -/
-- Proof sketch: apply the owner theorem `hf.locallyLipschitzOn_interior` to get a neighborhood
-- within `interior (dom f)`, then shrink simultaneously inside that neighborhood and inside an
-- explicit metric ball contained in `interior (dom f)`.
private theorem exists_metric_ball_lipschitzOnWith_of_mem_interior_local
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 ht with ⟨r₁, hr₁, hr₁sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r₂, hr₂, hr₂sub⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, K, hK.mono ?_⟩
  · -- The smaller ball stays inside `interior (dom f)`, hence inside `dom f)`.
    intro y hy
    exact interior_subset <|
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · -- The same smaller ball also lies in the neighborhood supporting the Lipschitz estimate.
    intro y hy
    exact hr₁sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- Helper for Theorem 3.1.3.1: on `ℝⁿ`, the Euclidean norm is bounded above by the chapter's
canonical `ℓ₁` seminorm. -/
-- Proof sketch: rewrite both norms by their coordinate formulas and compare
-- `√(∑ ‖v i‖²)` with `∑ ‖v i‖` using `Finset.sum_sq_le_sq_sum_of_nonneg`.
private theorem norm_le_l1Seminorm (v : E) :
    ‖v‖ ≤ l1Seminorm n v := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.l1Seminorm_apply]
  refine (Real.sqrt_le_iff).2 ?_
  constructor
  · -- The right-hand side is a sum of nonnegative coordinate norms.
    exact Finset.sum_nonneg fun i _ ↦ norm_nonneg (v i)
  · -- Squaring both sides reduces the comparison to the standard finite-sum inequality.
    simpa [sq] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin n ↦ ‖v i‖) (fun i _ ↦ norm_nonneg (v i))

/-- Helper for Theorem 3.1.3.1: every `ℓ₁`-ball is contained in the metric ball of the same
radius. -/
-- Proof sketch: membership in the seminorm ball gives `l1Seminorm n (y - x₀) < r`; the previous
-- norm comparison turns this into the metric-ball inequality `dist y x₀ < r`.
private theorem l1_ball_subset_metric_ball {x0 : E} {r : ℝ} :
    (l1Seminorm n).ball x0 r ⊆ Metric.ball x0 r := by
  intro y hy
  refine Metric.mem_ball.2 ?_
  have hy' : l1Seminorm n (y - x0) < r := (Seminorm.mem_ball _).1 hy
  exact lt_of_le_of_lt (norm_le_l1Seminorm (n := n) (y - x0)) <| by
    simpa [dist_eq_norm] using hy'

/-
Theorem 3.1.3.1 lies in the chapter's local regularity domain for convex `WithTop ℝ`-valued
functions on Euclidean space.

Sampled owner-style declarations:
- `ConvexOn.locallyLipschitzOn_interior` in mathlib;
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real part;
- `EuclideanSpace.l1Seminorm` in `Definition_3_7`, the chapter owner for `ℓ₁` geometry;
- `Seminorm.ball`, the canonical owner for open seminorm balls.

Best owner abstraction:
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- source-facing: a local `ℓ₁`-ball estimate on `(l1Seminorm n).ball x0 ε`;
- bridge/view: the metric-ball regularity theorem from `Theorem_3_1_11` together with the
  coordinate identity `l1Seminorm_apply`.

Primitive data:
- the convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior point `hx0 : x0 ∈ interior (dom f)`.

Derived API:
- the `ℓ₁`-ball inclusion into `dom f`;
- the local `ℓ₁`-Lipschitz estimate for `withTopRealPart f`.

This theorem remains source-facing because the textbook statement is explicitly an `ℓ₁`-ball local
estimate, but its ambient convex-analysis and `ℓ₁`-geometry data are already owned upstream. The
refinement therefore deletes the parallel inline effective-domain and coordinate-ball encodings and
states the theorem directly on those owner abstractions.
-/

/-- Theorem 3.1.3.1: if a convex `ℝ ∪ {+∞}`-valued function has `x₀` in the interior of its
effective domain, then some `ℓ₁`-ball about `x₀` stays inside the effective domain and the
finite-value part of the function satisfies a local `ℓ₁`-Lipschitz estimate there. The bounded
image consequence is recorded separately downstream. -/
-- Proof sketch: apply mathlib's local regularity theorem
-- `ConvexOn.locallyLipschitzOn_interior` to the convex real-valued representative
-- `withTopRealPart f` on the effective domain `dom f`. Then pass from the ambient Euclidean norm
-- to the chapter owner `ℓ₁` seminorm `l1Seminorm n`, and shrink the neighborhood
-- to an `ℓ₁`-ball contained in `dom f`.
theorem exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ ε > 0, ∃ L > 0,
      (l1Seminorm n).ball x0 ε ⊆ dom f ∧
        ∀ ⦃y : E⦄, y ∈ (l1Seminorm n).ball x0 ε →
          |withTopRealPart f y - withTopRealPart f x0| ≤
            L * l1Seminorm n (y - x0) := by
  obtain ⟨ε, hε, hmetric, K, hK⟩ :=
    exists_metric_ball_lipschitzOnWith_of_mem_interior_local (n := n) hf hx0
  refine ⟨ε, hε, (K : ℝ) + 1, by positivity, ?_, ?_⟩
  · -- Transport the effective-domain inclusion from the metric ball to the `ℓ₁` ball.
    exact Set.Subset.trans (l1_ball_subset_metric_ball (n := n)) hmetric
  · intro y hy
    have hyMetric : y ∈ Metric.ball x0 ε := l1_ball_subset_metric_ball (n := n) hy
    have hx0Metric : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
    have hdist := hK.dist_le_mul y hyMetric x0 hx0Metric
    rw [Real.dist_eq] at hdist
    -- First use the metric-ball Lipschitz estimate, then compare the ambient norm with `‖·‖₁`.
    calc
      |withTopRealPart f y - withTopRealPart f x0|
          ≤ (K : ℝ) * dist y x0 := hdist
      _ = (K : ℝ) * ‖y - x0‖ := by rw [dist_eq_norm]
      _ ≤ (K : ℝ) * l1Seminorm n (y - x0) := by
        gcongr
        exact norm_le_l1Seminorm (n := n) (y - x0)
      _ ≤ ((K : ℝ) + 1) * l1Seminorm n (y - x0) := by
        -- Enlarging the constant by `1` only needs the nonnegativity of the `ℓ₁` seminorm.
        have hnonneg : 0 ≤ l1Seminorm n (y - x0) := by
          rw [EuclideanSpace.l1Seminorm_apply]
          exact Finset.sum_nonneg fun i _ ↦ norm_nonneg ((y - x0) i)
        nlinarith [hnonneg]

end ConvexOn

/-! ### Theorem_3_1_3_2 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis Topology WithTopConvexAnalysis

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-
Theorem 3.1.3.2 lies in the chapter's convex directional-differentiability domain.

Primary domain:
- finite one-sided directional differentiability of convex `WithTop ℝ`-valued functions at
  interior points of the effective domain.

Relevant owner-style declarations sampled before refinement:
- `DirectionallyDifferentiableAt` and `HasDirectionalDerivAt` in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_3_1`, the source-facing directional-derivative owners;
- `dom f`, `withTopRealPart f`, and `withTopToEReal ∘ f` in `Definition_3_3`, the chapter's
  canonical bridge from `WithTop ℝ`-valued convex functions to the `EReal` directional-derivative
  owner surface;
- `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain` in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_1_12`, the upstream finite-real secant-slope limit theorem that
  supplies the bridge data.

Best owner abstraction:
- `DirectionallyDifferentiableAt (withTopToEReal ∘ f) x p`

Primitive data:
- the convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior-point assumption `hx : x ∈ interior (dom f)`.

Derived API:
- the source-facing directional differentiability statement below;
- the explicit `∃ d, HasDirectionalDerivAt ... d` companion.

Source/core/bridge triage:
- source-facing: directional differentiability of a convex `WithTop ℝ`-valued function at an
  interior point of `dom f`;
- core/canonical: `DirectionallyDifferentiableAt` and `HasDirectionalDerivAt`;
- bridge/view: the secant-slope existence theorem `Theorem_3_1_12`.

The previous version moved the numbered item to the weaker `EReal` secant-limit bridge layer by
recalling `Theorem_3_14`. This file now returns to the source-facing directional-derivative API,
uses `Theorem_3_1_12` only as internal bridge data, and keeps the ambient space at the weaker
topological real-module owner level already used by `HasDirectionalDerivAt`, rather than freezing
the older normed-space proof route into the public theorem surface.
-/
namespace ConvexOn

/-- Theorem 3.1.3.2: a convex `ℝ ∪ {+∞}`-valued function is directionally differentiable in every
direction at every interior point of its effective domain. -/
-- Proof sketch: `Theorem_3_1_12` already yields a finite real right limit of the secant slopes
-- together with eventual finiteness of the ray. Interpreting that limit as a derivative of the
-- scalar slice gives `HasDirectionalDerivAt` for the canonical `EReal` bridge `withTopToEReal ∘
-- f`, and hence `DirectionallyDifferentiableAt`.
theorem directionallyDifferentiableAt_of_mem_interior_dom
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    DirectionallyDifferentiableAt (withTopToEReal ∘ f) x p := by
  have hmem_dom_toEReal {y : E} (hy : y ∈ dom f) :
      y ∈ dom (withTopToEReal ∘ f) := by
    change withTopToEReal (f y) ≠ ⊤ ∧ withTopToEReal (f y) ≠ ⊥
    constructor
    · intro htop
      exact (ne_of_lt hy) (WithBot.coe_eq_top.mp htop)
    · exact WithBot.coe_ne_bot
  rcases exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
      hf hx with ⟨d, hd_dom, hd_tendsto⟩
  refine ⟨d, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hmem_dom_toEReal (interior_subset hx)
  · filter_upwards [hd_dom] with α hα
    exact hmem_dom_toEReal hα
  · have hderiv :
        HasDerivWithinAt
          (fun α ↦ extendedRealRealPart (withTopToEReal ∘ f) (x + α • p))
          d (Set.Ioi (0 : ℝ)) 0 := by
        have hslice :
            (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x + α • p)) =
              fun α : ℝ ↦ withTopRealPart f (x + α • p) := by
          funext α
          cases hfx : f (x + α • p) with
          | top =>
              simp [extendedRealRealPart, withTopRealPart, withTopToEReal, Function.comp, hfx]
              rfl
          | coe a =>
              simp [extendedRealRealPart, withTopRealPart, withTopToEReal, Function.comp, hfx]
              rfl
        rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
        rw [hslice]
        simpa [slope_fun_def_field] using hd_tendsto
    exact hderiv.Ici_of_Ioi

/-- A convex `ℝ ∪ {+∞}`-valued function admits a finite directional derivative in every direction
at every interior point of its effective domain. -/
theorem exists_hasDirectionalDerivAt_of_mem_interior_dom
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    ∃ d : ℝ, HasDirectionalDerivAt (withTopToEReal ∘ f) x p d := by
  simpa [DirectionallyDifferentiableAt] using
    hf.directionallyDifferentiableAt_of_mem_interior_dom hx

end ConvexOn

end

/-! ### Corollary_3_1_4 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E]

/- Corollary 3.1.4 is source-facing in the chapter's hyperplane-separation domain.

Primary domain:
- affine hyperplanes and point/set separation in a real inner-product space.

Sampled owner declarations:
- `AffineHyperplane`
- `AreStronglySeparable`
- `areStronglySeparable_singleton_of_nonmem_closed_convex`
- `areStronglySeparable_empty_singleton`

Core/canonical owner:
- `AreStronglySeparable Q ({x} : Set E)`, built from the chapter's `AffineHyperplane` owner API.

Bridge/view:
- `areStronglySeparable_iff`, which converts the owner-level set separation statement into
  coordinate data `(g, γ)`.

Primitive data:
- the nonzero normal vector and offset from the owner hyperplane API.

Derived API:
- the retained point-versus-set bridge `SeparatesPointFromWith Q x g γ`;
- the strict upper-side inequality `γ < ⟪g, x⟫`.

This file keeps the source-facing coordinate conclusion, but it now reuses the owner theorem
`AreStronglySeparable.exists_separatesPointFromWith` for the singleton-right bridge instead of
rebuilding that conversion locally. The public statement therefore stays source-faithful while the
singleton bridge lives at the owner layer, with the textbook `ℝⁿ` statement recovered by
specializing to `E = EuclideanSpace ℝ (Fin n)` and `n > 0`.
-/

/-- Corollary 3.1.4: if `Q` is a closed convex set in a nontrivial real inner-product space and
`x ∉ Q`, then there exist a nonzero normal vector `g` and an offset `γ` such that
`Q` lies in the lower closed half-space `⟪g, y⟫ ≤ γ` and `x` lies strictly above it:
`γ < ⟪g, x⟫`. The lower-side half-space inclusion is packaged by
`SeparatesPointFromWith Q x g γ`. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)` with `n > 0`. -/
-- Proof sketch: if `Q` is nonempty, apply the owner-level strong-separation theorem to `Q` and
-- the singleton `{x}`. If `Q = ∅`, use the intrinsic empty-set separation companion. Then apply
-- the canonical singleton-right bridge
-- `AreStronglySeparable.exists_separatesPointFromWith`.
theorem exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
    (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x : E} (hx : x ∉ Q) :
    ∃ g : E, ∃ γ : ℝ, SeparatesPointFromWith Q x g γ ∧ γ < inner ℝ g x := by
  have hstrong : AreStronglySeparable Q ({x} : Set E) := by
    by_cases hQ_nonempty : Q.Nonempty
    · exact
        areStronglySeparable_singleton_of_nonmem_closed_convex
          Q hQ_nonempty hQ_closed hQ_convex hx
    · have hQ_empty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ_nonempty
      simpa [hQ_empty] using
        (show AreStronglySeparable (∅ : Set E) ({x} : Set E) from
          areStronglySeparable_empty_singleton x)
  exact hstrong.exists_separatesPointFromWith

end

/-! ### Corollary_3_1_4_1 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Corollary 3.1.4.1 lies in the chapter's affine-hyperplane strong-separation domain.

Primary domain:
- strong separation of a closed convex set from an exterior point in a real inner-product space.

Relevant sampled declarations:
- `AreStronglySeparable` in `Definition_3_12`, the owner predicate for strong separation;
- `areStronglySeparable_empty_singleton` in `Definition_3_12`, the intrinsic empty-set companion;
- `areStronglySeparable_singleton_of_nonmem_closed_convex` in `Theorem_3_16`, the canonical
  owner-level theorem for the nonempty case;
- `exists_strictlySeparating_hyperplane_of_nonmem_closed_convex` in `Corollary_3_1_4`, the
  downstream coordinate bridge from the owner predicate to `(g, γ)`.

Best owner abstraction:
- `AreStronglySeparable`.

Primitive data:
- the closed convex set `Q`, the exterior point `x`, and, for the canonical owner theorem, the
  genuinely used nonemptiness witness `Q.Nonempty`.

Derived API:
- the owner-level theorem `areStronglySeparable_singleton_of_nonmem_closed_convex`;
- the coordinate `(g, γ)` consequence in `Corollary_3_1_4`.

Source/core/bridge triage:
- source-facing: the chapter corollary asserting strong separation of a closed convex set and an
  exterior point;
- core/canonical: `AreStronglySeparable Q ({x} : Set E)`;
- bridge/view: this file, which now reuses the existing owner theorem directly instead of keeping a
  second Euclidean-space-specialized wrapper.

The previous version introduced a new theorem over `EuclideanSpace ℝ (Fin n)` with a positivity
assumption on `n`, even though the mathematics here is already captured intrinsically by the
earlier owner theorem and the coordinate bridge is already handled in `Corollary_3_1_4`. This file
therefore becomes recall-only: `ℝⁿ` remains available purely as a downstream specialization of the
intrinsic owner statement.
-/

/- Corollary 3.1.4.1 is the direct chapter reuse of the canonical owner theorem for separating a
closed convex set from an exterior point. The coordinate `(g, γ)` form is recovered separately by
`exists_strictlySeparating_hyperplane_of_nonmem_closed_convex`. -/
recall areStronglySeparable_singleton_of_nonmem_closed_convex

end

/-! ### Corollary_3_1_4_2 (from Chap03) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConvexAnalysis SupportFunction

/- Corollary 3.1.4.2 belongs to the chapter's support-function comparison domain.

Primary domain:
- support functions of subsets of a real Hilbert space and the extended-real effective domain.

Sampled owner declarations:
- `extendedRealEffectiveDomain` / `dom` from `Definition_3_1_1_2`
- `supportFunction` from `Definition_3_9`
- `subset_of_supportFunction_le_on_domain` from `Theorem_3_17`
- `supportFunction_eq_on_common_domain_implies_eq` from `Theorem_3_17`

Source-facing layer:
- equality of closed convex sets from agreement of their support functions on the common
  finite-value domain, with empty/nonempty status already encoded by the shared effective domain.

Core/canonical layer:
- the owner constructions `extendedRealEffectiveDomain` and `supportFunction`, together with the
  exact comparison theorem `supportFunction_eq_on_common_domain_implies_eq`.

Bridge/view:
- the companion inclusion theorem `subset_of_supportFunction_le_on_domain`.

Primitive data:
- the sets `Q₁`, `Q₂` and the canonical support-function/effective-domain constructions.

Derived API:
- the inclusion and equality comparison theorems for those owner constructions.

This file therefore reuses the exact owner theorem from `Theorem_3_17` instead of keeping a
parallel local copy of `supportFunction`, `extendedRealEffectiveDomain`, and the same comparison
statement under a second name.
-/

recall supportFunction_eq_on_common_domain_implies_eq
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂
