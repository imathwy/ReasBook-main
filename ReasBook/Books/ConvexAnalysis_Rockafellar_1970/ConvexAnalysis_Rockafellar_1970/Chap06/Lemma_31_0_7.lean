import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_6_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.7 records the primal optimal-value identity and the
  strong-consistency criterion for the Fenchel perturbation program
  `F(u, x) = f x - g (A x + u)`.
- `core/canonical`: the owner abstractions already present in the project are
  `fenchelPerturbation`, `optimalValue`, `IsStronglyConsistent`, and the Chapter 1 domain owners
  `dom(·)` / `riDom[𝕜](·)`.
- `bridge/view`: the source formula `inf_x (f x - g (A x))` is the canonical optimal value
  `optimalValue (fenchelPerturbation A f g)`, equivalently the indexed infimum of the zero slice
  `objective (fenchelPerturbation A f g)`, and the source qualification condition is rendered in
  the existing domain language via `riDom[𝕜](f)` and `riDom[𝕜](-g)`.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation` and `objective_fenchelPerturbation_apply` from
  `Lemma_31_0_6`;
- `Bifunction.optimalValue` and `optimalValue_eq_iInf` from `Definition_6_29_15`;
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- the Chapter 1 owners `dom(·)` and `riDom[𝕜](·)`.

Layer target: keep the public API on the existing perturbation-program owners, with the primal
optimal-value clause stated directly on `optimalValue` and one labeled theorem for the
strong-consistency clause.

Abstraction notes for this file:
- the primal optimal-value clause is stated on the Chapter 6 owner `optimalValue`, with the raw
  zero-slice infimum view remaining derived through `optimalValue_eq_iInf`;
- the qualification clause stays on the same source-facing owner layer, but now uses the scalar-
  generic domain notation `riDom[𝕜](·)` and strong-consistency owner `IsStronglyConsistent 𝕜`;
  its ambient assumptions are trimmed to the finite-dimensional normed-field owner layer actually
  used by the Chapter 2 relative-interior image/preimage/sum bridges.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {α : Type*}
variable [Semiring 𝕜]
variable [InfSet (WithBotTop α)]
variable [Add α] [Neg α]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- The primal optimal value of the Fenchel perturbation program is the infimum of the source
expression `x ↦ f x - g (A x)`. -/
-- Proof sketch: rewrite `optimalValue` as the infimum of the zero-slice objective via
-- `optimalValue_eq_iInf`, then use `objective_fenchelPerturbation_apply` pointwise.
theorem optimalValue_fenchelPerturbation_eq_iInf
    (A : X →ₗ[𝕜] U) (f : X → WithBotTop α) (g : U → WithBotTop α) :
    optimalValue (fenchelPerturbation A f g) = ⨅ x : X, f x - g (A x) := by
  simpa using (optimalValue_eq_iInf (fenchelPerturbation A f g))

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [Preorder 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- The domain of the Fenchel perturbation consists exactly of sums `v + (-A x)` with
`v ∈ dom(-g)` and `x ∈ dom(f)`. -/
private theorem dom_fenchelPerturbation_eq
    (A : X →ₗ[𝕜] U) {f : X → WithBotTop 𝕜} {g : U → WithBotTop 𝕜}
    (hf_bot_lt : ∀ x, ⊥ < f x) (hg_bot_lt : ∀ u, ⊥ < (-g) u) :
    dom (fenchelPerturbation A f g) = dom(-g) + ((-A) '' dom(f)) := by
  ext u
  constructor
  · intro hu
    rcases (mem_dom_iff_exists.mp hu) with ⟨x, hx⟩
    have hsum_ne_top : f x + (-g) (A x + u) ≠ ⊤ := by
      exact lt_top_iff_ne_top.mp <| by
        simpa [fenchelPerturbation, sub_eq_add_neg, add_comm] using hx
    have hsum_finite :=
      (WithBotTop.add_ne_top_iff_ne_top₂ (hf_bot_lt x).ne' (hg_bot_lt (A x + u)).ne').1 hsum_ne_top
    have hx_dom : x ∈ dom(f) := by
      rw [mem_effectiveDomain]
      exact lt_top_iff_ne_top.mpr hsum_finite.1
    have hAxu_dom : A x + u ∈ dom(-g) := by
      rw [mem_effectiveDomain]
      exact lt_top_iff_ne_top.mpr hsum_finite.2
    refine ⟨A x + u, hAxu_dom, -A x, ?_, ?_⟩
    · exact ⟨x, hx_dom, rfl⟩
    · simp [add_assoc]
  · rintro ⟨v, hv, w, hw, rfl⟩
    rcases hw with ⟨x, hx_dom, rfl⟩
    refine mem_dom_iff_exists.mpr ⟨x, ?_⟩
    have hfx_ne_top : f x ≠ ⊤ := by
      exact lt_top_iff_ne_top.mp <| by
        simpa [mem_effectiveDomain] using hx_dom
    have hv_ne_top : (-g) v ≠ ⊤ := by
      exact lt_top_iff_ne_top.mp <| by
        simpa [mem_effectiveDomain] using hv
    have hsum_ne_top : f x + (-g) v ≠ ⊤ := by
      exact (WithBotTop.add_ne_top_iff_ne_top₂ (hf_bot_lt x).ne' (hg_bot_lt v).ne').2
        ⟨hfx_ne_top, hv_ne_top⟩
    have hsum_lt_top : f x + (-g) v < ⊤ :=
      lt_top_iff_ne_top.mpr hsum_ne_top
    simpa [fenchelPerturbation, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hsum_lt_top

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]

/-- Lemma 31.0.7: over the chapter's finite-dimensional normed-field owner layer, the Fenchel
perturbation program attached to `A`, `f`, and `g` is strongly consistent exactly when the
relative-interior qualification set `riDom[𝕜](f) ∩ A ⁻¹' riDom[𝕜](-g)` is nonempty. -/
-- Proof sketch: identify `dom (perturbationFunction (fenchelPerturbation A f g))` with the
-- Minkowski sum `dom(-g) + (-(A '' dom(f)))`, rewrite its relative interior using the linear-image
-- and sum formulas for convex sets, and then evaluate the condition that `0` lies in that
-- relative interior.
theorem isStronglyConsistent_fenchelPerturbation_iff_riDom_inter_preimage_nonempty
    (A : X →ₗ[𝕜] U) {f : X → WithBotTop 𝕜} {g : U → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 (fenchelPerturbation A f g) ↔
      (riDom[𝕜](f) ∩ A ⁻¹' riDom[𝕜](-g)).Nonempty := by
  have hg_convex : (-g).IsConvex 𝕜 := hg_concave.convex_neg
  have hg_neg_proper : (-g).IsProper := hg_proper.neg_isProper
  have hconv_image : Convex 𝕜 ((-A) '' dom(f)) :=
    hf_convex.convex_dom.linear_image (-A)
  rw [isStronglyConsistent_iff,
    dom_fenchelPerturbation_eq A hf_proper.bot_lt hg_neg_proper.bot_lt]
  rw [hg_convex.convex_dom.intrinsicInterior_add hconv_image]
  rw [hf_convex.convex_dom.intrinsicInterior_linear_image (-A)]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases hv with ⟨x, hx, rfl⟩
    refine ⟨x, ?_⟩
    have hu_eq : u = A x := by
      simpa using eq_neg_of_add_eq_zero_left huv
    refine ⟨hx, ?_⟩
    simpa [Set.mem_preimage, hu_eq] using hu
  · rintro ⟨x, hx⟩
    refine ⟨A x, ?_, -A x, ⟨x, hx.1, rfl⟩, by simp⟩
    simpa [Set.mem_preimage] using hx.2

/-- Lemma 31.0.7, existential view: strong consistency is equivalent to existence of
`x ∈ riDom[𝕜](f)` with `A x ∈ riDom[𝕜](-g)`. -/
theorem isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom
    (A : X →ₗ[𝕜] U) {f : X → WithBotTop 𝕜} {g : U → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 (fenchelPerturbation A f g) ↔
      ∃ x : X, x ∈ riDom[𝕜](f) ∧ A x ∈ riDom[𝕜](-g) := by
  simpa [Set.nonempty_def, Set.mem_inter_iff, Set.mem_preimage] using
    (isStronglyConsistent_fenchelPerturbation_iff_riDom_inter_preimage_nonempty
      A hf_convex hf_proper hg_concave hg_proper)

end

end Bifunction
