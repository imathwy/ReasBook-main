import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped BigOperators
open Function

noncomputable section

section

variable {E : Type u}
variable {ι : Type v}
variable {α : Type w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1 introduces the infimal convolution of a finite family
  `f : ι → E → EReal`; in this file, that owner is stated on the canonical codomain
  `WithTopBot α` and takes the infimum of `∑ i, f i (x i)` over finite decompositions
  `∑ i in s, x i = x`.
- `core/canonical`: the chapter owner abstraction for this kind of construction is
  `Function.verticalInfimum` from Theorem 5.3, applied to the scalar-height set of admissible
  finite decompositions indexed by a `Finset`.
- `bridge/view`: the binary operation `f □ g` from `Text_5_4_0` is identified with the
  `Finset.univ` finite-family owner both on the source-facing pair surface `![f, g]` and through
  the `Fin 2` family bridge.
- Primitive data vs derived API: the family `f` and a finite index set `s : Finset ι` are
  primitive; `finsetInfimalConvolution s f` is the canonical finite operational owner via
  `Function.verticalInfimum`; `finiteInfimalConvolution` is the `Fintype` specialization
  `s = Finset.univ`; decomposition formulas and binary-specialization are derived bridge results.
- Layer target: `source-facing`; the finite-family owner remains the public chapter declaration
  at the `Finset` layer, and the `Fin 2` comparison with `□` is kept as bridge API.
- Ambient minimization: support owners use only finite additive sums and scalar-height comparison,
  so they stay at `[AddCommMonoid E]`, `[AddCommMonoid α]`, `[LE α]`; the infimum owners add only
  the conditional completeness required by `Function.verticalInfimum`, i.e.
  `[ConditionallyCompleteLattice α]`. The decomposition formulas are stated at this same lattice
  layer, while the support-convexity bridge stays on the weaker ordered-semiring layer.
  The `Fintype` owner is kept only as a
  `Finset.univ` bridge to preserve chapter-level downstream theorems.

Domain-style sampling used here:
- the chapter owner declaration `Function.verticalInfimum` from `Theorem_5_3`;
- its companion theorem `Function.verticalInfimum_eq_sInf`;
- the chapter owner declaration `infimal_convolution` from `Text_5_4_0`;
- its companion theorem `infimal_convolution_eq_sInf_decompositions`;
 -/

section Support

variable [LE α]

/-- The scalar-height support set encoding admissible decompositions over a finite index set `s`
for the family `f`. This is the bridge object whose `Function.verticalInfimum` is
`finsetInfimalConvolution s f`. -/
def finsetInfimalConvolutionSupport (s : Finset ι)
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) : Set (E × α) :=
  {p | ∃ xs : ι → E, (∑ i ∈ s, xs i) = p.1 ∧ (∑ i ∈ s, f i (xs i)) ≤ p.2}

section FintypeFamily

variable [Fintype ι]

/-- The `Fintype` support owner is the `Finset.univ` specialization of
`finsetInfimalConvolutionSupport`. -/
def finiteInfimalConvolutionSupport
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) : Set (E × α) :=
  finsetInfimalConvolutionSupport (s := (Finset.univ : Finset ι)) f

end FintypeFamily

end Support

section Geometric

variable [ConditionallyCompleteLattice α]

/-- Text 5.4.1 at finite operational level: the infimal convolution over a finite index set `s`
sends `x` to the infimum of `∑ i in s, f i (x i)` over all decompositions `∑ i in s, x i = x`.
This geometric owner is defined via `Function.verticalInfimum`. -/
def finsetInfimalConvolution (s : Finset ι)
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) : E → WithTopBot α :=
  verticalInfimum (finsetInfimalConvolutionSupport s f)

/-- The finite-operational infimal convolution is the vertical infimum of its decomposition
support set. -/
@[simp] theorem finsetInfimalConvolution_eq_verticalInfimum (s : Finset ι)
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) :
    finsetInfimalConvolution s f = verticalInfimum (finsetInfimalConvolutionSupport s f) := rfl

section FintypeFamily

variable [Fintype ι]

/-- The finite-family owner is the `Finset.univ` specialization of `finsetInfimalConvolution`. -/
def finiteInfimalConvolution
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) : E → WithTopBot α :=
  finsetInfimalConvolution (s := (Finset.univ : Finset ι)) f

/-- The `Fintype` finite-family infimal convolution is the vertical infimum of its decomposition
support set. -/
@[simp] theorem finiteInfimalConvolution_eq_verticalInfimum
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) :
    finiteInfimalConvolution f = verticalInfimum (finiteInfimalConvolutionSupport f) := rfl

/-- Reindexing a finite family along an equivalence does not change its finite infimal
convolution. This owner-level invariance only uses the primitive finite-sum layer. -/
theorem finiteInfimalConvolution_comp_equiv {κ : Type*} [Fintype κ]
    [AddCommMonoid α] [AddCommMonoid E]
    (e : ι ≃ κ) (f : κ → E → WithTopBot α) :
    finiteInfimalConvolution (f ∘ e) = finiteInfimalConvolution f := by
  have hsupport :
      finiteInfimalConvolutionSupport (f ∘ e) = finiteInfimalConvolutionSupport f := by
    ext p
    constructor
    · rintro ⟨xs, hsum, hle⟩
      refine ⟨xs ∘ e.symm, ?_, ?_⟩
      · simpa [Function.comp] using (e.symm.sum_comp xs).trans hsum
      · have hsumf :
            (∑ i, (f ∘ e) i (xs i)) = ∑ j, f j ((xs ∘ e.symm) j) := by
          simpa [Function.comp] using (e.sum_comp fun j ↦ f j ((xs ∘ e.symm) j))
        exact hsumf ▸ hle
    · rintro ⟨xs, hsum, hle⟩
      refine ⟨xs ∘ e, ?_, ?_⟩
      · simpa [Function.comp] using (e.sum_comp xs).trans hsum
      · have hsumf :
            (∑ j, f j (xs j)) = ∑ i, (f ∘ e) i ((xs ∘ e) i) := by
          simpa [Function.comp] using (e.symm.sum_comp fun i ↦ f (e i) ((xs ∘ e) i))
        exact hsumf ▸ hle
  simpa [finiteInfimalConvolution, finsetInfimalConvolution] using
    congrArg verticalInfimum hsupport

end FintypeFamily

-- Proof sketch: unfold `finsetInfimalConvolution s` as `Function.verticalInfimum` of the support
-- set `finsetInfimalConvolutionSupport s f`, then specialize
-- `Function.verticalInfimum_eq_sInf`. Passing from the scalar-height
-- epigraph condition `∑ i in s, f i (xs i) ≤ μ` to the exact-value infimum over `WithTopBot α`
-- sums
-- does not change the infimum, because the infimum of the upward closure of a subset of
-- `WithTopBot α` is the infimum of the subset itself.
section DecompositionFormulas

/-- Helper for Text 5.4.1: a finite sum of non-`⊥` values in `WithTopBot α` stays off `⊥`. -/
private theorem sum_ne_bot_of_forall_ne_bot (s : Finset ι) [AddCommMonoid α]
    (g : ι → WithTopBot α) (hg : ∀ i ∈ s, g i ≠ ⊥) :
    (∑ i ∈ s, g i) ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is the finite zero branch, hence not `⊥`.
      change
        (((0 : α) : WithBot α) : WithTop (WithBot α)) ≠
          ((⊥ : WithBot α) : WithTop (WithBot α))
      intro h
      exact WithBot.coe_ne_bot (WithTop.coe_injective h)
  | @insert i s hi ih =>
      -- Peel off one summand and use the `WithTopBot` `add_eq_bot` characterization.
      have hi_ne_bot : g i ≠ ⊥ := hg i (by simp)
      have hs_ne_bot : (∑ j ∈ s, g j) ≠ ⊥ := by
        refine ih ?_
        intro j hj
        exact hg j (by simp [hj])
      rw [Finset.sum_insert hi]
      cases hgi : g i using WithTop.recTopCoe with
      | top => simp [hgi]
      | coe gi =>
          cases hgs : ∑ j ∈ s, g j using WithTop.recTopCoe with
          | top => simp [hgi, hgs]
          | coe gs =>
              have hgi_ne : gi ≠ ⊥ := by
                intro h
                apply hi_ne_bot
                calc
                  g i = (gi : WithTopBot α) := hgi
                  _ = ((⊥ : WithBot α) : WithTopBot α) := congrArg (fun z : WithBot α ↦ (z : WithTopBot α)) h
                  _ = ⊥ := rfl
              have hgs_ne : gs ≠ ⊥ := by
                intro h
                apply hs_ne_bot
                calc
                  ∑ j ∈ s, g j = (gs : WithTopBot α) := hgs
                  _ = ((⊥ : WithBot α) : WithTopBot α) := congrArg (fun z : WithBot α ↦ (z : WithTopBot α)) h
                  _ = ⊥ := rfl
              change
                ((gi + gs : WithBot α) : WithTop (WithBot α)) ≠
                  ((⊥ : WithBot α) : WithTop (WithBot α))
              intro h
              exact (WithBot.add_ne_bot.mpr ⟨hgi_ne, hgs_ne⟩) (WithTop.coe_injective h)

/-- Helper for Text 5.4.1: the infimum of the finite upper bounds above a non-`⊥` height is that
height itself. -/
private theorem upper_height_sInf_eq_of_ne_bot [AddCommMonoid α] {r : WithTopBot α}
    (hr : r ≠ ⊥) :
    sInf (((↑) : α → WithTopBot α) '' {μ : α | r ≤ μ}) = r := by
  induction r using WithTop.recTopCoe with
  | top =>
      -- The `⊤` slice has no finite upper bounds, so its infimum is `⊤`.
      simp
  | coe r =>
      induction r using WithBot.recBotCoe with
      | bot =>
          exact (hr rfl).elim
      | coe a =>
          -- In the finite branch, `a` itself is the least finite upper bound.
          let S : Set (WithTopBot α) :=
            ((↑) : α → WithTopBot α) '' {μ : α | ((a : α) : WithTopBot α) ≤ μ}
          have hleast : IsLeast S ((a : α) : WithTopBot α) := by
            constructor
            · exact ⟨a, (show ((a : α) : WithTopBot α) ≤ (a : α) from le_rfl), rfl⟩
            · intro z hz
              rcases hz with ⟨μ, hμ, rfl⟩
              simpa using hμ
          exact hleast.csInf_eq

/-- The finite-operational infimal convolution `finsetInfimalConvolution s f` is the infimum of
the values `∑ i in s, f i (x i)` over all decompositions `∑ i in s, x i = x`, provided the
summands indexed by `s` never take the value `⊥`. -/
theorem finsetInfimalConvolution_eq_sInf_decompositions (s : Finset ι)
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α)
    (hf_ne_bot : ∀ i ∈ s, ∀ y, f i y ≠ ⊥) (x : E) :
    finsetInfimalConvolution s f x =
      sInf {r : WithTopBot α | ∃ xs : ι → E, (∑ i ∈ s, xs i) = x ∧
        r = ∑ i ∈ s, f i (xs i)} := by
  let U : Set (WithTopBot α) :=
    ((↑) : α → WithTopBot α) ''
      {μ : α | ∃ xs : ι → E, (∑ i ∈ s, xs i) = x ∧ (∑ i ∈ s, f i (xs i)) ≤ μ}
  let D : Set (WithTopBot α) :=
    {r : WithTopBot α | ∃ xs : ι → E, (∑ i ∈ s, xs i) = x ∧ r = ∑ i ∈ s, f i (xs i)}
  -- Route correction: the unguarded statement is false when a decomposition value can be `⊥`;
  -- with the no-`⊥` guard in place, each fiber slice has the expected infimum.
  rw [finsetInfimalConvolution_eq_verticalInfimum, Function.verticalInfimum_eq_sInf]
  change sInf U = sInf D
  apply le_antisymm
  · -- Each exact decomposition value bounds the infimum over its own upper-height slice.
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨xs, hsum, rfl⟩
    let S : Set (WithTopBot α) :=
      ((↑) : α → WithTopBot α) '' {μ : α | (∑ i ∈ s, f i (xs i)) ≤ μ}
    have hS_subset : S ⊆ U := by
      intro z hz
      rcases hz with ⟨μ, hμ, rfl⟩
      exact ⟨μ, ⟨xs, hsum, hμ⟩, rfl⟩
    have hsum_ne_bot : (∑ i ∈ s, f i (xs i)) ≠ ⊥ := by
      refine sum_ne_bot_of_forall_ne_bot (s := s) (g := fun i ↦ f i (xs i)) ?_
      intro i hi
      exact hf_ne_bot i hi (xs i)
    have hsInf_slice : sInf U ≤ sInf S := by
      refine le_sInf ?_
      intro z hz
      exact sInf_le (hS_subset hz)
    exact le_trans hsInf_slice (by
      simpa [S] using (upper_height_sInf_eq_of_ne_bot hsum_ne_bot).le)
  · -- Every finite upper bound in `U` dominates the exact decomposition-value infimum.
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨μ, ⟨xs, hsum, hle⟩, rfl⟩
    have hmem : (∑ i ∈ s, f i (xs i)) ∈ D := by
      exact ⟨xs, hsum, rfl⟩
    exact le_trans (sInf_le hmem) hle

section FintypeFamily

variable [Fintype ι]

/-- The `Fintype` finite-family infimal convolution `finiteInfimalConvolution f` is the infimum
of `∑ i, f i (x i)` over all decompositions `∑ i, x i = x`, provided the family never takes the
value `⊥`. -/
theorem finiteInfimalConvolution_eq_sInf_decompositions
    [AddCommMonoid α] [AddCommMonoid E]
    (f : ι → E → WithTopBot α) (hf_ne_bot : ∀ i y, f i y ≠ ⊥) (x : E) :
    finiteInfimalConvolution f x =
      sInf {r : WithTopBot α | ∃ xs : ι → E, (∑ i, xs i) = x ∧ r = ∑ i, f i (xs i)} := by
  classical
  simpa [finiteInfimalConvolution, finiteInfimalConvolutionSupport] using
    (finsetInfimalConvolution_eq_sInf_decompositions (s := (Finset.univ : Finset ι)) f
      (fun i _ y ↦ hf_ne_bot i y) x)

end FintypeFamily

end DecompositionFormulas

end Geometric

end

section Convexity

variable {E : Type u}
variable {ι : Type v}
variable {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Helper for Text 5.4.1: the scalar action on `WithTopBot 𝕜` is multiplication by the finite
scalar branch. -/
local instance instSMulWithTopBot541 : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

private theorem mul_le_mul_left_coe_withTopBot {a : 𝕜} (ha : 0 ≤ a)
    {u v : WithTopBot 𝕜} (h : u ≤ v) :
    (a : WithTopBot 𝕜) * u ≤ (a : WithTopBot 𝕜) * v := by
  induction v using WithTop.recTopCoe with
  | top =>
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha0' : (a : WithTopBot 𝕜) ≠ 0 := by exact_mod_cast ha0
        rw [WithTop.mul_top ha0']
        exact le_top
  | coe v =>
      induction u using WithTop.recTopCoe with
      | top => simp at h
      | coe u =>
          have huv : u ≤ v := WithTop.coe_le_coe.mp h
          have ha' : (0 : WithBot 𝕜) ≤ (a : WithBot 𝕜) := WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

/-- Helper for Text 5.4.1: a nonnegative scalar preserves an upper bound by a finite height in
`WithTopBot 𝕜`. -/
private theorem smul_le_smul_coe_of_le_coe {a μ : 𝕜} (ha : 0 ≤ a) {z : WithTopBot 𝕜}
    (hz : z ≤ (μ : WithTopBot 𝕜)) :
    a • z ≤ a • (μ : WithTopBot 𝕜) := by
  change (a : WithTopBot 𝕜) * z ≤ (a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜)
  exact mul_le_mul_left_coe_withTopBot ha hz

/-- The canonical finite-branch scalar action distributes over `WithTopBot` addition. -/
private theorem smul_add_withTopBot (a : 𝕜) (ha : a ≠ 0)
    (u v : WithTopBot 𝕜) :
    (a : WithTopBot 𝕜) * (u + v) =
      (a : WithTopBot 𝕜) * u + (a : WithTopBot 𝕜) * v := by
  have ha_top : (a : WithTopBot 𝕜) ≠ 0 := by exact_mod_cast ha
  have ha_bot : (a : WithBot 𝕜) ≠ 0 := by exact_mod_cast ha
  induction u using WithTop.recTopCoe with
  | top => simp [WithTop.mul_top ha_top]
  | coe u =>
      induction v using WithTop.recTopCoe with
      | top => simp [WithTop.mul_top ha_top]
      | coe v =>
          induction u using WithBot.recBotCoe with
          | bot =>
              change
                (((a : WithBot 𝕜) * (⊥ + v) : WithBot 𝕜) : WithTopBot 𝕜) =
                  (((a : WithBot 𝕜) * ⊥ + (a : WithBot 𝕜) * v : WithBot 𝕜) :
                    WithTopBot 𝕜)
              rw [WithBot.bot_add, WithBot.mul_bot ha_bot, WithBot.bot_add]
          | coe u =>
              induction v using WithBot.recBotCoe with
              | bot =>
                  change
                    (((a : WithBot 𝕜) * ((u : WithBot 𝕜) + ⊥) : WithBot 𝕜) :
                        WithTopBot 𝕜) =
                      (((a : WithBot 𝕜) * (u : WithBot 𝕜) +
                          (a : WithBot 𝕜) * ⊥ : WithBot 𝕜) : WithTopBot 𝕜)
                  rw [WithBot.add_bot, WithBot.mul_bot ha_bot, WithBot.add_bot]
              | coe v =>
                  change
                    (((a * (u + v) : 𝕜) : WithBot 𝕜) : WithTopBot 𝕜) =
                      (((a * u + a * v : 𝕜) : WithBot 𝕜) : WithTopBot 𝕜)
                  rw [mul_add]

/-- Finite-sum form of `smul_add_withTopBot`. -/
private theorem sum_smul_withTopBot (s : Finset ι) (a : 𝕜) (ha : a ≠ 0)
    (g : ι → WithTopBot 𝕜) :
    (∑ i ∈ s, a • g i) = a • ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (0 : WithTopBot 𝕜) = (a : WithTopBot 𝕜) * 0
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
      change
        (a : WithTopBot 𝕜) * g i + (a : WithTopBot 𝕜) * ∑ j ∈ s, g j =
          (a : WithTopBot 𝕜) * (g i + ∑ j ∈ s, g j)
      exact (smul_add_withTopBot a ha _ _).symm

-- Proof sketch: `finsetInfimalConvolutionSupport s f` consists of pairs `(x, μ)` admitting a
-- finite decomposition `x = ∑ i in s, xs i` with scalar height bounded by
-- `∑ i in s, f i (xs i) ≤ μ`. For each
-- `i`, convexity of `f i` gives convexity of its epigraph slice
-- `{(x, μ) | f i x ≤ μ}`; combining these finite decomposition witnesses along convex
-- combinations and summing componentwise yields convexity of the support owner.
/-- If each summand of a family is convex, then the support set used by
`finsetInfimalConvolution` on a finite index set `s` is convex. This is the owner-level bridge
feeding Theorem 5.4 through `Function.isConvex_verticalInfimum`. -/
theorem convex_finsetInfimalConvolutionSupport (s : Finset ι)
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i ∈ s, ConvexOn 𝕜 (Set.univ : Set E) (f i)) :
    Convex 𝕜 (finsetInfimalConvolutionSupport s f) := by
  rintro ⟨x, μ⟩ ⟨xs, hxs_sum, hxs_le⟩ ⟨y, ν⟩ ⟨ys, hys_sum, hys_le⟩ a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by simpa using hab
    subst b
    simpa using (⟨ys, hys_sum, hys_le⟩ : (y, ν) ∈ finsetInfimalConvolutionSupport s f)
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by simpa using hab
    subst a
    simpa using (⟨xs, hxs_sum, hxs_le⟩ : (x, μ) ∈ finsetInfimalConvolutionSupport s f)
  refine ⟨fun i ↦ a • xs i + b • ys i, ?_, ?_⟩
  · -- The base-point witnesses combine componentwise under the convex weights.
    calc
      ∑ i ∈ s, (a • xs i + b • ys i)
          = (∑ i ∈ s, a • xs i) + ∑ i ∈ s, b • ys i := by
            rw [Finset.sum_add_distrib]
      _ = a • (∑ i ∈ s, xs i) + b • (∑ i ∈ s, ys i) := by
            rw [Finset.smul_sum, Finset.smul_sum]
      _ = a • x + b • y := by
            rw [hxs_sum, hys_sum]
      _ = (a • (x, μ) + b • (y, ν)).1 := by
            rfl
  · -- Convexity holds pointwise on each summand, and the finite upper bounds add componentwise.
    have hpointwise :
        ∀ i ∈ s, f i (a • xs i + b • ys i) ≤ a • f i (xs i) + b • f i (ys i) := by
      intro i hi
      simpa using (hf_convex i hi).2 (by simp) (by simp) ha hb hab
    have hsum_le :
        ∑ i ∈ s, f i (a • xs i + b • ys i) ≤
          ∑ i ∈ s, (a • f i (xs i) + b • f i (ys i)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hpointwise i hi
    calc
      ∑ i ∈ s, f i (a • xs i + b • ys i)
          ≤ ∑ i ∈ s, (a • f i (xs i) + b • f i (ys i)) := hsum_le
      _ = a • (∑ i ∈ s, f i (xs i)) +
            b • (∑ i ∈ s, f i (ys i)) := by
            rw [Finset.sum_add_distrib]
            rw [sum_smul_withTopBot (s := s) (a := a) ha0 (g := fun i ↦ f i (xs i)),
              sum_smul_withTopBot (s := s) (a := b) hb0 (g := fun i ↦ f i (ys i))]
      _ ≤ a • (μ : WithTopBot 𝕜) + b • (ν : WithTopBot 𝕜) := by
            exact add_le_add
              (smul_le_smul_coe_of_le_coe ha hxs_le)
              (smul_le_smul_coe_of_le_coe hb hys_le)
      _ = ((a * μ + b * ν : 𝕜) : WithTopBot 𝕜) := by
            change
              (a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜) +
                  (b : WithTopBot 𝕜) * (ν : WithTopBot 𝕜) = _
            simp [WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul]
      _ = (a • (x, μ) + b • (y, ν)).2 := by
            simp [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]

section FintypeFamily

variable [Fintype ι]

/-- If each summand of a finite family is convex, then the `Fintype` support owner
`finiteInfimalConvolutionSupport` is convex. -/
theorem convex_finiteInfimalConvolutionSupport
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i, ConvexOn 𝕜 (Set.univ : Set E) (f i)) :
    Convex 𝕜 (finiteInfimalConvolutionSupport f) := by
  classical
  simpa [finiteInfimalConvolutionSupport] using
    (convex_finsetInfimalConvolutionSupport (s := (Finset.univ : Finset ι)) f
      (fun i _ ↦ hf_convex i))

end FintypeFamily

end Convexity

section Binary

variable {E : Type u}
variable {α : Type w}
variable [ConditionallyCompleteLattice α] [AddCommMonoid α] [AddCommMonoid E]

/-- Helper for Text 5.4.1: `Fin 2` decompositions are exactly binary decomposition pairs. -/
private theorem fin_two_decomposition_set_eq_binary
    (f : Fin 2 → E → WithTopBot α) (x : E) :
    {r : WithTopBot α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧ r = ∑ i, f i (xs i)} =
      (fun p : E × E ↦ f 0 p.1 + f 1 p.2) '' {p : E × E | p.1 + p.2 = x} := by
  ext r
  constructor
  · rintro ⟨xs, hsum, hr⟩
    refine ⟨(xs 0, xs 1), ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hsum
    · simpa [Fin.sum_univ_two] using hr.symm
  · rintro ⟨p, hp, hr⟩
    refine ⟨![p.1, p.2], ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hp
    · simpa [Fin.sum_univ_two] using hr.symm

-- Proof sketch: compare the two owner decomposition formulas
-- `finiteInfimalConvolution_eq_sInf_decompositions` and
-- `infimal_convolution_eq_sInf_decompositions`. For `Fin 2`, every family decomposition `xs` is
-- exactly a pair `(xs 0, xs 1)`, and `Fin.sum_univ_two` rewrites both the ambient vector sum and
-- the corresponding `WithTopBot α` sum into the binary decomposition formula from Text 5.4.0.
/-- The finite-family construction specializes to the binary infimal convolution on `Fin 2`. -/
theorem finiteInfimalConvolution_two_eq_infimal_convolution
    (f : Fin 2 → E → WithTopBot α) (hf_ne_bot : ∀ i x, f i x ≠ ⊥) :
    finiteInfimalConvolution f = f 0 □ f 1 := by
  funext x
  -- Compare the guarded finite-family decomposition formula with the binary owner formula.
  calc
    finiteInfimalConvolution f x
        = sInf {r : WithTopBot α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
            r = ∑ i, f i (xs i)} :=
          finiteInfimalConvolution_eq_sInf_decompositions f hf_ne_bot x
    _ = sInf ((fun p : E × E ↦ f 0 p.1 + f 1 p.2) '' {p : E × E | p.1 + p.2 = x}) := by
          rw [fin_two_decomposition_set_eq_binary]
    _ = (f 0 □ f 1) x := by
          symm
          exact infimal_convolution_eq_sInf_decompositions (f 0) (f 1) x

/-- Source-facing binary specialization: the `Fintype` finite-family owner on the canonical pair
surface `![f, g]` is exactly `f □ g`. -/
theorem finiteInfimalConvolution_pair_eq_infimal_convolution
    (f g : E → WithTopBot α) (hf_ne_bot : ∀ x, f x ≠ ⊥) (hg_ne_bot : ∀ x, g x ≠ ⊥) :
    finiteInfimalConvolution (![f, g] : Fin 2 → E → WithTopBot α) = f □ g := by
  simpa using finiteInfimalConvolution_two_eq_infimal_convolution
    (f := (![f, g] : Fin 2 → E → WithTopBot α))
    (hf_ne_bot := Fin.forall_fin_two.2 ⟨hf_ne_bot, hg_ne_bot⟩)

end Binary
