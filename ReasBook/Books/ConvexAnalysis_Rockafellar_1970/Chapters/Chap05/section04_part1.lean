import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_4_0 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}

open Function
open scoped Pointwise

/-- Helper for Text 5.4.0: the vertical infimum of a finite-height epigraph set is the infimum of
the scalar heights above each base point. -/
noncomputable def epigraphVerticalInfimum [ConditionallyCompleteLattice 𝕜]
    (F : Set (E × 𝕜)) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F})

local notation "verticalInfimum" => epigraphVerticalInfimum

/-- Helper for Text 5.4.0: every point of a finite-height epigraph set gives an upper bound on the
corresponding vertical infimum. -/
theorem epigraphVerticalInfimum_le_of_mem [ConditionallyCompleteLattice 𝕜]
    {F : Set (E × 𝕜)} {x : E} {μ : 𝕜} (h : (x, μ) ∈ F) :
    verticalInfimum F x ≤ μ := by
  exact sInf_le ⟨μ, h, rfl⟩

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item introduces infimal convolution through decomposition infimums; the
  source-facing owner below keeps that operation while exposing only the minimal additive
  decomposition data needed for the construction itself.
- `core/canonical`: the chapter owner abstraction for infimums of vertical fibers is
  `Function.verticalInfimum`, and the binary infimal convolution is canonically the vertical
  infimum of the Minkowski sum of the two scalar epigraph bridge sets.
- `bridge/view`: under additive-group structure on the domain, the one-parameter bridge
  `⨅ y, f y + g (-y + x)` is obtained from the decomposition owner by the change of variables
  `(y, -y + x)`; under additive-commutative-group structure this specializes to the textbook
  surface `⨅ y, f y + g (x - y)`.
- Primitive data vs derived API: the binary owner `infimal_convolution f g` is primitive at the
  decomposition-set layer; the vertical-infimum bridge uses no-`⊥` guards
  `∀ x, f x ≠ ⊥` and `∀ x, g x ≠ ⊥`; the one-parameter bridge is derived API under additive-group
  structure, and the subtraction surface is the commutative specialization.
- Domain-style sampling used here: the chapter owner `Function.verticalInfimum`, its companion
  theorem `Function.verticalInfimum_eq_sInf`, pointwise Minkowski addition on subsets of `E × 𝕜`,
  and the analogous one-parameter infimum pattern `Metric.infDist_eq_iInf`.
- The textbook's proper-convex hypotheses govern the intended applications of this operation, but
  they are not part of the primitive data needed to define it.
- Ambient minimization: the primitive owner and the decomposition formula use only additive
  structure on the domain together with additive structure and `InfSet` on the scalar codomain;
  the epigraph bridge additionally uses ordered-additive monotonicity plus conditional
  completeness on that codomain, and the one-parameter bridge additionally uses additive-group
  structure on the domain (with the subtraction form using commutativity). Later concrete
  applications therefore reuse this owner by specialization rather than by a parallel coordinate
  model.
- Layer target: `source-facing` for `infimal_convolution` and its decomposition formula,
  `core/canonical` for the vertical-infimum owner comparison, and `bridge/view` for the
  additive-group one-parameter formula plus its subtraction-based commutative specialization.
-/

/-- The decomposition-value owner at `x`: all values `f x₁ + g x₂` coming from additive
decompositions `x₁ + x₂ = x`. -/
def infimalConvolutionDecompositionValues [Add E] [Add 𝕜]
    (f g : E → 𝕜) (x : E) : Set 𝕜 :=
  (fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x}

/-- Coercion-clean bridge: the decomposition-value owner is the image of the additive decomposition
set under `(x₁, x₂) ↦ f x₁ + g x₂`. -/
theorem infimalConvolutionDecompositionValues_eq_image [Add E] [Add 𝕜]
    (f g : E → 𝕜) (x : E) :
    infimalConvolutionDecompositionValues f g x =
      (fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x} := rfl

/-- Text 5.4.0: the infimal convolution of two codomain-valued functions sends `x` to the infimum
of `f x₁ + g x₂` over all decompositions `x₁ + x₂ = x`. The owner construction itself depends only
on additive structure of the domain, additive structure of the codomain, and its `InfSet`
structure. -/
def infimal_convolution [Add E] [InfSet 𝕜] [Add 𝕜] (f g : E → 𝕜) : E → 𝕜 :=
  fun x ↦ sInf (infimalConvolutionDecompositionValues f g x)

infixl:70 " □ " => infimal_convolution

section OrderedCodomain

variable [Add E]
variable [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid 𝕜] [IsOrderedAddMonoid 𝕜]

/-- Helper for Text 5.4.0: a point of the Minkowski sum `epi f + epi g` yields an additive
decomposition of the base point together with the corresponding decomposition-value upper bound. -/
lemma decomposition_le_of_mem_epi_add
    {f g : E → WithTopBot 𝕜} {x : E} {μ : 𝕜}
    (h : (x, μ) ∈ epi f + epi g) :
    ∃ x₁ x₂, x₁ + x₂ = x ∧ f x₁ + g x₂ ≤ μ := by
  -- Expand the Minkowski-sum witness into two epigraph points and compare their heights.
  rcases Set.mem_add.mp h with ⟨⟨x₁, μ₁⟩, h₁, ⟨x₂, μ₂⟩, h₂, hsum⟩
  have hsumx : x₁ + x₂ = x := by
    simpa using congrArg Prod.fst hsum
  have hsummu : (((μ₁ + μ₂ : 𝕜) : WithTopBot 𝕜)) = μ := by
    exact congrArg (fun t : 𝕜 ↦ (t : WithTopBot 𝕜)) (congrArg Prod.snd hsum)
  have h₁_le : f x₁ ≤ μ₁ := by
    simpa using h₁
  have h₂_le : g x₂ ≤ μ₂ := by
    simpa using h₂
  refine ⟨x₁, x₂, hsumx, ?_⟩
  calc
    f x₁ + g x₂ ≤ μ₁ + μ₂ := add_le_add h₁_le h₂_le
    _ = μ := hsummu

/-- Helper for Text 5.4.0: under the same pointwise no-`⊥` guard used by later epigraph-based
arguments, the owner formula for `f □ g` is the decomposition infimum over `x₁ + x₂ = x`. -/
theorem infimal_convolution_eq_verticalInfimum_epigraph_add
    (f g : E → WithTopBot 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    (f □ g) =
      fun x ↦ sInf ((fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x}) := by
  let _ := (inferInstance : IsOrderedAddMonoid 𝕜)
  let _ := hf_ne_bot
  let _ := hg_ne_bot
  funext x
  simp [infimal_convolution, infimalConvolutionDecompositionValues]

end OrderedCodomain

/-- Owner-level decomposition formula: evaluating `infimal_convolution` at `x` is the infimum of
its decomposition-value owner `infimalConvolutionDecompositionValues f g x`. -/
theorem infimal_convolution_eq_sInf_decompositionValues
    [Add E] [InfSet 𝕜] [Add 𝕜]
    (f g : E → 𝕜) (x : E) :
    (f □ g) x = sInf (infimalConvolutionDecompositionValues f g x) := rfl

/-- Source-facing bridge form of the decomposition formula:
`(f □ g) x` is the infimum of `f x₁ + g x₂` over all decompositions `x₁ + x₂ = x`. -/
theorem infimal_convolution_eq_sInf_decompositions
    [Add E] [InfSet 𝕜] [Add 𝕜]
    (f g : E → 𝕜) (x : E) :
    (f □ g) x =
      sInf ((fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x}) := by
  simpa [infimalConvolutionDecompositionValues] using
    (infimal_convolution_eq_sInf_decompositionValues (f := f) (g := g) (x := x))

section LeftSubFormula

variable [AddGroup E]

/-- Helper for Text 5.4.0: the additive decomposition values at `x` are exactly the range of the
one-parameter family `y ↦ f y + g (-y + x)`. -/
lemma infimalConvolutionDecompositionValues_eq_range_neg_add
    [Add 𝕜] (f g : E → 𝕜) (x : E) :
    infimalConvolutionDecompositionValues f g x =
      Set.range (fun y : E ↦ f y + g (-y + x)) := by
  -- Reindex decomposition pairs `(x₁, x₂)` by the first coordinate `y = x₁`.
  rw [infimalConvolutionDecompositionValues_eq_image]
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.1, ?_⟩
    have hp₂ : p.2 = -p.1 + x := by
      simpa [add_assoc] using congrArg (fun t : E ↦ -p.1 + t) hp
    simp [hp₂]
  · rintro ⟨y, rfl⟩
    refine ⟨(y, -y + x), ?_, rfl⟩
    simp

-- Proof sketch: compare the decomposition-set owner formula
-- `infimal_convolution_eq_sInf_decompositions` with the one-parameter family indexed by `y : E`.
-- The substitutions `y ↦ (y, -y + x)` and `(x₁, x₂) ↦ x₁` identify the decomposition set
-- `{(x₁, x₂) | x₁ + x₂ = x}` with `E` without using commutativity.
/-- Under additive-group structure on the domain, evaluating the infimal convolution at `x` gives
the one-parameter infimum `⨅ y, f y + g (-y + x)`. -/
theorem infimal_convolution_apply_neg_add
    [InfSet 𝕜] [Add 𝕜]
    (f g : E → 𝕜) (x : E) :
    (f □ g) x = ⨅ y : E, f y + g (-y + x) := by
  -- Rewrite the decomposition owner by the textbook change of variables `x₂ = -y + x`.
  rw [infimal_convolution_eq_sInf_decompositionValues,
    infimalConvolutionDecompositionValues_eq_range_neg_add]
  rfl

end LeftSubFormula

section SubtractionFormula

variable [AddCommGroup E]

-- Proof sketch: compare the decomposition-set owner formula
-- `infimal_convolution_eq_sInf_decompositions` with the one-parameter family indexed by `y : E`.
-- The substitutions `y ↦ (y, x - y)` and `(x₁, x₂) ↦ x₁` identify the decomposition set
-- `{(x₁, x₂) | x₁ + x₂ = x}` with `E`; this uses commutativity to recover `x₂ = x - x₁`.
/-- Under additive-commutative-group structure on the domain, evaluating the infimal convolution
at `x` gives
the textbook one-parameter infimum `⨅ y, f y + g (x - y)`. -/
@[simp] theorem infimal_convolution_apply
    [InfSet 𝕜] [Add 𝕜]
    (f g : E → 𝕜) (x : E) :
    (f □ g) x = ⨅ y : E, f y + g (x - y) := by
  refine (infimal_convolution_apply_neg_add (f := f) (g := g) (x := x)).trans ?_
  refine iInf_congr fun y ↦ ?_
  refine congrArg (fun t : E => f y + g t) ?_
  simpa [sub_eq_add_neg] using (add_comm (-y) x)

end SubtractionFormula

end

/-! ### Text_5_4_1 (from Chap01) -/
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
      simp
  | @insert i s hi ih =>
      -- Peel off one summand and use the `WithTopBot` `add_eq_bot` characterization.
      have hi_ne_bot : g i ≠ ⊥ := hg i (by simp)
      have hs_ne_bot : (∑ j ∈ s, g j) ≠ ⊥ := by
        refine ih ?_
        intro j hj
        exact hg j (by simp [hj])
      simp [Finset.sum_insert, hi, WithTopBot.add_eq_bot_iff, hi_ne_bot, hs_ne_bot]

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
            · exact ⟨a, le_rfl, rfl⟩
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
  · -- Every finite upper bound in `U` dominates the exact decomposition-value infimum.
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨μ, ⟨xs, hsum, hle⟩, rfl⟩
    have hmem : (∑ i ∈ s, f i (xs i)) ∈ D := by
      exact ⟨xs, hsum, rfl⟩
    exact le_trans (sInf_le hmem) hle
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
    exact le_trans hsInf_slice (upper_height_sInf_eq_of_ne_bot hsum_ne_bot)

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
variable [AddCommMonoid E] [DistribMulAction 𝕜 E]

/-- Helper for Text 5.4.1: the scalar action on `WithTopBot 𝕜` is multiplication by the finite
scalar branch. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Helper for Text 5.4.1: left multiplication by a nonnegative finite scalar is monotone on
`WithTopBot 𝕜`. -/
private theorem mul_le_mul_left_coe_withTopBot {a : 𝕜} (ha : 0 ≤ a) {u v : WithTopBot 𝕜}
    (h : u ≤ v) :
    (a : WithTopBot 𝕜) * u ≤ (a : WithTopBot 𝕜) * v := by
  -- Reduce first along the outer `WithTop`; the finite branch then drops to monotonicity on
  -- `WithBot 𝕜`.
  induction v using WithTop.recTopCoe with
  | top =>
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha0' : (a : WithTopBot 𝕜) ≠ 0 := by
          exact_mod_cast ha0
        rw [WithTop.mul_top ha0']
        exact le_top
  | coe v =>
      induction u using WithTop.recTopCoe with
      | top =>
          exfalso
          simp at h
      | coe u =>
          have huv : u ≤ v := WithTop.coe_le_coe.mp h
          have ha' : (0 : WithBot 𝕜) ≤ ((a : 𝕜) : WithBot 𝕜) := by
            exact WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

/-- Helper for Text 5.4.1: a nonnegative scalar preserves an upper bound by a finite height in
`WithTopBot 𝕜`. -/
private theorem smul_le_smul_coe_of_le_coe {a μ : 𝕜} (ha : 0 ≤ a) {z : WithTopBot 𝕜}
    (hz : z ≤ (μ : WithTopBot 𝕜)) :
    a • z ≤ a • (μ : WithTopBot 𝕜) := by
  -- Package the codomain transport through the monotonicity lemma for left multiplication.
  change ((a : WithTopBot 𝕜) * z ≤ ((a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜)))
  exact mul_le_mul_left_coe_withTopBot ha hz

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
      simpa using (hf_convex i hi) (by simp) (by simp) ha hb hab
    have hsum_le :
        ∑ i ∈ s, f i (a • xs i + b • ys i) ≤
          ∑ i ∈ s, (a • f i (xs i) + b • f i (ys i)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hpointwise i hi
    calc
      ∑ i ∈ s, f i (a • xs i + b • ys i)
          ≤ ∑ i ∈ s, (a • f i (xs i) + b • f i (ys i)) := hsum_le
      _ = (a : WithTopBot 𝕜) * (∑ i ∈ s, f i (xs i)) +
            (b : WithTopBot 𝕜) * (∑ i ∈ s, f i (ys i)) := by
            simp [instSMulWithTopBot, Finset.sum_add_distrib, Finset.mul_sum, add_assoc,
              add_left_comm, add_comm]
      _ ≤ (a : WithTopBot 𝕜) * μ + (b : WithTopBot 𝕜) * ν := by
            exact add_le_add
              (smul_le_smul_coe_of_le_coe ha hxs_le)
              (smul_le_smul_coe_of_le_coe hb hys_le)
      _ = ((a * μ + b * ν : 𝕜) : WithTopBot 𝕜) := by
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
    · simpa [Fin.sum_univ_two] using hr
  · rintro ⟨p, hp, hr⟩
    refine ⟨![p.1, p.2], ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hp
    · simpa [Fin.sum_univ_two] using hr

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

/-! ### Text_5_4_1_1 (from Chap01) -/
noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

section PointIndicatorNotation

/-- Point-indicator notation surface specialized from the set-indicator owner. -/
scoped[Rockafellar] notation:70 "δp" "(" x " | " a ")" =>
  δ(x | ({a} : Set _))

end PointIndicatorNotation

section

variable {E : Type u} {𝕜 : Type v}
variable [AddGroup E]
variable [ConditionallyCompleteLattice 𝕜] [AddZeroClass 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.1 identifies the infimal convolution of `f` with the singleton
  indicator at `a` as the translate `x ↦ f (x - a)`.
- `core/canonical`: the owner abstractions are the chapter binary infimal convolution `□` from
  `Text_5_4_0`, specifically its additive-group bridge `infimal_convolution_apply_neg_add`, and
  the chapter indicator `δ(· | C)` from `Defintion_4_8_1`.
- `bridge/view`: the textbook point-indicator is exposed as notation `δp(· | a)`, a thin view of
  the singleton-set indicator owner `δ(· | ({a} : Set E))`.
- Primitive data vs derived API: the primitive data are `f` and `a`; the point `x` appears only
  when evaluating the owner-level identity at a point.
- Ambient minimization: the statement only uses additive-group structure on the domain and the
  additive conditional-completeness required by `□`. Because the project codomain is
  `WithBotTop 𝕜`, the textbook extended-real condition that `f` never takes `-∞` becomes the
  explicit guard `∀ y, f y ≠ ⊥`, which is used through the canonical additive rule
  `WithBotTop.add_top_of_ne_bot`.
-/

-- Proof sketch: expand `(f □ δp(· | a)) x` with
-- `infimal_convolution_apply_neg_add`. The singleton indicator is `0` exactly when `-y + x = a`,
-- i.e. `y = x - a`, and is `⊤` otherwise.
-- The non-`⊥` guard on `f` turns every off-singleton summand into `⊤`, so the infimum reduces to
-- the unique admissible value `f (x - a)`.
/-- Text 5.4.1.1: infimal convolution with the singleton indicator at `a` translates `f` by `a`;
in the chapter codomain `WithBotTop 𝕜`, this requires the source-faithful exclusion of `⊥`
values from `f`. The canonical owner-level surface is a function equality. -/
theorem infimal_convolution_indicator_singleton_eq_sub
    (f : E → WithBotTop 𝕜) (a : E) (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    (f □ (δp(· | a))) = fun x ↦ f (x - a) := by
  classical
  funext x
  rw [infimal_convolution_apply_neg_add]
  calc
    (⨅ y : E, f y + δp(-y + x | a)) =
        ⨅ y : E, if -y + x = a then f y else ⊤ := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : -y + x = a
          · simp [hy]
          · have hy' : -y + x ∉ ({a} : Set E) := by
                simpa [Set.mem_singleton_iff] using hy
            simp [hy, hy', WithBotTop.add_top_of_ne_bot (hf_ne_bot y)]
    _ = ⨅ y : E, ⨅ (_ : -y + x = a), f y := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : -y + x = a
          · simp [hy]
          · simp [hy]
    _ = ⨅ y : {y : E // -y + x = a}, f (y : E) := by
          rw [iInf_subtype']
    _ = f (x - a) := by
          let y0 : {y : E // -y + x = a} := ⟨x - a, by
            simp [sub_eq_add_neg, add_assoc]⟩
          have hsub : Subsingleton {y : E // -y + x = a} := by
            constructor
            intro y₁ y₂
            apply Subtype.ext
            have hy₁ : (y₁ : E) = x - a := by
              rw [eq_sub_iff_add_eq]
              simpa [add_assoc] using congrArg (fun t ↦ (y₁ : E) + t) y₁.property.symm
            have hy₂ : (y₂ : E) = x - a := by
              rw [eq_sub_iff_add_eq]
              simpa [add_assoc] using congrArg (fun t ↦ (y₂ : E) + t) y₂.property.symm
            exact hy₁.trans hy₂.symm
          letI : Unique {y : E // -y + x = a} := ⟨⟨y0⟩, fun y ↦ hsub.elim y y0⟩
          have hdefault : ((default : {y : E // -y + x = a}) : E) = x - a := by
            exact congrArg Subtype.val (hsub.elim default y0)
          simpa using congrArg f hdefault

end

/-! ### Text_5_4_1_2 (from Chap01) -/
noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

section

variable {E : Type u} {𝕜 : Type v}
variable [AddGroup E]
variable [ConditionallyCompleteLattice 𝕜] [AddZeroClass 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.2 rewrites the binary infimal convolution `(f □ g) x` by
  reflecting `f` to `y ↦ f (-y)` and inserting the singleton indicator at `x`.
- `core/canonical`: the owner abstractions are the chapter binary infimal convolution
  `infimal_convolution` / `□` from `Text_5_4_0` and the indicator owner `indicator` from
  `Defintion_4_8_1`.
- `bridge/view`: the singleton indicator `δ[𝕜](· | ({x} : Set E))` isolates the affine constraint
  hidden in the textbook's iterated-infimum formula, and the reflection is kept directly as the
  explicit function `fun y ↦ f (-y)` rather than as a second owner wrapper.
- Primitive data vs derived API: the primitive data are the functions `f`, `g`, and the point
  `x`; the reflected inner convolution is the source-facing bridge used to restate `(f □ g) x`.
- Ambient minimization: the statement uses only additive-group structure on the domain and the
  ordered additive structure already used by `infimal_convolution`. In the project's
  `WithBotTop 𝕜` codomain, if `f` attains `⊥` then both sides of the displayed identity collapse
  to `⊥`, so no extra owner-level guard is needed. The outer and inner rewrites both use the
  noncommutative owner bridge `infimal_convolution_apply_neg_add`, so no domain or codomain
  commutativity assumption remains.
- Reuse check: the singleton-indicator collapse is already owned by
  `infimal_convolution_indicator_singleton_eq_sub` from `Text_5_4_1_1`, so the reflected-inner
  step below should reuse that theorem rather than duplicating its subtype argument.
-/

-- Proof sketch: first split on whether `f` attains `⊥`. If it does, then both outer infima are
-- already `⊥` by evaluating at that witness through `infimal_convolution_apply_neg_add`.
-- Otherwise expand the outer and inner convolutions by the same owner theorem. For the inner
-- term, the singleton indicator forces the unique decomposition `-y + z = x`, i.e.
-- `y = z + -x`, so the reflected summand becomes `f (x + -z)`.
/-- Text 5.4.1.2: if `h y = f (-y)`, then the binary infimal convolution `(f □ g) x` can be
rewritten as the infimum over `z` of `(h □ δ[𝕜](· | ({x} : Set E))) z + g z`. In the project's
`WithBotTop 𝕜` codomain this remains valid without extra hypotheses: if `f` takes the value `⊥`,
then both sides collapse to `⊥`. -/
theorem infimal_convolution_eq_iInf_add_reflection_infimal_convolution_singleton_indicator
    (f g : E → WithBotTop 𝕜)
    (x : E) :
    (f □ g) x =
      ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
  classical
  by_cases hbot : ∃ y : E, f y = ⊥
  · rcases hbot with ⟨y0, hy0⟩
    have hleft : (f □ g) x = ⊥ := by
      rw [infimal_convolution_apply_neg_add]
      exact bot_unique <| by
        simpa [hy0] using (iInf_le (fun y : E ↦ f y + g (-y + x)) y0)
    have hinner_bot : ∀ z : E,
        (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) = ⊥ := by
      intro z
      rw [infimal_convolution_apply_neg_add]
      exact bot_unique <| by
        simpa [hy0] using
          (iInf_le (fun y : E ↦ f (-y) + δ[𝕜](-y + z | ({x} : Set E))) (-y0))
    calc
      (f □ g) x = ⊥ := hleft
      _ = ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
            calc
              ⊥ = ⨅ z : E, (⊥ : WithBotTop 𝕜) + g z := by simp
              _ = ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
                    refine iInf_congr fun z ↦ ?_
                    rw [hinner_bot z]
  · have hf_ne_bot : ∀ y : E, f y ≠ ⊥ := by
      intro y hy
      exact hbot ⟨y, hy⟩
    have hinner : ∀ z : E,
        (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) = f (x + -z) := by
      intro z
      simpa [sub_eq_add_neg, neg_add_rev] using
        congrArg (fun h : E → WithBotTop 𝕜 => h z)
          (infimal_convolution_indicator_singleton_eq_sub
            (f := fun y ↦ f (-y))
            (a := x)
            (hf_ne_bot := fun y ↦ hf_ne_bot (-y)))
    calc
      (f □ g) x = ⨅ y : E, f y + g (-y + x) := infimal_convolution_apply_neg_add f g x
      _ = ⨅ z : E, f (x + -z) + g z := by
            let e : E ≃ E :=
              { toFun := fun y ↦ -y + x
                invFun := fun z ↦ x + -z
                left_inv := fun y ↦ by simp [neg_add_rev]
                right_inv := fun z ↦ by simp [neg_add_rev] }
            exact Equiv.iInf_congr e fun y ↦ by
              simp [e, neg_add_rev]
      _ = ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
            refine iInf_congr fun z ↦ ?_
            rw [hinner z]

end

/-! ### Text_5_4_1_3 (from Chap01) -/
open scoped Pointwise
open Function

section

variable {E : Type*} {𝕜 : Type*}
variable [AddCommMonoid 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [Add E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition identifies the effective domain of the infimal convolution
  `f □ g` with the Minkowski sum of the effective domains of `f` and `g`.
- `core/canonical`: the owner abstraction is the chapter declaration `infimal_convolution` from
  `Text_5_4_0`, together with the chapter properness owner `Function.IsProper` from
  `Definition_4_6`.
- `bridge/view`: for `WithBotTop`-valued functions, the textbook domain statement is recovered
  directly from the decomposition owner
  `infimal_convolution_eq_sInf_decompositions`. In this codomain one must stay in the no-`⊥`
  regime: otherwise `⊥ + ⊤ = ⊥`, so finiteness of a decomposition term `f x₁ + g x₂` no longer
  forces finiteness of the summands.
- Domain-style sampling used here: the chapter owner declaration `infimal_convolution`, the domain
  notation `dom(f)`, the properness owner `Function.IsProper`, the companion
  `Function.IsProper.ne_bot`, the owner bridge `infimal_convolution_eq_sInf_decompositions`, the
  additive boundary lemma `WithBotTop.add_ne_top_iff_ne_top₂`, and the canonical Minkowski-sum
  notation on sets.
- Primitive data vs derived API: the owner-level domain identity needs only the pointwise no-`⊥`
  hypotheses `hf_ne_bot` and `hg_ne_bot`; the textbook properness wording is therefore a derived
  companion obtained from `Function.IsProper`.
- Ambient minimization: the statement and proof use only additive structure on
  the domain, together with the ordered-additive codomain structure already required by the owner
  epigraph bridge, so the theorem remains at an abstract additive/order layer.
- Layer targets:
  - `bridge/view`: `infimal_convolution_dom_eq_add` records the exact owner-level
    `WithBotTop` domain formula under the no-`⊥` guard needed to avoid the mixed-infinite
    pathology;
  - `source-facing`: `infimal_convolution_dom_eq_add_of_isProper` recovers the
    textbook properness phrasing from the chapter owner `Function.IsProper`.
-/

-- Route correction: the old epigraph/vertical-infimum proof used the chapter `WithTopBot`
-- projection API, while this item lives in the `WithBotTop` codomain. The proof below stays on
-- `WithBotTop` and follows the textbook decomposition witnesses directly.
/-- Helper for Text 5.4.1.3: a decomposition whose two coordinates lie in the effective domains of
`f` and `g` has finite total value. -/
lemma decomposition_value_lt_top_of_mem_dom
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    {u v : E} (hu : u ∈ dom(f)) (hv : v ∈ dom(g)) :
    f u + g v < (⊤ : WithBotTop 𝕜) := by
  -- Translate domain membership into non-`⊤` facts and combine them through the additive boundary
  -- lemma for `WithBotTop`.
  rw [lt_top_iff_ne_top]
  exact
    (WithBotTop.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot v)).2
      ⟨(lt_top_iff_ne_top.mp hu), (lt_top_iff_ne_top.mp hv)⟩

/-- Helper for Text 5.4.1.3: if `x` is outside `dom(f) + dom(g)`, then every decomposition
`x = u + v` has value `f u + g v = ⊤`. -/
lemma decomposition_value_eq_top_of_not_mem_dom_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    {x u v : E} (huv : u + v = x) (hx : x ∉ dom(f) + dom(g)) :
    f u + g v = (⊤ : WithBotTop 𝕜) := by
  classical
  by_cases hsum : f u + g v = (⊤ : WithBotTop 𝕜)
  · exact hsum
  · -- If the decomposition value were finite, both summands would lie in their own domains and
    -- would therefore produce a forbidden representation of `x`.
    have hparts :=
      (WithBotTop.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot v)).1 hsum
    have hu_dom : u ∈ dom(f) := by
      exact (lt_top_iff_ne_top).2 hparts.1
    have hv_dom : v ∈ dom(g) := by
      exact (lt_top_iff_ne_top).2 hparts.2
    exact False.elim (hx (Set.mem_add.2 ⟨u, hu_dom, v, hv_dom, huv⟩))

/-- Helper for Text 5.4.1.3: every sum of points from `dom(f)` and `dom(g)` lies in
`dom(f □ g)`. -/
lemma add_subset_infimal_convolution_dom
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f) + dom(g) ⊆ dom(f □ g) := by
  intro x hx
  rcases Set.mem_add.1 hx with ⟨u, hu, v, hv, rfl⟩
  -- Use the textbook witness decomposition `u + v = x` inside the defining infimum.
  rw [mem_effectiveDomain, infimal_convolution_eq_sInf_decompositions]
  refine lt_of_le_of_lt ?_ (decomposition_value_lt_top_of_mem_dom f g hf_ne_bot hg_ne_bot hu hv)
  apply sInf_le
  exact ⟨(u, v), by simp, rfl⟩

/-- Helper for Text 5.4.1.3: every point of `dom(f □ g)` admits a decomposition with first
coordinate in `dom(f)` and second coordinate in `dom(g)`. -/
lemma infimal_convolution_dom_subset_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f □ g) ⊆ dom(f) + dom(g) := by
  classical
  intro x hx
  by_contra hx_add
  -- Contrapositively, if `x` is outside the Minkowski sum of the domains, then every
  -- decomposition value in the defining image set is `⊤`, so the infimum itself is `⊤`.
  have hx_value : (f □ g) x < (⊤ : WithBotTop 𝕜) := mem_effectiveDomain.mp hx
  have hsInf_eq_top :
      sInf ((fun p : E × E ↦ f p.1 + g p.2) '' {p : E × E | p.1 + p.2 = x}) =
        (⊤ : WithBotTop 𝕜) := by
    apply le_antisymm le_top
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨⟨u, v⟩, huv, rfl⟩
    simpa using
      (show (⊤ : WithBotTop 𝕜) ≤ f u + g v by
        rw [decomposition_value_eq_top_of_not_mem_dom_add f g hf_ne_bot hg_ne_bot huv hx_add])
  have hx_top : (f □ g) x = (⊤ : WithBotTop 𝕜) := by
    -- Rewrite the infimal convolution into its decomposition infimum and substitute the forced
    -- `⊤` value of that infimum.
    rw [infimal_convolution_eq_sInf_decompositions, hsInf_eq_top]
  exact (lt_top_iff_ne_top.mp hx_value) hx_top

/-- Text 5.4.1.3: the effective domain of the infimal convolution of `f` and `g` is the Minkowski
sum of the effective domains of `f` and `g`. For `WithBotTop`-valued functions this domain formula
is valid under the natural pointwise `⊥`-exclusion hypotheses `f x ≠ ⊥` and `g x ≠ ⊥`. -/
theorem infimal_convolution_dom_eq_add
    (f g : E → WithBotTop 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hg_ne_bot : ∀ x : E, g x ≠ ⊥) :
    dom(f □ g) = dom(f) + dom(g) := by
  -- The two textbook inclusions are proved separately so the main theorem stays at the set level.
  exact Set.Subset.antisymm
    (infimal_convolution_dom_subset_add f g hf_ne_bot hg_ne_bot)
    (add_subset_infimal_convolution_dom f g hf_ne_bot hg_ne_bot)

/-- Properness-form restatement of Text 5.4.1.3. This companion uses the chapter owner
`Function.IsProper` only to recover the pointwise no-`⊥` hypotheses needed by the main theorem
`infimal_convolution_dom_eq_add`. -/
theorem infimal_convolution_dom_eq_add_of_isProper
    (f g : E → WithBotTop 𝕜) (hf : f.IsProper) (hg : g.IsProper) :
    dom(f □ g) = dom(f) + dom(g) := by
  -- Properness is used only to recover the pointwise `≠ ⊥` hypotheses needed above.
  simpa using infimal_convolution_dom_eq_add f g hf.ne_bot hg.ne_bot

end

/-! ### Text_5_4_1_4 (from Chap01) -/
noncomputable section

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

section

variable {E : Type*} [SeminormedAddCommGroup E]

open Metric

scoped[Rockafellar] notation "d(" x ", " C ")" => Metric.infEDist x C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.4 specializes infimal convolution to the Euclidean norm and the
  `0/+∞` indicator of a set `C`, obtaining the distance-to-set function.
- `core/canonical`: the owner abstractions are the chapter operation `infimal_convolution` from
  `Text_5_4_0`, the chapter indicator owner `indicator` from `Defintion_4_8_1`, and the
  canonical distance owner `Metric.infEDist` viewed through the chapter notation `d(·, C)`.
- `bridge/view`: `d(·, C)` is notation for the canonical owner `Metric.infEDist`; this concrete
  owner is defined locally here because the dedicated distance file is currently unavailable as a
  compiled dependency.
- Primitive data vs derived API: the primitive inputs are the set `C` and the point `x`; the
  distance identity is the derived theorem.

Domain-style sampling used here:
- the chapter owner declaration `infimal_convolution`;
- the chapter owner declaration `indicator`;
- the chapter distance owner notation `d(·, C)` with its bridge to `Metric.infEDist`;
- the `dist`-bridge theorem `distanceToSet_eq_iInf_dist`;
- the canonical norm-metric bridge `dist_eq_norm`.

The source phrases the statement for a convex set `C`, but the identity itself depends on neither
convexity nor nonemptiness, so those hypotheses are removed as mathematically redundant.
- Ambient minimization: although the source states the formula on `ℝ^n`, the canonical owners used
  in the statement and proof already live on any seminormed additive commutative group, so the
  public theorem is stated at that intrinsic level rather than on a fixed coordinate model.
-/

/-- Helper for Text 5.4.1.4: the chapter distance owner is the subtype-indexed infimum of the
pointwise distances, viewed in `EReal`. -/
theorem infEDist_eq_iInf_dist_withTopBot {C : Set E} (x : E) :
    (d(x, C) : EReal) = ⨅ z : C, (dist x z : EReal) := by
  have hE' :
      (d(x, C) : EReal) = ⨅ z : C, (dist x z : EReal) := by
    -- Rewrite the edistance owner as a subtype-indexed infimum before coercing it to `EReal`.
    rw [Metric.infEDist, iInf_subtype']
    let f : C → ENNReal := fun z ↦ edist x z
    have hmono : Monotone ((↑) : ENNReal → EReal) :=
      EReal.coe_ennreal_strictMono.monotone
    -- Move the coercion through the infimum and then rewrite each edistance term via `dist`.
    have hmap :
        ((⨅ z, f z : ENNReal) : EReal) = ⨅ z, ((f z : ENNReal) : EReal) :=
      hmono.map_iInf_of_continuousAt continuous_coe_ennreal_ereal.continuousAt rfl
    calc
      ((⨅ z, f z : ENNReal) : EReal) = ⨅ z : C, ((f z : ENNReal) : EReal) := hmap
      _ = ⨅ z : C, (dist x z : EReal) := by
        exact iInf_congr fun z : C ↦
          (show ((f z : ENNReal) : EReal) = (dist x z : EReal) from by
            simpa [f, dist_edist] using (EReal.coe_ennreal_toReal (edist_ne_top x (z : E))).symm)
  exact hE'

/-- Helper for Text 5.4.1.4: outside the set, the indicator term is `⊤` when viewed in `EReal`. -/
theorem indicator_of_notMem_toEReal {C : Set E} {z : E} (hz : z ∉ C) :
    (show EReal from (δ[ℝ](z | C))) = (⊤ : EReal) := by
  -- Transport the indicator's off-set branch to the `EReal` codomain used in this file.
  simpa [indicator_def, hz]

/-- Helper for Text 5.4.1.4: restricting the indicator branch turns the ambient infimum into the
subtype infimum over the feasible shifts. -/
theorem indicator_shift_iInf_eq_subtype_iInf {C : Set E} (x : E) :
    (⨅ y : E, ((‖y‖ : ℝ) : EReal) + (show EReal from (δ[ℝ](x - y | C)))) =
      ⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal) := by
  -- Split on whether the indicator is finite and collapse the `+∞` branch.
  calc
    (⨅ y : E, ((‖y‖ : ℝ) : EReal) + (show EReal from (δ[ℝ](x - y | C)))) =
        ⨅ y : E, if x - y ∈ C then ((‖y‖ : ℝ) : EReal) else (⊤ : EReal) := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : x - y ∈ C
          · -- On feasible shifts, the indicator vanishes and the branch keeps the norm term.
            rw [if_pos hy, indicator_of_mem (α := ℝ) (C := C) hy]
            exact add_zero (((‖y‖ : ℝ) : EReal))
          · -- Outside the feasible set, the indicator becomes `⊤`, which absorbs finite addition.
            rw [if_neg hy]
            rw [indicator_of_notMem_toEReal (C := C) (z := x - y) hy]
            simp
    _ = ⨅ y : E, ⨅ (_ : x - y ∈ C), (((‖y‖ : ℝ) : EReal)) := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : x - y ∈ C
          · simp [hy]
          · simp [hy]
    _ = ⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal) := by
          rw [iInf_subtype']

/-- Helper for Text 5.4.1.4: subtracting a feasible shift from `x` lands in the target set. -/
theorem sub_mem_equiv_set_member_toFun_mem {C : Set E} (x : E)
    (y : {y : E // x - y ∈ C}) :
    x - (y : E) ∈ C :=
  y.property

/-- Helper for Text 5.4.1.4: subtracting a point of `C` from `x` produces a feasible shift. -/
theorem sub_mem_equiv_set_member_inv_mem {C : Set E} (x : E) (z : C) :
    x - (z : E) ∈ {y : E | x - y ∈ C} := by
  -- Rewrite the double subtraction so the goal becomes the stored membership proof of `z`.
  simp [sub_sub_cancel, z.property]

/-- Helper for Text 5.4.1.4: applying the subtraction reindexing twice recovers a feasible shift. -/
theorem sub_mem_equiv_set_member_left_inv_val {C : Set E} (x : E)
    (y : {y : E // x - y ∈ C}) :
    x - (x - (y : E)) = (y : E) := by
  -- Cancel the two subtractions to recover the original shift variable.
  simp [sub_sub_cancel]

/-- Helper for Text 5.4.1.4: applying the inverse subtraction reindexing twice recovers a point
of `C`. -/
theorem sub_mem_equiv_set_member_right_inv_val {C : Set E} (x : E) (z : C) :
    x - (x - (z : E)) = (z : E) := by
  -- The same cancellation now shows the reindexed point of `C` is unchanged.
  simp [sub_sub_cancel]

/-- Helper for Text 5.4.1.4: subtraction identifies the feasible shifts with the set itself. -/
def sub_mem_equiv_set_member {C : Set E} (x : E) : {y : E // x - y ∈ C} ≃ C :=
  { toFun := fun y ↦ ⟨x - y, y.property⟩
    invFun := fun z ↦ ⟨x - z, sub_mem_equiv_set_member_inv_mem (C := C) x z⟩
    left_inv := fun y ↦ Subtype.ext (sub_mem_equiv_set_member_left_inv_val (C := C) x y)
    right_inv := fun z ↦ Subtype.ext (sub_mem_equiv_set_member_right_inv_val (C := C) x z) }

/-- Helper for Text 5.4.1.4: after reindexing by subtraction, the constrained norm infimum is the
set-indexed distance infimum. -/
theorem subtype_iInf_norm_eq_set_iInf_dist {C : Set E} (x : E) :
    (⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal)) =
      ⨅ z : C, (dist x z : EReal) := by
  let e : {y : E // x - y ∈ C} ≃ C := sub_mem_equiv_set_member (C := C) x
  -- Reindex the subtype infimum by the subtraction equivalence.
  refine Equiv.iInf_congr e ?_
  intro y
  -- The reindexed norm is exactly the distance `dist x z`.
  show (dist x (e y) : EReal) = ((‖(y : E)‖ : ℝ) : EReal)
  simp [e, sub_mem_equiv_set_member]

-- Proof sketch: rewrite the infimal convolution with the inline `0/+∞` indicator as the infimum
-- of the norms `‖x - z‖` over `z ∈ C`. Then identify that subtype-indexed infimum directly with
-- the Chapter 1 `dist`-bridge theorem `distanceToSet_eq_iInf_dist`, keeping the theorem surface
-- on the chapter codomain owner `EReal`.
/-- Owner-facing form of Text 5.4.1.4: taking `f` to be the norm and `g` to be the `0/+∞`
indicator of a set `C`, the infimal convolution `f □ g` is exactly the chapter distance function
`x ↦ d(x, C)`.
The source states this on `ℝ^n`, but the canonical chapter statement is valid on any
seminormed additive commutative group. The source's convexity and nonemptiness assumptions on
`C` are redundant for this identity and are omitted. -/
theorem infimal_convolution_norm_indicator_eq_distanceToSet
    {C : Set E} :
    ((fun y : E ↦ ((‖y‖ : ℝ) : EReal)) □
      (fun z ↦ (show EReal from (δ[ℝ](z | C))))) =
      fun x ↦ (d(x, C) : EReal) := by
  funext x
  -- Rewrite the infimal convolution into the textbook one-parameter infimum.
  rw [infimal_convolution_apply]
  -- Restrict the ambient infimum to the feasible shifts where the indicator is zero.
  rw [indicator_shift_iInf_eq_subtype_iInf (C := C) (x := x)]
  -- Reindex the feasible shifts by points of `C` and rewrite norms as distances.
  rw [subtype_iInf_norm_eq_set_iInf_dist (C := C) (x := x)]
  -- Identify the resulting infimum with the canonical distance owner.
  exact (infEDist_eq_iInf_dist_withTopBot (C := C) x).symm

end

/-! ### Text_5_4_1_5 (from Chap01) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.5 asserts that for a convex set `C`, the distance-to-set function
  `x ↦ d(x, C)` is convex.
- `core/canonical`: the owner abstractions are the chapter distance notation `d(x, C)` from
  `Defintion_4_8_3`, the previous identity
  `infimal_convolution_norm_indicator_eq_distanceToSet` from `Text_5_4_1_4`, the norm-convexity
  theorem `Function.isConvex_norm`, the indicator bridge `indicator_isConvex_iff`, and the
  binary infimal-convolution convexity theorem `Function.IsConvex.infimal_convolution`.
- `bridge/view`: the corollary identifies `d(·, C)` with the infimal convolution of the norm and
  the indicator of `C`, then applies the convexity owners for those two factors.

Domain-style sampling used here:
- `Function.isConvex_norm`;
- `indicator_isConvex_iff`;
- `Function.IsConvex.infimal_convolution`;
- `infimal_convolution_norm_indicator_eq_distanceToSet`.

Ambient minimization: although the source states the result on `ℝ^n`, every owner used here lives
on an arbitrary real seminormed space, so the public statement is kept at that intrinsic level.
-/

-- Proof sketch: `Text_5_4_1_4` rewrites `d(·, C)` as the infimal convolution of the norm with
-- the indicator of `C`. The norm is convex by `Function.isConvex_norm`, and the indicator is
-- convex exactly when `C` is convex by `indicator_isConvex_iff`. Then apply
-- `Function.IsConvex.infimal_convolution` and rewrite back to `d(·, C)`.
/-- Text 5.4.1.5: for a convex set `C`, the distance-to-set function `x ↦ d(x, C)` is convex.
The source states this on `ℝ^n`; the canonical chapter owner statement is valid on any real
seminormed space. -/
theorem distanceToSet_isConvex
    (C : Set E) (hC : Convex ℝ C) :
    (fun x ↦ (d(x, C) : WithTopBot ℝ)).IsConvex ℝ := by
  classical
  have hconv : ((((norm : E → ℝ).toWithTopBot) □ (δ(· | C)))).IsConvex ℝ :=
    Function.IsConvex.infimal_convolution Function.isConvex_norm
      ((indicator_isConvex_iff C).2 hC)
  have hEq :
      (((norm : E → ℝ).toWithTopBot) □ (fun z ↦ if z ∈ C then (0 : WithTopBot ℝ) else ⊤)) =
        fun x ↦ (d(x, C) : WithTopBot ℝ) := by
    funext x
    simpa [indicator_def] using
      congrArg (fun F : E → WithTopBot ℝ => F x)
        (infimal_convolution_norm_indicator_eq_distanceToSet (C := C))
  exact hEq ▸ hconv

end

/-! ### Text_5_4_1_6 (from Chap01) -/
noncomputable section

open scoped Pointwise
open Function

namespace Function

/-- Helper for Text 5.4.1.6: the set of scalar heights whose vertical fiber above `x` meets `F`.
-/
def verticalHeights (F : Set (E × 𝕜)) (x : E) : Set (WithTopBot 𝕜) :=
  ((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F}

end Function

section

variable {E : Type*} {𝕜 : Type*}
variable [Add E]
variable [ConditionallyCompleteLattice 𝕜] [AddCommMonoid 𝕜]

/-- Helper for Text 5.4.1.6: the item-local infimal convolution is the vertical-fiber infimum of
the Minkowski sum of the two scalar epigraphs. -/
def infimal_convolution (f₁ f₂ : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (verticalHeights (epi f₁ + epi f₂) x)

infixl:70 " □ " => infimal_convolution

-- Proof sketch: in this item-local file, `□` is defined directly as the `sInf` of the scalar
-- heights in the vertical fiber of the epigraph Minkowski sum.

/-- Helper for Text 5.4.1.6: under the pointwise no-`⊥` guard, the infimal convolution is the
function that assigns to each `x` the infimum of the scalar heights in the vertical fiber of the
epigraph Minkowski sum `epi f₁ + epi f₂`. -/
theorem infimal_convolution_eq_sInf_verticalHeights_epi_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ y : E, f₁ y ≠ ⊥)
    (hf₂_ne_bot : ∀ y : E, f₂ y ≠ ⊥) :
    (f₁ □ f₂) =
      fun x ↦ sInf (verticalHeights (epi f₁ + epi f₂) x) := by
  -- The item-local owner is defined by this vertical-fiber infimum, so the bridge is
  -- definitional.
  let _h₁ := hf₁_ne_bot
  let _h₂ := hf₂_ne_bot
  rfl

/-- Text 5.4.1.6: for every `x`, the value of the infimal convolution is the infimum of the scalar
heights `μ` such that `(x, μ)` belongs to the Minkowski sum of the two scalar epigraphs, provided
both functions are nowhere `⊥`. -/
theorem infimal_convolution_eq_sInf_epigraph_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ y : E, f₁ y ≠ ⊥)
    (hf₂_ne_bot : ∀ y : E, f₂ y ≠ ⊥)
    (x : E) :
    (f₁ □ f₂) x = sInf (verticalHeights (epi f₁ + epi f₂) x) := by
  -- Evaluate the item-local definition at the chosen base point `x`.
  let _h₁ := hf₁_ne_bot
  let _h₂ := hf₂_ne_bot
  rfl

end

/-! ### Text_5_4_2 (from Chap01) -/
noncomputable section

open scoped Pointwise
open Function

variable {E : Type*}
variable {𝕜 : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

section

variable {α : Type*}

variable [Zero 𝕜] [Preorder 𝕜]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.2 defines the right scalar multiple `f λ` by applying Theorem 5.3 to
  the scaled epigraph `λ (epi f)`.
- `core/canonical`: the owner abstraction for this construction is the vertical-infimum function
  `Function.verticalInfimum` on subsets of `E × α`, with the chapter epigraph owner
  `epi f` and convexity recorded by `Function.IsConvex`.
- `bridge/view`: the textbook set `λ (epi f)` is represented directly by the canonical set scalar
  multiple `(lam : 𝕜) • epi f` of the chapter epigraph owner.
- Primitive data vs derived API: the source-facing operation `rightScalarMul` is the bridge
  to the owner `Function.verticalInfimum`; its `sInf` formula and convexity preservation are
  derived API.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf`;
- `Function.IsConvex`;
- `Function.IsConvex.convex_epigraph`;
- `Function.isConvex_verticalInfimum`;
- `sInf` on `WithBotTop α`;
- `Convex.smul`.

The source assumes `f` is convex, but the construction itself depends only on `f` and the
nonnegative scalar `λ`, so the convexity assumption is kept as a derived theorem rather than a
binder in the definition.
- Ambient minimization: the source-facing owner `rightScalarMul` and its `sInf` formula use only
  the ordered scalar layer for nonnegative parameters, together with the ambient `𝕜`-actions
  needed to scale epigraph points in `E × α`, so they are stated for an arbitrary `𝕜`-smul base
  and codomain. The stronger additive and module assumptions appear only in the derived convexity
  theorem.
- Layer target: `source-facing`; `rightScalarMul` remains the public owner for Text 5.4.2, and
  its bridge/view layer is kept as the direct canonical scaled-epigraph expression `(lam : 𝕜) •
  epi f` reused by the immediate downstream scalar-rescaling formulas.
-/

/-- Text 5.4.2: for a nonnegative scalar `λ`, the right scalar multiple `f λ` is the function
obtained by applying Theorem 5.3 to the scaled scalar epigraph `λ (epi f)`. -/
abbrev rightScalarMul (lam : 𝕜≥0) (f : E → WithBotTop α) : E → WithBotTop α :=
  verticalInfimum ((lam : 𝕜) • epi f)

local infixr:73 " •ʳ " => rightScalarMul

-- Proof sketch: `rightScalarMul` is `Function.verticalInfimum` applied to the scaled
-- epigraph, so this is exactly
-- `Function.verticalInfimum_eq_sInf_verticalHeights` for that set.
/-- The value of `lam •ʳ f` at `x` is the infimum of the intrinsic scalar-height owner
`verticalHeights` for the scaled epigraph `λ (epi f)` above `x`. -/
theorem rightScalarMul_eq_sInf (lam : 𝕜≥0) (f : E → WithBotTop α) (x : E) :
    (lam •ʳ f) x =
    sInf (verticalHeights ((lam : 𝕜) • epi f) x) := by
  simpa [rightScalarMul] using
    verticalInfimum_eq_sInf_verticalHeights ((lam : 𝕜) • epi f) x

end Function

end

infixr:73 " •ʳ " => Function.rightScalarMul

section

variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function.IsConvex

-- Proof sketch: rewrite `hf` as convexity of the scalar epigraph of `f`. Scalar multiplication by
-- the nonnegative scalar `(lam : 𝕜)` preserves convexity of that subset of `E × 𝕜`. Apply Theorem
-- 5.3 to the scaled epigraph and unfold `rightScalarMul`.
/-- The right scalar multiple of a convex function is again convex. -/
theorem rightScalarMul {f : E → WithBotTop 𝕜} (hf : f.IsConvex 𝕜) (lam : 𝕜≥0) :
    (lam •ʳ f).IsConvex 𝕜 := by
  have hF : Convex 𝕜 ((lam : 𝕜) • epi f) := by
    simpa [epi_univ_eq_setOf_le] using hf.convex_epigraph.smul (lam : 𝕜)
  simpa [Function.rightScalarMul] using Function.isConvex_verticalInfimum hF

end Function.IsConvex

end
