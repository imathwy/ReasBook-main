import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
