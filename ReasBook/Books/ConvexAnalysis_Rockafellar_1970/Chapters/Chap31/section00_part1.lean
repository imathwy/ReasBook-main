import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_31_0_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [LinearOrder α]
variable [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.1 is the weak-duality inequality comparing the primal difference
  `x ↦ f x - g x` with the dual difference `y ↦ g∗ y - f⋆ y`.
- `core/canonical`: the primitive owners are already the Chapter 12 conjugate `convexConjugate`
  and the Chapter 6 order-dual bridge owner `concaveConjugate`.
- `bridge/view`: the source inequality is assembled from the owner formulas
  `convexConjugate_eq_iSup_pairing_sub` and `concaveConjugate_eq_iInf_pairing_sub`.

Domain-style sampling used here:
- `convexConjugate_eq_iSup_pairing_sub`;
- `concaveConjugate_eq_iInf_pairing_sub`;
- `convexConjugate_le_of_isFenchelPair` from `Chap03.Text_12_2_2`, checked as the nearby owner
  theorem for generalized Fenchel inequalities.

Primitive data vs derived API:
- primitive inputs: the pairing data and functions `f g : X → WithTopBot α`;
- owner abstractions reused here: `f⋆` and `g∗`;
- derived API kept here: the pointwise weak-duality comparison and its `iInf`/`iSup` corollary.

Layer target: `core/canonical`. The file keeps the source-facing weak-duality statements, but it
does not expose the single-point `iInf`/`iSup` bounds as a second public API layer because those
are direct one-line consequences of the conjugate owners themselves.
-/

/-- Pointwise weak duality in canonical owner form: each dual gap value is bounded above by each
primal gap value. -/
-- Proof sketch: combine the owner formulas
-- `concaveConjugate_eq_iInf_pairing_sub` and `convexConjugate_eq_iSup_pairing_sub`. The chosen
-- primal point `x` bounds `g∗ y` from above and `f⋆ y` from below, and subtraction monotonicity
-- removes the pairing term.
theorem concaveConjugate_sub_convexConjugate_le_sub
    (f g : X → WithTopBot α)
    (x : X) (y : Y) :
    g∗ y - f⋆ y ≤ f x - g x := by
  let p : α := ⟪x, y⟫ₚ
  have hg : g∗ y ≤ ((p : WithTopBot α) - g x) := by
    rw [concaveConjugate_eq_iInf_pairing_sub]
    exact iInf_le (fun x' : X ↦ (((⟪x', y⟫ₚ : α) : WithTopBot α) - g x')) x
  have hf : ((p : WithTopBot α) - f x) ≤ f⋆ y := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    exact le_iSup (fun x' : X ↦ (((⟪x', y⟫ₚ : α) : WithTopBot α) - f x')) x
  have hcancel :
      (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x)) = f x - g x := by
    have hneg : -((p : WithTopBot α) - f x) = f x - (p : WithTopBot α) := by
      rw [WithBotTop.sub_eq_add_neg]
      calc
        -((p : WithTopBot α) + -f x) = -(-f x + (p : WithTopBot α)) := by
          simp [add_comm]
        _ = -(-f x) + -(p : WithTopBot α) := by
          exact WithBotTop.neg_add
            (Or.inr (WithBotTop.coe_ne_top p))
            (Or.inr (WithBotTop.coe_ne_bot p))
        _ = f x - (p : WithTopBot α) := by
          simp
    calc
      (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x))
          = ((p : WithTopBot α) - g x) + (f x - (p : WithTopBot α)) := by
              rw [WithBotTop.sub_eq_add_neg, hneg]
      _ = (p : WithTopBot α) + (f x - g x) - (p : WithTopBot α) := by
              simp [add_assoc, add_left_comm, add_comm]
      _ = f x - g x := by
            show (p : WithTopBot α) + (f x - g x) - (p : WithTopBot α) = f x - g x
            exact WithBotTop.add_sub_cancel_left
  calc
    g∗ y - f⋆ y ≤ (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x)) :=
      WithBotTop.sub_le_sub hg hf
    _ = f x - g x := hcancel

/-- Lemma 31.0.1 in canonical formula surface: the supremum of the dual gap is bounded above by
the infimum of the primal gap. -/
-- Proof sketch: apply the pointwise weak-duality inequality
-- `g∗ y - f⋆ y ≤ f x - g x` for arbitrary `x` and `y`, then take the supremum over `y` on the
-- left and the infimum over `x` on the right.
theorem iSup_concaveConjugate_sub_convexConjugate_le_iInf_sub
    (f g : X → WithTopBot α) :
    (⨆ y : Y, g∗ y - f⋆ y) ≤ ⨅ x : X, f x - g x := by
  refine iSup_le ?_
  intro y
  refine le_iInf ?_
  intro x
  exact concaveConjugate_sub_convexConjugate_le_sub f g x y

end

/-! ### Lemma_31_0_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable {E : Type u} {EStar : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid EStar] [Module 𝕜 EStar]
variable [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.2 records the dual-attainment implication for the Fenchel
  pair from the relative-interior qualification
  `riDom[𝕜](f) ∩ riDom[𝕜](g) ≠ ∅`, first at the
  primal-value layer `⨅ x, f x - g x` and then at a named codomain value `α`.
- `core/canonical`: this revised item is narrowed to the proved polyhedral branch on the Chapter 31
  linear-pairing owner `[HasLinearPairing E EStar 𝕜]`, with the dual witness carrier exposed
  directly as `EStar`.
- `bridge/view`: the second theorem is only the codomain-value reparameterization of the first
  theorem, not an independent payload assumption.

Primary mathematical domain:
- finite-dimensional Fenchel duality on the nondegenerate linear-pairing owner
  `HasLinearPairing E EStar 𝕜`.

Domain-style sampling used here:
- `riDom` from `Chap01/Definition_4_4`;
- dual witnesses in `EStar`;
- the Fenchel conjugate owner `(·)⋆` from `Chap03/Defn_12_2`;
- `exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral` from
  `Chap06/Lemma_31_0_4`, used as the proved canonical owner-level bridge.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, and the qualification point in
  `riDom[𝕜](f) ∩ riDom[𝕜](g)`, together with the polyhedral and pairing-nondegeneracy inputs;
- derived API: existence of a dual witness for the conjugate inequality, and its
  reparameterization along a named value `α`.
-/

/-- Narrowed, proved owner-level primal-value form of Lemma 31.0.2 on the
`WithTopBot 𝕜` linear-pairing polyhedral layer with canonical pairing nondegeneracy
`PairingNondegenerate`. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  exact
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri hpair_nondegenerate

/-- Derived codomain-value reparameterization of the narrowed Lemma 31.0.2 form. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α)
    : ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  have hmain : ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar :=
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri hpair_nondegenerate
  rcases hmain with ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

end

/-! ### Lemma_31_0_3 (from Chap06) -/
noncomputable section

open scoped Rockafellar

/-- Canonical owner alias for pairing nondegeneracy: reuse
`HasLinearPairing.Nondegenerate` directly on the chapter theorem surface. -/
abbrev PairingNondegenerate
    {𝕜 : Type*} [CommSemiring 𝕜]
    {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    {EStar : Type*} [AddCommMonoid EStar] [Module 𝕜 EStar]
    [HasLinearPairing E EStar 𝕜] : Prop :=
  HasLinearPairing.Nondegenerate E EStar 𝕜

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {EStar : Type*} [AddCommMonoid EStar] [Module 𝕜 EStar] [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.3 is the Fenchel-duality separation clause where `g` is polyhedral:
  if `f` is proper convex, `g` is polyhedral convex, `riDom(f)` meets `dom(g)`, and
  `α = inf_x (f x - g x)` is finite, then some dual point `xStar` satisfies
  `g⋆ xStar - f⋆ xStar ≥ α`.
- `core/canonical`: the chapter owners are `Function.IsConvex`, `Function.IsProper`,
  `Function.HasPolyhedralEpigraph`, `dom(·)`, `riDom(·)`, and `convexConjugate` notation `f⋆`.
- `bridge/view`: following the Chapter 31 pattern from Lemma 31.0.2, the owner-level payload is
  first exposed directly at the canonical value `⨅ x, f x - g x`, and the source scalar `α`
  then appears only in a thin reparameterization companion.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isClosedProperConvex` from `Chap04.Corollary_19_1_2`;
- `Set.IsPolyhedral.exists_hyperplane_strongly_separating_of_disjoint_nonempty` from
  `Chap04.Corollary_19_3_3`;
- `Set.IsPolyhedral.exists_separator_not_subset_right_iff_disjoint_ri` from
  `Chap04.Theorem_20_2`.

Primitive data vs derived API:
- primitive inputs: `f`, `g`, the convex/proper owner data for `f`, the polyhedral owner data for
  `g`, the mixed qualification point in `riDom[𝕜](f) ∩ dom(g)`, and the scalar primal-value
  witness `hα`, together with the pairing nondegeneracy owner `PairingNondegenerate`;
- derived API: existence of a dual point `xStar` satisfying the conjugate inequality
  `α ≤ g⋆ xStar - f⋆ xStar`.

Layer target: `source-facing`.

Ambient refinement:
- unlike the purely `riDom`-based Lemma 31.0.2, this polyhedral branch is justified in the
  repository through the Chapter 19/20 polyhedral closedness and separation owners, which live on
  finite-dimensional topological modules over an ordered topological field with linear pairing
  data;
- Chapter 20's separation owner
  `Set.IsPolyhedral.exists_separator_not_subset_right_iff_disjoint_ri`
  also requires the pairing nondegeneracy owner `PairingNondegenerate` (equivalently,
  injectivity of `HasLinearPairing.pairingLinear`), and without it the present
  Fenchel-duality statement is false;
- the main theorem therefore lives on the actual nondegenerate pairing owner
  `HasLinearPairing E EStar 𝕜`, rather than collapsing the dual variable to a self-pairing
  ambient copy of `E`.
-/

-- Proof sketch: form the translated hypograph set
-- `D = {(x, μ) | μ ≤ g x + α}` and separate it from the epigraph of `f` by the polyhedral
-- separation theorem. The qualification hypothesis excludes a vertical separator because
-- `riDom[𝕜](f)` meets `dom(g)`. Writing the resulting affine separator as
-- `μ = ⟪x, xStar⟫ₚ - αStar`, the same conjugate inequalities as in Lemma 31.0.2 give
-- `f⋆ xStar ≤ αStar` and `αStar + α ≤ g⋆ xStar`, hence `α ≤ g⋆ xStar - f⋆ xStar`.
/-- Owner-level payload for Lemma 31.0.3 on the canonical `WithTopBot 𝕜`
polyhedral-duality layer. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  sorry

/-- Lemma 31.0.3 (polyhedral `g` form): for proper convex `f` and polyhedral convex `g`, if
`riDom[𝕜](f)` meets `dom(g)` and `α = inf_x (f x - g x)` in `WithTopBot 𝕜`, then some dual
point `xStar` in the pairing-side space `EStar` satisfies `g⋆ xStar - f⋆ xStar ≥ α`, provided the
Chapter 20 pairing nondegeneracy owner `PairingNondegenerate`. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_dom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  rcases
      exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
        hf_convex hf_proper hg_poly hri_dom hpair_nondegenerate with
    ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

end

/-! ### Lemma_31_0_4 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {EStar : Type v} [AddCommMonoid EStar] [Module 𝕜 EStar] [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.4 is the all-polyhedral branch in Fenchel duality. This file keeps
  the qualification shape `riDom[𝕜](f) ∩ riDom[𝕜](g) ≠ ∅`.
- `core/canonical`: the reusable owners are `Function.IsConvex`, `Function.HasPolyhedralEpigraph`,
  `riDom[𝕜](·)`, `dom(·)`, `Function.IsProper`, and conjugate notation `f⋆` on the nondegenerate
  pairing layer `[HasLinearPairing E EStar 𝕜]`.
- `bridge/view`: the all-`riDom` qualification is reduced to the mixed qualification
  `riDom[𝕜](f) ∩ dom(g) ≠ ∅`, then the Chapter 31.0.3 mixed-qualification theorem is applied.

Primitive data vs derived API:
- primitive inputs for the canonical owner theorem: the functions `f`, `g`, convexity/properness
  data for `f`, polyhedrality data for `g`, pairing nondegeneracy, and the qualification point in
  `riDom[𝕜](f) ∩ riDom[𝕜](g)`;
- derived API kept here: the source scalar reparameterization
  `α = inf_x (f x - g x) ⟹ ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar`, and the source
  all-polyhedral `f` specialization;
- no extra wrapper owner is introduced: this file keeps the source-facing statement directly.

Layer target: `source-facing`, on the pairing-level canonical owner.
-/

/-- Canonical owner form of Lemma 31.0.4: if `f` is proper convex, `g` has polyhedral epigraph,
and `riDom[𝕜](f)` meets `riDom[𝕜](g)`, then the primal infimum `⨅ x, f x - g x` is bounded above
by a dual conjugate difference `g⋆ xStar - f⋆ xStar`. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  have hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty := by
    rcases hri with ⟨x, hxri⟩
    exact ⟨x, hxri.1, intrinsicInterior_subset hxri.2⟩
  exact
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri_dom hpair_nondegenerate

/-- Reparameterized form of Lemma 31.0.4 at scalar value `α = inf_x (f x - g x)` under the same
all-`riDom` qualification shape. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_riDom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  rcases
      exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
        hf_convex hf_proper hg_poly hri hpair_nondegenerate with
    ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

/-- Lemma 31.0.4 (source all-polyhedral specialization): if `f` and `g` are polyhedral
`WithTopBot 𝕜`-valued functions, `f` is proper, and `riDom[𝕜](f)` meets `riDom[𝕜](g)`, then any
scalar reparameterization `α = inf_x (f x - g x)` is dominated by a dual conjugate difference
`g⋆ xStar - f⋆ xStar`. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_poly : f.HasPolyhedralEpigraph)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  exact
    exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_riDom_nonempty_of_polyhedral
      hf_poly.isConvex hf_proper hg_poly hri hpair_nondegenerate hα

end

/-! ### Lemma_31_0_5 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasPairing E EStar 𝕜]
variable {f g : E → WithBotTop 𝕜}

local instance : HasPairing E EStar (WithBotTop 𝕜) := instHasPairingWithBotTop

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜
local notation "primalObjective" => fun x : E ↦ f x - g x
local notation "convexDual" => (f⋆ : EStar → WithBotTop 𝕜)
local notation "concaveDual" => (g∗ : EStar → WithBotTop 𝕜)
local notation "dualRiQualification" =>
  Set.Nonempty (riDom[𝕜](-concaveDual) ∩ riDom[𝕜](convexDual))
local notation "primalValue" => (⨅ x : E, primalObjective x)
local notation "dualObjective" => fun xStar : EStar ↦ concaveDual xStar - convexDual xStar
local notation "dualValue" => (⨆ xStar : EStar, dualObjective xStar)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.5 is the closed-case Fenchel duality statement for the identity
  pairing configuration, with the dual qualification written as a common relative-interior point of
  the dual effective domains.
- `core/canonical`: the chapter owner theorems are already
  `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification` and
  `exists_isMinOn_sub_of_dual_riDom_inter_nonempty` from `Theorem_31_1`, built on the core owners
  `Function.IsClosedProperConvex`, the Fenchel conjugate `(·)⋆`, the Chapter 6 concave-conjugate
  notation `(·)∗`, `riDom[𝕜](·)`, and `IsMinOn`.
- `bridge/view`: this file should therefore keep only the source-facing closed-owner specialization
  of those existing Chapter 31 results, with the source phrase "closed proper concave" rendered by
  the chapter owner `g.IsClosedProperConcave`.

Layer target: pairing-based source-facing API over `WithBotTop 𝕜`, stated directly on the chapter
owners rather than on a new duality-package wrapper or a parallel local proof payload.
-/

-- Proof sketch: specialize the Chapter 31 identity-map owner theorem
-- `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification` to the closed
-- qualification branch by packaging `hf`, `hg`, and `hri` into the branch-(b) owner
-- qualification, then pair that equality with the canonical
-- primal-attainment theorem `exists_isMinOn_sub_of_dual_riDom_inter_nonempty`.
/-- Lemma 31.0.5: if `f` is closed proper convex and `g` is closed proper concave, recorded
canonically as `hf : f.IsClosedProperConvex` and `hg : g.IsClosedProperConcave`, and if the
dual relative interiors `riDom[𝕜](-g∗)` and `riDom[𝕜](f⋆)` meet, then the primal value
`⨅ x, f x - g x` equals the dual value `⨆ xStar, g∗ xStar - f⋆ xStar`, and the primal infimum is
attained. -/
theorem fenchelDuality_eq_and_primalAttainment_of_dual_riDom_inter_nonempty
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hri : dualRiQualification) :
    (primalValue = dualValue) ∧
      ∃ x : E, IsMinOn primalObjective Set.univ x := by
  refine ⟨?_, ?_⟩
  · exact
      iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification
        (Or.inr ⟨hf, hg, hri⟩)
  · exact exists_isMinOn_sub_of_dual_riDom_inter_nonempty hf hg hri

end

/-! ### Lemma_31_0_6 (from Chap06) -/
noncomputable section

universe u v

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {α : Type*}
variable [Semiring 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Add α] [Neg α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.6 introduces the perturbation bifunction
  `F(u, x) = f x - g (A x + u)` attached to Fenchel duality with a linear map `A`.
- `core/canonical`: the existing owners already present in the project are
  `Bifunction.objective`, `Function.IsConvex`, `Function.IsProperConcave`, and
  `Function.IsClosedProperConvex`, applied to the ordinary function
  `Function.uncurry F : U × X → WithTopBot α`.
- `bridge/view`: the source's zero slice `F0(x) = f(x) - g(Ax)` is the Chapter 6 owner
  `objective F`, and the source's "proper/closed bivariate function" wording is expressed through
  the Chapter 1/12 owners on `Function.uncurry F`.

Domain-style sampling used here:
- `Bifunction.objective` from `Definition_6_29_12`;
- `Function.IsConvex.comp_linearMap` from `Chap01.Theorem_5_7`;
- `Function.IsProper` from `Chap01.Definition_4_6` and
  `Function.IsProperConcave` from `Chap06.Definition_6_30_2`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive source data: the linear map `A`, the convex function `f`, and the concave function `g`;
- primitive source-facing owner in this file: `fenchelPerturbation A f g`;
- derived API: the zero-slice formula `objective (fenchelPerturbation A f g)`, and the canonical
  convexity / properness / closed-proper-convex theorems for its uncurried realization on
  `U × X`.

Layer target: `source-facing` for `fenchelPerturbation`, with the property statements delegated to
the existing canonical owners rather than to a new local wrapper for "proper bivariate function".
-/

/-- Lemma 31.0.6: the Fenchel perturbation bifunction attached to `f`, `g`, and `A`,
`F(u, x) = f x - g (A x + u)`. -/
def fenchelPerturbation (A : X →ₗ[𝕜] U) (f : X → WithTopBot α) (g : U → WithTopBot α) :
    U → X → WithTopBot α :=
  fun u x ↦ f x - g (A x + u)

@[simp] theorem fenchelPerturbation_apply
    (A : X →ₗ[𝕜] U) (f : X → WithTopBot α) (g : U → WithTopBot α) (u : U) (x : X) :
    fenchelPerturbation A f g u x = f x - g (A x + u) :=
  rfl

/-- The unperturbed objective `F0` of the Fenchel perturbation bifunction is the source expression
`x ↦ f x - g (A x)`. -/
@[simp] theorem objective_fenchelPerturbation_apply
    (A : X →ₗ[𝕜] U) (f : X → WithTopBot α) (g : U → WithTopBot α) (x : X) :
    (fenchelPerturbation A f g)₀ x = f x - g (A x) := by
  simp [objective, fenchelPerturbation]

private def fenchelPerturbationShift (A : X →ₗ[𝕜] U) : U × X →ₗ[𝕜] U :=
  A.comp (LinearMap.snd 𝕜 U X) + LinearMap.fst 𝕜 U X

private theorem uncurry_fenchelPerturbation_eq
    (A : X →ₗ[𝕜] U) (f : X → WithTopBot α) (g : U → WithTopBot α) :
    Function.uncurry (fenchelPerturbation A f g) =
      (f ∘ LinearMap.snd 𝕜 U X) + (-g) ∘ fenchelPerturbationShift A := by
  funext p
  rcases p with ⟨u, x⟩
  simp [Function.uncurry, fenchelPerturbation, fenchelPerturbationShift]

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Primitive convexity bridge for Lemma 31.0.6: if `f` is convex, `g` is concave, and both
summands in the uncurried decomposition are pointwise strictly above `⊥`, then the Fenchel
perturbation bifunction is jointly convex on `U × X`. -/
theorem uncurry_fenchelPerturbation_isConvex_of_bot_lt
    [DenselyOrdered 𝕜]
    {A : X →ₗ[𝕜] U} {f : X → WithTopBot 𝕜} {g : U → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_bot : ∀ x : X, ⊥ < f x)
    (hg_concave : g.IsConcave 𝕜) (hg_neg_bot : ∀ u : U, ⊥ < (-g) u) :
    (Function.uncurry (fenchelPerturbation A f g)).IsConvex 𝕜 := by
  have hf_proj : (f ∘ LinearMap.snd 𝕜 U X).IsConvex 𝕜 :=
    hf_convex.comp_linearMap (LinearMap.snd 𝕜 U X)
  have hg_shift : ((-g) ∘ fenchelPerturbationShift A).IsConvex 𝕜 :=
    hg_concave.convex_neg.comp_linearMap (fenchelPerturbationShift A)
  have hf_proj_bot : ∀ p : U × X, ⊥ < (f ∘ LinearMap.snd 𝕜 U X) p := by
    intro p
    simpa [Function.comp] using hf_bot (LinearMap.snd 𝕜 U X p)
  have hg_shift_bot : ∀ p : U × X, ⊥ < ((-g) ∘ fenchelPerturbationShift A) p := by
    intro p
    simpa [Function.comp] using hg_neg_bot (fenchelPerturbationShift A p)
  have hsum :
      ((f ∘ LinearMap.snd 𝕜 U X) + ((-g) ∘ fenchelPerturbationShift A)).IsConvex 𝕜 :=
    hf_proj.add_of_bot_lt hg_shift hf_proj_bot hg_shift_bot
  simpa [uncurry_fenchelPerturbation_eq A f g] using hsum

/-- Lemma 31.0.6, source-facing convexity clause: if `f` is convex and `g` is concave, expressed
canonically as the Chapter 6 owner `g.IsConcave`, and both are proper, then the Fenchel
perturbation bifunction is jointly convex on `U × X`. -/
theorem uncurry_fenchelPerturbation_isConvex
    [DenselyOrdered 𝕜]
    {A : X →ₗ[𝕜] U} {f : X → WithTopBot 𝕜} {g : U → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    (Function.uncurry (fenchelPerturbation A f g)).IsConvex 𝕜 := by
  refine uncurry_fenchelPerturbation_isConvex_of_bot_lt
      (A := A) hf_convex hf_proper.bot_lt hg_concave ?_
  intro u
  exact hg_proper.neg_isProper.bot_lt u

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {α : Type*}
variable [Semiring 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Preorder α] [Add α] [Neg α]

/-- Lemma 31.0.6, properness clause: if `f` is proper and `g` is proper concave,
expressed canonically as `g.IsProperConcave`, then the Fenchel perturbation bifunction is proper as
an extended-`α`-valued function on `U × X`. -/
theorem uncurry_fenchelPerturbation_isProper
    {A : X →ₗ[𝕜] U} {f : X → WithTopBot α} {g : U → WithTopBot α}
    (hf : f.IsProper) (hg : g.IsProperConcave) :
    (Function.uncurry (fenchelPerturbation A f g)).IsProper := by
  have hg_neg : (-g).IsProper := hg.neg_isProper
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  rcases hf.nonempty_dom with ⟨x0, hx0⟩
  rcases hg_neg.nonempty_dom with ⟨u0, hu0⟩
  refine ⟨⟨(u0 + -A x0, x0), ?_⟩, ?_⟩
  · rw [mem_effectiveDomain]
    have hfx : f x0 ≠ ⊤ := lt_top_iff_ne_top.mp hx0
    have hgu : (-g) u0 ≠ ⊤ := lt_top_iff_ne_top.mp hu0
    have hshift : fenchelPerturbationShift A (u0 + -A x0, x0) = u0 := by
      simp [fenchelPerturbationShift, add_left_comm, add_comm]
    have hsum_ne_top : f x0 + (-g) u0 ≠ ⊤ := by
      exact (WithBotTop.add_ne_top_iff_ne_top₂ (hf.bot_lt x0).ne' (hg_neg.bot_lt u0).ne').2
        ⟨hfx, hgu⟩
    rw [uncurry_fenchelPerturbation_eq A f g]
    simpa [Function.comp, hshift] using (lt_top_iff_ne_top.mpr hsum_ne_top)
  · intro p
    rw [uncurry_fenchelPerturbation_eq A f g]
    exact (WithBotTop.bot_lt_add_iff).2
      ⟨by simpa [Function.comp] using hf.bot_lt (LinearMap.snd 𝕜 U X p),
        by simpa [Function.comp] using hg_neg.bot_lt (fenchelPerturbationShift A p)⟩

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜

/-- Lemma 31.0.6: if `f` is closed proper convex and `g` is closed proper concave, expressed
canonically as `g.IsClosedProperConcave`, then the Fenchel perturbation bifunction is a closed
proper convex function on `U × X`. -/
theorem uncurry_fenchelPerturbation_isClosedProperConvex
    [TopologicalSpace (WithTopBot 𝕜)]
    [TopologicalSpace U] [ContinuousAdd U]
    [TopologicalSpace X]
    {A : X →ₗ[𝕜] U} (hA : Continuous A) {f : X → WithTopBot 𝕜} {g : U → WithTopBot 𝕜}
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g) :
    IsClosedProperConvex[𝕜] (Function.uncurry (fenchelPerturbation A f g)) := by
  have hg_neg : IsClosedProperConvex[𝕜] (-g) :=
    hg.neg_isClosedProperConvex
  have hg_properConcave : g.IsProperConcave := hg_neg.proper
  rw [Function.isClosedProperConvex_iff]
  refine ⟨uncurry_fenchelPerturbation_isConvex hf.convex hf.proper hg_neg.convex hg_properConcave,
    uncurry_fenchelPerturbation_isProper hf.proper hg_properConcave, ?_⟩
  have hf' : LowerSemicontinuous (f ∘ LinearMap.snd 𝕜 U X) :=
    hf.lowerSemicontinuous.comp continuous_snd
  have hshift : Continuous (fenchelPerturbationShift A) := by
    simpa [fenchelPerturbationShift] using (hA.comp continuous_snd).add continuous_fst
  have hg' : LowerSemicontinuous ((-g) ∘ fenchelPerturbationShift A) :=
    hg_neg.lowerSemicontinuous.comp hshift
  have hsum : LowerSemicontinuous
      ((f ∘ LinearMap.snd 𝕜 U X) + (-g) ∘ fenchelPerturbationShift A) := by
    refine hf'.add' hg' ?_
    intro p
    have hne_g : ((-g) ∘ fenchelPerturbationShift A) p ≠ ⊥ := by
      simpa [Function.comp] using (hg_neg.proper.bot_lt (fenchelPerturbationShift A p)).ne'
    have hne_f : (f ∘ LinearMap.snd 𝕜 U X) p ≠ ⊥ := by
      simpa [Function.comp] using (hf.proper.bot_lt (LinearMap.snd 𝕜 U X p)).ne'
    exact WithBotTop.continuousAt_add
      (Or.inr hne_g)
      (Or.inl hne_f)
  simpa [uncurry_fenchelPerturbation_eq A f g] using hsum

end

end Bifunction

/-! ### Lemma_31_0_7 (from Chap06) -/
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

/-! ### Lemma_31_0_8 (from Chap06) -/
noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Semiring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.8 computes the adjoint bifunction of the Fenchel perturbation
  `F(u, x) = f x - g (A x + u)`.
- `core/canonical`: the owner abstractions are already `fenchelPerturbation`, `adjoint`,
  the zero-slice owner `(·)₀`, and the conjugate owners `(·)∗` and `(·)⋆`.
- `bridge/view`: the pairing-based theorem keeps an explicit dual-side map `Astar` satisfying the
  standard compatibility identity, while the strong-dual theorem below is only the canonical
  specialization `Astar u⋆ = u⋆.comp A`.

Domain-style sampling used here:
- `fenchelPerturbation` and `objective_fenchelPerturbation_apply` from `Lemma_31_0_6`;
- `adjoint` and `objective_adjoint_apply` from `Definition_6_30_14`;
- `concaveConjugate` from `Definition_6_30_4`;
- `convexConjugate` from `Chap03/Defn_12_2`.

Primitive data vs derived API:
- primitive source data: `A`, `f`, `g`;
- primitive owner reused directly: `fenchelPerturbation A f g`;
- derived API in this file: the adjoint-value formula and its zero-slice specialization, first on
  the pairing-based dual-map layer and then on the strong-dual bridge layer.

Layer target: the first theorem is `source-facing`; the second section is `bridge/view`.
-/

/-- Lemma 31.0.8 on the pairing-based dual-map layer: if `Astar` satisfies
`⟪A x, u⋆⟫ = ⟪x, Astar u⋆⟫`, then the adjoint bifunction of the Fenchel perturbation has value
`g∗ u⋆ - f⋆ (Astar u⋆ + x⋆)`. -/
theorem adjoint_fenchelPerturbation_apply
    [Add XStar]
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = (⟪x, Astar uStar⟫ₚ : 𝕜))
    (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      g∗ uStar - f⋆ (Astar uStar + xStar) := by
  sorry

/-- Zero-slice specialization of Lemma 31.0.8 at the pairing-based dual-map layer. -/
@[simp] theorem objective_adjoint_fenchelPerturbation_apply
    [AddZeroClass XStar]
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = (⟪x, Astar uStar⟫ₚ : 𝕜))
    (uStar : UStar) :
    ((F⋆)₀ uStar) =
      g∗ uStar - f⋆ (Astar uStar) := by
  simpa [objective, add_zero] using
    (adjoint_fenchelPerturbation_apply
      (A := A) (Astar := Astar) (f := f) (g := g)
      (hA := hA) (xStar := (0 : XStar)) (uStar := uStar))

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NormedField 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (A : X →L[𝕜] U) (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A.toLinearMap f g
local notation "F⋆" =>
  (adjoint (StrongDual 𝕜 X) (StrongDual 𝕜 U) F :
    StrongDual 𝕜 X → StrongDual 𝕜 U → WithTopBot 𝕜)

/-- Lemma 31.0.8 strong-dual bridge form. -/
theorem adjoint_fenchelPerturbation_apply_strongDual
    (xStar : StrongDual 𝕜 X) (uStar : StrongDual 𝕜 U) :
    F⋆ xStar uStar =
      g∗ uStar - f⋆ (uStar.comp A + xStar) := by
  simpa using
    (adjoint_fenchelPerturbation_apply
      (A := A.toLinearMap)
      (Astar := fun uStar : StrongDual 𝕜 U ↦ uStar.comp A)
      (hA := by
        intro x uStar
        rfl)
      (f := f) (g := g) (xStar := xStar) (uStar := uStar))

/-- Zero-slice specialization of Lemma 31.0.8 in strong-dual form. -/
@[simp] theorem objective_adjoint_fenchelPerturbation_apply_strongDual
    (uStar : StrongDual 𝕜 U) :
    ((F⋆)₀ uStar) =
      g∗ uStar - f⋆ (uStar.comp A) := by
  simpa using
    (objective_adjoint_fenchelPerturbation_apply
      (A := A.toLinearMap)
      (Astar := fun uStar : StrongDual 𝕜 U ↦ uStar.comp A)
      (hA := by
        intro x uStar
        rfl)
      (f := f) (g := g) (uStar := uStar))

end

end Bifunction

/-! ### Lemma_31_0_9 (from Chap06) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v u' v' w

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Semiring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.9 records the dual objective of the Fenchel perturbation program and
  the strong-consistency criterion for the dual concave program `(P*)`.
- `core/canonical`: the owner abstractions already present upstream are
  `Bifunction.adjoint`, the zero-slice owner `Bifunction.objective`, the
  Chapter 6 strong-consistency owner `IsStronglyConsistent`, the Chapter 6 concave conjugate owner
  `concaveConjugate`, and the Chapter 12 convex conjugate owner `f⋆`.
- `bridge/view`: the source graph-function condition
  `∃ u⋆, (0, u⋆) ∈ riDom(Function.uncurry F⋆)` is retained only as a companion bridge beneath the
  canonical owner theorem on `IsStronglyConsistent 𝕜 F⋆`, while any `StrongDual` expression is
  handled downstream as a specialization bridge.

Domain-style sampling used here:
- `Bifunction.adjoint`,
  `Bifunction.objective_adjoint_fenchelPerturbation_apply`, and its
  `StrongDual` specialization from `Lemma_31_0_8`;
- `((F⋆)₀)` from `Definition_6_30_16`;
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `concaveConjugate` from `Definition_6_30_4`;
- `riDom(·)` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive source data for the dual-value layer: the primal map `A`, a dual map `Astar` with
  pairing compatibility, and functions `f`, `g`;
- primitive owner objects: `F⋆ := adjoint XStar UStar (fenchelPerturbation A f g)` and its
  source-facing zero slice `(F⋆)₀`;
- derived API: the dual-objective optimal-value identity, the owner-side strong-consistency
  criterion in relative-interior-domain language, and the lower graph-function bridge theorem.

Layer target: `source-facing`, refined to the existing adjoint-bifunction owners, with the
strong-consistency clause upgraded to the canonical owner `IsStronglyConsistent 𝕜`.
-/

variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" =>
  (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

/-- Lemma 31.0.9 (dual-value owner clause): the dual value owner `supᵇ(F⋆) 0` equals the
indexed supremum of the source dual objective formula
`⨆ u⋆, g∗ u⋆ - f⋆ (Astar u⋆)`. -/
theorem upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    supᵇ(F⋆) (0 : XStar) =
      ⨆ uStar : UStar, g∗ uStar - f⋆ (Astar uStar) := by
  sorry

/-- Lemma 31.0.9 (optimal-value clause), source objective-slice view: this is the same identity
as `upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup`, written as
`⨆ u⋆, (F⋆)₀ u⋆ = ...`. -/
theorem iSup_objective_adjoint_fenchelPerturbation_eq_iSup
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (⨆ uStar : UStar, (F⋆)₀ uStar) =
      ⨆ uStar : UStar, g∗ uStar - f⋆ (Astar uStar) := by
  simpa using
    (upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

/-- Lemma 31.0.9 (optimal-value clause), source supremum-of-range view: this is the same owner
identity as `iSup_objective_adjoint_fenchelPerturbation_eq_iSup`, expressed in the
textbook `sup` notation on the range of the dual objective. -/
theorem sSup_range_objective_adjoint_fenchelPerturbation_eq_sSup_range
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    sSup (Set.range ((F⋆)₀)) =
      sSup (Set.range (fun uStar : UStar ↦ g∗ uStar - f⋆ (Astar uStar))) := by
  simpa [sSup_range] using
    (iSup_objective_adjoint_fenchelPerturbation_eq_iSup A Astar f g hA)

end

section

universe u v u' v' w

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Ring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [Top (WithTopBot 𝕜)] [LT (WithTopBot 𝕜)] [Neg (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar] [TopologicalSpace UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" =>
  adjoint XStar UStar F

/-- Lemma 31.0.9 (strong-consistency clause), canonical owner form: the dual concave program
attached to the adjoint bifunction `F*` is strongly consistent exactly when some dual point lies
in the effective relative interior of the dual domain `riDom[𝕜](-g∗)`, and its adjoint image lies
in `riDom[𝕜](f⋆)`. -/
theorem isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    IsStronglyConsistent 𝕜 F⋆ ↔
      ∃ uStar : UStar, uStar ∈ riDom[𝕜](-g∗) ∧
        Astar uStar ∈ riDom[𝕜](f⋆) := by
  sorry

/-- Graph-function owner bridge: over the zero fiber `x⋆ = 0`, the relative-interior graph
condition is equivalent to the canonical dual-program owner `IsStronglyConsistent 𝕜 F⋆`. -/
theorem exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff_isStronglyConsistent
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (∃ uStar : UStar,
      ((0 : XStar), uStar) ∈ riDom[𝕜](Function.uncurry F⋆)) ↔
      IsStronglyConsistent 𝕜 F⋆ := by
  sorry

/-- Graph-function source companion to Lemma 31.0.9: over the zero fiber `x⋆ = 0`, the
relative-interior condition on `Function.uncurry F*` is equivalent to the same dual-domain
criterion as in `isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom`. -/
theorem exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (∃ uStar : UStar,
      ((0 : XStar), uStar) ∈ riDom[𝕜](Function.uncurry F⋆)) ↔
      (∃ uStar : UStar, uStar ∈ riDom[𝕜](-g∗) ∧
        Astar uStar ∈ riDom[𝕜](f⋆)) := by
  simpa [exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff_isStronglyConsistent
    (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA)] using
    (isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

end

end Bifunction

/-! ### Lemma_31_0_10 (from Chap06) -/
noncomputable section

universe u

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.10 introduces the translated-value function
  `p(u) = inf_x (f x - g (x + u))` and asserts its convexity.
- `core/canonical`: the Chapter 6 owner for this value function is already
  `Bifunction.perturbationFunction`, implemented as the Chapter 1 owner
  `Function.partialInfimum`; the corresponding bifunction is the identity-map specialization of
  `Bifunction.fenchelPerturbation`.
- `bridge/view`: the source formula `p(u) = inf_x (f x - g (x + u))` is exactly the evaluation
  formula for `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)`.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation`;
- `Bifunction.perturbationFunction`;
- `Function.partialInfimum`;
- `Function.IsConvex.partialInfimum`;
- `Function.IsConvex.infimal_convolution`.

Primitive data vs derived API:
- primitive source data: the functions `f` and `g`;
- primitive owner object: the perturbation function of the identity Fenchel perturbation;
- derived API: the source infimum formula and the convexity theorem.

Layer target: `source-facing`, but expressed directly through the existing owner
`perturbationFunction` instead of a parallel local definition of `p`.
-/

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [Add α] [Neg α] [InfSet (WithTopBot α)]
variable (f g : E → WithTopBot α)

local notation "F" => fenchelPerturbation LinearMap.id f g
local notation "p" => perturbationFunction F

/-- Lemma 31.0.10, source formula: for any additive extended codomain layer with infima, the
perturbation function of the identity-map Fenchel perturbation is exactly
`u ↦ inf_x (f x - g (x + u))`. -/
@[simp] theorem perturbationFunction_fenchelPerturbation_id_apply
    (u : E) : p u = ⨅ x : E, f x - g (x + u) := by
  simpa [fenchelPerturbation, sub_eq_add_neg] using perturbationFunction_apply F u

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [Ring 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {f g : E → WithTopBot 𝕜}

local notation "F" => fenchelPerturbation LinearMap.id f g
local notation "p" => perturbationFunction F

/-- Primitive convexity owner form for Lemma 31.0.10: on the `WithTopBot` codomain layer,
convexity of `f`, concavity of `g`, and the pointwise non-`⊥` guards required by the additive
convexity bridge imply convexity of the perturbation-value function
`u ↦ inf_x (f x - g (x + u))`. -/
theorem perturbationFunction_fenchelPerturbation_id_isConvex_of_bot_lt
    (hf : f.IsConvex 𝕜) (hf_bot : ∀ x : E, ⊥ < f x)
    (hg_concave : g.IsConcave 𝕜) (hg_neg_bot : ∀ u : E, ⊥ < (-g) u) :
    p.IsConvex 𝕜 := by
  have h_uncurry_convex :
      (Function.uncurry F).IsConvex 𝕜 :=
    uncurry_fenchelPerturbation_isConvex_of_bot_lt
      (A := (LinearMap.id : E →ₗ[𝕜] E)) hf hf_bot hg_concave hg_neg_bot
  simpa [perturbationFunction] using
    h_uncurry_convex.partialInfimum_uncurry

/-- Lemma 31.0.10 source-facing corollary: properness assumptions imply the primitive non-`⊥`
guards, hence convexity of the perturbation-value function
`u ↦ inf_x (f x - g (x + u))`. -/
theorem perturbationFunction_fenchelPerturbation_id_isConvex
    (hf : f.IsConvex 𝕜) (hg_concave : g.IsConcave 𝕜)
    (hf_proper : f.IsProper) (hg_proper : g.IsProperConcave) :
    p.IsConvex 𝕜 := by
  refine perturbationFunction_fenchelPerturbation_id_isConvex_of_bot_lt
      (f := f) (g := g) hf hf_proper.bot_lt hg_concave ?_
  intro u
  exact hg_proper.neg_isProper.bot_lt u

end

end Bifunction

/-! ### Lemma_31_0_11 (from Chap06) -/
noncomputable section

universe u

namespace Bifunction

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.11 is the identity-map specialization of the Fenchel-duality
  qualification statement: if `riDom[𝕜](f)` meets `riDom[𝕜](-g)`, then the associated
  identity-map Fenchel perturbation is strongly consistent.
- `core/canonical`: the owner abstractions are already `fenchelPerturbation` and
  `IsStronglyConsistent`, with the general qualification theorem
  `isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom` established upstream in
  `Lemma_31_0_7`.
- `bridge/view`: the source intersection condition is a thin rewrite of the canonical
  existential qualification witness when the linear map is `LinearMap.id`.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation`;
- `Bifunction.IsStronglyConsistent`;
- `Bifunction.isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom`;
- the Chapter 1 domain owner `riDom[𝕜](·)`.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, and a witness `x` with
  `x ∈ riDom[𝕜](f)` and `x ∈ riDom[𝕜](-g)`;
- primitive owner object: `F := fenchelPerturbation LinearMap.id f g`;
- derived API: the strong-consistency conclusion for that owner.

Layer target: `source-facing`, kept as the source's identity-map corollary while delegating the
actual owner-level proof to the general Chapter 31 theorem instead of duplicating its domain and
epigraph infrastructure locally.
-/

variable (f g : E → WithBotTop 𝕜)

local notation "F" => fenchelPerturbation LinearMap.id f g

/-- Identity-map specialization of Lemma 31.0.7 at the canonical existential qualification layer.
For `F := fenchelPerturbation id f g`, strong consistency is equivalent to existence of
`x ∈ riDom[𝕜](f)` with `x ∈ riDom[𝕜](-g)`. -/
theorem isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 F ↔
      ∃ x : E, x ∈ riDom[𝕜](f) ∧ x ∈ riDom[𝕜](-g) := by
  simpa using
    (isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom
      (A := (LinearMap.id : E →ₗ[𝕜] E)) hf hf_proper hg_concave hg_proper)

/-- Identity-map specialization of Lemma 31.0.7: for `F := fenchelPerturbation id f g`, strong
consistency is equivalent to nonempty qualification intersection
`riDom[𝕜](f) ∩ riDom[𝕜](-g)`. -/
theorem isStronglyConsistent_fenchelPerturbation_id_iff_riDom_inter_nonempty
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 F ↔
      (riDom[𝕜](f) ∩ riDom[𝕜](-g)).Nonempty := by
  simpa [Set.nonempty_def, Set.mem_inter_iff] using
    (isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper)

/-- Canonical implication form: any existential `riDom` qualification witness implies strong
consistency for the identity-map Fenchel perturbation. -/
theorem isStronglyConsistent_fenchelPerturbation_id_of_exists_mem_riDom
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hri : ∃ x : E, x ∈ riDom[𝕜](f) ∧ x ∈ riDom[𝕜](-g)) :
    IsStronglyConsistent 𝕜 F := by
  exact
    (isStronglyConsistent_fenchelPerturbation_id_iff_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper).2 hri

/- Lemma 31.0.11: if `riDom[𝕜](f)` and `riDom[𝕜](-g)` intersect, then the identity-map Fenchel
perturbation associated to `f` and `g` is strongly consistent. -/
theorem isStronglyConsistent_fenchelPerturbation_id_of_riDom_inter_nonempty
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](-g)).Nonempty) :
    IsStronglyConsistent 𝕜 F := by
  exact
    isStronglyConsistent_fenchelPerturbation_id_of_exists_mem_riDom
      (f := f) (g := g) hf hf_proper hg_concave hg_proper
      (by simpa [Set.nonempty_def, Set.mem_inter_iff] using hri)

end

end Bifunction

/-! ### Lemma_31_0_12 (from Chap06) -/
noncomputable section

universe u

open Filter
open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]
variable {f g : E → WithTopBot 𝕜}

local notation "F" =>
  (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)
local notation "p" => perturbationFunction F
local notation "F⋆" => ((adjoint Y Y F) : Y → Y → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.12 compares the dual objective
  `sup_xStar (g* xStar - f* xStar)` on an abstract dual-side pairing carrier `Y`
  with the perturbation-value function
  `p(u) = inf_x (f x - g (x + u))`, concluding
  `sup_xStar (g* xStar - f* xStar) = liminf_{u → 0} p(u) ≤ p(0)`.
- `core/canonical`: the relevant owner abstractions already present in the project are
  `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)`,
  the Chapter 6 dual-objective owner `((F⋆)₀)`,
  the Chapter 6 consistency owners `IsConsistent F` and `IsConsistent F⋆`,
  the pairing-level identity-map specialization pattern used in `Lemma_31_0_13`,
  and the filter-side liminf owner.
- `bridge/view`: the source liminf statement is the evaluation at `0` of the canonical
  Chapter 6 perturbation/adjoint duality layer, with the self-dual or Euclidean surface treated
  only as a later bridge. No new local `p` definition or second dual-objective owner is needed.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `((adjoint Y Y F)₀)` / `(F⋆)₀` from `Definition_6_30_16`;
- `IsConsistent` from `Definition_6_29_1`;
- `Bifunction.objective_adjoint_fenchelPerturbation_apply` from `Lemma_31_0_8`;
- the pairing-level dual-owner formulation in `Lemma_31_0_13`;
- the Corollary 6.30.3 liminf owner theorem for perturbation functions and adjoint upper
  perturbation functions, whose self-dual specialization underlies this source-facing statement.

Primitive data vs derived API:
- primitive source data: joint convexity of the identity-map Fenchel perturbation on `E × E`,
  together with primal-or-dual consistency at the Chapter 6 owner layer
  `IsConsistent F ∨ IsConsistent F⋆`;
- primitive owner object: the perturbation function of the identity-map Fenchel perturbation;
- derived API: the dual-objective equality with the liminf of that perturbation function, and the
  immediate neighborhood-filter inequality `liminf ... ≤ p(0)`.

Layer target: `source-facing`, stated directly on the existing owner objects instead of on a
parallel local wrapper around `p` or around the concave conjugate.
-/

/-- Core owner form for Lemma 31.0.12: if the identity-map Fenchel perturbation is jointly convex
on `E × E` and either the primal or the dual program is consistent, then the dual upper
perturbation value at `0` equals the liminf at `0` of the perturbation function. -/
theorem upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    supᵇ(F⋆) (0 : Y) =
      liminf p (nhds (0 : E)) := by
  symm
  simpa [p] using
    (liminf_perturbationFunction_eq_upperPerturbationFunction_adjoint_zero_of_primal_or_dual_consistent
      (F := F) hF_convex hconsistent)

/-- Lemma 31.0.12, source dual-objective surface: the supremum of the dual objective
`((F⋆)₀ : Y → WithTopBot 𝕜)` equals the liminf at `0` of the perturbation function. This is the
zero-slice rewrite of
`upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id`. -/
theorem dualObjective_eq_liminf_perturbationFunction_fenchelPerturbation_id
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    (⨆ xStar : Y, (F⋆)₀ xStar) =
      liminf p (nhds (0 : E)) := by
  simpa using
    (upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id
      (hF_convex := hF_convex) (hconsistent := hconsistent))

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [Ring 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable {f g : E → WithTopBot 𝕜}

local notation "F" =>
  (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)
local notation "p" => perturbationFunction F

/-- The liminf at `0` of the identity-map Fenchel perturbation value function is bounded above by
its value at `0`, i.e. by Rockafellar's `p(0)`. Together with
`perturbationFunction_fenchelPerturbation_id_apply (u := 0)`, this is the source inequality
`liminf_{u → 0} p(u) ≤ p(0) = inf_x (f x - g x)`. -/
theorem liminf_perturbationFunction_fenchelPerturbation_id_le_at_zero
    : liminf p (nhds (0 : E)) ≤ p 0 := by
  refine liminf_le_of_frequently_le' ?_
  rw [frequently_iff]
  intro s hs
  exact ⟨0, mem_of_mem_nhds hs, le_rfl⟩

end

end Bifunction
