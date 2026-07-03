import Mathlib.Analysis.Calculus.Gradient.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_26_1_1 (from Chap05) -/
noncomputable section

open Filter
open scoped Rockafellar
open scoped Gradient

namespace Function

universe u v

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.1.1 introduces essential smoothness of a proper convex
  `WithTopBot ℝ`-valued function, with the source set `C = interior dom(f)`.
- `core/canonical`: the owner declarations already present upstream are `dom(·)`,
  `Function.IsProper`, `Function.IsConvex`, `DifferentiableOn`, and the Fréchet-derivative owner
  `fderivWithin`, together with the filter statement
  `Tendsto _ (nhdsWithin x C) atTop`.
- `bridge/view`: the repeated `(a)(b)(c)` data over a set is factored as
  `Function.IsEssentiallySmoothOn C f₀` for an arbitrary scalar branch `f₀`; the textbook
  `f.IsEssentiallySmooth` keeps the textbook clause `(a)` (`interior dom(f)` nonempty) but stores
  the differential clauses on the intrinsic owner `C = riDom(f)` with `f₀ = f.realBranch`, while
  the ambient-gradient surface remains a bridge theorem under inner-product assumptions.

Domain-style sampling used here:
- `dom(·)` and `Function.IsProper` from Chapter 1;
- `Function.IsConvex` from Chapter 1;
- mathlib's `DifferentiableOn` and `fderivWithin`.

Primitive data vs derived API:
- primitive source-facing data: the proper convex function `f`, the interior nonemptiness clause,
  and the finite branch map used for differentiation on `riDom(f)`;
- primitive reusable owner data: nonemptiness, differentiability on the set, and boundary
  blow-up of the within-set Fréchet-derivative norm for a scalar-valued function on a set;
- derived API: the interior-nonempty, differentiability, and boundary-limit projections for the
  source owner `f.IsEssentiallySmooth`, together with the bridge to `interior dom(f)` and then to
  the ordinary gradient on `interior dom(f)`.

Layer target: `source-facing` for `Function.IsEssentiallySmooth`, with the canonical reusable owner
`Function.IsEssentiallySmoothOn` supplying the abstraction layer used by later Chapter 26
Legendre-type statements.
-/

section Core

variable {E : Type u} [SeminormedAddCommGroup E]

/-- The common `(a)(b)(c)` data from Definition 26.1.1 on a specified set `C`: nonemptiness,
differentiability on `C`, and divergence of the within-set Fréchet-derivative norm along `C`
toward each boundary point. -/
@[mk_iff]
class IsEssentiallySmoothOn {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    (C : Set E) (f : E → 𝕜) : Prop where
  nonempty : C.Nonempty
  differentiableOn : DifferentiableOn 𝕜 f C
  boundaryFDerivWithinNorm_tendstoTop {x : E} (hx : x ∈ frontier C) :
      Tendsto (fun y : E ↦ ‖fderivWithin 𝕜 f C y‖) (nhdsWithin x C) atTop

/-- Definition 26.1.1 source-facing specialization:
a proper convex `WithTopBot ℝ`-valued function is essentially smooth when the canonical finite real
branch `f.realBranch` satisfies the intrinsic `riDom(f)` differentiability and boundary blow-up
conditions, together with nonempty `interior (dom(f))`. -/
@[mk_iff]
class IsEssentiallySmooth [NormedSpace ℝ E] (f : E → WithTopBot ℝ) :
    Prop extends IsEssentiallySmoothOn (riDom(f)) f.realBranch where
  interior_nonempty : (interior (dom(f))).Nonempty
  convex : f.IsConvex ℝ
  proper : f.IsProper

end Core

namespace IsEssentiallySmooth

section IntrinsicOwner

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Intrinsic-domain owner data carried by `f.IsEssentiallySmooth`. -/
theorem toIsEssentiallySmoothOn_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    IsEssentiallySmoothOn (riDom(f)) f.realBranch :=
  hf.toIsEssentiallySmoothOn

/-- Intrinsic-domain differentiability clause for Definition 26.1.1. -/
theorem differentiableOn_realBranch_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    DifferentiableOn ℝ f.realBranch (riDom(f)) :=
  hf.toIsEssentiallySmoothOn_riDom.differentiableOn

/-- Intrinsic restatement of condition (a): `riDom(f)` is nonempty. -/
theorem riDom_nonempty {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth) :
    (riDom(f)).Nonempty :=
  (hf.toIsEssentiallySmoothOn_riDom).nonempty

/-- Intrinsic restatement of condition (c): the within-`riDom(f)` Fréchet derivative norm blows up
at each boundary point of `riDom(f)`. -/
theorem boundaryFDerivWithinNorm_tendstoTop_riDom
    {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (riDom(f))) :
    Tendsto (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
      (nhdsWithin x (riDom(f))) atTop :=
  (hf.toIsEssentiallySmoothOn_riDom).boundaryFDerivWithinNorm_tendstoTop hx

end IntrinsicOwner

section InteriorBridge

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an essentially smooth convex function, the intrinsic domain owner `riDom(f)` coincides
with `interior (dom(f))`. -/
theorem riDom_eq_interior_dom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    riDom(f) = interior (dom(f)) := by
  have hspan_int : affineSpan ℝ (interior (dom(f)) : Set E) = ⊤ :=
    IsOpen.affineSpan_eq_top_of_nontriviallyNormedField
      (𝕜 := ℝ) (V := E) (P := E) isOpen_interior hf.interior_nonempty
  have hmono :
      affineSpan ℝ (interior (dom(f)) : Set E) ≤ affineSpan ℝ dom(f) :=
    affineSpan_mono (k := ℝ) (V := E) (P := E)
      (s₁ := interior (dom(f))) (s₂ := dom(f)) interior_subset
  have hspan_dom : affineSpan ℝ dom(f) = ⊤ := by
    apply top_unique
    simpa [hspan_int] using hmono
  rw [riDom_real_eq_intrinsicInterior_dom,
    intrinsicInterior_eq_interior_of_affineSpan_eq_top hspan_dom]

/-- Source-owner bridge back to `interior (dom(f))`. -/
theorem toIsEssentiallySmoothOn_interior_dom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    IsEssentiallySmoothOn (interior (dom(f))) f.realBranch := by
  simpa [hf.riDom_eq_interior_dom] using hf.toIsEssentiallySmoothOn

/-- Condition (b) of Definition 26.1.1. -/
theorem differentiableOn_realBranch {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth) :
    DifferentiableOn ℝ f.realBranch (interior (dom(f))) :=
  hf.toIsEssentiallySmoothOn_interior_dom.differentiableOn

end InteriorBridge

end IsEssentiallySmooth

namespace IsEssentiallySmoothOn

section InnerProductBridge

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On an open set, the within-set boundary blow-up clause is equivalent to the ambient-gradient
formulation used in Definition 26.1.1. -/
theorem boundaryGradientNorm_tendstoTop
    {C : Set E} {f : E → 𝕜} (hf : IsEssentiallySmoothOn C f) (hC : IsOpen C)
    {x : E} (hx : x ∈ frontier C) :
    Tendsto (fun y : E ↦ ‖∇ f y‖) (nhdsWithin x C) atTop := by
  have hgrad :
      (fun y : E ↦ ‖fderivWithin 𝕜 f C y‖) =ᶠ[nhdsWithin x C] (fun y : E ↦ ‖∇ f y‖) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hCy : C ∈ nhds y := hC.mem_nhds hy
    rw [fderivWithin_of_mem_nhds hCy, gradient]
    exact ((InnerProductSpace.toDual 𝕜 E).symm.norm_map (fderiv 𝕜 f y)).symm
  exact (hf.boundaryFDerivWithinNorm_tendstoTop hx).congr' hgrad

end InnerProductBridge

end IsEssentiallySmoothOn

namespace IsEssentiallySmooth

section InnerProductBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Condition (c) in intrinsic form: the ambient-gradient norm blows up along `riDom(f)` at each
boundary point of the intrinsic domain owner. -/
theorem boundaryGradientNorm_tendstoTop_riDom {f : E → WithTopBot ℝ}
    (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (riDom(f))) :
    Tendsto (fun y : E ↦ ‖∇ f.realBranch y‖)
      (nhdsWithin x (riDom(f))) atTop := by
  let hs : IsEssentiallySmoothOn (riDom(f)) f.realBranch := hf.toIsEssentiallySmoothOn_riDom
  have hri_open : IsOpen (riDom(f)) := by
    rw [hf.riDom_eq_interior_dom]
    exact isOpen_interior
  exact hs.boundaryGradientNorm_tendstoTop hri_open hx

/-- Condition (c) of Definition 26.1.1, in the source-facing ambient-gradient form on the open
set `interior (dom(f))`. -/
theorem boundaryGradientNorm_tendstoTop {f : E → WithTopBot ℝ} (hf : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ frontier (interior (dom(f)))) :
    Tendsto (fun y : E ↦ ‖∇ f.realBranch y‖)
      (nhdsWithin x (interior (dom(f)))) atTop := by
  let hs : IsEssentiallySmoothOn (interior (dom(f))) f.realBranch :=
    hf.toIsEssentiallySmoothOn_interior_dom
  exact hs.boundaryGradientNorm_tendstoTop isOpen_interior hx

end InnerProductBridge

end IsEssentiallySmooth

end Function

/-! ### Lemma_26_1 (from Chap05) -/
open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 26.1 is the graph criterion for when a multivalued mapping and its
  inverse are both single-valued.
- `core/canonical`: Definition 26.0.3 already identifies one-to-one multivalued mappings with the
  canonical `SetRel` owner `ρ.BiUnique`.
- `bridge/view`: the graph-language criterion in this lemma is the coordinate-projection
  reformulation of that owner: `Set.InjOn Prod.fst ρ` and `Set.InjOn Prod.fst ρ⁻¹`.

Domain-style sampling used here:
- `SetRel`, `SetRel.inv`, and graph-membership notation from mathlib's `Data/Rel`;
- `Relator.BiUnique` from `Mathlib/Logic/Relator.lean`;
- `SetRel.biUnique_iff_leftUnique_and_rightUnique` from `Definition_26_0_3`;
- `Relator.RightUnique` and `Relator.LeftUnique` from `Mathlib/Logic/Relator.lean`;
- `Set.InjOn`.

Primitive data vs derived API:
- primitive owner data: a relation `ρ : SetRel α β`;
- primitive owner predicate: `ρ.BiUnique`;
- derived API: first-projection injectivity on `ρ` and `ρ⁻¹` (source-primary inverse wording),
  together with the coordinate-uniqueness graph criterion.

Layer target: `bridge/view`. The public statement stays source-facing, but it is now phrased as a
companion characterization of the canonical owner from Definition 26.0.3 rather than as a parallel
replacement for it.
-/

namespace SetRel

/-- A relation has at most one second-coordinate value over each first-coordinate point exactly
when the first projection is injective on its graph. -/
theorem injOn_fst_iff (ρ : SetRel α β) :
    Set.InjOn Prod.fst ρ ↔
      ∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2 := by
  constructor
  · intro h x xStar1 xStar2 hx1 hx2
    simpa using congrArg Prod.snd (h hx1 hx2 rfl)
  · intro h p hp q hq hpq
    rcases p with ⟨x1, xStar1⟩
    rcases q with ⟨x2, xStar2⟩
    dsimp at hpq
    cases hpq
    simpa [Prod.mk.injEq] using h hp hq

/-- Injectivity of the second projection on the original graph is exactly injectivity of the first
projection on the inverse graph. This is the canonical bridge from the source's inverse-wording to
the owner projection criterion on `ρ` itself. -/
@[simp] theorem injOn_fst_inv_iff_injOn_snd (ρ : SetRel α β) :
    Set.InjOn Prod.fst ρ⁻¹ ↔ Set.InjOn Prod.snd ρ := by
  constructor
  · intro h p hp q hq hpq
    have hp' : p.swap ∈ ρ⁻¹ := hp
    have hq' : q.swap ∈ ρ⁻¹ := hq
    exact congrArg Prod.swap (h hp' hq' hpq)
  · intro h p hp q hq hpq
    have hp' : p.swap ∈ ρ := hp
    have hq' : q.swap ∈ ρ := hq
    exact congrArg Prod.swap (h hp' hq' hpq)

/-- A relation has at most one first-coordinate value over each second-coordinate point exactly
when the second projection is injective on its graph. This is the direct `ρ`-side companion to
`injOn_fst_inv_iff`. -/
theorem injOn_snd_iff (ρ : SetRel α β) :
    Set.InjOn Prod.snd ρ ↔
      ∀ ⦃x1 x2 : α⦄ ⦃xStar : β⦄, x1 ~[ρ] xStar → x2 ~[ρ] xStar → x1 = x2 := by
  rw [← injOn_fst_inv_iff_injOn_snd]
  constructor
  · intro h x1 x2 xStar hx1 hx2
    exact (injOn_fst_iff ρ⁻¹).1 h hx1 hx2
  · intro h
    exact (injOn_fst_iff ρ⁻¹).2 fun {x} {xStar1} {xStar2} hx1 hx2 ↦ h hx1 hx2

/-- Right-uniqueness of the relation owner is exactly injectivity of the first projection on its
graph. -/
theorem rightUnique_iff_injOn_fst (ρ : SetRel α β) :
    ρ.RightUnique ↔ Set.InjOn Prod.fst ρ := by
  simpa [SetRel.RightUnique, Relator.RightUnique] using (injOn_fst_iff ρ).symm

/-- Left-uniqueness of the relation owner is exactly injectivity of the second projection on its
graph. -/
theorem leftUnique_iff_injOn_snd (ρ : SetRel α β) :
    ρ.LeftUnique ↔ Set.InjOn Prod.snd ρ := by
  simpa [SetRel.LeftUnique, Relator.LeftUnique] using (injOn_snd_iff ρ).symm

/-- Left-uniqueness of the original relation is exactly injectivity of the first projection on
the inverse graph. This is the source inverse-single-valuedness bridge at the projection layer. -/
theorem leftUnique_iff_injOn_fst_inv (ρ : SetRel α β) :
    ρ.LeftUnique ↔ Set.InjOn Prod.fst ρ⁻¹ := by
  rw [leftUnique_iff_injOn_snd, ← injOn_fst_inv_iff_injOn_snd]

/-- Companion criterion: the canonical one-to-one owner is equivalent to injectivity of both
coordinate projections on the graph of `ρ`. -/
theorem biUnique_iff_injOn_fst_and_snd (ρ : SetRel α β) :
    ρ.BiUnique ↔
      Set.InjOn Prod.fst ρ ∧ Set.InjOn Prod.snd ρ := by
  constructor
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique] at h
    exact ⟨(rightUnique_iff_injOn_fst ρ).1 h.2, (leftUnique_iff_injOn_snd ρ).1 h.1⟩
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique]
    exact ⟨(leftUnique_iff_injOn_snd ρ).2 h.2, (rightUnique_iff_injOn_fst ρ).2 h.1⟩

/-- Source-inverse companion: the canonical one-to-one owner is equivalent to injectivity of the
first projection on the graph of `ρ` and on the graph of `ρ⁻¹`. -/
theorem biUnique_iff_injOn_fst_and_fst_inv (ρ : SetRel α β) :
    ρ.BiUnique ↔
      Set.InjOn Prod.fst ρ ∧ Set.InjOn Prod.fst ρ⁻¹ := by
  constructor
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique] at h
    exact ⟨(rightUnique_iff_injOn_fst ρ).1 h.2, (leftUnique_iff_injOn_fst_inv ρ).1 h.1⟩
  · intro h
    rw [SetRel.biUnique_iff_leftUnique_and_rightUnique]
    exact ⟨(leftUnique_iff_injOn_fst_inv ρ).2 h.2, (rightUnique_iff_injOn_fst ρ).2 h.1⟩

/-- Source-inverse graph criterion: one-to-one-ness is equivalent to first-coordinate uniqueness on
both `ρ` and `ρ⁻¹`. This keeps the source inverse wording while staying at the first-projection
criterion on each graph. -/
theorem biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness (ρ : SetRel α β) :
    ρ.BiUnique ↔
      (∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2) ∧
        ∀ ⦃xStar : β⦄ ⦃x1 x2 : α⦄, xStar ~[ρ⁻¹] x1 → xStar ~[ρ⁻¹] x2 → x1 = x2 := by
  rw [biUnique_iff_injOn_fst_and_fst_inv, injOn_fst_iff, injOn_fst_iff]

/-- Lemma 26.1: a multivalued mapping is one-to-one exactly when its graph contains neither two
distinct pairs with the same first coordinate nor two distinct pairs with the same second
coordinate. This is the graph-side characterization of the canonical owner
`ρ.BiUnique`. -/
theorem biUnique_iff_graph_coordinate_uniqueness (ρ : SetRel α β) :
    ρ.BiUnique ↔
      (∀ ⦃x : α⦄ ⦃xStar1 xStar2 : β⦄, x ~[ρ] xStar1 → x ~[ρ] xStar2 → xStar1 = xStar2) ∧
        ∀ ⦃x1 x2 : α⦄ ⦃xStar : β⦄, x1 ~[ρ] xStar → x2 ~[ρ] xStar → x1 = x2 := by
  constructor
  · intro h
    rcases (biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness ρ).1 h with ⟨hρ, hρinv⟩
    refine ⟨hρ, ?_⟩
    intro x1 x2 xStar hx1 hx2
    exact hρinv (by simpa [SetRel.mem_inv] using hx1) (by simpa [SetRel.mem_inv] using hx2)
  · intro h
    refine (biUnique_iff_graph_fst_uniqueness_and_inv_fst_uniqueness ρ).2 ?_
    refine ⟨h.1, ?_⟩
    intro xStar x1 x2 hx1 hx2
    exact h.2 (by simpa [SetRel.mem_inv] using hx1) (by simpa [SetRel.mem_inv] using hx2)

end SetRel

end

/-! ### Theorem_26_1 (from Chap05) -/
noncomputable section

open scoped Gradient SetRel Rockafellar

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 26.1 states that a closed proper convex function has a single-valued
  subdifferential mapping exactly when it is essentially smooth, and then identifies that mapping
  with the gradient on the intrinsic domain owner `riDom(f)`; the textbook
  `interior (dom(f))` phrasing is kept as a bridge view.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallySmooth`, the intrinsic graph relation `subdifferentialGraph f`, the
  single-valuedness owner `(subdifferentialGraph f).RightUnique`, the
  projection-criterion bridge `SetRel.injOn_fst_iff`, and the pointwise owner
  `subdifferentialAt f x`.
- `bridge/view`: the source phrase “`df` is single-valued” is owned by
  `(subdifferentialGraph f).RightUnique`; the graph condition
  `Set.InjOn Prod.fst (subdifferentialGraph f)` is only
  the coordinate-projection reformulation supplied by `Lemma_26_1`.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `subdifferentialGraph` from `Definition_5_24_3`;
- `SetRel.RightUnique` from `Definition_26_0_1`;
- `SetRel.injOn_fst_iff` from `Lemma_26_1`;
- `Function.subdifferentialWithinAt_eq_singleton_gradient` from `Theorem_25_1`,
  together with `Function.mem_subdifferentialAt_of_tendsto` from `Theorem_5_24_7`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f`;
- primitive owner surface: the subdifferential graph `subdifferentialGraph f`, its
  single-valuedness owner `(subdifferentialGraph f).RightUnique`, and the owner
  class
  `f.IsEssentiallySmooth`;
- derived API: source-facing bridge consequences on `Function.subdifferentialAt f x` inside and
  outside `interior (dom(f))`, derived from the intrinsic pointwise `riDom(f)` owner layer.

Layer target:
- the general forward theorems
  `_root_.rightUnique_subdifferentialGraph_of_isEssentiallySmooth` and
  `_root_.injOn_fst_subdifferentialGraph_of_isEssentiallySmooth`: `bridge/view` consequences
  keeping the genuinely ambient-general direction on the intrinsic canonical owner
  `subdifferentialGraph`;
- `_root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth` and
  `_root_.injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth`: `source-facing`
  finite-dimensional equivalences, matching Rockafellar's `ℝⁿ` theorem and the Chapter 25
  finite-dimensional converse differentiability owner;
- the four `Function` theorems below: `bridge/view` companions unpacking the source sentence back
  to the Fréchet-Riesz graph and then to pointwise vector-valued fibers
  `Function.subdifferentialAt f x`.

Scalar-layer note:
- this file remains at scalar `ℝ` because the source-facing owner
  `Function.IsEssentiallySmooth` is currently defined via the finite real branch `f.realBranch`
  and gradient clauses in `Definition_26_1_1`;
- the intrinsic graph codomain owner remains `StrongDual ℝ E` through `gph∂(f)` because
  `subdifferentialGraph` in `Definition_5_24_3` is canonically dual-valued; vector/primal-codomain
  surfaces below are explicit bridge views.
-/

/-- General forward clause of Theorem 26.1 on the intrinsic owner: essential smoothness forces the
subdifferential graph to be right-unique. -/
theorem rightUnique_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    (gph∂(f)).RightUnique := by
  sorry

/-- General projection-form forward clause of Theorem 26.1 on the intrinsic owner: essential
smoothness forces injectivity of `Prod.fst` on the subdifferential graph. -/
  theorem injOn_fst_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    Set.InjOn Prod.fst (gph∂(f)) := by
  exact (SetRel.rightUnique_iff_injOn_fst (gph∂(f))).1
    (rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Theorem 26.1, canonical intrinsic graph-owner form in the source finite-dimensional ambient:
for a closed proper convex function, the subdifferential mapping is single-valued exactly when the
function is essentially smooth. The source phrase “`df` is single-valued” is expressed through
the canonical owner `(subdifferentialGraph f).RightUnique`. -/
theorem rightUnique_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (gph∂(f)).RightUnique ↔
      f.IsEssentiallySmooth := by
  sorry

/-- Dual-domain codomain bridge of Theorem 26.1 in finite dimension: for a closed proper convex
function on `StrongDual ℝ E`, right-uniqueness of the subdifferential graph with primal codomain
`E` is equivalent to essential smoothness. This is the intrinsic owner form matching the
dual-primal graph inversion surface used in Chapter 26 Legendre duality bridges. -/
theorem rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth
    {f : StrongDual ℝ E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (gph∂[E](f)).RightUnique ↔ f.IsEssentiallySmooth := by
  sorry

/-- Theorem 26.1, finite-dimensional projection-criterion companion: the source single-valuedness
clause is equivalently the injectivity of `Prod.fst` on the intrinsic graph relation
`subdifferentialGraph f`. -/
theorem injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    Set.InjOn Prod.fst (gph∂(f)) ↔
      f.IsEssentiallySmooth := by
  rw [← SetRel.rightUnique_iff_injOn_fst]
  exact rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

end FiniteDimensional

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function

private theorem rightUnique_functionSubdifferentialGraph_iff
    {f : E → WithTopBot ℝ} [CompleteSpace E] :
    (subdifferentialGraph f).RightUnique ↔
      (gph∂(f)).RightUnique := by
  sorry

/-- General Fréchet-Riesz forward clause of Theorem 26.1: in a real inner-product space,
essential smoothness forces right-uniqueness of the vector-valued subdifferential graph. -/
theorem rightUnique_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    (subdifferentialGraph f).RightUnique := by
  intro x xStar1 xStar2 hx1 hx2
  apply (InnerProductSpace.toDualMap ℝ E).injective
  have hx1Dual :
      x ~[gph∂(f)]
        (InnerProductSpace.toDualMap ℝ E xStar1) :=
    _root_.mem_subdifferentialGraph.mpr (Function.mem_subdifferentialGraph.mp hx1)
  have hx2Dual :
      x ~[gph∂(f)]
        (InnerProductSpace.toDualMap ℝ E xStar2) :=
    _root_.mem_subdifferentialGraph.mpr (Function.mem_subdifferentialGraph.mp hx2)
  exact (_root_.rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)
    hx1Dual hx2Dual

/-- General Fréchet-Riesz projection-form forward clause of Theorem 26.1: in a real
inner-product space, essential smoothness forces injectivity of `Prod.fst` on the vector-valued
subdifferential graph. -/
theorem injOn_fst_subdifferentialGraph_of_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hess : f.IsEssentiallySmooth) :
    Set.InjOn Prod.fst (subdifferentialGraph f) := by
  exact (SetRel.rightUnique_iff_injOn_fst (subdifferentialGraph f)).1
    (rightUnique_subdifferentialGraph_of_isEssentiallySmooth hess)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Theorem 26.1, Fréchet-Riesz owner bridge form in the source finite-dimensional ambient:
single-valuedness of the vector-valued subdifferential graph is equivalent to essential
smoothness. -/
theorem rightUnique_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (subdifferentialGraph f).RightUnique ↔ f.IsEssentiallySmooth := by
  rw [rightUnique_functionSubdifferentialGraph_iff]
  exact _root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

/-- Theorem 26.1, finite-dimensional Fréchet-Riesz projection companion: the vector-valued
subdifferential graph is single-valued exactly when `Prod.fst` is injective on its graph. -/
theorem injOn_fst_subdifferentialGraph_iff_isEssentiallySmooth
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    Set.InjOn Prod.fst (subdifferentialGraph f) ↔ f.IsEssentiallySmooth := by
  rw [← SetRel.rightUnique_iff_injOn_fst]
  exact rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf

end FiniteDimensional

section Pointwise

variable [CompleteSpace E]
variable {f : E → WithTopBot ℝ}

/-- Theorem 26.1, intrinsic pointwise clause: for an essentially smooth lower-semicontinuous
function, the vector-valued subdifferential at a point of `riDom(f)` is the singleton containing
the gradient of the canonical finite real branch `f.realBranch`. The convexity and properness
data are already part of `hess`. -/
theorem subdifferentialAt_eq_singleton_gradient_of_mem_riDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ riDom(f)) :
    subdifferentialAt f x = {∇ f.realBranch x} := by
  sorry

/-- Theorem 26.1, intrinsic complement clause: for an essentially smooth lower-semicontinuous
function, the vector-valued subdifferential is empty at every point outside `riDom(f)`. The
convexity and properness data are already part of `hess`. -/
theorem subdifferentialAt_eq_empty_of_not_mem_riDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∉ riDom(f)) :
    subdifferentialAt f x = ∅ := by
  sorry

/-- Source-facing bridge companion of Theorem 26.1: the intrinsic `riDom(f)` pointwise singleton
formula, restated on `interior (dom(f))` via `hess.riDom_eq_interior_dom`. -/
theorem subdifferentialAt_eq_singleton_gradient_of_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ interior (dom(f))) :
    subdifferentialAt f x = {∇ f.realBranch x} := by
  have hx' : x ∈ riDom(f) := by
    simpa [hess.riDom_eq_interior_dom] using hx
  exact subdifferentialAt_eq_singleton_gradient_of_mem_riDom hclosed hess hx'

/-- Source-facing bridge companion of Theorem 26.1: the intrinsic `riDom(f)` emptiness clause,
restated on the textbook ambient complement `x ∉ interior (dom(f))`. -/
theorem subdifferentialAt_eq_empty_of_not_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∉ interior (dom(f))) :
    subdifferentialAt f x = ∅ := by
  have hx' : x ∉ riDom(f) := by
    simpa [hess.riDom_eq_interior_dom] using hx
  exact subdifferentialAt_eq_empty_of_not_mem_riDom hclosed hess hx'

end Pointwise

end Function

end
