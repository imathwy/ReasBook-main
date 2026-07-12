import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

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
