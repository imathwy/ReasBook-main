import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.2 characterizes subgradients at a finite point by domination of the
  directional derivative in every direction.
- `core/canonical`: the relevant owners already exist upstream as the dual-valued
  `_root_.subdifferentialAt` from `Definition_23_0_6` and the directional-derivative owner
  `Function.directionalDerivativeAt` from `Lemma_23_0_1`.
- `bridge/view`: in real inner-product spaces, the chapter's vector-valued bridge
  `Function.subdifferentialAt` is obtained from `_root_.subdifferentialAt` through the canonical
  Fréchet-Riesz embedding `InnerProductSpace.toDualMap ℝ E`, so the Euclidean source wording
  should be a companion theorem rather than a second owner.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  `Chap05/Definition_23_0_6`;
- `Function.subdifferentialAt` from the same file;
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
  `Chap05/Lemma_23_0_1`, which already owns the support-function clause appearing in this
  theorem's downstream use.

Primitive data vs derived API:
- primitive data: the convex function `f`, the base point `x`, its finiteness assumptions
  `x ∈ dom(f)` and `f x ≠ ⊥`, and a candidate subgradient `xStar`;
- primitive owner surface: pairing-level membership in `_root_.subdifferentialAt f x Y`;
- derived API: the directional-derivative lower-bound characterization and the vector-valued
  inner-product specialization in the second section below.

Layer target: `core/canonical` for the main theorem. The support-function identity already has the
exact canonical owner interface upstream, so this file reuses it by direct recall instead of
introducing a renamed wrapper.

Ambient-assumption minimization:
- the main characterization uses only a pairing instance `[HasPairing E Y 𝕜]` and the
  Chapter 23 directional-derivative owner, so it is stated on the scalar-generic additive-module
  layer (without a topology on `E`) rather than on a concrete Euclidean model;
- the extra finiteness hypothesis `f x ≠ ⊥` is essential, since if `f x = ⊥` then
  `_root_.subdifferentialAt f x` degenerates to the whole dual space.
-/

-- Proof sketch: if `xStar ∈ _root_.subdifferentialAt f x`, apply the supporting-affine inequality
-- at the points `x + t • d`, divide by `t > 0`, and pass to the canonical right limit defining
-- `Function.directionalDerivativeAt`. Conversely, test the directional-derivative lower bound on
-- the direction `d = z - x`, rewrite the difference quotient at step `t = 1`, and recover the
-- global supporting inequality.
/-- Theorem 23.2, canonical owner form: for a convex `WithTopBot 𝕜`-valued function finite at
`x`, a dual-side pairing element is a subgradient at `x` exactly when it is bounded above by the
directional derivative in every direction. -/
theorem mem_subdifferentialAt_iff_le_directionalDerivativeAt
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜)
    {x : E} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    {Y : Type (max u v)} [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ (∂[Y]f(x)) ↔
      ∀ d : E, ((⟪d, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ Function.directionalDerivativeAt f x d := by
  sorry

end

section

variable {E : Type u} [InnerProductSpace ℝ E]

open scoped RealInnerProductSpace

namespace Function

-- Proof sketch: rewrite the vector-valued bridge `Function.subdifferentialAt` through the
-- Fréchet-Riesz embedding `InnerProductSpace.toDualMap ℝ E`, then apply the canonical
-- dual-valued theorem above.
/-- Theorem 23.2, Euclidean bridge form: in a real inner-product space, a vector belongs to the
Fréchet-Riesz realization of the subdifferential exactly when its inner products are
bounded above by the directional derivative in every direction. -/
theorem mem_subdifferentialAt_iff_inner_le_directionalDerivativeAt
    {f : E → WithTopBot ℝ} (hf_convex : f.IsConvex ℝ)
    {x : E} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (g : E) :
    g ∈ ∂ᵥf(x) ↔
      ∀ d : E, ((⟪g, d⟫ : ℝ) : WithTopBot ℝ) ≤ directionalDerivativeAt f x d := by
  change InnerProductSpace.toDualMap ℝ E g ∈ _root_.subdifferentialAt f x ↔
      ∀ d : E, ((⟪g, d⟫ : ℝ) : WithTopBot ℝ) ≤ directionalDerivativeAt f x d
  constructor
  · intro hg d
    have hd :
        ((⟪d, InnerProductSpace.toDualMap ℝ E g⟫ₚ : ℝ) : WithTopBot ℝ) ≤
          directionalDerivativeAt f x d :=
      ((_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt
        (f := f) hf_convex hx hx_bot (xStar := InnerProductSpace.toDualMap ℝ E g)).mp hg d)
    have hpair :
        ((⟪d, InnerProductSpace.toDualMap ℝ E g⟫ₚ : ℝ) : WithTopBot ℝ) =
          ((⟪g, d⟫ : ℝ) : WithTopBot ℝ) := by
      change ((InnerProductSpace.toDualMap ℝ E g d : ℝ) : WithTopBot ℝ) =
          ((⟪g, d⟫ : ℝ) : WithTopBot ℝ)
      rw [InnerProductSpace.toDualMap_apply_apply]
    exact hpair ▸ hd
  · intro hg
    exact
      (_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt
        (f := f) hf_convex hx hx_bot (xStar := InnerProductSpace.toDualMap ℝ E g)).mpr
        (fun d ↦ by
          have hd :
              ((⟪g, d⟫ : ℝ) : WithTopBot ℝ) ≤ directionalDerivativeAt f x d := hg d
          have hpair :
              ((⟪d, InnerProductSpace.toDualMap ℝ E g⟫ₚ : ℝ) : WithTopBot ℝ) =
                ((⟪g, d⟫ : ℝ) : WithTopBot ℝ) := by
            change ((InnerProductSpace.toDualMap ℝ E g d : ℝ) : WithTopBot ℝ) =
                ((⟪g, d⟫ : ℝ) : WithTopBot ℝ)
            rw [InnerProductSpace.toDualMap_apply_apply]
          exact hpair.symm ▸ hd)

end Function

/- The support-function clause of Theorem 23.2 is already owned upstream by the exact canonical
Chapter 23 theorem identifying the directional derivative with
`δᵛ(· | _root_.subdifferentialAt f x)` whenever the subdifferential is nonempty. -/
recall Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt

end
