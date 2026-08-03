import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3

open Set
open scoped InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section AbstractConstrainedMinimizationProblems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 27.13 says the Gâteaux gradient field is constant on the constrained
  minimizer set.
- `core/canonical`: the reusable owners are `Argmin[C] f.asEReal`, `Γ₀(H)`, and the Chapter 2
  derivative-field owner `HasGateauxDerivativeOn`.
- `bridge/view`: the source statement remains the pairwise equality of gradients at two minimizers,
  and the companion theorem below packages the same content as an `EqOn` statement over
  `Argmin[C] f.asEReal`.
-/

-- Semantic recall note: `lean_leansearch` only surfaced generic gradient/convexity API. The
-- verified project-facing owners for this item are the constrained argmin surface
-- `Argmin[C] f.asEReal` and the Chapter 2 derivative-field owner `HasGateauxDerivativeOn`.

/-- Proposition 27.13: if `f ∈ Γ₀(H)`, if `C` is a convex subset of
`interior (effectiveDomain f)`, and if `gradf` is the Gâteaux gradient field of
`x ↦ (f x : EReal).toReal` on `C`, then any two minimizers of `f` over `C` have the same
gradient. -/
theorem gradient_eq_of_mem_argminOn_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC_convex : Convex ℝ C)
    (hC_dom : C ⊆ interior (effectiveDomain f)) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn
        (fun z : H ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDual ℝ H (gradf z)) C)
    {x y : H} (hx : x ∈ Argmin[C] f.asEReal) (hy : y ∈ Argmin[C] f.asEReal) :
    gradf x = gradf y := by
  sorry

/-- Companion API for Proposition 27.13: the gradient image of the constrained minimizer set is a
subsingleton. -/
theorem gradientImage_argminOn_subsingleton_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC_convex : Convex ℝ C)
    (hC_dom : C ⊆ interior (effectiveDomain f)) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn
        (fun z : H ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDual ℝ H (gradf z)) C) :
    (gradf '' Argmin[C] f.asEReal).Subsingleton := by
  intro u hu v hv
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  exact
    gradient_eq_of_mem_argminOn_of_hasGateauxDerivativeOn
      hf hC_convex hC_dom gradf hgrad hx hy

end AbstractConstrainedMinimizationProblems

end ERealFunction
