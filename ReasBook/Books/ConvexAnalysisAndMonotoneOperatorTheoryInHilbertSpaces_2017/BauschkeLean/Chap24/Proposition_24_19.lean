import Mathlib
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap10.Definition_10_1
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Owner/API sampling for this item:
-- - `source-facing`: Proposition 24.19 identifies the scaled proximal map of a positively
--   homogeneous `Γ₀(H)` function with projection onto the scaled zero-subdifferential.
-- - `core/canonical`: Chapter 16 supplies the support-function identification
--   `eq_supportFunction_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero`, and
--   Chapter 23 supplies the support-function/projection proximal formula.
-- - `bridge/view`: this file only adds the derived closed-convex/Chebyshev packaging for the
--   scaled zero-subdifferential, keeping the theorem surface on the existing `Prox` and `P`
--   owners.
/-- The scaled zero-subdifferential of a positively homogeneous member of `Γ₀(H)`
is Chebyshev. -/
theorem isChebyshev_smul_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    IsChebyshev ((γ : ℝ) • ((∂ f) 0) : Set H) := by
  obtain ⟨_, hminorant_nonempty, hminorant_closed, hminorant_convex⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hph hf
  have h0 : (f 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hsub :
      linearMinorantSet f = (∂ f) 0 :=
    linearMinorantSet_eq_subdifferential_zero h0
  have hsub_nonempty : ((∂ f) 0).Nonempty := by
    simpa [← hsub] using hminorant_nonempty
  have hsub_closed : IsClosed ((∂ f) 0) := by
    simpa [← hsub] using hminorant_closed
  have hsub_convex : Convex ℝ ((∂ f) 0) := by
    simpa [← hsub] using hminorant_convex
  have hscaled_nonempty : (((γ : ℝ) • ((∂ f) 0) : Set H)).Nonempty := by
    rcases hsub_nonempty with ⟨u, hu⟩
    exact ⟨(γ : ℝ) • u, Set.smul_mem_smul_set hu⟩
  have hscaled_closed : IsClosed ((γ : ℝ) • ((∂ f) 0) : Set H) := by
    simpa using hsub_closed.smul₀ (γ : ℝ)
  have hscaled_convex : Convex ℝ ((γ : ℝ) • ((∂ f) 0) : Set H) := by
    intro x hx y hy a b ha hb hab
    rcases Set.mem_smul_set.mp hx with ⟨u, hu, rfl⟩
    rcases Set.mem_smul_set.mp hy with ⟨v, hv, rfl⟩
    refine Set.mem_smul_set.mpr ⟨a • u + b • v, hsub_convex hu hv ha hb hab, ?_⟩
    simp [smul_add, smul_smul, mul_comm]
  exact isChebyshev_of_nonempty_isClosed_convex
    hscaled_nonempty hscaled_closed hscaled_convex

/-- Proposition 24.19: if `f ∈ Γ₀(H)` is positively homogeneous, `γ ∈ ℝ_{++}`,
and `x ∈ H`,
then `Prox_{γ f} x = x - P_{γ ∂ f(0)} x`. -/
theorem prox_eq_sub_projectionPoint_smul_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)}
    (hph : PositivelyHomogeneous f.asEReal) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    Prox[γ, f, hf] x =
      x - P[(γ : ℝ) • ((∂ f) 0),
        isChebyshev_smul_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
          hph hf γ] x := by
  let D : Set H := (γ : ℝ) • ((∂ f) 0)
  let hD : IsChebyshev D :=
    isChebyshev_smul_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero hph hf γ
  obtain ⟨_, hminorant_nonempty, hminorant_closed, hminorant_convex⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hph hf
  have h0 : (f 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hsub :
      linearMinorantSet f = (∂ f) 0 :=
    linearMinorantSet_eq_subdifferential_zero h0
  have hsub_nonempty : ((∂ f) 0).Nonempty := by
    simpa [← hsub] using hminorant_nonempty
  have hsub_closed : IsClosed ((∂ f) 0) := by
    simpa [← hsub] using hminorant_closed
  have hsub_convex : Convex ℝ ((∂ f) 0) := by
    simpa [← hsub] using hminorant_convex
  have hD_nonempty : D.Nonempty := by
    rcases hsub_nonempty with ⟨u, hu⟩
    exact ⟨(γ : ℝ) • u, by simpa [D] using Set.smul_mem_smul_set hu⟩
  have hD_closed : IsClosed D := by
    simpa [D] using hsub_closed.smul₀ (γ : ℝ)
  have hD_convex : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    rcases Set.mem_smul_set.mp hx with ⟨u, hu, rfl⟩
    rcases Set.mem_smul_set.mp hy with ⟨v, hv, rfl⟩
    refine Set.mem_smul_set.mpr ⟨a • u + b • v, hsub_convex hu hv ha hb hab, ?_⟩
    simp [smul_add, smul_smul, mul_comm]
  let σD : H → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (isProper_supportFunction_of_nonempty D hD_nonempty)
  have hσD : σD ∈ Γ₀(H) :=
    example_11_2_2_supportFunction_mem_gammaZero D hD_nonempty
  have hscaled :
      γ • f = σD := by
    funext u
    apply Subtype.ext
    change (((γ : ℝ) : EReal) * (f u : EReal)) = σ[D] u
    have hu :
        (f u : EReal) = σ[(∂ f) 0] u := by
      simpa using
        congrArg (fun g : H → EReal ↦ g u)
          (eq_supportFunction_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero hph hf)
    rw [hu, show D = (γ : ℝ) • ((∂ f) 0) by rfl]
    calc
      ((γ : ℝ) : EReal) * σ[(∂ f) 0] u
          = (σ[(∂ f) 0] ∘ fun v : H ↦ (γ : ℝ) • v) u := by
              simpa using
                (congrFun
                  (supportFunction_comp_pos_smul_eq_mul_supportFunction ((∂ f) 0) γ.2) u).symm
      _ = σ[((γ : ℝ) • ((∂ f) 0) : Set H)] u := by
            simpa using
              congrFun
                (supportFunction_comp_smul_eq_supportFunction_smul_set
                  ((∂ f) 0) (γ : ℝ)) u
  have hEq :
      Prox[σD, hσD] = fun y : H ↦ y - P[D, hD] y := by
    have hιD : ι[D] ∈ Γ₀(H) :=
      indicator_mem_gammaZero_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
    have hconj : ι[D]∗[hιD] = σD := by
      funext y
      apply Subtype.ext
      change ((ι[D]∗[hιD] y : EReal)) = (σD y : EReal)
      rw [gammaZeroConjugate_apply, conjugate_indicator_eq_supportFunction]
    have hprox_conj : Prox⋆[ι[D], hιD] = Prox[σD, hσD] := by
      funext y
      apply eq_proximityOperator_of_isProxPoint σD (hasUniqueProxPoint_of_mem_gammaZero σD hσD)
      simpa [hconj] using
        (proximityOperator_isProxPoint (ι[D]∗[hιD])
          (hasUniqueProxPoint_of_mem_gammaZero
            (ι[D]∗[hιD]) (gammaZeroConjugate_mem_gammaZero hιD))
          y)
    have hproj : Prox[ι[D], hιD] = P[D, hD] := by
      funext y
      simpa using
        congrFun
          (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
            hD_nonempty hD_closed hD_convex) y
    funext y
    calc
      Prox[σD, hσD] y = Prox⋆[ι[D], hιD] y := by rw [hprox_conj]
      _ = y - Prox[ι[D], hιD] y := by
        simpa using conjugate_proximityOperator_eq_sub_proximityOperator (ι[D]) hιD y
      _ = y - P[D, hD] y := by rw [hproj]
  have hprox_scaled :
      IsProxPoint (γ • f) x (x - P[D, hD] x) := by
    have hproxσ :
        IsProxPoint σD x (x - P[D, hD] x) := by
      simpa [hEq] using
        proximityOperator_isProxPoint σD (hasUniqueProxPoint_of_mem_gammaZero σD hσD) x
    simpa [hscaled] using hproxσ
  simpa [scaledProximityOperator, D, hD] using
    (eq_proximityOperator_of_isProxPoint
      (γ • f)
      (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
      hprox_scaled).symm

end BasicProperties

end

end ERealFunction
