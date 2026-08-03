import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap24.Proposition_24_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic parity facts for
-- arbitrary functions, so this item follows the verified local Chapter 24 reflection identity
-- `prox_reverse_eq_neg_prox_neg` together with the canonical unit-scale proximal owner
-- `Prox[f, hf]`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)}

/-- Proposition 24.10 (1): if `f ∈ Γ₀(ℋ)` is even, then its proximity operator `Prox[f, hf]`
is odd. -/
theorem odd_proximityOperator_of_even
    (hf : f ∈ Γ₀(H)) (heven : Function.Even f) :
    Function.Odd (Prox[f, hf]) := by
  let e : H ≃L[ℝ] H := ContinuousLinearEquiv.neg ℝ
  let hrev : Function.reverse f ∈ Γ₀(H) := by
    simpa [Function.comp, Function.reverse, e] using
      (mem_gammaZero_comp_continuousLinearEquiv hf e)
  have hreverse_eq : Function.reverse f = f := by
    funext x
    simpa using heven x
  intro x
  have hreverse_prox :
      Prox[Function.reverse f, hrev] (-x) = Prox[f, hf] (-x) := by
    apply eq_proximityOperator_of_isProxPoint f
      (hasUniqueProxPoint_of_mem_gammaZero f hf)
    simpa [hreverse_eq] using
      proximityOperator_isProxPoint
        (Function.reverse f)
        (hasUniqueProxPoint_of_mem_gammaZero (Function.reverse f) hrev)
        (-x)
  calc
    Prox[f, hf] (-x) = Prox[Function.reverse f, hrev] (-x) := hreverse_prox.symm
    _ = Prox[(1 : PosReal), Function.reverse f, hrev] (-x) := by
          symm
          exact congrFun (unit_scaledProx_eq_prox (Function.reverse f) hrev) (-x)
    _ = -Prox[(1 : PosReal), f, hf] x := by
          simpa [hrev] using prox_reverse_eq_neg_prox_neg hf (1 : PosReal) (-x)
    _ = -Prox[f, hf] x := by
          change
            -Prox[((1 : PosReal) • f), smul_mem_gammaZero f hf (1 : PosReal)] x =
              -Prox[f, hf] x
          exact congrArg Neg.neg (congrFun (unit_scaledProx_eq_prox f hf) x)

/-- Proposition 24.10 (2): if `f ∈ Γ₀(ℋ)` is even, then the proximal point of `f` at `0` is
`0`. -/
theorem proximityOperator_zero_eq_zero_of_even
    (hf : f ∈ Γ₀(H)) (heven : Function.Even f) :
    Prox[f, hf] (0 : H) = 0 := by
  have hodd_zero : Prox[f, hf] (0 : H) = -Prox[f, hf] (0 : H) := by
    simpa using (odd_proximityOperator_of_even hf heven) (0 : H)
  have htwo : (2 : ℝ) • Prox[f, hf] (0 : H) = 0 := by
    simpa [two_smul] using eq_neg_iff_add_eq_zero.mp hodd_zero
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end ERealFunction
