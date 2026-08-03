import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap03.Example_3_23
import BauschkeLean.Chap08.Proposition_8_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {K : Set H}

-- Semantic recall: `lean_leansearch` surfaced only generic orthogonal-projection owners, while
-- the verified project surface for this item is the Chapter 3 hyperplane owner
-- `innerProductLevelSet u η` together with the metric projector notation `P[C, hC]`.

/-- Proposition 29.33 (1): if `K` is a cone, `u ∈ K` satisfies `‖u‖ = 1`, `η ∈ ℝ_{++}`, and
`C = K ∩ innerProductLevelSet u η`, then `C` is nonempty. In the source this sits under the
standing nonempty closed convex assumptions on `K`, but the conclusion only uses the cone
hypothesis. -/
theorem nonempty_inter_innerProductLevelSet_of_mem_unit_of_cone
    (hK_cone : IsCone K) (u : H) (huK : u ∈ K) (hu_norm : ‖u‖ = 1)
    (η : PosReal) :
    (K ∩ innerProductLevelSet u η).Nonempty := by
  rw [isCone_iff] at hK_cone
  refine ⟨(η : ℝ) • u, ?_, ?_⟩
  · rw [hK_cone]
    exact ⟨η, η.2, u, huK, rfl⟩
  · rw [mem_innerProductLevelSet_iff]
    calc
      ⟪(η : ℝ) • u, u⟫_ℝ = (η : ℝ) * ⟪u, u⟫_ℝ := by rw [real_inner_smul_left]
      _ = (η : ℝ) * ‖u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = (η : ℝ) := by simp [hu_norm]

section

variable [CompleteSpace H]

/-- The intersection of a closed convex cone with a positive inner-product level set is
Chebyshev. -/
theorem isChebyshev_inter_innerProductLevelSet_of_mem_unit_of_cone
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (u : H) (huK : u ∈ K) (hu_norm : ‖u‖ = 1) (η : PosReal) :
    IsChebyshev (K ∩ innerProductLevelSet u η) := by
  exact isChebyshev_of_nonempty_isClosed_convex
    (nonempty_inter_innerProductLevelSet_of_mem_unit_of_cone hK_cone u huK hu_norm η)
    (hK_closed.inter (hyperplane_isClosed u η))
    (hK_convex.inter (innerProductLevelSet_convex u η))

end

section

variable [CompleteSpace H]
variable (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
variable (u : H) (huK : u ∈ K) (hu_norm : ‖u‖ = 1) (η : PosReal)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem nonempty_of_mem (u : H) (huK : u ∈ K) : K.Nonempty := ⟨u, huK⟩

local notation "hK_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex (nonempty_of_mem u huK) hK_closed hK_convex

local notation "P_K" => P[K, hK_cheb]

local notation "C" => K ∩ innerProductLevelSet u η

local notation "hC_cheb" =>
  isChebyshev_inter_innerProductLevelSet_of_mem_unit_of_cone
    hK_closed hK_convex hK_cone u huK hu_norm η

local notation "P_C" => P[C, hC_cheb]

/-- Proposition 29.33 (2): under the same assumptions, if `vbar : ℝ` satisfies
`⟪P_K (vbar • u + x), u⟫_ℝ = η`, then for `C = K ∩ innerProductLevelSet u η` one has
`P_C x = P_K (vbar • u + x)`. -/
theorem projectionPoint_inter_innerProductLevelSet_eq_projectionPoint_add_smul_of_inner_eq
    (x : H) (vbar : ℝ) (hvbar : ⟪P_K (vbar • u + x), u⟫_ℝ = η) :
    P_C x = P_K (vbar • u + x) := sorry

end

end
