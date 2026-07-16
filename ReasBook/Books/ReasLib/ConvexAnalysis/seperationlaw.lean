import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import ReasLib.Basic.ProperFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Set Inner Function Module Submodule AffineSubspace
open scoped Pointwise


local notation "ri" s => intrinsicInterior ℝ s


/- Rockafellar Thm.11.1: existence of a proper separating hyperplane is equivalent to
the existence of a vector b satisfying two sup/inf inequalities; all inner products
in the inequalities are taken in EReal. -/
/- The theorem states that if two nonempty sets s and t can be properly separated by a hyperplane,
  Then there exists a vector b such that:
    1. The infimum of inner products over s is at least the supremum over t (in EReal)
    2. The supremum over s is strictly greater than the infimum over t (in EReal) -/
lemma separate_two_sets_iff_inf_sup_Cond'' (s : Set E) (t : Set E)
    (hns : s.Nonempty) (hnt : t.Nonempty) :
    (∃ (b : E) (c : ℝ), (∀ x ∈ s, inner ℝ b x  ≥ c) ∧
    (∀ y ∈ t, inner ℝ b y ≤ c) ∧ (¬ (s ⊆ {x | inner ℝ b x = c})) ∧
    (¬ (t ⊆ {x | inner ℝ b x = c}))) → ∃ b : E,
    (⨅ x ∈ s, (inner ℝ b x : ℝ) : EReal) ≥ (⨆ y ∈ t, (inner ℝ b y : ℝ) : EReal)
    ∧ (⨆ x ∈ s, (inner ℝ b x : ℝ) : EReal) > (⨅ y ∈ t, (inner ℝ b y : ℝ) : EReal) := by
  rintro ⟨b, c, hs, ht, hs_neq, _⟩
  use b
  have ht1 : ∀ y ∈ t, ((inner ℝ b y : ℝ) : EReal) ≤ ↑c := by
    exact fun y a ↦ (fun {x y} ↦ EReal.coe_le_coe_iff.mpr) (ht y a)
  have hs1 : ∀ x ∈ s, ((inner ℝ b x : ℝ) : EReal) ≥ ↑c := by
    exact fun x a ↦ (fun {x y} ↦ EReal.coe_le_coe_iff.mpr) (hs x a)
  constructor
  · apply le_iInf₂
    intro i hi
    apply iSup₂_le
    intro j hj
    /- have h1 : ((inner ℝ b i : ℝ) : EReal) ≥ c := hs1 i hi
    have h2 : ((inner ℝ b j : ℝ) : EReal) ≤ c := ht1 j hj -/
    exact le_trans (ht1 j hj) (hs1 i hi)
  refine lt_of_not_ge (fun h => ?_)
  have h₁ : ∀ x ∈ s, ((inner ℝ b x : ℝ) : EReal) = c := by
    intro x hx
    apply le_antisymm ?_ (hs1 x hx)
    have h1 : ⨅ y ∈ t, ((inner ℝ b y : ℝ) : EReal) ≤ (c : EReal) := by
      obtain ⟨y, hy⟩ := hnt  -- t is nonempty
      exact iInf₂_le_of_le y hy (ht1 y hy)
      --have h2 : ⨆ x ∈ s, ((inner b x : ℝ) : EReal) ≤ c := le_trans h h1
    have h3 : BddAbove (Set.range (fun x : s => ((inner ℝ b x : ℝ) : EReal))) := by
      exact OrderTop.bddAbove (Set.range (fun x : s => ((inner ℝ b x : ℝ) : EReal)))
    have h4 : ((inner ℝ b x : ℝ) : EReal) ≤ ⨆ x ∈ s, ((inner ℝ b x : ℝ) : EReal) := by
      have : Nonempty (Subtype (Membership.mem s)) := by exact Nonempty.to_subtype hns
      rw [ciSup_subtype'] /- requires Bdd and nonempty -/
      exact le_ciSup h3 ⟨x, hx⟩
      exact h3
      simp [sSup_empty] /- sSup ∅ ≤ ⨆ i, ↑(inner b ↑i) -/
    apply le_trans
    exact h4
    apply le_trans h h1
  have : ∀ x ∈ s, (inner ℝ b x : ℝ) = c := by
    exact fun x a ↦ (fun {x y} ↦ EReal.coe_eq_coe_iff.mp) (h₁ x a)
  exact hs_neq this

-- ri is closed under linear maps; this theorem was proved in
-- optlib.ConvexOptimizationKKT.convex_conjugate but not migrated.
lemma linear_ri {E F} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (C : Set E) (A : E →L[ℝ] F) (hC : Convex ℝ C) :
    (ri (A '' C)) = A '' (ri C) := by
    sorry

/- A relatively open set is open in its affine span.
The relative interior of a set s is an open set within the affine span of s -/
lemma intrinsic_interior_is_open_in_affine_span (s : Set E) :
  IsOpen ((↑) ⁻¹'(intrinsicInterior ℝ s) : Set <| affineSpan ℝ s) := by
  unfold intrinsicInterior
  set fs := (Subtype.val : affineSpan ℝ s → E)
  have (t: Set <| affineSpan ℝ s) : (fs ⁻¹' (fs '' t)) = t := by
    apply Set.preimage_image_eq
    exact Subtype.val_injective
  rw [this]
  exact isOpen_interior

/- Separation theorem: a nonempty relatively open set and a point outside it. -/
/-
In a finite-dimensional space, any non-empty, convex,
and relatively open set can be strictly separated
by a hyperplane from any point not contained within it.

The proof is a case analysis on whether the point x lies within the affine span of s, denoted A.

Case 1: x is in A.
The affine problem is reduced to a linear one.
The affine space A is mapped to its direction vector space S
via translation. Crucially, the relative openness of s implies its image s'' is an open set in S.
The standard geometric Hahn-Banach theorem is then applied in S to find a separating functional,
which is extended to the full space E by orthogonal projection.
Case 2: x is not in A.
This case is simpler. Since the space is finite-dimensional,
the affine span A is a closed convex set.
The version of the Hahn-Banach theorem for separating a point from a closed convex set is
applied directly to separate x from all of A, which consequently separates x from s.-/

theorem separation_point_from_convex_rel_open
    [FiniteDimensional ℝ E] (s : Set E) (x : E) (hs_conv : Convex ℝ s)
    (hs_nonempty : s.Nonempty) (hs_rel_open : s = ri s) (hx : x ∉ s) :
  ∃ (f : E →L[ℝ] ℝ), ∀ a ∈ s, f a > f x := by
  let A := affineSpan ℝ s
  by_cases hx_in_A : x ∈ A
  · rcases hs_nonempty with ⟨p, hp⟩
    let s' := s - (Set.singleton p); let x' := x - p; let S := A.direction
    have h_x'_in_S : x' ∈ S := AffineSubspace.vsub_mem_direction hx_in_A (mem_affineSpan ℝ hp)
    let s'' : Set S := Subtype.val ⁻¹' s'; let x'' : S := ⟨x', h_x'_in_S⟩
    have hs''_conv : Convex ℝ s'' := by
      have convex_preimage_of_linear_map :
      ∀ {t : Set E} (ht : Convex ℝ t) (f : S →ₗ[ℝ] E), Convex ℝ (f ⁻¹' t) := by
        rintro _ ht _ _ y _ hy _ _ ha hb hab
        simp only [mem_preimage, map_add, map_smul]
        exact ht y hy ha hb hab
      exact convex_preimage_of_linear_map (hs_conv.sub (convex_singleton p)) S.subtype
    have hs''_open : IsOpen s'' := by
      let p_in_A : A := ⟨p, mem_affineSpan ℝ hp⟩
      let e : A ≃ₜ S := {
        toFun := fun (x : A) => ⟨x.val - p_in_A.val,
          by exact vsub_mem_direction x.mem p_in_A.mem⟩,
        invFun := fun (v : S) => ⟨v.val + p_in_A.val,
          by exact vadd_mem_of_mem_direction v.mem p_in_A.mem⟩,
        left_inv := by rintro _; apply Subtype.ext; rw [← @eq_sub_iff_add_eq],
        right_inv := by rintro _; apply Subtype.ext; rw [@sub_eq_iff_eq_add],
        continuous_toFun  := by apply (continuous_subtype_val.sub continuous_const).subtype_mk,
        continuous_invFun := by apply (continuous_subtype_val.add continuous_const).subtype_mk}
      have h_s''_eq_image : s'' = e '' (Subtype.val ⁻¹' s) := by
        ext v
        simp only [mem_image, mem_preimage, Subtype.exists, exists_and_left]
        constructor
        rintro ⟨y, hy_s, b, hb_mem, h_eq_raw⟩
        rw [hb_mem] at h_eq_raw
        exact ⟨y, hy_s, ⟨(mem_affineSpan ℝ hy_s), Subtype.ext (h_eq_raw)⟩⟩
        rintro ⟨y, hy_s, hy_A, h_eq⟩
        apply mem_preimage.mpr
        apply Set.mem_sub.mpr
        exact ⟨y, hy_s, ⟨p, ⟨by trivial, (by rw [← h_eq]; rfl)⟩⟩⟩
      rw [h_s''_eq_image, @Homeomorph.isOpen_image, hs_rel_open]
      exact intrinsic_interior_is_open_in_affine_span s
    have hx'' : x'' ∉ s'' := by
      simp only [s'', x'', s', x', mem_preimage]
      rintro ht
      have (x p :E)(s : Set E) (h: x - p ∈ s - {p}) : x ∈ s := by
        simp only [sub_singleton, mem_image, sub_left_inj, exists_eq_right] at h
        exact h
      exact hx (this x p s ht)
    obtain ⟨g, hg_strict_sep⟩ := geometric_hahn_banach_point_open  hs''_conv hs''_open hx''
    use g.comp (orthogonalProjection S); intro a ha
    rw [@gt_iff_lt,← sub_pos, ← map_sub (g.comp (orthogonalProjection S))]
    have h_ax_in_S : a - x ∈ S := vsub_mem_direction (mem_affineSpan ℝ ha) hx_in_A
    have ha_p_in_S : a - p ∈ S := vsub_mem_direction (mem_affineSpan ℝ ha) (mem_affineSpan ℝ hp)
    rw [ContinuousLinearMap.comp_apply]
    have : S.orthogonalProjection (a - x) = ⟨a - x, h_ax_in_S⟩ := by
      exact SetLike.coe_eq_coe.mp (starProjection_eq_self_iff.mpr h_ax_in_S)
    have sep: g ⟨a - x, h_ax_in_S⟩ = g (⟨a - p, ha_p_in_S⟩ - ⟨x - p, h_x'_in_S⟩) := by
      apply DFunLike.congr rfl (SetLike.coe_eq_coe.mp (by change a - x = (a - p) - (x - p); abel))
    rw [this, sep, map_sub, @sub_pos]
    apply hg_strict_sep ⟨a - p, ha_p_in_S⟩
    simp only [s'', mem_preimage]
    exact Set.sub_mem_sub ha rfl
  obtain ⟨f, u, hfu1, hfu2⟩ :=
  geometric_hahn_banach_closed_point (A.convex) (closed_of_finiteDimensional A) hx_in_A
  use -f; intro a ha; change - (f a) > - (f x)
  simp only [gt_iff_lt, _root_.neg_lt_neg_iff]
  linarith [hfu1 a (mem_affineSpan ℝ ha)]

/- Rockafellar Thm.11.2: Let C be a nonempty relatively open convex set in R^n,
and M a nonempty affine set in R^n disjoint from C. Then there exists a hyperplane H
containing M such that the associated open halfspace contains C.
In a finite-dimensional space, any non-empty, relatively open convex set can be strictly separated
from any disjoint non-empty affine subspace by a hyperplane that fully contains the affine subspace.

The proof reduces the problem to the previous theorem of separating a point from a convex set.
It does this by orthogonally projecting the entire space onto
a subspace perpendicular to the direction
of the affine subspace M. In this projected space, M collapses to a single point,
while the convex set C projects to another convex set.
The disjointness condition ensures the projected point is outside the projected set,
allowing the previous separation theorem to be applied.
This separation is then lifted back to the original space.-/

lemma exists_hyperplane_containing_affine_subspace_separating_convex_set
    [FiniteDimensional ℝ E] (C : Set E) (hC : Convex ℝ C) (M : AffineSubspace ℝ E)
    (hc_nonempty : C.Nonempty) (hc_ri : (ri C) = C) (hcm : C ∩ M = ∅)
    (hm_nonempty : M.carrier.Nonempty) :
  ∃ (g : E →L[ℝ] ℝ) (c : ℝ), (∀x ∈ M.1 , g x = c) ∧ ∀x ∈ C , g x > c := by
  let ⟨p, hp⟩ := hm_nonempty
  let proj : E →L[ℝ] E :=
  ContinuousLinearMap.comp (subtypeL M.directionᗮ) (orthogonalProjection M.directionᗮ)
  let C' := proj '' C; let p' := proj p
  have con_C' : Convex ℝ C' := Convex.is_linear_image hC (proj.isLinear)
  have disjcp : p' ∉  C' := by
    rintro ⟨t, ht_in_C, h_proj_t_eq_p'⟩
    have h_vsub_in_direction : t - p ∈ M.direction := by
      rw [← orthogonal_orthogonal M.direction]
      apply orthogonalProjection_eq_zero_iff.mp
      apply Subtype.ext_iff.mpr
      exact (by change proj (t - p) = 0; rw [map_sub, h_proj_t_eq_p', sub_self])
    have ht_in_M : t ∈ M := (vsub_right_mem_direction_iff_mem hp t).mp h_vsub_in_direction
    have h_intersect_nonempty : (C ∩ M).Nonempty := ⟨t, ht_in_C, ht_in_M⟩
    apply nonempty_iff_ne_empty.mp h_intersect_nonempty hcm
  have hC'nonempty : C'.Nonempty := image_nonempty.mpr hc_nonempty
  have Cri : C'= (ri C') := by rw [linear_ri C proj hC, hc_ri]
  rcases (separation_point_from_convex_rel_open C' p' con_C' hC'nonempty Cri disjcp) with ⟨g, hg⟩
  use g.comp proj, g.comp proj p
  constructor <;> intro x hx
  · apply congrArg g
    rw [← sub_eq_zero, ← map_sub]
    apply ZeroMemClass.coe_eq_zero.mpr
    simp only [ContinuousLinearMap.coe_coe]
    exact orthogonalProjection_orthogonal_apply_eq_zero (vsub_mem_direction hx hp)
  simp only [ContinuousLinearMap.coe_comp', comp_apply, gt_iff_lt]
  exact hg (proj x) (mem_image_of_mem (⇑proj) hx)

lemma exists_hyperplane_containing_affine_subspace_separating_convex_set'
    [FiniteDimensional ℝ E] (C : Set E) (hC : Convex ℝ C) (M : AffineSubspace ℝ E)
    (hc_nonempty : C.Nonempty) (hc_ri : (ri C) = C) (hcm : C ∩ M = ∅)
    (hm_nonempty : (M : Set E).Nonempty) :
  ∃ (g : E →L[ℝ] ℝ) (c : ℝ), (∀x ∈ M.1 , g x = c) ∧ ∀x ∈ C , g x > c :=
  exists_hyperplane_containing_affine_subspace_separating_convex_set
    C hC M hc_nonempty hc_ri hcm hm_nonempty

-- The following prepares for discussion of 13.3, 16.2, etc.


def recessionCone (s : Set E) : ConvexCone ℝ E
  where
  carrier : Set E :=  {v | ∀ (a : ℝ), 0 ≤ a → ∀ x ∈ s, x + a • v ∈ s}
  add_mem' := by
    intro x hx y hy a ha x1 hx1
    rw [DistribSMul.smul_add, ← add_assoc]
    exact hy a ha (x1 + a • x) (hx a ha x1 hx1)
  smul_mem' := by
    intro c hc x hx a ha x1 hx1
    rw [smul_smul]
    have hac : 0 ≤ a * c := mul_nonneg ha (le_of_lt hc)
    exact hx (a * c) hac x1 hx1


section RecessionCone
/- Theorem 8.3
Let C be a nonempty closed convex set and y ≠ 0. If there exists even one x such that
the ray {x + λy | λ > 0} is contained in C, then the same holds for every x ∈ C,
so y ∈ 0 + C. Moreover, for each x ∈ ri C, the set {x + λy | λ ≥ 0} is contained in ri C,
so y ∈ 0 + (ri C). -/
theorem recessioncone_one_exist_all_exist {C : Set E}
    {x y : E} (hC_conv : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_nonempty : C.Nonempty) (y_ne_zero : y ≠ 0) (h_exist : ∃ x ∈ C, ∀ a ≥ 0, x + a • y ∈ C) :
  y ∈ recessionCone C := by

  sorry

theorem recessioncone_ri {C : Set E} {x y : E}(hC_conv : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_nonempty : C.Nonempty) (y_ne_zero : y ≠ 0) (h_exist : ∃ x ∈ C, ∀ a ≥ 0, x + a • y ∈ C) :
  y ∈ recessionCone (ri C):= by sorry


/- Corollary 8.3.1
For any nonempty set C, 0 + (ri C) = 0 + (cl C).
In fact, for any given x ∈ ri C, y ∈ 0 + (cl C) iff for all λ > 0, x + λy ∈ C. -/
theorem recessioncone_rel_eq_cl {C : Set E}(hC_nonempty : C.Nonempty) :
  recessionCone (ri C) = recessionCone (closure C) := by
  sorry

theorem recessioncone_rel_eq_cl' {C : Set E}(x y: E) (hC_nonempty : C.Nonempty) (hx : x ∈ ri C) :
  y ∈ recessionCone (closure C) ↔ ∀a > 0, x + a • y ∈ C := by
  sorry


/- Corollary 8.3.2
If C is a closed convex set containing the origin, then
0 + C = {y | ε⁻¹ • y ∈ C, ∀ ε > 0}. -/
theorem recessioncone_eq {C : Set E} (h_C_closed : IsClosed C) (h_C_convex : Convex ℝ C)
 (h0 : (0 : E) ∈ C) : recessionCone C = ({ y | ∀ (a : ℝ), a > 0 → a ⁻¹ • y ∈ C}: Set E) := by
  sorry

/- {ι : Sort*} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) : Convex 𝕜 (⋂ i, s i)-/
variable {i : Sort*} {s : i → Set E}

/- If (C_i : i ∈ I) is a family of convex sets in Rⁿ with nonempty intersection, then
0 + C = (∩ (i ∈ I) C_i, ∩ (i ∈ I) 0 + C. -/
theorem recession_cone_of_iInter_of_convex_sets
  (h_convex : ∀ i, Convex ℝ (s i)) (h_nonempty : (⋂ i, s i).Nonempty) :
  recessionCone (⋂ i, s i) = ⨅ i, recessionCone (s i) := by
  sorry

end RecessionCone

section recessionfunction_def

open EReal Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (s : Set E)

noncomputable def recessionFunction (f : E → EReal) :=
  fun y => ⨆ x ∈ {x | x ∈ dom s f}, (f (x + y) - f x)

end recessionfunction_def
