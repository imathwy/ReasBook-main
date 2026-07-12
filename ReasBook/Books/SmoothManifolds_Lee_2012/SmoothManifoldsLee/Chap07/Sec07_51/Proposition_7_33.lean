import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Complement

open SemidirectProduct
open scoped Pointwise

section Proposition733

variable {N H : Type*} [Group N] [Group H]
variable (φ : H →* MulAut N)

/-- Proposition 7.33 (1). The canonical homomorphism from `N` onto `\tilde N` is bijective. -/
theorem proposition_7_33_tildeN_rangeRestrict_bijective
    :
    Function.Bijective
      ((inl : N →* N ⋊[φ] H).rangeRestrict : N → (inl : N →* N ⋊[φ] H).range) := by
  refine ⟨?_, (inl : N →* N ⋊[φ] H).rangeRestrict_surjective⟩
  simpa using ((inl : N →* N ⋊[φ] H).rangeRestrict_injective_iff).2 inl_injective

/-- Proposition 7.33 (2). The canonical homomorphism from `H` onto `\tilde H` is bijective. -/
theorem proposition_7_33_tildeH_rangeRestrict_bijective
    :
    Function.Bijective
      ((inr : H →* N ⋊[φ] H).rangeRestrict : H → (inr : H →* N ⋊[φ] H).range) := by
  refine ⟨?_, (inr : H →* N ⋊[φ] H).rangeRestrict_surjective⟩
  simpa using ((inr : H →* N ⋊[φ] H).rangeRestrict_injective_iff).2 inr_injective

/-- Proposition 7.33 (3). The subgroup `\tilde N` is normal in the semidirect product. -/
theorem proposition_7_33_tildeN_normal
    :
    ((inl : N →* N ⋊[φ] H).range).Normal := by
  simpa [range_inl_eq_ker_rightHom] using
    (show ((rightHom : N ⋊[φ] H →* H).ker).Normal from inferInstance)

/-- Canonical owner for Proposition 7.33 (4) and (5): the subgroups `\tilde N` and `\tilde H`
form a complementary pair in the semidirect product. -/
theorem proposition_7_33_tildeN_isComplement'
    :
    ((inl : N →* N ⋊[φ] H).range).IsComplement' ((inr : H →* N ⋊[φ] H).range) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro g hgN hgH
    rcases hgN with ⟨n, rfl⟩
    rcases hgH with ⟨h, hh⟩
    have hn : n = 1 := by
      simpa using congrArg SemidirectProduct.left hh.symm
    simp [hn]
  · refine Set.eq_univ_iff_forall.mpr fun g ↦ ?_
    exact ⟨inl g.left, ⟨g.left, rfl⟩, inr g.right, ⟨g.right, rfl⟩, inl_left_mul_inr_right g⟩

/-- Proposition 7.33 (4). The intersection `\tilde N ∩ \tilde H` is the singleton `{(e, e)}`. -/
theorem proposition_7_33_tildeN_inter_tildeH
    :
    (((inl : N →* N ⋊[φ] H).range : Set (N ⋊[φ] H)) ∩
        ((inr : H →* N ⋊[φ] H).range : Set (N ⋊[φ] H))) =
      ({(1 : N ⋊[φ] H)} : Set (N ⋊[φ] H)) := by
  ext g
  constructor
  · intro hg
    have hg1 : g = 1 := (Subgroup.disjoint_def.mp
      (proposition_7_33_tildeN_isComplement' φ).disjoint) hg.1 hg.2
    simp [hg1]
  · intro hg
    simp only [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-- Proposition 7.33 (5). Every element of the semidirect product factors as `\tilde N \tilde H`. -/
theorem proposition_7_33_tildeN_mul_tildeH
    (g : N ⋊[φ] H) : ∃ n : N, ∃ h : H, (inl n : N ⋊[φ] H) * inr h = g := by
  have hg :
      g ∈ (((inl : N →* N ⋊[φ] H).range : Set (N ⋊[φ] H)) *
        ((inr : H →* N ⋊[φ] H).range : Set (N ⋊[φ] H))) :=
    Set.eq_univ_iff_forall.mp (proposition_7_33_tildeN_isComplement' φ).mul_eq g
  rcases hg with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨n, rfl⟩
  rcases hy with ⟨h, rfl⟩
  exact ⟨n, h, hxy⟩

end Proposition733
