module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

public section

universe u v

namespace Monoid.Coprod

/-- Helper for Exercise 68.3: the first-factor retraction sends a conjugated
first-factor element to the corresponding conjugate in `G₁`. -/
private lemma fst_conj_inl {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    (c : G₁ ∗ G₂) (x : G₁) :
    fst ((MulAut.conj c) (inl x)) = fst c * x * (fst c)⁻¹ := by
  -- Expand conjugation, then evaluate the retraction on each factor.
  simp only [MulAut.conj_apply, map_mul, map_inv, fst_apply_inl]

/-- Helper for Exercise 68.3: a conjugated first-factor element lying in the
second-factor range must come from the identity of `G₁`. -/
private lemma eq_one_of_conj_inl_mem_range_inr {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (c : G₁ ∗ G₂) (x : G₁)
    (h : (MulAut.conj c) (inl x) ∈ MonoidHom.range (inr : G₂ →* G₁ ∗ G₂)) :
    x = 1 := by
  -- A range witness becomes the identity after applying the first-factor retraction.
  rcases MonoidHom.mem_range.mp h with ⟨y, hy⟩
  have retracted := congrArg (fst : G₁ ∗ G₂ →* G₁) hy
  have conjugate_eq_one : fst c * x * (fst c)⁻¹ = 1 := by
    simpa only [fst_conj_inl, fst_apply_inr] using retracted.symm
  -- Conjugate back inside `G₁` to cancel the two copies of `fst c`.
  have canceled :=
    congrArg (fun z : G₁ ↦ (fst c)⁻¹ * z * fst c) conjugate_eq_one
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
    one_mul, mul_one] using canceled

/-- Exercise 68.3: In the free product of `G₁` and `G₂`, the subgroup obtained by
mapping the first-factor range under conjugation by `c` (the source's `cG₁c⁻¹`)
is disjoint from the second-factor range, so their intersection contains only the identity. -/
theorem disjoint_conj_range_inl_range_inr {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (c : G₁ ∗ G₂) :
    Disjoint
      ((MonoidHom.range (inl : G₁ →* G₁ ∗ G₂)).map (MulAut.conj c))
      (MonoidHom.range (inr : G₂ →* G₁ ∗ G₂)) := by
  -- Reduce disjointness to proving that an arbitrary common element is the identity.
  rw [Subgroup.disjoint_def]
  intro y hy_conj hy_inr
  -- Unpack the mapped subgroup and then the first-factor range witness.
  rcases Subgroup.mem_map.mp hy_conj with ⟨z, hz, hzy⟩
  rcases MonoidHom.mem_range.mp hz with ⟨x, hxz⟩
  rw [← hxz] at hzy
  have hconj_inr :
      (MulAut.conj c) (inl x) ∈ MonoidHom.range (inr : G₂ →* G₁ ∗ G₂) := by
    exact hzy ▸ hy_inr
  -- The retraction forces the source element to be `1`, so the common element is `1`.
  have hx_one := eq_one_of_conj_inl_mem_range_inr c x hconj_inr
  subst x
  simpa only [map_one] using hzy.symm

end Monoid.Coprod
