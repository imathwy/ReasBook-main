import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_51.Theorem_7_35

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` is unavailable in this environment; repository inspection verified that
-- `semidirect_product_lie_group_isomorphism` is the canonical local owner-level bridge for this
-- item.

open scoped Manifold ContDiff Pointwise

section

universe u𝕜 uE uHG uG uEN uHN uEH uHH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable (I_N : ModelWithCorners 𝕜 EN HN) (I_H : ModelWithCorners 𝕜 EH HH)
variable (N H : Subgroup G)
variable [ChartedSpace HN N] [ChartedSpace HH H]
variable [LieGroup I_N (∞ : ℕ∞ω) N] [LieGroup I_H (∞ : ℕ∞ω) H]

/-- Definition 7.51-extra-2: under the hypotheses of Theorem 7.35, the ambient Lie group `G` is
the internal semidirect product of the subgroups `N` and `H`. -/
class IsInternalSemidirectProduct : Prop where
  /-- The subgroup inclusion `N ↪ G` is smooth for the chosen Lie-group structure on `N`. -/
  n_subtype_contMDiff : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype
  /-- The subgroup inclusion `H ↪ G` is smooth for the chosen Lie-group structure on `H`. -/
  h_subtype_contMDiff : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype
  /-- The subgroup `N` is closed in `G`. -/
  n_closed : IsClosed (N : Set G)
  /-- The subgroup `H` is closed in `G`. -/
  h_closed : IsClosed (H : Set G)
  /-- The subgroup `N` is normal in `G`. -/
  normal : N.Normal
  /-- The intersection of `N` and `H` is trivial, encoded by disjointness. -/
  disjoint : Disjoint N H
  /-- Every element of `G` is a product of an element of `N` and an element of `H`. -/
  mul_eq_univ : (N : Set G) * (H : Set G) = Set.univ

/-- The proposition of being an internal semidirect product is subsingleton. -/
instance isInternalSemidirectProduct_subsingleton :
    Subsingleton (IsInternalSemidirectProduct I I_N I_H N H) := inferInstance

/-- In an internal semidirect product, the induced conjugation action of `H` on `N` is smooth. -/
theorem internal_semidirect_product_conjugation_action_contMDiff
    (h : IsInternalSemidirectProduct I I_N I_H N H) :
    let _ : N.Normal := h.normal
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    ContMDiff (I_H.prod I_N) I_N (∞ : ℕ∞ω) (fun p : H × N ↦ θ p.1 p.2) := sorry

/-- Theorem 7.35 applies to an internal semidirect product, yielding a Lie-group isomorphism from
the corresponding semidirect product onto `G`. -/
noncomputable def internal_semidirect_product_lie_group_isomorphism
    (h : IsInternalSemidirectProduct I I_N I_H N H) :
    let _ : N.Normal := h.normal
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) (∞ : ℕ∞ω) (N × H) :=
      semidirectProductLieGroup θ
        (internal_semidirect_product_conjugation_action_contMDiff I I_N I_H N H h)
    LieGroupIsomorphism (I_N.prod I_H) I (N × H) G :=
  let _ : N.Normal := h.normal
  semidirect_product_lie_group_isomorphism_of_subgroup_data I I_N I_H N H
    h.n_subtype_contMDiff h.h_subtype_contMDiff h.n_closed h.h_closed h.disjoint h.mul_eq_univ

@[simp] theorem internal_semidirect_product_lie_group_isomorphism_apply
    (h : IsInternalSemidirectProduct I I_N I_H N H) (p : N × H) :
    internal_semidirect_product_lie_group_isomorphism I I_N I_H N H h p =
      p.1.1 * p.2.1 := by
  let _ : N.Normal := h.normal
  simp [internal_semidirect_product_lie_group_isomorphism]

end
