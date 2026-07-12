import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_51.Exercise_7_31

-- `lean_leansearch` is unavailable in this environment; the statement below uses the canonical
-- owners `MulAut.conjNormal`, `semidirectProductGroup`, `semidirectProductLieGroup`, and
-- `LieGroupIsomorphism`.

open scoped Manifold ContDiff Pointwise

noncomputable section

section SemidirectProductCharacterization

universe u𝕜 uE uHG uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]
local notation "LieSubgroupI" => @LieSubgroup 𝕜 _ E _ _ HG _ G _ _ _ I

variable (N H : LieSubgroupI)

namespace LieSubgroup

/-- A closed Lie subgroup has smooth inclusion into the ambient Lie group. -/
theorem subtype_contMDiff (S : LieSubgroupI) (hS_closed : IsClosed (S.carrier : Set G)) :
    ContMDiff (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) := sorry

/-- The conjugation action of one Lie subgroup on a normal Lie subgroup. -/
def conjNormalHom (N H : LieSubgroupI) [N.carrier.Normal] : H.carrier →* MulAut N.carrier :=
  (MulAut.conjNormal : G →* MulAut N.carrier).comp H.carrier.subtype

end LieSubgroup

/-- Helper for Theorem 7.35: for closed Lie subgroups `N` and `H`, the conjugation action of `H`
on the normal subgroup `N` is smooth. -/
theorem lie_subgroup_conjugation_action_contMDiff
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    ContMDiff
      ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
      (modelWithCornersSelf 𝕜 N.ModelSpace) (∞ : ℕ∞ω)
      (fun p : H.carrier × N.carrier ↦ θ p.1 p.2) := sorry

/-- The textbook multiplication map `(n, h) ↦ nh` from the product of subgroup types into the
ambient Lie group. -/
def semidirect_product_multiplication : N.carrier × H.carrier → G :=
  fun p ↦ p.1.1 * p.2.1

/-- Under the internal-product hypotheses `N ∩ H = {e}` and `NH = G`, the textbook multiplication
map `(n, h) ↦ nh` is bijective. -/
theorem semidirect_product_multiplication_bijective
    (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    Function.Bijective (semidirect_product_multiplication N H) := by
  simpa [semidirect_product_multiplication] using
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hNH

/-- The textbook multiplication map is multiplicative for the semidirect-product group law on
`N × H` coming from conjugation of `H` on the normal subgroup `N`. -/
theorem semidirect_product_multiplication_map_mul
    [N.carrier.Normal] (a b : N.carrier × H.carrier) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    semidirect_product_multiplication N H (a.1 * θ a.2 b.1, a.2 * b.2) =
      semidirect_product_multiplication N H a * semidirect_product_multiplication N H b := sorry

/-- Under the internal-product hypotheses `N ∩ H = {e}` and `NH = G`, the textbook multiplication
map `(n, h) ↦ nh` is a local diffeomorphism for the product manifold structure on `N × H`.
Combined with bijectivity, this gives the global Lie-group isomorphism in Theorem 7.35. -/
theorem semidirect_product_multiplication_isLocalDiffeomorph
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    IsLocalDiffeomorph
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (∞ : ℕ∞ω) (semidirect_product_multiplication N H) := sorry

/-- Theorem 7.35: if `N` and `H` are closed Lie subgroups of a Lie group `G`, with `N` normal,
`N ∩ H = {e}` (encoded as `Disjoint N.carrier H.carrier`), and `NH = G`, then the multiplication
map `(n, h) ↦ nh` identifies the semidirect product `N ⋊_θ H` with `G` as a Lie group. Here the
semidirect product is realized on the product manifold `N × H` using the conjugation action of `H`
on `N`. -/
noncomputable def semidirect_product_lie_group_isomorphism
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff
          I N H hN_closed hH_closed)
    LieGroupIsomorphism
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (N.carrier × H.carrier) G :=
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff
        I N H hN_closed hH_closed)
  let hLocal :=
    semidirect_product_multiplication_isLocalDiffeomorph
      I N H hN_closed hH_closed hdisj hNH
  let Φ :=
    hLocal.diffeomorphOfBijective (semidirect_product_multiplication_bijective N H hdisj hNH)
  { toDiffeomorph := Φ
    map_mul' := sorry }

@[simp] theorem semidirect_product_lie_group_isomorphism_apply
    (_hN_closed : IsClosed (N.carrier : Set G)) (_hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ)
    (p : N.carrier × H.carrier) :
    semidirect_product_lie_group_isomorphism I N H _hN_closed _hH_closed hdisj hNH p =
      semidirect_product_multiplication N H p := rfl

end SemidirectProductCharacterization

section SemidirectProductCharacterizationBridge

universe u𝕜' uE' uHG' uG' uEN uHN uEH uHH

variable {𝕜 : Type u𝕜'} [NontriviallyNormedField 𝕜]
variable {E : Type uE'} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG'} [TopologicalSpace HG]
variable {G : Type uG'} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable (I_N : ModelWithCorners 𝕜 EN HN) (I_H : ModelWithCorners 𝕜 EH HH)
variable (N H : Subgroup G)
variable [ChartedSpace HN N] [ChartedSpace HH H]
variable [LieGroup I_N (∞ : ℕ∞ω) N] [LieGroup I_H (∞ : ℕ∞ω) H]

private def subgroup_data_multiplication : N × H → G :=
  fun p ↦ p.1.1 * p.2.1

private theorem subgroup_data_conjugation_action_contMDiff
    (hN_subtype : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype)
    (hH_subtype : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype)
    (hN_closed : IsClosed (N : Set G)) (hH_closed : IsClosed (H : Set G)) [N.Normal] :
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    ContMDiff (I_H.prod I_N) I_N (∞ : ℕ∞ω) (fun p : H × N ↦ θ p.1 p.2) := sorry

private theorem subgroup_data_multiplication_bijective
    {G : Type uG'} [Group G] (N H : Subgroup G)
    (hdisj : Disjoint N H) (hNH : (N : Set G) * (H : Set G) = Set.univ) :
    Function.Bijective (subgroup_data_multiplication N H) := by
  simpa [subgroup_data_multiplication] using
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hNH : N.IsComplement' H)

private theorem subgroup_data_multiplication_isLocalDiffeomorph
    (hN_subtype : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype)
    (hH_subtype : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype)
    (hN_closed : IsClosed (N : Set G)) (hH_closed : IsClosed (H : Set G)) [N.Normal]
    (hdisj : Disjoint N H) (hNH : (N : Set G) * (H : Set G) = Set.univ) :
    IsLocalDiffeomorph (I_N.prod I_H) I (∞ : ℕ∞ω) (subgroup_data_multiplication N H) := sorry

/-- Bridge view of Theorem 7.35 on raw subgroup-presentation data. The canonical owner-level
statement is `semidirect_product_lie_group_isomorphism`. -/
noncomputable def semidirect_product_lie_group_isomorphism_of_subgroup_data
    (hN_subtype : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype)
    (hH_subtype : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype)
    (hN_closed : IsClosed (N : Set G)) (hH_closed : IsClosed (H : Set G))
    [N.Normal] (hdisj : Disjoint N H) (hNH : (N : Set G) * (H : Set G) = Set.univ) :
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) (∞ : ℕ∞ω) (N × H) :=
      semidirectProductLieGroup θ
        (subgroup_data_conjugation_action_contMDiff
          I I_N I_H N H hN_subtype hH_subtype hN_closed hH_closed)
    LieGroupIsomorphism (I_N.prod I_H) I (N × H) G :=
  let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) (∞ : ℕ∞ω) (N × H) :=
    semidirectProductLieGroup θ
      (subgroup_data_conjugation_action_contMDiff
        I I_N I_H N H hN_subtype hH_subtype hN_closed hH_closed)
  let hLocal :=
    subgroup_data_multiplication_isLocalDiffeomorph
      I I_N I_H N H hN_subtype hH_subtype hN_closed hH_closed hdisj hNH
  let Φ :=
    hLocal.diffeomorphOfBijective
      (subgroup_data_multiplication_bijective N H hdisj hNH)
  { toDiffeomorph := Φ
    map_mul' := sorry }

@[simp] theorem semidirect_product_lie_group_isomorphism_of_subgroup_data_apply
    (hN_subtype : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype)
    (hH_subtype : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype)
    (hN_closed : IsClosed (N : Set G)) (hH_closed : IsClosed (H : Set G))
    [N.Normal] (hdisj : Disjoint N H) (hNH : (N : Set G) * (H : Set G) = Set.univ)
    (p : N × H) :
    semidirect_product_lie_group_isomorphism_of_subgroup_data I I_N I_H N H
      hN_subtype hH_subtype hN_closed hH_closed hdisj hNH p =
      p.1.1 * p.2.1 := rfl

end SemidirectProductCharacterizationBridge
