import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Subgroup

variable {G : Type u} [Group G]

/-- Helper for Lemma 8-8.5-1: a nontrivial supersolvable group has a nontrivial normal cyclic
subgroup, obtained from the first nontrivial term of a supersolvable series. -/
lemma exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable
    {Q : Type u} [Group Q] [IsSupersolvable Q] [Nontrivial Q] :
    ∃ B : Subgroup Q, B.Normal ∧ B ≠ ⊥ ∧ IsCyclic B := by
  classical
  let hsup : IsSupersolvable Q := inferInstance
  rcases hsup.supersolvable with ⟨n, f, _, hnormal, hcyclic, h0, hn⟩
  -- Pick the earliest nontrivial term in the finite series by minimizing the index.
  have hex : ∃ m, m ≤ n ∧ f m ≠ ⊥ := by
    refine ⟨n, le_rfl, ?_⟩
    simp [hn]
  let m := Nat.find hex
  have hm_le_n : m ≤ n := (Nat.find_spec hex).1
  have hm_ne_bot : f m ≠ ⊥ := (Nat.find_spec hex).2
  have hm_min : ∀ k, k < m → f k = ⊥ := by
    intro k hk
    by_contra hk_ne_bot
    have hk_witness : k ≤ n ∧ f k ≠ ⊥ :=
      ⟨Nat.le_trans (Nat.le_of_lt hk) hm_le_n, hk_ne_bot⟩
    exact Nat.find_min hex hk hk_witness
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    apply hm_ne_bot
    simp [m, hm0, h0]
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hk1_le_n : k + 1 ≤ n := by
    simpa [m, hk_eq] using hm_le_n
  have hk_lt : k < n := Nat.lt_of_succ_le hk1_le_n
  have hk_bot : f k = ⊥ := hm_min k (by simp [m, hk_eq])
  -- The first nontrivial term is normal, and its quotient by the previous trivial term is cyclic.
  have hk1_normal : (f (k + 1)).Normal := by
    by_cases hk1_lt_n : k + 1 < n
    · exact hnormal (k + 1) hk1_lt_n
    · have hk1_eq_n : k + 1 = n := le_antisymm hk1_le_n (Nat.le_of_not_gt hk1_lt_n)
      rw [hk1_eq_n, hn]
      infer_instance
  refine ⟨f (k + 1), hk1_normal, ?_, ?_⟩
  · simpa [m, hk_eq] using hm_ne_bot
  · letI : (f k).Normal := hnormal k hk_lt
    letI : ((f k).subgroupOf (f (k + 1))).Normal := (hnormal k hk_lt).subgroupOf (f (k + 1))
    let e : f (k + 1) ⧸ (f k).subgroupOf (f (k + 1)) ≃* f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1))) :=
        QuotientGroup.quotientMulEquivOfEq (by simp [hk_bot])
    -- Replace the trivial predecessor by `⊥`, then remove the trivial quotient.
    have hcyc_quot : IsCyclic (f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1)))) :=
      e.isCyclic.mp (hcyclic k hk_lt)
    exact (QuotientGroup.quotientBot (G := f (k + 1))).isCyclic.mp hcyc_quot

/-- Helper for Lemma 8-8.5-1: elements of the ambient center remain central after restricting to a
subgroup. -/
lemma center_subgroupOf_le_center (A : Subgroup G) : (center G).subgroupOf A ≤ center A := by
  intro x hx
  change x.1 ∈ center G at hx
  -- Ambient centrality immediately implies centrality against every element of the subgroup.
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  exact Subtype.ext (hx y.1)

/-- Helper for Lemma 8-8.5-1: the pullback of a cyclic subgroup of `G ⧸ center G` is
commutative. -/
lemma isMulCommutative_comap_center_of_isCyclic (B : Subgroup (G ⧸ center G))
    (hB : IsCyclic B) :
    IsMulCommutative (B.comap (QuotientGroup.mk' (center G))) := by
  let q : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  let A : Subgroup G := B.comap q
  have hmap : A.map q = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center G)) B
  have hcyc : IsCyclic (A.map q) := by
    rw [hmap]
    exact hB
  let φ : A →* A.map q := q.subgroupMap A
  have hker : φ.ker ≤ center A := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact center_subgroupOf_le_center A
  letI : IsCyclic (A.map q) := hcyc
  -- The restricted quotient map has cyclic image and central kernel, so the pullback is abelian.
  rw [show B.comap (QuotientGroup.mk' (center G)) = A by rfl, isMulCommutative_iff]
  intro a b
  exact commutative_of_cyclic_center_quotient φ hker a b

/-- Helper for Lemma 8-8.5-1: the pullback of a nontrivial subgroup of `G ⧸ center G` is not
contained in `center G`. -/
lemma comap_center_not_le_center_of_nontrivial (B : Subgroup (G ⧸ center G)) (hB : B ≠ ⊥) :
    ¬ B.comap (QuotientGroup.mk' (center G)) ≤ center G := by
  let q : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  intro hle
  have hmap : (B.comap q).map q = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center G)) B
  have hbot : (B.comap q).map q ≤ ⊥ := by
    calc
      (B.comap q).map q ≤ (center G).map q := Subgroup.map_mono hle
      _ = ⊥ := QuotientGroup.map_mk'_self (center G)
  -- Mapping the pullback into the quotient would force `B` to be trivial, contradicting `hB`.
  apply hB
  rw [← hmap]
  exact le_antisymm hbot bot_le

variable [IsSupersolvable G]

-- Source/core/bridge triage:
-- * `source-facing`: the lemma asserts existence of a normal commutative subgroup not contained in
--   the center.
-- * `core/canonical`: the ambient owner notions are `IsSupersolvable G`,
--   `IsSupersolvableSeries`, and `center G`.
-- * `bridge/view`: the quotient closure result
--   `supersolvable_quotient_of_supersolvable` for `G ⧸ center G` from Exercise `8-8.3-9` is
--   proof-only support, not a second owner in this file.
--
-- Proof sketch: let `C = Subgroup.center G` and pass to the supersolvable quotient `G ⧸ C`.
-- Choose the first nontrivial term in a cyclic normal series of that quotient; its inverse image in
-- `G` is normal and abelian, and if it were contained in the center then the quotient term would be
-- trivial, contradicting the choice. The nonabelian hypothesis and `center_eq_top_iff` rule out
-- the degenerate case `center G = ⊤`.
/-- Lemma 8-8.5-1: a nonabelian supersolvable group has a normal commutative subgroup that is not
contained in the center. -/
theorem exists_normal_commutative_subgroup_not_le_center_of_nonabelian_supersolvable
    (hnonabelian : ¬ IsMulCommutative G) :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ ¬ A ≤ center G := by
  have hcenter_ne_top : center G ≠ ⊤ := by
    intro hcenter_top
    apply hnonabelian
    exact Subgroup.center_eq_top_iff.mp hcenter_top
  letI : Nontrivial (G ⧸ center G) := QuotientGroup.nontrivial_iff.mpr hcenter_ne_top
  letI : IsSupersolvable (G ⧸ center G) := supersolvable_quotient_of_supersolvable (center G)
  -- Follow the source proof: choose a first nontrivial cyclic quotient term in `G ⧸ center G`.
  obtain ⟨B, hBnormal, hBne, hBcyc⟩ :=
    exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable (Q := G ⧸ center G)
  refine ⟨B.comap (QuotientGroup.mk' (center G)), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.comap hBnormal (QuotientGroup.mk' (center G))
  · exact isMulCommutative_comap_center_of_isCyclic B hBcyc
  · exact comap_center_not_le_center_of_nontrivial B hBne

end
