module

public import Topology_Munkres_2000.Book.Definition_68_3.FreeProduct

public section

namespace Subgroup

open scoped FreeProduct

universe u v

variable {G : Type u} {ι : Type v} [Group G]

namespace ReducedWord

/-- Helper for Proposition 68.1: reversing a list of inverted letters preserves separation
between adjacent subgroup letters. -/
private lemma invReverseChainSeparated (H : ι → Subgroup G) {l : List G}
    (hl : l.IsChain (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i))) :
    ((l.map fun x ↦ x⁻¹).reverse).IsChain
      (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i)) := by
  -- Reverse the chain and use invariance of subgroup membership under inversion.
  rw [List.isChain_reverse, List.isChain_map]
  exact hl.imp fun x y hxy i h_membership ↦
    hxy i ⟨(H i).inv_mem_iff.mp h_membership.2,
      (H i).inv_mem_iff.mp h_membership.1⟩

/-- Helper for Proposition 68.1: distinct specified subgroup indices force two nonidentity
letters to be separated. -/
private lemma separatedOfIndicesNe (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    {x y : G} {i j : ι} (hx : x ∈ H i) (hy : y ∈ H j)
    (hx_ne_one : x ≠ 1) (hy_ne_one : y ≠ 1) (hij : i ≠ j) :
    ∀ k, ¬ (x ∈ H k ∧ y ∈ H k) := by
  -- Unique subgroup membership would identify both displayed indices with any common one.
  have hx_unique :=
    existsUnique_mem_of_pairwise_disjoint h_disjoint hx_ne_one ⟨i, hx⟩
  have hy_unique :=
    existsUnique_mem_of_pairwise_disjoint h_disjoint hy_ne_one ⟨j, hy⟩
  intro k hk
  exact hij ((hx_unique.unique hx hk.1).trans (hy_unique.unique hy hk.2).symm)

/-- Helper for Proposition 68.1: replacing the left letter by a nonidentity letter from the
same subgroup preserves separation from the right letter. -/
private lemma separatedReplaceLeftOfSameSubgroup (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    {x y z : G} {i : ι} (hx : x ∈ H i) (hz : z ∈ H i) (hz_ne_one : z ≠ 1)
    (hxy : ∀ k, ¬ (x ∈ H k ∧ y ∈ H k)) :
    ∀ k, ¬ (z ∈ H k ∧ y ∈ H k) := by
  -- Uniqueness for the replacement letter transports the old membership to a common index.
  have hz_unique :=
    existsUnique_mem_of_pairwise_disjoint h_disjoint hz_ne_one ⟨i, hz⟩
  intro k hk
  have hik : i = k := hz_unique.unique hz hk.1
  exact hxy k ⟨hik ▸ hx, hk.2⟩

/-- Helper for Proposition 68.1: every nonempty reduced word splits into its first letter and
a reduced tail, with the first letter's subgroup data recorded. -/
private lemma existsHeadTail (H : ι → Subgroup G) (w : ReducedWord H)
    (hw : w.toList ≠ []) :
    ∃ x i, ∃ r : ReducedWord H,
      w.toList = x :: r.toList ∧ x ∈ H i ∧ x ≠ 1 := by
  cases h_list : w.toList with
  | nil =>
      exact (hw h_list).elim
  | cons x xs =>
      have h_tail_mem : ∀ z ∈ xs, ∃ i, z ∈ H i := by
        intro z hz
        exact w.toWord.mem_subgroup z (h_list.symm ▸ List.mem_cons_of_mem x hz)
      have h_tail_ne : ∀ z ∈ xs, z ≠ 1 := by
        intro z hz
        exact w.ne_one z (h_list.symm ▸ List.mem_cons_of_mem x hz)
      have h_tail_chain :
          xs.IsChain (fun a b ↦ ∀ i, ¬ (a ∈ H i ∧ b ∈ H i)) := by
        have hw_chain := w.chain_separated
        rw [h_list] at hw_chain
        exact hw_chain.tail
      let r := ofList H xs h_tail_mem h_tail_ne h_tail_chain
      obtain ⟨i, hxi⟩ := w.toWord.mem_subgroup x (h_list.symm ▸ List.mem_cons_self)
      have hx_ne_one : x ≠ 1 :=
        w.ne_one x (h_list.symm ▸ List.mem_cons_self)
      refine ⟨x, i, r, ?_, hxi, hx_ne_one⟩
      simp only [r, toList_ofList]

/-- Helper for Proposition 68.1: reduced words with equal underlying lists are equal. -/
private lemma eqOfToListEq (H : ι → Subgroup G) {u v : ReducedWord H}
    (h : u.toList = v.toList) : u = v := by
  -- Structure injectivity discards the proof fields at both the reduced-word and word levels.
  cases u with
  | mk uWord uNe uChain =>
      cases v with
      | mk vWord vNe vChain =>
          rw [ReducedWord.mk.injEq]
          cases uWord with
          | mk uList uMem =>
              cases vWord with
              | mk vList vMem =>
                  rw [Word.mk.injEq]
                  exact h

/-- Helper for Proposition 68.1: nonempty reduced words with the same product have the same
first letter when the empty word is the only reduced representative of `1`. -/
private lemma head_eq_of_prod_eq (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (h_unique_one : ∀ w : ReducedWord H, w.prod = 1 → w = empty H)
    {u v uTail vTail : ReducedWord H} {x y : G}
    (hu : u.toList = x :: uTail.toList)
    (hv : v.toList = y :: vTail.toList) (h_prod : u.prod = v.prod) :
    x = y := by
  classical
  -- Record the subgroup data and the displayed chain decompositions of both heads.
  obtain ⟨i, hxi⟩ := u.toWord.mem_subgroup x (hu.symm ▸ List.mem_cons_self)
  obtain ⟨j, hyj⟩ := v.toWord.mem_subgroup y (hv.symm ▸ List.mem_cons_self)
  have hx_ne_one : x ≠ 1 := u.ne_one x (hu.symm ▸ List.mem_cons_self)
  have hy_ne_one : y ≠ 1 := v.ne_one y (hv.symm ▸ List.mem_cons_self)
  have hu_chain := u.chain_separated
  have hv_chain := v.chain_separated
  rw [hu] at hu_chain
  rw [hv] at hv_chain
  have hu_prod : u.prod = x * uTail.prod := by
    rw [prod_def H u, hu, List.prod_cons, ← prod_def H uTail]
  have hv_prod : v.prod = y * vTail.prod := by
    rw [prod_def H v, hv, List.prod_cons, ← prod_def H vTail]
  have h_indices : i = j := by
    by_contra hij
    -- With distinct head indices, inverse `v` followed by `u` is itself a nonempty reduced word.
    have h_inv_v := invReverseChainSeparated H v.chain_separated
    rw [hv, List.map_cons, List.reverse_cons] at h_inv_v
    have h_first_mem :
        ∀ z ∈ (vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
            y⁻¹ :: x :: uTail.toList,
          ∃ k, z ∈ H k := by
      intro z hz
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | hz | hz | hz
      · rw [List.mem_reverse, List.mem_map] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        obtain ⟨k, hak⟩ := vTail.toWord.mem_subgroup a ha
        exact ⟨k, (H k).inv_mem hak⟩
      · subst z
        exact ⟨j, (H j).inv_mem hyj⟩
      · subst z
        exact ⟨i, hxi⟩
      · exact uTail.toWord.mem_subgroup z hz
    have h_first_ne :
        ∀ z ∈ (vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
            y⁻¹ :: x :: uTail.toList,
          z ≠ 1 := by
      intro z hz
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | hz | hz | hz
      · rw [List.mem_reverse, List.mem_map] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        exact inv_ne_one.mpr (vTail.ne_one a ha)
      · subst z
        exact inv_ne_one.mpr hy_ne_one
      · subst z
        exact hx_ne_one
      · exact uTail.ne_one z hz
    have h_first_chain :
        ((vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
            y⁻¹ :: x :: uTail.toList).IsChain
          (fun a b ↦ ∀ k, ¬ (a ∈ H k ∧ b ∈ H k)) := by
      rw [List.isChain_append_cons_cons]
      exact ⟨h_inv_v,
        separatedOfIndicesNe H h_disjoint ((H j).inv_mem hyj) hxi
          (inv_ne_one.mpr hy_ne_one) hx_ne_one (Ne.symm hij),
        hu_chain⟩
    let firstWord := ofList H
      ((vTail.toList.map (fun a ↦ a⁻¹)).reverse ++ y⁻¹ :: x :: uTail.toList)
      h_first_mem h_first_ne h_first_chain
    have h_first_prod : firstWord.prod = 1 := by
      calc
        firstWord.prod =
            vTail.prod⁻¹ * (y⁻¹ * (x * uTail.prod)) := by
          simp only [firstWord, prod_def, toList_ofList, List.prod_append,
            ← List.prod_inv_reverse, List.prod_cons]
        _ = (y * vTail.prod)⁻¹ * (x * uTail.prod) := by
          simp only [mul_inv_rev, mul_assoc]
        _ = v.prod⁻¹ * u.prod := by rw [hu_prod, hv_prod]
        _ = 1 := by
          rw [h_prod]
          exact inv_mul_eq_one.mpr rfl
    have h_first_empty := congrArg (fun w : ReducedWord H ↦ w.toList)
      (h_unique_one firstWord h_first_prod)
    simp only [firstWord, toList_ofList, toWord_empty, Word.toList_empty] at h_first_empty
    exact (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil y⁻¹ _)) h_first_empty
  subst j
  by_contra hxy
  -- Once the head indices agree, merge `y⁻¹ * x`; if it were nonidentity, the merged
  -- inverse-tail word would again be a nonempty reduced representative of `1`.
  have h_merged_ne : y⁻¹ * x ≠ 1 := by
    intro h_merged
    exact hxy (inv_mul_eq_one.mp h_merged).symm
  have h_merged_mem : y⁻¹ * x ∈ H i :=
    (H i).mul_mem ((H i).inv_mem hyj) hxi
  have h_right_chain :
      (y⁻¹ * x :: uTail.toList).IsChain
        (fun a b ↦ ∀ k, ¬ (a ∈ H k ∧ b ∈ H k)) := by
    apply hu_chain.imp_head
    intro a hxa
    exact separatedReplaceLeftOfSameSubgroup H h_disjoint hxi h_merged_mem h_merged_ne hxa
  have h_second_chain :
      ((vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
          (y⁻¹ * x) :: uTail.toList).IsChain
        (fun a b ↦ ∀ k, ¬ (a ∈ H k ∧ b ∈ H k)) := by
    cases h_tail : vTail.toList with
    | nil =>
        simpa only [h_tail, List.map_nil, List.reverse_nil, List.nil_append] using h_right_chain
    | cons a as =>
        have h_inv_tail := invReverseChainSeparated H vTail.chain_separated
        rw [h_tail, List.map_cons, List.reverse_cons] at h_inv_tail
        have h_y_a : ∀ k, ¬ (y ∈ H k ∧ a ∈ H k) := by
          rw [h_tail, List.isChain_cons_cons] at hv_chain
          exact hv_chain.1
        have h_y_ainv : ∀ k, ¬ (y ∈ H k ∧ a⁻¹ ∈ H k) := by
          intro k hk
          exact h_y_a k ⟨hk.1, (H k).inv_mem_iff.mp hk.2⟩
        have h_merged_ainv :
            ∀ k, ¬ (y⁻¹ * x ∈ H k ∧ a⁻¹ ∈ H k) :=
          separatedReplaceLeftOfSameSubgroup H h_disjoint hyj h_merged_mem
            h_merged_ne h_y_ainv
        have h_ainv_merged :
            ∀ k, ¬ (a⁻¹ ∈ H k ∧ y⁻¹ * x ∈ H k) := by
          intro k hk
          exact h_merged_ainv k ⟨hk.2, hk.1⟩
        simp only [List.map_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append, List.isChain_append_cons_cons]
        exact ⟨h_inv_tail, h_ainv_merged, h_right_chain⟩
  have h_second_mem :
      ∀ z ∈ (vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
          (y⁻¹ * x) :: uTail.toList,
        ∃ k, z ∈ H k := by
    intro z hz
    simp only [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | hz | hz
    · rw [List.mem_reverse, List.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨k, hak⟩ := vTail.toWord.mem_subgroup a ha
      exact ⟨k, (H k).inv_mem hak⟩
    · subst z
      exact ⟨i, h_merged_mem⟩
    · exact uTail.toWord.mem_subgroup z hz
  have h_second_ne :
      ∀ z ∈ (vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
          (y⁻¹ * x) :: uTail.toList,
        z ≠ 1 := by
    intro z hz
    simp only [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | hz | hz
    · rw [List.mem_reverse, List.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      exact inv_ne_one.mpr (vTail.ne_one a ha)
    · subst z
      exact h_merged_ne
    · exact uTail.ne_one z hz
  let secondWord := ofList H
    ((vTail.toList.map (fun a ↦ a⁻¹)).reverse ++
      (y⁻¹ * x) :: uTail.toList)
    h_second_mem h_second_ne h_second_chain
  have h_second_prod : secondWord.prod = 1 := by
    calc
      secondWord.prod = vTail.prod⁻¹ * ((y⁻¹ * x) * uTail.prod) := by
        simp only [secondWord, prod_def, toList_ofList, List.prod_append,
          ← List.prod_inv_reverse, List.prod_cons]
      _ = (y * vTail.prod)⁻¹ * (x * uTail.prod) := by
        simp only [mul_inv_rev, mul_assoc]
      _ = v.prod⁻¹ * u.prod := by rw [hu_prod, hv_prod]
      _ = 1 := by
        rw [h_prod]
        exact inv_mul_eq_one.mpr rfl
  have h_second_empty := congrArg (fun w : ReducedWord H ↦ w.toList)
    (h_unique_one secondWord h_second_prod)
  simp only [secondWord, toList_ofList, toWord_empty, Word.toList_empty] at h_second_empty
  exact (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil (y⁻¹ * x) _)) h_second_empty

/-- If the empty reduced word is the unique reduced word representing `1`, then evaluation of
reduced words over pairwise disjoint subgroups is injective. -/
theorem prod_injective_of_unique_one (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (h_unique_one : ∀ w : ReducedWord H, w.prod = 1 → w = empty H) :
    Function.Injective (fun w : ReducedWord H ↦ w.prod) := by
  intro u
  induction h_length : u.toList.length using Nat.strong_induction_on generalizing u with
  | h n ih =>
      intro v h_prod
      by_cases hu_empty : u.toList = []
      · -- An empty first list has product `1`, so uniqueness identifies both words as empty.
        have hu_one : u.prod = 1 := by
          rw [prod_def H u, hu_empty, List.prod_nil]
        have hv_one : v.prod = 1 := by
          calc
            v.prod = u.prod := h_prod.symm
            _ = 1 := hu_one
        exact (h_unique_one u hu_one).trans (h_unique_one v hv_one).symm
      · by_cases hv_empty : v.toList = []
        · -- The symmetric empty case likewise forces both words to be the empty word.
          have hv_one : v.prod = 1 := by
            rw [prod_def H v, hv_empty, List.prod_nil]
          have hu_one : u.prod = 1 := h_prod.trans hv_one
          exact (h_unique_one u hu_one).trans (h_unique_one v hv_one).symm
        · -- Equal products force equal heads; cancellation then exposes equal shorter tails.
          obtain ⟨x, _, uTail, hu, _, _⟩ := existsHeadTail H u hu_empty
          obtain ⟨y, _, vTail, hv, _, _⟩ := existsHeadTail H v hv_empty
          have hxy : x = y :=
            head_eq_of_prod_eq H h_disjoint h_unique_one hu hv h_prod
          subst y
          have hu_prod : u.prod = x * uTail.prod := by
            rw [prod_def H u, hu, List.prod_cons, ← prod_def H uTail]
          have hv_prod : v.prod = x * vTail.prod := by
            rw [prod_def H v, hv, List.prod_cons, ← prod_def H vTail]
          have h_tail_prod : uTail.prod = vTail.prod := by
            apply mul_left_cancel (a := x)
            calc
              x * uTail.prod = u.prod := hu_prod.symm
              _ = v.prod := h_prod
              _ = x * vTail.prod := hv_prod
          have h_tail_length : uTail.toList.length < n := by
            rw [← h_length, hu, List.length_cons]
            exact Nat.lt_succ_self uTail.toList.length
          have h_tail_eq : uTail = vTail :=
            ih uTail.toList.length h_tail_length rfl h_tail_prod
          apply eqOfToListEq H
          calc
            u.toList = x :: uTail.toList := hu
            _ = x :: vTail.toList := congrArg (fun l ↦ x :: l.toList) h_tail_eq
            _ = v.toList := hv.symm

end ReducedWord

/-- Proposition 68.1: If pairwise disjoint subgroups generate the ambient group and the empty
reduced word is the unique reduced word representing `1`, then the ambient group is their free
product. -/
theorem isFreeProduct_of_unique_one (H : ι → Subgroup G)
    (h_generate : ⨆ i, H i = ⊤)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (h_unique_one : ∀ w : ReducedWord H, w.prod = 1 → w = ReducedWord.empty H) :
    G = *ᵢ H := by
  -- Injectivity is the cancellation theorem above; generation supplies surjectivity.
  refine ⟨h_disjoint, ?_⟩
  constructor
  · exact ReducedWord.prod_injective_of_unique_one H h_disjoint h_unique_one
  · intro x
    exact ReducedWord.exists_prod_eq_of_iSup_eq_top H h_generate x

end Subgroup
