import Mathlib
import StacksProject_2024.Chap15.Lemma_15_36_5_Open_mapping_lemma.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Topology Pointwise

/- Domain-style sampling for the open mapping lemma in linearly topologized additive groups:
- primary domain: topological additive groups with linear/nonarchimedean topology and open-map
  phenomena
- sampled owner-level declarations:
  `IsLinearTopology.hasBasis_open_submodule`,
  `OpenAddSubgroup`,
  `dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup`,
  `AddSubgroup.exists_isOpen_of_iUnion_eq_univ_of_isClosed`
- best owner abstraction: `IsLinearTopology ℤ N` is the chapter/mathlib owner for a linearly
  topologized abelian group, `OpenAddSubgroup N` is the canonical owner for open subgroups, and
  `IsOpenMap` remains the owner for the open-map conclusion
- primitive data: the continuous additive homomorphism `u`, the source linear-topology and
  completeness hypotheses, and the separated target topological additive group
- derived API: the Baire-space consequences of completeness and countable generation of `𝓝 0`,
  already packaged in the preceding chapter lemmas, so they should not be restated as primitive
  public data here

Layer triage:
- `source-facing`: the Stacks either/or open-mapping statement below
- `core/canonical`: `IsLinearTopology ℤ N` for the linearly topologized source, and `IsOpenMap`
  for the openness alternative
- `bridge/view`: the chapter bridge from completeness plus countable generation to Baire-category
  consequences, used through Lemmas `15.36.3` and `15.36.4`
-/

noncomputable section

variable {N : Type u} {M : Type v}
variable [TopologicalSpace N] [AddCommGroup N] [IsTopologicalAddGroup N] [IsLinearTopology ℤ N]
  [(𝓝 (0 : N)).IsCountablyGenerated]
  [@CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N)]
variable [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [T2Space M]

/-- Helper for Lemma 15.36.5 (Open mapping lemma): a linearly topologized additive group with
countably generated `𝓝 0` admits a decreasing sequence of open additive subgroups forming a basis
of neighborhoods of `0`. -/
lemma exists_antitone_openAddSubgroup_basis_nhds_zero :
    ∃ U : ℕ → OpenAddSubgroup N,
      Antitone (fun n => (U n : Set N)) ∧
        ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V := by
  let hBasisSubmodule :
      (𝓝 (0 : N)).HasBasis
        (fun S : Submodule ℤ N => (S : Set N) ∈ 𝓝 (0 : N))
        (fun S : Submodule ℤ N => (S : Set N)) :=
    IsLinearTopology.hasBasis_submodule'
  let hBasis :
      (𝓝 (0 : N)).HasBasis
        (fun S : Submodule ℤ N => IsOpen (S : Set N))
        (fun S : Submodule ℤ N => (S : Set N)) :=
    hBasisSubmodule.congr
      (fun S => by
        constructor
        · intro hS
          exact S.toAddSubgroup.isOpen_of_mem_nhds hS
        · intro hS
          exact hS.mem_nhds S.zero_mem)
      (fun _ _ => rfl)
  -- Pass from a countably generated basis of open submodules to a decreasing sequence.
  rcases hBasis.exists_antitone_subbasis with ⟨S, hS_open, hS_basis⟩
  let U : ℕ → OpenAddSubgroup N := fun n =>
    { toAddSubgroup := (S n).toAddSubgroup
      isOpen' := hS_open n }
  refine ⟨U, ?_, ?_⟩
  · -- The resulting open subgroups inherit the antitone property on their underlying sets.
    intro i j hij
    exact hS_basis.2 hij
  · -- The antitone basis gives the usual neighborhood-basis characterization.
    intro V
    constructor
    · intro hV
      simpa [U] using hS_basis.mem_iff.mp hV
    · rintro ⟨n, hn⟩
      exact Filter.mem_of_superset ((U n).isOpen.mem_nhds (U n).zero_mem) hn

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if the image of an open additive subgroup is
not nowhere dense, then the closure of its image is an open additive subgroup of the target. -/
lemma closure_image_open_of_not_nowhereDense
    (u : N →ₜ+ M) (U : OpenAddSubgroup N)
    (hU : ¬ IsNowhereDense (u '' (U : Set N))) :
    IsOpen ((((U : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure : AddSubgroup M) :
      Set M) := by
  let A : AddSubgroup M := (U : AddSubgroup N).map u.toAddMonoidHom
  -- Rewrite the nowhere-dense hypothesis in terms of the subgroup closure.
  have hInterior :
      (interior ((A.topologicalClosure : AddSubgroup M) : Set M)).Nonempty := by
    have hNe :
        interior ((A.topologicalClosure : AddSubgroup M) : Set M) ≠ ∅ := by
      simpa [A, IsNowhereDense, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] using hU
    exact Set.nonempty_iff_ne_empty.mpr hNe
  rcases hInterior with ⟨x, hx⟩
  -- An additive subgroup with an interior point is open.
  exact A.topologicalClosure.isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the closures of the images of a neighborhood
basis in the source form a neighborhood basis at `0` in the target. -/
lemma closure_image_basis_at_zero
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V) :
    ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ n,
      ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure : AddSubgroup M) :
        Set M) ⊆ W := by
  intro W hW
  -- Shrink to a closed neighborhood in the target so that closure arguments become stable.
  rcases exists_mem_nhds_isClosed_subset hW with ⟨T, hT_mem, hT_closed, hT_subset⟩
  have hT_mem' : T ∈ 𝓝 (u 0) := by
    simpa using hT_mem
  have hPreimage : u ⁻¹' T ∈ 𝓝 (0 : N) := by
    simpa using u.continuous.continuousAt.preimage_mem_nhds hT_mem'
  rcases (hU_basis _).1 hPreimage with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hImage : u '' (U n : Set N) ⊆ T := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hn hx
  have hClosure :
      ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure : AddSubgroup M) :
          Set M) ⊆ T := by
    simpa [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] using
      (hT_closed.closure_subset_iff.2 hImage)
  exact hClosure.trans hT_subset

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if the next closure image is open, then the
current closure image is contained in the current image plus that next closure image. -/
lemma closure_image_subset_image_add_next
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    {n : ℕ}
    (hopen :
      IsOpen ((((U (n + 1) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
        AddSubgroup M) : Set M)) :
    ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure : AddSubgroup M) :
      Set M) ⊆
        u '' (U n : Set N) +
          ((((U (n + 1) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
            AddSubgroup M) : Set M) := by
  let A : AddSubgroup M := (U n : AddSubgroup N).map u.toAddMonoidHom
  let B : AddSubgroup M := ((U (n + 1) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure
  have hB_le_A : (U (n + 1) : Set N) ⊆ (U n : Set N) := hU_antitone (Nat.le_succ n)
  have hB_le_sup : B ≤ A ⊔ B := le_sup_right
  have hSup_open : IsOpen ((A ⊔ B : AddSubgroup M) : Set M) := by
    exact AddSubgroup.isOpen_mono hB_le_sup hopen
  have hSup_closed : IsClosed ((A ⊔ B : AddSubgroup M) : Set M) := by
    exact AddSubgroup.isClosed_of_isOpen (A ⊔ B) hSup_open
  have hClosure_le : A.topologicalClosure ≤ A ⊔ B := by
    exact AddSubgroup.topologicalClosure_minimal A le_sup_left hSup_closed
  intro y hy
  have hy' : y ∈ A ⊔ B := hClosure_le hy
  rcases AddSubgroup.mem_sup.mp hy' with ⟨a, ha, b, hb, hab⟩
  refine ⟨a, ?_, b, ?_, hab⟩
  · simpa [A, AddSubgroup.coe_map] using ha
  · simpa [B] using hb

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if each correction term lies in a deeper open
subgroup, then every partial sum stays in the initial subgroup. -/
lemma partial_sum_mem_of_mem_antitone_openAddSubgroup
    {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    {n : ℕ} {x : ℕ → N}
    (hx : ∀ k, x k ∈ U (n + k)) :
    ∀ m, Finset.sum (Finset.range m) x ∈ U n := by
  intro m
  induction m with
  | zero =>
      -- The empty partial sum is `0`, hence belongs to every additive subgroup.
      simpa using (U n).zero_mem
  | succ m ih =>
      -- Add the next correction term, which still lies in the initial subgroup by antitonicity.
      rw [Finset.sum_range_succ]
      refine (U n).add_mem ih ?_
      exact hU_antitone (Nat.le_add_right n m) (hx m)

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the difference of two partial sums lies in the
subgroup indexed by the smaller endpoint. -/
lemma partial_sum_sub_mem_of_mem_antitone_openAddSubgroup
    {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    {n : ℕ} {x : ℕ → N}
    (hx : ∀ k, x k ∈ U (n + k))
    {m l : ℕ} (hml : m ≤ l) :
    Finset.sum (Finset.range l) x - Finset.sum (Finset.range m) x ∈ U (n + m) := by
  rcases Nat.exists_eq_add_of_le hml with ⟨t, rfl⟩
  clear hml
  induction t with
  | zero =>
      -- When the endpoints coincide, the difference of partial sums is zero.
      simp
  | succ t ih =>
      -- Peel off the last term of the longer partial sum and keep the tail inside `U (n + m)`.
      have htail : x (m + t) ∈ U (n + m) := by
        exact hU_antitone (Nat.add_le_add_left (Nat.le_add_right m t) n) (hx (m + t))
      have hrewrite :
          Finset.sum (Finset.range (m + t.succ)) x - Finset.sum (Finset.range m) x =
            (Finset.sum (Finset.range (m + t)) x - Finset.sum (Finset.range m) x) + x (m + t) := by
        have hsum :
            Finset.sum (Finset.range (m + t.succ)) x =
              Finset.sum (Finset.range (m + t)) x + x (m + t) := by
          simpa [Nat.add_assoc] using (Finset.sum_range_succ (f := x) (n := m + t))
        calc
          Finset.sum (Finset.range (m + t.succ)) x - Finset.sum (Finset.range m) x
              = (Finset.sum (Finset.range (m + t)) x + x (m + t)) -
                  Finset.sum (Finset.range m) x := by
                  rw [hsum]
          _ = (Finset.sum (Finset.range (m + t)) x - Finset.sum (Finset.range m) x) + x (m + t) := by
            abel
      rw [hrewrite]
      exact (U (n + m)).add_mem ih htail

/-- Helper for Lemma 15.36.5 (Open mapping lemma): a one-step recursive existence rule along a
natural-number indexed invariant can be assembled into global sequences. -/
lemma exists_recursive_sequence_of_step
    {α : Type*} {β : Type*}
    {R : ℕ → β → Prop} {P : ℕ → α → Prop} {Φ : ℕ → β → α → β → Prop}
    {z₀ : β}
    (hz₀ : R 0 z₀)
    (hstep : ∀ k z, R k z → ∃ a, P k a ∧ ∃ z', R (k + 1) z' ∧ Φ k z a z') :
    ∃ x : ℕ → α, ∃ r : ℕ → β,
      r 0 = z₀ ∧
        (∀ k, R k (r k)) ∧
        (∀ k, P k (x k)) ∧
        (∀ k, Φ k (r k) (x k) (r (k + 1))) := by
  classical
  have hstep' :
      ∀ k z, R k z → ∃ p : α × β, P k p.1 ∧ R (k + 1) p.2 ∧ Φ k z p.1 p.2 := by
    intro k z hz
    rcases hstep k z hz with ⟨a, ha, z', hz', hΦ⟩
    exact ⟨(a, z'), ha, hz', hΦ⟩
  choose next hnextP hnextR hnextΦ using hstep'
  let state : ∀ k, { z : β // R k z } :=
    Nat.rec
      (motive := fun k ↦ { z : β // R k z })
      ⟨z₀, hz₀⟩
      (fun k prev ↦ ⟨(next k prev.1 prev.2).2, hnextR k prev.1 prev.2⟩)
  let r : ℕ → β := fun k ↦ (state k).1
  let x : ℕ → α := fun k ↦ (next k (r k) (state k).2).1
  have hr0 : r 0 = z₀ := by
    simp [r, state]
  have hr : ∀ k, R k (r k) := by
    intro k
    exact (state k).2
  refine ⟨x, r, hr0, hr, ?_, ?_⟩
  · -- Each chosen correction satisfies the one-step side condition `P`.
    intro k
    exact hnextP k (r k) (hr k)
  · -- The recursion equations identify the next remainder with the chosen successor.
    intro k
    have hr_succ : r (k + 1) = (next k (r k) (hr k)).2 := by
      simp [r, state]
    have hΦk : Φ k (r k) (x k) ((next k (r k) (hr k)).2) := by
      simpa [x] using hnextΦ k (r k) (hr k)
    simpa [hr_succ] using hΦk

/-- Helper for Lemma 15.36.5 (Open mapping lemma): recursively peel off corrections from a point
in a closure image, pushing the remainder into the next closure image. -/
lemma exists_recursive_corrections_of_mem_closure_image
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hC_open : ∀ n,
      IsOpen ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
        AddSubgroup M) : Set M))
    {n : ℕ} {y : M}
    (hy : y ∈ ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
      AddSubgroup M) : Set M)) :
    ∃ x : ℕ → N, ∃ r : ℕ → M,
      r 0 = y ∧
        (∀ k, x k ∈ U (n + k)) ∧
        (∀ k, r k ∈ ((((U (n + k) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
          AddSubgroup M) : Set M)) ∧
        (∀ k, r k = u (x k) + r (k + 1)) := by
  let C : ℕ → AddSubgroup M := fun k ↦
    ((U (n + k) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure
  have hyC : y ∈ (C 0 : Set M) := by
    simpa [C] using hy
  have hstep :
      ∀ k z, z ∈ (C k : Set M) →
        ∃ a : N, a ∈ U (n + k) ∧ ∃ z', z' ∈ (C (k + 1) : Set M) ∧ z = u a + z' := by
    intro k z hz
    have hz_step :
        z ∈ u '' (U (n + k) : Set N) + (C (k + 1) : Set M) := by
      have hsubset :=
        closure_image_subset_image_add_next u hU_antitone (n := n + k)
          (by simpa [C, Nat.add_assoc] using hC_open (n + k + 1))
      exact hsubset (by simpa [C] using hz)
    -- Route correction: isolate the Stacks one-step splitting before any recursive bookkeeping.
    rcases hz_step with ⟨w, hw, z', hz', hEq⟩
    rcases hw with ⟨a, ha, rfl⟩
    refine ⟨a, ?_, z', ?_, ?_⟩
    · simpa [Nat.add_assoc] using ha
    · simpa [C, Nat.add_assoc] using hz'
    · simpa using hEq.symm
  rcases exists_recursive_sequence_of_step
      (R := fun k z ↦ z ∈ (C k : Set M))
      (P := fun k a ↦ a ∈ U (n + k))
      (Φ := fun k z a z' ↦ z = u a + z')
      hyC hstep with ⟨x, r, hr0, hrC, hx, hrec⟩
  refine ⟨x, r, hr0, hx, ?_, hrec⟩
  intro k
  simpa [C] using hrC k

/-- Helper for Lemma 15.36.5 (Open mapping lemma): membership in deeper and deeper antitone basis
subgroups forces convergence to `0`. -/
lemma tendsto_zero_of_mem_antitone_basis
    {C : ℕ → AddSubgroup M}
    (hC_antitone : Antitone fun n => (C n : Set M))
    (hC_small : ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ n, (C n : Set M) ⊆ W)
    {n : ℕ} {r : ℕ → M}
    (hr : ∀ k, r k ∈ C (n + k)) :
    Filter.Tendsto r Filter.atTop (𝓝 (0 : M)) := by
  -- Check the limit against arbitrary neighborhoods of `0`.
  rw [Filter.tendsto_def]
  intro W hW
  rcases hC_small W hW with ⟨j, hj⟩
  refine Filter.mem_atTop_sets.2 ⟨j, ?_⟩
  intro k hk
  exact hj (hC_antitone (le_trans hk (by simpa [Nat.add_comm] using (Nat.le_add_left k n))) (hr k))

/-- Helper for Lemma 15.36.5 (Open mapping lemma): correction terms in deeper and deeper open
subgroups give a Cauchy sequence of partial sums in the ambient right-uniform additive group. -/
lemma cauchySeq_partial_sums_of_mem_antitone_openAddSubgroup_basis
    {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V)
    {n : ℕ} {x : ℕ → N}
    (hx : ∀ k, x k ∈ U (n + k)) :
    @Cauchy N (IsTopologicalAddGroup.rightUniformSpace N)
      (Filter.map (fun m ↦ Finset.sum (Finset.range m) x) Filter.atTop) := by
  letI : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  letI : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
  -- Route correction: prove Cauchy-ness through the right-uniform `sub → 0` criterion rather
  -- than by unfolding completeness of a subtype of `U n`.
  rw [IsUniformAddGroup.cauchy_map_iff_tendsto_swapped]
  refine ⟨Filter.atTop_neBot, ?_⟩
  rw [Filter.tendsto_def]
  intro V hV
  rcases (hU_basis V).1 hV with ⟨j, hj⟩
  refine Filter.mem_prod_iff.2 ?_
  refine ⟨{m | j ≤ m}, Filter.mem_atTop_sets.2 ⟨j, fun m hm ↦ hm⟩,
    {l | j ≤ l}, Filter.mem_atTop_sets.2 ⟨j, fun l hl ↦ hl⟩, ?_⟩
  rintro ⟨m, l⟩ ⟨hm, hl⟩
  rcases le_total m l with hml | hlm
  · -- When `m ≤ l`, the ordered partial-sum difference is controlled by the smaller endpoint.
    have hdiff : Finset.sum (Finset.range l) x - Finset.sum (Finset.range m) x ∈ U (n + m) :=
      partial_sum_sub_mem_of_mem_antitone_openAddSubgroup hU_antitone hx hml
    have hsubset : (U (n + m) : Set N) ⊆ V := by
      intro y hy
      exact hj <| hU_antitone
        (le_trans
          (by simpa [Nat.add_comm] using (Nat.le_add_right j n))
          (Nat.add_le_add_left hm n))
        hy
    exact hsubset hdiff
  · -- When `l ≤ m`, negate the controlled ordered difference to recover the swapped one.
    have hdiff : Finset.sum (Finset.range m) x - Finset.sum (Finset.range l) x ∈ U (n + l) :=
      partial_sum_sub_mem_of_mem_antitone_openAddSubgroup hU_antitone hx hlm
    have hsubset : (U (n + l) : Set N) ⊆ V := by
      intro y hy
      exact hj <| hU_antitone
        (le_trans
          (by simpa [Nat.add_comm] using (Nat.le_add_right j n))
          (Nat.add_le_add_left hl n))
        hy
    have hneg : -(Finset.sum (Finset.range m) x - Finset.sum (Finset.range l) x) ∈ U (n + l) :=
      (U (n + l)).neg_mem hdiff
    simpa using hsubset hneg

/-- Helper for Lemma 15.36.5 (Open mapping lemma): correction terms in deeper basis subgroups have
partial sums converging to a point of the initial subgroup. -/
lemma exists_limit_of_partial_sums_of_mem_antitone_basis
    {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V)
    {n : ℕ} {x : ℕ → N}
    (hx : ∀ k, x k ∈ U (n + k)) :
    ∃ z ∈ U n, Filter.Tendsto (fun m ↦ Finset.sum (Finset.range m) x) Filter.atTop (𝓝 z) := by
  letI : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  letI : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace N :=
    (inferInstance : @CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N))
  let s : ℕ → N := fun m ↦ Finset.sum (Finset.range m) x
  have hs_mem : ∀ m, s m ∈ U n :=
    partial_sum_mem_of_mem_antitone_openAddSubgroup hU_antitone hx
  have hs_cauchy : CauchySeq s := by
    change @Cauchy N (IsTopologicalAddGroup.rightUniformSpace N) (Filter.map s Filter.atTop)
    simpa [s] using
      cauchySeq_partial_sums_of_mem_antitone_openAddSubgroup_basis hU_antitone hU_basis hx
  have h_complete : IsComplete ((U n : Set N)) := by
    -- The ambient completeness of `N` restricts to the closed open subgroup `U n`.
    exact (AddSubgroup.isClosed_of_isOpen (U n : AddSubgroup N) (U n).isOpen).isComplete
  -- Apply the ambient-set completeness theorem directly to avoid coercion-heavy subtype work.
  rcases cauchySeq_tendsto_of_isComplete h_complete hs_mem hs_cauchy with ⟨z, hz, hzlim⟩
  exact ⟨z, hz, by simpa [s] using hzlim⟩

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the recursive remainder identities telescope to
recover the original point as a partial sum image plus the current remainder. -/
lemma eq_image_partial_sum_add_remainder_of_recursive_corrections
    (u : N →ₜ+ M) {x : ℕ → N} {r : ℕ → M} {y : M}
    (hr0 : r 0 = y)
    (hrec : ∀ k, r k = u (x k) + r (k + 1)) :
    ∀ m, y = u (Finset.sum (Finset.range m) x) + r m := by
  intro m
  induction m with
  | zero =>
      -- At stage `0`, the empty partial sum contributes nothing.
      simpa [hr0]
  | succ m ih =>
      -- One recursive step turns the current remainder into the next correction plus remainder.
      calc
        y = u (Finset.sum (Finset.range m) x) + r m := ih
        _ = u (Finset.sum (Finset.range m) x) + (u (x m) + r (m + 1)) := by rw [hrec m]
        _ = (u (Finset.sum (Finset.range m) x) + u (x m)) + r (m + 1) := by abel
        _ = u (Finset.sum (Finset.range m) x + x m) + r (m + 1) := by
          congr 1
          exact (u.map_add (Finset.sum (Finset.range m) x) (x m)).symm
        _ = u (Finset.sum (Finset.range (m + 1)) x) + r (m + 1) := by
          rw [Finset.sum_range_succ]

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the closure of the image of the `n`-th open
subgroup is the target-side object controlled by the completion argument. -/
def closure_image_subgroup
    (u : N →ₜ+ M) (U : ℕ → OpenAddSubgroup N) (n : ℕ) : AddSubgroup M :=
  ((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure

/-- Helper for Lemma 15.36.5 (Open mapping lemma): every target-side closure image is open. -/
abbrev ClosureImageOpenHyp (u : N →ₜ+ M) (U : ℕ → OpenAddSubgroup N) : Prop :=
  ∀ n, IsOpen ((closure_image_subgroup u U n : AddSubgroup M) : Set M)

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the target-side closure images shrink to `0`. -/
abbrev ClosureImageSmallHyp (u : N →ₜ+ M) (U : ℕ → OpenAddSubgroup N) : Prop :=
  ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ n, (closure_image_subgroup u U n : Set M) ⊆ W

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the target-side closure images along the shifted
source basis form the closure chain used in the Stacks completion argument. -/
def closure_image_chain (u : N →ₜ+ M) (U : ℕ → OpenAddSubgroup N) (n : ℕ) : ℕ → AddSubgroup M :=
  fun k => closure_image_subgroup u U (n + k)

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the shifted closure-image chain inherits the
antitone behavior of the source open-subgroup basis. -/
lemma closure_image_chain_antitone
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (n : ℕ) :
    Antitone fun k => (closure_image_chain u U n k : Set M) := by
  intro i j hij
  change closure_image_chain u U n j ≤ closure_image_chain u U n i
  -- Passing to images and then closures preserves the antitone inclusion pattern.
  exact AddSubgroup.topologicalClosure_mono <|
    AddSubgroup.map_mono <|
      hU_antitone (Nat.add_le_add_left hij n)

/-- Helper for Lemma 15.36.5 (Open mapping lemma): the shifted closure-image chain still shrinks to
`0`, because deeper source basis terms sit inside the original neighborhood basis. -/
lemma closure_image_chain_small
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hC_small : ClosureImageSmallHyp u U)
    (n : ℕ) :
    ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ k, (closure_image_chain u U n k : Set M) ⊆ W := by
  intro W hW
  rcases hC_small W hW with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro w hw
  -- Compare the shifted term to the original `j`-th closure image, then use the global smallness.
  exact hj <|
    (AddSubgroup.topologicalClosure_mono <|
      AddSubgroup.map_mono <|
        hU_antitone (by simpa [Nat.add_comm] using (Nat.le_add_right j n))) hw

/-- Helper for Lemma 15.36.5 (Open mapping lemma): once every closure image is open and these
closure images shrink to `0`, the completion argument upgrades each closure image to the actual
image of the corresponding open subgroup. -/
lemma mem_image_of_mem_closure_image_chain
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V)
    (hC_open : ClosureImageOpenHyp u U)
    (hC_small : ClosureImageSmallHyp u U)
    {n : ℕ} {y : M}
    (hy : y ∈ closure_image_chain u U n 0) :
    y ∈ u '' (U n : Set N) := by
  -- Route correction: keep the Stacks recursive-correction route, but package the final Hausdorff
  -- comparison in the abstract limit lemma from the theorem-local support file.
  have hy0 :
      y ∈ ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
        AddSubgroup M) : Set M) := by
    simpa [closure_image_chain] using hy
  -- Build the recursive corrections and remainders starting from `y`.
  rcases exists_recursive_corrections_of_mem_closure_image u hU_antitone hC_open hy0 with
    ⟨x, r, hr0, hx, hrC, hrec⟩
  -- Completeness of `N` produces a limit `z` in the initial subgroup `U n`.
  rcases exists_limit_of_partial_sums_of_mem_antitone_basis hU_antitone hU_basis hx with
    ⟨z, hz, hs⟩
  have hr_zero : Filter.Tendsto r Filter.atTop (𝓝 (0 : M)) := by
    have hChain_antitone :
        Antitone fun k =>
          (((((U (n + k) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
            AddSubgroup M) : Set M)) := by
      intro i j hij
      exact AddSubgroup.topologicalClosure_mono <|
        AddSubgroup.map_mono <|
          hU_antitone (Nat.add_le_add_left hij n)
    have hChain_small :
        ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ k,
          (((((U (n + k) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
            AddSubgroup M) : Set M)) ⊆ W := by
      intro W hW
      rcases hC_small W hW with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      intro w hw
      exact hj <|
        (AddSubgroup.topologicalClosure_mono <|
          AddSubgroup.map_mono <|
            hU_antitone (by simpa [Nat.add_comm] using (Nat.le_add_right j n))) hw
    -- Work directly with the shifted raw chain to avoid extra definitional unfolding through
    -- `closure_image_chain`.
    exact tendsto_zero_of_mem_antitone_basis
      (C := fun k ↦
        ((U (n + k) : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure)
      (n := 0)
      hChain_antitone hChain_small (by
        intro k
        simpa using hrC k)
  have hy_partial : ∀ m, y = u (Finset.sum (Finset.range m) x) + r m := by
    -- Telescope the recursive identities to express each stage as partial sum plus remainder.
    exact eq_image_partial_sum_add_remainder_of_recursive_corrections u hr0 hrec
  have hy_eq : y = u z := by
    -- Apply the abstract limit comparison to the recursive-correction sequence.
    exact eq_map_limit_of_partial_sum_add_remainder u hy_partial hs hr_zero
  exact ⟨z, hz, hy_eq.symm⟩

/-- Helper for Lemma 15.36.5 (Open mapping lemma): once every closure image is open and these
closure images shrink to `0`, the completion argument upgrades each closure image to the actual
image of the corresponding open subgroup. -/
lemma closure_image_eq_image_of_antitone_basis
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_antitone : Antitone fun n => (U n : Set N))
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V)
    (hC_open : ClosureImageOpenHyp u U)
    (hC_small : ClosureImageSmallHyp u U) :
    ∀ n,
      (closure_image_subgroup u U n : Set M) ⊆ u '' (U n : Set N) := by
  intro n y hy
  -- Reduce the subset statement to the fixed-point version proved by the Stacks completion step.
  simpa [closure_image_chain] using
    mem_image_of_mem_closure_image_chain u hU_antitone hU_basis hC_open hC_small hy

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if a neighborhood basis of `0` has open images,
then the continuous additive homomorphism is an open map. -/
lemma isOpenMap_of_openAddSubgroup_basis
    (u : N →ₜ+ M) {U : ℕ → OpenAddSubgroup N}
    (hU_basis : ∀ V : Set N, V ∈ 𝓝 (0 : N) ↔ ∃ n, (U n : Set N) ⊆ V)
    (hImage_open : ∀ n, IsOpen (u '' (U n : Set N))) :
    IsOpenMap u := by
  intro S hS
  -- Check openness pointwise by translating the basis neighborhood at `0`.
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hS_mem : S ∈ 𝓝 x := hS.mem_nhds hx
  have hS_mem' : S ∈ 𝓝 ((fun z : N => x + z) 0) := by
    simpa using hS_mem
  have hPreimage : (fun z : N => x + z) ⁻¹' S ∈ 𝓝 (0 : N) := by
    simpa using (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds hS_mem'
  rcases (hU_basis _).1 hPreimage with ⟨n, hn⟩
  let T : Set M := (fun z : M => u x + z) '' (u '' (U n : Set N))
  have hT_open : IsOpen T := by
    exact (isOpenMap_add_left (u x)) _ (hImage_open n)
  have hT_mem : u x ∈ T := by
    refine ⟨0, ?_, by simp⟩
    exact ⟨0, (U n).zero_mem, by simp⟩
  have hT_subset : T ⊆ u '' S := by
    intro z hz
    rcases hz with ⟨z', hz', rfl⟩
    rcases hz' with ⟨a, ha, rfl⟩
    refine ⟨x + a, hn ha, ?_⟩
    simp
  exact Filter.mem_of_superset (hT_open.mem_nhds hT_mem) hT_subset

/-- Lemma 15.36.5 (Open mapping lemma): a continuous homomorphism from a complete linearly
topologized abelian group with a countable fundamental system of neighbourhoods of `0` to a
separated topological abelian group is either open, or the image of some open subgroup is nowhere
dense. -/
-- Proof sketch: choose a decreasing countable basis of open subgroups in `N`; if no image of such
-- a subgroup is nowhere dense, then the closures of these images form a neighborhood basis in `M`.
-- Use completeness of `N` to lift an arbitrary point of the first closure by an infinite sum, and
-- use separatedness of `M` to identify the limit with its image under `u`, proving openness.
theorem isOpenMap_or_exists_nowhereDense_image_openAddSubgroup
    (u : N →ₜ+ M) :
    IsOpenMap u ∨ ∃ N₀ : OpenAddSubgroup N, IsNowhereDense (u '' N₀) := by
  classical
  rcases exists_antitone_openAddSubgroup_basis_nhds_zero (N := N) with ⟨U, hU_antitone, hU_basis⟩
  by_cases hBad : ∃ N₀ : OpenAddSubgroup N, IsNowhereDense (u '' N₀)
  · -- The nowhere-dense alternative is already the desired conclusion.
    exact Or.inr hBad
  · -- Otherwise every basis image has open closure, and the Stacks completion argument applies.
    have hC_open : ∀ n,
        IsOpen ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
          AddSubgroup M) : Set M) := by
      intro n
      apply closure_image_open_of_not_nowhereDense u (U n)
      intro hNowhere
      exact hBad ⟨U n, hNowhere⟩
    have hC_small :
        ∀ W : Set M, W ∈ 𝓝 (0 : M) → ∃ n,
          ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
            AddSubgroup M) : Set M) ⊆ W :=
      closure_image_basis_at_zero u hU_basis
    have hC_eq : ∀ n,
        ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
          AddSubgroup M) : Set M) ⊆ u '' (U n : Set N) :=
      closure_image_eq_image_of_antitone_basis u hU_antitone hU_basis hC_open hC_small
    have hImage_open : ∀ n, IsOpen (u '' (U n : Set N)) := by
      intro n
      have hImage_subset :
          u '' (U n : Set N) ⊆
            ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
              AddSubgroup M) : Set M) := by
        simpa [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] using
          (subset_closure : u '' (U n : Set N) ⊆ closure (u '' (U n : Set N)))
      have hEq :
          ((((U n : AddSubgroup N).map u.toAddMonoidHom).topologicalClosure :
            AddSubgroup M) : Set M) = u '' (U n : Set N) :=
        Set.Subset.antisymm (hC_eq n) hImage_subset
      have hEq' : closure (u '' (U n : Set N)) = u '' (U n : Set N) := by
        simpa [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] using hEq
      simpa [hEq'] using hC_open n
    exact Or.inl (isOpenMap_of_openAddSubgroup_basis u hU_basis hImage_open)

end
