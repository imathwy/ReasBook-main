import stacks_project.Chap10.Definition_10_84_1

open scoped DirectSum

universe u v w

section Lemma_10_84_2

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace DirectSumDevissage

/-- The ordinal stages of a dévissage that have a successor stage still inside the dévissage. -/
abbrev successorIndex (D : DirectSumDevissage R M) : Type _ :=
  { α : Ordinal.{w} // α + 1 < D.length }

/-- The quotient attached to a successor step of a direct sum dévissage. -/
abbrev successiveQuotient (D : DirectSumDevissage R M) (α : D.successorIndex) : Type _ :=
  D.stages (α.1 + 1) ⧸ D.predecessorStage α.1

section

open scoped Ordinal

variable (D : DirectSumDevissage R M)

/-- Helper for Lemma 10.84.2: choose a complement to the predecessor stage inside each successor
stage. -/
noncomputable abbrev successorComplement (α : D.successorIndex) :
    Submodule R (D.stages (α.1 + 1)) :=
  Classical.choose (D.stage_succ_isCompl α.2)

/-- Helper for Lemma 10.84.2: the chosen complement is complementary to the predecessor stage. -/
lemma predecessorStage_isCompl_successorComplement (α : D.successorIndex) :
    IsCompl (D.predecessorStage α.1) (D.successorComplement α) :=
  Classical.choose_spec (D.stage_succ_isCompl α.2)

/-- Helper for Lemma 10.84.2: the successor complement viewed as a submodule of the ambient
module. -/
noncomputable abbrev successorPiece (α : D.successorIndex) : Submodule R M :=
  (D.successorComplement α).map (D.stages (α.1 + 1)).subtype

/-- Helper for Lemma 10.84.2: the quotient at a successor stage identifies with the chosen
successor piece in the ambient module. -/
noncomputable def successiveQuotient_linearEquiv_successorPiece
    (α : D.successorIndex) :
    D.successiveQuotient α ≃ₗ[R] D.successorPiece α :=
  -- First identify the quotient with the chosen complement inside the successor stage, then
  -- transport that complement into the ambient module.
  Submodule.quotientEquivOfIsCompl _ _ (D.predecessorStage_isCompl_successorComplement α) ≪≫ₗ
    Submodule.equivSubtypeMap _ _

/-- Helper for Lemma 10.84.2: each successor piece lies inside the corresponding successor stage. -/
lemma successorPiece_le_stage_succ (α : D.successorIndex) :
    D.successorPiece α ≤ D.stages (α.1 + 1) :=
  Submodule.map_subtype_le _ _

/-- Helper for Lemma 10.84.2: the predecessor stage and the new successor piece are disjoint in the
ambient module. -/
lemma successorPiece_disjoint_stage (α : D.successorIndex) :
    Disjoint (D.stages α.1) (D.successorPiece α) := by
  -- Map the complement decomposition inside the successor stage into the ambient module.
  have hmap :
      (D.predecessorStage α.1).map (D.stages (α.1 + 1)).subtype = D.stages α.1 := by
    rw [DirectSumDevissage.predecessorStage, Submodule.map_comap_subtype]
    exact inf_eq_right.mpr ((D.monotone_stages) <| le_self_add)
  have hdisjoint :
      Disjoint ((D.predecessorStage α.1).map (D.stages (α.1 + 1)).subtype) (D.successorPiece α) :=
    Submodule.disjoint_map Subtype.val_injective
      (D.predecessorStage_isCompl_successorComplement α).disjoint
  simpa [hmap] using hdisjoint

/-- Helper for Lemma 10.84.2: a successor stage is the supremum of its predecessor stage and the
new successor piece. -/
lemma stage_succ_eq_sup_successorPiece (α : D.successorIndex) :
    D.stages (α.1 + 1) = D.stages α.1 ⊔ D.successorPiece α := by
  -- Push the complement decomposition in the successor stage forward along the subtype map.
  have hsup :
      (D.predecessorStage α.1).map (D.stages (α.1 + 1)).subtype ⊔ D.successorPiece α =
        D.stages (α.1 + 1) := by
    rw [← Submodule.map_sup, D.predecessorStage_isCompl_successorComplement α |>.sup_eq_top,
      Submodule.map_top, Submodule.range_subtype]
  have hmap :
      (D.predecessorStage α.1).map (D.stages (α.1 + 1)).subtype = D.stages α.1 := by
    rw [DirectSumDevissage.predecessorStage, Submodule.map_comap_subtype]
    exact inf_eq_right.mpr ((D.monotone_stages) <| le_self_add)
  simpa [hmap] using hsup.symm

/-- Helper for Lemma 10.84.2: there are no successor pieces below the zero stage. -/
lemma successorPieces_below_zero :
    (⨆ a : {α : D.successorIndex // α.1 + 1 ≤ 0}, D.successorPiece a.1) = ⊥ := by
  -- The indexing subtype is empty because no ordinal successor is at most `0`.
  refine le_antisymm (iSup_le fun a ↦ ?_) bot_le
  have hpos : 0 < a.1.1 + 1 := by
    exact bot_lt_iff_ne_bot.mpr (by simp)
  exact False.elim <| (not_lt_of_ge a.2) hpos

/-- Helper for Lemma 10.84.2: every successor piece indexed below `β` already lies in stage
`β`. -/
lemma successorPiece_le_stage_of_le (α : D.successorIndex) {β : Ordinal.{w}}
    (h : α.1 + 1 ≤ β) :
    D.successorPiece α ≤ D.stages β :=
  (D.successorPiece_le_stage_succ α).trans ((D.monotone_stages) h)

/-- Helper for Lemma 10.84.2: the successor pieces below `β + 1` split into the older pieces and
the new piece at stage `β + 1`. -/
lemma successorPieces_below_succ_iSup (β : Ordinal.{w}) (hβ : β + 1 < D.length) :
    (⨆ a : {α : D.successorIndex // α.1 + 1 ≤ β + 1}, D.successorPiece a.1) =
      (⨆ a : {α : D.successorIndex // α.1 + 1 ≤ β}, D.successorPiece a.1) ⊔
        D.successorPiece ⟨β, hβ⟩ := by
  refine le_antisymm ?_ ?_
  · -- Every piece below `β + 1` is either already below `β` or is the new `β`-piece itself.
    refine iSup_le fun a ↦ ?_
    rcases a with ⟨a, ha⟩
    have hlt : a.1 < Order.succ β := by
      exact Order.succ_le_iff.mp ha
    obtain rfl | hltβ := Order.lt_succ_iff_eq_or_lt.mp hlt
    · simpa using le_sup_of_le_right (show D.successorPiece ⟨β, hβ⟩ ≤ D.successorPiece ⟨β, hβ⟩ from
        le_rfl)
    · have hle : a.1 + 1 ≤ β := by
        exact Order.succ_le_of_lt hltβ
      exact le_sup_of_le_left <| le_iSup_of_le ⟨a, hle⟩ le_rfl
  · -- Both the old pieces and the new piece occur among the indices below `β + 1`.
    refine sup_le ?_ ?_
    · refine iSup_le fun a ↦ ?_
      exact le_iSup_of_le ⟨a.1, le_trans a.2 (le_self_add)⟩ le_rfl
    · exact le_iSup_of_le ⟨⟨β, hβ⟩, le_rfl⟩ le_rfl

/-- Helper for Lemma 10.84.2: the successor pieces below a stage span that stage. -/
lemma stage_eq_iSup_successorPieces_below
    (β : Ordinal.{w}) (hβ : β < D.length) :
    D.stages β = ⨆ a : {α : D.successorIndex // α.1 + 1 ≤ β}, D.successorPiece a.1 := by
  -- Route correction: the source proof is a transfinite induction on the stage ordinal itself,
  -- not on auxiliary partial direct sums.
  induction β using Ordinal.limitRecOn with
  | zero =>
      -- The zero stage is trivial, and there are no successor pieces below it.
      rw [D.stage_zero, D.successorPieces_below_zero]
  | succ β IH =>
      have hβ' : β < D.length := by
        exact Order.succ_le_iff.mp hβ.le
      -- The successor step adds exactly one new summand.
      calc
        D.stages (Order.succ β)
            = D.stages β ⊔ D.successorPiece ⟨β, hβ⟩ := by
                simpa using D.stage_succ_eq_sup_successorPiece ⟨β, hβ⟩
        _ = (⨆ a : {α : D.successorIndex // α.1 + 1 ≤ β}, D.successorPiece a.1) ⊔
              D.successorPiece ⟨β, hβ⟩ := by
                rw [IH hβ']
        _ = ⨆ a : {α : D.successorIndex // α.1 + 1 ≤ Order.succ β}, D.successorPiece a.1 := by
                simpa using (D.successorPieces_below_succ_iSup β hβ).symm
  | limit β hlimit IH =>
      refine le_antisymm ?_ ?_
      · -- At a limit stage, every earlier stage is already spanned by the earlier successor pieces.
        rw [D.stage_limit hβ hlimit]
        refine iSup_le fun a ↦ ?_
        have hstage :
            D.stages a.1 =
              ⨆ b : {α : D.successorIndex // α.1 + 1 ≤ a.1}, D.successorPiece b.1 :=
          IH a.1 a.2 (lt_trans a.2 hβ)
        rw [hstage]
        refine iSup_le fun b ↦ ?_
        exact le_iSup_of_le ⟨b.1, le_trans b.2 (le_of_lt a.2)⟩ le_rfl
      · -- Conversely, each successor piece below `β` lies in stage `β` by monotonicity.
        refine iSup_le fun a ↦ D.successorPiece_le_stage_of_le a.1 a.2

/-- Helper for Lemma 10.84.2: the successor pieces span the whole ambient module. -/
lemma iSup_successorPiece_eq_top :
    (⨆ α : D.successorIndex, D.successorPiece α) = ⊤ := by
  refine le_antisymm le_top ?_
  -- Each stage is spanned by successor pieces below it, so the global stage supremum is too.
  rw [← D.iSup_stages]
  refine iSup_le fun β ↦ ?_
  rw [D.stage_eq_iSup_successorPieces_below β.1 β.2]
  refine iSup_le fun a ↦ ?_
  exact le_iSup_of_le a.1 le_rfl

/-- Helper for Lemma 10.84.2: if the sum over a finite set of successor pieces is zero, then the
maximal-index component is zero. -/
lemma successorPiece_finset_sum_eq_zero_of_max (s : Finset D.successorIndex) (a : D.successorIndex)
    (ha : a ∈ s) (hmax : ∀ b ∈ s, b.1 ≤ a.1) (v : D.successorIndex → M)
    (hv : ∀ i ∈ s, v i ∈ D.successorPiece i) (hsum : s.sum v = 0) :
    v a = 0 := by
  -- The sum over `s.erase a` lands in the predecessor stage `D.stages a.1`.
  have hsum_mem : (s.erase a).sum v ∈ D.stages a.1 := by
    refine Submodule.sum_mem _ fun b hb ↦ ?_
    have hbs : b ∈ s := Finset.mem_of_mem_erase hb
    have hne : b ≠ a := Finset.ne_of_mem_erase hb
    have hlt : b.1 < a.1 := by
      refine lt_of_le_of_ne (hmax b hbs) ?_
      intro hEq
      apply hne
      exact Subtype.ext hEq
    have hle : b.1 + 1 ≤ a.1 := by
      exact Order.succ_le_of_lt hlt
    exact D.successorPiece_le_stage_of_le b hle (hv b hbs)
  have hva_stage : v a ∈ D.stages a.1 := by
    have hEq : v a = -((s.erase a).sum v) := by
      rw [← add_eq_zero_iff_eq_neg]
      simpa [s.add_sum_erase v ha] using hsum
    rw [hEq]
    exact (D.stages a.1).neg_mem hsum_mem
  -- Disjointness of the old stage and the new piece forces the maximal component to vanish.
  exact (Submodule.disjoint_def.mp (D.successorPiece_disjoint_stage a)) (v a) hva_stage (hv a ha)

/-- Helper for Lemma 10.84.2: a vanishing finite sum of successor-piece vectors has trivial
components. -/
lemma successorPiece_finset_sum_eq_zero_imp_eq_zero (s : Finset D.successorIndex)
    (v : D.successorIndex → M) (hv : ∀ i ∈ s, v i ∈ D.successorPiece i)
    (hsum : s.sum v = 0) :
    ∀ i ∈ s, v i = 0 := by
  classical
  -- Remove a maximal index and apply the previous lemma, then recurse on the remaining support.
  refine Finset.eraseInduction
      (p := fun t : Finset D.successorIndex =>
        ∀ w : D.successorIndex → M, (∀ i ∈ t, w i ∈ D.successorPiece i) →
          t.sum w = 0 → ∀ i ∈ t, w i = 0)
      ?_ s v hv hsum
  intro t ih w hw hsumw i hi
  by_cases ht : t = ∅
  · simp [ht] at hi
  · have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
    let a := t.max' htne
    have ha : a ∈ t := Finset.max'_mem _ _
    have hmax : ∀ b ∈ t, b.1 ≤ a.1 := fun b hb ↦ Finset.le_max' _ _ hb
    have hwa : w a = 0 := D.successorPiece_finset_sum_eq_zero_of_max t a ha hmax w hw hsumw
    have hsumErase : (t.erase a).sum w = 0 := by
      rw [← t.add_sum_erase w ha, hwa, zero_add] at hsumw
      exact hsumw
    have hwErase : ∀ j ∈ t.erase a, w j ∈ D.successorPiece j := fun j hj ↦
      hw j (Finset.mem_of_mem_erase hj)
    by_cases hia : i = a
    · simpa [hia] using hwa
    · exact ih a ha w hwErase hsumErase i (by simpa [Finset.mem_erase, hia] using hi)

/-- Helper for Lemma 10.84.2: the successor pieces are independent. -/
lemma iSupIndep_successorPiece :
    iSupIndep D.successorPiece := by
  classical
  -- The textbook injectivity argument is exactly the finset criterion for `iSupIndep`.
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  exact D.successorPiece_finset_sum_eq_zero_imp_eq_zero s v hv hsum i hi

-- Proof sketch: choose complements from `D.stage_succ_isCompl`, identify each successor quotient
-- with its chosen complement using `Submodule.quotientEquivOfIsCompl`, then prove by transfinite
-- induction on `β < D.length` that the partial direct sum over stages below `β` maps isomorphically
-- onto `D.stages β`.
/-- Lemma 10.84.2: a direct sum dévissage yields an `R`-linear equivalence between `M` and the
direct sum of the successive quotients `M_(α + 1) / M_ α`. -/
theorem nonempty_linearEquiv_directSum_successiveQuotients
    (D : DirectSumDevissage R M) :
    Nonempty (M ≃ₗ[R] ⨁ α : D.successorIndex, D.successiveQuotient α) := by
  classical
  let ePieces : (⨁ α : D.successorIndex, D.successorPiece α) ≃ₗ[R] M :=
    (D.iSupIndep_successorPiece).linearEquiv D.iSup_successorPiece_eq_top
  let eQuot :
      (⨁ α : D.successorIndex, D.successorPiece α) ≃ₗ[R]
        ⨁ α : D.successorIndex, D.successiveQuotient α :=
    (DirectSum.congrLinearEquiv (R := R)
      (fun α : D.successorIndex ↦ D.successiveQuotient_linearEquiv_successorPiece α)).symm
  -- Identify `M` with the direct sum of the chosen successor pieces, then transport each piece
  -- back to the corresponding successive quotient.
  exact ⟨ePieces.symm.trans eQuot⟩

end

end DirectSumDevissage

end Lemma_10_84_2
