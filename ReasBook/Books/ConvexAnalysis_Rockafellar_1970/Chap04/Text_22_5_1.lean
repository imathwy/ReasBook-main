import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.5.1 is the one-dimensional Helly statement for a finite family of real
  intervals with pairwise nonempty intersections.
- `core/canonical`: finite families are handled at the intrinsic owner
  `S : Set (Set α)` with `Set.sInter`, `S.Finite`, and `Set.Pairwise`.
- `bridge/view`: the indexed `Finset` family form is kept as a bridge from the intrinsic owner
  layer.

Domain-style sampling used here:
- `Set.OrdConnected` from the order-interval API;
- `Set.OrdConnected.out` for the defining interval-membership elimination rule;
- `Set.ordConnected_biInter` for finite intersections of interval families;
- `Set.sInter` / `Set.Finite` for intrinsic finite families of sets;
- `(s : Set ι).Pairwise` for pairwise-intersection side conditions on finite families;
- `Finset.max'` / `Finset.min'` for the finite extremal witness step in a linear order.

Primitive data vs derived API:
- primitive data (canonical owner): a finite set `S : Set (Set α)` of intervals, intervalhood of
  each `U ∈ S` via `Set.OrdConnected`, one selected nonempty interval in `S`, and pairwise
  nonempty intersections in `S`;
- bridge data: an indexed finite family `s : Finset ι`, `J : ι → Set α`;
- derived API: nonemptiness of `⋂₀ S` (canonical) and of `⋂ i ∈ s, J i` (bridge).

Layer target: `source-facing`, since the textbook statement is directly about intervals themselves,
not about a convex reformulation. The source's real statement is recovered by specializing
`α = ℝ`.
-/

section

universe u v

variable {α : Type u} [LinearOrder α]
variable {ι : Type v}

namespace Set

/-- Canonical owner form for Text 22.5.1: a finite family of pairwise intersecting intervals in a
linear order has nonempty total intersection as soon as one selected interval is nonempty.
Specializing `α = ℝ` recovers the textbook real statement. -/
-- Proof sketch: induct on the family. For the induction step, let `K` be the current total
-- intersection and choose `x ∈ K`. If `x ∈ J i`, we are done. Otherwise, the points chosen from
-- the pairwise intersections `J i ∩ J j` all lie strictly on the same side of `x`; if two lay on
-- opposite sides, order-connectedness of `J i` would force `x ∈ J i`. Take the extremal witness on
-- that side; it lies in `J i` and, because it sits between the pairwise witness for `J j` and the
-- point `x ∈ J j`, it also lies in every `J j`.
private theorem ordConnected_biInter_nonempty_of_pairwise_nonempty_of_forall_nonempty
    (s : Finset ι) (hs : s.Nonempty) (J : ι → Set α) (hJ : ∀ i ∈ s, (J i).OrdConnected)
    (hJ_nonempty : ∀ i ∈ s, (J i).Nonempty)
    (hpair : (s : Set ι).Pairwise (fun i j ↦ (J i ∩ J j).Nonempty)) :
    (⋂ i ∈ s, J i).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (hs.ne_empty rfl).elim
  | @insert i s hi ih =>
      have hJi : (J i).OrdConnected := hJ i (by simp)
      have hJi_nonempty : (J i).Nonempty := hJ_nonempty i (by simp)
      have hpair_s :
          (s : Set ι).Pairwise (fun j k ↦ (J j ∩ J k).Nonempty) := by
        intro j hj k hk hjk
        exact hpair (by simp [hj]) (by simp [hk]) hjk
      have hi_pair : ∀ j ∈ s, (J i ∩ J j).Nonempty := by
        intro j hj
        exact hpair (by simp) (by simp [hj]) (by
          intro hij
          exact hi (hij ▸ hj))
      rcases s.eq_empty_or_nonempty with rfl | hs'
      · simpa using hJi_nonempty
      · have hJ_s : ∀ j ∈ s, (J j).OrdConnected := fun j hj ↦ hJ j (by simp [hj])
        have hJ_nonempty_s : ∀ j ∈ s, (J j).Nonempty := fun j hj ↦ hJ_nonempty j (by simp [hj])
        obtain ⟨x, hx⟩ := ih hs' hJ_s hJ_nonempty_s hpair_s
        have hx_all : ∀ j ∈ s, x ∈ J j := by
          simpa using hx
        by_cases hxi : x ∈ J i
        · refine ⟨x, ?_⟩
          have hx_insert : ∀ j ∈ insert i s, x ∈ J j := by
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact hxi
            · exact hx_all j hj
          simpa using hx_insert
        · let y : ι → α := fun j ↦ if hj : j ∈ s then Classical.choose (hi_pair j hj) else x
          have hy : ∀ j ∈ s, y j ∈ J i ∩ J j := by
            intro j hj
            simp only [y, dif_pos hj]
            exact Classical.choose_spec (hi_pair j hj)
          have hside (j : ι) (hj : j ∈ s) : y j < x ∨ x < y j := by
            have hy_ne : y j ≠ x := by
              intro hyx
              exact hxi (hyx ▸ (hy j hj).1)
            exact lt_or_gt_of_ne hy_ne
          have hsameSide : (∀ j ∈ s, y j < x) ∨ (∀ j ∈ s, x < y j) := by
            by_cases hallLeft : ∀ j ∈ s, y j < x
            · exact Or.inl hallLeft
            · push Not at hallLeft
              rcases hallLeft with ⟨j₀, hj₀, hj₀_not_lt⟩
              have hx_lt_yj₀ : x < y j₀ := by
                rcases hside j₀ hj₀ with hj₀_lt_x | hx_lt_yj₀
                · exact (not_lt_of_ge hj₀_not_lt hj₀_lt_x).elim
                · exact hx_lt_yj₀
              refine Or.inr fun j hj ↦ ?_
              rcases hside j hj with hyj_lt | hx_lt_yj
              · exact (hxi <| hJi.out (hy j hj).1 (hy j₀ hj₀).1
                  ⟨hyj_lt.le, hx_lt_yj₀.le⟩).elim
              · exact hx_lt_yj
          rcases hsameSide with hallLeft | hallRight
          · let z := (s.image y).max' (hs'.image y)
            have hz_mem : z ∈ s.image y := (s.image y).max'_mem (hs'.image y)
            rcases Finset.mem_image.mp hz_mem with ⟨j₀, hj₀, hjz⟩
            have hz_eq : z = y j₀ := hjz.symm
            have hy_max : ∀ j ∈ s, y j ≤ z := fun j hj ↦
              (s.image y).le_max' _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
            have hz_all : ∀ j ∈ insert i s, z ∈ J j := by
              intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact hz_eq ▸ (hy j₀ hj₀).1
              · exact (hJ_s j hj).out (hy j hj).2 (hx_all j hj)
                  ⟨hy_max j hj, hz_eq ▸ (hallLeft j₀ hj₀).le⟩
            exact ⟨z, by simpa using hz_all⟩
          · let z := (s.image y).min' (hs'.image y)
            have hz_mem : z ∈ s.image y := (s.image y).min'_mem (hs'.image y)
            rcases Finset.mem_image.mp hz_mem with ⟨j₀, hj₀, hjz⟩
            have hz_eq : z = y j₀ := hjz.symm
            have hy_min : ∀ j ∈ s, z ≤ y j := fun j hj ↦
              (s.image y).min'_le _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
            have hz_all : ∀ j ∈ insert i s, z ∈ J j := by
              intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact hz_eq ▸ (hy j₀ hj₀).1
              · exact (hJ_s j hj).out (hx_all j hj) (hy j hj).2
                  ⟨hz_eq ▸ (hallRight j₀ hj₀).le, hy_min j hj⟩
            exact ⟨z, by simpa using hz_all⟩

/-- Canonical owner form for Text 22.5.1: a finite family of pairwise intersecting intervals in a
linear order has nonempty total intersection, provided one selected interval is nonempty. -/
theorem ordConnected_sInter_nonempty_of_pairwise_nonempty
    (S : Set (Set α)) (hS_finite : S.Finite) (hS : ∀ U ∈ S, U.OrdConnected)
    (hseed : ∃ U ∈ S, U.Nonempty)
    (hpair : S.Pairwise (fun U V ↦ (U ∩ V).Nonempty)) :
    (⋂₀ S).Nonempty := by
  classical
  let s : Finset (Set α) := hS_finite.toFinset
  have hs_mem : ∀ {U : Set α}, U ∈ s ↔ U ∈ S := by
    intro U
    change U ∈ hS_finite.toFinset ↔ U ∈ S
    exact hS_finite.mem_toFinset
  have hJ : ∀ U ∈ s, U.OrdConnected := by
    intro U hU
    exact hS U (hs_mem.mp hU)
  have hseed' : ∃ U ∈ s, U.Nonempty := by
    rcases hseed with ⟨U, hU, hU_nonempty⟩
    exact ⟨U, hs_mem.mpr hU, hU_nonempty⟩
  have hpair' : (s : Set (Set α)).Pairwise (fun U V ↦ (U ∩ V).Nonempty) := by
    intro U hU V hV hUV
    exact hpair (hs_mem.mp hU) (hs_mem.mp hV) hUV
  obtain ⟨U₀, hU₀, hU₀_nonempty⟩ := hseed'
  have hs : s.Nonempty := ⟨U₀, hU₀⟩
  have hJ_nonempty : ∀ U ∈ s, U.Nonempty := by
    intro U hU
    by_cases hUU₀ : U = U₀
    · simpa [hUU₀] using hU₀_nonempty
    · rcases hpair' (by simpa using hU) (by simpa using hU₀) hUU₀ with ⟨x, hx⟩
      exact ⟨x, hx.1⟩
  obtain ⟨x, hx⟩ :=
    ordConnected_biInter_nonempty_of_pairwise_nonempty_of_forall_nonempty
      s hs id hJ hJ_nonempty hpair'
  have hx_all : ∀ U ∈ s, x ∈ U := by
    simpa [Set.mem_iInter] using hx
  refine ⟨x, ?_⟩
  intro U hU
  exact hx_all U (hs_mem.mpr hU)

/-- Bridge form for Text 22.5.1: an indexed finite family of pairwise intersecting intervals in a
linear order has nonempty total intersection, provided one selected interval is nonempty. -/
theorem ordConnected_biInter_nonempty_of_pairwise_nonempty
    (s : Finset ι) (J : ι → Set α) (hJ : ∀ i ∈ s, (J i).OrdConnected)
    (hseed : ∃ i ∈ s, (J i).Nonempty)
    (hpair : (s : Set ι).Pairwise (fun i j ↦ (J i ∩ J j).Nonempty)) :
    (⋂ i ∈ s, J i).Nonempty := by
  obtain ⟨i₀, hi₀, hi₀_nonempty⟩ := hseed
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  have hJ_nonempty : ∀ i ∈ s, (J i).Nonempty := by
    intro i hi
    by_cases hii₀ : i = i₀
    · simpa [hii₀] using hi₀_nonempty
    · rcases hpair (by simpa using hi) (by simpa using hi₀) hii₀ with ⟨x, hx⟩
      exact ⟨x, hx.1⟩
  exact ordConnected_biInter_nonempty_of_pairwise_nonempty_of_forall_nonempty
    s hs J hJ hJ_nonempty hpair

end Set

end
