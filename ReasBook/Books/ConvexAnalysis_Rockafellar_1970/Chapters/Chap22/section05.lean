import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_22_5_1 (from Chap04) -/
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

/-! ### Lemma_22_5 (from Chap04) -/
open Function

section

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
  [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 22.5 states that a subspace of `𝕜^n` is generated by its elementary
  vectors.
- `core/canonical`: the owner abstraction is the finite-coordinate function-space submodule
  `L : Submodule 𝕜 (ι → E)` (specialized to `E = 𝕜` for the generation equality) together
  with the chapter predicate `L.IsElementary` from `Text_22_3_12`.
- `bridge/view`: there is no extra wrapper notion here; the item should be an owner-side theorem on
  `Submodule`, not a parallel free-standing API.

Domain-style sampling used here:
- `Submodule 𝕜 (ι → E)` as the intrinsic owner for elementary vectors in function-space submodules,
  with the division-based equality theorem specialized to `E = 𝕜`;
- `Submodule.elementary` from `Text_22_3_12` as the canonical owner-side set of
  elementary vectors;
- `Submodule.span` and `Submodule.span_le` as the canonical generating-submodule API;
- `Submodule.mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero` as the
  canonical strict-subset-zero elementary-owner specification.

Primitive data vs derived API:
- primitive owner data already upstream: the submodule `L` and the predicate `L.IsElementary`;
- primitive finite-support hypothesis layer: the canonical quantified
  `Function.HasFiniteSupport`;
- derived public API here: the finite-free owner-side inclusion
  `span 𝕜 L.elementary ≤ L` at the intrinsic module layer `Submodule 𝕜 (ι → E)`;
- downstream division-based API: the owner-prefix theorem
  `Submodule.eq_span_elementary_of_hasFiniteSupport`, then the finite-coordinate wrapper
  asserting that `L` is generated by its elementary vectors;
- proof-internal support only: the inclusion `L ≤ span 𝕜 L.elementary` together with the canonical
  span-order API `Submodule.span_le`.

Layer target: `source-facing`, expressed directly on the canonical `Submodule` owner.
-/

namespace Submodule

/-- Every linear combination of elementary vectors of `L` lies in `L`. This owner-side inclusion
is finite-free and only uses the defining owner predicate. -/
theorem span_elementary_le (L : Submodule 𝕜 (ι → E)) :
    span 𝕜 L.elementary ≤ L := by
  refine span_le.2 ?_
  intro v hv
  exact (show L.IsElementary v from hv).mem

section

variable [Finite ι]

/-- On a finite coordinate type, every function-space submodule has finite-support vectors. -/
theorem hasFiniteSupport_of_finite (L : Submodule 𝕜 (ι → E)) :
    ∀ ⦃z : ι → E⦄, z ∈ L → Function.HasFiniteSupport z := by
  intro z hzL
  simpa [Function.HasFiniteSupport] using (Set.toFinite (support z))

end

end Submodule

end

section

variable {ι : Type*} {𝕜 : Type*} [DivisionRing 𝕜]

namespace Submodule

section

/-- Intrinsic finite-support owner form of Lemma 22.5: if every vector of `L` has finite support,
then `L` is generated by its owner-side set of elementary vectors. -/
theorem eq_span_elementary_of_hasFiniteSupport {L : Submodule 𝕜 (ι → 𝕜)}
    (hfinite_support : ∀ ⦃z : ι → 𝕜⦄, z ∈ L → Function.HasFiniteSupport z) :
    L = span 𝕜 L.elementary := by
  classical
  have hmem :
      ∀ n : ℕ, ∀ z : ι → 𝕜, z ∈ L → (support z).ncard = n → z ∈ span 𝕜 L.elementary := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih z hzL hzcard
    by_cases hz0 : z = 0
    · simp [hz0]
    have hz_elem_or :
        L.IsElementary z ∨ ∃ y : ι → 𝕜, y ∈ L ∧ y ≠ 0 ∧ support y ⊂ support z := by
      by_cases hz_elem : L.IsElementary z
      · exact Or.inl hz_elem
      · exact Or.inr <| by
          by_contra hno
          have hssubset_zero :
              ∀ ⦃y : ι → 𝕜⦄, y ∈ L → support y ⊂ support z → y = 0 := by
            intro y hyL hyss
            by_contra hy0
            exact hno ⟨y, hyL, hy0, hyss⟩
          have hz_elem' : z ∈ L.elementary :=
            (L.mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero).2
              ⟨hzL, hz0, hssubset_zero⟩
          exact hz_elem (show L.IsElementary z from hz_elem')
    rcases hz_elem_or with hz_elem | ⟨y, hyL, hy0, hyss⟩
    · exact subset_span hz_elem
    · obtain ⟨i, hi⟩ : (support y).Nonempty := support_nonempty_iff.mpr hy0
      have hyi : y i ≠ 0 := mem_support.mp hi
      have hzi : z i ≠ 0 := mem_support.mp (hyss.subset hi)
      let a : 𝕜 := z i / y i
      have hwL : z - a • y ∈ L := L.sub_mem hzL (L.smul_mem a hyL)
      have hw_subset : support (z - a • y) ⊆ support z := by
        refine (support_sub z (a • y)).trans ?_
        exact Set.union_subset (Set.Subset.refl _) <|
          (support_const_smul_subset a y).trans hyss.subset
      have hwi : (z - a • y) i = 0 := by
        change z i - a * y i = 0
        rw [show a = z i / y i by rfl, div_mul_cancel₀ _ hyi, sub_self]
      have hwi_not_mem : i ∉ support (z - a • y) := by
        simp [mem_support, hwi]
      have hw_ssubset : support (z - a • y) ⊂ support z := by
        refine Set.ssubset_iff_subset_ne.2 ⟨hw_subset, ?_⟩
        intro hEq
        exact hwi_not_mem (hEq.symm ▸ hyss.subset hi)
      have hy_span : y ∈ span 𝕜 L.elementary := by
        apply ih
        · rw [← hzcard]
          exact Set.ncard_lt_ncard hyss (by
            simpa [Function.HasFiniteSupport] using hfinite_support hzL)
        · exact hyL
        · rfl
      have hw_span : z - a • y ∈ span 𝕜 L.elementary := by
        apply ih
        · rw [← hzcard]
          exact Set.ncard_lt_ncard hw_ssubset (by
            simpa [Function.HasFiniteSupport] using hfinite_support hzL)
        · exact hwL
        · rfl
      exact (sub_add_cancel z (a • y)).symm ▸ add_mem hw_span (smul_mem _ a hy_span)
  have hle : L ≤ span 𝕜 L.elementary := by
    intro z hzL
    exact hmem (support z).ncard z hzL rfl
  exact le_antisymm hle L.span_elementary_le

section

variable [Finite ι]

/-- Lemma 22.5: every subspace of `𝕜^n` is generated by its owner-side set of elementary vectors.
-/
theorem eq_span_elementary (L : Submodule 𝕜 (ι → 𝕜)) :
    L = span 𝕜 L.elementary := by
  exact L.eq_span_elementary_of_hasFiniteSupport (L.hasFiniteSupport_of_finite)

end

end

end Submodule

end
