/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Mathlib.Topology.Instances.EReal.Lemmas
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part2

noncomputable section

section Chap02
section Section10

open scoped BigOperators

/-- Upper semicontinuity at a vertex of an `m`-simplex contained in `dom f`. -/
lemma Section10.upperSemicontinuousWithinAt_of_isSimplex_vertex {n m : ℕ}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {b : Fin (m + 1) → Fin n → Real} (hb : AffineIndependent Real b)
    (hdom : convexHull Real (Set.range b) ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (j : Fin (m + 1)) :
    UpperSemicontinuousWithinAt f (convexHull Real (Set.range b)) (b j) := by
  classical
  intro y hxy
  set S : Set (Fin n → Real) := convexHull Real (Set.range b)
  have hx0S : b j ∈ S := (subset_convexHull (𝕜 := Real) (s := Set.range b) ⟨j, rfl⟩)
  have hmap :
      nhdsWithin (b j) S =
        Filter.map ((↑) : {z // z ∈ S} → Fin n → Real) (nhds (⟨b j, hx0S⟩ : {z // z ∈ S})) := by
    simpa [S] using (nhdsWithin_eq_map_subtype_coe (s := S) (a := b j) hx0S)
  -- Reduce the `nhdsWithin` statement to one on the simplex subtype.
  suffices
      ∀ᶠ z : {z // z ∈ S} in nhds (⟨b j, hx0S⟩ : {z // z ∈ S}), f z.1 < y by
    simpa [UpperSemicontinuousWithinAt, hmap, Filter.eventually_map, S] using this
  by_cases hyTop : y = ⊤
  · subst hyTop
    refine Filter.Eventually.of_forall ?_
    intro z
    have hzdom : z.1 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := hdom z.2
    have : z.1 ∈ (Set.univ : Set (Fin n → Real)) ∧ f z.1 < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hzdom
    exact this.2
  · have hyBot : y ≠ ⊥ := by
      intro hyBot
      subst hyBot
      simp at hxy
    lift y to Real using ⟨hyTop, hyBot⟩
    -- A uniform real upper bound on the simplex.
    have hSsimplex : IsSimplex n m S := ⟨b, hb, rfl⟩
    rcases
        Section10.simplex_real_upper_bound_of_dom (hf := hf) (hP := hSsimplex) (hPdom := hdom) with
      ⟨M, hM⟩
    -- Extract finiteness at the vertex from `hdom`.
    have hx0dom : b j ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := hdom hx0S
    have hx0ltTop : f (b j) < (⊤ : EReal) := by
      have : b j ∈ (Set.univ : Set (Fin n → Real)) ∧ f (b j) < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hx0dom
      exact this.2
    have hx0neTop : f (b j) ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hx0ltTop
    -- Choose a real `r0` with `f (b j) ≤ r0 < y`.
    by_cases hx0bot : f (b j) = ⊥
    · -- Vertex value `-∞`: take `r0 = y - 1`.
      let r0 : Real := y - 1
      have hr0_lt_y : r0 < y := by linarith
      have hvertex_le : f (b j) ≤ (r0 : EReal) := by
        simp [hx0bot]
      -- If the global bound is already ≤ r0, the claim is immediate.
      by_cases hMr0 : M ≤ r0
      · refine Filter.Eventually.of_forall ?_
        intro z
        have hzle : f z.1 ≤ (M : EReal) := hM z.1 z.2
        have hzle' : f z.1 ≤ (r0 : EReal) := le_trans hzle (by exact_mod_cast hMr0)
        have : (r0 : EReal) < (y : EReal) := (EReal.coe_lt_coe_iff).2 hr0_lt_y
        exact lt_of_le_of_lt hzle' this
      · have hMr0' : r0 < M := lt_of_not_ge hMr0
        -- Control the barycentric coordinate at `j` near the vertex.
        let δ : Real := (y - r0) / (2 * (M - r0))
        have hδpos : 0 < δ := by
          have hy_r0 : 0 < y - r0 := by linarith
          have hden : 0 < 2 * (M - r0) := by nlinarith
          exact div_pos hy_r0 hden
        set B : AffineBasis (Fin (m + 1)) Real (affineSpan Real (Set.range b)) :=
          Section10.simplex_affineBasis_on_affineSpan (b := b) hb
        let incl : {z // z ∈ S} → affineSpan Real (Set.range b) :=
          fun z => ⟨z.1, convexHull_subset_affineSpan (𝕜 := Real) (s := Set.range b) z.2⟩
        have hcoord :
            ∀ᶠ z : {z // z ∈ S} in nhds (⟨b j, hx0S⟩ : {z // z ∈ S}),
              (1 - δ) < B.coord j (incl z) := by
          simpa [B, incl, S] using
            (Section10.vertex_coord_eventually_gt (b := b) hb j (δ := δ) hδpos)
        filter_upwards [hcoord] with z hzcoord
        let q : affineSpan Real (Set.range b) := incl z
        let w : Fin (m + 1) → Real := fun i => B.coord i q
        have hw1 : (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := by
          simp [w]
        have hBcoe :
            ((affineSpan Real (Set.range b)).subtype ∘ fun i : Fin (m + 1) => B i) = b := by
          funext i
          change ((B i : Fin n → Real) = b i)
          simp [B, Section10.simplex_affineBasis_on_affineSpan]
          rfl
        have hzcomb : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w = z.1 := by
          -- Map `AffineBasis.affineCombination_coord_eq_self` into the ambient space.
          have hq : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i)
              (fun i => B.coord i q) = q := by
            exact B.affineCombination_coord_eq_self q
          have hq' := congrArg ((affineSpan Real (Set.range b)).subtype) hq
          have hmap' :=
            (Finset.map_affineCombination (s := (Finset.univ : Finset (Fin (m + 1))))
              (p := fun i : Fin (m + 1) => B i) (w := fun i => B.coord i q) (hw := hw1)
              (f := (affineSpan Real (Set.range b)).subtype))
          -- Rewrite both sides.
          simpa [q, w, incl, hBcoe] using (hmap'.symm.trans hq')
        -- `w` agrees with convex-hull weights, hence is nonnegative.
        have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w i := by
          intro i hi
          have hz_repr :
              ∃ w0 : Fin (m + 1) → Real, (∀ i, 0 ≤ w0 i) ∧ (∑ i, w0 i) = (1 : Real) ∧
                z.1 = ∑ i, w0 i • b i := by
            simpa [S, convexHull_range_eq_setOf_weighted_sum] using z.2
          rcases hz_repr with ⟨w0, hw0_nonneg, hw0_sum, hz0⟩
          have hw0_sum' :
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w0 i) = 1 := by
            simpa using hw0_sum
          have hz_aff : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w0 = z.1 := by
            rw [Finset.affineCombination_eq_linear_combination _ _ _ hw0_sum']
            simpa using hz0.symm
          have hinj :
              Function.Injective ((affineSpan Real (Set.range b)).subtype) :=
            AffineSubspace.subtype_injective (affineSpan Real (Set.range b))
          have hqcomb :
              q =
                (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i) w0 := by
            apply hinj
            have hmap' :=
              (Finset.map_affineCombination (s := (Finset.univ : Finset (Fin (m + 1))))
                (p := fun i : Fin (m + 1) => B i) (w := w0) (hw := hw0_sum')
                (f := (affineSpan Real (Set.range b)).subtype))
            -- Compare in the ambient space.
            calc
              (affineSpan Real (Set.range b)).subtype q = z.1 := rfl
              _ = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w0 := hz_aff.symm
              _ =
                  (Finset.univ : Finset (Fin (m + 1))).affineCombination Real
                    (((affineSpan Real (Set.range b)).subtype) ∘ fun i : Fin (m + 1) => B i) w0 := by
                    simpa using
                      congrArg
                        (fun p =>
                          (Finset.univ : Finset (Fin (m + 1))).affineCombination Real p w0)
                        (hBcoe.symm)
              _ =
                  (affineSpan Real (Set.range b)).subtype
                    ((Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i) w0) := by
                    simpa using hmap'.symm
          have hwi : B.coord i q = w0 i := by
            have := B.coord_apply_combination_of_mem (s := (Finset.univ : Finset (Fin (m + 1))))
              (i := i) (hi := by simp) (w := w0) hw0_sum'
            simpa [hqcomb] using this
          simpa [w, hwi] using (hw0_nonneg i)
        -- Apply the affine-combination inequality with bounds `r0`/`M`.
        let μ : Fin (m + 1) → Real := fun i => if i = j then r0 else M
        have hμ : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), f (b i) ≤ (μ i : EReal) := by
          intro i hi
          by_cases hij : i = j
          · subst hij
            simpa [μ] using hvertex_le
          · have hbi : b i ∈ S :=
              (subset_convexHull (𝕜 := Real) (s := Set.range b) ⟨i, rfl⟩)
            have : f (b i) ≤ (M : EReal) := hM (b i) hbi
            simpa [μ, hij] using this
        have hle :=
          Section10.convexFunctionOn_le_affineCombination_real (hf := hf)
            (s := (Finset.univ : Finset (Fin (m + 1)))) (x := b) (μ := μ) (w := w)
            hμ hw0 hw1
        have hle' :
            f z.1 ≤ ((∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) : EReal) := by
          simpa [hzcomb] using hle
        -- Show the real bound is strictly below `y`.
        have hjlt : 1 - w j < δ := by
          -- From `1 - δ < w j`, rearrange.
          have : (1 - δ) < w j := by simpa [w, q] using hzcoord
          linarith
        have hpos : 0 < M - r0 := by linarith
        have hδmul : (1 - w j) * (M - r0) < δ * (M - r0) :=
          mul_lt_mul_of_pos_right hjlt hpos
        have hδeval : δ * (M - r0) = (y - r0) / 2 := by
          have hne : M - r0 ≠ 0 := sub_ne_zero.2 (ne_of_gt hMr0')
          calc
            δ * (M - r0) = ((y - r0) / (2 * (M - r0))) * (M - r0) := by simp [δ]
            _ = ((y - r0) * (M - r0)) / (2 * (M - r0)) := by
                  simp [div_mul_eq_mul_div]
            _ = (y - r0) / 2 := by
                  simpa using
                    (mul_div_mul_right (y - r0) (2 : Real) (c := (M - r0)) hne)
        have hy_mid : (r0 + y) / 2 < y := by linarith [hr0_lt_y]
        have hR :
            (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) < y := by
          -- Rewrite the sum and estimate using `hjlt`.
          have hw1' : (∑ i ∈ (Finset.univ.erase j), w i) = 1 - w j := by
            have hsplit :=
              (Finset.univ.sum_erase_add (f := w) (Finset.mem_univ j))
            have hw1'' : (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := hw1
            linarith [hsplit, hw1'']
          have hsum :
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) =
                w j * r0 + (1 - w j) * M := by
            have hsplit :=
              (Finset.univ.sum_erase_add (f := fun i => w i * μ i) (Finset.mem_univ j))
            have hsum' :
                (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) =
                  (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) + w j * μ j := by
              exact hsplit.symm
            have hsum_erase :
                (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) =
                  (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by
              classical
              have hrewrite :
                  (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) =
                    ∑ i ∈ (Finset.univ.erase j), w i * M := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hij : i ≠ j := (Finset.mem_erase.mp hi).1
                simp [μ, hij]
              have hfact :
                  (∑ i ∈ (Finset.univ.erase j), w i * M : Real) =
                    (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by
                simpa using
                  (Finset.sum_mul (s := (Finset.univ.erase j)) (f := w) (a := M)).symm
              simpa [hrewrite] using hfact
            -- Put everything together.
            calc
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real)
                  = (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) + w j * μ j := hsum'
              _ = (∑ i ∈ (Finset.univ.erase j), w i : Real) * M + w j * r0 := by
                    rw [hsum_erase]
                    simp [μ]
              _ = w j * r0 + (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by ac_rfl
              _ = w j * r0 + (1 - w j) * M := by simp [hw1']
          -- Now bound `w j * r0 + (1 - w j) * M`.
          have hbound :
              w j * r0 + (1 - w j) * M < y := by
            have hrewrite : w j * r0 + (1 - w j) * M = r0 + (1 - w j) * (M - r0) := by
              ring
            have hstep :
                r0 + (1 - w j) * (M - r0) < r0 + δ * (M - r0) := by
              linarith [hδmul]
            have hstep' : r0 + δ * (M - r0) = (r0 + y) / 2 := by
              -- Use the definition of `δ`.
              have : r0 + δ * (M - r0) = r0 + (y - r0) / 2 := by
                simp [hδeval]
              -- Simplify.
              linarith
            calc
              w j * r0 + (1 - w j) * M
                  = r0 + (1 - w j) * (M - r0) := hrewrite
              _ < r0 + δ * (M - r0) := hstep
              _ = (r0 + y) / 2 := hstep'
              _ < y := hy_mid
          simpa [hsum] using hbound
        have hlt' :
            ((∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) : EReal) < (y : EReal) :=
          (EReal.coe_lt_coe_iff).2 hR
        exact lt_of_le_of_lt hle' hlt'
    · -- Vertex value finite: take `r0` as the midpoint between `f(b j)` and `y`.
      have hx0neBot : f (b j) ≠ (⊥ : EReal) := hx0bot
      set a : Real := (f (b j)).toReal
      have ha : (a : EReal) = f (b j) := by
        simpa [a] using (EReal.coe_toReal (x := f (b j)) hx0neTop hx0neBot)
      have ha_lt_y : a < y := by
        have : (a : EReal) < (y : EReal) := by simpa [ha] using hxy
        exact (EReal.coe_lt_coe_iff).1 this
      let r0 : Real := (a + y) / 2
      have hr0_lt_y : r0 < y := by
        dsimp [r0]
        nlinarith [ha_lt_y]
      have hvertex_le : f (b j) ≤ (r0 : EReal) := by
        have ha_le : a ≤ r0 := by
          dsimp [r0]
          nlinarith [ha_lt_y]
        simpa [ha] using (show (a : EReal) ≤ (r0 : EReal) from by exact_mod_cast ha_le)
      by_cases hMr0 : M ≤ r0
      · refine Filter.Eventually.of_forall ?_
        intro z
        have hzle : f z.1 ≤ (M : EReal) := hM z.1 z.2
        have hzle' : f z.1 ≤ (r0 : EReal) := le_trans hzle (by exact_mod_cast hMr0)
        have : (r0 : EReal) < (y : EReal) := (EReal.coe_lt_coe_iff).2 hr0_lt_y
        exact lt_of_le_of_lt hzle' this
      · have hMr0' : r0 < M := lt_of_not_ge hMr0
        let δ : Real := (y - r0) / (2 * (M - r0))
        have hδpos : 0 < δ := by
          have hy_r0 : 0 < y - r0 := by linarith
          have hden : 0 < 2 * (M - r0) := by nlinarith
          exact div_pos hy_r0 hden
        set B : AffineBasis (Fin (m + 1)) Real (affineSpan Real (Set.range b)) :=
          Section10.simplex_affineBasis_on_affineSpan (b := b) hb
        let incl : {z // z ∈ S} → affineSpan Real (Set.range b) :=
          fun z => ⟨z.1, convexHull_subset_affineSpan (𝕜 := Real) (s := Set.range b) z.2⟩
        have hcoord :
            ∀ᶠ z : {z // z ∈ S} in nhds (⟨b j, hx0S⟩ : {z // z ∈ S}),
              (1 - δ) < B.coord j (incl z) := by
          simpa [B, incl, S] using
            (Section10.vertex_coord_eventually_gt (b := b) hb j (δ := δ) hδpos)
        filter_upwards [hcoord] with z hzcoord
        let q : affineSpan Real (Set.range b) := incl z
        let w : Fin (m + 1) → Real := fun i => B.coord i q
        have hw1 : (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := by
          simp [w]
        have hBcoe :
            ((affineSpan Real (Set.range b)).subtype ∘ fun i : Fin (m + 1) => B i) = b := by
          funext i
          change ((B i : Fin n → Real) = b i)
          simp [B, Section10.simplex_affineBasis_on_affineSpan]
          rfl
        have hzcomb : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w = z.1 := by
          have hq : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i)
              (fun i => B.coord i q) = q := by
            exact B.affineCombination_coord_eq_self q
          have hq' := congrArg ((affineSpan Real (Set.range b)).subtype) hq
          have hmap' :=
            (Finset.map_affineCombination (s := (Finset.univ : Finset (Fin (m + 1))))
              (p := fun i : Fin (m + 1) => B i) (w := fun i => B.coord i q) (hw := hw1)
              (f := (affineSpan Real (Set.range b)).subtype))
          simpa [q, w, incl, hBcoe] using (hmap'.symm.trans hq')
        have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w i := by
          intro i hi
          have hz_repr :
              ∃ w0 : Fin (m + 1) → Real, (∀ i, 0 ≤ w0 i) ∧ (∑ i, w0 i) = (1 : Real) ∧
                z.1 = ∑ i, w0 i • b i := by
            simpa [S, convexHull_range_eq_setOf_weighted_sum] using z.2
          rcases hz_repr with ⟨w0, hw0_nonneg, hw0_sum, hz0⟩
          have hw0_sum' :
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w0 i) = 1 := by
            simpa using hw0_sum
          have hz_aff : (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w0 = z.1 := by
            rw [Finset.affineCombination_eq_linear_combination _ _ _ hw0_sum']
            simpa using hz0.symm
          have hinj :
              Function.Injective ((affineSpan Real (Set.range b)).subtype) :=
            AffineSubspace.subtype_injective (affineSpan Real (Set.range b))
          have hqcomb :
              q =
                (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i) w0 := by
            apply hinj
            have hmap' :=
              (Finset.map_affineCombination (s := (Finset.univ : Finset (Fin (m + 1))))
                (p := fun i : Fin (m + 1) => B i) (w := w0) (hw := hw0_sum')
                (f := (affineSpan Real (Set.range b)).subtype))
            calc
              (affineSpan Real (Set.range b)).subtype q = z.1 := rfl
              _ = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b w0 := hz_aff.symm
              _ =
                  (Finset.univ : Finset (Fin (m + 1))).affineCombination Real
                    (((affineSpan Real (Set.range b)).subtype) ∘ fun i : Fin (m + 1) => B i) w0 := by
                    simpa using
                      congrArg
                        (fun p =>
                          (Finset.univ : Finset (Fin (m + 1))).affineCombination Real p w0)
                        (hBcoe.symm)
              _ =
                  (affineSpan Real (Set.range b)).subtype
                    ((Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => B i) w0) := by
                    simpa using hmap'.symm
          have hwi : B.coord i q = w0 i := by
            have := B.coord_apply_combination_of_mem (s := (Finset.univ : Finset (Fin (m + 1))))
              (i := i) (hi := by simp) (w := w0) hw0_sum'
            simpa [hqcomb] using this
          simpa [w, hwi] using (hw0_nonneg i)
        let μ : Fin (m + 1) → Real := fun i => if i = j then r0 else M
        have hμ : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), f (b i) ≤ (μ i : EReal) := by
          intro i hi
          by_cases hij : i = j
          · subst hij
            simpa [μ] using hvertex_le
          · have hbi : b i ∈ S :=
              (subset_convexHull (𝕜 := Real) (s := Set.range b) ⟨i, rfl⟩)
            have : f (b i) ≤ (M : EReal) := hM (b i) hbi
            simpa [μ, hij] using this
        have hle :=
          Section10.convexFunctionOn_le_affineCombination_real (hf := hf)
            (s := (Finset.univ : Finset (Fin (m + 1)))) (x := b) (μ := μ) (w := w)
            hμ hw0 hw1
        have hle' :
            f z.1 ≤ ((∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) : EReal) := by
          simpa [hzcomb] using hle
        have hjlt : 1 - w j < δ := by
          have : (1 - δ) < w j := by simpa [w, q] using hzcoord
          linarith
        have hpos : 0 < M - r0 := by linarith
        have hδmul : (1 - w j) * (M - r0) < δ * (M - r0) :=
          mul_lt_mul_of_pos_right hjlt hpos
        have hδeval : δ * (M - r0) = (y - r0) / 2 := by
          have hne : M - r0 ≠ 0 := sub_ne_zero.2 (ne_of_gt hMr0')
          calc
            δ * (M - r0) = ((y - r0) / (2 * (M - r0))) * (M - r0) := by simp [δ]
            _ = ((y - r0) * (M - r0)) / (2 * (M - r0)) := by
                  simp [div_mul_eq_mul_div]
            _ = (y - r0) / 2 := by
                  simpa using
                    (mul_div_mul_right (y - r0) (2 : Real) (c := (M - r0)) hne)
        have hy_mid : (r0 + y) / 2 < y := by linarith [hr0_lt_y]
        have hR :
            (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) < y := by
          have hw1' : (∑ i ∈ (Finset.univ.erase j), w i) = 1 - w j := by
            have hsplit :=
              (Finset.univ.sum_erase_add (f := w) (Finset.mem_univ j))
            have hw1'' : (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i) = 1 := hw1
            linarith [hsplit, hw1'']
          have hsum :
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) =
                w j * r0 + (1 - w j) * M := by
            have hsplit :=
              (Finset.univ.sum_erase_add (f := fun i => w i * μ i) (Finset.mem_univ j))
            have hsum' :
                (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) =
                  (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) + w j * μ j := by
              exact hsplit.symm
            have hsum_erase :
                (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) =
                  (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by
              classical
              have hrewrite :
                  (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) =
                    ∑ i ∈ (Finset.univ.erase j), w i * M := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hij : i ≠ j := (Finset.mem_erase.mp hi).1
                simp [μ, hij]
              have hfact :
                  (∑ i ∈ (Finset.univ.erase j), w i * M : Real) =
                    (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by
                simpa using
                  (Finset.sum_mul (s := (Finset.univ.erase j)) (f := w) (a := M)).symm
              simpa [hrewrite] using hfact
            calc
              (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real)
                  = (∑ i ∈ (Finset.univ.erase j), w i * μ i : Real) + w j * μ j := hsum'
              _ = (∑ i ∈ (Finset.univ.erase j), w i : Real) * M + w j * r0 := by
                    rw [hsum_erase]
                    simp [μ]
              _ = w j * r0 + (∑ i ∈ (Finset.univ.erase j), w i : Real) * M := by ac_rfl
              _ = w j * r0 + (1 - w j) * M := by simp [hw1']
          have hbound :
              w j * r0 + (1 - w j) * M < y := by
            have hrewrite : w j * r0 + (1 - w j) * M = r0 + (1 - w j) * (M - r0) := by
              ring
            have hstep :
                r0 + (1 - w j) * (M - r0) < r0 + δ * (M - r0) := by
              linarith [hδmul]
            have hstep' : r0 + δ * (M - r0) = (r0 + y) / 2 := by
              have : r0 + δ * (M - r0) = r0 + (y - r0) / 2 := by
                simp [hδeval]
              linarith
            calc
              w j * r0 + (1 - w j) * M
                  = r0 + (1 - w j) * (M - r0) := hrewrite
              _ < r0 + δ * (M - r0) := hstep
              _ = (r0 + y) / 2 := hstep'
              _ < y := hy_mid
          simpa [hsum] using hbound
        have hlt' :
            ((∑ i ∈ (Finset.univ : Finset (Fin (m + 1))), w i * μ i : Real) : EReal) < (y : EReal) :=
          (EReal.coe_lt_coe_iff).2 hR
        exact lt_of_le_of_lt hle' hlt'
/-- Upper semicontinuity within an `m`-simplex contained in `dom f`. -/
lemma Section10.upperSemicontinuousWithinAt_of_isSimplex {n m : ℕ}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {P : Set (Fin n → Real)} {x : Fin n → Real} (hP : IsSimplex n m P) (hxP : x ∈ P)
    (hPdom : P ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    UpperSemicontinuousWithinAt f P x := by
  classical
  rcases hP with ⟨b, hb, rfl⟩
  -- Choose barycentric coordinates for `x` in the simplex.
  have hxw :
      ∃ μ : Fin (m + 1) → Real, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i = (1 : Real)) ∧
        x = ∑ i, μ i • b i := by
    have : x ∈ {y : Fin n → Real |
        ∃ w : Fin (m + 1) → Real, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧
          x = ∑ i, w i • b i} := by
      simpa [convexHull_range_eq_setOf_weighted_sum] using hxP
    simpa using this
  rcases hxw with ⟨μ, hμ0, hμ1, hxμ⟩
  -- Work with the subfamily of facets indexed by vertices with positive weight in `x`.
  let J : Set (Fin (m + 1)) := { j | 0 < μ j }
  have hJne : (J : Set (Fin (m + 1))).Nonempty := by
    -- Specialize `exists_index_min_ratio_barycentric` to `ν := μ`.
    rcases
        exists_index_min_ratio_barycentric (μ := μ) (ν := μ) (m := m) hμ0 hμ1 hμ0 with
      ⟨j, hj, -⟩
    exact ⟨j, hj⟩
  let Pj : Fin (m + 1) → Set (Fin n → Real) := fun j =>
    convexHull Real (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i)))
  let 𝒮 : Set (Set (Fin n → Real)) := Set.range fun j : {j : Fin (m + 1) // j ∈ J} => Pj j.1
  have h𝒮fin : 𝒮.Finite := Set.finite_range _
  have hcover : (⋃₀ 𝒮) = convexHull Real (Set.range b) := by
    classical
    ext y
    constructor
    · intro hy
      rcases hy with ⟨Q, ⟨j, rfl⟩, hyQ⟩
      -- Each `Pj` is contained in the original simplex.
      have hsub : Pj j.1 ⊆ convexHull Real (Set.range b) := by
        refine convexHull_min ?_ (convex_convexHull Real (Set.range b))
        intro z hz
        rcases hz with (rfl | hz)
        · exact hxP
        · rcases hz with ⟨i, rfl⟩
          exact (subset_convexHull (𝕜 := Real) (s := Set.range b)) ⟨j.1.succAbove i, rfl⟩
      exact hsub hyQ
    · intro hy
      -- Represent `y` as a convex combination of vertices and use the min-ratio construction.
      rcases (by
        simpa [convexHull_range_eq_setOf_weighted_sum] using hy) with ⟨ν, hν0, hν1, hyν⟩
      rcases
          exists_index_min_ratio_barycentric (μ := μ) (ν := ν) (m := m) hμ0 hμ1 hν0 with
        ⟨j, hjμ, hcross⟩
      have hjJ : j ∈ J := hjμ
      refine ⟨Pj j, ⟨⟨j, hjJ⟩, rfl⟩, ?_⟩
      -- `y` lies in the cone-over-facet simplex determined by `j`.
      have hy_mem :
          y ∈ convexHull Real (Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j i))) := by
        exact
          mem_cone_facet_of_min_ratio (b := b) (x := x) (y := y) (μ := μ) (ν := ν)
            (hμ1 := hμ1) (hν0 := hν0) (hν1 := hν1) (hx := hxμ) (hy := hyν) (hμj := hjμ)
            (hcross := hcross)
      simpa [Pj] using hy_mem
  -- Upper semicontinuity on each cone-over-facet simplex at the common vertex `x`.
  have husc_each : ∀ Q ∈ 𝒮, UpperSemicontinuousWithinAt f Q x := by
    classical
    intro Q hQ
    rcases hQ with ⟨j, rfl⟩
    -- Each member of `𝒮` is of the form `convexHull (range (update b j x))` with `μ j > 0`.
    have hjμ : 0 < μ j.1 := j.2
    let b0 : Fin (m + 1) → Fin n → Real := Function.update b j.1 x
    have hrange :
        Set.range b0 =
          Set.insert x (Set.range fun i : Fin m => b (Fin.succAbove j.1 i)) := by
      simpa [b0] using
        (range_update_eq_insert_range_succAbove (b := b) (j := j.1) (x := x))
    have hx_not :
        x ∉ affineSpan Real (b '' { i | i ≠ j.1 }) :=
      not_mem_affineSpan_facet_of_barycentric_weight_pos (b := b) hb hμ1 hxμ hjμ
    have hx_not' : x ∉ affineSpan Real (b0 '' { i | i ≠ j.1 }) := by
      have himage : b0 '' { i | i ≠ j.1 } = b '' { i | i ≠ j.1 } := by
        ext y
        constructor
        · rintro ⟨i, hi, rfl⟩
          refine ⟨i, hi, ?_⟩
          have hij : i ≠ j.1 := by simpa using hi
          simp [b0, hij]
        · rintro ⟨i, hi, rfl⟩
          refine ⟨i, hi, ?_⟩
          have hij : i ≠ j.1 := by simpa using hi
          simp [b0, hij]
      simpa [himage] using hx_not
    have hrest :
        AffineIndependent Real (fun i : { y : Fin (m + 1) // y ≠ j.1 } => b0 i) := by
      let e : { y : Fin (m + 1) // y ≠ j.1 } ↪ Fin (m + 1) := ⟨Subtype.val, Subtype.val_injective⟩
      have : (fun i : { y : Fin (m + 1) // y ≠ j.1 } => b0 i) = fun i => b (e i) := by
        funext i
        simp [b0, e, i.property]
      simpa [this] using hb.comp_embedding e
    have hb0 : AffineIndependent Real b0 :=
      (AffineIndependent.affineIndependent_of_notMem_span (p := b0) (i := j.1) hrest (by
        simpa [b0] using hx_not'))
    have hdom0 :
        convexHull Real (Set.range b0) ⊆
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      intro z hz
      have hz' : z ∈ convexHull Real (Set.range b) := by
        have hsub : (Pj j.1) ⊆ convexHull Real (Set.range b) := by
          refine convexHull_min ?_ (convex_convexHull Real (Set.range b))
          intro u hu
          rcases hu with (rfl | hu)
          · exact hxP
          · rcases hu with ⟨i, rfl⟩
            exact (subset_convexHull (𝕜 := Real) (s := Set.range b)) ⟨j.1.succAbove i, rfl⟩
        -- `hz` is membership in `convexHull (range b0)`, rewrite via `hrange`.
        have hzPj : z ∈ Pj j.1 := by simpa [Pj, hrange, b0] using hz
        exact hsub hzPj
      exact hPdom hz'
    have husc0 :
        UpperSemicontinuousWithinAt f (convexHull Real (Set.range b0)) (b0 j.1) :=
      Section10.upperSemicontinuousWithinAt_of_isSimplex_vertex (hf := hf) (hb := hb0) hdom0 j.1
    -- Rewrite `b0 j.1 = x` and the simplex set.
    simpa [Pj, hrange, b0] using husc0
  -- Combine across the finite cover.
  have husc_union : UpperSemicontinuousWithinAt f (⋃₀ 𝒮) x :=
    upperSemicontinuousWithinAt_sUnion_of_finite (f := f) (x := x) h𝒮fin husc_each
  simpa [hcover] using husc_union

/-- Theorem 10.2. Let `f` be a convex function on `ℝ^n`, and let `S` be any locally simplicial
subset of `dom f`. Then `f` is upper semicontinuous relative to `S`, so that if `f` is closed,
then `f` is continuous relative to `S`. -/
theorem convexFunctionOn_upperSemicontinuousOn_of_locallySimplicial {n : ℕ}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {S : Set (Fin n → Real)} (hS : Set.LocallySimplicial n S)
    (hSdom : S ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    UpperSemicontinuousOn f S ∧ (ClosedConvexFunction f → ContinuousOn f S) := by
  classical
  -- TODO (Theorem 10.2): the main missing ingredient is upper semicontinuity at a point within a
  -- simplex contained in `dom f`. Once available, the locally simplicial hypothesis reduces the
  -- general case to finitely many simplices via `upperSemicontinuousWithinAt_sUnion_of_finite` and
  -- `upperSemicontinuousWithinAt_congr_of_local_eq`.
  have hUSC : UpperSemicontinuousOn f S := by
    intro x hxS
    rcases hS x hxS with ⟨𝒮, U, h𝒮fin, hUnhds, hsimplex, hUeq⟩
    have husc_sUnion : UpperSemicontinuousWithinAt f (⋃₀ 𝒮) x := by
      -- Reduce to upper semicontinuity on each simplex in the finite family.
      have husc_each : ∀ P ∈ 𝒮, UpperSemicontinuousWithinAt f P x := by
        intro P hP
        rcases hsimplex P hP with ⟨m, hPm, hPsubS⟩
        have hPdom : P ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
          fun y hy => hSdom (hPsubS hy)
        by_cases hxP : x ∈ P
        · -- Main missing step: upper semicontinuity of convex functions on simplices at points.
          exact
            Section10.upperSemicontinuousWithinAt_of_isSimplex (hf := hf) (hP := hPm)
              (hxP := hxP) (hPdom := hPdom)
        · -- If `x ∉ P` and `P` is closed, then `𝓝[P] x = ⊥`, hence semicontinuity is trivial.
          rcases hPm with ⟨b, hb, rfl⟩
          have hclosed : IsClosed (convexHull Real (Set.range b)) := by
            exact (Set.finite_range b).isCompact_convexHull.isClosed
          have hxcl : x ∉ closure (convexHull Real (Set.range b)) := by
            simpa [hclosed.closure_eq] using hxP
          have hbot : nhdsWithin x (convexHull Real (Set.range b)) = ⊥ :=
            (notMem_closure_iff_nhdsWithin_eq_bot).1 hxcl
          simp [UpperSemicontinuousWithinAt, hbot]
      exact upperSemicontinuousWithinAt_sUnion_of_finite (f := f) (x := x) h𝒮fin husc_each
    -- Transfer from the local finite union to `S` using the neighborhood equality.
    exact
      (upperSemicontinuousWithinAt_congr_of_local_eq (f := f) (s := ⋃₀ 𝒮) (t := S) (U := U)
          (x := x) hUnhds hUeq).1 husc_sUnion
  refine ⟨hUSC, ?_⟩
  intro hclosed x hxS
  -- Continuity follows from lower + upper semicontinuity.
  have hLower : LowerSemicontinuousWithinAt f S x :=
    (hclosed.2 x).lowerSemicontinuousWithinAt (s := S)
  have hUpper : UpperSemicontinuousWithinAt f S x := hUSC x hxS
  exact (continuousWithinAt_iff_lower_upperSemicontinuousWithinAt (f := f) (s := S) (x := x)).2
    ⟨hLower, hUpper⟩

/-- Extending a finite convex function by `⊤` outside a nonempty set yields a proper convex function
on `Set.univ`. -/
lemma Section10.properConvexFunctionOn_univ_extendTopOutside_ri {n : ℕ}
    {riCE : Set (EuclideanSpace Real (Fin n))} (hri : riCE.Nonempty)
    (f : EuclideanSpace Real (Fin n) → Real) (hfconv : ConvexOn ℝ riCE f)
    (e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x : Fin n → Real => by
        classical
        exact if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)) := by
  classical
  let F : (Fin n → Real) → EReal :=
    fun x => if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)
  have hconvF : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) F := by
    have hconv_g :
        ConvexOn ℝ {x : Fin n → Real | e.symm x ∈ riCE} (fun x => f (e.symm x)) := by
      simpa [Set.preimage, Function.comp] using
        (ConvexOn.comp_linearMap (hf := hfconv) (e.symm.toLinearMap))
    simpa [F] using
      (convexFunctionOn_univ_if_top (C := {x : Fin n → Real | e.symm x ∈ riCE}) (g := fun x =>
        f (e.symm x)) hconv_g)
  refine ⟨hconvF, ?_, ?_⟩
  · rcases hri with ⟨x0, hx0⟩
    refine ⟨(e x0, f x0), ?_⟩
    have : F (e x0) ≤ ((f x0) : EReal) := by
      simp [F, hx0]
    exact (mem_epigraph_univ_iff (f := F)).2 this
  · intro x _
    by_cases hx : e.symm x ∈ riCE
    · simp [hx]
    · simp [hx]

/-- For the `⊤`-extension `F` outside the relative interior `riCE`, the effective domain of `F`
pulled back to `EuclideanSpace` is exactly `riCE`; hence its relative interior is `riCE`. -/
lemma Section10.preimage_effectiveDomain_extendTopOutside_ri {n : ℕ} {C : Set (Fin n → Real)}
    (f : EuclideanSpace Real (Fin n) → Real) :
    let CE : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C
    let riCE : Set (EuclideanSpace Real (Fin n)) := euclideanRelativeInterior n CE
    let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
    let F : (Fin n → Real) → EReal :=
      fun x : Fin n → Real => by
        classical
        exact if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)
    ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) F = riCE) ∧
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) F) = riCE := by
  classical
  intro CE riCE e F
  have hdom :
      ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) F) = riCE := by
    ext z
    constructor
    · intro hz
      have hz_lt : F (z : Fin n → Real) < (⊤ : EReal) := by
        have :
            (z : Fin n → Real) ∈
              {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ F x < (⊤ : EReal)} := by
          simpa [effectiveDomain_eq] using hz
        exact this.2
      by_contra hzri
      have hz_eq : (z : Fin n → Real) = e z := by
        simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hsymm : e.symm (z : Fin n → Real) = z := by
        simp [hz_eq]
      have : F (z : Fin n → Real) = (⊤ : EReal) := by
        simp [F, hsymm, hzri]
      exact (lt_irrefl (⊤ : EReal)) (this ▸ hz_lt)
    · intro hzri
      have hsymm : e.symm (z : Fin n → Real) = z := by
        have hz_eq : (z : Fin n → Real) = e z := by
          simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
        simp [hz_eq]
      have hz_lt : F (z : Fin n → Real) < (⊤ : EReal) := by
        simp [F, hsymm, hzri, EReal.coe_lt_top]
      have :
          (z : Fin n → Real) ∈
            {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ F x < (⊤ : EReal)} := by
        exact ⟨by simp, hz_lt⟩
      simpa [effectiveDomain_eq] using this
  refine ⟨hdom, ?_⟩
  -- `ri (riCE) = riCE` since `riCE` is itself a relative interior.
  have hri_idem :
      euclideanRelativeInterior n (euclideanRelativeInterior n CE) =
        euclideanRelativeInterior n CE :=
    (euclidean_closure_closure_eq_and_relativeInterior_relativeInterior_eq n CE).2
  simpa [hdom, riCE] using hri_idem

/-- Boundedness above on bounded subsets of `riCE` forces the convex closure of the `⊤`-extension
to be finite at any point in the closure of `riCE`. -/
lemma Section10.convexFunctionClosure_ne_top_of_mem_closure_ri_of_bddAbove {n : ℕ}
    {riCE : Set (EuclideanSpace Real (Fin n))} {f : EuclideanSpace Real (Fin n) → Real}
    (hf_bddAbove : ∀ s, s ⊆ riCE → Bornology.IsBounded s → BddAbove (f '' s))
    (e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    (y : Fin n → Real) (hy : (e.symm y : EuclideanSpace Real (Fin n)) ∈ closure riCE) :
    convexFunctionClosure (fun x : Fin n → Real => by
        classical
        exact if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)) y ≠ (⊤ : EReal) := by
  classical
  let F : (Fin n → Real) → EReal :=
    fun x : Fin n → Real => if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)
  let clF : (Fin n → Real) → EReal := convexFunctionClosure F
  -- Approximate `yE := e.symm y` by a sequence in `riCE`.
  rcases (mem_closure_iff_seq_limit).1 hy with ⟨u, hu_mem, hu_tendsto⟩
  have hbounded : Bornology.IsBounded (Set.range u) :=
    Metric.isBounded_range_of_tendsto (u := u) hu_tendsto
  have hbddAbove : BddAbove (f '' Set.range u) :=
    hf_bddAbove (Set.range u) (by
      intro x hx
      rcases hx with ⟨k, rfl⟩
      exact hu_mem k) hbounded
  rcases hbddAbove with ⟨M, hM⟩
  have hfu_le : ∀ k, f (u k) ≤ M := by
    intro k
    apply hM
    refine ⟨u k, ⟨k, rfl⟩, rfl⟩
  -- Show `(y, M)` is in the closure of the epigraph of `F`.
  have hbot : ∀ x, F x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : e.symm x ∈ riCE
    · simp [F, hx, EReal.coe_ne_bot]
    · simp [F, hx]
  have h_epi :
      epigraph (S := (Set.univ : Set (Fin n → Real))) clF =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) F) :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := F) hbot).1
  have hyM :
      (y, M) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) F) := by
    -- Use the sequence `k ↦ (e (u k), M)` in the epigraph.
    refine (mem_closure_iff_seq_limit).2 ?_
    refine ⟨(fun k : ℕ => (e (u k), M)), ?_, ?_⟩
    · intro k
      have hsymm : e.symm (e (u k)) = u k := by
        simp
      have hF_le : F (e (u k)) ≤ (M : EReal) := by
        have hu : u k ∈ riCE := hu_mem k
        have : (f (u k) : EReal) ≤ (M : EReal) := by exact_mod_cast (hfu_le k)
        simpa [F, hsymm, hu] using this
      exact (mem_epigraph_univ_iff (f := F)).2 hF_le
    · have ht1 :
        Filter.Tendsto (fun k : ℕ => e (u k)) Filter.atTop (nhds y) := by
        simpa using (e.continuous.tendsto (e.symm y)).comp hu_tendsto
      have ht2 : Filter.Tendsto (fun _ : ℕ => M) Filter.atTop (nhds M) := tendsto_const_nhds
      simpa using (Filter.Tendsto.prodMk_nhds ht1 ht2)
  have hyM' :
      (y, M) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) clF := by
    simpa [h_epi] using hyM
  have hle : clF y ≤ (M : EReal) :=
    (mem_epigraph_univ_iff (f := clF)).1 hyM'
  intro htop
  have htop' : clF y = (⊤ : EReal) := by
    simpa [clF, F] using htop
  have hle' := hle
  simp [htop'] at hle'

/-- If two functions are continuous relative to `CE` and agree on `riCE`, then they agree on `CE`
provided `riCE ⊆ CE` and `CE ⊆ closure riCE`. -/
lemma Section10.unique_extension_on_C_of_continuous_eqOn_ri {n : ℕ}
    {CE riCE : Set (EuclideanSpace Real (Fin n))} (hri : riCE ⊆ CE)
    (hclosure : CE ⊆ closure riCE) {g g' : EuclideanSpace Real (Fin n) → Real}
    (hg : Function.ContinuousRelativeTo g CE) (hg' : Function.ContinuousRelativeTo g' CE)
    (hEq : ∀ x ∈ riCE, g x = g' x) :
    ∀ x ∈ CE, g x = g' x := by
  classical
  intro x hxCE
  have hxcl : x ∈ closure riCE := hclosure hxCE
  rcases (mem_closure_iff_seq_limit).1 hxcl with ⟨u, hu_mem, hu_tendsto⟩
  have hu_memCE : ∀ k, u k ∈ CE := fun k => hri (hu_mem k)
  have ht_g :
      Filter.Tendsto (fun k => g (u k)) Filter.atTop (nhds (g x)) :=
    (Function.continuousRelativeTo_iff_seq_tendsto g CE).1 hg x hxCE u hu_memCE hu_tendsto
  have ht_g' :
      Filter.Tendsto (fun k => g' (u k)) Filter.atTop (nhds (g' x)) :=
    (Function.continuousRelativeTo_iff_seq_tendsto g' CE).1 hg' x hxCE u hu_memCE hu_tendsto
  have hEq_seq : (fun k => g (u k)) = fun k => g' (u k) := by
    funext k
    exact hEq (u k) (hu_mem k)
  have ht_g'' : Filter.Tendsto (fun k => g (u k)) Filter.atTop (nhds (g' x)) := by
    simpa [hEq_seq] using ht_g'
  exact tendsto_nhds_unique ht_g ht_g''


end Section10
end Chap02
