import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Tactic.NoncommRing

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [DivisionRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
variable {m : ℕ}

namespace Affine.Simplex

/-
Source/core/bridge triage:
- `source-facing`: Theorem 10.1.6 says that if `x ∈ s.closedInterior`, then every
  `y ∈ s.closedInterior` lies in a same-dimensional simplex contained in `s` whose vertices are
  `x` together with exactly `m` of the `m + 1` original vertices of `s`.
- `core/canonical`: the owner abstraction is mathlib's bundled simplex `Affine.Simplex 𝕜 P m`,
  with carrier set `Affine.Simplex.closedInterior`; public theorem surfaces are stated in terms of
  an existential pointed subsimplex `t : Affine.Simplex 𝕜 P m`.
- `bridge/view`: under `[NeZero m]`, the codimension-one piece is packaged as
  `Affine.Simplex.faceOpposite`, with `s.range_faceOpposite_points` providing the thin bridge to
  the primitive omitted-vertex set.
- Primitive data vs derived API: the public source-facing output is the omitted index
  `i : Fin (m + 1)` together with a same-dimensional simplex `t` whose vertex set is
  `insert x (s.points '' ({i}ᶜ))`; `replaceVertex` is an internal constructor used to witness this
  existential output. The omitted-face owner `s.faceOpposite i` is bridge-level data.
- Domain-style sampling used here: `Affine.Simplex.closedInterior`,
  `Affine.Simplex.faceOpposite`, `Affine.Simplex.range_faceOpposite_points`, and
  `AffineIndependent.affineIndependent_update_of_notMem_affineSpan`.
- Layer target: this item stays source-facing, but its public API is attached directly to the
  canonical owner `Affine.Simplex`; `replaceVertex` is kept as implementation scaffolding at the
  primitive omitted-vertex layer, and `faceOpposite` remains a thin bridge/view companion.
- Ambient refinement: the source theorem is real-simplex geometry, but its barycentric
  comparison/minimum-ratio argument is expected to live at an ordered-field layer rather than a
  normed or finite-dimensional real model. We keep the public statements at
  `[DivisionRing 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]` (not the stronger concrete `ℝ`
  specialization).
-/

section ReplaceVertex

/-- The simplex obtained from `s` by replacing the vertex indexed by `i` with `x`. The hypothesis
states that `x` lies outside the affine span of the omitted-vertex set
`s.points '' ({i}ᶜ)`. -/
private def replaceVertex (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) : Simplex 𝕜 P m where
  points := Function.update s.points i x
  independent :=
    s.independent.affineIndependent_update_of_notMem_affineSpan <| by
      simpa using hxi

@[simp] private theorem replaceVertex_points_self (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    (s.replaceVertex i x hxi).points i = x := by
  simp [replaceVertex, Function.update]

@[simp] private theorem replaceVertex_points_of_ne (s : Simplex 𝕜 P m) {i j : Fin (m + 1)} (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) (hji : j ≠ i) :
    (s.replaceVertex i x hxi).points j = s.points j := by
  simp [replaceVertex, Function.update, hji]

/-- The vertices of `s.replaceVertex i x hxi` are exactly `x` together with the vertices of the
simplex `s` other than `s.points i`, at the primitive omitted-vertex-set layer. -/
private theorem range_replaceVertex_points (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    Set.range (s.replaceVertex i x hxi).points =
      insert x (s.points '' ({i}ᶜ)) := by
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst hji
      simp
    · right
      refine ⟨j, ?_, ?_⟩
      · simpa using hji
      · simp [replaceVertex, Function.update, hji]
  · intro hp
    rcases hp with rfl | hp
    · exact ⟨i, by simp [replaceVertex, Function.update]⟩
    · rcases hp with ⟨j, hj, rfl⟩
      have hji : j ≠ i := by simpa using hj
      refine ⟨j, ?_⟩
      simp [replaceVertex, Function.update, hji]

section FaceOppositeBridge

variable [NeZero m]

/-- Under `m ≠ 0`, the primitive omitted-vertex set agrees with the opposite-face vertex set. -/
private theorem range_replaceVertex_points_faceOpposite (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    Set.range (s.replaceVertex i x hxi).points =
      insert x (Set.range (s.faceOpposite i).points) := by
  simpa [s.range_faceOpposite_points] using s.range_replaceVertex_points i x hxi

end FaceOppositeBridge

end ReplaceVertex

private theorem affineCombination_replaceVertex_transfer
    (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P) (α β : Fin (m + 1) → 𝕜)
    (hαsum : ∑ j, α j = 1) (hβsum : ∑ j, β j = 1)
    (hxEq : Finset.univ.affineCombination 𝕜 s.points α = x) (c : 𝕜)
    (hci : c * α i = β i) :
    Finset.univ.affineCombination 𝕜 (Function.update s.points i x)
        (Function.update (fun j => β j - c * α j) i c) =
      Finset.univ.affineCombination 𝕜 s.points β := by
  have hUpdateSum : ∑ j, (Function.update (fun j => β j - c * α j) i c) j = 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hβsum, hαsum, ← hci]
    noncomm_ring
  apply (vsub_left_cancel (p := s.points i))
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      (s := Finset.univ) (w := Function.update (fun j => β j - c * α j) i c)
      (p := Function.update s.points i x) hUpdateSum (b := s.points i)]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      (s := Finset.univ) (w := β) (p := s.points) hβsum (b := s.points i)]
  simp only [vadd_vsub]
  have hxv : x -ᵥ s.points i = ∑ j, α j • (s.points j -ᵥ s.points i) := by
    calc
      x -ᵥ s.points i = (Finset.univ.affineCombination 𝕜 s.points α) -ᵥ s.points i := by simp [hxEq]
      _ = (Finset.univ.weightedVSubOfPoint s.points (s.points i)) α := by
        rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
          (s := Finset.univ) (w := α) (p := s.points) hαsum (b := s.points i)]
        simp
      _ = ∑ j, α j • (s.points j -ᵥ s.points i) := by
        simp [Finset.weightedVSubOfPoint_apply]
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply]
  have hsplitL := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i)
    (f := fun j => (Function.update (fun j => β j - c * α j) i c) j •
      (Function.update s.points i x j -ᵥ s.points i))
  have hsplitR := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i) (f := fun j => β j • (s.points j -ᵥ s.points i))
  rw [hsplitL, hsplitR]
  simp only [Function.update_self, vsub_self, smul_zero, add_zero, add_right_inj]
  have hxv' : c • (x -ᵥ s.points i) = ∑ j, (c * α j) • (s.points j -ᵥ s.points i) := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [smul_smul]
  rw [hxv']
  have hsplitC := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i) (f := fun j => (c * α j) • (s.points j -ᵥ s.points i))
  rw [hsplitC]
  simp only [vsub_self, smul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    exact fun hji => (Finset.mem_sdiff.mp hj).2 (by simpa [hji])
  simp [Function.update_of_ne hji, hji, ← add_smul, sub_add_cancel]

section Ordered

variable [LinearOrder 𝕜] [IsOrderedRing 𝕜]

private theorem closedInterior_replaceVertex_subset_of_mem_closedInterior
    (s : Simplex 𝕜 P m) (x : P) (hx : x ∈ s.closedInterior)
    (i : Fin (m + 1)) (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior := by
  rcases hx with ⟨α, hαsum, hαIcc, hxEq⟩
  intro z hz
  rcases hz with ⟨lam, hLamSum, hLamIcc, hzEq⟩
  let c : 𝕜 := lam i
  let β : Fin (m + 1) → 𝕜 := Function.update (fun j => lam j + c * α j) i (c * α i)
  have hβdef : Function.update (fun j => β j - c * α j) i c = lam := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [β, c]
    · simp [β, c, hji, sub_add_cancel]
  have hβsum : ∑ j, β j = 1 := by
    dsimp [β]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hLamSum, hαsum]
    noncomm_ring
  have hβIcc : ∀ j, β j ∈ Set.Icc (0 : 𝕜) 1 := by
    intro j
    by_cases hji : j = i
    · subst hji
      constructor
      · simp [β, c, mul_nonneg, (hLamIcc j).1, (hαIcc j).1]
      · have hmul_le : c * α j ≤ (1 : 𝕜) * 1 := by
          refine mul_le_mul (hLamIcc j).2 (hαIcc j).2 (hαIcc j).1 ?_
          simpa using (show (0 : 𝕜) ≤ (1 : 𝕜) from zero_le_one)
        simpa [β, c] using hmul_le
    · constructor
      · have hmul_nonneg : 0 ≤ c * α j := mul_nonneg (hLamIcc i).1 (hαIcc j).1
        have hnonneg : 0 ≤ lam j + c * α j := add_nonneg (hLamIcc j).1 hmul_nonneg
        simpa [β, c, hji] using hnonneg
      · have hmul_le_c : c * α j ≤ c := by
          calc
            c * α j ≤ c * 1 := mul_le_mul_of_nonneg_left (hαIcc j).2 (hLamIcc i).1
            _ = c := by simp
        have hlamj_le_sumErase : lam j ≤ Finset.sum (Finset.univ.erase i) lam := by
          refine Finset.single_le_sum ?_ ?_
          · intro k hk
            exact (hLamIcc k).1
          · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
        have hsumErase_plus_c : Finset.sum (Finset.univ.erase i) lam + c = 1 := by
          calc
            Finset.sum (Finset.univ.erase i) lam + c = ∑ k, lam k := by
              simpa [c] using (Finset.sum_erase_add (s := Finset.univ) (f := lam) (h := Finset.mem_univ i))
            _ = 1 := hLamSum
        have hlamj_plus_c_le_one : lam j + c ≤ (1 : 𝕜) := by
          calc
            lam j + c = c + lam j := by simp [add_comm]
            _ ≤ c + Finset.sum (Finset.univ.erase i) lam := add_le_add_right hlamj_le_sumErase c
            _ = 1 := by simpa [add_comm] using hsumErase_plus_c
        have hβj_le_one : lam j + c * α j ≤ (1 : 𝕜) := by
          calc
            lam j + c * α j = c * α j + lam j := by simp [add_comm]
            _ ≤ c + lam j := add_le_add_left hmul_le_c (lam j)
            _ = lam j + c := by simp [add_comm]
            _ ≤ 1 := hlamj_plus_c_le_one
        simpa [β, c, hji] using hβj_le_one
  have hzEq' : Finset.univ.affineCombination 𝕜 s.points β = z := by
    calc
      Finset.univ.affineCombination 𝕜 s.points β
          = Finset.univ.affineCombination 𝕜 (Function.update s.points i x) lam := by
            symm
            have hci' : c * α i = β i := by simp [β, c]
            simpa [hβdef] using
              s.affineCombination_replaceVertex_transfer i x α β hαsum hβsum hxEq c hci'
      _ = z := by
            simpa [replaceVertex] using hzEq
  exact ⟨β, hβsum, hβIcc, hzEq'⟩

-- Proof sketch: write `y` in barycentric coordinates relative to `s`. At least one coordinate can
-- be chosen as the omitted vertex while keeping the remaining coefficients nonnegative after
-- transferring the missing mass to the new vertex `x`; this yields a same-dimensional simplex
-- contained in `s` whose vertices are `x` together with the complementary original vertices
-- `s.points '' ({i}ᶜ)`.
-- Internal bridge: this dependent formulation is used only to construct the public
-- non-dependent existential theorem surface below.
private theorem exists_replaceVertex_of_mem_closedInterior_aux (s : Simplex 𝕜 P m) (x y : P)
    (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1),
      ∃ hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ)),
      (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior ∧
        y ∈ (s.replaceVertex i x hxi).closedInterior := by
  rcases hx with ⟨α, hαsum, hαIcc, hxEq⟩
  rcases hy with ⟨β, hβsum, hβIcc, hyEq⟩
  let nz : Finset (Fin (m + 1)) := Finset.univ.filter (fun j => α j ≠ 0)
  have hnz : nz.Nonempty := by
    have hsum_ne : (∑ j, α j) ≠ 0 := by simpa [hαsum] using (one_ne_zero : (1 : 𝕜) ≠ 0)
    rcases Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) hsum_ne with ⟨j, -, hj⟩
    exact ⟨j, by simpa [nz, hj]⟩
  have hαsum_nz : Finset.sum nz α = 1 := by
    simpa [nz, hαsum] using (Finset.sum_filter_ne_zero (s := Finset.univ) (f := α))
  have hβsum_nz_le_one : Finset.sum nz β ≤ (1 : 𝕜) := by
    have hcomp_nonneg : 0 ≤ Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact (hβIcc j).1
    have hsplit :
        Finset.sum nz β + Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β = ∑ j, β j := by
      simpa [nz] using (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j => α j ≠ 0) (f := β))
    calc
      Finset.sum nz β ≤ Finset.sum nz β + Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β :=
        le_add_of_nonneg_right hcomp_nonneg
      _ = ∑ j, β j := hsplit
      _ = 1 := hβsum
  have hβsum_nz_le_hαsum_nz : Finset.sum nz β ≤ Finset.sum nz α := by
    simpa [hαsum_nz] using hβsum_nz_le_one
  obtain ⟨k, hk_nz, hβk_le_αk⟩ :=
    Finset.exists_le_of_sum_le (s := nz) (f := β) (g := α) hnz hβsum_nz_le_hαsum_nz
  obtain ⟨i, hi_nz, hmin⟩ := Finset.exists_min_image nz (fun j => β j / α j) hnz
  have hαi_ne : α i ≠ 0 := (Finset.mem_filter.mp hi_nz).2
  have hαk_ne : α k ≠ 0 := (Finset.mem_filter.mp hk_nz).2
  have hαi_pos : 0 < α i := lt_of_le_of_ne (hαIcc i).1 (by simpa [eq_comm] using hαi_ne)
  have hαk_pos : 0 < α k := lt_of_le_of_ne (hαIcc k).1 (by simpa [eq_comm] using hαk_ne)
  have hratio_k_le_one : β k / α k ≤ (1 : 𝕜) := div_le_one_of_le₀ hβk_le_αk (hαIcc k).1
  have hc_le_one : β i / α i ≤ (1 : 𝕜) := le_trans (hmin k hk_nz) hratio_k_le_one
  have hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ)) := by
    intro hxspan
    have hm : Finset.univ.affineCombination 𝕜 s.points α ∈ affineSpan 𝕜 (s.points '' ({i}ᶜ)) := by
      simpa [hxEq] using hxspan
    have hαi_zero : α i = 0 := s.independent.eq_zero_of_affineCombination_mem_affineSpan
      (fs := Finset.univ) (w := α) (hw := by simpa using hαsum)
      (s := ({i}ᶜ : Set (Fin (m + 1)))) hm (hifs := by simp) (his := by simp)
    exact hαi_ne hαi_zero
  have hsub :
      (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior :=
    s.closedInterior_replaceVertex_subset_of_mem_closedInterior x ⟨α, hαsum, hαIcc, hxEq⟩ i hxi
  let c : 𝕜 := β i / α i
  let lam : Fin (m + 1) → 𝕜 := Function.update (fun j => β j - c * α j) i c
  have hci : c * α i = β i := by
    dsimp [c]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hαi_ne, mul_one]
  have hLamSum : ∑ j, lam j = 1 := by
    dsimp [lam]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hβsum, hαsum, ← hci]
    noncomm_ring
  have hLamIcc : ∀ j, lam j ∈ Set.Icc (0 : 𝕜) 1 := by
    intro j
    by_cases hji : j = i
    ·
      constructor
      · simpa [lam, c, hji] using (div_nonneg (hβIcc j).1 (hαIcc j).1)
      · simpa [lam, c, hji] using hc_le_one
    · constructor
      · by_cases hαj_ne : α j ≠ 0
        · have hj_nz : j ∈ nz := by simp [nz, hαj_ne]
          have hαj_pos : 0 < α j := lt_of_le_of_ne (hαIcc j).1 (by simpa [eq_comm] using hαj_ne)
          have hratio : c ≤ β j / α j := by simpa [c] using hmin j hj_nz
          have hmul_le : c * α j ≤ β j := (le_div_iff₀ hαj_pos).1 hratio
          have hnonneg : 0 ≤ β j - c * α j := (sub_nonneg).2 hmul_le
          simpa [lam, c, hji] using hnonneg
        · have hαj_zero : α j = 0 := by simpa using hαj_ne
          have hnonneg : 0 ≤ β j := (hβIcc j).1
          simpa [lam, c, hji, hαj_zero] using hnonneg
      · have hmul_nonneg : 0 ≤ c * α j := by
          exact mul_nonneg (div_nonneg (hβIcc i).1 (hαIcc i).1) (hαIcc j).1
        have hle : β j - c * α j ≤ β j := sub_le_self _ hmul_nonneg
        have hβj_le_one : β j ≤ (1 : 𝕜) := (hβIcc j).2
        exact (le_trans (by simpa [lam, c, hji] using hle) hβj_le_one)
  have hyi : y ∈ (s.replaceVertex i x hxi).closedInterior := by
    refine ⟨lam, hLamSum, hLamIcc, ?_⟩
    calc
      Finset.univ.affineCombination 𝕜 (s.replaceVertex i x hxi).points lam
          = Finset.univ.affineCombination 𝕜 (Function.update s.points i x) lam := by
            simp [replaceVertex]
      _ = Finset.univ.affineCombination 𝕜 s.points β := by
            simpa [lam] using
              s.affineCombination_replaceVertex_transfer i x α β hαsum hβsum hxEq c hci
      _ = y := hyEq
  exact ⟨i, hxi, hsub, hyi⟩

/-- Theorem 10.1.6, canonical source-facing owner form: `y` lies in a same-dimensional simplex
contained in `s` whose vertices are `x` together with exactly `m` of the `m + 1` vertices of
`s`. -/
theorem exists_pointedSubsimplex_of_mem_closedInterior (s : Simplex 𝕜 P m) (x y : P)
    (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1), ∃ t : Simplex 𝕜 P m,
      Set.range t.points = insert x (s.points '' ({i}ᶜ)) ∧
        t.closedInterior ⊆ s.closedInterior ∧ y ∈ t.closedInterior := by
  rcases s.exists_replaceVertex_of_mem_closedInterior_aux x y hx hy with ⟨i, hxi, hsub, hyi⟩
  refine ⟨i, s.replaceVertex i x hxi, ?_, hsub, hyi⟩
  exact s.range_replaceVertex_points i x hxi

section FaceOppositeBridge

variable [NeZero m]

/-- Face-opposite bridge form of Theorem 10.1.6 on the same non-dependent theorem surface. -/
theorem exists_pointedSubsimplex_of_mem_closedInterior_faceOpposite
    (s : Simplex 𝕜 P m) (x y : P) (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1), ∃ t : Simplex 𝕜 P m,
      Set.range t.points = insert x (Set.range (s.faceOpposite i).points) ∧
        t.closedInterior ⊆ s.closedInterior ∧ y ∈ t.closedInterior := by
  rcases s.exists_pointedSubsimplex_of_mem_closedInterior x y hx hy with ⟨i, t, hrange, hsub, hyi⟩
  refine ⟨i, t, ?_, hsub, hyi⟩
  simpa [s.range_faceOpposite_points] using hrange

end FaceOppositeBridge

end Ordered

end Affine.Simplex

end
