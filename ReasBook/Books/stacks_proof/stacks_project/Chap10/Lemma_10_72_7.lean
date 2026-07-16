import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.72.7: a finite subsingleton module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a subsingleton module, the top submodule is already `⊥`, so `𝔪 • M = M`.
  have htop_eq_bot : (⊤ : Submodule R M) = ⊥ := by
    ext m
    simp [Subsingleton.elim m 0]
  have hsmul_bot : maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext m
    simp
  have hsmul_top : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul_top

/-- Helper for Lemma 10.72.7: a maximal-ideal nonzerodivisor forces positive depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ moduleDepth R M := by
  letI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
  -- The singleton sequence `[x]` is regular, so its length contributes to the depth supremum.
  have hnil : IsRegular (R := R) (M := QuotSMulTop x M) [] := by
    simpa using (IsRegular.nil R (QuotSMulTop x M))
  have hsingleton_reg : IsRegular M [x] := by
    exact IsRegular.cons hreg hnil
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal R := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/- Domain-style sampling:
* primary domain: depth and regular sequences for finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`;
* best owner abstraction: the local depth owner is the chapter bridge `moduleDepth R M`, while
  regular sequences are owned by `RingTheory.Sequence.IsRegular`;
* source/core/bridge triage:
  `source-facing`: the one-step depth drop and the extension of a regular sequence to maximal
  length;
  `core/canonical`: `moduleDepth` and `IsRegular`;
  `bridge/view`: the quotient module `QuotSMulTop x M` and the tail list `rs'`.

Primitive data are only the module, the regular sequence owner predicate, and the quotient owner
`QuotSMulTop x M`. A package bundling the appended regularity proof, maximal-ideal membership, and
length equality is derived theorem-shaped API, so it should not be a public class. -/

namespace IsSMulRegular

/-- Helper for Lemma 10.72.7: quotienting by a maximal-ideal nonzerodivisor lowers depth by at
most one. -/
private lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    moduleDepth R (QuotSMulTop x M) ≤ moduleDepth R M - 1 := by
  letI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
  -- Rewrite both depths as suprema of regular-sequence lengths and prepend `x`.
  have hquot_smul :
      maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
  have hmodule_smul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth R M = n := by
    simpa using hn.symm
  rw [show moduleDepth R (QuotSMulTop x M) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : IsRegular M ([x] ++ ys) := by
    have hfull : IsRegular M (x :: ys) := by
      exact IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal R := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
    · exact hx
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([x] ++ ys).length : ℕ∞) ≤ moduleDepth R M) := by
    rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hmodule_smul]
    refine le_sSup ?_
    exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([x] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

-- Proof sketch: apply Lemma `10.72.6` to the short exact sequence
-- `0 → M --(x • ·)→ M → QuotSMulTop x M → 0`. The hypothesis `hreg` gives injectivity on the left,
-- `hx` ensures the quotient is still a module over the local ring with respect to the maximal
-- ideal, and comparing with the regular sequence `x` shows the inequalities from Lemma `10.72.6`
-- force the depth to drop by exactly one. Any nontriviality needed in the proof is recovered
-- internally from `hreg`.
/-- Lemma 10.72.7 (1): if `x ∈ 𝔪` is a nonzerodivisor on a finite module `M` over a Noetherian
local ring `R`, then the depth of `M / xM` is the depth of `M` minus `1`. -/
@[stacks 090R]
theorem moduleDepth_quotSMulTop_eq_sub_one {x : R}
    (hreg : IsSMulRegular M x) (hx : x ∈ maximalIdeal R) :
    moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    letI : Subsingleton (QuotSMulTop x M) := by infer_instance
    -- In the zero-module branch, both depths are `⊤`.
    have hdepth_M : moduleDepth R M = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) M
    have hdepth_quot : moduleDepth R (QuotSMulTop x M) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) (QuotSMulTop x M)
    simpa [hdepth_M, hdepth_quot]
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    let S := ModuleCat.smulShortComplex (ModuleCat.of R M) x
    let hS : S.ShortExact :=
      IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
    letI : Module.Finite R S.X₁ := by
      change Module.Finite R M
      infer_instance
    letI : Module.Finite R S.X₃ := by
      change Module.Finite R (QuotSMulTop x M)
      infer_instance
    -- Lemma `10.72.6` gives the lower bound, and the regular-sequence argument gives the upper.
    have hlower :
        moduleDepth R (QuotSMulTop x M) ≥ moduleDepth R M - 1 := by
      simpa [S, min_eq_right (tsub_le_self : moduleDepth R M - 1 ≤ moduleDepth R M)] using
        CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
          (R := R) (S := S) hS
    have hupper :
        moduleDepth R (QuotSMulTop x M) ≤ moduleDepth R M - 1 :=
      moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal (R := R) (M := M) hx hreg
    exact le_antisymm hupper hlower

end IsSMulRegular

namespace IsRegular

-- Proof sketch: induct on the difference between the current regular sequence length and the
-- depth. If the lengths already agree, take the empty tail. Otherwise, recover internally that
-- the current regular sequence already lies in `maximalIdeal R` using the auxiliary companion
-- `ofList_le_maximalIdeal`, apply part (1) to the quotient by that regular sequence to obtain
-- another nonzerodivisor in the maximal ideal, adjoin it using
-- `isRegular_append_of_isRegular_of_quotient_isRegular`, and continue until the resulting
-- sequence has length equal to the depth.
/-- Lemma 10.72.7 (2): every `M`-regular sequence over a Noetherian local ring extends to an
`M`-regular sequence whose length is the depth of `M`. The maximal-ideal containment of the
extended sequence is recovered from the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. -/
@[stacks 090R]
theorem exists_append_eq_moduleDepth {rs : List R} (hreg : IsRegular M rs) :
    ∃ rs' : List R,
      IsRegular M (rs ++ rs') ∧
        moduleDepth R M = (rs ++ rs').length := by
  induction rs generalizing M with
  | nil =>
      letI : Nontrivial M := hreg.nontrivial
      -- In the empty case, choose a depth-realizing regular sequence.
      have hsmul :
          maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        maximalIdeal_smul_top_ne_top (R := R) (M := M)
      have hfiniteDepth : moduleDepth R M < ⊤ := by
        simpa [moduleDepth] using
          Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
      have hdepth : moduleDepth R M = n := by
        simpa using hn.symm
      obtain ⟨rs', hreg', -, hlen'⟩ :=
        exists_regularSequence_of_length_eq_moduleDepth (R := R) (M := M) (n := n) hdepth
      refine ⟨rs', ?_, ?_⟩
      · simpa using hreg'
      · rw [hdepth]
        exact_mod_cast hlen'.symm
  | cons x xs ih =>
      -- Peel off the head element and recurse on the regular tail over the quotient.
      have hx : x ∈ maximalIdeal R := by
        by_contra hx_not_mem
        change x ∉ maximalIdeal R at hx_not_mem
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx_not_mem
        have hx_unit : IsUnit x := by
          exact not_not.mp hx_not_mem
        have hx_mem : x ∈ Ideal.ofList (x :: xs) := by
          exact Ideal.subset_span (by simp)
        have htop : Ideal.ofList (x :: xs) = ⊤ :=
          Ideal.eq_top_of_isUnit_mem (Ideal.ofList (x :: xs)) hx_mem hx_unit
        have hsmul : Ideal.ofList (x :: xs) • (⊤ : Submodule R M) = ⊤ := by
          simpa [htop]
        exact hreg.top_ne_smul hsmul.symm
      rcases (isRegular_cons_iff (M := M) x xs).1 hreg with ⟨hxreg, hxsreg⟩
      letI : Nontrivial (QuotSMulTop x M) := hxsreg.nontrivial
      obtain ⟨ys, htail_reg, htail_depth⟩ := ih (M := QuotSMulTop x M) hxsreg
      refine ⟨ys, ?_, ?_⟩
      · have hfull : IsRegular M (x :: (xs ++ ys)) := by
          exact IsRegular.cons hxreg htail_reg
        simpa [List.cons_append] using hfull
      · letI : Nontrivial M := hreg.nontrivial
        have hone : (1 : ℕ∞) ≤ moduleDepth R M :=
          one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular (R := R) (M := M) hx hxreg
        calc
          moduleDepth R M = moduleDepth R (QuotSMulTop x M) + 1 := by
            rw [IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := R) (M := M) hxreg hx]
            exact (tsub_add_cancel_of_le hone).symm
          _ = ((xs ++ ys).length : ℕ∞) + 1 := by
            rw [htail_depth]
          _ = (((x :: xs) ++ ys).length : ℕ∞) := by
            simp [List.cons_append]

-- Proof sketch: if `x ∈ rs` and `x ∉ maximalIdeal R`, then `x` generates the unit ideal, so
-- `Ideal.ofList rs = ⊤`. This contradicts the `top_ne_smul` field of `hreg`. Applying this to
-- every term of `rs` shows `Ideal.ofList rs ≤ maximalIdeal R`.
/-- Auxiliary companion: every `M`-regular sequence over a local ring is contained in
`maximalIdeal R`. -/
theorem ofList_le_maximalIdeal {rs : List R} (hreg : IsRegular M rs) :
    Ideal.ofList rs ≤ maximalIdeal R := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  -- An element of a regular sequence outside `𝔪` would be a unit, forcing the unit ideal.
  by_contra hx_not_mem
  change x ∉ maximalIdeal R at hx_not_mem
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx_not_mem
  have hx_unit : IsUnit x := by
    exact not_not.mp hx_not_mem
  have hx_mem : x ∈ Ideal.ofList rs := by
    exact Ideal.subset_span hx
  have htop : Ideal.ofList rs = ⊤ :=
    Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) hx_mem hx_unit
  have hsmul : Ideal.ofList rs • (⊤ : Submodule R M) = ⊤ := by
    simpa [htop]
  exact hreg.top_ne_smul hsmul.symm

end IsRegular

end
