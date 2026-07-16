import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_68_7
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18
import stacks_proof.stacks_project.Chap10.Lemma_10_71_6
import stacks_proof.stacks_project.Chap10.Lemma_10_71_8
import stacks_proof.stacks_project.Chap10.Lemma_10_72_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open IsLocalRing
open RingTheory
open RingTheory.Sequence
open scoped ENat Pointwise

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/- Domain triage:
* primary domain: local commutative algebra of module depth and residue-field Ext groups;
* sampled owner declarations of the same kind: `Ideal.depth`, the chapter-local bridge
  `moduleDepth`, and `Abelian.Ext` on `ModuleCat`;
* best owner abstraction: `Ideal.depth`, with `moduleDepth R M` as the canonical local bridge for
  the main theorem surface, while `Abelian.Ext` is the owner of the residue-field `Ext` groups
  whose first nonvanishing degree is the source-facing content here;
* layer: `moduleDepth` remains the owner-facing bridge reused downstream, while the least
  nonvanishing residue-field `Ext` degree is source-facing derived data in this file.
* primitive vs derived split: the primitive data here are the groups `Ext^i_R(k, M)` themselves;
  nonvanishing in degree `i` and the first such degree are derived API and should be built from
  that owner rather than encoded by repeated raw existential statements.
-/

/-- The residue-field `Ext` group `Ext^i_R(ResidueField R, M)`. -/
abbrev residueFieldExt (i : ℕ) :=
  Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R M) i

/-- Degree `i` is the first kind of datum used in this file: `Ext^i_R(ResidueField R, M)` is
nonzero. -/
def residueFieldExtNonzero (i : ℕ) : Prop :=
  ∃ e : residueFieldExt R M i, e ≠ 0

/-- Helper for Lemma 10.72.5: the maximal ideal cannot generate a nonzero finite module over a
local ring. This lets us rewrite `moduleDepth` as a supremum of regular-sequence lengths. -/
lemma maximalIdeal_smul_top_ne_top :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  -- A Jacobson-ideal version of Nakayama rules out `𝔪 M = M` for a nonzero finite module.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M)))

/-- Helper for Lemma 10.72.5: over a Noetherian local ring, depth zero is equivalent to the
absence of an `M`-regular element in the maximal ideal. -/
lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular :
    moduleDepth R M = 0 ↔ ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    -- A single regular element in `𝔪` gives a length-one regular sequence, forcing positive depth.
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((isWeaklyRegular_singleton_iff M x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal R := by
            exact hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular M x :=
            ((isRegular_cons_iff M x xs).1 hreg).1
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.72.5: the residue field is annihilated exactly by the maximal ideal. -/
lemma module_annihilator_residueField_eq_maximalIdeal :
    Module.annihilator R (ResidueField R) = maximalIdeal R := by
  ext x
  constructor
  · intro hx
    -- Evaluating at `1` identifies annihilators with the kernel of `R → κ(R)`.
    have hx0 : algebraMap R (ResidueField R) x = 0 := by
      simpa [Algebra.smul_def] using (Module.mem_annihilator.mp hx (1 : ResidueField R))
    exact (IsLocalRing.residue_eq_zero_iff (R := R) x).mp <| by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx0
  · intro hx
    -- Once `x` maps to zero in the residue field, it kills every residue-class scalar.
    have hx0 : algebraMap R (ResidueField R) x = 0 := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_eq_zero_iff (R := R) x).mpr hx
    exact Module.mem_annihilator.mpr fun y ↦ by
      rw [Algebra.smul_def, hx0, zero_mul]

/-- Helper for Lemma 10.72.5: nonvanishing of `Ext⁰_R(k, M)` is the same as the existence of a
nonzero `R`-linear map `k → M`. -/
lemma residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap :
    residueFieldExtNonzero R M 0 ↔ ∃ f : ResidueField R →ₗ[R] M, f ≠ 0 := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(CategoryTheory.Abelian.Ext.addEquiv₀ e).hom, ?_⟩
    intro hf
    apply he
    apply (CategoryTheory.Abelian.Ext.addEquiv₀).injective
    exact ModuleCat.hom_injective (by simpa using hf)
  · rintro ⟨f, hf⟩
    refine ⟨(CategoryTheory.Abelian.Ext.addEquiv₀).symm (ModuleCat.ofHom f), ?_⟩
    intro heq
    have hmor : ModuleCat.ofHom f = 0 := by
      simpa using congrArg (fun e ↦ CategoryTheory.Abelian.Ext.addEquiv₀ e) heq
    have hf0 : f = 0 := by
      simpa using congrArg ModuleCat.Hom.hom hmor
    exact hf hf0

/-- Helper for Lemma 10.72.5: a nonzero linear map from the residue field exists exactly when the
space of such maps is not subsingleton. -/
lemma exists_nonzero_linearMap_iff_not_subsingleton :
    (∃ f : ResidueField R →ₗ[R] M, f ≠ 0) ↔
      ¬ Subsingleton (ResidueField R →ₗ[R] M) := by
  constructor
  · rintro ⟨f, hf⟩ hsub
    exact hf (Subsingleton.elim _ _)
  · intro hsub
    classical
    by_cases hlin : Subsingleton (ResidueField R →ₗ[R] M)
    · exact False.elim (hsub hlin)
    · letI : Nontrivial (ResidueField R →ₗ[R] M) :=
        not_subsingleton_iff_nontrivial.mp hlin
      obtain ⟨f, hf⟩ := exists_ne (0 : ResidueField R →ₗ[R] M)
      exact ⟨f, hf⟩

/-- Helper for Lemma 10.72.5: `Ext⁰_R(k, M)` is nonzero exactly in the depth-zero case. -/
lemma residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero :
    residueFieldExtNonzero R M 0 ↔ moduleDepth R M = 0 := by
  have hsub :
      Subsingleton (ResidueField R →ₗ[R] M) ↔
        ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
    constructor
    · intro hlin
      rcases
          (IsSMulRegular.subsingleton_linearMap_iff (R := R) (M := M)
            (N := ResidueField R)).1 hlin with
        ⟨x, hx, hxreg⟩
      refine ⟨x, ?_, hxreg⟩
      simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx
    · rintro ⟨x, hx, hxreg⟩
      exact
        (IsSMulRegular.subsingleton_linearMap_iff (R := R) (M := M)
          (N := ResidueField R)).2
          ⟨x, by simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx, hxreg⟩
  -- The degree-zero Ext group is `Hom(k, M)`, and depth zero is the negation of the same
  -- regular-element criterion that controls subsingularity of `Hom(k, M)`.
  rw [residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap (R := R) (M := M),
    exists_nonzero_linearMap_iff_not_subsingleton (R := R) (M := M),
    moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := M)]
  simpa [hsub]

/-- Helper for Lemma 10.72.5: positive depth yields a nonzerodivisor in the maximal ideal. -/
lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
    (hdepth : moduleDepth R M ≠ 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hno
  exact hdepth ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := M)).2 hno)

/-- Helper for Lemma 10.72.5: when the depth is the natural number `n`, some regular sequence in
the maximal ideal realizes that exact length. -/
lemma exists_regularSequence_of_length_eq_moduleDepth {n : ℕ}
    (hdepth : moduleDepth R M = n) :
    ∃ rs : List R, IsRegular M rs ∧ Ideal.ofList rs ≤ maximalIdeal R ∧ rs.length = n := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hsSup :
      sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) = n := by
    rw [← Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
    exact hdepth
  by_cases hn : n = 0
  · refine ⟨[], ?_, by simp, by simpa [hn]⟩
    simpa using (IsRegular.nil R M)
  · by_contra hno
    have hsSup_le : sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) ≤ n - 1 := by
      refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      have hrs_le :
          (rs.length : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) := by
        refine le_sSup ?_
        exact ⟨rs, hreg, hmem, rfl⟩
      have hrs_le_nat : rs.length ≤ n := by
        simpa [hsSup] using hrs_le
      have hrs_ne : rs.length ≠ n := by
        intro hrs_eq
        exact hno ⟨rs, hreg, hmem, hrs_eq⟩
      have hrs_lt : rs.length < n := lt_of_le_of_ne hrs_le_nat hrs_ne
      exact_mod_cast Nat.le_pred_of_lt hrs_lt
    have hnot_le : ¬ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) ≤ n - 1 := by
      rw [hsSup]
      have hlt_nat : n - 1 < n := by
        omega
      have hlt : ((n - 1 : ℕ) : ℕ∞) < n := by
        exact_mod_cast hlt_nat
      exact not_le_of_gt hlt
    exact hnot_le hsSup_le

/-- Helper for Lemma 10.72.5: if `depth(M) = n + 1`, then one can choose a maximal-ideal
nonzerodivisor whose quotient has depth exactly `n`. -/
lemma exists_mem_maximalIdeal_isSMulRegular_and_depth_drop_of_eq_succ {n : ℕ}
    (hdepth : moduleDepth R M = n + 1) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧ moduleDepth R (QuotSMulTop x M) = n := by
  obtain ⟨rs, hreg, hmem, hlen⟩ :=
    exists_regularSequence_of_length_eq_moduleDepth (R := R) (M := M) hdepth
  cases rs with
  | nil =>
      cases Nat.succ_ne_zero n (by simpa using hlen)
  | cons x xs =>
      have hx : x ∈ maximalIdeal R := by
        exact hmem (Ideal.subset_span (by simp))
      rcases (isRegular_cons_iff (M := M) x xs).1 hreg with ⟨hxreg, hxsreg⟩
      have hxs_len : xs.length = n := by
        simpa using hlen
      refine ⟨x, hx, hxreg, le_antisymm ?_ ?_⟩
      · -- Any longer regular sequence on the quotient would prepend to a too-long one on `M`.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
        rw [show moduleDepth R (QuotSMulTop x M) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
              hquot_smul]
        refine sSup_le ?_
        intro d hd
        rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
        have hx_single : IsRegular M [x] := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          exact IsRegular.cons hxreg (by simpa using (IsRegular.nil R (QuotSMulTop x M)))
        have hsingleton :
            Ideal.ofList [x] • (⊤ : Submodule R M) = x • (⊤ : Submodule R M) := by
          simp [Submodule.ideal_span_singleton_smul]
        have hysreg' : IsRegular (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))) ys := by
          exact ((Submodule.quotEquivOfEq _ _ hsingleton).isRegular_congr ys).2 hysreg
        have hcons_reg : IsRegular M ([x] ++ ys) := by
          simpa using RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular
            (M := M) hx_single hysreg'
        have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal R := by
          refine Ideal.span_le.mpr ?_
          intro r hr
          rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
          · exact hx
          · exact hysmem (Ideal.subset_span hyr)
        have hcons_le :
            (([x] ++ ys).length : ℕ∞) ≤ moduleDepth R M := by
          have hsmul :
              maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
            maximalIdeal_smul_top_ne_top (R := R) (M := M)
          rw [show moduleDepth R M =
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
              Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
          refine le_sSup ?_
          exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
        have hlength_le : ([x] ++ ys).length ≤ n + 1 := by
          simpa [hdepth] using hcons_le
        have hys_le : ys.length ≤ n := by
          simpa using hlength_le
        exact_mod_cast hys_le
      · -- The tail of a depth-realizing regular sequence gives the lower bound on the quotient depth.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
        rw [show moduleDepth R (QuotSMulTop x M) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
              hquot_smul]
        have hxs_le :
            ((xs.length : ℕ∞) ≤
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M))) := by
          refine le_sSup ?_
          refine ⟨xs, hxsreg, ?_, ?_⟩
          · refine Ideal.span_le.mpr ?_
            intro r hr
            exact hmem (Ideal.subset_span (List.mem_cons_of_mem _ hr))
          · rfl
        simpa [hxs_len] using hxs_le

/-- Helper for Lemma 10.72.5: an element of the maximal ideal annihilates the residue field. -/
lemma smul_residueField_eq_zero_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) :
    ∀ y : ResidueField R, x • y = 0 := by
  intro y
  -- Rewrite maximal-ideal membership as an annihilator statement and apply it to `y`.
  have hx_ann : x ∈ Module.annihilator R (ResidueField R) := by
    simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx
  exact Module.mem_annihilator.mp hx_ann y

/-- Helper for Lemma 10.72.5: in the long exact sequence for `0 → M --x→ M → M/xM → 0`, the
endomorphism of `Ext^i_R(k, M)` induced by multiplication by `x ∈ 𝔪` is zero. -/
lemma residueFieldExt_self_map_zero_of_mem_maximalIdeal {x : R} {i : ℕ}
    (hx : x ∈ maximalIdeal R) (e : residueFieldExt R M i) :
    e.comp (mk₀ (ModuleCat.smulShortComplex (ModuleCat.of R M) x).f) (add_zero i) = 0 := by
  -- Route correction: normalize the categorical self-map to scalar multiplication by `x`
  -- before using Lemma 10.71.8, instead of fighting the long exact sequence API directly.
  have hsmul : x • e = 0 := by
    exact
      smul_ext_eq_zero_of_annihilates_target_or_source
        (R := R) (M := ResidueField R) (N := M)
        (x := x)
        (hx := Or.inr (smul_residueField_eq_zero_of_mem_maximalIdeal (R := R) (x := x) hx))
        (i := i) (e := e)
  -- The first map in `smulShortComplex` is multiplication by `x` on `M`.
  rw [smul_eq_comp_mk₀] at hsmul
  simpa [ModuleCat.smulShortComplex] using hsmul

/-- Helper for Lemma 10.72.5: once `Ext^i_R(k, M)` vanishes, the long exact sequence for
`0 → M --x→ M → M/xM → 0` identifies nonvanishing of `Ext^i_R(k, M/xM)` with nonvanishing of
`Ext^(i+1)_R(k, M)`. -/
lemma residueFieldExt_profile_step_of_prev_vanishing {x : R} {i : ℕ}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    (hprev : ¬ residueFieldExtNonzero R M i) :
    residueFieldExtNonzero R (QuotSMulTop x M) i ↔ residueFieldExtNonzero R M (i + 1) := by
  let S := ModuleCat.smulShortComplex (ModuleCat.of R M) x
  let hS : S.ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.comp hS.extClass rfl, ?_⟩
    intro hzero
    -- Exactness identifies the kernel of the connecting morphism with the image of `Ext^i(k, M)`.
    obtain ⟨e', he'⟩ :=
      covariant_sequence_exact₃ (ModuleCat.of R (ResidueField R)) hS e rfl hzero
    have he'zero : e' = 0 := by
      by_contra he'zero
      exact hprev ⟨e', he'zero⟩
    have hcomp_zero : e'.comp (mk₀ S.g) (add_zero i) = 0 := by
      simp [he'zero]
    have heq0 : e = 0 := by
      calc
        e = e'.comp (mk₀ S.g) (add_zero i) := he'.symm
        _ = 0 := hcomp_zero
    exact he heq0
  · rintro ⟨e, he⟩
    -- The self-map on `Ext^(i+1)(k, M)` is zero because `x` annihilates the residue field.
    have hself : e.comp (mk₀ S.f) (add_zero (i + 1)) = 0 := by
      simpa [S] using
        residueFieldExt_self_map_zero_of_mem_maximalIdeal
          (R := R) (M := M) (x := x) (i := i + 1) hx e
    obtain ⟨e', he'⟩ :=
      covariant_sequence_exact₁ (ModuleCat.of R (ResidueField R)) hS e hself (n₀ := i) rfl
    refine ⟨e', ?_⟩
    intro he'zero
    have hcomp_zero : e'.comp hS.extClass rfl = 0 := by
      rw [he'zero]
      exact
        zero_comp
          (X := ModuleCat.of R (ResidueField R))
          (Y := S.X₃) (Z := S.X₁) (n := i) hS.extClass (i + 1) rfl
    have heq0 : e = 0 := by
      calc
        e = e'.comp hS.extClass rfl := he'.symm
        _ = 0 := hcomp_zero
    exact he heq0

/-- Helper for Lemma 10.72.5: depth `n` determines the first nonzero residue-field `Ext` group and
forces vanishing in smaller degrees. -/
lemma residueFieldExt_profile_of_depth_eq {n : ℕ}
    (hdepth : moduleDepth R M = n) :
    residueFieldExtNonzero R M n ∧ ∀ i < n, ¬ residueFieldExtNonzero R M i := by
  induction n generalizing M with
  | zero =>
      refine ⟨?_, ?_⟩
      · -- In depth zero, the source criterion is exactly the nonvanishing of `Ext⁰(k, M)`.
        exact (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero (R := R) (M := M)).2 hdepth
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
      obtain ⟨x, hx, hreg, hquotdepth⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_and_depth_drop_of_eq_succ
          (R := R) (M := M) (n := n) hdepth
      letI : Nontrivial (QuotSMulTop x M) :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
      have hquot_profile :=
        ih (M := QuotSMulTop x M) hquotdepth
      have hzero_vanish : ¬ residueFieldExtNonzero R M 0 := by
        intro hzero
        have hdepth_zero :
            moduleDepth R M = 0 :=
          (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero (R := R) (M := M)).1 hzero
        have hsucc_ne_zero : (((n + 1 : ℕ) : WithTop ℕ) ≠ 0) := by
          exact_mod_cast Nat.succ_ne_zero n
        exact hsucc_ne_zero (hdepth.symm.trans hdepth_zero)
      have hvanish_lt : ∀ i < n + 1, ¬ residueFieldExtNonzero R M i := by
        intro i hi
        induction' i with i ih_i
        · exact hzero_vanish
        · have hprev : ¬ residueFieldExtNonzero R M i := by
            apply ih_i
            exact Nat.lt_trans (Nat.lt_succ_self i) hi
          have hquot_vanish : ¬ residueFieldExtNonzero R (QuotSMulTop x M) i := by
            exact hquot_profile.2 i (Nat.lt_of_succ_lt_succ hi)
          intro hnonzero
          exact hquot_vanish <|
            (residueFieldExt_profile_step_of_prev_vanishing
              (R := R) (M := M) (x := x) (i := i) hx hreg hprev).mpr hnonzero
      have hprev_n : ¬ residueFieldExtNonzero R M n :=
        hvanish_lt n (Nat.lt_succ_self n)
      refine ⟨?_, hvanish_lt⟩
      -- After proving vanishing below `n + 1`, the quotient nonvanishing in degree `n`
      -- transfers across the long exact sequence to `Ext^(n+1)(k, M)`.
      exact
        (residueFieldExt_profile_step_of_prev_vanishing
          (R := R) (M := M) (x := x) (i := n) hx hreg hprev_n).mp hquot_profile.1

/-- Some residue-field Ext group of a nonzero finite module over a Noetherian local ring is
nonzero. -/
-- Proof sketch: finite depth gives a natural number `n = depth(M)`, and the profile theorem shows
-- that `Ext^n_R(ResidueField R, M)` is already nonzero.
theorem exists_nonzero_residueFieldExt :
    ∃ i : ℕ, residueFieldExtNonzero R M i := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  refine ⟨n, ?_⟩
  exact
    (residueFieldExt_profile_of_depth_eq (R := R) (M := M) (n := n) <|
      by simpa using hn.symm).1

/-- The least index for which `Ext^i_R(ResidueField R, M)` is nonzero. -/
noncomputable def firstNonzeroResidueFieldExtIndex : ℕ :=
  let _ : DecidablePred (residueFieldExtNonzero R M) := Classical.decPred _
  Nat.find <| exists_nonzero_residueFieldExt R M

/-- The first nonvanishing residue-field Ext group of `M` is nonzero in the defining degree. -/
-- Proof sketch: this is the defining property of `Nat.find` applied to
-- `exists_nonzero_residueFieldExt`.
theorem firstNonzeroResidueFieldExtIndex_spec :
    residueFieldExtNonzero R M (firstNonzeroResidueFieldExtIndex R M) := by
  -- `Nat.find` returns a witness for the existential used in the definition.
  classical
  simpa [firstNonzeroResidueFieldExtIndex] using
    Nat.find_spec (exists_nonzero_residueFieldExt R M)

-- Proof sketch: let `i(M)` be `firstNonzeroResidueFieldExtIndex M`. When `moduleDepth M = 0`, the
-- zeroth Ext group is `Hom_R(ResidueField R, M)`, and its nonvanishing is equivalent to
-- `maximalIdeal R ∈ associatedPrimes R M`. For positive depth, choose a nonzerodivisor
-- `x ∈ maximalIdeal R`, apply the long exact Ext sequence for `0 → M --x→ M → M / xM → 0`, use
-- that `x` acts trivially on residue-field Ext groups, deduce `i(M / xM) = i(M) - 1`, and combine
-- this with the depth drop `moduleDepth (M / xM) = moduleDepth M - 1`.
/-- Lemma 10.72.5: for a nonzero finite module `M` over a Noetherian local ring `R`, the depth of
`M` is the least integer `i` such that `Ext^i_R(ResidueField R, M)` is nonzero. -/
@[stacks 00LW]
theorem moduleDepth_eq_firstNonzeroResidueFieldExtIndex :
    moduleDepth R M = (firstNonzeroResidueFieldExtIndex R M : WithTop ℕ) := by
  classical
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth R M = n := by
    simpa using hn.symm
  have hprofile :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := M) (n := n) hdepth
  have hfind_le : firstNonzeroResidueFieldExtIndex R M ≤ n := by
    exact Nat.find_min' (exists_nonzero_residueFieldExt R M) hprofile.1
  have hfind_ge : n ≤ firstNonzeroResidueFieldExtIndex R M := by
    by_contra hlt
    exact
      (hprofile.2 _ (lt_of_not_ge hlt))
        (firstNonzeroResidueFieldExtIndex_spec (R := R) (M := M))
  rw [hdepth, le_antisymm hfind_le hfind_ge]
  rfl

end
