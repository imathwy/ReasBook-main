import StacksProject_2024.Chap10.Definition_10_109_2
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_55_8
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_109_3
import StacksProject_2024.Chap10.Lemma_10_109_5
import StacksProject_2024.Chap10.Proposition_10_110_1
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_72_6
import Mathlib.Algebra.Category.ModuleCat.Ulift

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian.Ext
open CategoryTheory.ShortComplex.ShortExact
open IsLocalRing
open RingTheory.Sequence
open scoped ENat Pointwise TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling:
* primary domain: projective dimension and local depth for finite modules over Noetherian local
  rings;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `projectiveDimension_le_iff`,
  `moduleDepth`;
* best owner abstraction: the theorem should use the canonical owners
  `projectiveDimension (ModuleCat.of R M)` and `moduleDepth R _` directly;
* source/core/bridge triage:
  `source-facing`: the Auslander--Buchsbaum equality for a finite module over a Noetherian local
    ring;
  `core/canonical`: `projectiveDimension` and `moduleDepth`;
  `bridge/view`: the self-module specialization `moduleDepth R R`, which is the chapter's canonical
    surface for ring depth rather than a separate local definition.

Primitive data are only the finite module and the canonical projective-dimension value. The
`Nontrivial M` assumption is derived from `hpd : projectiveDimension (ModuleCat.of R M) = d`, since
the zero module has projective dimension `⊥`, so it should not remain a primitive hypothesis.
-/

-- Proof sketch: choose a minimal finite free resolution of `M`; the Buchsbaum--Eisenbud
-- acyclicity criterion and the depth inequalities for short exact sequences handle the case
-- `moduleDepth R M = 0`. For positive depth, choose a nonzerodivisor in the maximal ideal that is
-- regular on both `R` and `M`, pass to the quotient by that element, use that projective
-- dimension is unchanged modulo such a nonzerodivisor and that both depths drop by one, and then
-- conclude by induction on `moduleDepth R M`.

/-- Helper for Proposition 10.111.1: a finite natural projective-dimension value forces the module
to be nonzero. -/
private theorem nontrivial_of_projectiveDimension_eq_nat {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Finite R N] {d : ℕ}
    (hpd : projectiveDimension (ModuleCat.of R N) = d) :
    Nontrivial N := by
  -- Proof comment: a zero module has projective dimension `⊥`, so a natural value excludes that
  -- case.
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hzero : Limits.IsZero (ModuleCat.of R N) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)
  have hbot :
      projectiveDimension (ModuleCat.of R N) = ⊥ :=
    (projectiveDimension_eq_bot_iff (ModuleCat.of R N)).2 hzero
  have hcontra : ((d : ℕ∞) : WithBot ℕ∞) = ⊥ := by
    simpa [hpd] using hbot
  have hne : ((d : ℕ∞) : WithBot ℕ∞) ≠ ⊥ := by
    simp
  exact hne hcontra

/-- Helper for Chap10 Proposition 10 111 1: depth zero on the ring produces a nonzero element
annihilated by the maximal ideal. -/
private theorem exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero_for_entry
    (hdepth0 : moduleDepth R R = 0) :
    ∃ x : R, x ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r * x = 0 := by
  -- Proof comment: convert depth zero into a nonzero degree-zero residue-field `Ext` class, then
  -- read it as a nonzero map `k → R` whose image is killed by the maximal ideal.
  have hExtIff : residueFieldExtNonzero R R 0 ↔ moduleDepth R R = 0 :=
    residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero R R
  have hExt : residueFieldExtNonzero R R 0 := by
    exact hExtIff.2 hdepth0
  have hMapIff : residueFieldExtNonzero R R 0 ↔
      ∃ f : ResidueField R →ₗ[R] R, f ≠ 0 :=
    residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap R R
  obtain ⟨f, hf⟩ :=
    hMapIff.1 hExt
  have hvalue : ∃ y : ResidueField R, f y ≠ 0 := by
    by_contra hvalue
    apply hf
    ext y
    by_contra hy
    exact hvalue ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hvalue
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨f (IsLocalRing.residue R a), hy, ?_⟩
  intro r hr
  have hsmul : r • IsLocalRing.residue R a = 0 := by
    exact smul_residueField_eq_zero_of_mem_maximalIdeal R hr (IsLocalRing.residue R a)
  change r • f (IsLocalRing.residue R a) = 0
  rw [← map_smul, hsmul, map_zero]

/-- Helper for Proposition 10.111.1: the maximal ideal of a Noetherian local ring cannot generate
a nonzero finite module, even when the module universe differs from the ring universe. -/
private theorem maximalIdeal_smul_top_ne_top_for_entry {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Nontrivial N] :
    maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ := by
  -- Proof comment: this is the Jacobson-ideal form of Nakayama's lemma for the maximal ideal.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R N)))

/-- Helper for Proposition 10.111.1: linear equivalences preserve the set of regular-sequence
lengths in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Proof comment: transport each regular sequence across the equivalence and then reverse the
  -- argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Proposition 10.111.1: ideal depth is invariant under a linear equivalence of finite
modules. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- Proof comment: the branch `I • M = M` is preserved by the equivalence, and otherwise both
  -- sides compute depth from the same regular-sequence lengths.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Proposition 10.111.1: module depth is invariant under a linear equivalence of
finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Proof comment: specialize the ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (maximalIdeal R) e

/-- Helper for Proposition 10.111.1: a positive-rank standard finite free module has the same
depth as the ring itself. -/
private theorem moduleDepth_piFinSucc_eq_ringDepth [Nontrivial R] (n : ℕ) :
    moduleDepth R (Fin n.succ → R) = moduleDepth R R := by
  induction n with
  | zero =>
      -- Proof comment: `R^1` is linearly equivalent to `R`.
      simpa using moduleDepth_eq_of_linearEquiv (LinearEquiv.funUnique (Fin 1) R R)
  | succ n ih =>
      let T : ShortComplex (ModuleCat R) :=
        ShortComplex.mk
          (ModuleCat.ofHom (LinearMap.inl R R (Fin n.succ → R)))
          (ModuleCat.ofHom (LinearMap.snd R R (Fin n.succ → R)))
          (by
            ext x
            rfl)
      have hT : T.ShortExact :=
        ModuleCat.shortComplex_shortExact T
          Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      have hmid_ge : moduleDepth R (R × (Fin n.succ → R)) ≥ moduleDepth R R := by
        -- Proof comment: the split exact sequence pushes the product depth up to the ring depth.
        have hmiddle := moduleDepth_middle_ge_min hT
        simpa [T, ih, min_self] using hmiddle
      have hleft := moduleDepth_left_ge_min hT
      have hRsmul :
          maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ :=
        maximalIdeal_smul_top_ne_top_for_entry
      have hRfiniteDepth : moduleDepth R R < ⊤ := by
        simpa [moduleDepth] using
          Ideal.depth_lt_top_of_smul_top_ne_top (maximalIdeal R) hRsmul
      obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hRfiniteDepth)
      have hProdsmul :
          maximalIdeal R • (⊤ : Submodule R (R × (Fin n.succ → R))) ≠ ⊤ :=
        maximalIdeal_smul_top_ne_top_for_entry
      have hProdfiniteDepth : moduleDepth R (R × (Fin n.succ → R)) < ⊤ := by
        simpa [moduleDepth] using
          Ideal.depth_lt_top_of_smul_top_ne_top (maximalIdeal R) hProdsmul
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hProdfiniteDepth)
      have hmid_ge_nat : r ≤ m := by
        have hmid_ge' : (r : ℕ∞) ≤ m := by
          simpa [hr, hm] using hmid_ge
        exact ENat.coe_le_coe.mp hmid_ge'
      have hleft_nat : r ≥ min m (r + 1) := by
        have hleft' : min (m : ℕ∞) ((r : ℕ∞) + 1) ≤ r := by
          simpa [T, hr, hm, ih] using hleft
        exact ENat.coe_le_coe.mp hleft'
      have hm_eq : m = r := by
        omega
      have hprod : moduleDepth R (R × (Fin n.succ → R)) = moduleDepth R R := by
        calc
          moduleDepth R (R × (Fin n.succ → R)) = m := by simpa using hm.symm
          _ = r := by simpa [hm_eq]
          _ = moduleDepth R R := by simpa using hr
      calc
        moduleDepth R (Fin n.succ.succ → R)
            = moduleDepth R (R × (Fin n.succ → R)) := by
              symm
              exact moduleDepth_eq_of_linearEquiv
                (Fin.consLinearEquiv R (fun _ : Fin n.succ.succ ↦ R))
        _ = moduleDepth R R := hprod

/-- Helper for Proposition 10.111.1: a nonzero finite free module has the same depth as the ring
itself. -/
private theorem moduleDepth_eq_ringDepth_of_nontrivial_finite_free {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P] [Nontrivial P] :
    moduleDepth R P = moduleDepth R R := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex R P) R P := Module.Free.chooseBasis R P
  let ι := Module.Free.ChooseBasisIndex R P
  letI : Finite ι := Module.Finite.finite_basis b
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hι_nonempty : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      exact b.equivFun.injective (Subsingleton.elim _ _)
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hR_nontrivial : Nontrivial R := by
    by_contra hR
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have hsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      exact b.equivFun.injective (Subsingleton.elim _ _)
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  letI : Nontrivial R := hR_nontrivial
  have hcard_ne_zero : Fintype.card ι ≠ 0 := Nat.ne_of_gt (Fintype.card_pos_iff.mpr hι_nonempty)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard_ne_zero
  let eBasis : (ι → R) ≃ₗ[R] P := b.equivFun.symm
  let eFin : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin ι)
  -- Proof comment: transport the finite free module to standard coordinates and apply the
  -- positive-rank computation above.
  calc
    moduleDepth R P = moduleDepth R (ι → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv eBasis
    _ = moduleDepth R (Fin (Fintype.card ι) → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv eFin
    _ = moduleDepth R R := by
      rw [hn]
      exact moduleDepth_piFinSucc_eq_ringDepth n

/-- Helper for Proposition 10.111.1: a nonzero finite module has finite depth, so the source proof
may induct on an ordinary natural number. -/
private theorem exists_nat_moduleDepth_of_nontrivial_finite {N : Type v} [AddCommGroup N]
    [Module R N] [Module.Finite R N] [Nontrivial N] :
    ∃ n : ℕ, moduleDepth R N = n := by
  -- Proof comment: the maximal ideal acts nontrivially on a nonzero finite module over the local
  -- ring, so the depth cannot be `⊤`.
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry
  have hfiniteDepth : moduleDepth R N < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (maximalIdeal R) hsmul
  rcases ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth) with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Helper for Chap10 Proposition 10 111 1: if mixed-universe finite module depth is `n + 1`,
then a maximal-ideal nonzerodivisor drops the quotient depth to `n`. -/
private theorem exists_mem_maximalIdeal_isSMulRegular_and_depth_drop_of_eq_succ_for_entry
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] {n : ℕ}
    (hdepth : moduleDepth R N = n + 1) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular N x ∧ moduleDepth R (QuotSMulTop x N) = n := by
  letI : Small.{u} N := Module.Finite.small R N
  have hdepthShrink : moduleDepth R (Shrink.{u} N) = n + 1 := by
    let eN : Shrink.{u} N ≃ₗ[R] N := Shrink.linearEquiv R N
    have hshrink : moduleDepth R (Shrink.{u} N) = moduleDepth R N :=
      moduleDepth_eq_of_linearEquiv eN
    simpa [hdepth] using hshrink
  obtain ⟨rs, hreg, hmem, hlen⟩ :=
    exists_regularSequence_of_length_eq_moduleDepth R (Shrink.{u} N) hdepthShrink
  cases rs with
  | nil =>
      cases Nat.succ_ne_zero n (by simpa using hlen.symm)
  | cons x xs =>
      have hx : x ∈ maximalIdeal R := by
        exact hmem (Ideal.subset_span (by simp))
      have hconsIff :
          IsRegular (Shrink.{u} N) (x :: xs) ↔
            IsSMulRegular (Shrink.{u} N) x ∧ IsRegular (QuotSMulTop x (Shrink.{u} N)) xs :=
        isRegular_cons_iff (Shrink.{u} N) x xs
      obtain ⟨hxregShrink, hxsregShrink⟩ := hconsIff.1 hreg
      have eN : Shrink.{u} N ≃ₗ[R] N := Shrink.linearEquiv R N
      have hxreg : IsSMulRegular N x :=
        (eN.isSMulRegular_congr x).1 hxregShrink
      have hxs_len : xs.length = n := by
        simpa using hlen
      let eQuot :
          QuotSMulTop x (Shrink.{u} N) ≃ₗ[R] QuotSMulTop x N :=
        QuotSMulTop.congr x eN
      have hxsreg : RingTheory.Sequence.IsRegular (QuotSMulTop x N) xs :=
        (eQuot.isRegular_congr xs).1 hxsregShrink
      refine ⟨x, hx, hxreg, le_antisymm ?_ ?_⟩
      · -- Proof comment: a too-long regular sequence on the quotient would prepend to a
        -- too-long regular sequence on `N`.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x N)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x N) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
          simpa using
            maximalIdeal_smul_top_ne_top_for_entry
        rw [show moduleDepth R (QuotSMulTop x N) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x N)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x N)
              hquot_smul]
        refine sSup_le ?_
        intro d hd
        rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
        have hx_single : RingTheory.Sequence.IsRegular N [x] := by
          letI : Nontrivial (QuotSMulTop x N) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
          exact IsRegular.cons hxreg (by simpa using (IsRegular.nil R (QuotSMulTop x N)))
        have hsingleton :
            Ideal.ofList [x] • (⊤ : Submodule R N) = x • (⊤ : Submodule R N) := by
          simp [Submodule.ideal_span_singleton_smul]
        have hysreg' :
            RingTheory.Sequence.IsRegular
              (N ⧸ (Ideal.ofList [x] • (⊤ : Submodule R N))) ys := by
          exact ((Submodule.quotEquivOfEq _ _ hsingleton).isRegular_congr ys).2 hysreg
        have hcons_reg : RingTheory.Sequence.IsRegular N ([x] ++ ys) := by
          simpa using RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular
            hx_single hysreg'
        have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal R := by
          refine Ideal.span_le.mpr ?_
          intro r hr
          rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
          · exact hx
          · exact hysmem (Ideal.subset_span hyr)
        have hcons_le :
            (([x] ++ ys).length : ℕ∞) ≤ moduleDepth R N := by
          have hsmul :
              maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ :=
            maximalIdeal_smul_top_ne_top_for_entry
          rw [show moduleDepth R N =
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) N) from
              Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) N hsmul]
          refine le_sSup ?_
          exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
        have hlength_le : ([x] ++ ys).length ≤ n + 1 := by
          simpa [hdepth] using hcons_le
        have hys_le : ys.length ≤ n := by
          simpa using hlength_le
        exact_mod_cast hys_le
      · -- Proof comment: the tail of the chosen regular sequence gives the matching lower
        -- bound on quotient depth.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x N)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x N) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
          simpa using
            maximalIdeal_smul_top_ne_top_for_entry
        rw [show moduleDepth R (QuotSMulTop x N) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x N)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x N)
              hquot_smul]
        have hxs_le :
            ((xs.length : ℕ∞) ≤
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x N))) := by
          refine le_sSup ?_
          refine ⟨xs, hxsreg, ?_, ?_⟩
          · refine Ideal.span_le.mpr ?_
            intro r hr
            exact hmem (Ideal.subset_span (List.mem_cons_of_mem _ hr))
          · rfl
        simpa [hxs_len] using hxs_le

/-- Helper for Chap10 Proposition 10 111 1: if the ring is small in the module universe, a
finite module of categorical projective dimension `0` has ring depth. -/
private theorem moduleDepth_eq_ringDepth_of_projectiveDimension_zero_of_small {N : Type v}
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Small.{v} R]
    (hpd : projectiveDimension (ModuleCat.of R N) = 0) :
    moduleDepth R N = moduleDepth R R := by
  -- Proof comment: convert the numerical projective-dimension value into categorical
  -- projectivity.
  have hpdle : HasProjectiveDimensionLE (ModuleCat.of R N) 0 := by
    rw [← CategoryTheory.projectiveDimension_le_iff]
    rw [hpd]
    simp
  have hproj_cat : Projective (ModuleCat.of R N) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R N)).2 hpdle
  -- Proof comment: under the explicit smallness side condition, mathlib identifies categorical
  -- projectivity with the module-theoretic projectivity needed for local freeness.
  let _ : Module.Projective R N := (IsProjective.iff_projective N).2 hproj_cat
  let _ : Module.Free R N := finite_projective_module_free_of_isLocalRing R
  letI : Nontrivial N := nontrivial_of_projectiveDimension_eq_nat hpd
  -- Proof comment: finite projective modules over a local ring are finite free, and the already
  -- proved finite-free depth computation applies.
  exact moduleDepth_eq_ringDepth_of_nontrivial_finite_free

/-- Helper for Chap10 Proposition 10 111 1: a coordinate of a finitely supported vector lying in
`J • ⊤` already lies in `J`. -/
private theorem coeff_mem_ideal_of_mem_finsupp_ideal_smul_top
    {A : Type u} {J : Ideal R} {x : A →₀ R}
    (hx : x ∈ J • (⊤ : Submodule R (A →₀ R))) (a : A) :
    x a ∈ J := by
  -- Proof comment: coordinate evaluation transports `J • ⊤` on the free module to
  -- `J • ⊤ = J` on the ring itself.
  let lapply : (A →₀ R) →ₗ[R] R := Finsupp.lapply a
  have h_eval :
      lapply x ∈ J • (⊤ : Submodule R R) := by
    exact (Submodule.smul_top_le_comap_smul_top J lapply) hx
  simpa using h_eval

/-- Helper for Chap10 Proposition 10 111 1: a map between finite free modules is the finite sum
of its coordinate rank-one pieces. -/
private theorem linearMapBetweenFiniteFrees_eq_sumRankOne
    {A B : Type u} [Fintype A] [Fintype B]
    (f : (B →₀ R) →ₗ[R] (A →₀ R)) :
    f = ∑ b, ∑ a,
      (let lsingle : A → R →ₗ[R] (A →₀ R) := fun a ↦ Finsupp.lsingle a
       let lapply : B → (B →₀ R) →ₗ[R] R := fun b ↦ Finsupp.lapply b
       (lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) := by
  classical
  let lsingle : A → R →ₗ[R] (A →₀ R) := fun a ↦ Finsupp.lsingle a
  let lapply : B → (B →₀ R) →ₗ[R] R := fun b ↦ Finsupp.lapply b
  apply LinearMap.ext
  intro x
  -- Proof comment: expand `x` in the standard basis of the source free module, then rebuild each
  -- coefficient vector in the target free module from its own standard basis coordinates.
  calc
    f x = f (∑ b, Finsupp.single b (x b)) := by rw [Finsupp.univ_sum_single]
    _ = ∑ b, f (Finsupp.single b (x b)) := by rw [map_sum]
    _ = ∑ b, x b • f (Finsupp.single b (1 : R)) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      calc
        f (Finsupp.single b (x b)) = f (x b • Finsupp.single b (1 : R)) := by
          simp [Finsupp.smul_single]
        _ = x b • f (Finsupp.single b (1 : R)) := by rw [map_smul]
    _ = ∑ b, ∑ a,
          ((lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) x := by
      refine Finset.sum_congr rfl ?_
      intro b _
      calc
        x b • f (Finsupp.single b (1 : R)) =
            x b • ∑ a, Finsupp.single a ((f (Finsupp.single b 1)) a) := by
              rw [Finsupp.univ_sum_single]
        _ = ∑ a, x b • Finsupp.single a ((f (Finsupp.single b 1)) a) := by
              rw [Finset.smul_sum]
        _ = ∑ a,
              ((lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) x := by
              refine Finset.sum_congr rfl ?_
              intro a _
              ext c
              by_cases hca : c = a
              · subst hca
                simp [lsingle, lapply, LinearMap.comp_apply, LinearMap.smulRight_apply,
                  Finsupp.lapply_apply, Finsupp.lsingle_apply, smul_eq_mul]
              · simp [lsingle, lapply, LinearMap.comp_apply, LinearMap.smulRight_apply,
                  Finsupp.lapply_apply, Finsupp.lsingle_apply, smul_eq_mul, hca]
    _ = (∑ b, ∑ a,
          (lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) x := by
          simp [LinearMap.sum_apply]

/-- Helper for Chap10 Proposition 10 111 1: quotient reduction commutes with composition. -/
private theorem quotientMapByIdeal_comp
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (J : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    (g.comp f).quotientMapByIdeal J =
      (g.quotientMapByIdeal J).comp (f.quotientMapByIdeal J) := by
  -- Proof comment: both quotient maps agree on quotient representatives of the source module.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R M)) x
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Chap10 Proposition 10 111 1: exactness is preserved after reduction modulo an
ideal. -/
private theorem quotientMapByIdeal_exact
    {I : Ideal R}
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x := by
      refine Submodule.smul_induction_on hx' ?_ ?_
      · intro r hr z _
        obtain ⟨y, rfl⟩ := hg z
        refine ⟨r • y, ?_, ?_⟩
        · exact Submodule.smul_mem_smul hr (by simp)
        · simp
      · intro y z hy hz
        rcases hy with ⟨y', hy', rfl⟩
        rcases hz with ⟨z', hz', rfl⟩
        refine ⟨y' + z', Submodule.add_mem _ hy' hz', ?_⟩
        simp
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    rw [hn]
    simpa using hyI
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

/-- Helper for Chap10 Proposition 10 111 1: quotient reduction agrees with tensoring by
`R ⧸ I` under the standard quotient-tensor comparison. -/
private theorem quotientMapByIdeal_lTensor_naturality
    {I : Ideal R}
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul P I ∘ₗ f.lTensor (R ⧸ I) := by
  -- Proof comment: check the commuting square on pure tensors coming from quotient scalars.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Chap10 Proposition 10 111 1: surjectivity transfers across a commuting square of
linear equivalences. -/
private theorem surjective_of_ladder_linearEquiv_local
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Surjective f) :
    Function.Surjective g := by
  intro y
  obtain ⟨x, hx⟩ := hf (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  -- Proof comment: move the target point back along `e₂`, solve surjectively for `f`, and then
  -- return through `e₁`.
  calc
    g (e₁ x) = e₂ (f x) := by
      simpa using LinearMap.congr_fun h x
    _ = e₂ (e₂.symm y) := by rw [hx]
    _ = y := by simp

/-- Helper for Chap10 Proposition 10 111 1: injectivity transfers across a commuting square of
linear equivalences. -/
private theorem injective_of_ladder_linearEquiv_local
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Chap10 Proposition 10 111 1: after tensoring with `R ⧸ I`, the reduced free cover
is identified with the basis linear-combination map. -/
private theorem reduced_free_cover_lTensor_comparison
    {I : Ideal R} {A : Type v} [DecidableEq A]
    {M : Type u} [AddCommGroup M] [Module R M]
    (x : A → M) :
    (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ
        (LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm.toLinearMap =
      (TensorProduct.quotTensorEquivQuotSMul M I).symm.toLinearMap ∘ₗ
        (Finsupp.linearCombination (R ⧸ I)
          (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ x)).restrictScalars R := by
  -- Proof comment: check the comparison on the `Finsupp.single` generators of the free module
  -- over `R ⧸ I`.
  apply Finsupp.lhom_ext
  intro a q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  calc
    (Finsupp.linearCombination R x).lTensor (R ⧸ I)
        ((LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm
          (Finsupp.single a (Ideal.Quotient.mk I r)))
      = (Ideal.Quotient.mk I r) ⊗ₜ[R] x a := by
          simp [Finsupp.linearCombination_single]
    _ = (r • (1 : R ⧸ I)) ⊗ₜ[R] x a := by
          congr 1
          change Ideal.Quotient.mk I r = (Ideal.Quotient.mk I r) * 1
          simp
    _ = r • ((1 : R ⧸ I) ⊗ₜ[R] x a) := by
          rw [TensorProduct.smul_tmul']
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Ideal.Quotient.mk I r) •
            Submodule.mkQ (I • (⊤ : Submodule R M)) (x a)) := by
          apply (TensorProduct.quotTensorEquivQuotSMul M I).injective
          simp only [map_smul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
            Submodule.mkQ_apply, LinearEquiv.apply_symm_apply]
          exact Module.Quotient.mk_smul_mk M I r (x a)
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Finsupp.linearCombination (R ⧸ I)
            (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ x)).restrictScalars R
            (Finsupp.single a (Ideal.Quotient.mk I r))) := by
          simp [Finsupp.linearCombination_single]

/-- Helper for Chap10 Proposition 10 111 1: a quotient basis makes the reduced free cover
injective. -/
private theorem free_cover_mod_ideal_injective_of_quotient_basis
    {I : Ideal R} {A : Type v}
    {M : Type u} [AddCommGroup M] [Module R M]
    (x : A → M)
    (hbasis :
      ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))),
        ∀ a, bbar a = Submodule.mkQ (I • (⊤ : Submodule R M)) (x a)) :
    Function.Injective ((Finsupp.linearCombination R x).quotientMapByIdeal I) := by
  classical
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx : Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  let e₁ : (A →₀ (R ⧸ I)) ≃ₗ[R] (R ⧸ I) ⊗[R] (A →₀ R) :=
    LinearEquiv.restrictScalars R
      (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A).symm
  let e₂ : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] (R ⧸ I) ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm
  have hCompare :
      (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ e₁.toLinearMap =
        e₂.toLinearMap ∘ₗ (Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R := by
    -- Proof comment: rewrite the quotient family `Submodule.mkQ _ ∘ x` as the chosen basis.
    simpa [e₁, e₂, hmkQx] using
      (@reduced_free_cover_lTensor_comparison R _ _ _ I A _ M _ _ x)
  have hBasisInj :
      Function.Injective ((Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R) := by
    -- Proof comment: the basis linear-combination map is inverse to the coordinate map.
    intro c d hcd
    have hrepr := congrArg bbar.repr hcd
    simpa using hrepr
  have hTensorInj : Function.Injective ((Finsupp.linearCombination R x).lTensor (R ⧸ I)) :=
    injective_of_ladder_linearEquiv_local hCompare hBasisInj
  -- Proof comment: transfer tensor-side injectivity back through the quotient-tensor comparison.
  exact injective_of_ladder_linearEquiv_local
    (quotientMapByIdeal_lTensor_naturality (Finsupp.linearCombination R x))
    hTensorInj

/-- Helper for Chap10 Proposition 10 111 1: a linear equivalence stays invertible after quotient
reduction modulo an ideal. -/
private theorem quotientMapByIdeal_comp_eq_id_of_linearEquiv
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) :
    ((e.symm.toLinearMap).quotientMapByIdeal J).comp ((e.toLinearMap).quotientMapByIdeal J) =
        LinearMap.id ∧
      ((e.toLinearMap).quotientMapByIdeal J).comp ((e.symm.toLinearMap).quotientMapByIdeal J) =
        LinearMap.id := by
  constructor
  · -- Proof comment: the left inverse identity is checked directly on quotient representatives.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R M)) x
    simp [LinearMap.quotientMapByIdeal]
  · -- Proof comment: the same representative computation gives the right inverse identity.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R N)) x
    simp [LinearMap.quotientMapByIdeal]

/-- Helper for Chap10 Proposition 10 111 1: if a map between finite free modules reduces to zero
modulo `maximalIdeal R`, then it induces the zero postcomposition map on residue-field `Ext`. -/
private theorem residueFieldExtCompZeroOfQuotientMapByIdealZeroBetweenFiniteFrees
    {A B : Type u} [Fintype A] [Fintype B]
    (f : (B →₀ R) →ₗ[R] (A →₀ R))
    (hf : f.quotientMapByIdeal (maximalIdeal R) = 0)
    {i : ℕ} (e : residueFieldExt R (B →₀ R) i) :
    e.comp (mk₀ (ModuleCat.ofHom f)) (add_zero i) = 0 := by
  -- Route correction: the false arbitrary-submodule bridge is replaced by the canonical finite-free
  -- matrix statement needed for the minimal-cover argument.
  classical
  let lsingle : A → R →ₗ[R] (A →₀ R) := fun a ↦ Finsupp.lsingle a
  let lapply : B → (B →₀ R) →ₗ[R] R := fun b ↦ Finsupp.lapply b
  -- Proof comment: normalize `f` into its coordinate rank-one summands so it is enough to kill
  -- one summand at a time.
  have hmk₀sum :
      mk₀ (ModuleCat.ofHom (∑ b, ∑ a,
        (lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a)))) =
        ∑ b, ∑ a,
          mk₀ (ModuleCat.ofHom ((lsingle a).comp
            ((lapply b).smulRight ((f (Finsupp.single b 1)) a)))) := by
    -- Proof comment: `mk₀` is additive on degree-zero morphisms, so the finite matrix expansion
    -- passes unchanged to `Ext⁰`.
    have hcatSum :
        ModuleCat.ofHom (∑ b, ∑ a,
          (lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) =
          ∑ b, ∑ a,
            ModuleCat.ofHom ((lsingle a).comp
              ((lapply b).smulRight ((f (Finsupp.single b 1)) a))) := by
      ext x
      simp
    rw [hcatSum, mk₀_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [mk₀_sum]
  rw [linearMapBetweenFiniteFrees_eq_sumRankOne f, hmk₀sum, comp_sum]
  refine Finset.sum_eq_zero ?_
  intro b _
  rw [comp_sum]
  refine Finset.sum_eq_zero ?_
  intro a _
  let g : (B →₀ R) →ₗ[R] (A →₀ R) :=
    (lsingle a).comp (lapply b)
  have hcoeffQ :
      ((Submodule.Quotient.mk :
          (A →₀ R) → (A →₀ R) ⧸ (maximalIdeal R • (⊤ : Submodule R (A →₀ R))))
        (f (Finsupp.single b (1 : R)))) = 0 := by
    simpa [LinearMap.quotientMapByIdeal] using
      LinearMap.congr_fun hf (Submodule.Quotient.mk (Finsupp.single b (1 : R)))
  have hcoeff :
      ((f (Finsupp.single b 1)) a) ∈ maximalIdeal R := by
    -- Proof comment: the reduced map is zero, so each matrix coefficient of `f` lands in the
    -- maximal ideal.
    have hmem :
        f (Finsupp.single b (1 : R)) ∈ maximalIdeal R • (⊤ : Submodule R (A →₀ R)) := by
      simpa using hcoeffQ
    exact coeff_mem_ideal_of_mem_finsupp_ideal_smul_top hmem a
  have hrank :
      (lsingle a).comp ((lapply b).smulRight ((f (Finsupp.single b 1)) a)) =
        ((f (Finsupp.single b 1)) a) • g := by
    -- Proof comment: each coordinate summand is the fixed rank-one map `g`, scaled by the
    -- corresponding matrix coefficient.
    ext x c
    by_cases hca : c = a
    · subst hca
      simp [g, lsingle, lapply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply,
        smul_eq_mul, mul_comm]
    · simp [g, lsingle, lapply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply,
        smul_eq_mul, hca]
  have hmk₀ :
      mk₀ (ModuleCat.ofHom (((f (Finsupp.single b 1)) a) • g)) =
        ((f (Finsupp.single b 1)) a) • mk₀ (ModuleCat.ofHom g) := by
    simpa using mk₀_smul ((f (Finsupp.single b 1)) a) (ModuleCat.ofHom g)
  rw [hrank, hmk₀, comp_smul]
  -- Proof comment: a maximal-ideal scalar annihilates the residue field, so it annihilates this
  -- `Ext` class after postcomposition with the rank-one map.
  exact smul_ext_eq_zero_of_annihilates_target_or_source
    (Or.inr (smul_residueField_eq_zero_of_mem_maximalIdeal R hcoeff))
    i
    (e.comp (mk₀ (ModuleCat.ofHom g)) (add_zero i))

/-- Helper for Chap10 Proposition 10 111 1: after choosing coordinates on a finite free source, a
quotient-zero map into a standard finite free module still kills postcomposition on residue-field
`Ext`. -/
private theorem residueFieldExtCompZeroOfQuotientMapByIdealZeroBetweenFiniteFreeModules
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P]
    {A : Type u} [Fintype A]
    (f : P →ₗ[R] (A →₀ R))
    (hf : f.quotientMapByIdeal (maximalIdeal R) = 0)
    {i : ℕ} (e : residueFieldExt R P i) :
    e.comp (mk₀ (ModuleCat.ofHom f)) (add_zero i) = 0 := by
  classical
  let bP : Module.Basis (Module.Free.ChooseBasisIndex R P) R P := Module.Free.chooseBasis R P
  let eP : (Module.Free.ChooseBasisIndex R P →₀ R) ≃ₗ[R] P := bP.repr.symm
  let fstd : (Module.Free.ChooseBasisIndex R P →₀ R) →ₗ[R] (A →₀ R) :=
    f.comp eP.toLinearMap
  have hfstd : fstd.quotientMapByIdeal (maximalIdeal R) = 0 := by
    -- Proof comment: quotient reduction commutes with the chosen basis change, so the reduced
    -- coordinate map is still zero.
    calc
      fstd.quotientMapByIdeal (maximalIdeal R) =
          (f.quotientMapByIdeal (maximalIdeal R)).comp
            (eP.toLinearMap.quotientMapByIdeal (maximalIdeal R)) := by
              simp [fstd, quotientMapByIdeal_comp]
      _ = 0 := by
        simp [hf]
  have hcomp :
      (e.comp (mk₀ (ModuleCat.ofHom eP.symm.toLinearMap)) (add_zero i)).comp
          (mk₀ (ModuleCat.ofHom fstd)) (add_zero i) =
        e.comp (mk₀ (ModuleCat.ofHom f)) (add_zero i) := by
    -- Proof comment: after reassociating the two degree-zero maps, the basis change cancels.
    have hmap :
        ModuleCat.ofHom eP.symm.toLinearMap ≫ ModuleCat.ofHom fstd = ModuleCat.ofHom f := by
      ext x
      simp [fstd, eP]
    calc
      (e.comp (mk₀ (ModuleCat.ofHom eP.symm.toLinearMap)) (add_zero i)).comp
          (mk₀ (ModuleCat.ofHom fstd)) (add_zero i) =
          e.comp (mk₀
            (ModuleCat.ofHom eP.symm.toLinearMap ≫ ModuleCat.ofHom fstd)) (add_zero i) := by
              simpa using
                (Ext.mk₀_comp_mk₀_assoc
                  (ModuleCat.ofHom eP.symm.toLinearMap)
                  (ModuleCat.ofHom fstd) e).symm
      _ = e.comp (mk₀ (ModuleCat.ofHom f)) (add_zero i) := by
        rw [hmap]
  -- Proof comment: the standard-coordinate theorem applies to the conjugated map, and then the
  -- previous reassociation identifies the result with the original postcomposition map.
  rw [← hcomp]
  exact residueFieldExtCompZeroOfQuotientMapByIdealZeroBetweenFiniteFrees
    fstd hfstd
    (e.comp (mk₀ (ModuleCat.ofHom eP.symm.toLinearMap)) (add_zero i))

/-- Helper for Chap10 Proposition 10 111 1: in a surjective short exact sequence with projective
middle term, the first syzygy drops projective dimension by exactly one. -/
private theorem projectiveDimension_kernel_of_surjective_freeCover
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {F₀ : Type u} [AddCommGroup F₀] [Module R F₀] [Module.Projective R F₀]
    (π : F₀ →ₗ[R] N) (hπ : Function.Surjective π) {d : ℕ}
    (hpd : projectiveDimension (ModuleCat.of R N) = d + 1) :
    projectiveDimension (ModuleCat.of R (LinearMap.ker π)) = d := by
  let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  have hpdle : HasProjectiveDimensionLE (ModuleCat.of R N) (d + 1) := by
    rw [← CategoryTheory.projectiveDimension_le_iff]
    rw [hpd]
    simp
  have hproj : Projective S.X₂ := by
    change Projective (ModuleCat.of R F₀)
    infer_instance
  have hker_le : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) d := by
    simpa [S, HasProjectiveDimensionLE] using
      (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mp (by
        simpa [HasProjectiveDimensionLE] using hpdle)
  apply le_antisymm
  · -- Proof comment: the short-exact syzygy lemma gives the expected upper bound immediately.
    rw [CategoryTheory.projectiveDimension_le_iff]
    exact hker_le
  · -- Proof comment: a strictly smaller kernel bound would shift back to a strict smaller bound
    -- on `N`, contradicting the assumed equality `pd(N) = d + 1`.
    rw [CategoryTheory.projectiveDimension_ge_iff]
    intro hlt
    have hN_lt : HasProjectiveDimensionLT (ModuleCat.of R N) (d + 1) := by
      simpa [S] using hS.hasProjectiveDimensionLT_X₃ d hlt inferInstance
    have hN_ge : ¬ HasProjectiveDimensionLT (ModuleCat.of R N) (d + 1) := by
      rw [← CategoryTheory.projectiveDimension_ge_iff]
      simpa [hpd]
    exact hN_ge hN_lt

/-- Helper for Chap10 Proposition 10 111 1: in `0 → ker π → F₀ → N → 0` with `F₀` depth-equal to
the ring, the induction formula on `ker π` forces the quotient depth to drop by one. -/
private theorem moduleDepth_kernel_eq_succ_of_surjective_freeCover
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {F₀ : Type u} [AddCommGroup F₀] [Module R F₀] [Module.Finite R F₀]
    (π : F₀ →ₗ[R] N) (hπ : Function.Surjective π)
    (hfreeDepth : moduleDepth R F₀ = moduleDepth R R)
    {d : ℕ} (hkerFormula : moduleDepth R R = d + moduleDepth R (LinearMap.ker π))
    (hdpos : 0 < d) [Nontrivial (LinearMap.ker π)] :
    moduleDepth R (LinearMap.ker π) = moduleDepth R N + 1 := by
  let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  letI : IsNoetherian R F₀ := inferInstance
  letI : IsNoetherian R (LinearMap.ker π) := inferInstance
  letI : Module.Finite R (LinearMap.ker π) := Module.IsNoetherian.finite R (LinearMap.ker π)
  have hNatN : ∃ n : ℕ, moduleDepth R N = n := exists_nat_moduleDepth_of_nontrivial_finite
  have hNatKer : ∃ k : ℕ, moduleDepth R (LinearMap.ker π) = k :=
    exists_nat_moduleDepth_of_nontrivial_finite
  obtain ⟨n, hn⟩ := hNatN
  obtain ⟨k, hk⟩ := hNatKer
  have hfreeDepth' : moduleDepth R F₀ = d + k := by
    calc
      moduleDepth R F₀ = moduleDepth R R := hfreeDepth
      _ = d + moduleDepth R (LinearMap.ker π) := hkerFormula
      _ = d + k := by rw [hk]
  -- Proof comment: the short exact sequence `0 → ker π → F₀ → N → 0` bounds the quotient depth
  -- below by `depth ker - 1`.
  have hright :
      min (moduleDepth R F₀) (moduleDepth R (LinearMap.ker π) - 1) ≤ moduleDepth R N := by
    simpa [S] using
      moduleDepth_right_ge_min hS
  have hright_nat :
      (((d : ℕ∞) + k : ℕ∞) ≤ (n : ℕ∞)) ∨ (((k : ℕ∞) : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞)) := by
    simpa [hfreeDepth', hk, hn] using hright
  have hkerPred_le : k ≤ n + 1 := by
    rcases hright_nat with hdk_le_n | hk_le
    · have hdk_le_n' : d + k ≤ n := by exact_mod_cast hdk_le_n
      omega
    · exact_mod_cast hk_le
  -- Proof comment: the companion inequality bounds the kernel depth below by `depth N + 1`,
  -- because the alternative branch `depth F₀ ≤ depth N + 1` would contradict `0 < d`.
  have hleft :
      min (moduleDepth R F₀) (moduleDepth R N + 1) ≤ moduleDepth R (LinearMap.ker π) := by
    simpa [S] using
      moduleDepth_left_ge_min hS
  have hleft_nat :
      (((d : ℕ∞) + k : ℕ∞) ≤ (k : ℕ∞)) ∨ (((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)) := by
    simpa [hfreeDepth', hk, hn] using hleft
  have hn_lt_k : n < k := by
    rcases hleft_nat with hdk_le_k | hnk
    · have hdk_le_k' : d + k ≤ k := by exact_mod_cast hdk_le_k
      omega
    · have hnk' : n + 1 ≤ k := by exact_mod_cast hnk
      omega
  rw [hk, hn]
  exact_mod_cast (by omega : k = n + 1)

/-- Helper for Chap10 Proposition 10 111 1: for a free cover whose reduction modulo
`maximalIdeal R` is injective on the quotient basis, the reduced kernel inclusion is zero. -/
private theorem quotientCoverSurjectiveOfQuotientBasis
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {A : Type u} (x : A → N)
    (hbasis :
      ∃ bbar : Module.Basis A (R ⧸ maximalIdeal R)
        (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))),
        ∀ a, bbar a = Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R N)) (x a)) :
    Function.Surjective ((Finsupp.linearCombination R x).quotientMapByIdeal (maximalIdeal R)) := by
  classical
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx :
      Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R N)) ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  let e₁ :=
    LinearEquiv.restrictScalars R
      ((TensorProduct.finsuppScalarRight R (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) A).symm)
  let e₂ : (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) ≃ₗ[R]
      TensorProduct R (R ⧸ maximalIdeal R) N :=
    (TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)).symm
  have hCompare :
      (Finsupp.linearCombination R x).lTensor (R ⧸ maximalIdeal R) ∘ₗ e₁.toLinearMap =
        e₂.toLinearMap ∘ₗ (Finsupp.linearCombination (R ⧸ maximalIdeal R) bbar).restrictScalars R := by
    -- Proof comment: after tensoring with `R ⧸ maximalIdeal R`, the reduced free cover becomes
    -- the basis linear-combination map.
    simpa [e₁, e₂, hmkQx] using
      (@reduced_free_cover_lTensor_comparison R _ _ _ (maximalIdeal R) A _ N _ _ x)
  have hBasisSurj :
      Function.Surjective ((Finsupp.linearCombination (R ⧸ maximalIdeal R) bbar).restrictScalars R) := by
    intro y
    refine ⟨bbar.repr y, ?_⟩
    -- Proof comment: the basis coordinates give the inverse to linear combination.
    simpa using bbar.sum_repr y
  have hTensorSurj :
      Function.Surjective ((Finsupp.linearCombination R x).lTensor (R ⧸ maximalIdeal R)) :=
    surjective_of_ladder_linearEquiv_local hCompare hBasisSurj
  -- Proof comment: transport the tensor-side surjectivity back to quotient reduction via the
  -- standard quotient-tensor comparison.
  exact surjective_of_ladder_linearEquiv_local
    (quotientMapByIdeal_lTensor_naturality (Finsupp.linearCombination R x))
    hTensorSurj

/-- Helper for Chap10 Proposition 10 111 1: for a free cover whose reduction modulo
`maximalIdeal R` is injective on the quotient basis, the reduced kernel inclusion is zero. -/
private theorem kernelSubtypeQuotientMapByIdealZeroOfQuotientBasis
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {A : Type u} (x : A → N)
    (hbasis :
      ∃ bbar : Module.Basis A (R ⧸ maximalIdeal R)
        (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))),
        ∀ a, bbar a = Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R N)) (x a))
    (hπ : Function.Surjective (Finsupp.linearCombination R x)) :
    let π : (A →₀ R) →ₗ[R] N := Finsupp.linearCombination R x
    let K : Submodule R (A →₀ R) := LinearMap.ker π
    K.subtype.quotientMapByIdeal (maximalIdeal R) = 0 := by
  let π : (A →₀ R) →ₗ[R] N := Finsupp.linearCombination R x
  let K : Submodule R (A →₀ R) := LinearMap.ker π
  have hExact : Function.Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hQuotExact :
      Function.Exact (K.subtype.quotientMapByIdeal (maximalIdeal R))
        (π.quotientMapByIdeal (maximalIdeal R)) :=
    quotientMapByIdeal_exact K.subtype π hExact hπ
  have hQuotInj : Function.Injective (π.quotientMapByIdeal (maximalIdeal R)) := by
    -- Proof comment: the chosen quotient basis identifies the reduced free cover with the basis
    -- coordinate isomorphism, so it is injective.
    simpa [π] using
      free_cover_mod_ideal_injective_of_quotient_basis x hbasis
  have hRangeBot :
      LinearMap.range (K.subtype.quotientMapByIdeal (maximalIdeal R)) = ⊥ := by
    -- Proof comment: exactness modulo `maximalIdeal R` and injectivity of the reduced cover force
    -- the reduced kernel inclusion to have trivial range.
    rw [← LinearMap.exact_iff.mp hQuotExact, LinearMap.ker_eq_bot]
    exact hQuotInj
  exact LinearMap.range_eq_bot.mp hRangeBot

/-- Helper for Chap10 Proposition 10 111 1: in a short exact sequence, vanishing of the middle
`Ext^n` and of the left `Ext^(n+1)` forces vanishing of the right `Ext^n`. -/
private theorem residueFieldExtVanishRightOfMiddleVanishOfLeftSuccVanish
    {S : ShortComplex (ModuleCat R)} [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    [Module.Finite R S.X₂] [Nontrivial S.X₁] [Nontrivial S.X₂] [Nontrivial S.X₃]
    (hS : S.ShortExact) {n : ℕ}
    (hmiddle : ¬ residueFieldExtNonzero R S.X₂ n)
    (hleft_succ : ¬ residueFieldExtNonzero R S.X₁ (n + 1)) :
    ¬ residueFieldExtNonzero R S.X₃ n := by
  rintro ⟨e, he⟩
  by_cases hδ : e.comp hS.extClass rfl = 0
  · -- Proof comment: exactness at `Ext^n(k, S.X₃)` lifts a zero boundary class to the middle
    -- term, contradicting the assumed vanishing there.
    obtain ⟨e₂, he₂⟩ :=
      covariant_sequence_exact₃ (ModuleCat.of R (ResidueField R)) hS e rfl hδ
    have he₂_ne : e₂ ≠ 0 := by
      intro he₂_zero
      apply he
      calc
        e = e₂.comp (mk₀ S.g) (add_zero n) := he₂.symm
        _ = 0 := by simp [he₂_zero]
    exact hmiddle ⟨e₂, he₂_ne⟩
  · -- Proof comment: if the boundary is already nonzero, it directly violates left-side
    -- vanishing in degree `n + 1`.
    exact hleft_succ ⟨e.comp hS.extClass rfl, hδ⟩

/-- Helper for Chap10 Proposition 10 111 1: if the kernel inclusion of a finite free cover is
zero after reducing modulo `maximalIdeal R`, then the kernel has positive depth. -/
private theorem kernelDepthPositiveOfMinimalCover
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {A : Type u} [Fintype A]
    (π : (A →₀ R) →ₗ[R] N)
    (hKQ0 :
      (LinearMap.ker π).subtype.quotientMapByIdeal (maximalIdeal R) = 0)
    [Module.Finite R (LinearMap.ker π)] [Module.Free R (LinearMap.ker π)]
    [Nontrivial (LinearMap.ker π)] :
    0 < moduleDepth R (LinearMap.ker π) := by
  -- Proof comment: minimality makes postcomposition along `ker π ↪ F₀` zero on `Ext⁰`, while
  -- mono-postcomposition is injective in degree `0`, so `Ext⁰(k, ker π)` must vanish.
  have hExt0Vanish : ¬ residueFieldExtNonzero R (LinearMap.ker π) 0 := by
    let _ : Mono (ModuleCat.ofHom (LinearMap.ker π).subtype) :=
      (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker π).injective_subtype
    rintro ⟨e, he⟩
    have hcompZero :
        e.comp (mk₀ (ModuleCat.ofHom (LinearMap.ker π).subtype)) (add_zero 0) = 0 := by
      simpa using
        residueFieldExtCompZeroOfQuotientMapByIdealZeroBetweenFiniteFreeModules
          ((LinearMap.ker π).subtype) hKQ0 e
    have himageEq :
        ((mk₀ (ModuleCat.ofHom (LinearMap.ker π).subtype)).postcomp
            (ModuleCat.of R (ResidueField R)) (add_zero 0)) e =
          ((mk₀ (ModuleCat.ofHom (LinearMap.ker π).subtype)).postcomp
            (ModuleCat.of R (ResidueField R)) (add_zero 0)) 0 := by
      simpa using hcompZero
    have heZero :
        e = 0 :=
      (postcomp_mk₀_injective_of_mono
        (ModuleCat.of R (ResidueField R))
        (ModuleCat.ofHom (LinearMap.ker π).subtype)) himageEq
    exact he heZero
  obtain ⟨n, hn⟩ :=
    (@exists_nat_moduleDepth_of_nontrivial_finite R _ _ _ (LinearMap.ker π) _ _ _ _)
  rw [hn]
  have hnPos : 0 < n := by
    by_contra hnPos
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnPos
    have hdepthZero : moduleDepth R (LinearMap.ker π) = 0 := by
      simpa [hnZero] using hn
    exact hExt0Vanish <|
      (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero
        R (LinearMap.ker π)).2 hdepthZero
  exact_mod_cast hnPos

/-- Helper for Chap10 Proposition 10 111 1: in the short exact sequence
`0 → ker π → (A →₀ R) → N → 0`, if both `ker π` and `(A →₀ R)` have depth `n + 1`, then the
residue-field `Ext` groups of `N` vanish below degree `n`. -/
private theorem residueFieldExtVanishBelowKernelPredOfMinimalCover
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {A : Type u} [Fintype A]
    (π : (A →₀ R) →ₗ[R] N) (hπ : Function.Surjective π)
    [Module.Finite R (LinearMap.ker π)] [Nontrivial (LinearMap.ker π)]
    {n : ℕ}
    (hKerDepth : moduleDepth R (LinearMap.ker π) = n + 1)
    (hFreeDepth : moduleDepth R (A →₀ R) = n + 1) :
    ∀ i < n, ¬ residueFieldExtNonzero R N i := by
  let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  letI : Nontrivial (A →₀ R) := Function.Surjective.nontrivial hπ
  have hKerProfile :=
    (@residueFieldExt_profile_of_depth_eq
      R _ _ _ (LinearMap.ker π) _ _ _ _ (n + 1) hKerDepth)
  have hFreeProfile :=
    (@residueFieldExt_profile_of_depth_eq
      R _ _ _ (A →₀ R) _ _ _ _ (n + 1) hFreeDepth)
  intro i hi
  -- Proof comment: for `i < n`, both the middle degree `i` and the left degree `i + 1` are
  -- below their first nonvanishing residue-field `Ext` degree `n + 1`.
  exact residueFieldExtVanishRightOfMiddleVanishOfLeftSuccVanish
    hS
    (hFreeProfile.2 i (lt_trans hi (Nat.lt_succ_self n)))
    (hKerProfile.2 (i + 1) (Nat.succ_lt_succ hi))

/-- Helper for Chap10 Proposition 10 111 1: under the minimality condition on `ker π ↪ F₀`, the
first nonzero residue-field `Ext` class of `ker π` shifts one degree down to `N`. -/
private theorem residueFieldExtNonzeroAtKernelPredOfMinimalCover
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {A : Type u} [Fintype A]
    (π : (A →₀ R) →ₗ[R] N) (hπ : Function.Surjective π)
    (hKQ0 :
      (LinearMap.ker π).subtype.quotientMapByIdeal (maximalIdeal R) = 0)
    [Module.Finite R (LinearMap.ker π)] [Module.Free R (LinearMap.ker π)]
    [Nontrivial (LinearMap.ker π)]
    {n : ℕ}
    (hKerDepth : moduleDepth R (LinearMap.ker π) = n + 1) :
    residueFieldExtNonzero R N n := by
  let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  have hKerProfile :=
    (@residueFieldExt_profile_of_depth_eq
      R _ _ _ (LinearMap.ker π) _ _ _ _ (n + 1) hKerDepth)
  obtain ⟨e, he⟩ := hKerProfile.1
  have hcompZero :
      e.comp (mk₀ (ModuleCat.ofHom (LinearMap.ker π).subtype)) (add_zero (n + 1)) = 0 := by
    simpa using
      residueFieldExtCompZeroOfQuotientMapByIdealZeroBetweenFiniteFreeModules
        ((LinearMap.ker π).subtype) hKQ0 e
  obtain ⟨eN, heN⟩ :=
    covariant_sequence_exact₁
      (ModuleCat.of R (ResidueField R)) hS e
      (by simpa [S] using hcompZero) rfl
  refine ⟨eN, ?_⟩
  intro heNZero
  apply he
  calc
    e = eN.comp hS.extClass rfl := heN.symm
    _ = 0 := by simp [heNZero]

/-- Helper for Chap10 Proposition 10 111 1: the induction only needs the genuine `pd = 1`
base case, not the false arbitrary-cover statement from the previous route. -/
private theorem ringDepth_eq_one_add_moduleDepth_of_projectiveDimension_one_same_universe
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hpd : projectiveDimension (ModuleCat.of R N) = 1) :
    moduleDepth R R = 1 + moduleDepth R N := by
  -- Route correction: the base case must use a minimal free cover, because an arbitrary free
  -- cover does not control the boundary map in the long exact `Ext` sequence.
  letI : Nontrivial N := nontrivial_of_projectiveDimension_eq_nat hpd
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : Module.Free (R ⧸ maximalIdeal R)
      (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) :=
    Module.Free.of_divisionRing
      (R ⧸ maximalIdeal R)
      (N ⧸ (maximalIdeal R • (⊤ : Submodule R N)))
  let bbar : Module.Basis
      (Module.Free.ChooseBasisIndex (R ⧸ maximalIdeal R)
        (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))))
      (R ⧸ maximalIdeal R)
      (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) :=
    Module.Free.chooseBasis (R ⧸ maximalIdeal R)
      (N ⧸ (maximalIdeal R • (⊤ : Submodule R N)))
  let A :=
    Module.Free.ChooseBasisIndex (R ⧸ maximalIdeal R)
      (N ⧸ (maximalIdeal R • (⊤ : Submodule R N)))
  letI : Finite A := Module.Finite.finite_basis bbar
  classical
  letI : Fintype A := Fintype.ofFinite A
  choose x hx using fun a : A ↦
    Submodule.mkQ_surjective (maximalIdeal R • (⊤ : Submodule R N)) (bbar a)
  have hbasis :
      ∃ bbar' : Module.Basis A (R ⧸ maximalIdeal R)
        (N ⧸ (maximalIdeal R • (⊤ : Submodule R N))),
        ∀ a, bbar' a = Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R N)) (x a) := by
    refine ⟨bbar, ?_⟩
    intro a
    exact (hx a).symm
  let π : (A →₀ R) →ₗ[R] N := Finsupp.linearCombination R x
  have hπquot :
      Function.Surjective (π.quotientMapByIdeal (maximalIdeal R)) := by
    simpa [π] using quotientCoverSurjectiveOfQuotientBasis x hbasis
  have hπ : Function.Surjective π := by
    -- Proof comment: surjectivity modulo the maximal ideal upgrades to surjectivity by Nakayama.
    refine
      (@surjective_of_quotientMap_surjective_of_le_ring_jacobson
        R _ N _ _ (A →₀ R) _ _ (maximalIdeal R) π _ hπquot ?_)
    simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
      (show maximalIdeal R ≤ maximalIdeal R from le_rfl)
  have hKQ0 :
      (LinearMap.ker π).subtype.quotientMapByIdeal (maximalIdeal R) = 0 := by
    simpa [π] using kernelSubtypeQuotientMapByIdealZeroOfQuotientBasis x hbasis hπ
  letI : IsNoetherian R (LinearMap.ker π) := inferInstance
  letI : Module.Finite R (LinearMap.ker π) := Module.IsNoetherian.finite R (LinearMap.ker π)
  have hKerPd0 :
      projectiveDimension (ModuleCat.of R (LinearMap.ker π)) = 0 :=
    projectiveDimension_kernel_of_surjective_freeCover π hπ hpd
  have hKerPdLe :
      HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 0 := by
    rw [← CategoryTheory.projectiveDimension_le_iff]
    rw [hKerPd0]
    simp
  have hKerProjCat :
      Projective (ModuleCat.of R (LinearMap.ker π)) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
      (ModuleCat.of R (LinearMap.ker π))).2 hKerPdLe
  let _ : Module.Projective R (LinearMap.ker π) :=
    (IsProjective.iff_projective (LinearMap.ker π)).2 hKerProjCat
  let _ : Module.Free R (LinearMap.ker π) := finite_projective_module_free_of_isLocalRing R
  letI : Nontrivial (LinearMap.ker π) := nontrivial_of_projectiveDimension_eq_nat hKerPd0
  letI : Nontrivial (A →₀ R) := Function.Surjective.nontrivial hπ
  have hKerDepth :
      moduleDepth R (LinearMap.ker π) = moduleDepth R R := by
    letI : Small.{u} R := small_self R
    exact moduleDepth_eq_ringDepth_of_projectiveDimension_zero_of_small hKerPd0
  have hFreeDepth :
      moduleDepth R (A →₀ R) = moduleDepth R R := by
    exact moduleDepth_eq_ringDepth_of_nontrivial_finite_free
  have hKerDepthPos :
      0 < moduleDepth R (LinearMap.ker π) :=
    kernelDepthPositiveOfMinimalCover π hKQ0
  obtain ⟨k, hk⟩ :=
    (@exists_nat_moduleDepth_of_nontrivial_finite R _ _ _ (LinearMap.ker π) _ _ _ _)
  have hkPos : 0 < k := by
    rw [hk] at hKerDepthPos
    exact_mod_cast hKerDepthPos
  obtain ⟨n, hkSucc⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkPos)
  have hKerDepthSucc :
      moduleDepth R (LinearMap.ker π) = n + 1 := by
    simpa [hkSucc] using hk
  have hFreeDepthSucc :
      moduleDepth R (A →₀ R) = n + 1 := by
    calc
      moduleDepth R (A →₀ R) = moduleDepth R R := hFreeDepth
      _ = moduleDepth R (LinearMap.ker π) := hKerDepth.symm
      _ = n + 1 := hKerDepthSucc
  have hVanishBelow :
      ∀ i < n, ¬ residueFieldExtNonzero R N i :=
    residueFieldExtVanishBelowKernelPredOfMinimalCover
      π hπ hKerDepthSucc hFreeDepthSucc
  have hNonzeroAt :
      residueFieldExtNonzero R N n :=
    residueFieldExtNonzeroAtKernelPredOfMinimalCover
      π hπ hKQ0 hKerDepthSucc
  have hExistsNonzero : ∃ i : ℕ, residueFieldExtNonzero R N i :=
    @exists_nonzero_residueFieldExt R _ _ _ N _ _ _ _
  have hFirstLe :
      firstNonzeroResidueFieldExtIndex R N ≤ n :=
    Nat.find_min' hExistsNonzero hNonzeroAt
  have hFirstGe :
      n ≤ firstNonzeroResidueFieldExtIndex R N := by
    by_contra hlt
    exact hVanishBelow _ (lt_of_not_ge hlt) <|
      (@firstNonzeroResidueFieldExtIndex_spec R _ _ _ N _ _ _ _ :
        residueFieldExtNonzero R N (firstNonzeroResidueFieldExtIndex R N))
  have hFirstEq :
      firstNonzeroResidueFieldExtIndex R N = n :=
    Nat.le_antisymm hFirstLe hFirstGe
  have hDepthN :
      moduleDepth R N = n := by
    simpa [hFirstEq] using
      (@moduleDepth_eq_firstNonzeroResidueFieldExtIndex R _ _ _ N _ _ _ _ : moduleDepth R N =
        (firstNonzeroResidueFieldExtIndex R N : WithTop ℕ))
  -- Proof comment: once the first nonzero `Ext` degree of `N` is identified as `n`, the kernel
  -- depth equality `depth(ker π) = depth(R)` becomes exactly `depth(R) = 1 + depth(N)`.
  calc
    moduleDepth R R = moduleDepth R (LinearMap.ker π) := hKerDepth.symm
    _ = n + 1 := hKerDepthSucc
    _ = 1 + n := by
      exact_mod_cast (by omega : n + 1 = 1 + n)
    _ = 1 + moduleDepth R N := by rw [hDepthN]

/-- Helper for Proposition 10.111.1: the Auslander--Buchsbaum formula is proved by induction on
projective dimension using a finite free cover. -/
private theorem ringDepth_eq_projectiveDimension_add_moduleDepth_same_universe {N : Type u}
    [AddCommGroup N] [Module R N] [Module.Finite R N] {d : ℕ}
    (hpd : projectiveDimension (ModuleCat.of R N) = d) :
    moduleDepth R R = d + moduleDepth R N := by
  induction d generalizing N with
  | zero =>
      -- Proof comment: the induction starts with the projective-dimension-zero finite free case.
      letI : Small.{u} R := small_self R
      have hfreeDepth :=
        moduleDepth_eq_ringDepth_of_projectiveDimension_zero_of_small hpd
      simpa using hfreeDepth.symm
  | succ d ih =>
      -- Proof comment: choose a finite free cover of `N`, pass to its kernel, and apply the
      -- induction hypothesis to that first syzygy.
      letI : Nontrivial N := nontrivial_of_projectiveDimension_eq_nat hpd
      obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R N
      letI : IsNoetherian R (Fin n → R) := inferInstance
      letI : IsNoetherian R (LinearMap.ker π) := inferInstance
      letI : Module.Finite R (LinearMap.ker π) := Module.IsNoetherian.finite R (LinearMap.ker π)
      have hkerPd :
          projectiveDimension (ModuleCat.of R (LinearMap.ker π)) = d :=
        projectiveDimension_kernel_of_surjective_freeCover π hπ hpd
      letI : Nontrivial (LinearMap.ker π) :=
        nontrivial_of_projectiveDimension_eq_nat hkerPd
      have hkerFormula :
          moduleDepth R R = d + moduleDepth R (LinearMap.ker π) :=
        ih hkerPd
      have hfreeDepth : moduleDepth R (Fin n → R) = moduleDepth R R := by
        letI : Nontrivial (Fin n → R) := Function.Surjective.nontrivial hπ
        exact moduleDepth_eq_ringDepth_of_nontrivial_finite_free
      have hNatN : ∃ m : ℕ, moduleDepth R N = m := exists_nat_moduleDepth_of_nontrivial_finite
      obtain ⟨m, hm⟩ := hNatN
      cases d with
      | zero =>
          -- Proof comment: the `pd = 1` branch is the genuine base case, handled separately by
          -- the minimal-free-cover argument from the source proof.
          simpa using
            ringDepth_eq_one_add_moduleDepth_of_projectiveDimension_one_same_universe
              (by simpa using hpd)
      | succ d' =>
          have hshift :
              moduleDepth R (LinearMap.ker π) = moduleDepth R N + 1 :=
            moduleDepth_kernel_eq_succ_of_surjective_freeCover
              π hπ hfreeDepth hkerFormula
              (Nat.succ_pos d')
          calc
            moduleDepth R R = Nat.succ d' + moduleDepth R (LinearMap.ker π) := hkerFormula
            _ = Nat.succ d' + (m + 1) := by rw [hshift, hm]
            _ = (Nat.succ d' + 1) + m := by
              exact_mod_cast (by omega : Nat.succ d' + (m + 1) = (Nat.succ d' + 1) + m)
            _ = (Nat.succ d' + 1) + moduleDepth R N := by rw [hm]

/-- Helper for Chap10 Proposition 10 111 1: projective-dimension bounds transport across an
`R`-linear equivalence between finite modules even when their universes differ. -/
private theorem hasProjectiveDimensionLE_of_linearEquivMixedUniverse
    {N₁ : Type v} {N₂ : Type w}
    [AddCommGroup N₁] [Module R N₁] [Small.{v} R]
    [AddCommGroup N₂] [Module R N₂] [Small.{w} R]
    (e : N₁ ≃ₗ[R] N₂) {n : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R N₁) n) :
    HasProjectiveDimensionLE (ModuleCat.of R N₂) n := by
  let _ : HasProjectiveDimensionLE (ModuleCat.of R N₁) n := hpd
  -- Proof comment: once `R` is small in both ambient module universes, the canonical `ModuleCat`
  -- transport theorem applies verbatim.
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
    (M := ModuleCat.of R N₁) (N := ModuleCat.of R N₂) e n

/-- Helper for Chap10 Proposition 10 111 1: exact natural projective dimension transports across
an `R`-linear equivalence once `R` is made small in the two ambient module universes. -/
private theorem projectiveDimensionEqOfLinearEquivMixedUniverse
    {N₁ : Type v} {N₂ : Type w}
    [AddCommGroup N₁] [Module R N₁] [Small.{v} R]
    [AddCommGroup N₂] [Module R N₂] [Small.{w} R]
    (e : N₁ ≃ₗ[R] N₂) :
    projectiveDimension (ModuleCat.of R N₁) = projectiveDimension (ModuleCat.of R N₂) := by
  -- Proof comment: the linear equivalence identifies the two `ModuleCat` objects, so their exact
  -- projective dimensions coincide by the canonical owner-level transport theorem.
  exact ModuleCat.projectiveDimension_eq_of_linearEquiv
    (M := ModuleCat.of R N₁) (N := ModuleCat.of R N₂) e

/-- Helper for Chap10 Proposition 10 111 1: exact projective dimension transports from the ring
universe to any raised ambient module universe `max u v`, where the needed smallness of `R` is
automatic. -/
private theorem projectiveDimensionEqOfLinearEquivRaisedUniverse
    {N₁ : Type u} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type (max u v)} [AddCommGroup N₂] [Module R N₂]
    (e : N₁ ≃ₗ[R] N₂) :
    projectiveDimension (ModuleCat.of R N₁) = projectiveDimension (ModuleCat.of R N₂) := by
  let _ : Small.{u} R := small_self R
  let _ : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{max u v} R)) ULift.up_injective
  -- Proof comment: after raising the target module universe to `max u v`, the standard
  -- `ModuleCat` owner theorem applies with explicit smallness instances on both sides.
  exact ModuleCat.projectiveDimension_eq_of_linearEquiv
    (M := ModuleCat.of R N₁) (N := ModuleCat.of R N₂) e

/-- Helper for Chap10 Proposition 10 111 1: a nontrivial free `R`-module in universe `v` forces
`R` to be small in universe `v`. -/
private theorem smallRing_of_nontrivial_free_module
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Free R P] [Nontrivial P] :
    Small.{v} R := by
  classical
  let b := Module.Free.chooseBasis R P
  let i : Module.Free.ChooseBasisIndex R P := Classical.choice inferInstance
  have hinj : Function.Injective (fun r : R ↦ r • b i) := by
    intro r s hrs
    have hrepr : b.repr (r • b i) = b.repr (s • b i) := congrArg b.repr hrs
    have hcoeff : (b.repr (r • b i)) i = (b.repr (s • b i)) i :=
      congrArg (fun x ↦ x i) hrepr
    -- Proof comment: the chosen basis vector records the scalar in its own coordinate.
    simpa using hcoeff
  -- Proof comment: the basis line through any chosen basis vector gives an embedding of `R` into
  -- the free module.
  exact small_of_injective (f := fun r : R ↦ r • b i) hinj

/-- Helper for Proposition 10.111.1: categorical projectivity of `ModuleCat.of R N` implies the
usual module-theoretic projectivity of `N` in any ambient module universe. -/
private theorem module_projective_of_categorical_projective_mixed_universe
    {N : Type (max u v)}
    [AddCommGroup N] [Module R N] (hN : Projective (ModuleCat.of R N)) :
    Module.Projective R N := by
  let _ : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{max u v, u} R)) ULift.up_injective
  -- Proof comment: convert categorical lifting against epis into the module-theoretic lifting
  -- property against surjective linear maps.
  refine Module.Projective.of_lifting_property ?_
  intro A B _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R N) := hN
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Chap10 Proposition 10 111 1: a bounded free resolution lifts along
`ModuleCat.uliftFunctor` to any larger universe `max u v w`. -/
private theorem hasFreeResolutionLengthLE_of_ulift
    {N : Type v} [AddCommGroup N] [Module R N] {d : ℕ}
    (hres : HasFreeResolutionLengthLE R N d) :
    HasFreeResolutionLengthLE R (ULift.{max u v w, v} N) d := by
  rcases hres with ⟨F, π, hπ, hbound⟩
  let U : ModuleCat.{v} R ⥤ ModuleCat.{max u v w} R :=
    ModuleCat.uliftFunctor.{max u v w, v} R
  let FU : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj F
  let eSingle :
      (ChainComplex.single₀ (ModuleCat.{v} R) ⋙
          U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (ModuleCat.of R N) ≅
        (U ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj (ModuleCat.of R N) :=
    (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).app
      (ModuleCat.of R N)
  let πU :
      FU ⟶
        (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
          (ModuleCat.of R (ULift.{max u v w, v} N)) :=
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).map π ≫ eSingle.hom
  refine ⟨FU, πU, ?_, ?_⟩
  · -- Proof comment: `ModuleCat.uliftFunctor` preserves quasi-isomorphisms, and its objectwise
    -- action turns each free term into the canonically equivalent `ULift` free module.
    refine { toQuasiIso := ?_, termwise_free := ?_ }
    · infer_instance
    · intro n
      let _ : Module.Free R (F.X n) := hπ.termwise_free n
      simpa [FU, U] using
        Module.Free.of_equiv
          (ULift.moduleEquiv : ULift.{max u v w, v} (F.X n) ≃ₗ[R] F.X n).symm
  · intro n hn
    -- Proof comment: the length bound is preserved because a zero term stays zero after `ULift`.
    have hsub : Subsingleton (F.X n) :=
      (ModuleCat.isZero_iff_subsingleton).1 (hbound n hn)
    let _ : Subsingleton (F.X n) := hsub
    have hsubU :
        Subsingleton (((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj F).X n) := by
      simpa [FU, U] using
        (inferInstance : Subsingleton (ULift.{max u v w, v} (F.X n)))
    exact
      (ModuleCat.isZero_iff_subsingleton).2 hsubU

/-- Helper for Chap10 Proposition 10 111 1: a module-theoretic projective module is projective in
`ModuleCat`, without any extra smallness assumption on the ring universe. -/
private theorem categoricalProjective_of_module_projective_mixed_universe
    {N : Type (max u v)} [AddCommGroup N] [Module R N] [Module.Projective R N] :
    Projective (ModuleCat.of R N) := by
  -- Proof comment: `ModuleCat` already provides the categorical-projective instance for
  -- module-projective objects in any universe.
  exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R N)

/-- Helper for Chap10 Proposition 10 111 1: if `0 → ker π → F₀ → N → 0` has `F₀` projective and
the kernel has projective dimension at most `n`, then the target has projective dimension at most
`n + 1`. -/
private theorem hasProjectiveDimensionLE_of_kernel_of_surjective_projective
    {N : Type u} [AddCommGroup N] [Module R N]
    {F₀ : Type u} [AddCommGroup F₀] [Module R F₀] [Module.Projective R F₀]
    (π : F₀ →ₗ[R] N) (hπ : Function.Surjective π) {n : ℕ}
    (hker : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1) := by
  let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  have hproj : Projective S.X₂ :=
    categoricalProjective_of_module_projective_mixed_universe
  -- Proof comment: the short exact sequence identifies the `(n + 1)`-bound on `N` with the
  -- `n`-bound on the first syzygy.
  simpa [S, HasProjectiveDimensionLE] using
    (hS.hasProjectiveDimensionLT_X₃_iff n hproj).mpr (by
      simpa [HasProjectiveDimensionLE] using hker)

/-- Helper for Chap10 Proposition 10 111 1: lifting a linear map through `ULift` preserves the
controlled source and target modules in one common universe. -/
private noncomputable abbrev uliftLinearMap
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    (f : N₁ →ₗ[S] N₂) :
    ULift.{max u v w, v} N₁ →ₗ[S] ULift.{max u v w, w} N₂ :=
  (ULift.moduleEquiv : ULift.{max u v w, w} N₂ ≃ₗ[S] N₂).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{max u v w, v} N₁ ≃ₗ[S] N₁).toLinearMap)

/-- Helper for Chap10 Proposition 10 111 1: surjectivity survives after lifting a linear map to a
common `ULift` universe. -/
private theorem uliftLinearMap_surjective
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    {f : N₁ →ₗ[S] N₂} (hf : Function.Surjective f) :
    Function.Surjective (uliftLinearMap (S := S) f) := by
  intro y
  -- Proof comment: lift the target element back to the original module, solve surjectivity there,
  -- and then repackage the chosen preimage in the common `ULift` universe.
  obtain ⟨x, hx⟩ := hf ((ULift.moduleEquiv : ULift.{max u v w, w} N₂ ≃ₗ[S] N₂) y)
  refine ⟨(ULift.moduleEquiv : ULift.{max u v w, v} N₁ ≃ₗ[S] N₁).symm x, ?_⟩
  apply (ULift.moduleEquiv : ULift.{max u v w, w} N₂ ≃ₗ[S] N₂).injective
  simpa [uliftLinearMap] using hx

/-- Helper for Chap10 Proposition 10 111 1: the kernel of a lifted linear map is linearly
equivalent to the lift of the original kernel. -/
private noncomputable def uliftLinearMapKerEquiv
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    (f : N₁ →ₗ[S] N₂) :
    LinearMap.ker (uliftLinearMap (S := S) f) ≃ₗ[S] ULift.{max u v w, v} (LinearMap.ker f) where
  toFun x := ⟨⟨(ULift.moduleEquiv : ULift.{max u v w, v} N₁ ≃ₗ[S] N₁) x.1, by
    -- Proof comment: applying the codomain `ULift` equivalence converts the lifted kernel
    -- equation into the original one.
    simpa [LinearMap.mem_ker, uliftLinearMap] using x.2⟩⟩
  invFun x := ⟨(ULift.moduleEquiv : ULift.{max u v w, v} N₁ ≃ₗ[S] N₁).symm x.1.1, by
    -- Proof comment: lifting an original kernel element gives a kernel element of the lifted map.
    simpa [LinearMap.mem_ker, uliftLinearMap] using x.1.2⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

/-- Helper for Chap10 Proposition 10 111 1: shrinking a linear map conjugates both source and
target into the ring universe. -/
private noncomputable abbrev shrinkLinearMap
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    [Small.{u} N₁] [Small.{u} N₂] (f : N₁ →ₗ[S] N₂) :
    Shrink.{u} N₁ →ₗ[S] Shrink.{u} N₂ :=
  (Shrink.linearEquiv S N₂).symm.toLinearMap.comp
    (f.comp (Shrink.linearEquiv S N₁).toLinearMap)

/-- Helper for Chap10 Proposition 10 111 1: surjectivity survives passage to the shrunken model of
a finite module. -/
private theorem shrinkLinearMap_surjective
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    [Small.{u} N₁] [Small.{u} N₂] {f : N₁ →ₗ[S] N₂} (hf : Function.Surjective f) :
    Function.Surjective (shrinkLinearMap (S := S) f) := by
  intro y
  -- Proof comment: lift the shrunken target element back to the original module, solve there,
  -- and shrink the chosen preimage.
  obtain ⟨x, hx⟩ := hf ((Shrink.linearEquiv S N₂) y)
  refine ⟨(Shrink.linearEquiv S N₁).symm x, ?_⟩
  apply (Shrink.linearEquiv S N₂).injective
  simpa [shrinkLinearMap] using hx

/-- Helper for Chap10 Proposition 10 111 1: the kernel of a shrunken linear map is linearly
equivalent to the original kernel. -/
private noncomputable def shrinkLinearMapKerEquiv
    {S : Type u} [CommRing S]
    {N₁ : Type v} {N₂ : Type w} [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    [Small.{u} N₁] [Small.{u} N₂] (f : N₁ →ₗ[S] N₂) :
    LinearMap.ker (shrinkLinearMap (S := S) f) ≃ₗ[S] LinearMap.ker f where
  toFun x := ⟨(Shrink.linearEquiv S N₁) x.1, by
    -- Proof comment: applying the target shrink equivalence recovers the original kernel
    -- equation.
    simpa [LinearMap.mem_ker, shrinkLinearMap] using x.2⟩
  invFun x := ⟨(Shrink.linearEquiv S N₁).symm x.1, by
    -- Proof comment: shrinking a kernel element keeps it inside the shrunken kernel.
    simpa [LinearMap.mem_ker, shrinkLinearMap] using x.2⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

/-- Helper for Chap10 Proposition 10 111 1: a zero projective-dimension bound is an exact zero
value once the module is known to be nontrivial. -/
private theorem projectiveDimensionEqZero_of_hasProjectiveDimensionLE_zero_of_nontrivial
    {X : Type v} [AddCommGroup X] [Module R X] [Nontrivial X]
    (hpdle : HasProjectiveDimensionLE (ModuleCat.of R X) 0) :
    projectiveDimension (ModuleCat.of R X) = 0 := by
  have hproj : Projective (ModuleCat.of R X) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R X)).2 hpdle
  have hnotzero : ¬ Limits.IsZero (ModuleCat.of R X) := by
    intro hzero
    have hsub : Subsingleton X :=
      (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R X)).1 hzero
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  -- Proof comment: projective objects have projective dimension `0`, and nontriviality excludes
  -- the degenerate `⊥` case.
  exact (CategoryTheory.projectiveDimension_eq_zero_iff (ModuleCat.of R X)).2
    ⟨hproj, hnotzero⟩

/-- Helper for Chap10 Proposition 10 111 1: failure of a successor strict bound survives an
`R`-linear equivalence across universes. -/
private theorem not_hasProjectiveDimensionLT_succ_of_linearEquivMixedUniverse
    {N₁ : Type v} {N₂ : Type w}
    [AddCommGroup N₁] [Module R N₁] [Small.{v} R]
    [AddCommGroup N₂] [Module R N₂] [Small.{w} R]
    (e : N₁ ≃ₗ[R] N₂) {n : ℕ}
    (hnotlt : ¬ HasProjectiveDimensionLT (ModuleCat.of R N₁) (n + 1)) :
    ¬ HasProjectiveDimensionLT (ModuleCat.of R N₂) (n + 1) := by
  intro hlt₂
  have hle₁ : HasProjectiveDimensionLE (ModuleCat.of R N₁) n :=
    hasProjectiveDimensionLE_of_linearEquivMixedUniverse
      (R := R) (N₁ := N₂) (N₂ := N₁) e.symm (by
        simpa [HasProjectiveDimensionLE] using hlt₂)
  -- Proof comment: rewrite the successor strict bound as the predecessor non-strict bound, move
  -- that bound back along `e.symm`, and contradict the original obstruction.
  exact hnotlt (by simpa [HasProjectiveDimensionLE] using hle₁)

/-- Helper for Chap10 Proposition 10 111 1: shrinking a finite module to the ring universe
preserves its exact natural projective-dimension value. -/
private theorem projectiveDimensionEqOfULiftNat
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] {d : ℕ}
    (hpd : projectiveDimension (ModuleCat.of R N) = d) :
    projectiveDimension (ModuleCat.of R (ULift.{max u v, v} N)) = d := by
  -- Route correction: the failed owner-level exact transport through `ULift.moduleEquiv`
  -- TODO: the remaining blocker is an owner-level exact transport of projective dimension between
  -- `N` and `ULift N` without `Small.{v} R`. The verified frontier is the lifted linear-map API
  -- above (`uliftLinearMap`, `uliftLinearMap_surjective`, `uliftLinearMapKerEquiv`), which is
  -- enough to run the syzygy induction once a mixed-universe descent from `ULift` bounds back to
  -- `N` is packaged.
  sorry

/-- Helper for Chap10 Proposition 10 111 1: shrinking a finite module to the ring universe
preserves its exact natural projective-dimension value. -/
private theorem projectiveDimensionEqOfShrinkNat
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Small.{u} N]
    {d : ℕ} (hpd : projectiveDimension (ModuleCat.of R N) = d) :
    projectiveDimension (ModuleCat.of R (Shrink.{u} N)) = d := by
  let eN : Shrink.{u} N ≃ₗ[R] N := Shrink.linearEquiv R N
  let _ : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{max u v, u} R)) ULift.up_injective
  let eShrinkU : Shrink.{u} N ≃ₗ[R] ULift.{max u v, u} (Shrink.{u} N) :=
    (ULift.moduleEquiv : ULift.{max u v, u} (Shrink.{u} N) ≃ₗ[R] Shrink.{u} N).symm
  let eU :
      ULift.{max u v, u} (Shrink.{u} N) ≃ₗ[R] ULift.{max u v, v} N :=
    (ULift.moduleEquiv : ULift.{max u v, u} (Shrink.{u} N) ≃ₗ[R] Shrink.{u} N).trans
      (eN.trans (ULift.moduleEquiv : ULift.{max u v, v} N ≃ₗ[R] N).symm)
  have hpdU :
      projectiveDimension (ModuleCat.of R (ULift.{max u v, v} N)) = d :=
    projectiveDimensionEqOfULiftNat (R := R) (N := N) (d := d) hpd
  -- Route correction: compare `Shrink N` and `N` by passing both through a common `ULift`
  -- universe where the ring is automatically small, instead of reconstructing `Small.{v} R`.
  calc
    projectiveDimension (ModuleCat.of R (Shrink.{u} N)) =
        projectiveDimension (ModuleCat.of R (ULift.{max u v, u} (Shrink.{u} N))) := by
          -- Proof comment: first raise the shrunken module to the common ambient universe.
          exact projectiveDimensionEqOfLinearEquivRaisedUniverse
            (R := R) (N₁ := Shrink.{u} N)
            (N₂ := ULift.{max u v, u} (Shrink.{u} N)) eShrinkU
    _ = projectiveDimension (ModuleCat.of R (ULift.{max u v, v} N)) := by
          -- Proof comment: inside the raised universe, the canonical shrink equivalence now
          -- transports projective dimension directly.
          exact projectiveDimensionEqOfLinearEquivMixedUniverse
            (R := R)
            (N₁ := ULift.{max u v, u} (Shrink.{u} N))
            (N₂ := ULift.{max u v, v} N) eU
    _ = d := hpdU

/-- Helper for Proposition 10.111.1: the source-faithful proof is an induction on the natural
depth of the module, with the projective-dimension-zero branch already separated out. -/
private theorem ringDepth_eq_projectiveDimension_add_moduleDepth_of_natDepth
    {N : Type v}
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {d n : ℕ} (hpd : projectiveDimension (ModuleCat.of R N) = d) (hdepth : moduleDepth R N = n) :
    moduleDepth R R = d + moduleDepth R N := by
  letI : Small.{u} R := small_self R
  letI : Small.{u} N := Module.Finite.small R N
  let _ := hdepth
  let eN : Shrink.{u} N ≃ₗ[R] N := Shrink.linearEquiv R N
  have hpdShrink :
      projectiveDimension (ModuleCat.of R (Shrink.{u} N)) = d :=
    projectiveDimensionEqOfShrinkNat hpd
  have hdepthShrink :
      moduleDepth R (Shrink.{u} N) = moduleDepth R N :=
    moduleDepth_eq_of_linearEquiv eN
  -- Proof comment: move to the ring universe, apply the same-universe theorem there, and then
  -- rewrite the depth back across the canonical shrink equivalence.
  calc
    moduleDepth R R = d + moduleDepth R (Shrink.{u} N) :=
      ringDepth_eq_projectiveDimension_add_moduleDepth_same_universe hpdShrink
    _ = d + moduleDepth R N := by rw [hdepthShrink]

/-- Chap10 Proposition 10 111 1: for a nonzero finite module `M` over a Noetherian local ring `R`,
if the projective dimension of `M` is the natural number `d`, then the depth of `R` is `d` plus
the depth of `M` (the Auslander--Buchsbaum formula). -/
@[stacks 090V]
theorem ringDepth_eq_projectiveDimension_add_moduleDepth
    {d : ℕ} (hpd : projectiveDimension (ModuleCat.of R M) = d) :
    moduleDepth R R = d + moduleDepth R M := by
  letI : Nontrivial M := nontrivial_of_projectiveDimension_eq_nat hpd
  have hNatM : ∃ n : ℕ, moduleDepth R M = n := exists_nat_moduleDepth_of_nontrivial_finite
  obtain ⟨n, hdepth⟩ := hNatM
  -- Proof comment: the source proof is organized as an induction on the natural depth value.
  exact ringDepth_eq_projectiveDimension_add_moduleDepth_of_natDepth hpd hdepth

end
