import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_62_3
import StacksProject_2024.Chap10.Lemma_10_68_7
import StacksProject_2024.Chap10.Lemma_10_72_3
import StacksProject_2024.Chap10.Lemma_10_72_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Domain-style sampling:
* primary domain: regular sequences, depth/support dimension, and Cohen-Macaulay quotients over
  Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.depth_le_supportDim`,
  `IsRegular.exists_append_eq_moduleDepth`,
  `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular`;
* best owner abstraction: the source-facing owner in this file is the predicate
  `IsGoodWithRespectTo M g fs`, built from the canonical quotient/support-dimension API
  `QuotSMulTop` and `supportDim`; the primitive ambient owner data are `Module.Finite R M` and
  `IsRegular M fs`, while `CohenMacaulay R M` is derived internally from the maximal-length
  regular sequence hypothesis `supportDim R M = fs.length`;

Source/core/bridge triage:
* source-facing: the predicate `IsGoodWithRespectTo M g fs` formalizes the source notion that
  `g ∈ maximalIdeal R` is good with respect to the maximal regular sequence `fs`;
* core/canonical: `Module.Finite R M`, `moduleDepth R M`, `CohenMacaulay R M`,
  `RingTheory.Sequence.IsRegular M fs`, `QuotSMulTop g`, and `supportDim R`;
* bridge/view: the source notion is expressed through the canonical support-dimension equalities
  for the prefix quotients, and the Cohen-Macaulay owner condition is recovered from
  `depth_le_supportDim` and `IsRegular.exists_append_eq_moduleDepth` rather than stored as
  primitive input data.
-/

variable [Module.Finite R M] {fs : List R} {g : R}

/-- `g` is good with respect to the finite module `M` and the sequence `fs` when
`g ∈ maximalIdeal R` and each prefix quotient
`M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule R M))` has support dimension lowered by exactly
`1` after quotienting by `g`. This is the quotient-module form of the source condition
`dim (Supp(M/(f₁, …, fᵢ)M) ∩ V(g)) = d - i - 1`. -/
def IsGoodWithRespectTo (M : Type v) [AddCommGroup M] [Module R M] (g : R) (fs : List R) : Prop :=
  g ∈ maximalIdeal R ∧
    ∀ i : Fin fs.length,
      supportDim R
          (QuotSMulTop g
            (M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule R M)))) =
        ((fs.length - i - 1 : ℕ) : WithBot ℕ∞)

/-- Helper for Lemma 10.103.2: a regular sequence whose length already equals the support
dimension forces the ambient module to be Cohen--Macaulay. -/
private theorem cohenMacaulay_of_supportDim_eq_length_of_isRegular
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {rs : List R} (hNdim : supportDim R N = rs.length) (hreg : IsRegular N rs) :
    CohenMacaulay R N := by
  -- Extend the given regular sequence to one of depth length and show the extension is empty.
  obtain ⟨rs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  letI : Nontrivial N := hreg.nontrivial
  letI :
      Nontrivial (N ⧸ (Ideal.ofList (rs ++ rs') • (⊤ : Submodule R N))) :=
    RingTheory.Sequence.IsRegular.quot_ofList_smul_nontrivial hreg' ⊤
  have hquot_nonbot :
      supportDim R (N ⧸ (Ideal.ofList (rs ++ rs') • (⊤ : Submodule R N))) ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial R _
  have hlen_le :
      (((rs ++ rs').length : ℕ∞) : WithBot ℕ∞) ≤ supportDim R N := by
    rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular (M := N) (rs := rs ++ rs') hreg']
    simpa [add_comm] using WithBot.le_add_self hquot_nonbot
      ((((rs ++ rs').length : ℕ∞) : WithBot ℕ∞))
  have hrs' : rs' = [] := by
    cases rs' with
    | nil =>
        rfl
    | cons r rs'' =>
        have hbad : False := by
          have :
              (((rs.length + (r :: rs'').length : ℕ∞) : WithBot ℕ∞)) ≤ rs.length := by
            simpa [hNdim, List.length_append] using hlen_le
          have hnot :
              ¬ (((rs.length + (r :: rs'').length : ℕ∞) : WithBot ℕ∞)) ≤ rs.length := by
            have hlt :
                ((rs.length : ℕ∞) : WithBot ℕ∞) <
                  (((rs.length + (r :: rs'').length : ℕ∞) : WithBot ℕ∞)) := by
              exact_mod_cast Nat.lt_add_of_pos_right (Nat.succ_pos _)
            exact not_le_of_gt hlt
          exact hnot this
        exact False.elim hbad
  -- With no extra tail, the support-dimension equality is exactly the Cohen--Macaulay identity.
  refine Module.CohenMacaulay.mk ?_
  rw [hdepth, hrs']
  simpa using hNdim

/-- Helper for Lemma 10.103.2: the kernel of multiplication by `g` is supported inside the support
of the quotient `M / gM`. -/
private theorem support_ker_lsmul_subset_support_quotSMulTop (g : R) :
    Module.support R (LinearMap.ker (LinearMap.lsmul R M g)) ⊆
      Module.support R (QuotSMulTop g M) := by
  let K : Submodule R M := LinearMap.ker (LinearMap.lsmul R M g)
  intro p hp
  -- The kernel sits inside `M`, and `g` annihilates it by definition.
  have hpM : p ∈ Module.support R M := by
    exact Module.support_subset_of_injective K.subtype K.subtype_injective hp
  have hg_ann : g ∈ K.annihilator := by
    rw [Submodule.mem_annihilator]
    intro n hn
    simpa [K, LinearMap.mem_ker, LinearMap.lsmul_apply] using hn
  have hpK : p ∈ PrimeSpectrum.zeroLocus (K.annihilator : Set R) := by
    simpa [K, Module.support_eq_zeroLocus] using hp
  have hgp : g ∈ p.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus p (K.annihilator : Set R)).1 hpK hg_ann
  have hpzero : p ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
    exact (PrimeSpectrum.mem_zeroLocus p ({g} : Set R)).2
      (Set.singleton_subset_iff.mpr hgp)
  simpa [Module.support_quotSMulTop] using And.intro hpM hpzero

/-- Helper for Lemma 10.103.2: the two-generator ideals `(g, f)` and `(f, g)` act identically on
`M`. -/
private theorem ofList_pair_smul_top_eq_swap (f g : R) :
    Ideal.ofList (g :: [f]) • (⊤ : Submodule R M) =
      Ideal.ofList (f :: [g]) • (⊤ : Submodule R M) := by
  -- Reordering the two generators does not change the ideal smul on the ambient module.
  simp [Ideal.ofList_cons, sup_comm]

/-- Helper for Lemma 10.103.2: the one-generator list quotient agrees with the canonical quotient
by `fM`. -/
private theorem ofList_singleton_smul_top_eq (f : R) :
    Ideal.ofList [f] • (⊤ : Submodule R M) = f • (⊤ : Submodule R M) := by
  -- The singleton-list ideal is just the principal ideal generated by `f`.
  simp [Submodule.ideal_span_singleton_smul]

/-- Helper for Lemma 10.103.2: the quotient by `Ideal.ofList [f]` identifies with `QuotSMulTop f
M`. -/
private noncomputable def quotOfListSingletonEquivQuotSMulTop (f : R) :
    (M ⧸ (Ideal.ofList [f] • (⊤ : Submodule R M))) ≃ₗ[R] QuotSMulTop f M :=
  Submodule.quotEquivOfEq _ _ (ofList_singleton_smul_top_eq (R := R) f)

/-- Helper for Lemma 10.103.2: quotienting first by `f` and then by `g` is canonically
equivalent to quotienting first by `g` and then by `f`. -/
private noncomputable def quotSMulTop_swapEquiv (f g : R) :
    QuotSMulTop g (QuotSMulTop f M) ≃ₗ[R] QuotSMulTop f (QuotSMulTop g M) :=
  QuotSMulTop.congr g (quotOfListSingletonEquivQuotSMulTop (M := M) f).symm ≪≫ₗ
    (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter (M := M) g [f]).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (ofList_pair_smul_top_eq_swap (M := M) f g) ≪≫ₗ
        Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter (M := M) f [g] ≪≫ₗ
          QuotSMulTop.congr f (quotOfListSingletonEquivQuotSMulTop (M := M) g)

/-- Helper for Lemma 10.103.2: goodness descends from `(M, f :: rs)` to the quotient by the head
regular element `f`. -/
private theorem isGoodWithRespectTo_quotSMulTop_head {f : R} {rs : List R}
    (hgood : IsGoodWithRespectTo M g (f :: rs)) :
    IsGoodWithRespectTo (QuotSMulTop f M) g rs := by
  rcases hgood with ⟨hg_mem, hgood'⟩
  refine ⟨hg_mem, ?_⟩
  intro i
  have hsucc :
      supportDim R
          (QuotSMulTop g
            (M ⧸ (Ideal.ofList ((f :: rs).take (i.1 + 1)) • (⊤ : Submodule R M)))) =
        (((f :: rs).length - (i.1 + 1) - 1 : ℕ) : WithBot ℕ∞) := by
    -- The `i.succ` goodness clause is exactly the tail statement after rewriting the prefix.
    simpa using hgood' ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩
  calc
    supportDim R
        (QuotSMulTop g
          ((QuotSMulTop f M) ⧸
            (Ideal.ofList (rs.take i.1) • (⊤ : Submodule R (QuotSMulTop f M))))) =
      supportDim R
        (QuotSMulTop g
          (M ⧸ (Ideal.ofList (f :: rs.take i.1) • (⊤ : Submodule R M)))) := by
            -- Transport the prefix quotient through the canonical inner quotient equivalence.
            symm
            exact Module.supportDim_eq_of_equiv <|
              QuotSMulTop.congr g
                (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M f (rs.take i.1))
    _ = (((f :: rs).length - (i.1 + 1) - 1 : ℕ) : WithBot ℕ∞) := by
      simpa [List.take] using hsucc
    _ = ((rs.length - i.1 - 1 : ℕ) : WithBot ℕ∞) := by
      simp

/-- Helper for Lemma 10.103.2: the `i = 0` goodness clause identifies the support dimension of
`M / gM`. -/
private theorem supportDim_quotSMulTop_eq_pred_of_isGoodWithRespectTo
    (hpos : 0 < fs.length) (hgood : IsGoodWithRespectTo M g fs) :
    supportDim R (QuotSMulTop g M) = ((fs.length - 1 : ℕ) : WithBot ℕ∞) := by
  rcases hgood with ⟨_, hgood'⟩
  have hzero :
      supportDim R
          (QuotSMulTop g
            (M ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)))) =
        ((fs.length - 1 : ℕ) : WithBot ℕ∞) := by
    simpa using hgood' ⟨0, hpos⟩
  rw [Ideal.ofList_nil, Submodule.bot_smul,
    Module.supportDim_eq_of_equiv
      (QuotSMulTop.congr g
        (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl))] at hzero
  simpa using hzero

/-- Helper for Lemma 10.103.2: if `M / gM` has zero-dimensional support, then the kernel of
multiplication by `g` has finite length. -/
private theorem isFiniteLength_ker_lsmul_of_supportDim_quotSMulTop_eq_zero
    (hquot : supportDim R (QuotSMulTop g M) = 0) :
    IsFiniteLength R (LinearMap.ker (LinearMap.lsmul R M g)) := by
  let K : Submodule R M := LinearMap.ker (LinearMap.lsmul R M g)
  by_cases hK : Subsingleton K
  · -- A subsingleton kernel already has finite length by definition.
    letI : Subsingleton K := hK
    exact IsFiniteLength.of_subsingleton
  · letI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
    have hsupp_quot :
        Module.support R (QuotSMulTop g M) = ({closedPoint R} : Set (PrimeSpectrum R)) := by
      -- Zero-dimensional support over a local ring is exactly the singleton closed point.
      simpa [PrimeSpectrum.zeroLocus_eq_singleton] using
        support_of_supportDim_eq_zero (R := R) (N := QuotSMulTop g M) hquot
    have hsupp_K :
        Module.support R K = ({closedPoint R} : Set (PrimeSpectrum R)) := by
      apply Set.Subset.antisymm
      · intro p hp
        have hp' : p ∈ Module.support R (QuotSMulTop g M) :=
          support_ker_lsmul_subset_support_quotSMulTop (R := R) (M := M) g hp
        simpa [hsupp_quot] using hp'
      · exact Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support R K)
    -- Finite support at the closed point is the finite-length criterion from Lemma 10.62.3.
    exact (support_eq_singleton_closedPoint_iff_isFiniteLength (R := R) (M := K)).mp hsupp_K

/-- Helper for Lemma 10.103.2: in a local ring, a singleton ideal generated by an element of the
maximal ideal lies in the Jacobson radical. -/
private theorem span_singleton_le_ringJacobson_of_mem_maximalIdeal {f : R}
    (hf : f ∈ maximalIdeal R) :
    Ideal.span ({f} : Set R) ≤ Ring.jacobson R := by
  -- In a local ring, the Jacobson radical is the maximal ideal.
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
  exact (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).2 hf

/-- Helper for Lemma 10.103.2: in the singleton case, the source finite-length plus Nakayama
argument forces the kernel of multiplication by `g` to vanish. -/
private theorem ker_lsmul_eq_bot_of_good_singleton {f : R}
    (hreg : IsRegular M [f]) (hgood : IsGoodWithRespectTo M g [f]) :
    LinearMap.ker (LinearMap.lsmul R M g) = ⊥ := by
  let K : Submodule R M := LinearMap.ker (LinearMap.lsmul R M g)
  have hquot : supportDim R (QuotSMulTop g M) = 0 := by
    -- The `i = 0` goodness clause says exactly that `M / gM` has zero-dimensional support.
    simpa using
      supportDim_quotSMulTop_eq_pred_of_isGoodWithRespectTo
        (M := M) (fs := [f]) (g := g) (by simp) hgood
  have hK_finiteLength : IsFiniteLength R K := by
    -- The kernel support sits inside the zero-dimensional quotient support.
    simpa [K] using
      isFiniteLength_ker_lsmul_of_supportDim_quotSMulTop_eq_zero (M := M) (g := g) hquot
  letI : IsNoetherian R K := (isFiniteLength_iff_isNoetherian_isArtinian.mp hK_finiteLength).1
  letI : IsArtinian R K := (isFiniteLength_iff_isNoetherian_isArtinian.mp hK_finiteLength).2
  have hf_reg : IsSMulRegular M f := by
    -- Regularity of `[f]` starts with injectivity of multiplication by `f`.
    simpa using ((isRegular_cons_iff (M := M) f []).1 hreg).1
  have hf_mem : f ∈ maximalIdeal R := by
    -- Every regular sequence over a local ring is contained in the maximal ideal.
    have hle : Ideal.ofList [f] ≤ maximalIdeal R := IsRegular.ofList_le_maximalIdeal hreg
    exact hle <| by
      simpa [Ideal.ofList_cons] using (Ideal.mem_span_singleton_self f : f ∈ Ideal.span ({f} : Set R))
  have hphi_injective : Function.Injective (LinearMap.lsmul R K f) := by
    -- Injectivity on the ambient module restricts to the kernel submodule.
    intro x y hxy
    apply Subtype.ext
    exact hf_reg (congrArg Subtype.val hxy)
  have hphi_surjective : Function.Surjective (LinearMap.lsmul R K f) :=
    IsArtinian.surjective_of_injective_endomorphism (LinearMap.lsmul R K f) hphi_injective
  have hK_smul_top : Ideal.span ({f} : Set R) • (⊤ : Submodule R K) = ⊤ := by
    -- Surjectivity says every kernel element is an `f`-multiple, so `(f)K = K`.
    refine top_unique ?_
    intro k hk
    rcases hphi_surjective k with ⟨x, rfl⟩
    simpa [Submodule.ideal_span_singleton_smul] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
        (show x ∈ (⊤ : Submodule R K) by simp))
  have hK_subsingleton : Subsingleton K :=
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
      (I := Ideal.span ({f} : Set R)) hK_smul_top
      (span_singleton_le_ringJacobson_of_mem_maximalIdeal (R := R) hf_mem)
  -- Nakayama kills the finite-length kernel.
  exact Submodule.subsingleton_iff_eq_bot.mp hK_subsingleton

/-- Helper for Lemma 10.103.2: quotienting by a head regular element drops the support dimension
from the full length of `f :: rs` to the length of the tail `rs`. -/
private theorem supportDim_quotSMulTop_eq_length_tail_of_cons {f : R} {rs : List R}
    (hf_reg : IsSMulRegular M f) (hf_mem : f ∈ maximalIdeal R)
    (hMdim : supportDim R M = (f :: rs).length) :
    supportDim R (QuotSMulTop f M) = ((rs.length : ℕ∞) : WithBot ℕ∞) := by
  have hsucc := supportDim_quotSMulTop_succ_eq_supportDim (M := M) hf_reg hf_mem
  rw [hMdim] at hsucc
  have hsucc' :
      supportDim R (QuotSMulTop f M) + 1 =
        (((rs.length : ℕ∞) : WithBot ℕ∞) + 1) := by
    -- Rewrite the source dimension equality into the canonical `a + 1 = b + 1` form.
    simpa using hsucc
  simpa using hsucc'

/-- Helper for Lemma 10.103.2: the source-faithful induction produces both the regularity of `g`
on `M` and the regularity of the shortened sequence on `M / gM`. -/
private theorem isSMulRegular_and_isRegular_take_pred_of_isGoodWithRespectTo
    (hMdim : supportDim R M = fs.length)
    (hpos : 0 < fs.length)
    (hfs : IsRegular M fs)
    (hgood : IsGoodWithRespectTo M g fs) :
    IsSMulRegular M g ∧ IsRegular (QuotSMulTop g M) (fs.take (fs.length - 1)) := by
  revert hMdim hpos hfs hgood
  induction fs generalizing M with
  | nil =>
      intro hMdim hpos hfs hgood
      cases hpos
  | cons f rs ih =>
      intro hMdim hpos hfs hgood
      cases rs with
      | nil =>
          have hreg_single : IsRegular M [f] := hfs
          have hker_bot :
              LinearMap.ker (LinearMap.lsmul R M g) = ⊥ :=
            ker_lsmul_eq_bot_of_good_singleton (M := M) (g := g) hreg_single hgood
          have hg_reg : IsSMulRegular M g :=
            (isSMulRegular_iff_ker_lsmul_eq_bot (R := R) (M := M) g).2 hker_bot
          have hquot_dim : supportDim R (QuotSMulTop g M) = 0 := by
            -- The singleton goodness clause gives the zero-dimensional quotient case from the source.
            simpa using
              supportDim_quotSMulTop_eq_pred_of_isGoodWithRespectTo
                (M := M) (fs := [f]) (g := g) (by simp) hgood
          letI : Nontrivial (QuotSMulTop g M) :=
            (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop g M)).mp <| by
              simpa [hquot_dim]
          refine ⟨hg_reg, ?_⟩
          -- A zero-dimensional nontrivial quotient carries the empty regular sequence.
          simpa using (IsRegular.nil R (QuotSMulTop g M))
      | cons r rt =>
          rcases (isRegular_cons_iff (M := M) f (r :: rt)).1 hfs with ⟨hf_reg, htail_reg⟩
          have hf_mem : f ∈ maximalIdeal R := by
            -- The head of a regular sequence over a local ring lies in the maximal ideal.
            have hle : Ideal.ofList (f :: r :: rt) ≤ maximalIdeal R :=
              IsRegular.ofList_le_maximalIdeal hfs
            have hf_ofList : f ∈ Ideal.ofList (f :: r :: rt) := by
              rw [Ideal.ofList_cons, Ideal.ofList_cons]
              exact
                (show
                    Ideal.span ({f} : Set R) ≤
                      Ideal.span ({f} : Set R) ⊔
                        (Ideal.span ({r} : Set R) ⊔ Ideal.ofList rt) from
                    le_sup_left)
                  (Ideal.mem_span_singleton_self f)
            exact hle hf_ofList
          have htail_dim :
              supportDim R (QuotSMulTop f M) = (((r :: rt).length : ℕ∞) : WithBot ℕ∞) :=
            supportDim_quotSMulTop_eq_length_tail_of_cons
              (M := M) hf_reg hf_mem hMdim
          have hgood_tail :
              IsGoodWithRespectTo (QuotSMulTop f M) g (r :: rt) :=
            isGoodWithRespectTo_quotSMulTop_head
              (M := M) (g := g) (f := f) (rs := r :: rt) hgood
          rcases
              ih (M := QuotSMulTop f M)
                htail_dim (by simp) htail_reg hgood_tail with
            ⟨hg_on_quot, htail_quot⟩
          have htail_swap :
              IsRegular (QuotSMulTop f (QuotSMulTop g M))
                ((r :: rt).take ((r :: rt).length - 1)) := by
            -- Transport the inductive tail regularity across the canonical quotient swap.
            exact ((quotSMulTop_swapEquiv (M := M) f g).isRegular_congr _).1 htail_quot
          have hreg_f_single : IsRegular M [f] := by
            letI : Nontrivial (QuotSMulTop f M) := htail_reg.nontrivial
            -- The head regular element gives a singleton regular sequence on `M`.
            exact IsRegular.cons hf_reg (by simpa using (IsRegular.nil R (QuotSMulTop f M)))
          have hreg_g_single : IsRegular (QuotSMulTop f M) [g] := by
            letI : Nontrivial (QuotSMulTop g (QuotSMulTop f M)) := htail_quot.nontrivial
            -- Induction says `g` is regular on `M / fM`, so `[g]` is regular there.
            exact IsRegular.cons hg_on_quot
              (by simpa using (IsRegular.nil R (QuotSMulTop g (QuotSMulTop f M))))
          have hreg_g_single_ofList :
              IsRegular (M ⧸ (Ideal.ofList [f] • (⊤ : Submodule R M))) [g] := by
            -- Rewrite the quotient by `[f]` to the canonical quotient `M / fM`.
            exact ((quotOfListSingletonEquivQuotSMulTop (M := M) f).isRegular_congr [g]).2
              hreg_g_single
          have hpair_fg : IsRegular M [f, g] := by
            -- Rebuild the ordered pair `(f, g)` exactly as in the source proof.
            simpa using
              RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular
                (M := M) (fs := [f]) (gs := [g]) hreg_f_single hreg_g_single_ofList
          have hpair_gf : IsRegular M [g, f] := by
            -- Lemma 10.68.4 permutes the regular pair to the source order `(g, f)`.
            exact IsLocalRing.isRegular_of_perm (M := M) hpair_fg (List.Perm.swap g f [])
          rcases (isRegular_cons_iff (M := M) g [f]).1 hpair_gf with ⟨hg_reg, hquotg_single⟩
          have hf_on_quotg : IsSMulRegular (QuotSMulTop g M) f := by
            -- Peeling off the head of `[f]` gives regularity of `f` on `M / gM`.
            simpa using ((isRegular_cons_iff (M := QuotSMulTop g M) f []).1 hquotg_single).1
          refine ⟨hg_reg, ?_⟩
          have hfinal :
              IsRegular (QuotSMulTop g M)
                (f :: (r :: rt).take ((r :: rt).length - 1)) := by
            -- Append the transported tail regularity behind the recovered head `f`.
            exact IsRegular.cons hf_on_quotg htail_swap
          simpa using hfinal

-- Proof sketch: first derive `CohenMacaulay R M` internally from `hfs` and `hMdim`. The regular
-- sequence gives `Nontrivial M`, `depth_le_supportDim` yields
-- `moduleDepth R M ≤ supportDim R M = fs.length`, and
-- `IsRegular.exists_append_eq_moduleDepth hfs` forces the reverse inequality, so
-- `supportDim R M = .some (moduleDepth R M)`. Then induct on `fs.length`, exactly as in the
-- source. For the inductive step, the `i.succ` instances of `hgood` identify `g` as good with
-- respect to the tail sequence on the quotient by `f₁`, so induction gives that `g` is a
-- nonzerodivisor on `M / f₁M` and that `M / (g, f₁)M` is Cohen-Macaulay with regular sequence
-- `fs.tail.take (fs.length - 2)`. Then
-- `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular` upgrades this to the
-- stated regularity and Cohen-Macaulay consequences on `M` and `M / gM`.
/-- Lemma 10.103.2 (a): if `fs` is an `M`-regular sequence with
`supportDim R M = fs.length`, `0 < fs.length`, and `g` is good with respect to `(M, fs)`, then
`g` is a nonzerodivisor on `M`. The Cohen-Macaulay condition on `M` is derived internally from the
maximal-length regular sequence hypothesis. -/
@[stacks 00N4]
theorem isSMulRegular_of_isGoodWithRespectTo
    (hMdim : supportDim R M = fs.length)
    (hpos : 0 < fs.length)
    (hfs : IsRegular M fs)
    (hgood : IsGoodWithRespectTo M g fs) :
    IsSMulRegular M g := by
  -- The induction helper proves both the nonzerodivisor statement and the quotient regularity.
  exact
    (isSMulRegular_and_isRegular_take_pred_of_isGoodWithRespectTo
      (M := M) (fs := fs) (g := g) hMdim hpos hfs hgood).1

-- Proof sketch: apply part (a) after deriving `CohenMacaulay R M` internally from `hMdim` and
-- `hfs`. The tail part of `hgood` is the corresponding goodness condition for the quotient by the
-- first element of `fs`, so the inductive argument gives Cohen-Macaulayness of `M / (g, f₁)M`
-- together with regularity of the shortened sequence on that quotient. Appending back `f₁` shows
-- that `fs.take (fs.length - 1)` is regular on `M / gM`, and `hgood` at `i = 0` gives the
-- support-dimension formula for `QuotSMulTop g M`.
/-- Lemma 10.103.2 (b): under the same hypotheses, `M / gM`, written as `QuotSMulTop g M`, is
Cohen--Macaulay with maximal regular sequence `fs.take (fs.length - 1)`. The `i = 0` case of
`hgood` yields the support-dimension equality
`supportDim R (QuotSMulTop g M) = fs.length - 1`, and the Cohen-Macaulay hypothesis on `M` is
again derived internally from `hMdim` and `hfs`. -/
@[stacks 00N4]
theorem cohenMacaulay_quotSMulTop_and_isRegular_take_of_isGoodWithRespectTo
    (hMdim : supportDim R M = fs.length)
    (hpos : 0 < fs.length)
    (hfs : IsRegular M fs)
    (hgood : IsGoodWithRespectTo M g fs) :
    CohenMacaulay R (QuotSMulTop g M) ∧
      IsRegular (QuotSMulTop g M) (fs.take (fs.length - 1)) ∧
      supportDim R (QuotSMulTop g M) = ((fs.length - 1 : ℕ) : WithBot ℕ∞) := by
  rcases
      isSMulRegular_and_isRegular_take_pred_of_isGoodWithRespectTo
        (M := M) (fs := fs) (g := g) hMdim hpos hfs hgood with
    ⟨_, htake⟩
  -- The `i = 0` clause of goodness gives the expected support dimension of `M / gM`.
  have hquot_dim : supportDim R (QuotSMulTop g M) = ((fs.length - 1 : ℕ) : WithBot ℕ∞) :=
    supportDim_quotSMulTop_eq_pred_of_isGoodWithRespectTo (M := M) (fs := fs) (g := g) hpos hgood
  have hquot_dim_length : supportDim R (QuotSMulTop g M) = (fs.take (fs.length - 1)).length := by
    simpa [List.length_take, min_eq_left (Nat.sub_le _ _)] using hquot_dim
  -- The shortened regular sequence has maximal length on the quotient, so the quotient is
  -- Cohen--Macaulay.
  refine ⟨cohenMacaulay_of_supportDim_eq_length_of_isRegular
      (R := R) (N := QuotSMulTop g M) (rs := fs.take (fs.length - 1)) hquot_dim_length htake,
    htake, hquot_dim⟩

end Module

end
