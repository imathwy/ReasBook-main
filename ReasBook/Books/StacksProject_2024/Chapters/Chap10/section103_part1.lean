import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_103_1 (from Chap10) -/
universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.CohenMacaulay R M`, the Cohen-Macaulay condition for finite modules over
  a Noetherian local ring;
* core/canonical: the same owner class, expressed directly with `supportDim` and `moduleDepth` in
  the Noetherian local setting;
* bridge/view: the projection `CohenMacaulay.supportDim_eq_moduleDepth`, which exposes the
  defining equality directly from the owner class.

Primitive data are only the finiteness assumption carried by the owner class and the defining
equality `supportDim R M = .some (moduleDepth R M)`. The inherited `Module.Finite` instance is
derived from the owner abstraction and should not be restated as a parallel local instance or a
duplicate unpacking theorem.
-/
/-- Definition 10.103.1: a finite `R`-module over a Noetherian local ring is Cohen-Macaulay when
the Krull dimension of its support equals its depth. -/
class CohenMacaulay : Prop extends Module.Finite R M where
  supportDim_eq_moduleDepth : supportDim R M = .some (moduleDepth R M)

end Module

end

/-! ### Lemma_10_103_2 (from Chap10) -/
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

/-! ### Lemma_10_103_3 (from Chap10) -/
universe u v

open IsLocalRing
open scoped ENat Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Lemma `10.103.3` extracts the regularity and quotient consequences of the support
  dimension equality for `QuotSMulTop g M`;
* core/canonical: `CohenMacaulay R M`, `IsSMulRegular M g`, and the local-depth bridge
  `moduleDepth R M`;
* bridge/view: the quotient module `QuotSMulTop g M` together with the hypothesis
  `supportDim R (QuotSMulTop g M) + 1 = supportDim R M`.

Primitive data are only the owner assumption `[CohenMacaulay R M]` and the support-dimension
equality. In a local ring, `g ∈ maximalIdeal R` is recovered internally from that equality, since
the Cohen-Macaulay hypothesis gives `supportDim R M ≠ ⊥` while a unit `g` would force
`QuotSMulTop g M = 0` and hence `supportDim R (QuotSMulTop g M) = ⊥`. The quotient
Cohen-Macaulayness and depth drop are derived consequences and should be stated through the owner
APIs rather than by repeating a longer `Ideal.depth (maximalIdeal R)` surface.
-/

/-- Helper for Lemma 10.103.3: the support-dimension drop forces the element to lie in the maximal
ideal of the local ring. -/
private theorem mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    g ∈ maximalIdeal R := by
  -- If `g` were a unit, then `gM = M`, so the quotient would be zero and have support dimension
  -- `⊥`, contradicting the Cohen-Macaulay support-dimension identity for `M`.
  by_contra hg
  have hg_unit : IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact not_not.mp hg
  have hsmul_top : g • (⊤ : Submodule R M) = ⊤ := by
    refine top_unique ?_
    intro m hm
    rcases hg_unit with ⟨u, rfl⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(↑u⁻¹ : R) • m, by simp, ?_⟩
    simp [smul_smul]
  have hquot_subsingleton : Subsingleton (QuotSMulTop g M) := by
    rw [Submodule.Quotient.subsingleton_iff]
    simpa using hsmul_top
  letI : Subsingleton (QuotSMulTop g M) := hquot_subsingleton
  have hquot_bot : supportDim R (QuotSMulTop g M) = ⊥ := by
    simpa using Module.supportDim_eq_bot_of_subsingleton (R := R) (M := QuotSMulTop g M)
  have hM_bot : supportDim R M = ⊥ := by
    simpa [hquot_bot] using hdim.symm
  simpa [hM_bot] using
    (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))

/-- Helper for Lemma 10.103.3: every associated prime of a Cohen-Macaulay module has quotient ring
dimension equal to the support dimension of the module. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    [CohenMacaulay R M] (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) = supportDim R M := by
  -- The depth lower bound from the associated-prime theorem matches the ambient support
  -- dimension because `M` is Cohen-Macaulay.
  have hlower :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := M) p hp
  have hlower' : supportDim R M ≤ ringKrullDim (R ⧸ p) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hlower
  have hp_support :
      (⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp)
  have hann_le : Module.annihilator R M ≤ p :=
    Module.annihilator_le_of_mem_support hp_support
  have hup : ringKrullDim (R ⧸ p) ≤ supportDim R M := by
    -- The quotient by `p` is a further quotient of `R / Ann(M)`, so its dimension is no larger.
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
      (Ideal.Quotient.factor_surjective hann_le)
  exact le_antisymm hup hlower'

-- Proof sketch: the Cohen-Macaulay hypothesis gives `supportDim R M = .some (moduleDepth R M)`,
-- so `supportDim R M ≠ ⊥`. If `g` were a unit, then `QuotSMulTop g M = 0`, forcing
-- `supportDim R (QuotSMulTop g M) = ⊥`, contradicting `hdim`; hence `g ∈ maximalIdeal R`
-- internally. Choose a maximal `M`-regular sequence in the maximal ideal from the Cohen-Macaulay
-- hypothesis. The support-dimension equality for `QuotSMulTop g M` shows that `g` is good with
-- respect to that sequence, so Lemma `10.103.2 (1)` yields injectivity of multiplication by `g`.
/-- Lemma 10.103.3 (1): if `R` is a Noetherian local ring, `M` is a Cohen-Macaulay `R`-module,
and `g` cuts the support dimension down by one, written as
`supportDim R (QuotSMulTop g M) + 1 = supportDim R M`, then `g` is a nonzerodivisor on `M`. -/
theorem isSMulRegular_of_cohenMacaulay_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    IsSMulRegular M g := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (M := M) hdim
  -- Route correction: rather than rebuilding the source induction locally, exclude `g` from every
  -- associated prime using the dimension contradiction forced by the assumed one-step drop.
  have hg_not_mem_union : g ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro hg_union
    rcases Set.mem_iUnion.1 hg_union with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hp_assoc, hg_mem_p⟩
    let p' : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime⟩
    have hp_supportM : p' ∈ Module.support R M :=
      Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp_assoc)
    have hp_zeroLocus : p' ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p' ({g} : Set R)).2
        (Set.singleton_subset_iff.mpr hg_mem_p)
    have hp_supportQuot : p' ∈ Module.support R (QuotSMulTop g M) := by
      simpa [Module.support_quotSMulTop] using And.intro hp_supportM hp_zeroLocus
    have hquot_le : ringKrullDim (R ⧸ p) ≤ supportDim R (QuotSMulTop g M) := by
      -- Membership in the quotient support bounds the dimension of `R / p` by the quotient
      -- support dimension.
      have hann_le : Module.annihilator R (QuotSMulTop g M) ≤ p :=
        Module.annihilator_le_of_mem_support hp_supportQuot
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R)
        (M := QuotSMulTop g M)]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
        (Ideal.Quotient.factor_surjective hann_le)
    have hp_dim : ringKrullDim (R ⧸ p) = supportDim R M :=
      ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
        (R := R) (M := M) p hp_assoc
    have hle : supportDim R M ≤ supportDim R (QuotSMulTop g M) := by
      calc
        supportDim R M = ringKrullDim (R ⧸ p) := hp_dim.symm
        _ ≤ supportDim R (QuotSMulTop g M) := hquot_le
    have hnot :
        ¬ supportDim R M ≤ supportDim R (QuotSMulTop g M) := by
      cases hq : supportDim R (QuotSMulTop g M) with
      | bot =>
          have hM_bot : supportDim R M = ⊥ := by
            simpa [hq] using hdim.symm
          have : False := by
            simpa [hM_bot] using
              (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))
          exact False.elim this
      | coe n =>
          letI : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime.ne_top
          have hM_ne_top : supportDim R M ≠ ⊤ := by
            letI : IsLocalRing (R ⧸ p) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
            intro htop
            have : ringKrullDim (R ⧸ p) = ⊤ := by
              simpa [hp_dim] using htop
            exact ringKrullDim_ne_top this
          have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
            intro hn_top
            have hM_top : supportDim R M = ⊤ := by
              calc
                supportDim R M = supportDim R (QuotSMulTop g M) + 1 := hdim.symm
                _ = (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) := by rw [hq, hn_top]
                _ = ⊤ := by rfl
            exact hM_ne_top hM_top
          exact fun hle' ↦
            (lt_irrefl (n : ℕ∞)) <|
              (ENat.add_one_le_iff hn_ne_top).1 <| by
                have hle'' :
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                  calc
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) = supportDim R M := by
                      simpa [hq] using hdim
                    _ ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                      simpa [hq] using hle'
                exact_mod_cast hle''
    exact hnot hle
  -- Avoiding the union of associated primes is exactly the nonzerodivisor criterion.
  simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hg_not_mem_union

-- Proof sketch: first recover `g ∈ maximalIdeal R` internally from `hdim` as in part (1), and
-- then apply part (1) to obtain that `g` is a nonzerodivisor on `M`. Use the quotient criterion
-- for Cohen-Macaulay modules together with the support-dimension equality to identify the depth of
-- `QuotSMulTop g M` as one less than the depth of `M`.
/-- Lemma 10.103.3 (2): under the same hypotheses, the quotient `M / gM`, written canonically as
`QuotSMulTop g M`, is Cohen-Macaulay, and its depth is one less than the depth of `M`. -/
theorem cohenMacaulay_quotSMulTop_and_depth_eq_sub_one_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    CohenMacaulay R (QuotSMulTop g M) ∧
      moduleDepth R (QuotSMulTop g M) = moduleDepth R M - 1 := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (M := M) hdim
  have hreg : IsSMulRegular M g :=
    isSMulRegular_of_cohenMacaulay_of_supportDim_quotSMulTop_add_one_eq
      (R := R) (M := M) hdim
  have hdepth :
      moduleDepth R (QuotSMulTop g M) = moduleDepth R M - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hg_mem
  refine ⟨?_, hdepth⟩
  refine Module.CohenMacaulay.mk ?_
  -- The assumed support-dimension drop and the one-step depth drop identify the quotient as
  -- Cohen-Macaulay.
  cases hq : supportDim R (QuotSMulTop g M) with
  | bot =>
      have hM_bot : supportDim R M = ⊥ := by
        simpa [hq] using hdim.symm
      have : False := by
        simpa [hM_bot] using
          (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))
      exact False.elim this
  | coe n =>
      rw [hdepth]
      have hn_cast :
          (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) := by
        simpa [hq, Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hdim
      have hn : (n : ℕ∞) + 1 = moduleDepth R M :=
        WithBot.coe_inj.mp hn_cast
      have hn_tsub : (n : ℕ∞) = moduleDepth R M - 1 := by
        rw [← hn]
        simpa using
          (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
      simpa using congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hn_tsub

end Module

end

/-! ### Proposition_10_103_4 (from Chap10) -/
universe u

open RingTheory Sequence IsLocalRing
open scoped ENat Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Proposition `10.103.4` is the textbook criterion that a sequence in the maximal
  ideal of a Cohen-Macaulay local module is regular, and hence extends to a maximal regular
  sequence, once the quotient has the expected support dimension;
* core/canonical: `CohenMacaulay R M`, `supportDim R M`, and `RingTheory.Sequence.IsRegular M`;
* bridge/view: the quotient module `M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))`.

Primitive data are only the maximal-ideal membership of `gs`, the ambient support dimension of
`M`, and the owner-level additive equality
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`. The maximal extension is
derived from the existing regular-sequence extension theorem to depth, so this file should not
repackage that owner API through a separate truncated-subtraction condition.
-/

/-- Helper for Proposition 10.103.4: the quotient by a cons list is the quotient by the head
followed by the quotient by the tail on `QuotSMulTop`. -/
private theorem supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop
    {N : Type u} [AddCommGroup N] [Module R N] {g : R} {gs : List R} :
    Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) =
      Module.supportDim R
        ((QuotSMulTop g N) ⧸ (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) := by
  -- The canonical quotient-by-prefix equivalence realizes the source proof's nested quotient.
  exact Module.supportDim_eq_of_equiv <|
    Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N g gs

/-- Helper for Proposition 10.103.4: quotienting by a list of maximal-ideal elements lowers the
support dimension by at most the length of the list. -/
private theorem supportDim_le_supportDim_quotient_ofList_add_length_of_mem_maximalIdeal
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    Module.supportDim R N ≤
      Module.supportDim R (N ⧸ (Ideal.ofList rs • (⊤ : Submodule R N))) + rs.length := by
  induction rs generalizing N with
  | nil =>
      -- The empty list leaves the module unchanged.
      have hquot :
          Module.supportDim R (N ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R N))) =
            Module.supportDim R N := by
        calc
          Module.supportDim R (N ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R N))) =
              Module.supportDim R (N ⧸ (⊥ : Submodule R N)) := by
                rw [Ideal.ofList_nil, Submodule.bot_smul]
          _ = Module.supportDim R N := by
                simpa using
                  (Module.supportDim_eq_of_equiv
                    (Submodule.quotEquivOfEqBot (⊥ : Submodule R N) rfl))
      simpa [hquot] using (le_rfl : Module.supportDim R N ≤ Module.supportDim R N)
  | cons r rs ih =>
      have hr_mem : r ∈ maximalIdeal R := hrs r (by simp)
      have hrs_mem : ∀ s ∈ rs, s ∈ maximalIdeal R := fun s hs ↦ hrs s (by simp [hs])
      have hhead :
          Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop r N) + 1 :=
        (Module.supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (R := R) (M := N) r hr_mem).2
      have htail :
          Module.supportDim R (QuotSMulTop r N) ≤
            Module.supportDim R
                ((QuotSMulTop r N) ⧸
                  (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop r N)))) +
              rs.length :=
        ih (N := QuotSMulTop r N) hrs_mem
      -- Compare the one-step quotient bound with the inductive tail bound.
      calc
        Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop r N) + 1 := hhead
        _ ≤
            (Module.supportDim R
                ((QuotSMulTop r N) ⧸
                  (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop r N)))) +
              rs.length) +
              1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right htail 1
        _ =
            Module.supportDim R (N ⧸ (Ideal.ofList (r :: rs) • (⊤ : Submodule R N))) +
              (r :: rs).length := by
              rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R) (N := N)
                (g := r) (gs := rs)]
              simp [add_assoc]

/-- Helper for Proposition 10.103.4: an equality `x + 1 = d` with `d : ℕ` forces
`x = d - 1` in `WithBot ℕ∞`. -/
private theorem withBotENat_eq_nat_pred_of_add_one_eq_nat {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 = d) :
    x = (d - 1 : ℕ) := by
  cases hx : x with
  | bot =>
      simp [hx] at h
  | coe n =>
      apply WithBot.coe_injective
      have hn_cast :
          ((((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞)) := by
        simpa [hx] using h
      have hn : (n : ℕ∞) + 1 = d :=
        WithBot.coe_inj.mp hn_cast
      have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
        intro hn_top
        have : (⊤ : ℕ∞) = d := by
          simpa [hn_top] using hn
        simpa using this
      have hnat : ENat.toNat (n : ℕ∞) + 1 = d := by
        have hnat' := congrArg ENat.toNat hn
        calc
          ENat.toNat (n : ℕ∞) + 1 = ENat.toNat ((n : ℕ∞) + (1 : ℕ∞)) := by
            symm
            simpa using ENat.toNat_add hn_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
          _ = d := by
            simpa using hnat'
      have hnat_sub : ENat.toNat (n : ℕ∞) = d - 1 := by
        omega
      rw [← ENat.coe_toNat hn_ne_top, hnat_sub]
      rfl

/-- Helper for Proposition 10.103.4: a one-step support-dimension drop forces the element into
the maximal ideal. -/
private theorem mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N) :
    g ∈ maximalIdeal R := by
  -- A unit would make the quotient zero, contradicting the Cohen-Macaulay support-depth identity.
  by_contra hg
  have hg_unit : IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact not_not.mp hg
  have hsmul_top : g • (⊤ : Submodule R N) = ⊤ := by
    refine top_unique ?_
    intro n hn
    rcases hg_unit with ⟨u, rfl⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(↑u⁻¹ : R) • n, by simp, ?_⟩
    simp [smul_smul]
  have hquot_subsingleton : Subsingleton (QuotSMulTop g N) := by
    rw [Submodule.Quotient.subsingleton_iff]
    simpa using hsmul_top
  letI : Subsingleton (QuotSMulTop g N) := hquot_subsingleton
  have hquot_bot : Module.supportDim R (QuotSMulTop g N) = ⊥ := by
    simpa using Module.supportDim_eq_bot_of_subsingleton (R := R) (M := QuotSMulTop g N)
  have hN_bot : Module.supportDim R N = ⊥ := by
    simpa [hquot_bot] using hdim.symm
  simpa [hN_bot] using
    (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))

/-- Helper for Proposition 10.103.4: every associated prime of a Cohen-Macaulay module realizes
the full support dimension. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N]
    (p : Ideal R) (hp : p ∈ associatedPrimes R N) :
    ringKrullDim (R ⧸ p) = Module.supportDim R N := by
  -- Compare the associated-prime depth lower bound with the annihilator quotient upper bound.
  have hlower :
      ((moduleDepth R N : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := N) p hp
  have hlower' : Module.supportDim R N ≤ ringKrullDim (R ⧸ p) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N)] using hlower
  have hp_support :
      (⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩ : PrimeSpectrum R) ∈ Module.support R N :=
    Module.associatedPrimes_subset_support (R := R) (M := N) (by simpa using hp)
  have hann_le : Module.annihilator R N ≤ p :=
    Module.annihilator_le_of_mem_support hp_support
  have hup : ringKrullDim (R ⧸ p) ≤ Module.supportDim R N := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := N)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
      (Ideal.Quotient.factor_surjective hann_le)
  exact le_antisymm hup hlower'

/-- Helper for Proposition 10.103.4: a one-step support-dimension drop makes the head element a
nonzerodivisor and keeps the quotient Cohen-Macaulay. -/
private theorem regular_and_cohenMacaulay_quotSMulTop_of_supportDim_add_one_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N) :
    IsSMulRegular N g ∧ CohenMacaulay R (QuotSMulTop g N) := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (N := N) hdim
  -- Route correction: instead of importing the broken later file, reproduce only the one-step
  -- associated-prime argument needed by the source proof.
  have hg_not_mem_union : g ∉ ⋃ p ∈ associatedPrimes R N, (p : Set R) := by
    intro hg_union
    rcases Set.mem_iUnion.1 hg_union with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hp_assoc, hg_mem_p⟩
    let p' : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime⟩
    have hp_supportN : p' ∈ Module.support R N :=
      Module.associatedPrimes_subset_support (R := R) (M := N) (by simpa using hp_assoc)
    have hp_zeroLocus : p' ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p' ({g} : Set R)).2
        (Set.singleton_subset_iff.mpr hg_mem_p)
    have hp_supportQuot : p' ∈ Module.support R (QuotSMulTop g N) := by
      simpa [Module.support_quotSMulTop] using And.intro hp_supportN hp_zeroLocus
    have hquot_le : ringKrullDim (R ⧸ p) ≤ Module.supportDim R (QuotSMulTop g N) := by
      have hann_le : Module.annihilator R (QuotSMulTop g N) ≤ p :=
        Module.annihilator_le_of_mem_support hp_supportQuot
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R)
        (M := QuotSMulTop g N)]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
        (Ideal.Quotient.factor_surjective hann_le)
    have hp_dim : ringKrullDim (R ⧸ p) = Module.supportDim R N :=
      ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
        (R := R) (N := N) p hp_assoc
    have hle : Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) := by
      calc
        Module.supportDim R N = ringKrullDim (R ⧸ p) := hp_dim.symm
        _ ≤ Module.supportDim R (QuotSMulTop g N) := hquot_le
    have hnot :
        ¬ Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) := by
      cases hq : Module.supportDim R (QuotSMulTop g N) with
      | bot =>
          have hN_bot : Module.supportDim R N = ⊥ := by
            simpa [hq] using hdim.symm
          have : False := by
            simpa [hN_bot] using
              (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))
          exact False.elim this
      | coe n =>
          letI : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime.ne_top
          have hN_ne_top : Module.supportDim R N ≠ ⊤ := by
            letI : IsLocalRing (R ⧸ p) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
            intro htop
            have : ringKrullDim (R ⧸ p) = ⊤ := by
              simpa [hp_dim] using htop
            exact ringKrullDim_ne_top this
          have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
            intro hn_top
            have hN_top : Module.supportDim R N = ⊤ := by
              calc
                Module.supportDim R N = Module.supportDim R (QuotSMulTop g N) + 1 := hdim.symm
                _ = (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) := by rw [hq, hn_top]
                _ = ⊤ := by rfl
            exact hN_ne_top hN_top
          exact fun hle' ↦
            (lt_irrefl (n : ℕ∞)) <|
              (ENat.add_one_le_iff hn_ne_top).1 <| by
                have hle'' :
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                  calc
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) = Module.supportDim R N := by
                      simpa [hq] using hdim
                    _ ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                      simpa [hq] using hle'
                exact_mod_cast hle''
    exact hnot hle
  have hg_reg : IsSMulRegular N g := by
    simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R N] using hg_not_mem_union
  have hdepth :
      moduleDepth R (QuotSMulTop g N) = moduleDepth R N - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hg_reg hg_mem
  refine ⟨hg_reg, ?_⟩
  refine Module.CohenMacaulay.mk ?_
  -- Rewriting the quotient support dimension against the depth drop shows the quotient is still
  -- Cohen-Macaulay.
  cases hq : Module.supportDim R (QuotSMulTop g N) with
  | bot =>
      have hN_bot : Module.supportDim R N = ⊥ := by
        simpa [hq] using hdim.symm
      have : False := by
        simpa [hN_bot] using
          (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))
      exact False.elim this
  | coe n =>
      rw [hdepth]
      have hn_cast :
          (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((moduleDepth R N : ℕ∞) : WithBot ℕ∞) := by
        simpa [hq, Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N)] using hdim
      have hn : (n : ℕ∞) + 1 = moduleDepth R N :=
        WithBot.coe_inj.mp hn_cast
      have hn_tsub : (n : ℕ∞) = moduleDepth R N - 1 := by
        rw [← hn]
        simpa using
          (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
      simpa using congrArg (fun depth : ℕ∞ ↦ (depth : WithBot ℕ∞)) hn_tsub

/-- Helper for Proposition 10.103.4: the expected total support-dimension drop forces the whole
list to be regular by successively applying Lemma `10.103.3` to the head quotient. -/
private theorem regularSequence_of_supportDim_quotient_add_length_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N]
    {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hNdim : Module.supportDim R N = d)
    (hquot :
      Module.supportDim R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))) + gs.length =
        Module.supportDim R N) :
    IsRegular N gs := by
  induction gs generalizing N d with
  | nil =>
      have hN_ne_bot : Module.supportDim R N ≠ ⊥ := by
        simpa [hNdim]
      letI : Nontrivial N := (supportDim_ne_bot_iff_nontrivial R N).mp hN_ne_bot
      -- A Cohen-Macaulay module with finite support dimension is nontrivial, so the empty list
      -- is regular.
      simpa using (IsRegular.nil R N)
  | cons g gs ih =>
      have hg_mem : g ∈ maximalIdeal R := hgs g (by simp)
      have htail_mem : ∀ r ∈ gs, r ∈ maximalIdeal R := fun r hr ↦ hgs r (by simp [hr])
      have htail_le :
          Module.supportDim R (QuotSMulTop g N) ≤
            Module.supportDim R
                ((QuotSMulTop g N) ⧸
                  (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
              gs.length :=
        supportDim_le_supportDim_quotient_ofList_add_length_of_mem_maximalIdeal
          (R := R) (N := QuotSMulTop g N) htail_mem
      have hhead_upper :
          Module.supportDim R (QuotSMulTop g N) + 1 ≤ Module.supportDim R N := by
        -- The total equality forces the first step to drop by exactly one.
        calc
          Module.supportDim R (QuotSMulTop g N) + 1 ≤
              (Module.supportDim R
                  ((QuotSMulTop g N) ⧸
                    (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
                gs.length) +
                1 := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right htail_le 1
          _ =
              Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) +
                (g :: gs).length := by
                rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R)
                  (N := N) (g := g) (gs := gs)]
                simp [add_assoc]
          _ = Module.supportDim R N := hquot
      have hhead_lower :
          Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) + 1 :=
        (Module.supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (R := R) (M := N) g hg_mem).2
      have hhead_eq :
          Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N :=
        le_antisymm hhead_upper hhead_lower
      have hstep :
          IsSMulRegular N g ∧ CohenMacaulay R (QuotSMulTop g N) :=
        regular_and_cohenMacaulay_quotSMulTop_of_supportDim_add_one_eq
          (R := R) (N := N) hhead_eq
      have hg_reg : IsSMulRegular N g := hstep.1
      have hquot_cm :
          CohenMacaulay R (QuotSMulTop g N) :=
        hstep.2
      let _ : CohenMacaulay R (QuotSMulTop g N) := hquot_cm
      have hquot_dim_nat :
          Module.supportDim R (QuotSMulTop g N) = (d - 1 : ℕ) := by
        -- Rewrite the one-step dimension drop against the ambient finite dimension `d`.
        exact withBotENat_eq_nat_pred_of_add_one_eq_nat <| by
          calc
            Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N := hhead_eq
            _ = d := hNdim
      have htail_quot_nat :
          Module.supportDim R
              ((QuotSMulTop g N) ⧸
                (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
            gs.length =
              (d - 1 : ℕ) := by
        -- The same finite-dimension calculation identifies the quotient seen by the recursive
        -- tail step.
        exact withBotENat_eq_nat_pred_of_add_one_eq_nat <| by
          calc
            (Module.supportDim R
                ((QuotSMulTop g N) ⧸
                  (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
              gs.length) +
                1 =
                Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) +
                  (g :: gs).length := by
                    rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R)
                      (N := N) (g := g) (gs := gs)]
                    simp [add_assoc]
            _ = Module.supportDim R N := hquot
            _ = d := hNdim
      have htail_quot :
          Module.supportDim R
              ((QuotSMulTop g N) ⧸
                (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
            gs.length =
              Module.supportDim R (QuotSMulTop g N) := by
        rw [hquot_dim_nat]
        exact htail_quot_nat
      have htail_reg :
          IsRegular (QuotSMulTop g N) gs :=
        ih (N := QuotSMulTop g N) (d := d - 1) htail_mem hquot_dim_nat htail_quot
      -- After proving regularity of the head and of the tail on the head quotient, rebuild the
      -- full regular sequence.
      exact IsRegular.cons hg_reg htail_reg

-- Proof sketch: compare the support dimensions of the successive quotients by the prefixes of
-- `gs` using the one-step bound from Lemma `10.60.13`; the hypothesis `hquot` forces each step to
-- drop the support dimension by exactly one. Apply Lemma `10.103.3` inductively to show that each
-- element of `gs` is a nonzerodivisor on the preceding quotient, hence `gs` is `M`-regular.
-- Then use prime avoidance to choose further elements of `maximalIdeal R` that keep lowering the
-- support dimension until the sequence has length `d`, which is maximal because `M` is
-- Cohen-Macaulay and `hMdim` identifies `d` with `dim (Supp M)`.
/-- Proposition 10.103.4: if `M` is a Cohen-Macaulay module over a Noetherian local ring `R`,
`gs` is a list of elements of `maximalIdeal R`, `dim (Supp M) = d`, and the quotient by the
submodule `(g₁, …, g_c)M`, written as `M ⧸ (Ideal.ofList gs • ⊤)`, has support dimension
`dim (Supp M) - c` in the canonical owner form
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`, then `gs` extends to an
`M`-regular sequence of length `d`. In a local ring, containment of the extended sequence in
`maximalIdeal R` is recovered from regularity by the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. Since `M` is
Cohen-Macaulay, this is a maximal `M`-regular sequence. -/
theorem exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
    [CohenMacaulay R M] {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    ∃ gs' : List R,
      IsRegular M (gs ++ gs') ∧ d = (gs ++ gs').length := by
  have hreg : IsRegular M gs :=
    regularSequence_of_supportDim_quotient_add_length_eq
      (R := R) (N := M) hgs hMdim hquot
  -- Extend the verified regular prefix to one of depth length and identify depth with `d`.
  obtain ⟨gs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  have hdepth_cast :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hMdim
  have hdepth_nat : moduleDepth R M = d :=
    WithBot.coe_inj.mp hdepth_cast
  have hlen_enat : (d : ℕ∞) = (gs ++ gs').length := by
    calc
      (d : ℕ∞) = moduleDepth R M := by simpa using hdepth_nat.symm
      _ = (gs ++ gs').length := hdepth
  refine ⟨gs', hreg', ?_⟩
  exact_mod_cast hlen_enat

-- Proof sketch: apply
-- `exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay`
-- then pass from regularity of the appended sequence to regularity of its initial segment `gs`.
/-- If the quotient by `(g₁, …, g_c)M` has the expected support dimension drop in a
Cohen-Macaulay module, then `gs` itself is an `M`-regular sequence. -/
theorem isRegular_of_supportDim_quotient_add_length_eq_of_cohenMacaulay [CohenMacaulay R M]
    {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    IsRegular M gs := by
  obtain ⟨gs', hreg', -⟩ :=
    exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
      (R := R) (M := M) hgs hMdim hquot
  -- Only the prefix corresponding to the original list is needed here.
  exact isRegular_left_of_isRegular_append (M := M) hreg'

end Module

end

/-! ### Lemma_10_103_5 (from Chap10) -/
open IsLocalRing RingTheory Sequence
open scoped ENat

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/- Domain-style sampling:
* primary domain: Cohen-Macaulay finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.supportDim_quotSMulTop_succ_eq_supportDim`,
  `IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* source/core/bridge triage:
  `source-facing`: the iff statement for passing the Cohen-Macaulay condition across quotient by a
  regular element in the maximal ideal;
  `core/canonical`: `Module.CohenMacaulay`, together with the canonical support-dimension and
  depth-drop theorems for `QuotSMulTop`;
  `bridge/view`: the quotient module `QuotSMulTop x M`.

Primitive data are only `x ∈ maximalIdeal R` and the owner-level regularity hypothesis
`IsSMulRegular M x`. The quotient Cohen-Macaulayness and the reconstruction of
`CohenMacaulay R M` from the quotient are derived API over the existing support-dimension and
depth-drop theorems, so this file should reuse those owner-level equalities directly instead of
introducing a parallel local bridge API.
-/

-- Proof sketch: in both directions, the source proof is that quotienting by a regular element in
-- the maximal ideal lowers both support dimension and module depth by exactly one. For the
-- forward implication, combine the two drop formulas with the Cohen-Macaulay equality for `M` and
-- cancel the common `+ 1` after a case split on `supportDim R (QuotSMulTop x M)`. For the
-- reverse implication, the quotient Cohen-Macaulay hypothesis supplies the quotient equality, and
-- the regular element itself provides the positivity needed to cancel the `- 1` terms.
/-- Helper for Lemma 10.103.5: a nonzerodivisor in the maximal ideal gives positive module
depth. -/
lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ moduleDepth R M := by
  by_cases hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤
  · -- If `𝔪 M = M`, the local depth is infinite, so positivity is immediate.
    have hdepth_top : moduleDepth R M = ⊤ :=
      Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul
    rw [hdepth_top]
    simp
  · -- Otherwise depth is computed by regular-sequence lengths, and `[x]` is one such sequence.
    have hnontrivial : Nontrivial M := by
      by_contra hsub
      letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hsub
      apply hsmul
      ext m
      simp [Subsingleton.elim m 0]
    letI : Nontrivial M := hnontrivial
    have hsingleton_reg : IsRegular M [x] :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
        (by
          intro r hr
          simpa [List.mem_singleton.mp hr] using hx)
        ((isWeaklyRegular_singleton_iff M x).2 hreg)
    have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal R := by
      simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
    have hdepth_eq :
        moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) :=
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul
    rw [hdepth_eq]
    refine le_sSup ?_
    exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Lemma 10.103.5: if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`x ∈ maximalIdeal R` is a nonzerodivisor on `M`, then `M` is Cohen-Macaulay if and only if the
quotient `M / xM`, written canonically as `QuotSMulTop x M`, is Cohen-Macaulay. -/
theorem cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    CohenMacaulay R M ↔ CohenMacaulay R (QuotSMulTop x M) := by
  constructor
  · intro hM
    have hsupport :
        supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
      supportDim_quotSMulTop_succ_eq_supportDim hreg hx
    have hdepth_quot :
        moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 :=
      IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hx
    refine Module.CohenMacaulay.mk ?_
    -- Rewrite the Cohen-Macaulay equality for `M` through the one-step quotient formulas.
    cases hq : supportDim R (QuotSMulTop x M) with
    | bot =>
        have hM_bot : supportDim R M = ⊥ := by
          simpa [hq] using hsupport.symm
        have : False := by
          simpa [hM_bot] using hM.supportDim_eq_moduleDepth
        exact False.elim this
    | coe n =>
        rw [hdepth_quot]
        have hn_cast :
            (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (moduleDepth R M : WithBot ℕ∞) := by
          simpa [hq, hM.supportDim_eq_moduleDepth] using hsupport
        have hn : (n : ℕ∞) + 1 = moduleDepth R M :=
          WithBot.coe_inj.mp hn_cast
        have hn_tsub : (n : ℕ∞) = moduleDepth R M - 1 := by
          rw [← hn]
          simpa using
            (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
        simpa [hq] using congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hn_tsub
  · intro hquot
    -- The regular element in `𝔪` gives the positivity needed to cancel the `- 1` identities.
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth R M :=
      one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular (R := R) (M := M) hx hreg
    have hsupport :
        supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
      supportDim_quotSMulTop_succ_eq_supportDim hreg hx
    have hdepth_quot :
        moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 :=
      IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hx
    have hdepth_cancel : moduleDepth R M - 1 + 1 = moduleDepth R M :=
      tsub_add_cancel_of_le hdepth_pos
    have hdepth_cancel_cast :
        ((moduleDepth R M - 1 + 1 : ℕ∞) : WithBot ℕ∞) =
          (moduleDepth R M : WithBot ℕ∞) :=
      congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hdepth_cancel
    refine Module.CohenMacaulay.mk ?_
    -- Rewriting support dimension and depth through the quotient recovers the defining equality.
    rw [← hsupport, hquot.supportDim_eq_moduleDepth, hdepth_quot]
    simpa using hdepth_cancel_cast

end Module

end
