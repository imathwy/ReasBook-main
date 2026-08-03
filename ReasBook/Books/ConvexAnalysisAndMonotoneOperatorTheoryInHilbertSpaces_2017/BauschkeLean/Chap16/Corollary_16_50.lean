import Mathlib
import BauschkeLean.Chap06.Proposition_6_20
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped BigOperators InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

open InfimalConvolutionRegularity

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 16 50: the effective domain of a finite pointwise sum is the
intersection of the effective domains of its summands. -/
theorem effectiveDomain_sum_eq_iInter
    (m : ℕ) (g : Fin (m + 1) → H → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (∑ i, g i) = ⋂ i, effectiveDomain (g i) := by
  induction m with
  | zero =>
      -- The one-term sum has the same effective domain as its only summand.
      ext x
      simp
  | succ m ih =>
      -- Split the finite sum into its prefix and final summand, then read the domain
      -- componentwise through `mem_effectiveDomain_pointwiseAdd_iff`.
      ext x
      rw [Fin.sum_univ_castSucc, mem_effectiveDomain_pointwiseAdd_iff]
      rw [ih (fun i : Fin (m + 1) ↦ g i.castSucc)]
      constructor
      · rintro ⟨hprefix, hlast⟩
        rw [Set.mem_iInter]
        intro i
        rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
        · exact Set.mem_iInter.mp hprefix j
        · simpa using hlast
      · intro hx
        rw [Set.mem_iInter] at hx
        refine ⟨?_, ?_⟩
        · rw [Set.mem_iInter]
          intro i
          exact hx i.castSucc
        · exact hx (Fin.last _)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 16 50: the last prefix intersection is exactly the intersection of the
`castSucc` family. -/
theorem previousIntersection_last_eq_iInter_castSucc
    (n : ℕ) (C : Fin (n + 3) → Set H) :
    previousIntersection (n + 1) C (Fin.last (n + 1)) = ⋂ i : Fin (n + 2), C i.castSucc := by
  -- The final prefix contains precisely the first `n + 2` members of the family.
  ext x
  constructor
  · intro hx
    rw [previousIntersection, Set.mem_iInter] at hx
    rw [Set.mem_iInter]
    intro i
    simpa using hx i
  · intro hx
    rw [previousIntersection, Set.mem_iInter]
    intro i
    simpa using Set.mem_iInter.mp hx i

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 16 50: the first prefix intersection is the first set itself. -/
theorem previousIntersection_zero_eq
    (C : Fin 2 → Set H) :
    previousIntersection 0 C 0 = C 0 := by
  ext x
  constructor
  · intro hx
    rw [previousIntersection, Set.mem_iInter] at hx
    exact hx 0
  · intro hx
    rw [previousIntersection, Set.mem_iInter]
    intro i
    have hi : i = 0 := Fin.eq_zero i
    simpa [hi] using hx

omit [CompleteSpace H] in
/-- Helper for Corollary 16 50: the prefix family inherits the successive strong-relative-interior
regularity from the longer family. -/
theorem zero_mem_successiveStrongRelativeInteriorIntersection_prefix
    (n : ℕ) (C : Fin (n + 3) → Set H)
    (hsri : (0 : H) ∈ successiveStrongRelativeInteriorIntersection (n + 1) C) :
    (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
      (fun i : Fin (n + 2) ↦ C i.castSucc) := by
  -- Each prefix successive difference is definitionally the corresponding earlier difference of
  -- the longer family.
  rw [successiveStrongRelativeInteriorIntersection, Set.mem_iInter] at hsri ⊢
  intro i
  simpa [successiveDifference, previousIntersection] using hsri i.castSucc

omit [CompleteSpace H] in
/-- Helper for Corollary 16 50: restricting a `Γ₀` family to its `castSucc` prefix preserves the
`Γ₀` hypothesis on each remaining term. -/
theorem gammaZero_family_castSucc
    (n : ℕ) (f : Fin (n + 3) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 3), f i ∈ Γ₀(H)) :
    ∀ i : Fin (n + 2), f i.castSucc ∈ Γ₀(H) := by
  -- The prefix family is obtained by evaluating the original family on `castSucc` indices.
  intro i
  exact hf i.castSucc

omit [CompleteSpace H] in
/-- Helper for Corollary 16 50: the last successive-difference clause rewrites to the binary
regularity hypothesis for the last summand and the prefix sum. -/
theorem zero_mem_sri_sub_effectiveDomain_last_of_successive_sri
    (n : ℕ) (f : Fin (n + 3) → H → Set.Ioi (⊥ : EReal))
    (hsri :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection (n + 1)
        (fun i ↦ effectiveDomain (f i))) :
    (0 : H) ∈ sri
      (effectiveDomain (f (Fin.last (n + 2))) -
        effectiveDomain (∑ i : Fin (n + 2), f i.castSucc)) := by
  -- Read the last component of the successive-intersection hypothesis and rewrite its prefix part
  -- as the effective domain of the preceding finite sum.
  rw [successiveStrongRelativeInteriorIntersection, Set.mem_iInter] at hsri
  have hlast := hsri (Fin.last (n + 1))
  have hprefix_dom :
      effectiveDomain (∑ i : Fin (n + 2), f i.castSucc) =
        ⋂ i : Fin (n + 2), effectiveDomain (f i.castSucc) :=
    effectiveDomain_sum_eq_iInter (n + 1) (fun i : Fin (n + 2) ↦ f i.castSucc)
  simpa [successiveDifference, previousIntersection_last_eq_iInter_castSucc, hprefix_dom] using
    hlast

omit [CompleteSpace H] in
/-- Helper for Corollary 16 50: under the successive strong-relative-interior hypothesis, the
finite pointwise sum still belongs to `Γ₀(H)`. -/
theorem sum_mem_gammaZero_of_zero_mem_successiveStrongRelativeInteriorIntersection
    (n : ℕ) (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hsri :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
        (fun i ↦ effectiveDomain (f i))) :
    (∑ i, f i) ∈ Γ₀(H) := by
  induction n with
  | zero =>
      -- In the two-term case, use the binary Chapter 15 `Γ₀` sum theorem in the source
      -- orientation `f 1 - f 0`.
      rw [successiveStrongRelativeInteriorIntersection, Set.mem_iInter] at hsri
      have hpair :
          (0 : H) ∈ sri (effectiveDomain (f 1) - effectiveDomain (f 0)) := by
        have hpair' :
            (0 : H) ∈ sri
              (effectiveDomain (f 1) -
                previousIntersection 0 (fun i : Fin 2 ↦ effectiveDomain (f i)) 0) := by
          simpa [successiveDifference] using hsri 0
        simpa [previousIntersection_zero_eq] using hpair'
      -- Rewrite the finite sum into the source binary order after applying the owner theorem.
      simpa [Fin.sum_univ_two, add_comm] using
        pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
          (f 1)
          (f 0)
          (hf 1)
          (hf 0)
          hpair
  | succ n ih =>
      -- Apply the induction hypothesis to the `castSucc` prefix, then add the last function using
      -- the binary Chapter 15 `Γ₀` sum rule in the source orientation `last - prefix`.
      have hprefix_hsri :
          (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
            (fun i : Fin (n + 2) ↦ effectiveDomain (f i.castSucc)) :=
        zero_mem_successiveStrongRelativeInteriorIntersection_prefix n
          (fun i : Fin (n + 3) ↦ effectiveDomain (f i)) hsri
      have hprefix_gamma :
          (∑ i : Fin (n + 2), f i.castSucc) ∈ Γ₀(H) :=
        ih (fun i : Fin (n + 2) ↦ f i.castSucc)
          (gammaZero_family_castSucc n f hf) hprefix_hsri
      have hlast_sri :
          (0 : H) ∈ sri
            (effectiveDomain (f (Fin.last (n + 2))) -
              effectiveDomain (∑ i : Fin (n + 2), f i.castSucc)) :=
        zero_mem_sri_sub_effectiveDomain_last_of_successive_sri
          n
          f
          hsri
      -- The total sum is the prefix sum plus the last summand after commuting the source order.
      simpa [Fin.sum_univ_castSucc, add_comm] using
        pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
          (f (Fin.last (n + 2)))
          (∑ i : Fin (n + 2), f i.castSucc)
          (hf (Fin.last (n + 2)))
          hprefix_gamma
          hlast_sri

omit [CompleteSpace H] in
/-- Helper for Corollary 16 50: a Fenchel--Young equality split for `f + g` separates into the two
component subgradient memberships. -/
theorem component_subgradients_of_dual_sum_split
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x u w : H}
    (hsplit : ((f x : EReal) + (g x : EReal)) +
        (conjugate f.asEReal (u - w) + conjugate g.asEReal w) =
          ((inner ℝ x u : ℝ) : EReal)) :
    u - w ∈ (∂ f) x ∧ w ∈ (∂ g) x := by
  -- The conjugate terms are never `-∞` because `Γ₀(H)` functions have nonempty effective domain.
  have hc_bot : f.asEReal∗ (u - w) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty (u - w)
  have hd_bot : g.asEReal∗ w ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty w
  have hab_bot : (f x : EReal) + (g x : EReal) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hcd_bot : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2
      ⟨bot_lt_iff_ne_bot.mpr hc_bot, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hsum_top :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ (u - w) + g.asEReal∗ w) ≠ ⊤ := by
    intro htop
    exact EReal.coe_ne_top (inner ℝ x u : ℝ) (hsplit.symm.trans htop)
  have hsum_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hab_bot hcd_bot).1 hsum_top
  have hab_top : (f x : EReal) + (g x : EReal) ≠ ⊤ := hsum_top_parts.1
  have hcd_top : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊤ := hsum_top_parts.2
  have hab_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) (ne_of_gt (g x).2)).1 hab_top
  have hcd_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hc_bot hd_bot).1 hcd_top
  have ha_top : (f x : EReal) ≠ ⊤ := hab_top_parts.1
  have hb_top : (g x : EReal) ≠ ⊤ := hab_top_parts.2
  have hc_top : f.asEReal∗ (u - w) ≠ ⊤ := hcd_top_parts.1
  have hd_top : g.asEReal∗ w ≠ ⊤ := hcd_top_parts.2
  have hac_top : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊤ :=
    EReal.add_ne_top ha_top hc_top
  have hbd_top : (g x : EReal) + g.asEReal∗ w ≠ ⊤ :=
    EReal.add_ne_top hb_top hd_top
  have hac_bot : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, bot_lt_iff_ne_bot.mpr hc_bot⟩
  have hbd_bot : (g x : EReal) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(g x).2, bot_lt_iff_ne_bot.mpr hd_bot⟩
  -- Fenchel--Young gives the component lower bounds.
  have hfy_f :
      ((inner ℝ x (u - w) : ℝ) : EReal) ≤
        (f x : EReal) + f.asEReal∗ (u - w) :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hf) x (u - w)
  have hfy_g :
      ((inner ℝ x w : ℝ) : EReal) ≤
        (g x : EReal) + g.asEReal∗ w :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hg) x w
  have hfy_f_toReal :
      inner ℝ x (u - w) ≤
        (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_f (EReal.coe_ne_bot _) hac_top
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot] at htmp
    exact htmp
  have hfy_g_toReal :
      inner ℝ x w ≤
        (g x : EReal).toReal + (g.asEReal∗ w).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_g (EReal.coe_ne_bot _) hbd_top
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot] at htmp
    exact htmp
  -- Convert the displayed equality to `ℝ` so linear arithmetic can isolate each equality case.
  have hsplit_toReal :
      ((f x : EReal).toReal + (g x : EReal).toReal) +
          ((f.asEReal∗ (u - w)).toReal + (g.asEReal∗ w).toReal) =
        inner ℝ x u := by
    have htmp := congrArg EReal.toReal hsplit
    rw [EReal.toReal_add hab_top hab_bot hcd_top hcd_bot,
      EReal.toReal_add ha_top (ne_of_gt (f x).2) hb_top (ne_of_gt (g x).2),
      EReal.toReal_add hc_top hc_bot hd_top hd_bot] at htmp
    exact htmp
  have hpair_real :
      inner ℝ x (u - w) + inner ℝ x w = inner ℝ x u := by
    calc
      inner ℝ x (u - w) + inner ℝ x w
          = (inner ℝ x u - inner ℝ x w) + inner ℝ x w := by
              simp [inner_sub_right]
      _ = inner ℝ x u := by ring
  have hcomp_f_toReal :
      (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal =
        inner ℝ x (u - w) := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hcomp_g_toReal :
      (g x : EReal).toReal + (g.asEReal∗ w).toReal = inner ℝ x w := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hfy_f_eq :
      (f x : EReal) + f.asEReal∗ (u - w) =
        ((inner ℝ x (u - w) : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hac_top hac_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot]
    exact hcomp_f_toReal
  have hfy_g_eq :
      (g x : EReal) + g.asEReal∗ w =
        ((inner ℝ x w : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hbd_top hbd_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot]
    exact hcomp_g_toReal
  -- Read the two exact Fenchel--Young equalities back as subgradient memberships.
  constructor
  · exact
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x (u - w)).2 hfy_f_eq
  · exact
      (mem_subdifferential_iff_fenchel_young_eq (f := g) hg.2.nonempty x w).2 hfy_g_eq

/-- Helper for Corollary 16 50: the binary sum rule follows from Attouch--Brézis exactness under
the canonical strong-relative-interior hypothesis. -/
theorem subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
  ext x u
  have hfg : (f + g) ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri
  constructor
  · intro hu
    -- Use the exact dual split supplied by Attouch--Brézis to separate the active subgradient.
    have hconj :
        (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ :=
      conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri
    have hconj_gamma :
        (((f∗[hf]) □ (g∗[hg])) : H → EReal) = f.asEReal∗ □ g.asEReal∗ := by
      funext z
      simp
    have hprimal_ne_bot : ((f x : EReal) + (g x : EReal)) ≠ ⊥ := by
      refine ne_of_gt ?_
      exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
    have hfy :
        ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u =
          ((inner ℝ x u : ℝ) : EReal) := by
      simpa [pointwiseAdd_apply] using
        (mem_subdifferential_iff_fenchel_young_eq (f := f + g) hfg.2.nonempty x u).1 hu
    have hu_conj_ne_top : (f + g).asEReal∗ u ≠ ⊤ := by
      intro hu_top
      have hsum_top :
          ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u = ⊤ := by
        rw [hu_top]
        exact EReal.add_top_of_ne_bot hprimal_ne_bot
      exact EReal.coe_ne_top (inner ℝ x u : ℝ) (hfy.symm.trans hsum_top)
    have hu_exact_dom :
        u ∈ dom ((((f∗[hf]) □ (g∗[hg])) : H → EReal)) := by
      rw [hconj_gamma, ← hconj, mem_dom_iff]
      exact lt_top_iff_ne_top.mpr hu_conj_ne_top
    rcases
        (infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
          f g hf hg hsri) hu_exact_dom with
      ⟨y, hy⟩
    let w : H := u - y
    have hw :
        (f.asEReal∗ □ g.asEReal∗) u = f.asEReal∗ (u - w) + g.asEReal∗ w := by
      simpa [w, gammaZeroConjugate_apply, sub_sub_cancel] using hy
    have hsplit :
        ((f x : EReal) + (g x : EReal)) +
            (f.asEReal∗ (u - w) + g.asEReal∗ w) =
          ((inner ℝ x u : ℝ) : EReal) := by
      calc
        ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ (u - w) + g.asEReal∗ w)
            = ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ □ g.asEReal∗) u := by
                rw [hw]
        _ = ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u := by
              rw [← hconj]
        _ = ((inner ℝ x u : ℝ) : EReal) := hfy
    rcases component_subgradients_of_dual_sum_split hf hg hsplit with ⟨hvf, hwg⟩
    exact Set.mem_add.2 ⟨u - w, hvf, w, hwg, by simp⟩
  · intro hu
    -- Proposition 16.6 gives the easy inclusion after specializing the linear map to the identity.
    have hu_id :
        u ∈ (∂ f) x +
          ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g x := by
      simpa [ContinuousLinearMap.adjointImageSubdifferential] using hu
    simpa [Function.comp] using
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) x hu_id)

/-- Helper for Corollary 16 50: under the successive strong-relative-interior hypothesis, the
subdifferential of the finite sum is the sum of the subdifferentials. -/
theorem subdifferential_sum_eq_sum_of_zero_mem_successiveStrongRelativeInteriorIntersection
    (n : ℕ) (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hsri :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
        (fun i ↦ effectiveDomain (f i))) :
    (∂ (∑ i, f i) : SetValuedOperator H H) = ∑ i, ∂ f i := by
  induction n with
  | zero =>
      -- In the two-term case, the claim is exactly Corollary 16.48 after rewriting the
      -- one-element intersection hypothesis.
      rw [successiveStrongRelativeInteriorIntersection, Set.mem_iInter] at hsri
      have hpair :
          (0 : H) ∈ sri (effectiveDomain (f 1) - effectiveDomain (f 0)) := by
        have hpair' :
            (0 : H) ∈ sri
              (effectiveDomain (f 1) -
                previousIntersection 0 (fun i : Fin 2 ↦ effectiveDomain (f i)) 0) := by
          simpa [successiveDifference] using hsri 0
        simpa [previousIntersection_zero_eq] using hpair'
      -- Use the binary subdifferential sum rule with the source orientation `f 1 - f 0`.
      simpa [Fin.sum_univ_two, add_comm] using
        subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain (hf 1) (hf 0) hpair
  | succ n ih =>
      -- Route correction: split off the last summand and apply the binary subdifferential sum rule
      -- to `(f last, prefixSum)`, matching the source successive-difference orientation.
      have hprefix_hsri :
          (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
            (fun i : Fin (n + 2) ↦ effectiveDomain (f i.castSucc)) :=
        zero_mem_successiveStrongRelativeInteriorIntersection_prefix n
          (fun i : Fin (n + 3) ↦ effectiveDomain (f i)) hsri
      have hprefix_gamma :
          (∑ i : Fin (n + 2), f i.castSucc) ∈ Γ₀(H) :=
        sum_mem_gammaZero_of_zero_mem_successiveStrongRelativeInteriorIntersection
          n
          (fun i : Fin (n + 2) ↦ f i.castSucc)
          (gammaZero_family_castSucc n f hf)
          hprefix_hsri
      have hprefix_sub :
          (∂ (∑ i : Fin (n + 2), f i.castSucc) : SetValuedOperator H H) =
            ∑ i : Fin (n + 2), ∂ (f i.castSucc) :=
        ih (fun i : Fin (n + 2) ↦ f i.castSucc)
          (gammaZero_family_castSucc n f hf) hprefix_hsri
      have hlast_sri :
          (0 : H) ∈ sri
            (effectiveDomain (f (Fin.last (n + 2))) -
              effectiveDomain (∑ i : Fin (n + 2), f i.castSucc)) :=
        zero_mem_sri_sub_effectiveDomain_last_of_successive_sri
          n
          f
          hsri
      have hbinary :
          (∂
              (f (Fin.last (n + 2)) + ∑ i : Fin (n + 2), f i.castSucc) :
            SetValuedOperator H H) =
            (∂ (f (Fin.last (n + 2)))) +
              ∂ (∑ i : Fin (n + 2), f i.castSucc) :=
        subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain
          (hf (Fin.last (n + 2)))
          hprefix_gamma
          hlast_sri
      -- Rewrite both the function sum and the operator sum by splitting off the final index.
      calc
        (∂ (∑ i, f i) : SetValuedOperator H H)
            = ∂ (∑ i : Fin (n + 2), f i.castSucc + f (Fin.last (n + 2))) := by
                simp [Fin.sum_univ_castSucc, add_comm]
        _ = (∂ (f (Fin.last (n + 2)))) +
              ∂ (∑ i : Fin (n + 2), f i.castSucc) := by
                simpa [add_comm] using hbinary
        _ = (∂ (f (Fin.last (n + 2)))) +
              ∑ i : Fin (n + 2), ∂ (f i.castSucc) := by
                rw [hprefix_sub]
        _ = ∑ i, ∂ f i := by
              simp [Fin.sum_univ_castSucc, add_comm, add_left_comm]

-- Proof sketch: prove the statement by induction on the family length. In the inductive step,
-- apply Corollary 16.48 to the pair consisting of the last function and the preceding finite sum;
-- clause (i) is used directly, while clauses (ii)--(v) reduce to clause (i) through Proposition
-- 6.20 together with Proposition 8.2, exactly as in the source proof.
/-- Corollary 16 50: for a finite family `f : Fin (n + 2) → Γ₀(H)` corresponding to the
textbook index set `{1, ..., m}` with `m ≥ 2`, if one of the source regularity conditions
`(i)`--`(v)` holds for the effective domains, then the subdifferential of the finite sum is the
finite sum of the subdifferentials. -/
theorem subdifferential_sum_eq_sum_of_successiveDomainRegularity
    (n : ℕ) (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hregular :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
          (fun i ↦ effectiveDomain (f i)) ∨
        successiveDifferenceRegularity n (fun i ↦ effectiveDomain (f i))) :
    (∂ (∑ i, f i) : SetValuedOperator H H) = ∑ i, ∂ f i := by
  rcases hregular with hsri | hreg
  · -- Clause `(i)` is exactly the core finite-sum theorem proved above.
    exact
      subdifferential_sum_eq_sum_of_zero_mem_successiveStrongRelativeInteriorIntersection
        n f hf hsri
  · -- Proposition 6.20 converts the remaining regularity clauses to the canonical successive
    -- strong-relative-interior condition.
    have hsri :
        (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
          (fun i ↦ effectiveDomain (f i)) :=
      zero_mem_successiveStrongRelativeInteriorIntersection_of_regularity
        n
        (fun i ↦ effectiveDomain (f i))
        (fun i ↦ (hf i).2.convex_effectiveDomain)
        hreg
    exact
      subdifferential_sum_eq_sum_of_zero_mem_successiveStrongRelativeInteriorIntersection
        n f hf hsri

end SubdifferentialCalculus

end

end ERealFunction
