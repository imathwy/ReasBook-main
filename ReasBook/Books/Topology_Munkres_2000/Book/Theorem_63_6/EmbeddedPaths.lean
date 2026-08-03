module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Subpath

public section

open Set Filter

namespace Path

/-- Helper for Theorem 63.6: concatenating injective paths whose ranges meet
only at their common endpoint gives an injective path. -/
lemma trans_injective_of_range_inter_eq_singleton
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (alpha : Path x y) (beta : Path y z)
    (halpha : Function.Injective alpha) (hbeta : Function.Injective beta)
    (hinter : Set.range alpha ∩ Set.range beta = {y}) :
    Function.Injective (alpha.trans beta) := by
  -- Equal parameters in the same half are handled by the corresponding path;
  -- parameters in opposite halves must both represent the joining endpoint.
  have hcross (s t : unitInterval) (hs : (s : ℝ) ≤ 1 / 2)
      (ht : ¬ (t : ℝ) ≤ 1 / 2)
      (hst : (alpha.trans beta) s = (alpha.trans beta) t) : s = t := by
    rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
    have hsMem : 2 * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [s.property.1], by linarith⟩
    have htMem : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [not_le.mp ht], by linarith [t.property.2]⟩
    let s₁ : unitInterval := ⟨2 * (s : ℝ), hsMem⟩
    let t₂ : unitInterval := ⟨2 * (t : ℝ) - 1, htMem⟩
    change alpha s₁ = beta t₂ at hst
    have hsInter : alpha s₁ ∈ Set.range alpha ∩ Set.range beta :=
      ⟨Set.mem_range_self s₁, ⟨t₂, hst.symm⟩⟩
    rw [hinter, Set.mem_singleton_iff] at hsInter
    have hsOne : s₁ = 1 := halpha (hsInter.trans alpha.target.symm)
    have htZero : t₂ = 0 :=
      hbeta (hst.symm.trans hsInter |>.trans beta.source.symm)
    apply Subtype.ext
    have hsValue := congrArg Subtype.val hsOne
    have htValue := congrArg Subtype.val htZero
    dsimp [s₁, t₂] at hsValue htValue ⊢
    linarith
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have hparameters := congrArg Subtype.val (halpha hst)
      apply Subtype.ext
      dsimp at hparameters ⊢
      linarith
    · exact hcross s t hs ht hst
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · exact (hcross t s ht hs hst.symm).symm
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_neg ht] at hst
      have hparameters := congrArg Subtype.val (hbeta hst)
      apply Subtype.ext
      dsimp at hparameters ⊢
      linarith

/-- Helper for Theorem 63.6: a nondegenerate subpath of an injective path is
injective. -/
lemma subpath_injective_of_ne
    {X : Type*} [TopologicalSpace X] {x y : X}
    (gamma : Path x y) (hgamma : Function.Injective gamma)
    (s t : unitInterval) (hst : s ≠ t) :
    Function.Injective (gamma.subpath s t) := by
  -- The affine interval reparametrization is injective when its endpoints differ.
  intro u v huv
  change gamma (Set.Icc.convexComb s t u) =
    gamma (Set.Icc.convexComb s t v) at huv
  have hparameters := congrArg Subtype.val (hgamma huv)
  have hvalues : (s : ℝ) ≠ (t : ℝ) := Subtype.coe_ne_coe.mpr hst
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb] at hparameters
  rcases lt_or_gt_of_ne hvalues with hlt | hgt
  · nlinarith
  · nlinarith

/-- Helper for Theorem 63.6: two embedded paths with a common endpoint contain
an embedded path joining their other endpoints. -/
theorem existsEmbeddingInRangeUnion
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y z : X}
    (alpha : Path x y) (beta : Path y z)
    (halpha : Topology.IsEmbedding alpha) (hbeta : Topology.IsEmbedding beta)
    (hxz : x ≠ z) :
    ∃ gamma : Path x z, Topology.IsEmbedding gamma ∧
      Set.range gamma ⊆ Set.range alpha ∪ Set.range beta := by
  classical
  -- Choose the first parameter at which `alpha` meets the compact range of `beta`.
  let hitSet : Set unitInterval := alpha ⁻¹' Set.range beta
  have hitSetClosed : IsClosed hitSet := by
    exact (isCompact_range beta.continuous).isClosed.preimage alpha.continuous
  have hitSetCompact : IsCompact hitSet :=
    isCompact_univ.of_isClosed_subset hitSetClosed (Set.subset_univ _)
  have hitSetNonempty : hitSet.Nonempty := by
    refine ⟨1, ?_⟩
    change alpha 1 ∈ Set.range beta
    exact ⟨0, beta.source.trans alpha.target.symm⟩
  obtain ⟨t₀, ht₀Hit, ht₀Least⟩ := hitSetCompact.exists_isLeast hitSetNonempty
  change alpha t₀ ∈ Set.range beta at ht₀Hit
  obtain ⟨s₀, hs₀⟩ := ht₀Hit
  by_cases ht₀Zero : t₀ = 0
  · -- If the first hit is the source, the terminal subpath of `beta` suffices.
    have hs₀One : s₀ ≠ 1 := by
      intro hs₀One
      apply hxz
      calc
        x = alpha 0 := alpha.source.symm
        _ = alpha t₀ := congrArg alpha ht₀Zero.symm
        _ = beta s₀ := hs₀.symm
        _ = beta 1 := congrArg beta hs₀One
        _ = z := beta.target
    let raw : Path (beta s₀) (beta 1) := beta.subpath s₀ 1
    have sourceEq : x = beta s₀ := by
      calc
        x = alpha 0 := alpha.source.symm
        _ = alpha t₀ := congrArg alpha ht₀Zero.symm
        _ = beta s₀ := hs₀.symm
    let gamma : Path x z := raw.cast sourceEq beta.target.symm
    have gammaCoe : (gamma : unitInterval → X) = raw :=
      Path.cast_coe raw sourceEq beta.target.symm
    have gammaInjective : Function.Injective gamma := by
      rw [gammaCoe]
      exact Path.subpath_injective_of_ne beta hbeta.injective s₀ 1 hs₀One
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    rw [Set.range_subset_iff, gammaCoe]
    intro u
    exact Or.inr ⟨Set.Icc.convexComb s₀ 1 u, rfl⟩
  by_cases hs₀One : s₀ = 1
  · -- Dually, a hit at the target of `beta` leaves only the initial subpath.
    let raw : Path (alpha 0) (alpha t₀) := alpha.subpath 0 t₀
    have targetEq : z = alpha t₀ := by
      calc
        z = beta 1 := beta.target.symm
        _ = beta s₀ := congrArg beta hs₀One.symm
        _ = alpha t₀ := hs₀
    let gamma : Path x z := raw.cast alpha.source.symm targetEq
    have gammaCoe : (gamma : unitInterval → X) = raw :=
      Path.cast_coe raw alpha.source.symm targetEq
    have gammaInjective : Function.Injective gamma := by
      rw [gammaCoe]
      exact Path.subpath_injective_of_ne alpha halpha.injective 0 t₀
        (Ne.symm ht₀Zero)
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    rw [Set.range_subset_iff, gammaCoe]
    intro u
    exact Or.inl ⟨Set.Icc.convexComb 0 t₀ u, rfl⟩
  · -- Otherwise trim both paths and concatenate them at the first hit.
    let leftRaw : Path (alpha 0) (alpha t₀) := alpha.subpath 0 t₀
    let rightRaw : Path (beta s₀) (beta 1) := beta.subpath s₀ 1
    let left : Path x (alpha t₀) := leftRaw.cast alpha.source.symm rfl
    let right : Path (alpha t₀) z := rightRaw.cast hs₀.symm beta.target.symm
    let gamma : Path x z := left.trans right
    have leftCoe : (left : unitInterval → X) = leftRaw :=
      Path.cast_coe leftRaw alpha.source.symm rfl
    have rightCoe : (right : unitInterval → X) = rightRaw :=
      Path.cast_coe rightRaw hs₀.symm beta.target.symm
    have leftInjective : Function.Injective left := by
      rw [leftCoe]
      exact Path.subpath_injective_of_ne alpha halpha.injective 0 t₀
        (Ne.symm ht₀Zero)
    have rightInjective : Function.Injective right := by
      rw [rightCoe]
      exact Path.subpath_injective_of_ne beta hbeta.injective s₀ 1 hs₀One
    have rangeInter : Set.range left ∩ Set.range right = {alpha t₀} := by
      rw [leftCoe, rightCoe, Path.range_subpath_of_le alpha 0 t₀ bot_le,
        Path.range_subpath_of_le beta s₀ 1 le_top]
      ext w
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
        have huHit : u ∈ hitSet := by
          change alpha u ∈ Set.range beta
          exact ⟨v, huv⟩
        have ht₀u : t₀ ≤ u := ht₀Least huHit
        have hut₀ : u = t₀ := le_antisymm hu.2 ht₀u
        rw [Set.mem_singleton_iff, hut₀]
      · intro hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact ⟨⟨t₀, ⟨bot_le, le_rfl⟩, rfl⟩,
          ⟨s₀, ⟨le_rfl, le_top⟩, hs₀⟩⟩
    have gammaInjective : Function.Injective gamma :=
      Path.trans_injective_of_range_inter_eq_singleton left right
        leftInjective rightInjective rangeInter
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    change Set.range (left.trans right) ⊆ Set.range alpha ∪ Set.range beta
    rw [Path.trans_range, leftCoe, rightCoe]
    apply Set.union_subset
    · rw [Path.range_subpath]
      exact (Set.image_subset_range alpha _).trans Set.subset_union_left
    · rw [Path.range_subpath]
      exact (Set.image_subset_range beta _).trans Set.subset_union_right

end Path

namespace Schoenflies

/-- Helper for Theorem 63.6: distinct points of an open connected subset of a
real normed vector space are joined inside it by an embedded path. -/
theorem existsEmbeddedPathInOpenConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUconnected : IsConnected U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ gamma : Path x y, Topology.IsEmbedding gamma ∧ Set.range gamma ⊆ U := by
  -- Use embedded path access as the locally generated symmetric relation.
  let R : E → E → Prop := fun a b ↦
    a = b ∨ ∃ gamma : Path a b, Topology.IsEmbedding gamma ∧ Set.range gamma ⊆ U
  have localAccess : ∀ a ∈ U, ∀ᶠ b in nhdsWithin a U, R a b := by
    intro a ha
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hUopen a ha
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds a hepsilon)] with b hb
    by_cases hab : a = b
    · exact Or.inl hab
    · right
      let gamma : Path a b := Path.segment a b
      have gammaInjective : Function.Injective gamma :=
        Path.segment_injective_of_ne hab
      have gammaRange : Set.range gamma ⊆ U := by
        change Set.range (Path.segment a b) ⊆ U
        rw [Path.range_segment]
        exact ((convex_ball a epsilon).segment_subset
          (Metric.mem_ball_self hepsilon) hb).trans hball
      exact ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding,
        gammaRange⟩
  have transitiveAccess : ∀ a b d, a ∈ U → b ∈ U → d ∈ U →
      R a b → R b d → R a d := by
    intro a b d _ _ _ hab hbd
    rcases hab with rfl | ⟨alpha, halpha, halphaRange⟩
    · exact hbd
    rcases hbd with rfl | ⟨beta, hbeta, hbetaRange⟩
    · exact Or.inr ⟨alpha, halpha, halphaRange⟩
    by_cases had : a = d
    · exact Or.inl had
    · right
      obtain ⟨gamma, hgamma, hgammaRange⟩ :=
        Path.existsEmbeddingInRangeUnion alpha beta halpha hbeta had
      exact ⟨gamma, hgamma,
        hgammaRange.trans (Set.union_subset halphaRange hbetaRange)⟩
  have symmetricAccess : ∀ a b, a ∈ U → b ∈ U → R a b → R b a := by
    intro a b _ _ hab
    rcases hab with rfl | ⟨gamma, hgamma, hgammaRange⟩
    · exact Or.inl rfl
    · right
      have reverseInjective : Function.Injective gamma.symm := by
        intro s t hst
        apply unitInterval.symm_bijective.injective
        exact hgamma.injective hst
      exact ⟨gamma.symm,
        gamma.symm.continuous.isClosedEmbedding reverseInjective |>.isEmbedding,
        Path.symm_range gamma ▸ hgammaRange⟩
  have haccess : R x y := by
    exact hUconnected.isPreconnected.induction₂ R localAccess transitiveAccess
      symmetricAccess hx hy
  rcases haccess with hxy' | hpath
  · exact False.elim (hxy hxy')
  · exact hpath

end Schoenflies
