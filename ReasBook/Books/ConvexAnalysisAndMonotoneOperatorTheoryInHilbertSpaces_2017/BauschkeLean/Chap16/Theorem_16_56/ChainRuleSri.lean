import Mathlib
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap15.Corollary_15_28
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10

open Set
open scoped InnerProductSpace

universe u v

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 16 56: the `sri` regularity hypothesis already forces the range of `L`
to meet the effective domain of `g`. -/
private lemma range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub_range
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L)) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  -- Unpack the `sri` witness at `0` into a literal difference representation.
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
  rcases hz with ⟨x, rfl⟩
  -- Then the zero difference identifies the range point with the domain point.
  refine ⟨y, ?_, hy⟩
  simpa [sub_eq_zero.mp hyz]

/-- Helper for Theorem 16 56: under the `sri` regularity branch, every subgradient of `g ∘ L`
already lies in the adjoint image `L^*(∂ g)(L x)`. -/
theorem mem_adjointImage_of_mem_subdifferential_comp_under_zero_mem_sri_range
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L))
    {x u : H} (hu : u ∈ (∂ (g ∘ L)) x) :
    u ∈ ContinuousLinearMap.adjointImageSubdifferential L g x := by
  have hu_eq :
      (g (L x) : EReal) + (g ∘ L).asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    -- Start from the Fenchel-Young characterization of the composite subgradient.
    exact (mem_subdifferential_iff_fenchel_young_eq (f := g ∘ L) x u).1 hu
  have hdom : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub_range (g := g) (L := L) hsri
  have hcomp_eq : (g ∘ L).asEReal∗ u = (L.adjoint ▷ g.asEReal∗) u := by
    -- Rewrite the conjugate of the composite through Chapter 15's adjoint infimal postcomposition.
    simpa [Function.asEReal_apply] using
      congrFun (conjugate_comp_eq_adjointInfimalPostcomposition (g := g) (L := L) hdom) u
  have hu_finite : (L.adjoint ▷ g.asEReal∗) u < ⊤ := by
    have htop : (g ∘ L).asEReal∗ u ≠ ⊤ := by
      intro htop
      have hsum : (g (L x) : EReal) + (g ∘ L).asEReal∗ u = ⊤ := by
        rw [htop, EReal.add_top_of_ne_bot (ne_of_gt (g (L x)).2)]
      exact EReal.coe_ne_top _ (hu_eq.symm.trans hsum)
    -- Finite Fenchel-Young equality forces finiteness of the infimal postcomposition value.
    rw [← hcomp_eq]
    exact lt_top_iff_ne_top.mpr htop
  have hu_dom : u ∈ dom (L.adjoint ▷ g∗[hg]) := by
    -- Move from the `EReal` inequality to membership in the exactness domain.
    rw [mem_dom_iff]
    simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using hu_finite
  obtain ⟨_, ⟨v, hLv, huvalue⟩⟩ :=
    -- Apply the Chapter 15 exactness theorem specialized to the `sri` branch.
    (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).1
      (infimalPostcomposition_adjoint_conjugate_exact_of_regular
        (g := g) (hg := hg) (L := L) (Or.inl hsri) hu_dom)
  have hinner_real : ⟪x, u⟫_ℝ = ⟪L x, v⟫_ℝ := by
    -- Transport the inner product through the adjoint identity and the exact witness `L.adjoint v = u`.
    simpa [hLv] using (ContinuousLinearMap.adjoint_inner_right L x v)
  have hinner : ((⟪x, u⟫_ℝ : ℝ) : EReal) = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  have huvalue' : (L.adjoint ▷ g.asEReal∗) u = g.asEReal∗ v := by
    -- Reinterpret exactness on the packaged `Γ₀` conjugate as equality of the raw conjugates.
    simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using huvalue
  have hgy :
      (g (L x) : EReal) + g.asEReal∗ v = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
    -- Substitute the attained infimal-postcomposition value back into Fenchel-Young equality.
    calc
      (g (L x) : EReal) + g.asEReal∗ v = (g (L x) : EReal) + (L.adjoint ▷ g.asEReal∗) u := by
        rw [huvalue'.symm]
      _ = (g (L x) : EReal) + (g ∘ L).asEReal∗ u := by
        rw [← hcomp_eq]
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hu_eq
      _ = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := hinner
  have hv : v ∈ (∂ g) (L x) := by
    -- One more Fenchel-Young rewrite identifies `v` as a subgradient of `g` at `L x`.
    exact (mem_subdifferential_iff_fenchel_young_eq (f := g) (L x) v).2 hgy
  -- Finally package the witness as membership in the adjoint-image operator.
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
  exact ⟨v, hv, hLv⟩

end SubdifferentialCalculus

end ERealFunction
