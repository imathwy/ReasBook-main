import BauschkeLean.Chap19.Proposition_19_20
import BauschkeLean.Chap26.Remark_26_29

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ContinuousLinearMap
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u v

namespace ERealFunction

section CompositeDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Remark 26.31 identifies the composite subgradient-pair set with the saddle-point
  set of the Chapter 19 composite perturbation Lagrangian.
- `core/canonical`: the ambient saddle-point owner is `IsSaddlePointOn`, applied to the canonical
  perturbation owner `compositePerturbationFunction`.
- `bridge/view`: the pointwise equivalence below packages the set equality as a directly callable
  membership theorem.
-/

/-- Remark 26.31, pointwise form: the subgradient-pair condition is equivalent to the saddle-point
condition for the canonical Chapter 19 composite perturbation Lagrangian
`ℒ[compositePerturbationFunction f g L]`. -/
theorem
    subgradient_pair_iff_isSaddlePointOn_lagrangian_compositePerturbationFunction
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    (-L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x)) ↔
      IsSaddlePointOn (univ : Set H) (univ : Set K)
        (ℒ[compositePerturbationFunction f g L]) x v := by
  let F : H × K → Set.Ioi (⊥ : EReal) := compositePerturbationFunction f g L
  constructor
  · intro hsub
    have hzero :
        ((f x : EReal) + (g (L x) : EReal)) +
            (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 :=
      (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).2 hsub
    have hcontact :
        compositePrimalObjective f g L x = -compositeDualObjective f g L v :=
      (composite_contact_eq_iff_zero_gap hf hg L x v).2 hzero
    have hgv : L x ∈ (∂ (g∗[hg])) v :=
      (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate g hg (L x) v).1 hsub.2
    have hfy_g :
        (g (L x) : EReal) + g.asEReal∗ v = ((⟪L x, v⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        g hg.2.nonempty (L x) v).1 hsub.2
    have hxdom : x ∈ effectiveDomain f := by
      exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf <| by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨-(L.adjoint v), hsub.1⟩
    have hvdom : v ∈ effectiveDomain (g∗[hg]) := by
      exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
        (gammaZeroConjugate_mem_gammaZero hg) <| by
          rw [SetValuedOperator.mem_dom_iff]
          exact ⟨L x, hgv⟩
    classical
    have hlag :
        ℒ[F] x v = compositePrimalObjective f g L x := by
      have hLxdom : L x ∈ effectiveDomain g := by
        exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg <| by
          rw [SetValuedOperator.mem_dom_iff]
          exact ⟨v, hsub.2⟩
      have hgx_bot : (g (L x) : EReal) ≠ ⊥ := ne_of_gt (g (L x)).2
      have hgx_top : (g (L x) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hLxdom)
      have hgv_bot : (g∗[hg] v : EReal) ≠ ⊥ := ne_of_gt (g∗[hg] v).2
      have hgv_top : (g∗[hg] v : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hvdom)
      have hbranch :
          (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) = (g (L x) : EReal) := by
        have hsum : (g (L x) : EReal) + (g∗[hg] v : EReal) = (⟪L x, v⟫_ℝ : EReal) := by
          simpa [gammaZeroConjugate_apply] using hfy_g
        apply le_antisymm
        · exact
            (EReal.sub_le_iff_le_add (.inl hgv_bot) (.inl hgv_top)).2
              (by simpa [add_comm] using hsum.symm.le)
        · exact
            (EReal.le_sub_iff_add_le (.inl hgv_bot) (.inl hgv_top)).2
              (by simpa using hsum.le)
      have hlag_if :
          (if hx : x ∈ effectiveDomain f then
              if hv : v ∈ effectiveDomain (g∗[hg]) then
                (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
              else
                ⊥
            else
              ⊤) =
            (f x : EReal) + (g (L x) : EReal) := by
        calc
          (if hx : x ∈ effectiveDomain f then
              if hv : v ∈ effectiveDomain (g∗[hg]) then
                (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
              else
                ⊥
            else
              ⊤) =
              (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) := by
                simp [hxdom, hvdom]
          _ = (f x : EReal) + (g (L x) : EReal) := by
                calc
                  (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) =
                      (f x : EReal) + ((⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)) := by
                        simp [sub_eq_add_neg, add_assoc]
                  _ = (f x : EReal) + (g (L x) : EReal) := by
                        rw [hbranch]
      have hlag_comp :
          ℒ[compositePerturbationFunction f g L] x v =
            if hx : x ∈ effectiveDomain f then
              if hv : v ∈ effectiveDomain (g∗[hg]) then
                (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
              else
                ⊥
            else
              ⊤ :=
        lagrangian_compositePerturbationFunction f g L hg x v
      simpa [F] using hlag_comp.trans hlag_if
    refine (lagrangian_isSaddlePointOn_iff F x v).2 ?_
    constructor
    · calc
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = compositePrimalObjective f g L x := by
            have hsup :
                sSup (Set.range fun w : K ↦ ℒ[compositePerturbationFunction f g L] x w) =
                  compositePrimalObjective f g L x :=
              lagrangian_sSup_eq_compositePrimalObjective f g L hg x
            simpa [F] using hsup
        _ = ℒ[F] x v := hlag.symm
    · calc
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -compositeDualObjective f g L v := by
            have hinf :
                sInf (Set.range fun z : H ↦ ℒ[compositePerturbationFunction f g L] z v) =
                  -compositeDualObjective f g L v :=
              lagrangian_sInf_eq_neg_compositeDualObjective f g L v
            simpa [F] using hinf
        _ = compositePrimalObjective f g L x := hcontact.symm
        _ = ℒ[F] x v := hlag.symm
  · intro hsaddle
    have hs := (lagrangian_isSaddlePointOn_iff F x v).1 (by simpa [F] using hsaddle)
    have hcontact :
        compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
      have hsup :
          sSup (Set.range fun w : K ↦ ℒ[compositePerturbationFunction f g L] x w) =
            compositePrimalObjective f g L x :=
        lagrangian_sSup_eq_compositePrimalObjective f g L hg x
      have hinf :
          sInf (Set.range fun z : H ↦ ℒ[compositePerturbationFunction f g L] z v) =
            -compositeDualObjective f g L v :=
        lagrangian_sInf_eq_neg_compositeDualObjective f g L v
      calc
        compositePrimalObjective f g L x = sSup (Set.range fun w : K ↦ ℒ[F] x w) := by
          simpa [F] using hsup.symm
        _ = ℒ[F] x v := hs.1
        _ = sInf (Set.range fun z : H ↦ ℒ[F] z v) := hs.2.symm
        _ = -compositeDualObjective f g L v := by
          simpa [F] using hinf
    have hzero :
        ((f x : EReal) + (g (L x) : EReal)) +
            (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 :=
      (composite_contact_eq_iff_zero_gap hf hg L x v).1 hcontact
    exact (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).1 hzero

/-- Remark 26.31: the subgradient-pair set
`{(x, v) | -L^* v ∈ ∂ f(x) ∧ v ∈ ∂ g(Lx)}` is exactly the set of saddle points of the
Chapter 19 composite perturbation Lagrangian `ℒ[compositePerturbationFunction f g L]`. -/
theorem subgradient_pair_set_eq_saddlePoints_lagrangian_compositePerturbationFunction
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) :
    {p : H × K | -L.adjoint p.2 ∈ (∂ f) p.1 ∧ p.2 ∈ (∂ g) (L p.1)} =
      {p : H × K |
        IsSaddlePointOn (univ : Set H) (univ : Set K)
          (ℒ[compositePerturbationFunction f g L]) p.1 p.2} := by
  ext p
  simpa using
    subgradient_pair_iff_isSaddlePointOn_lagrangian_compositePerturbationFunction
      hf hg L p.1 p.2

end CompositeDuality

end ERealFunction
