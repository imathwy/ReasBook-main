import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_13
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PolarCone Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type (max u v)}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜]
variable {f : E → WithBotTop 𝕜} {L : Submodule 𝕜 E}

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "convexDual" => (f⋆ : EStar → WithBotTop 𝕜)
local notation "Ldual" => (Lᗮₚ : Submodule 𝕜 EStar)
local notation "primalValue" => ⨅ x : L, f x
local notation "dualValue" => ⨅ xStar : Ldual, convexDual xStar

omit [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [OrderTopology (WithBotTop 𝕜)] [FiniteDimensional 𝕜 E] [TopologicalSpace EStar] in
private theorem dualCone_eq_pairingOrthogonal :
    (((L : Set E)∗[𝕜] : Set EStar)) = (Ldual : Set EStar) := by
  ext xStar
  constructor
  · intro hx
    have hx' : -xStar ∈ ((L : Set E)ᵒ[𝕜] : Set EStar) := by
      simpa [mem_sourceDualCone_iff_neg_mem_polarCone] using hx
    have hxorth : -xStar ∈ (Ldual : Set EStar) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hx'
    simpa using (Lᗮₚ : Submodule 𝕜 EStar).neg_mem hxorth
  · intro hxorth
    have hxneg : -xStar ∈ (Ldual : Set EStar) := (Lᗮₚ : Submodule 𝕜 EStar).neg_mem hxorth
    have hxpolar : -xStar ∈ ((L : Set E)ᵒ[𝕜] : Set EStar) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hxneg
    simpa [mem_sourceDualCone_iff_neg_mem_polarCone] using hxpolar

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] [FiniteDimensional 𝕜 E] in
private theorem hL_cone : Set.IsConvexCone 𝕜 (L : Set E) := by
  refine ⟨?_, L.convex⟩
  intro c hc x hx
  exact L.smul_mem c hx

omit [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [OrderTopology 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] in
private theorem intrinsicInterior_submodule_eq {F : Type*}
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] (K : Submodule 𝕜 F) :
    intrinsicInterior 𝕜 (K : Set F) = (K : Set F) := by
  simpa only [Submodule.mem_toAffineSubspace] using
    (K.toAffineSubspace.intrinsicInterior_coe :
      intrinsicInterior 𝕜 ((K.toAffineSubspace : AffineSubspace 𝕜 F) : Set F) =
        ((K.toAffineSubspace : AffineSubspace 𝕜 F) : Set F))

omit [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] [TopologicalSpace EStar] in
private theorem hL_closed [CompleteSpace 𝕜] : IsClosed (L : Set E) := by
  have hnormNeOne : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ (1 : ℝ) := by
    rcases NormedField.discreteTopology_or_nontriviallyNormedField 𝕜 with hdisc | hnontriv
    · exfalso
      letI : DiscreteTopology 𝕜 := hdisc
      have hs : Subsingleton 𝕜 := DenselyOrdered.subsingleton_of_discreteTopology (α := 𝕜)
      exact zero_ne_one (α := 𝕜) (Subsingleton.elim 0 1)
    · rcases hnontriv with ⟨⟨h𝕜, hh𝕜⟩⟩
      cases hh𝕜
      rcases h𝕜.non_trivial with ⟨x, hx⟩
      refine ⟨x, ?_, ne_of_gt hx⟩
      intro hx0
      have : ‖x‖ = (0 : ℝ) := by simp [hx0]
      linarith
  letI : NontriviallyNormedField 𝕜 := NontriviallyNormedField.ofNormNeOne hnormNeOne
  haveI : FiniteDimensional 𝕜 L := inferInstance
  exact Submodule.closed_of_finiteDimensional (𝕜 := 𝕜) (E := E) L

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.4.2 is the subspace specialization of Fenchel duality, comparing
  the infimum of `f` on `L` with the infimum of `f⋆` on the pairing annihilator `Lᗮₚ`,
  together with the two branchwise attainment clauses and the equality-case criterion.
- `core/canonical`: the owner declarations are already the cone version
  `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and its companion
  attainment/optimality theorems from `Theorem_31_4`, together with the project owners
  `Function.IsClosedProperConvex`, `riDom[𝕜](·)`, `convexConjugate` (notation `f⋆`), `IsMinOn`,
  and pairing-level `Function.subdifferentialAt` notation `∂[EStar]`.
- `bridge/view`: this file specializes the cone theorem to the subspace cone `K = (L : Set E)`
  and uses the canonical subspace dual-cone bridge
  `Submodule.polarCone_eq_pairingOrthogonal`.

Domain-style sampling used here:

- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and its attainment
  companions from `Theorem_31_4`;
- `optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity` from `Theorem_31_4`;
- `Submodule.polarCone_eq_pairingOrthogonal` as the subspace dual-cone bridge.

Layer target: `bridge/view`.
-/

-- Proof sketch: specialize Theorem 31.4 to the cone `K = (L : Set E)`. A subspace is a convex
-- cone, and its source dual cone is exactly the pairing annihilator `Lᗮₚ`, so the cone duality-gap
-- identity becomes the stated subspace formula under the same two qualification branches.
/-- Corollary 31.4.2: for a closed proper convex function `f` and a linear subspace `L`,
`inf_L f = -inf_{Lᗮₚ} f⋆` whenever either `L ∩ ri(dom f)` or `Lᗮₚ ∩ ri(dom f⋆)` is nonempty. -/
theorem iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification
    [CompleteSpace 𝕜]
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((L : Set E) ∩ riDom[𝕜](f)).Nonempty ∨
      ((Ldual : Set EStar) ∩ riDom[𝕜](convexDual)).Nonempty) :
    primalValue = -dualValue := by
  have hLri : intrinsicInterior 𝕜 (L : Set E) = (L : Set E) :=
    intrinsicInterior_submodule_eq L
  have hLdual : (((L : Set E)∗[𝕜] : Set EStar)) = (Ldual : Set EStar) :=
    dualCone_eq_pairingOrthogonal
  have hLorthri : intrinsicInterior 𝕜 (Ldual : Set EStar) = (Ldual : Set EStar) :=
    intrinsicInterior_submodule_eq Ldual
  have hLclosed : IsClosed (L : Set E) := hL_closed (𝕜 := 𝕜) (E := E) (L := L)
  have hqual' :
      (riDom[𝕜](f) ∩ intrinsicInterior 𝕜 (L : Set E)).Nonempty ∨
        (riDom[𝕜](convexDual) ∩ intrinsicInterior 𝕜 (((L : Set E)∗[𝕜] : Set EStar))).Nonempty := by
    rcases hqual with hq | hq
    · exact Or.inl <| by
        simpa [hLri, Set.inter_comm] using hq
    · exact Or.inr <| by
        simpa [hLdual, hLorthri, Set.inter_comm] using hq
  have hmain :
      primalValue =
        -(⨅ xStar : ↥(((L : Set E)∗[𝕜] : Set EStar)),
          (convexConjugate f : EStar → WithBotTop 𝕜) xStar) :=
    iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification
      hf ⟨0, L.zero_mem⟩ hLclosed hL_cone hqual'
  let e : ↥(((L : Set E)∗[𝕜] : Set EStar)) ≃ Ldual :=
    Equiv.setCongr hLdual
  have hdual :
      (⨅ xStar : ↥(((L : Set E)∗[𝕜] : Set EStar)),
        (convexConjugate f : EStar → WithBotTop 𝕜) xStar) =
        ⨅ xStar : Ldual, (convexConjugate f : EStar → WithBotTop 𝕜) xStar := by
    exact Equiv.iInf_congr e (fun xStar ↦ rfl)
  calc
    primalValue = -(⨅ xStar : ↥(((L : Set E)∗[𝕜] : Set EStar)),
      (convexConjugate f : EStar → WithBotTop 𝕜) xStar) := hmain
    _ = -dualValue := by rw [hdual]

-- Proof sketch: apply the branch-(a) attainment clause of Theorem 31.4 to the cone
-- `K = (L : Set E)`, then rewrite the source dual cone of a subspace as `Lᗮₚ`.
/-- Under qualification (a), the infimum of `f⋆` on `Lᗮₚ` is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_pairingOrthogonal_of_subspace_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((L : Set E) ∩ riDom[𝕜](f)).Nonempty) :
    ∃ xStar ∈ (Ldual : Set EStar), IsMinOn convexDual (Ldual : Set EStar) xStar := by
  have hLri : intrinsicInterior 𝕜 (L : Set E) = (L : Set E) := intrinsicInterior_submodule_eq L
  have hLdual : (((L : Set E)∗[𝕜] : Set EStar)) = (Ldual : Set EStar) :=
    dualCone_eq_pairingOrthogonal
  have hqual' : (riDom[𝕜](f) ∩ intrinsicInterior 𝕜 (L : Set E)).Nonempty := by
    simpa [hLri, Set.inter_comm] using hqual
  have hdualMin :
      ∃ xStar ∈ (((L : Set E)∗[𝕜] : Set EStar)),
        IsMinOn convexDual (((L : Set E)∗[𝕜] : Set EStar)) xStar :=
    exists_mem_isMinOn_convexConjugate_on_dualCone_of_primal_qualification hf hL_cone hqual'
  simpa [hLdual] using hdualMin

-- Proof sketch: apply the branch-(b) attainment clause of Theorem 31.4 to
-- `K = (L : Set E)` and rewrite the source dual cone using the pairing-annihilator bridge.
/-- Under qualification (b), the infimum of `f` on `L` is attained. -/
theorem exists_mem_isMinOn_on_subspace_of_pairingOrthogonal_dual_qualification
    [CompleteSpace 𝕜]
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((Ldual : Set EStar) ∩ riDom[𝕜](convexDual)).Nonempty) :
    ∃ x ∈ (L : Set E), IsMinOn f (L : Set E) x := by
  have hLdual : (((L : Set E)∗[𝕜] : Set EStar)) = (Ldual : Set EStar) :=
    dualCone_eq_pairingOrthogonal
  have hLorthri : intrinsicInterior 𝕜 (Ldual : Set EStar) = (Ldual : Set EStar) :=
    intrinsicInterior_submodule_eq Ldual
  have hLclosed : IsClosed (L : Set E) := hL_closed (𝕜 := 𝕜) (E := E) (L := L)
  have hqual' :
      (riDom[𝕜](convexDual) ∩ intrinsicInterior 𝕜 (((L : Set E)∗[𝕜] : Set EStar))).Nonempty := by
    simpa [hLdual, hLorthri, Set.inter_comm] using hqual
  have hsubspaceMin : ∃ x ∈ (L : Set E), IsMinOn f (L : Set E) x :=
    exists_mem_isMinOn_on_cone_of_dual_qualification hf ⟨0, L.zero_mem⟩ hLclosed hL_cone hqual'
  simpa using hsubspaceMin

-- Proof sketch: specialize the equality-case criterion from Theorem 31.4 to the subspace cone
-- `L`. For a subspace, dual feasibility and complementary slackness reduce canonically to
-- `x ∈ L`, `xStar ∈ Lᗮₚ`, and `⟪x, xStar⟫ₚ = 0`.
/-- The equality-case criterion for the subspace specialization of Fenchel duality, stated in the
canonical `IsMinOn` owner form corresponding to the source equality chain
`f x = inf_L f = -inf_{Lᗮₚ} f⋆ = -f⋆ xStar`. -/
theorem optimalValue_pair_iff_mem_subdifferential_on_subspace
    [CompleteSpace 𝕜]
    (hf : IsClosedProperConvex[𝕜] f)
    (x : E) (xStar : EStar) :
    IsMinOn f (L : Set E) x ∧
      IsMinOn convexDual (Ldual : Set EStar) xStar ∧
      f x = -convexDual xStar ↔
        x ∈ (L : Set E) ∧
          xStar ∈ (Ldual : Set EStar) ∧
            xStar ∈ ∂[EStar]f(x) := by
  have hLdual : (((L : Set E)∗[𝕜] : Set EStar)) = (Ldual : Set EStar) :=
    dualCone_eq_pairingOrthogonal
  have hLclosed : IsClosed (L : Set E) := hL_closed (𝕜 := 𝕜) (E := E) (L := L)
  have hopt :
      IsMinOn f (L : Set E) x ∧
        IsMinOn convexDual (Ldual : Set EStar) xStar ∧
        f x = -convexDual xStar ↔
          xStar ∈ ∂[EStar]f(x) ∧
            x ∈ (L : Set E) ∧ xStar ∈ (Ldual : Set EStar) ∧ ⟪x, xStar⟫ₚ = (0 : 𝕜) := by
    rw [← hLdual]
    exact optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity
      hf hLclosed hL_cone x xStar
  rw [hopt]
  constructor
  · rintro ⟨hxsub, hxL, hxStar, _⟩
    exact ⟨hxL, hxStar, hxsub⟩
  · rintro ⟨hxL, hxStar, hxsub⟩
    refine ⟨hxsub, hxL, hxStar, ?_⟩
    exact (Submodule.mem_pairingOrthogonal_iff (K := L) (y := xStar)).1 hxStar x hxL

end
