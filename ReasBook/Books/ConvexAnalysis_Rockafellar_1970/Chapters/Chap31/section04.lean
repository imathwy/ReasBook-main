import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_31_4_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]

variable {f : (ι → 𝕜) → WithBotTop 𝕜}

local notation "IsClosedProperConvex[𝕜]" => @Function.IsClosedProperConvex 𝕜
local notation "orthant" => (ConvexCone.positive 𝕜 (ι → 𝕜) : Set (ι → 𝕜))
local notation "convexDual" => (f⋆ : (ι → 𝕜) → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.4.1 is the nonnegative-orthant specialization of Fenchel duality
  on a finite coordinate space `𝕜^ι`, together with the two branchwise attainment
  conclusions and the coordinatewise complementary-slackness optimality criterion.
- `core/canonical`: the owner abstraction is the cone-duality package in `Theorem_31_4`,
  specialized to the canonical chapter orthant owner `orthant`,
  together with `f.IsClosedProperConvex`, the Fenchel conjugate `convexDual`, `riDom[𝕜](·)`,
  `IsMinOn`, and the pairing-level Chapter 23 subgradient owner `_root_.subdifferentialAt`
  (surface notation: `∂[(ι → 𝕜)]f(x)`).
- `bridge/view`: the source inequalities `x ≥ 0` and `x⋆ ≥ 0` are rendered by membership in the
  canonical orthant owner in the intrinsic coordinate ambient `X = ι → 𝕜`;
  `mem_nonnegativeOrthant_iff` therefore
  recovers the source reading `∀ i, 0 ≤ x i`, and the source coordinatewise complementarity
  condition is kept explicitly as `∀ i, x i * xStar i = 0`.

Domain-style sampling used here:

- `ConvexCone.positive` and `mem_nonnegativeOrthant_iff` from `Chap01.Definition_2_5_11`;
- `polarCone_nonnegativeOrthant_eq_neg` from `Chap03.Text_14_0_10`;
- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_polyhedral_fenchel_cone_qualification`,
  `exists_mem_isMinOn_convexConjugate_on_dualCone_of_polyhedral_primal_qualification`,
  `exists_mem_isMinOn_on_cone_of_polyhedral_dual_qualification`, and
  `optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity` from
  `Chap06.Theorem_31_4`.
- the canonical pointwise-order instances on `ι → 𝕜`, which make `0 ≤ x` equivalent to
  `∀ i, 0 ≤ x i`.

Primitive data vs derived API:

- primitive inputs: the closed proper convex function `f` on the finite coordinate space `𝕜^ι`
  and the two source
  qualification clauses on `riDom[𝕜](f)` and `riDom[𝕜](convexDual)`;
- derived API: the zero-duality-gap identity on the nonnegative orthant, the two attainment
  conclusions, and the orthant-specialized optimality criterion.

Layer target: `bridge/view`, implemented as the orthant specialization of the existing cone
duality owner rather than by introducing a parallel local orthant owner.
-/

-- Proof sketch: specialize the polyhedral cone theorem from `Theorem_31_4` to the nonnegative
-- orthant owner `orthant`. The source coordinatewise reading is a
-- companion view supplied by `mem_nonnegativeOrthant_iff`.
/-- Corollary 31.4.1: for a closed proper convex function `f` on the finite coordinate space
`𝕜^ι`, the infimum of `f` over the nonnegative orthant equals the negative of the infimum of
`f⋆` over the nonnegative orthant whenever either some `x ∈ riDom[𝕜](f)` satisfies `x ≥ 0`
or some `x⋆ ∈ riDom[𝕜](f⋆)` satisfies
`x⋆ ≥ 0`. -/
theorem
    iInf_on_nonnegativeOrthant_eq_neg_iInf_convexConjugate_of_fenchel_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual :
      ((riDom[𝕜](f) : Set (ι → 𝕜)) ∩ orthant).Nonempty ∨
        ((riDom[𝕜](convexDual) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    (⨅ x : orthant, f x) = -(⨅ xStar : orthant, convexDual xStar) := sorry

-- Proof sketch: specialize the polyhedral attainment clause (a) of `Theorem_31_4` to the orthant
-- cone. After identifying the sign-twisted dual cone with the orthant again, the dual minimizer
-- lies in the same nonnegative orthant as in the source statement.
/-- Under the primal qualification `∃ x ∈ riDom[𝕜](f), x ≥ 0`, the infimum of `f⋆` over the
nonnegative orthant is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_nonnegativeOrthant_of_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((riDom[𝕜](f) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    ∃ xStar ∈ orthant, IsMinOn convexDual orthant xStar := sorry

-- Proof sketch: specialize the polyhedral attainment clause (b) of `Theorem_31_4` to the orthant
-- cone. The orthant is self-dual up to the chapter sign convention, so the primal minimizer is
-- exactly a point of the nonnegative orthant.
/-- Under the dual qualification `∃ x⋆ ∈ riDom[𝕜](f⋆), x⋆ ≥ 0`, the infimum of `f` over the
nonnegative orthant is attained. -/
theorem exists_mem_isMinOn_on_nonnegativeOrthant_of_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((riDom[𝕜](convexDual) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    ∃ x ∈ orthant, IsMinOn f orthant x := sorry

-- Proof sketch: specialize the orthant instance of `Theorem_31_4`'s optimality criterion. The
-- feasibility conditions are `x ∈ orthant` and `x⋆ ∈ orthant`; `mem_nonnegativeOrthant_iff`
-- recovers the coordinatewise nonnegativity reading, and the self-dual orthant specialization
-- turns complementary slackness into the coordinatewise relations `x i * xStar i = 0`.
/-- The orthant specialization of Fenchel optimality: the two orthant infima are negatives of one
another and are attained at `x` and `x⋆` exactly when `x⋆ ∈ ∂[(ι → 𝕜)]f(x)` and the
coordinates of `x` and `x⋆` satisfy nonnegativity and complementary slackness. -/
theorem optimalValue_pair_iff_mem_subdifferential_and_nonnegative_coordinate_complementarity
    (hf : IsClosedProperConvex[𝕜] f)
    (x xStar : ι → 𝕜) :
    IsMinOn f orthant x ∧
      IsMinOn convexDual orthant xStar ∧
      f x = -(convexDual xStar) ↔
      xStar ∈ ∂[(ι → 𝕜)]f(x) ∧
        x ∈ orthant ∧
          xStar ∈ orthant ∧
            ∀ i : ι, x i * xStar i = (0 : 𝕜) := sorry

end

/-! ### Corollary_31_4_2 (from Chap06) -/
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

/-! ### Corollary_31_4_3 (from Chap06) -/
noncomputable section

open scoped Pointwise PolarCone Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜] [HasContinuousPairing E EStar 𝕜]
variable {h : E → 𝕜} {K : Set E}

local notation "hStar" => (((h.toWithBotTop)⋆ : EStar → WithBotTop 𝕜))
local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.4.3 is the translated Fenchel-duality identity over a closed convex
  cone, together with attainment of the two translated infima.
- `core/canonical`: the existing owner theorem is
  `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` from `Theorem_31_4`,
  together with its two attainment companions, the Chapter 3 co-finiteness owner
  `Function.IsCofinite`, the paired-duality finiteness bridge
  `convexConjugate_finite_everywhere_iff_isCofinite`, the canonical Fenchel conjugate owner
  `hStar : EStar → WithBotTop 𝕜`.
- `bridge/view`: the source dual cone `K*` is rendered by the reusable Chapter 14 bridge
  `K∗[𝕜] : Set EStar`.

Domain-style sampling used here:

- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification`,
  `exists_mem_isMinOn_convexConjugate_on_dualCone_of_primal_qualification`, and
  `exists_mem_isMinOn_on_cone_of_dual_qualification` from `Theorem_31_4`;
- `convexConjugate_finite_everywhere_iff_isCofinite` from `Corollary_13_3_1`;
- the project owners `Function.IsCofinite`, `convexConjugate`, and the cone-polar notation `Kᵒ`.

Primitive data vs derived API:

- primitive inputs: the finite scalar-valued function `h`, the canonical Chapter 3 owner
  `h.toWithBotTop.IsCofinite` encoding the closed/proper/convex and recession data used
  downstream, a closed convex cone `K`, and translation data `z : E`, `zStar : EStar`;
- derived API: the translated zero-gap identity and the two attainment clauses. The source's
  printed right-hand side `⟨z, x*⟩` is treated as the evident bound-variable typo and rendered as
  `⟪z, zStar⟫ₚ`.

Layer target: `source-facing`, stated directly on the translated primal and dual objectives rather
than introducing a local wrapper around Theorem 31.4.
-/

-- Proof sketch: apply Theorem 31.4 to the translated-tilted closed proper convex function
-- `f x = h (z + x) - ⟪x, zStar⟫ₚ`, whose effective domain is all of `E` because `h` is finite.
-- Corollary 13.3.1 turns co-finiteness of `h` into finiteness of `hStar` everywhere on the paired
-- dual carrier `EStar`, so the translated cone problem satisfies the required qualification. The
-- translated conjugate is
-- then rewritten by the existing bridge `convexConjugate_translate_sub_pairing`, with the
-- constant term moved to the right-hand side.
/-- Corollary 31.4.3: for a finite convex function `h` on a finite-dimensional normed space over
`𝕜`,
paired with a dual carrier `EStar`, whose canonical Chapter 3 lift `h.toWithBotTop` is
co-finite, and a nonempty closed convex cone `K`, the translated primal infimum over `K` plus
the translated dual infimum over `K∗[𝕜]` equals `⟪z, zStar⟫ₚ`. This corrects the evident
bound-variable typo in the source display, whose right-hand side should read `⟨z, z*⟩`. -/
theorem iInf_translate_sub_pairing_on_cone_add_iInf_translate_sub_pairing_on_dualCone_eq_pairing
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    (⨅ x : K, (((h (z + x) - ⟪x, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜))) +
        (⨅ xStar : (K∗[𝕜] : Set EStar),
          hStar (zStar + xStar) - ⟪z, (xStar : EStar)⟫ₚ) =
      (⟪z, zStar⟫ₚ : WithBotTop 𝕜) := sorry

-- Proof sketch: the dual relative-interior qualification in Theorem 31.4 is automatic because the
-- translated conjugate is finite everywhere by the Chapter 3 co-finiteness bridge, so
-- `riDom(f⋆) = Set.univ`; since `0 ∈ K∗[𝕜]`, the source dual cone is a nonempty convex cone and
-- therefore has nonempty intrinsic interior. Rewriting the dual minimizer for the conjugate of
-- the translated-tilted function gives the stated minimizer of the translated dual objective, so
-- no separate `K.Nonempty` binder is part of the public API.
/-- The translated dual infimum in Corollary 31.4.3 is attained on `K∗[𝕜]`. -/
theorem exists_mem_isMinOn_convexConjugate_translate_sub_pairing_on_dualCone
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar),
      IsMinOn
        (fun xStar : EStar ↦ hStar (zStar + xStar) - ⟪z, xStar⟫ₚ)
        (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: co-finiteness of `h` makes `hStar` finite everywhere, so the dual
-- relative-interior qualification in Theorem 31.4 is automatic for the translated-tilted
-- function `x ↦ h (z + x) - ⟪x, zStar⟫ₚ`. The primal attainment conclusion of Theorem 31.4
-- therefore yields a minimizer of the translated primal objective on `K`.
/-- The translated primal infimum in Corollary 31.4.3 is attained on `K`. -/
theorem exists_mem_isMinOn_translate_sub_pairing_on_cone
    (hcof : IsCofinite[𝕜] h.toWithBotTop)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (z : E) (zStar : EStar) :
    ∃ x ∈ K,
      IsMinOn (fun x : E ↦ (((h (z + x) - ⟪x, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜))) K x := sorry

end

/-! ### Remark_31_4_3 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

local instance : HasPairing X Y (WithTopBot 𝕜) := instHasPairingWithTopBot

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_withTopBot_eq_coe (x : X) (y : Y) :
    (⟪x, y⟫ₚ : WithTopBot 𝕜) = ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) := rfl

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_neg_left (x : X) (y : Y) :
    (⟪-x, y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ := by
  simp [HasLinearPairing.pairing_eq_pairingLinear]

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_neg_right (x : X) (y : Y) :
    (⟪x, -y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ := by
  simp [HasLinearPairing.pairing_eq_pairingLinear]

/-!
Source/core/bridge triage:

- `source-facing`: Remark 31.4.3 introduces the translated-tilted function
  `x ↦ h (z + x) - ⟪x, z⋆⟫` and records the explicit formula for its Fenchel conjugate.
- `core/canonical`: the owner abstraction is the chapter affine-change theorem
  `convexConjugate_affineChange`, built on the pairing owner
  `HasLinearPairing`.
- `bridge/view`: this file keeps only the single source-facing combined formula as a specialization
  of that owner, without adding a second translated-duality wrapper. The later finite-valued
  duality specialization is delegated to the downstream corollary item.

Domain-style sampling used here:

- `convexConjugate`;
- `convexConjugate_eq_iSup_pairing_sub`;
- `convexConjugate_affineChange`;
- `convexConjugate_sub_pairing_const`.

Primitive data vs derived API:

- primitive inputs: the canonical `WithTopBot 𝕜`-valued function `h`, the primal translation
  vector `z`, and the dual shift vector `zStar`;
- owner-side primitive data already upstream: the affine-change conjugate owner and the linear
  pairing structure;
- derived API: the single explicit conjugate formula for the translated-tilted function. The
  pairing additivity used in the specialization is now derived from `HasLinearPairing`, not stored
  as primitive public data.

Layer target: `bridge/view`.
-/

-- Proof sketch: specialize the chapter affine-change owner with both bijections equal to
-- the identity, translation parameter `a = -z`, dual affine term `aStar = -zStar`, and zero
-- constant term. The pairing-side additivity and negation identities are discharged canonically
-- from `HasLinearPairing`.
/-- Remark 31.4.3: for the translated-tilted function `x ↦ h (z + x) - ⟪x, zStar⟫ₚ`, the
Fenchel conjugate is `xStar ↦ h⋆ (zStar + xStar) - ⟪z, xStar⟫ₚ - ⟪z, zStar⟫ₚ`. This is the
function-theoretic bridge used by the later finite-valued duality specialization. -/
theorem convexConjugate_translate_sub_pairing
    (h : X → WithTopBot 𝕜) (z : X) (zStar : Y) :
    (fun x : X ↦ h (z + x) - ⟪x, zStar⟫ₚ)⋆ =
      fun xStar : Y ↦ h⋆ (zStar + xStar) - ⟪z, xStar⟫ₚ - ⟪z, zStar⟫ₚ := by
  simpa [HasLinearPairing.pairing_eq_pairingLinear, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (-z) (-zStar) (0 : WithTopBot 𝕜))

end

/-! ### Remark_31_4_4 (from Chap06) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 31.4.4 points out three application classes for the Chapter 31.4 value
  formulas: partially affine orthant models, partially quadratic orthant models, and Tucker
  representable pairing-orthogonal subspace pairs.
- `core/canonical`: the owner theorems are already
  `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and
  `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification`, together with the
  source-facing owners `ConvexCone.positive`, `Function.toWithBotTopOn`,
  `Function.IsPartiallyQuadratic`, and
  `AffineSubspace.IsTuckerRepresentable` for the model classes mentioned in the remark.
- `bridge/view`: this remark contributes no new mathematical data beyond those existing owners, so
  the canonical refinement is to recall them directly instead of keeping three parallel local
  wrapper theorems with redundant hypotheses.

Primary mathematical domain:
- finite-dimensional Fenchel duality applications on the nonnegative orthant and on
  pairing-orthogonal subspace pairs.

Domain-style sampling used here:
- `ConvexCone.positive` from `Chap01.Definition_2_5_11`;
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `AffineSubspace.IsTuckerRepresentable` from `Chap01.Text_1_13`;
- `Function.IsPartiallyQuadratic` from `Chap03.Text_12_3_3`;
- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification` and
  `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification` from
  `Chap06.Theorem_31_4` and `Chap06.Corollary_31_4_2`.

Primitive data vs derived API:
- primitive source-facing model owners: `Function.toWithBotTopOn`, `Function.IsPartiallyQuadratic`,
  `AffineSubspace.IsTuckerRepresentable`, and the canonical orthant owner `ConvexCone.positive`;
- derived API: the orthant and subspace value identities already owned by the Chapter 31.4 cone
  theorem and its subspace specialization.

Layer target: `bridge/view`. The remark is an application note pointing back to existing owner
theorems, not a source-facing owner of new theorem statements.
-/

/- Remark 31.4.4(1): the partially affine model mentioned in the remark is already expressed by
the canonical support-cut owner `Function.toWithBotTopOn`, while the orthant value formula sits on
the core cone-duality owner theorem specialized to the canonical orthant `ConvexCone.positive`. -/
recall Function.toWithBotTopOn
recall ConvexCone.positive
recall iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification

/- Remark 31.4.4(2): the partially quadratic model is already owned by
`Function.IsPartiallyQuadratic`, while the value identity is the same orthant specialization of the
core cone-duality theorem recalled above. -/
recall Function.IsPartiallyQuadratic
#check iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification

/- Remark 31.4.4(3): the Tucker-representable subspace hypothesis is already owned by
`AffineSubspace.IsTuckerRepresentable`, and the corresponding subspace value formula is the
existing Chapter 31.4 subspace corollary. -/
recall AffineSubspace.IsTuckerRepresentable
recall iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification

/-! ### Theorem_31_4 (from Chap06) -/
noncomputable section

open scoped Pointwise PolarCone Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type (max u v)}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜]
variable {f : E → WithBotTop 𝕜} {K : Set E}

local notation "ri(" C ")" => intrinsicInterior 𝕜 C
local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "convexDual" => (f⋆ : EStar → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 31.4 is Fenchel duality for minimization over a closed convex cone,
  together with the branchwise attainment conclusions, the polyhedral weakening of the
  qualifications, and the equality-case criterion.
- `core/canonical`: the relevant project owners are the paired-duality ambient
  `HasLinearPairing E EStar 𝕜`, `Function.IsClosedProperConvex`, the Fenchel conjugate owner
  `convexConjugate` with notation `f⋆ : EStar → WithBotTop 𝕜`, Rockafellar's
  effective-domain notation `riDom[𝕜](·)`, the source-facing polar-cone notation
  `Kᵒ[𝕜] : Set EStar`, `Set.IsPolyhedral`, `IsMinOn`, and the Chapter 23 pairing-valued
  subgradient owner `_root_.subdifferentialAt`, exposed here through the notation
  `∂[EStar]f(x)`.
- `bridge/view`: the source dual cone `K* = {x* | ⟪x, x*⟫ ≥ 0 for all x ∈ K}` is the reusable
  Chapter 14 bridge `K∗[𝕜]`, defined there as the sign-twisted polar cone `-Kᵒ`.

Domain-style sampling used here:

- `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification`,
  `exists_isMaxOn_concaveConjugate_sub_convexConjugate_of_riDom_inter_nonempty`, and
  `exists_isMinOn_sub_of_dual_riDom_inter_nonempty` from `Theorem_31_1`;
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone` from `Theorem_14_1`;
- `Set.IsPolyhedral.isClosed_of_finiteDimensional` from `Definition_2_1_2`;
- `_root_.subdifferentialAt` and the notation `∂[Y]f(x)` from `Definition_23_0_6`.

Primitive data vs derived API:

- primitive inputs: the paired primal/dual ambient `E × EStar`, the closed proper convex
  function `f`, the cone `K`, and the qualification conditions on `riDom[𝕜](f)` and
  `riDom[𝕜](f⋆)` relative to `K` and the source dual cone `K∗[𝕜]`;
- derived API: the zero-duality-gap identity for the infima of `f` on `K` and of `f⋆` on
  `K∗[𝕜]`, the branchwise attainment statements in owner form `IsMinOn`, the polyhedral
  weakening of the qualification hypotheses, and the equality-case criterion expressed through
  the pairing-level subgradient owner plus the direct complementary-slackness conjunction.

Layer target: `source-facing`. The theorem remains directly about minimization of `f` over `K`
and of `f⋆` over the source dual cone `K∗[𝕜]`, rather than being repackaged as a new local
structure.
-/

-- Proof sketch: apply Theorem 31.1 to `g = -δ[𝕜](· | K)`. Theorem 14.1 identifies the convex
-- conjugate of `δ[𝕜](· | K)` with `δ[𝕜](· | Kᵒ)`, so the concave conjugate of `g` is the
-- negative indicator of the source dual cone `K∗[𝕜]`.
/-- Theorem 31.4: if `f` is closed proper convex and `K` is a nonempty closed convex cone, then
`inf_K f` equals the negative of `inf_{K∗[𝕜]} f⋆` whenever either `riDom[𝕜](f)` meets `ri(K)` or
`riDom[𝕜](f⋆)` meets `ri(K∗[𝕜])`. -/
theorem iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (hqual :
      Set.Nonempty (riDom[𝕜](f) ∩ ri(K)) ∨
        Set.Nonempty (riDom[𝕜](convexDual) ∩ ri(K∗[𝕜]))) :
    (⨅ x : K, f x) = -(⨅ xStar : (K∗[𝕜] : Set EStar), convexDual xStar) := sorry

-- Proof sketch: specialize the attainment clause (a) of Theorem 31.1 to
-- `g = -δ[𝕜](· | K)`, then rewrite the dual objective by the same sign-twisted indicator
-- identity used in the main theorem.
/-- Under the primal relative-interior qualification, the infimum of `f⋆` over `K∗[𝕜]`
is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_dualCone_of_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK : Set.IsConvexCone 𝕜 K)
    (hqual : Set.Nonempty (riDom[𝕜](f) ∩ ri(K))) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar), IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: specialize the attainment clause (b) of Theorem 31.1 to the indicator-cone
-- choice `g = -δ[𝕜](· | K)`. After rewriting the primal objective as the restriction of `f` to
-- `K`, the resulting minimizer is exactly a point of `K` attaining the infimum of `f` there.
/-- Under the dual relative-interior qualification, the infimum of `f` over `K` is attained. -/
theorem exists_mem_isMinOn_on_cone_of_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (hqual : Set.Nonempty (riDom[𝕜](convexDual) ∩ ri(K∗[𝕜]))) :
    ∃ x ∈ K, IsMinOn f K x := sorry

-- Proof sketch: apply the Chapter 31 equality-case criterion for the indicator-cone perturbation
-- `g = -δ[𝕜](· | K)` on the pairing-level dual carrier.
/-- The attainment form of the optimality criterion in Theorem 31.4 is equivalent to the source
subgradient, dual-feasibility, and complementary-slackness conditions. -/
theorem optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (x : E) (xStar : EStar) :
    IsMinOn f K x ∧
      IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar ∧
      f x = -convexDual xStar ↔
      xStar ∈ ∂[EStar]f(x) ∧
        x ∈ K ∧ xStar ∈ (K∗[𝕜] : Set EStar) ∧ ⟪x, xStar⟫ₚ = (0 : 𝕜) := sorry

section

variable [CompleteSpace 𝕜]

-- Proof sketch: for a polyhedral cone, the relative interior conditions in Theorem 31.4 may be
-- replaced by ordinary membership on the cone side and on the source-dual-cone side.
/-- If `K` is polyhedral, the qualification clauses in Theorem 31.4 may be weakened by replacing
`ri(K)` and `ri(K∗[𝕜])` with `K` and `K∗[𝕜]`. -/
theorem iInf_on_cone_eq_neg_iInf_on_dualCone_of_polyhedral_fenchel_cone_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual :
      Set.Nonempty (riDom[𝕜](f) ∩ K) ∨
        Set.Nonempty (riDom[𝕜](convexDual) ∩ K∗[𝕜])) :
    (⨅ x : K, f x) = -(⨅ xStar : (K∗[𝕜] : Set EStar), convexDual xStar) := sorry

-- Proof sketch: use the same polyhedral weakening of clause (a), then apply the dual-attainment
-- argument above. Closedness of `K` is derived from `hK_poly.isClosed_of_finiteDimensional`.
/-- If `K` is polyhedral and `riDom[𝕜](f)` meets `K`, then the infimum of `f⋆` over `K∗[𝕜]`
is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_dualCone_of_polyhedral_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual : Set.Nonempty (riDom[𝕜](f) ∩ K)) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar), IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: use the polyhedral weakening of clause (b), then repeat the primal-attainment
-- specialization of Theorem 31.1 for the indicator-cone perturbation.
/-- If `K` is polyhedral and `riDom[𝕜](f⋆)` meets `K∗[𝕜]`, then the infimum of `f` over `K`
is attained. -/
theorem exists_mem_isMinOn_on_cone_of_polyhedral_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual : Set.Nonempty (riDom[𝕜](convexDual) ∩ K∗[𝕜])) :
    ∃ x ∈ K, IsMinOn f K x := sorry

end

end

/-! ### Lemma_31_4_5 (from Chap06) -/
open scoped BigOperators PolarCone Rockafellar

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]
variable {f : ι → 𝕜 → WithBotTop 𝕜}
variable {L : Submodule 𝕜 (ι → 𝕜)}
local notation "IsClosedProperConvex[𝕜]" => @Function.IsClosedProperConvex 𝕜
local notation "separableObjective" =>
  (separableCoordinateSum f : (ι → 𝕜) → WithBotTop 𝕜)
local notation "separableDualObjective" =>
  ((separableObjective)⋆ : (ι → 𝕜) → WithBotTop 𝕜)
local notation "Ldual" => (Lᗮₚ : Submodule 𝕜 (ι → 𝕜))

/- Domain-style sampling:
- `separableCoordinateSum` and
  `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate` from `Text_16_0_4`;
- `iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification` and
  `optimalValue_pair_iff_mem_subdifferential_on_subspace` from `Corollary_31_4_2`;
- the pairing-level subspace-duality surfaces `Lᗮₚ` and
  `∂[(ι → 𝕜)]` from the existing owner layer.

Layer target: `bridge/view`.
-/

/-- The subspace-duality value formula for a separable closed proper convex objective, written in
the source coordinatewise form `x ↦ ∑ i, fᵢ(xᵢ)`, with dual value owned intrinsically by
`(separableObjective)⋆`. -/
theorem iInf_on_subspace_eq_neg_iInf_on_orthogonal_of_separable_qualification
    (hf : IsClosedProperConvex[𝕜] separableObjective)
    (hqual :
      ((L : Set (ι → 𝕜)) ∩ riDom[𝕜](separableObjective)).Nonempty ∨
        ((Ldual : Set (ι → 𝕜)) ∩ riDom[𝕜](separableDualObjective)).Nonempty) :
    (⨅ x : L, separableObjective x) =
      -(⨅ xStar : Ldual, separableDualObjective xStar) := by
  exact iInf_on_subspace_eq_neg_iInf_on_pairingOrthogonal_of_fenchel_qualification
      (𝕜 := 𝕜) (E := (ι → 𝕜)) (EStar := (ι → 𝕜))
      (f := separableObjective) (L := L) hf hqual

/-- The Kuhn--Tucker criterion for the separable subspace problem. Primal and dual optimality are
equivalent to primal feasibility, dual feasibility, and intrinsic subdifferential membership of the
separable objective. -/
theorem optimalValue_pair_iff_mem_subdifferential_on_subspace_for_separableObjective
    (hf : IsClosedProperConvex[𝕜] separableObjective)
    (x xStar : ι → 𝕜) :
    IsMinOn separableObjective (L : Set (ι → 𝕜)) x ∧
      IsMinOn separableDualObjective (Ldual : Set (ι → 𝕜)) xStar ∧
      separableObjective x = -separableDualObjective xStar ↔
        x ∈ L ∧
          xStar ∈ Ldual ∧
            xStar ∈ ∂[(ι → 𝕜)]separableObjective(x) := by
  exact optimalValue_pair_iff_mem_subdifferential_on_subspace
      (𝕜 := 𝕜) (E := (ι → 𝕜)) (EStar := (ι → 𝕜))
      (f := separableObjective) (L := L) hf x xStar

/- Lemma 31.4.5, clause (1): the coordinatewise conjugacy statement is already the canonical owner
theorem `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate`. -/
#check convexConjugate_separableCoordinateSum_eq_sum_convexConjugate

end
