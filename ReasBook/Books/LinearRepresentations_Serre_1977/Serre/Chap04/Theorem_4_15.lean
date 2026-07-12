import LinearRepresentations_Serre_1977.Chap04.Definition_4_12
import LinearRepresentations_Serre_1977.Chap04.Lemma_4_22
import LinearRepresentations_Serre_1977.Chap04.Proposition_4_18
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_13
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace Representation

/- Source/core/bridge triage:
- `source-facing`: Theorem 4-15 is the compact-group character orthogonality formula for the
  normalized-Haar pairing `(characterL2 ρ | characterL2 σ)_G`.
- `core/canonical`: the finite-group analogue is `Representation.char_orthonormal`, but Chapter 4
  needs the compact-group `L²(G)` owner `Representation.characterL2`.
- `bridge/view`: the explicit-equivalence, self-pairing, and nonisomorphic-vanishing statements
  are companion APIs derived from the delta formula below.
-/

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

-- Classical decidability is only used to state the source-facing piecewise formula in (3).
attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 4-15: an irreducible representation has nontrivial carrier. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] : Nontrivial V := by
  -- If every vector were equal, then the zero subrepresentation would coincide with the whole
  -- carrier, contradicting irreducibility.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext y
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim y 0)
  exact bot_ne_top hbot

/-- Helper for Theorem 4-15: the character of a finite-dimensional continuous complex
representation of a compact group is continuous. -/
lemma continuous_character_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    Continuous ρ.character := by
  classical
  let ι := Module.Basis.ofVectorSpaceIndex ℂ V
  let b : Module.Basis ι ℂ V := Module.Basis.ofVectorSpace ℂ V
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  have hmat : Continuous fun g : G ↦ LinearMap.toMatrix b b (ρ g) :=
    continuous_toMatrix ρ b
  have hdiag : Continuous fun g : G ↦ ∑ i, LinearMap.toMatrix b b (ρ g) i i := by
    -- The trace is the finite sum of the diagonal coordinate functions of the matrix of `ρ g`.
    refine continuous_finset_sum Finset.univ fun i _ ↦ ?_
    exact (_root_.continuous_apply i).comp ((_root_.continuous_apply i).comp hmat)
  have hchar : (fun g : G ↦ ∑ i, LinearMap.toMatrix b b (ρ g) i i) = ρ.character := by
    -- Rewrite the character as the matrix trace in the chosen basis.
    funext g
    simp [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simpa [hchar] using hdiag

/-- Helper for Theorem 4-15: `ρ.character` viewed as an element of `L²(G)` via the canonical
`ContinuousMap.toLp` map. -/
def characterL2
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    G →₂[(μG : Measure G)] ℂ :=
  (ContinuousMap.toLp 2 μG ℂ)
    ⟨ρ.character, continuous_character_of_isContinuousCompact (ρ := ρ)⟩

/-- Helper for Theorem 4-15: the Chapter 4 pairing of `characterL2 ρ` and `characterL2 σ`
is the normalized-Haar integral of `ρ.character * conj σ.character`. -/
lemma characterL2_pairing_eq_characterIntegral
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : Representation ℂ G W) [Representation.IsContinuous σ] :
    (characterL2 ρ | characterL2 σ)_G = ∫ t, ρ.character t * conj (σ.character t) ∂μG := by
  rw [squareIntegrableFunctionInner_def]
  have hρ : ↑↑(characterL2 ρ) =ᵐ[μG] ρ.character := by
    -- Unfold `characterL2` once and use the canonical `ContinuousMap.toLp` evaluation theorem.
    simpa [Representation.characterL2, continuous_character_of_isContinuousCompact (ρ := ρ)] using
      (ContinuousMap.coeFn_toLp (p := 2) (μ := μG) (𝕜 := ℂ)
        (f := ⟨ρ.character, continuous_character_of_isContinuousCompact (ρ := ρ)⟩))
  have hσ : ↑↑(characterL2 σ) =ᵐ[μG] σ.character := by
    -- The same `toLp` bridge identifies the second character almost everywhere.
    simpa [Representation.characterL2, continuous_character_of_isContinuousCompact (ρ := σ)] using
      (ContinuousMap.coeFn_toLp (p := 2) (μ := μG) (𝕜 := ℂ)
        (f := ⟨σ.character, continuous_character_of_isContinuousCompact (ρ := σ)⟩))
  refine integral_congr_ae ?_
  filter_upwards [hρ, hσ] with t htρ htσ
  simpa using
    show (characterL2 ρ t) * conj (characterL2 σ t) =
        ρ.character t * conj (σ.character t) by
      rw [htρ, htσ]

/-- Helper for Theorem 4-15: in an orthonormal basis, the character is the sum of the diagonal
matrix coefficients. -/
lemma character_eq_sumDiagonalMatrixCoefficient
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G H) (b : OrthonormalBasis ι ℂ H) (t : G) :
    ρ.character t = ∑ i, matrixCoefficient ρ b i i t := by
  -- Rewrite the trace through the matrix of `ρ t` in the orthonormal basis `b`.
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  simp [Matrix.trace, matrixCoefficient, LinearMap.toMatrix_apply]

/-- Helper for Theorem 4-15: a vector-valued map into a finite-dimensional complex space is
continuous once all of its basis coordinates are continuous. -/
lemma continuous_of_continuousBasisCoordinates
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V) (f : G → V)
    (hcoord : ∀ i, Continuous fun g ↦ b.equivFun (f g) i) :
    Continuous f := by
  -- Package the scalar coordinates into a continuous map to `ι → ℂ`, then apply the continuous
  -- inverse of the basis equivalence.
  have htuple : Continuous fun g ↦ b.equivFun (f g) := by
    exact continuous_pi hcoord
  have hback : Continuous b.equivFun.symm := by
    exact b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hcontinuous : Continuous fun g ↦ b.equivFun.symm (b.equivFun (f g)) := by
    exact hback.comp htuple
  simpa using hcontinuous

/-- Helper for Theorem 4-15: continuity of the orbit maps on a basis reconstructs continuity of
the whole action map. -/
lemma isContinuous_of_continuousBasisOrbits
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V)
    (ρ : Representation ℂ G V)
    (horbit : ∀ i, Continuous fun g ↦ ρ g (b i)) :
    Representation.IsContinuous ρ := by
  -- Expand vectors in the basis `b` and combine the continuous basis-orbit maps termwise.
  refine Representation.isContinuous_of_continuousAction ρ ?_
  have hcoord : Continuous fun gv : G × V ↦ b.equivFun gv.2 := by
    exact (continuous_equivFun_basis b).comp continuous_snd
  have hsum :
      Continuous fun gv : G × V ↦ ∑ i, b.equivFun gv.2 i • ρ gv.1 (b i) := by
    refine continuous_finset_sum Finset.univ fun i _ ↦ ?_
    exact ((_root_.continuous_apply i).comp hcoord).smul ((horbit i).comp continuous_fst)
  have hrewrite :
      (fun gv : G × V ↦ ρ gv.1 gv.2) =
        fun gv : G × V ↦ ∑ i, b.equivFun gv.2 i • ρ gv.1 (b i) := by
    funext gv
    exact Representation.action_eq_sum_basis b ρ gv.1 gv.2
  rw [hrewrite]
  exact hsum

/-- Helper for Theorem 4-15: an action preserving the ambient inner product is unitary. -/
lemma isUnitary_of_innerInvariant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Representation ℂ G H)
    (hρ : ∀ t : G, ∀ x y : H, ⟪ρ t x, ρ t y⟫_ℂ = ⟪x, y⟫_ℂ) :
    Representation.IsUnitary ρ := by
  -- Inner-product preservation turns each operator `ρ t` into an isometry.
  refine Representation.isUnitary_of_isometry ρ fun t ↦ ?_
  simpa using ((ρ t).isometryOfInner (hρ t)).isometry

/-- Helper for Theorem 4-15: products of continuous matrix coefficients are integrable on the
compact group `G`. -/
lemma integrable_matrixCoefficient_mul_conj
    {Hπ : Type*} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ] [FiniteDimensional ℂ Hπ]
    {Hσ : Type*} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]
    {ιπ : Type*} [Fintype ιπ] {ισ : Type*} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (i j : ιπ) (k l : ισ) :
    Integrable (fun t ↦ mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t)) μG := by
  -- Each coefficient is continuous, so compactness upgrades their product to an integrable map.
  have hπ_eq :
      (fun t ↦ mc[π, bπ, i, j] t) = fun t ↦ ⟪bπ i, π t (bπ j)⟫_ℂ := by
    funext t
    rw [matrixCoefficient_eq_inner]
  have hσ_eq :
      (fun t ↦ mc[σ, bσ, k, l] t) = fun t ↦ ⟪bσ k, σ t (bσ l)⟫_ℂ := by
    funext t
    rw [matrixCoefficient_eq_inner]
  have hπcont : Continuous fun t ↦ mc[π, bπ, i, j] t := by
    rw [hπ_eq]
    exact (innerSL ℂ (bπ i)).continuous.comp (Representation.continuous_apply π (bπ j))
  have hσcont : Continuous fun t ↦ mc[σ, bσ, k, l] t := by
    rw [hσ_eq]
    exact (innerSL ℂ (bσ k)).continuous.comp (Representation.continuous_apply σ (bσ l))
  have hIntOn :
      IntegrableOn (fun t ↦ mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t)) Set.univ μG :=
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
      ((hπcont.mul (Complex.continuous_conj.comp hσcont)).continuousOn)
  simpa [MeasureTheory.integrableOn_univ] using hIntOn

/-- Helper for Theorem 4-15: distinct irreducible continuous unitary characters are orthogonal in
the Chapter 4 pairing. -/
lemma characterPairing_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact_unitary
    {Hπ : Type*} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ] [FiniteDimensional ℂ Hπ]
    {Hσ : Type*} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary σ]
    (hπσ : ¬ Nonempty (π.Equiv σ)) :
    (characterL2 π | characterL2 σ)_G = 0 := by
  classical
  let bπ : OrthonormalBasis (Fin (Module.finrank ℂ Hπ)) ℂ Hπ := stdOrthonormalBasis ℂ Hπ
  let bσ : OrthonormalBasis (Fin (Module.finrank ℂ Hσ)) ℂ Hσ := stdOrthonormalBasis ℂ Hσ
  -- Rewrite the character pairing as a double sum of matrix-coefficient integrals.
  rw [Representation.characterL2_pairing_eq_characterIntegral]
  calc
    ∫ t, π.character t * conj (σ.character t) ∂μG
      = ∫ t, (∑ i, mc[π, bπ, i, i] t) * conj (∑ k, mc[σ, bσ, k, k] t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [Representation.character_eq_sumDiagonalMatrixCoefficient π bπ]
          rw [Representation.character_eq_sumDiagonalMatrixCoefficient σ bσ]
    ∫ t, (∑ i, mc[π, bπ, i, i] t) * conj (∑ k, mc[σ, bσ, k, k] t) ∂μG
      = ∫ t, ∑ i, ∑ k, mc[π, bπ, i, i] t * conj (mc[σ, bσ, k, k] t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            (∑ i, mc[π, bπ, i, i] t) * conj (∑ k, mc[σ, bσ, k, k] t)
              = ∑ k, (∑ i, mc[π, bπ, i, i] t) * conj (mc[σ, bσ, k, k] t) := by
                  simp_rw [map_sum]
                  rw [Finset.mul_sum]
            _ = ∑ k, ∑ i, mc[π, bπ, i, i] t * conj (mc[σ, bσ, k, k] t) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _
                  rw [Finset.sum_mul]
            _ = ∑ i, ∑ k, mc[π, bπ, i, i] t * conj (mc[σ, bσ, k, k] t) := by
                  rw [Finset.sum_comm]
    _ = ∑ i, ∫ t, ∑ k, mc[π, bπ, i, i] t * conj (mc[σ, bσ, k, k] t) ∂μG := by
          rw [integral_finset_sum Finset.univ]
          intro i _
          exact integrable_finset_sum Finset.univ fun k _ =>
            integrable_matrixCoefficient_mul_conj π σ bπ bσ i i k k
    _ = ∑ i, ∑ k, ∫ t, mc[π, bπ, i, i] t * conj (mc[σ, bσ, k, k] t) ∂μG := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [integral_finset_sum Finset.univ]
          intro k _
          exact integrable_matrixCoefficient_mul_conj π σ bπ bσ i i k k
    _ = ∑ i, ∑ k, (0 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa using
            Representation.matrixCoefficientIntegral_eq_zero_of_not_isomorphic
              π σ bπ bσ i i k k hπσ
    _ = 0 := by
          simp

/-- Helper for Theorem 4-15: the diagonal Kronecker sum in the unitary self-pairing proof
collapses to `1`. -/
private lemma characterPairingSelfDiagonalCollapse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [Nontrivial H] :
    ∑ i : Fin (Module.finrank ℂ H), ∑ k : Fin (Module.finrank ℂ H),
      (Module.finrank ℂ H : ℂ)⁻¹ * (if i = k then 1 else 0) * (if i = k then 1 else 0) = 1 := by
  have hfin_nat : 0 < Module.finrank ℂ H := Module.finrank_pos
  have hfin : (Module.finrank ℂ H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfin_nat)
  -- Only the diagonal terms survive the inner Kronecker sum.
  calc
    ∑ i : Fin (Module.finrank ℂ H), ∑ k : Fin (Module.finrank ℂ H),
        (Module.finrank ℂ H : ℂ)⁻¹ * (if i = k then 1 else 0) * (if i = k then 1 else 0)
      = ∑ i : Fin (Module.finrank ℂ H), (Module.finrank ℂ H : ℂ)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp
    _ = (Module.finrank ℂ H : ℂ) * (Module.finrank ℂ H : ℂ)⁻¹ := by
          simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
    _ = 1 := by
          exact mul_inv_cancel₀ hfin

/-- Helper for Theorem 4-15: an irreducible continuous unitary character has norm `1` in the
Chapter 4 pairing. -/
lemma characterPairing_self_eq_one_of_isIrreducible_of_isContinuousCompact_unitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π] :
    (characterL2 π | characterL2 π)_G = 1 := by
  classical
  letI : Nontrivial H := nontrivial_of_isIrreducible (ρ := π)
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  -- Expand the character pairing into the double diagonal matrix-coefficient sum.
  rw [Representation.characterL2_pairing_eq_characterIntegral]
  calc
    ∫ t, π.character t * conj (π.character t) ∂μG
      = ∫ t, (∑ i, mc[π, b, i, i] t) * conj (∑ k, mc[π, b, k, k] t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [Representation.character_eq_sumDiagonalMatrixCoefficient π b]
    _ = ∫ t, ∑ i, ∑ k, mc[π, b, i, i] t * conj (mc[π, b, k, k] t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            (∑ i, mc[π, b, i, i] t) * conj (∑ k, mc[π, b, k, k] t)
              = ∑ k, (∑ i, mc[π, b, i, i] t) * conj (mc[π, b, k, k] t) := by
                  simp_rw [map_sum]
                  rw [Finset.mul_sum]
            _ = ∑ k, ∑ i, mc[π, b, i, i] t * conj (mc[π, b, k, k] t) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _
                  rw [Finset.sum_mul]
            _ = ∑ i, ∑ k, mc[π, b, i, i] t * conj (mc[π, b, k, k] t) := by
                  rw [Finset.sum_comm]
    _ = ∑ i, ∫ t, ∑ k, mc[π, b, i, i] t * conj (mc[π, b, k, k] t) ∂μG := by
          rw [integral_finset_sum Finset.univ]
          intro i _
          exact integrable_finset_sum Finset.univ fun k _ =>
            integrable_matrixCoefficient_mul_conj π π b b i i k k
    _ = ∑ i, ∑ k, ∫ t, mc[π, b, i, i] t * conj (mc[π, b, k, k] t) ∂μG := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [integral_finset_sum Finset.univ]
          intro k _
          exact integrable_matrixCoefficient_mul_conj π π b b i i k k
    _ = ∑ i, ∑ k,
          (Module.finrank ℂ H : ℂ)⁻¹ * (if i = k then 1 else 0) * (if i = k then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa using
            Representation.matrixCoefficientIntegral_eq_inv_finrank_mul_kronecker π b i i k k
    _ = 1 := by
          exact characterPairingSelfDiagonalCollapse (H := H)

/-- Helper for Theorem 4-15: the unitary self-orthogonality theorem rewritten on the integral
surface. -/
private lemma characterIntegral_self_eq_one_of_isIrreducible_of_isContinuousCompact_unitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π] :
    ∫ t, π.character t * conj (π.character t) ∂μG = 1 := by
  -- This is exactly the unitary self-pairing theorem after unfolding the Chapter 4 pairing.
  rw [← Representation.characterL2_pairing_eq_characterIntegral]
  exact Representation.characterPairing_self_eq_one_of_isIrreducible_of_isContinuousCompact_unitary
    π

/-- Helper for Theorem 4-15: the unitary nonisomorphic orthogonality theorem rewritten on the
integral surface. -/
private lemma characterIntegral_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact_unitary
    {Hπ : Type*} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ] [FiniteDimensional ℂ Hπ]
    {Hσ : Type*} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary σ]
    (hπσ : ¬ Nonempty (π.Equiv σ)) :
    ∫ t, π.character t * conj (σ.character t) ∂μG = 0 := by
  -- This is exactly the unitary nonisomorphic pairing theorem after unfolding the pairing.
  rw [← Representation.characterL2_pairing_eq_characterIntegral]
  exact
    Representation.characterPairing_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact_unitary
      π σ hπσ

/-- Helper for Theorem 4-15: the averaged inner product upgrades an irreducible continuous
representation to a unitary model without changing the self-pairing statement. -/
private lemma characterPairing_self_eq_one_via_averagedModel
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ] :
    (characterL2 ρ | characterL2 ρ)_G = 1 := by
  classical
  -- Route correction: rewrite to the character integral first, then rebuild the averaged-model
  -- instances only for an alias living entirely in the new inner-product world.
  rw [Representation.characterL2_pairing_eq_characterIntegral]
  let ι := Module.Basis.ofVectorSpaceIndex ℂ V
  let b : Module.Basis ι ℂ V := Module.Basis.ofVectorSpace ℂ V
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  have hcoord : ∀ i j, Continuous fun g ↦ b.equivFun (ρ g (b j)) i := by
    -- Cache the scalar coordinate continuities before changing the local structure on `V`.
    intro i j
    exact (_root_.continuous_apply i).comp
      ((continuous_equivFun_basis b).comp (Representation.continuous_apply ρ (b j)))
  let core : InnerProductSpace.Core ℂ V := innerProductCoreOfAveragedCoordinateHermitian b ρ
  letI : InnerProductSpace.Core ℂ V := core
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    { toNormedSpace := inferInstance
      toInner := ⟨averagedCoordinateHermitian b ρ⟩
      norm_sq_eq_re_inner := by
        intro x
        simpa [pow_two] using
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℂ) (F := V) x).symm
      conj_inner_symm := averagedCoordinateHermitian_conjSymm b ρ
      add_left := averagedCoordinateHermitian_add_left b ρ
      smul_left := fun x y r ↦ averagedCoordinateHermitian_smul_left b ρ r x y }
  let topV : TopologicalSpace V := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace V := topV
  letI : IsTopologicalAddGroup V := inferInstance
  letI : ContinuousSMul ℂ V := inferInstance
  letI : T2Space V := inferInstance
  let ρavg : Representation ℂ G V := ρ
  have horbit : ∀ j, Continuous fun g ↦ ρavg g (b j) := by
    -- Reassemble continuity of the averaged-model orbit maps from the saved coordinates.
    intro j
    refine Representation.continuous_of_continuousBasisCoordinates b
      (fun g ↦ ρavg g (b j)) ?_
    intro i
    simpa [ρavg] using hcoord i j
  have hρavg_cont : Representation.IsContinuous ρavg := by
    -- The alias is continuous in the averaged topology because each basis orbit is.
    exact Representation.isContinuous_of_continuousBasisOrbits b ρavg horbit
  letI : Representation.IsContinuous ρavg := hρavg_cont
  have hρavg_irred : Representation.IsIrreducible ρavg := by
    -- Irreducibility is unchanged under the definitional alias `ρavg := ρ`.
    simpa [ρavg] using (inferInstance : Representation.IsIrreducible ρ)
  letI : Representation.IsIrreducible ρavg := hρavg_irred
  have hρavg_inner : ∀ s : G, ∀ x y : V, ⟪ρavg s x, ρavg s y⟫_ℂ = ⟪x, y⟫_ℂ := by
    -- The averaged Hermitian form is `G`-invariant, so it is the local inner product.
    intro s x y
    simpa [ρavg] using averagedCoordinateHermitian_invariant b ρ s x y
  have hρavg_unitary : Representation.IsUnitary ρavg := by
    -- Inner-product invariance upgrades the averaged model to a unitary representation.
    exact Representation.isUnitary_of_innerInvariant ρavg hρavg_inner
  letI : Representation.IsUnitary ρavg := hρavg_unitary
  have hselfavg : ∫ t, ρavg.character t * conj (ρavg.character t) ∂μG = 1 :=
    @Representation.characterIntegral_self_eq_one_of_isIrreducible_of_isContinuousCompact_unitary
      G _ _ _ _ _ _ V _ _ _ ρavg hρavg_cont hρavg_irred hρavg_unitary
  -- The integral statement is already proved for continuous irreducible unitary models.
  simpa [ρavg] using hselfavg

/-- Helper for Theorem 4-15: after averaging the inner products on both carriers, the
nonisomorphic branch reduces to the already proved unitary orthogonality lemma. -/
private lemma characterPairing_eq_zero_of_not_isomorphic_via_averagedModels
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    (hρσ : ¬ Nonempty (ρ.Equiv σ)) :
    (characterL2 ρ | characterL2 σ)_G = 0 := by
  classical
  -- Route correction: rewrite to the integral surface first, then move entirely into theorem-local
  -- averaged aliases instead of calling matrix-coefficient lemmas across transported structures.
  rw [Representation.characterL2_pairing_eq_characterIntegral]
  let ιV := Module.Basis.ofVectorSpaceIndex ℂ V
  let bV : Module.Basis ιV ℂ V := Module.Basis.ofVectorSpace ℂ V
  letI : Fintype ιV := Fintype.ofFinite ιV
  letI : DecidableEq ιV := Classical.decEq ιV
  have hcoordV : ∀ i j, Continuous fun g ↦ bV.equivFun (ρ g (bV j)) i := by
    -- Save the scalar coordinate continuities for `ρ` before replacing the local structure on `V`.
    intro i j
    exact (_root_.continuous_apply i).comp
      ((continuous_equivFun_basis bV).comp (Representation.continuous_apply ρ (bV j)))
  let ιW := Module.Basis.ofVectorSpaceIndex ℂ W
  let bW : Module.Basis ιW ℂ W := Module.Basis.ofVectorSpace ℂ W
  letI : Fintype ιW := Fintype.ofFinite ιW
  letI : DecidableEq ιW := Classical.decEq ιW
  have hcoordW : ∀ i j, Continuous fun g ↦ bW.equivFun (σ g (bW j)) i := by
    -- Save the scalar coordinate continuities for `σ` before replacing the local structure on `W`.
    intro i j
    exact (_root_.continuous_apply i).comp
      ((continuous_equivFun_basis bW).comp (Representation.continuous_apply σ (bW j)))
  let coreV : InnerProductSpace.Core ℂ V := innerProductCoreOfAveragedCoordinateHermitian bV ρ
  letI : InnerProductSpace.Core ℂ V := coreV
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    { toNormedSpace := inferInstance
      toInner := ⟨averagedCoordinateHermitian bV ρ⟩
      norm_sq_eq_re_inner := by
        intro x
        simpa [pow_two] using
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℂ) (F := V) x).symm
      conj_inner_symm := averagedCoordinateHermitian_conjSymm bV ρ
      add_left := averagedCoordinateHermitian_add_left bV ρ
      smul_left := fun x y r ↦ averagedCoordinateHermitian_smul_left bV ρ r x y }
  let coreW : InnerProductSpace.Core ℂ W := innerProductCoreOfAveragedCoordinateHermitian bW σ
  letI : InnerProductSpace.Core ℂ W := coreW
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ W := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ W :=
    { toNormedSpace := inferInstance
      toInner := ⟨averagedCoordinateHermitian bW σ⟩
      norm_sq_eq_re_inner := by
        intro x
        simpa [pow_two] using
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℂ) (F := W) x).symm
      conj_inner_symm := averagedCoordinateHermitian_conjSymm bW σ
      add_left := averagedCoordinateHermitian_add_left bW σ
      smul_left := fun x y r ↦ averagedCoordinateHermitian_smul_left bW σ r x y }
  let topV : TopologicalSpace V := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace V := topV
  letI : IsTopologicalAddGroup V := inferInstance
  letI : ContinuousSMul ℂ V := inferInstance
  letI : T2Space V := inferInstance
  let topW : TopologicalSpace W := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : TopologicalSpace W := topW
  letI : IsTopologicalAddGroup W := inferInstance
  letI : ContinuousSMul ℂ W := inferInstance
  letI : T2Space W := inferInstance
  let ρavg : Representation ℂ G V := ρ
  let σavg : Representation ℂ G W := σ
  have hρavg_orbit : ∀ j, Continuous fun g ↦ ρavg g (bV j) := by
    -- Rebuild continuity of the averaged-model `ρ`-orbits from the cached basis coordinates.
    intro j
    refine Representation.continuous_of_continuousBasisCoordinates bV
      (fun g ↦ ρavg g (bV j)) ?_
    intro i
    simpa [ρavg] using hcoordV i j
  have hρavg_cont : Representation.IsContinuous ρavg := by
    -- Each basis orbit for `ρavg` is continuous, so the full action is continuous.
    exact Representation.isContinuous_of_continuousBasisOrbits bV ρavg hρavg_orbit
  letI : Representation.IsContinuous ρavg := hρavg_cont
  have hρavg_irred : Representation.IsIrreducible ρavg := by
    -- Irreducibility is unchanged under the alias `ρavg := ρ`.
    simpa [ρavg] using (inferInstance : Representation.IsIrreducible ρ)
  letI : Representation.IsIrreducible ρavg := hρavg_irred
  have hρavg_inner : ∀ s : G, ∀ x y : V, ⟪ρavg s x, ρavg s y⟫_ℂ = ⟪x, y⟫_ℂ := by
    -- The averaged Hermitian form on `V` is `G`-invariant.
    intro s x y
    simpa [ρavg] using averagedCoordinateHermitian_invariant bV ρ s x y
  have hρavg_unitary : Representation.IsUnitary ρavg := by
    -- `ρavg` is unitary for the averaged inner product.
    exact Representation.isUnitary_of_innerInvariant ρavg hρavg_inner
  letI : Representation.IsUnitary ρavg := hρavg_unitary
  have hσavg_orbit : ∀ j, Continuous fun g ↦ σavg g (bW j) := by
    -- Rebuild continuity of the averaged-model `σ`-orbits from the cached basis coordinates.
    intro j
    refine Representation.continuous_of_continuousBasisCoordinates bW
      (fun g ↦ σavg g (bW j)) ?_
    intro i
    simpa [σavg] using hcoordW i j
  have hσavg_cont : Representation.IsContinuous σavg := by
    -- Each basis orbit for `σavg` is continuous, so the full action is continuous.
    exact Representation.isContinuous_of_continuousBasisOrbits bW σavg hσavg_orbit
  letI : Representation.IsContinuous σavg := hσavg_cont
  have hσavg_irred : Representation.IsIrreducible σavg := by
    -- Irreducibility is unchanged under the alias `σavg := σ`.
    simpa [σavg] using (inferInstance : Representation.IsIrreducible σ)
  letI : Representation.IsIrreducible σavg := hσavg_irred
  have hσavg_inner : ∀ s : G, ∀ x y : W, ⟪σavg s x, σavg s y⟫_ℂ = ⟪x, y⟫_ℂ := by
    -- The averaged Hermitian form on `W` is `G`-invariant.
    intro s x y
    simpa [σavg] using averagedCoordinateHermitian_invariant bW σ s x y
  have hσavg_unitary : Representation.IsUnitary σavg := by
    -- `σavg` is unitary for the averaged inner product.
    exact Representation.isUnitary_of_innerInvariant σavg hσavg_inner
  letI : Representation.IsUnitary σavg := hσavg_unitary
  have hρσ' : ¬ Nonempty (ρavg.Equiv σavg) := by
    -- Nonisomorphism transports directly across the theorem-local aliases.
    simpa [ρavg, σavg] using hρσ
  have hpairavg : ∫ t, ρavg.character t * conj (σavg.character t) ∂μG = 0 :=
    @Representation.characterIntegral_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact_unitary
      G _ _ _ _ _ _ V _ _ _ W _ _ _ ρavg hρavg_cont hρavg_irred hρavg_unitary
      σavg hσavg_cont hσavg_irred hσavg_unitary hρσ'
  -- The unitary averaged models now satisfy the already proved integral orthogonality theorem.
  simpa [ρavg, σavg] using hpairavg

/-- Theorem 4-15 (3): equivalently, for irreducible finite-dimensional continuous complex
representations `ρ` and `σ` of a compact group, the normalized-Haar character pairing is `1`
when `ρ ≃ σ` and `0` otherwise. -/
theorem characterPairing_eq_ite_of_isIrreducible_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W) [Representation.IsContinuous σ] [Representation.IsIrreducible σ] :
    (characterL2 ρ | characterL2 σ)_G = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  -- Route correction: the finite-group theorem `Representation.char_orthonormal` is not the
  -- right owner here; the compact proof has to run through `characterL2` and Lemma 4-22.
  by_cases hρσ : Nonempty (ρ.Equiv σ)
  · rcases hρσ with ⟨e⟩
    have hself : (characterL2 ρ | characterL2 ρ)_G = 1 :=
      characterPairing_self_eq_one_via_averagedModel ρ
    -- Rewrite the isomorphic branch to the self-pairing statement via `Representation.char_iso`.
    rw [Representation.characterL2_pairing_eq_characterIntegral] at hself ⊢
    simpa [if_pos (show Nonempty (ρ.Equiv σ) from ⟨e⟩), Representation.char_iso e] using hself
  · -- The nonisomorphic branch is already packaged on the original theorem surface.
    simpa [if_neg hρσ] using
      characterPairing_eq_zero_of_not_isomorphic_via_averagedModels ρ σ hρσ

/-- Companion to Theorem 4-15: equivalent irreducible finite-dimensional continuous complex
representations of a compact group have character pairing `1`. -/
theorem characterPairing_eq_one_of_equiv_of_isIrreducible_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    (e : ρ.Equiv σ) :
    (characterL2 ρ | characterL2 σ)_G = 1 := by
  let hρσ : Nonempty (ρ.Equiv σ) := ⟨e⟩
  simpa [if_pos hρσ] using
    characterPairing_eq_ite_of_isIrreducible_of_isContinuousCompact ρ σ

/-- Theorem 4-15 (1): if `ρ` is an irreducible finite-dimensional continuous complex
representation of a compact group, then the normalized-Haar pairing of its character with itself
is `1`; equivalently, `(χ | χ)_G = 1`. -/
theorem characterPairing_self_eq_one_of_isIrreducible_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ] :
    (characterL2 ρ | characterL2 ρ)_G = 1 := by
  simpa using
    characterPairing_eq_one_of_equiv_of_isIrreducible_of_isContinuousCompact
      ρ ρ (Representation.Equiv.refl _)

/-- Theorem 4-15 (2): if `ρ` and `σ` are nonisomorphic irreducible finite-dimensional continuous
complex representations of a compact group, then the normalized-Haar pairing of their characters
is `0`; equivalently, `(χ | χ')_G = 0`. -/
theorem characterPairing_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (σ : Representation ℂ G W) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    (hρσ : ¬ Nonempty (ρ.Equiv σ)) :
    (characterL2 ρ | characterL2 σ)_G = 0 := by
  simpa [if_neg hρσ] using
    characterPairing_eq_ite_of_isIrreducible_of_isContinuousCompact ρ σ

end

end Representation
