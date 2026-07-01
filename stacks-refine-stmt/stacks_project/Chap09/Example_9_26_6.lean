import Mathlib
import stacks_project.Chap09.Example_9_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open Cardinal
open IntermediateField.AdjoinPair
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

section

/- Domain-style sampling for Example 9.26.6:
- primary domain: transcendence degree of finitely generated field extensions;
- sampled owner declarations:
  `Algebra.trdeg`,
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`,
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `IntermediateField.AdjoinPair.gen₁` / `IntermediateField.AdjoinPair.gen₂`;
- best owner abstraction: the transcendence-degree owner `Algebra.trdeg` of the intermediate field
  `ℚ⟮Real.exp 1, Real.pi⟯`.

Primitive data are the two generators `Real.exp 1` and `Real.pi` and the intermediate field they
generate. The `Fin 2` family in `K` is only bridge/view API into the canonical owner
`IsTranscendenceBasis` and the resulting invariant `Algebra.trdeg`.

Source/core/bridge triage:
- `source-facing`: the concrete field `ℚ(e, π)` and the question whether its transcendence degree
  is `1` or `2`;
- `core/canonical`: `Algebra.trdeg ℚ K`;
- `bridge/view`: the two-generator family in `K`, used only to invoke
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic` and then
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`;
- `layer`: `source-facing`.
-/

local notation "K" => ℚ⟮Real.exp 1, Real.pi⟯

-- Proof sketch: exhibit a transcendental element of `K` over `ℚ` and then apply the canonical
-- owner lemma `trdeg_pos`, converting `0 < Algebra.trdeg ℚ K` into the equivalent lower bound
-- `1 ≤ Algebra.trdeg ℚ K`.
/-- Example 9.26.6: the field `ℚ(e, π)` has transcendence degree at least `1` over `ℚ`. -/
theorem rat_e_pi_field_trdeg_one_le :
    1 ≤ Algebra.trdeg ℚ K := by
  let πK : K := gen₂ ℚ (Real.exp 1) Real.pi
  have hπK : Transcendental ℚ πK := by
    rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective K ℝ)]
    simpa [πK] using real_pi_transcendental
  haveI : Algebra.Transcendental ℚ K := ⟨⟨πK, hπK⟩⟩
  simpa [Cardinal.one_le_iff_pos] using (trdeg_pos ℚ K)

-- Proof sketch: transport algebraic independence of `![Real.exp 1, Real.pi]` to the canonical
-- two-generator family in `K`, show that `K` is algebraic over the intermediate field generated
-- by that family, and conclude that this family is a transcendence basis. The equality
-- `Algebra.trdeg ℚ K = 2` is then the canonical basis-cardinality formula
-- `IsTranscendenceBasis.cardinalMk_eq_trdeg`.
/-- If `e` and `π` are algebraically independent over `ℚ`, then `ℚ(e, π)` has transcendence
degree `2` over `ℚ`. -/
theorem rat_e_pi_field_trdeg_eq_two_of_algebraicIndependent
    (h_alg : AlgebraicIndependent ℚ (![Real.exp 1, Real.pi] : Fin 2 → ℝ)) :
    Algebra.trdeg ℚ K = 2 := by
  let x : Fin 2 → K :=
    ![gen₁ ℚ (Real.exp 1) Real.pi, gen₂ ℚ (Real.exp 1) Real.pi]
  have hx_ind : AlgebraicIndependent ℚ x := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom ℚ K ℝ)
    convert h_alg using 1
    ext i
    fin_cases i
    · simpa [x] using (AdjoinPair.algebraMap_gen₁ ℚ (Real.exp 1) Real.pi : _)
    · simpa [x] using (AdjoinPair.algebraMap_gen₂ ℚ (Real.exp 1) Real.pi : _)
  have hx_top : IntermediateField.adjoin ℚ (Set.range x) = (⊤ : IntermediateField ℚ K) := by
    let L : IntermediateField ℚ ℝ := K
    apply IntermediateField.lift_injective L
    have hx_image : Subtype.val '' Set.range x = ({Real.exp 1, Real.pi} : Set ℝ) := by
      ext z
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨x 0, ⟨0, rfl⟩, rfl⟩
        · exact ⟨x 1, ⟨1, rfl⟩, rfl⟩
    calc
      IntermediateField.lift (IntermediateField.adjoin ℚ (Set.range x)) = L := by
        rw [IntermediateField.lift_adjoin, hx_image]
      _ = IntermediateField.lift (⊤ : IntermediateField ℚ K) := by
        ext z
        constructor
        · intro hz
          let zL : L := ⟨z, hz⟩
          exact (IntermediateField.mem_lift zL).2 (by trivial)
        · rintro ⟨zL, -, rfl⟩
          exact zL.2
  have hK_alg_if : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range x)) K := by
    rw [hx_top, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  have hK_alg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range x)) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp hK_alg_if
  have hbasis : IsTranscendenceBasis ℚ x :=
    hx_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hK_alg
  simpa using hbasis.cardinalMk_eq_trdeg.symm

/- Stacks Example 9.26.6 also records the meta-mathematical third point: it is currently unknown
whether `e` and `π` are algebraically independent over `ℚ`, so the exact value of
`Algebra.trdeg ℚ ℚ⟮Real.exp 1, Real.pi⟯` remains an open problem. -/

end
