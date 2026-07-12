import Mathlib
import StacksProject_2024.Chap04.Definition_4_22_1
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Lemma_13_33_5
import StacksProject_2024.Chap13.Lemma_13_33_6
import StacksProject_2024.Chap13.Lemma_13_33_7
import StacksProject_2024.Chap13.Definition_13_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Example 13.41.2:
- primary domain: the brutal left-truncation tower in `CochainComplex 𝒜 ℤ` and its induced
  Postnikov-style stage triangles in `D(𝒜)` for a bounded-above complex
  `(... ⟶ A₂ ⟶ A₁ ⟶ A₀ ⟶ 0 ⟶ ...)`;
- inspected owner declarations:
  `CochainComplex.IsStrictlyLE`,
  `CochainComplex.minus`,
  `HomologicalComplex.stupidTrunc`,
  `HomologicalComplex.stupidTruncXIso`,
  `PostnikovSystem`,
  `termwise_colimit_is_homotopy_colimit`;
- best owner abstraction:
  the primitive owner is the cochain complex `K` itself, because the brutal truncation stages,
  their transition maps, the sequential tower, and the finite row `Xₙ ⟶ ⋯ ⟶ X₀` are canonical
  for every `K`. The bounded-above hypothesis `[K.IsStrictlyLE 0]` belongs only to the theorem
  layer where those primitive constructions are identified with the source finite-stage picture.
  The core truncation engine is still the canonical mathlib owner
  `HomologicalComplex.stupidTrunc`, while the finite-row packaging is handled by the chapter
  owner `PostnikovSystem`, and the infinite `hocolim` statement is owned by the Chapter `13`
  telescope theorem `termwise_colimit_is_homotopy_colimit`;
- primitive-vs-derived split:
  primitive data: the source complex `K`, the brutal finite stage complexes `Yₙ[n]`, the stage
    maps `Yₙ[n] ⟶ Yₙ₊₁[n + 1]`, the projections `Yₙ[n] ⟶ Aₙ[-n]`, and the induced derived-stage
    objects `Yₙ` and `Xₙ`;
  derived API: the stage triangles and comparison maps in `D(𝒜)`, the finite `PostnikovSystem`
    bridge on the row `Xₙ ⟶ ⋯ ⟶ X₀`, and the homotopy colimit theorem for the shifted tower
    `Y₀ ⟶ Y₁[1] ⟶ Y₂[2] ⟶ ⋯`, with `[K.IsStrictlyLE 0]` imposed only where the bounded-above
    source interpretation is used.

Source/core/bridge triage:
- source-facing:
  `boundedAbovePostnikovX`,
  `boundedAbovePostnikovY`,
  `boundedAbovePostnikovXMap`,
  `boundedAboveTermSequence`,
  `boundedAbovePostnikovToX`,
  `boundedAbovePostnikovToNext`,
  `boundedAbovePostnikovConnecting`,
  `boundedAbovePostnikovToX_zero_isIso`,
  `boundedAbovePostnikov_distinguished`,
  `boundedAbovePostnikov_comp`,
  `boundedAboveTermSequencePostnikovSystem`;
- core/canonical:
  `CochainComplex.IsStrictlyLE`,
  `CochainComplex.minus`,
  `HomologicalComplex.stupidTrunc`,
  `PostnikovSystem`,
  `IsHomotopyColimitOf`;
-- bridge/view:
  `brutalLeftTruncationStage`,
  `brutalLeftTruncationStep`,
  `brutalLeftTruncationTower`,
  `brutalLeftTruncationColimitComparison`,
  `brutalLeftTruncationColimitComparison_isIso`,
  `brutalLeftTruncation_isHomotopyColimitOf`,
  the left-to-right `Fin (n + 1)` reindexing used to present the source family `Yₙ, …, Y₀`
  as the auxiliary-object function of a finite `PostnikovSystem`,
  together with the internal single-complex, stage-triangle, and colimit-comparison bridges used
  to build the finite `PostnikovSystem` and the sequential colimit comparison. -/

private abbrev boundedAboveTermIndex (n : ℕ) (i : Fin (n + 1)) : ℕ :=
  n - i.1

private theorem boundedAboveTermIndex_succ_add_one
    (n : ℕ) (i : Fin n) :
    boundedAboveTermIndex n i.succ + 1 = boundedAboveTermIndex n i.castSucc := by
  dsimp [boundedAboveTermIndex]
  omega

variable (K : CochainComplex 𝒜 ℤ)

section

/-- The `n`th stage of the brutal left-truncation tower of `K`, starting in degree `-n`. Under
`[K.IsStrictlyLE 0]`, its nonzero degrees are `-n, …, 0`, so it is the source complex `Y_n[n]`. -/
abbrev brutalLeftTruncationStage (n : ℕ) :
    CochainComplex 𝒜 ℤ :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ)))

/-- The single cochain complex with `A_n` in degree `-n`, representing the source term `X_n`
before shifting it to degree `0`. -/
private noncomputable abbrev boundedAbovePostnikovXComplex (n : ℕ) :
    CochainComplex 𝒜 ℤ :=
  (CochainComplex.singleFunctor 𝒜 (-((n : ℕ) : ℤ))).obj (K.X (-((n : ℕ) : ℤ)))

/-- Helper for Example 13.41.2: the canonical index in the brutal left-truncation stage whose
image is a retained degree `i`. -/
private theorem brutalLeftTruncation_stage_index_eq (n : ℕ) {i : ℤ}
    (hi : -((n : ℕ) : ℤ) ≤ i) :
    (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))).f (Int.toNat (i + (n : ℤ))) = i := by
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Example 13.41.2: the cutoff degree `-n` belongs to the retained range of the
`n`th brutal left-truncation stage. -/
private theorem brutalLeftTruncation_cutoff_le (n : ℕ) :
    -((n : ℕ) : ℤ) ≤ -((n : ℕ) : ℤ) := by
  simp

/-- Helper for Example 13.41.2: every degree retained by the `n`th brutal left-truncation stage
is also retained by the next stage. -/
private theorem brutalLeftTruncation_next_le (n : ℕ) {i : ℤ}
    (hi : -((n : ℕ) : ℤ) ≤ i) :
    -(((n + 1 : ℕ)) : ℤ) ≤ i := by
  omega

/-- Helper for Example 13.41.2: on every retained degree of the `n`th brutal left-truncation
stage, the stage term identifies with the original term of `K`. -/
private noncomputable abbrev brutalLeftTruncationXIso (n : ℕ) {i : ℤ}
    (hi : -((n : ℕ) : ℤ) ≤ i) :
    (brutalLeftTruncationStage K n).X i ≅ K.X i :=
  K.stupidTruncXIso
    (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ)))
    (brutalLeftTruncation_stage_index_eq (K := K) n hi)

/-- Helper for Example 13.41.2: after identifying retained degrees with the corresponding terms of
`K`, the brutal left-truncation differential agrees with the original differential of `K`. -/
private theorem brutalLeftTruncation_d_via_x_iso
    (n : ℕ) {i j : ℤ}
    (hi : -((n : ℕ) : ℤ) ≤ i) (hj : -((n : ℕ) : ℤ) ≤ j) :
    (brutalLeftTruncationXIso K n hi).inv ≫
      (brutalLeftTruncationStage K n).d i j ≫
      (brutalLeftTruncationXIso K n hj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))
  let i₀ : ℕ := Int.toNat (i + (n : ℤ))
  let j₀ : ℕ := Int.toNat (j + (n : ℤ))
  have hi₀ : e.f i₀ = i := by
    simpa [e, i₀] using brutalLeftTruncation_stage_index_eq (K := K) n hi
  have hj₀ : e.f j₀ = j := by
    simpa [e, j₀] using brutalLeftTruncation_stage_index_eq (K := K) n hj
  -- First peel off the `extend` isomorphisms, then peel off the `restriction` isomorphisms.
  change (brutalLeftTruncationXIso K n hi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (brutalLeftTruncationXIso K n hj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [brutalLeftTruncationStage, brutalLeftTruncationXIso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀,
    hi₀, hj₀]

/-- Helper for Example 13.41.2: the component of the consecutive-stage inclusion in degree `i`. -/
private noncomputable def brutalLeftTruncationStepComponent (n : ℕ) (i : ℤ) :
    (brutalLeftTruncationStage K n).X i ⟶ (brutalLeftTruncationStage K (n + 1)).X i :=
  if hi : -((n : ℕ) : ℤ) ≤ i then
    (brutalLeftTruncationXIso K n hi).hom ≫
      (brutalLeftTruncationXIso K (n + 1) (brutalLeftTruncation_next_le (n := n) hi)).inv
  else
    0

/-- Helper for Example 13.41.2: the degreewise components of the consecutive-stage inclusion
commute with differentials. -/
private theorem brutalLeftTruncationStep_comm
    (n : ℕ) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    brutalLeftTruncationStepComponent K n i ≫ (brutalLeftTruncationStage K (n + 1)).d i j =
      (brutalLeftTruncationStage K n).d i j ≫ brutalLeftTruncationStepComponent K n j := by
  have hij' : i + 1 = j := by
    simpa using hij
  by_cases hi : -((n : ℕ) : ℤ) ≤ i
  · have hj : -((n : ℕ) : ℤ) ≤ j := by
      omega
    have hi' : -(((n + 1 : ℕ)) : ℤ) ≤ i := brutalLeftTruncation_next_le (n := n) hi
    have hj' : -(((n + 1 : ℕ)) : ℤ) ≤ j := brutalLeftTruncation_next_le (n := n) hj
    -- On shared degrees, both stage differentials identify with the differential of `K`.
    apply (cancel_mono (brutalLeftTruncationXIso K (n + 1) hj').hom).1
    apply (cancel_epi (brutalLeftTruncationXIso K n hi).inv).1
    rw [dif_pos hi, dif_pos hj]
    repeat rw [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
    rw [brutalLeftTruncation_d_via_x_iso (K := K) (n := n + 1) hi' hj']
    simpa [Category.assoc] using
      (brutalLeftTruncation_d_via_x_iso (K := K) (n := n) hi hj).symm
  · by_cases hj : -((n : ℕ) : ℤ) ≤ j
    · have hi_lt : i < -((n : ℕ) : ℤ) := by
        omega
      have hzero :
          IsZero ((brutalLeftTruncationStage K n).X i) := by
        exact
          (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) i hi_lt
      -- Below the previous cutoff, the source term is zero, so the square is trivial.
      rw [dif_neg hi, zero_comp, dif_pos hj]
      exact hzero.eq_of_src _ _
    · -- Strictly below the shared range, both components of the inclusion are zero.
      rw [dif_neg hi, dif_neg hj, zero_comp, comp_zero]

/-- Helper for Example 13.41.2: below the old cutoff, the consecutive-stage inclusion vanishes in
degree `i`. -/
private theorem brutalLeftTruncationStep_component_eq_zero
    (n : ℕ) {i : ℤ} (hi : i < -((n : ℕ) : ℤ)) :
    brutalLeftTruncationStepComponent K n i = 0 := by
  -- Outside the retained range, the stage inclusion is zero by definition.
  simp [brutalLeftTruncationStepComponent, not_le_of_gt hi]

/-- Helper for Example 13.41.2: on degrees shared by two consecutive brutal left-truncation
stages, the stage inclusion is transported from the identity on `K.X i`. -/
private theorem brutalLeftTruncationStep_component_eq_iso
    (n : ℕ) {i : ℤ} (hi : -((n : ℕ) : ℤ) ≤ i) :
    brutalLeftTruncationStepComponent K n i =
      (brutalLeftTruncationXIso K n hi).hom ≫
        (brutalLeftTruncationXIso K (n + 1)
          (brutalLeftTruncation_next_le (n := n) hi)).inv := by
  -- On shared degrees, the inclusion is the transported identity.
  simp [brutalLeftTruncationStepComponent, hi]

/-- Helper for Example 13.41.2: the degreewise component of the canonical inclusion from a brutal
left-truncation stage into `K`. -/
private noncomputable def brutalLeftTruncationInclusionComponent (n : ℕ) (i : ℤ) :
    (brutalLeftTruncationStage K n).X i ⟶ K.X i :=
  if hi : -((n : ℕ) : ℤ) ≤ i then
    (brutalLeftTruncationXIso K n hi).hom
  else
    0

/-- Helper for Example 13.41.2: the degreewise components of the canonical inclusion into `K`
commute with differentials. -/
private theorem brutalLeftTruncationInclusion_comm
    (n : ℕ) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    brutalLeftTruncationInclusionComponent K n i ≫ K.d i j =
      (brutalLeftTruncationStage K n).d i j ≫ brutalLeftTruncationInclusionComponent K n j := by
  have hij' : i + 1 = j := by
    simpa using hij
  by_cases hi : -((n : ℕ) : ℤ) ≤ i
  · have hj : -((n : ℕ) : ℤ) ≤ j := by
      omega
    -- On retained degrees, the inclusion is identified with the identity on `K`.
    apply (cancel_epi (brutalLeftTruncationXIso K n hi).inv).1
    rw [dif_pos hi, dif_pos hj]
    repeat rw [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
    exact brutalLeftTruncation_d_via_x_iso (K := K) (n := n) hi hj
  · by_cases hj : -((n : ℕ) : ℤ) ≤ j
    · have hi_lt : i < -((n : ℕ) : ℤ) := by
        omega
      have hzero :
          IsZero ((brutalLeftTruncationStage K n).X i) := by
        exact
          (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) i hi_lt
      -- Below the cutoff, the source term is zero, so the compatibility square is trivial.
      rw [dif_neg hi, zero_comp, dif_pos hj]
      exact hzero.eq_of_src _ _
    · -- Outside the retained range, both components of the inclusion vanish.
      rw [dif_neg hi, dif_neg hj, zero_comp, comp_zero]

/-- Helper for Example 13.41.2: below the cutoff, the canonical inclusion from the brutal
left-truncation stage into `K` vanishes in degree `i`. -/
private theorem brutalLeftTruncationInclusion_component_eq_zero
    (n : ℕ) {i : ℤ} (hi : i < -((n : ℕ) : ℤ)) :
    brutalLeftTruncationInclusionComponent K n i = 0 := by
  -- The stage has no degree-`i` term below the cutoff, so the inclusion is zero there.
  simp [brutalLeftTruncationInclusionComponent, not_le_of_gt hi]

/-- Helper for Example 13.41.2: on retained degrees, the canonical inclusion from the brutal
left-truncation stage into `K` is the canonical stage-term identification. -/
private theorem brutalLeftTruncationInclusion_component_eq_iso
    (n : ℕ) {i : ℤ} (hi : -((n : ℕ) : ℤ) ≤ i) :
    brutalLeftTruncationInclusionComponent K n i =
      (brutalLeftTruncationXIso K n hi).hom := by
  -- On retained degrees, the inclusion is the tautological identification with `K.X i`.
  simp [brutalLeftTruncationInclusionComponent, hi]

/-- Helper for Example 13.41.2: once degree `i` survives in stage `n`, the canonical inclusion of
that stage into `K` is an isomorphism in degree `i`. -/
private theorem brutalLeftTruncationInclusionComponent_isIso
    (n : ℕ) {i : ℤ} (hi : -((n : ℕ) : ℤ) ≤ i) :
    IsIso (brutalLeftTruncationInclusionComponent K n i) := by
  -- On retained degrees, the inclusion is literally the structural stage-term isomorphism.
  rw [brutalLeftTruncationInclusion_component_eq_iso (K := K) (n := n) (i := i) hi]
  infer_instance

/-- Helper for Example 13.41.2: the `mkHomToSingle` side condition for the quotient projection to
the cutoff term. -/
private theorem brutalLeftTruncationToSingle_comm
    (n : ℕ) {i : ℤ} (hi : (ComplexShape.up ℤ).Rel i (-((n : ℕ) : ℤ))) :
    (brutalLeftTruncationStage K n).d i (-((n : ℕ) : ℤ)) ≫
      (brutalLeftTruncationXIso K n (brutalLeftTruncation_cutoff_le n)).hom = 0 := by
  have hi' : i < -((n : ℕ) : ℤ) := by
    have : i + 1 = -((n : ℕ) : ℤ) := by
      simpa using hi
    omega
  have hzero :
      IsZero ((brutalLeftTruncationStage K n).X i) := by
    exact
      (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
        (-((n : ℕ) : ℤ)) i hi'
  -- The boundary source lies below the cutoff, so the projection condition is automatic.
  exact hzero.eq_of_src _ _

/-- The canonical projection
`Y_n[n] ⟶ A_n[-n]`
onto the leftmost term of the brutal left-truncation stage. -/
private noncomputable def brutalLeftTruncationToSingle (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ boundedAbovePostnikovXComplex K n :=
  HomologicalComplex.mkHomToSingle
    ((brutalLeftTruncationXIso K n (brutalLeftTruncation_cutoff_le n)).hom)
    (brutalLeftTruncationToSingle_comm (K := K) n)

/-- Helper for Example 13.41.2: away from the cutoff degree `-n`, the projection from the brutal
left-truncation stage to the single complex vanishes. -/
private theorem brutalLeftTruncationToSingle_component_eq_zero
    (n : ℕ) {i : ℤ} (hi : i ≠ -((n : ℕ) : ℤ)) :
    (brutalLeftTruncationToSingle K n).f i = 0 := by
  -- The single target is supported only at its distinguished degree.
  dsimp [brutalLeftTruncationToSingle, HomologicalComplex.mkHomToSingle]
  split_ifs with h
  · exact (hi h).elim
  · rfl

/-- Helper for Example 13.41.2: at the cutoff degree `-n`, the projection to the single complex is
the canonical stage-term identification followed by the self-iso of the single complex. -/
private theorem brutalLeftTruncationToSingle_component_eq_cutoff
    (n : ℕ) :
    (brutalLeftTruncationToSingle K n).f (-((n : ℕ) : ℤ)) =
      (brutalLeftTruncationXIso K n (brutalLeftTruncation_cutoff_le n)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((n : ℕ) : ℤ))
          (K.X (-((n : ℕ) : ℤ)))).inv := by
  -- Evaluating `mkHomToSingle` at the cutoff returns the defining component.
  simp [brutalLeftTruncationToSingle]

/-- The canonical inclusion
`Y_n[n] ⟶ Y_{n + 1}[n + 1]`
between consecutive brutal left-truncation stages. -/
noncomputable def brutalLeftTruncationStep (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ brutalLeftTruncationStage K (n + 1) where
  f := brutalLeftTruncationStepComponent K n
  comm' := brutalLeftTruncationStep_comm (K := K) n

/-- Helper for Example 13.41.2: the consecutive-stage inclusion followed by the quotient
projection to the new cutoff term vanishes. -/
private theorem brutalLeftTruncationStep_comp_toSingle
    (n : ℕ) :
    brutalLeftTruncationStep K n ≫ brutalLeftTruncationToSingle K (n + 1) = 0 := by
  ext i
  by_cases hi : i = -((n + 1 : ℕ) : ℤ)
  · subst hi
    -- At the new cutoff, the previous stage has no term, so the first component is already zero.
    rw [HomologicalComplex.comp_f,
      brutalLeftTruncationStep_component_eq_zero (K := K) (n := n)
        (i := -((n + 1 : ℕ) : ℤ)) (by omega),
      zero_comp]
    rfl
  · -- Away from the new cutoff, the quotient projection is zero by support reasons.
    rw [HomologicalComplex.comp_f,
      brutalLeftTruncationToSingle_component_eq_zero (K := K) (n := n + 1) (i := i) hi,
      comp_zero]
    rfl

/-- The short exact sequence
`Y_n[n] ⟶ Y_{n + 1}[n + 1] ⟶ A_{n + 1}[-(n + 1)]`
whose quotient is the new leftmost term of the next brutal left-truncation stage. -/
private noncomputable def boundedAbovePostnikovStageShortComplex (n : ℕ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (brutalLeftTruncationStep K n)
    (brutalLeftTruncationToSingle K (n + 1))
    (brutalLeftTruncationStep_comp_toSingle (K := K) n)

/-- Helper for Example 13.41.2: evaluating the stage short complex in any degree yields one of the
canonical split shapes `0 ⟶ 0 ⟶ 0`, `0 ⟶ K.X i ⟶ K.X i`, or `K.X i ⟶ K.X i ⟶ 0`. -/
private noncomputable def boundedAbovePostnikovStageDegreewiseSplitting
    (n : ℕ) (i : ℤ) :
    ((boundedAbovePostnikovStageShortComplex K n).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)).Splitting := by
  let S : ShortComplex 𝒜 :=
    (boundedAbovePostnikovStageShortComplex K n).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  by_cases hi_lt : i < -((n + 1 : ℕ) : ℤ)
  · change S.Splitting
    have hX₁ : IsZero S.X₁ := by
      dsimp [S]
      exact
        (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
          (-((n : ℕ) : ℤ)) i (by omega)
    have hX₂ : IsZero S.X₂ := by
      dsimp [S]
      exact
        (brutalLeftTruncationStage K (n + 1)).isZero_of_isStrictlyGE
          (-((n + 1 : ℕ) : ℤ)) i hi_lt
    have hX₃ : IsZero S.X₃ := by
      dsimp [S, boundedAbovePostnikovXComplex]
      exact
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
          (K.X (-((n + 1 : ℕ) : ℤ))) i (by omega)
    have hg : IsIso S.g := by
      dsimp [S, boundedAbovePostnikovStageShortComplex]
      rw [brutalLeftTruncationToSingle_component_eq_zero (K := K) (n := n + 1)
        (i := i) (by omega)]
      exact hX₂.isIso hX₃ 0
    -- Strictly below the new cutoff, every term in the degreewise short complex is zero.
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · by_cases hi_eq : i = -((n + 1 : ℕ) : ℤ)
    · subst hi_eq
      change S.Splitting
      have hX₁ : IsZero S.X₁ := by
        dsimp [S]
        exact
          (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
      have hg : IsIso S.g := by
        dsimp [S, boundedAbovePostnikovStageShortComplex]
        rw [brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := n + 1)]
        haveI :
            IsIso
              ((brutalLeftTruncationXIso K (n + 1)
                (brutalLeftTruncation_cutoff_le (n + 1))).hom) := by
          infer_instance
        exact IsIso.comp_isIso
      -- At the new cutoff, the short complex is `0 ⟶ K.X i ⟶ K.X i`.
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
    · change S.Splitting
      have hi_ge : -((n : ℕ) : ℤ) ≤ i := by
        omega
      have hX₃ : IsZero S.X₃ := by
        dsimp [S, boundedAbovePostnikovXComplex]
        exact
          HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-((n + 1 : ℕ) : ℤ))
            (K.X (-((n + 1 : ℕ) : ℤ))) i hi_eq
      have hf : IsIso S.f := by
        dsimp [S, boundedAbovePostnikovStageShortComplex]
        rw [brutalLeftTruncationStep_component_eq_iso (K := K) (n := n) (i := i) hi_ge]
        infer_instance
      -- Above the new cutoff, the quotient term vanishes and the inclusion is an isomorphism.
      exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃

/-- The stage short complex is short exact. -/
private theorem boundedAbovePostnikovStageShortExact (n : ℕ) :
    (boundedAbovePostnikovStageShortComplex K n).ShortExact := by
  -- Evaluate degreewise and use the canonical splittings in the three cutoff regimes.
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i ↦ (boundedAbovePostnikovStageDegreewiseSplitting (K := K) n i).shortExact)

/-- The sequential tower
`Y_0[0] ⟶ Y_1[1] ⟶ Y_2[2] ⟶ ⋯`
of shifted brutal left-truncation stages. -/
noncomputable abbrev brutalLeftTruncationTower :
    ℕ ⥤ CochainComplex 𝒜 ℤ :=
  Functor.ofSequence (brutalLeftTruncationStep K)

/-- The canonical inclusion of the `n`th brutal left-truncation stage into the source complex
`K`. -/
noncomputable def brutalLeftTruncationInclusion (n : ℕ) :
    brutalLeftTruncationStage K n ⟶ K where
  f := brutalLeftTruncationInclusionComponent K n
  comm' := brutalLeftTruncationInclusion_comm (K := K) n

-- Proof sketch: on each degree, both composites are the identity on the shared source term when
-- that degree lies in the stage `Y_n[n]`, and are zero otherwise.
/-- The tower maps are compatible with the canonical inclusions into the source complex `K`. -/
theorem brutalLeftTruncationStep_comp_inclusion (n : ℕ) :
    brutalLeftTruncationStep K n ≫ brutalLeftTruncationInclusion K (n + 1) =
      brutalLeftTruncationInclusion K n := by
  ext i
  by_cases hi : -((n : ℕ) : ℤ) ≤ i
  · -- On retained degrees, both composites are the same transported identity on `K.X i`.
    rw [HomologicalComplex.comp_f,
      brutalLeftTruncationStep_component_eq_iso (K := K) (n := n) (i := i) hi,
      brutalLeftTruncationInclusion_component_eq_iso (K := K) (n := n + 1) (i := i)
        (brutalLeftTruncation_next_le (n := n) hi),
      brutalLeftTruncationInclusion_component_eq_iso (K := K) (n := n) (i := i) hi]
    simp [Category.assoc]
  · have hi_lt : i < -((n : ℕ) : ℤ) := by
      omega
    -- Below the cutoff, both morphisms vanish because the source stage term is zero.
    rw [HomologicalComplex.comp_f,
      brutalLeftTruncationStep_component_eq_zero (K := K) (n := n) (i := i) hi_lt,
      zero_comp,
      brutalLeftTruncationInclusion_component_eq_zero (K := K) (n := n) (i := i) hi_lt]
    rfl

/-- The canonical cocone from the brutal-stage tower to the source complex `K`. -/
private noncomputable def brutalLeftTruncationCocone :
    Cocone (brutalLeftTruncationTower K) where
  pt := K
  ι := NatTrans.ofSequence
    (fun n ↦ brutalLeftTruncationInclusion K n)
    (fun n ↦ by
      simpa [brutalLeftTruncationTower] using
        brutalLeftTruncationStep_comp_inclusion K n)

/-- Helper for Example 13.41.2: evaluating the brutal left-truncation cocone in degree `i` gives
the cocone whose legs are the degree-`i` stage inclusions. -/
private noncomputable def brutalLeftTruncationEvalCocone (i : ℤ) :
    Cocone (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) :=
  (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i).mapCocone (brutalLeftTruncationCocone K)

/-- Helper for Example 13.41.2: the `n`th leg of the evaluated brutal left-truncation cocone is
the degree-`i` component of the stage inclusion into `K`. -/
@[simp] private theorem brutalLeftTruncationEvalCocone_ι_app
    (i : ℤ) (n : ℕ) :
    (brutalLeftTruncationEvalCocone K i).ι.app n =
      brutalLeftTruncationInclusionComponent K n i := by
  rfl

section

variable [HasColimitsOfShape ℕ 𝒜]

/-- The canonical map from the sequential colimit of the brutal left-truncation tower to the
source complex `K`. -/
noncomputable def brutalLeftTruncationColimitComparison :
    colimit (brutalLeftTruncationTower K) ⟶ K :=
  colimit.desc (brutalLeftTruncationTower K) (brutalLeftTruncationCocone K)

/-- Helper for Example 13.41.2: evaluating the colimit of the brutal left-truncation tower at a
fixed degree agrees with the colimit of the evaluated tower. -/
private noncomputable def brutalLeftTruncationEvalColimitIso (i : ℤ) :
    colimit (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) ≅
      (colimit (brutalLeftTruncationTower K)).X i :=
  ((isColimitOfPreserves (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
      (colimit.isColimit (brutalLeftTruncationTower K))).coconePointUniqueUpToIso
    (colimit.isColimit
      (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))).symm

/-- Helper for Example 13.41.2: on each cocone leg, the evaluated-colimit comparison is the
degree-`i` component of the complex-level colimit cocone map. -/
private theorem brutalLeftTruncation_eval_colimit_iso_hom_ι
    (i : ℤ) (n : ℕ) :
    colimit.ι
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) n ≫
          (brutalLeftTruncationEvalColimitIso (K := K) i).hom =
      (colimit.ι (brutalLeftTruncationTower K) n).f i := by
  let e :
      (colimit (brutalLeftTruncationTower K)).X i ≅
        colimit (brutalLeftTruncationTower K ⋙
          HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) :=
    (isColimitOfPreserves (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
      (colimit.isColimit (brutalLeftTruncationTower K))).coconePointUniqueUpToIso
        (colimit.isColimit
          (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfPreserves (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
        (colimit.isColimit (brutalLeftTruncationTower K)))
      (colimit.isColimit
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)) n
  -- Compose the universal cocone-leg formula with the inverse comparison to expose the component.
  simpa [brutalLeftTruncationEvalColimitIso, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Example 13.41.2: the complex-level colimit comparison evaluates on each cocone leg
to the canonical inclusion of that stage into `K`. -/
private theorem brutalLeftTruncationColimitComparison_f_ι
    (n : ℕ) (i : ℤ) :
    (colimit.ι (brutalLeftTruncationTower K) n).f i ≫
      (brutalLeftTruncationColimitComparison K).f i =
        brutalLeftTruncationInclusionComponent K n i := by
  -- This is just the defining cocone equation for `colimit.desc`, read in degree `i`.
  simpa [brutalLeftTruncationColimitComparison, brutalLeftTruncationCocone] using
    congrArg (fun f ↦ f.f i)
      (colimit.ι_desc (brutalLeftTruncationTower K) (brutalLeftTruncationCocone K) n)

/-- Helper for Example 13.41.2: after replacing the complex colimit by the evaluated colimit, the
comparison to `K.X i` is still read off on cocone legs by the stage inclusion component. -/
private theorem brutalLeftTruncation_eval_colimitComparison_hom_ι
    (i : ℤ) (n : ℕ) :
    colimit.ι
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) n ≫
          (brutalLeftTruncationEvalColimitIso (K := K) i).hom ≫
            (brutalLeftTruncationColimitComparison K).f i =
      brutalLeftTruncationInclusionComponent K n i := by
  -- First identify the cocone leg in the evaluated colimit, then use the defining `desc` formula.
  rw [Category.assoc, brutalLeftTruncation_eval_colimit_iso_hom_ι,
    brutalLeftTruncationColimitComparison_f_ι]

/-- Helper for Example 13.41.2: every integer degree appears in some brutal left-truncation
stage. -/
private theorem brutalLeftTruncation_eventual_stage_le (i : ℤ) :
    -((Int.toNat (-i) : ℕ) : ℤ) ≤ i := by
  by_cases hi : 0 ≤ i
  · rw [Int.toNat_of_nonpos (by omega)]
    omega
  · rw [Int.toNat_of_nonneg (by omega)]
    omega

/-- Helper for Example 13.41.2: once stage `n` already contains degree `i`, the evaluated
brutal left-truncation cocone is essentially constant and hence colimiting with value `K.X i`. -/
private theorem brutalLeftTruncation_eval_stabilized_isColimit
    (i : ℤ) (n : ℕ) (hn : -((n : ℕ) : ℤ) ≤ i) :
    IsColimit (brutalLeftTruncationEvalCocone K i) := by
  -- The source route is degreewise stabilization: from stage `n` onward every leg into `K.X i`
  -- is an isomorphism, so the evaluated cocone is essentially constant.
  letI : IsIso ((brutalLeftTruncationEvalCocone K i).ι.app n) := by
    simpa using brutalLeftTruncationInclusionComponent_isIso (K := K) n hn
  refine IsEssentiallyConstantFilteredCocone.isColimit ?_
  refine ⟨n, ⟨(asIso ((brutalLeftTruncationEvalCocone K i).ι.app n)).inv, ?_⟩, ?_⟩
  · simp
  · intro j
    let k := max n j
    letI : IsIso ((brutalLeftTruncationEvalCocone K i).ι.app k) := by
      have hk : -((k : ℕ) : ℤ) ≤ i := by
        dsimp [k]
        omega
      simpa using brutalLeftTruncationInclusionComponent_isIso (K := K) k hk
    refine ⟨k, homOfLE (Nat.le_max_left _ _), homOfLE (Nat.le_max_right _ _), ?_⟩
    -- Postcompose both sides with the stabilized leg at stage `k`; cocone naturality then
    -- reduces the equality to the section-retraction identity at the chosen stable stage.
    apply (cancel_mono ((brutalLeftTruncationEvalCocone K i).ι.app k)).1
    rw [Category.assoc]
    have hjk :
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i).map
            (homOfLE (Nat.le_max_right n j)) ≫
          (brutalLeftTruncationEvalCocone K i).ι.app k =
            (brutalLeftTruncationEvalCocone K i).ι.app j := by
      simpa [k] using
        (brutalLeftTruncationEvalCocone K i).w (homOfLE (Nat.le_max_right n j))
    have hnk :
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i).map
            (homOfLE (Nat.le_max_left n j)) ≫
          (brutalLeftTruncationEvalCocone K i).ι.app k =
            (brutalLeftTruncationEvalCocone K i).ι.app n := by
      simpa [k] using
        (brutalLeftTruncationEvalCocone K i).w (homOfLE (Nat.le_max_left n j))
    rw [hjk, Category.assoc, hnk, Iso.inv_hom_id_assoc]

section

-- Proof sketch: the tower consists of the intrinsic inclusions of the brutal left-truncation stages into
-- one another. Degreewise, every term stabilizes after finitely many stages, so the termwise
-- colimit is exactly the source complex `K`.
/-- The brutal left-truncation tower stabilizes degreewise, so its colimit maps isomorphically to
the source complex `K`. Under `[K.IsStrictlyLE 0]`, this is the source tower
`Y_0[0] ⟶ Y_1[1] ⟶ Y_2[2] ⟶ ⋯` from Example 13.41.2 (3). -/
theorem brutalLeftTruncationColimitComparison_isIso :
    IsIso (brutalLeftTruncationColimitComparison K) := by
  let e :
      ∀ i : ℤ,
        colimit (brutalLeftTruncationTower K ⋙
            HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) ≅
          (colimit (brutalLeftTruncationTower K)).X i :=
    brutalLeftTruncationEvalColimitIso (K := K)
  let hstable :
      ∀ i : ℤ, IsColimit (brutalLeftTruncationEvalCocone K i) := by
    intro i
    exact brutalLeftTruncation_eval_stabilized_isColimit (K := K) i (Int.toNat (-i))
      (brutalLeftTruncation_eventual_stage_le (i := i))
  let d :
      ∀ i : ℤ,
        colimit (brutalLeftTruncationTower K ⋙
            HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) ≅
          K.X i := fun i ↦
    ((hstable i).coconePointUniqueUpToIso
      (colimit.isColimit
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))).symm
  have hdι :
      ∀ i : ℤ, ∀ n : ℕ,
        colimit.ι
            (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) n ≫
              (d i).hom =
          brutalLeftTruncationInclusionComponent K n i := by
    intro i n
    let e' : K.X i ≅
        colimit (brutalLeftTruncationTower K ⋙
          HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) :=
      (hstable i).coconePointUniqueUpToIso
        (colimit.isColimit
          (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))
    have h :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (hstable i)
        (colimit.isColimit
          (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)) n
    -- Read the universal comparison on cocone legs and then move back through the inverse iso.
    simpa [d, e', brutalLeftTruncationEvalCocone] using
      (congrArg (fun f ↦ f ≫ e'.inv) h).symm
  have hcomp :
      ∀ i : ℤ, IsIso ((brutalLeftTruncationColimitComparison K).f i) := by
    intro i
    have heq :
        (e i).hom ≫ (brutalLeftTruncationColimitComparison K).f i =
          (d i).hom := by
      apply (colimit.isColimit
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)).hom_ext
      intro n
      rw [Category.assoc, brutalLeftTruncation_eval_colimitComparison_hom_ι, hdι i n]
    have hf :
        (brutalLeftTruncationColimitComparison K).f i =
          (e i).inv ≫ (d i).hom := by
      apply (cancel_mono (e i).hom).1
      simpa [Category.assoc] using heq
    rw [hf]
    infer_instance
  letI : ∀ i : ℤ, IsIso ((brutalLeftTruncationColimitComparison K).f i) := hcomp
  -- A map of complexes is an isomorphism once all its degreewise components are.
  exact HomologicalComplex.Hom.isIso_of_components (brutalLeftTruncationColimitComparison K)

end

end

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (K : CochainComplex 𝒜 ℤ)

/-- The stage object `X_n = A_n` of the source example, viewed in `D(𝒜)` as an object
concentrated in degree `0`. -/
abbrev boundedAbovePostnikovX (n : ℕ) : DerivedCategory 𝒜 :=
  (DerivedCategory.singleFunctor 𝒜 (0 : ℤ)).obj (K.X (-((n : ℕ) : ℤ)))

/-- The differential map `X_{n + 1} ⟶ X_n` in the source row
`⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀`. -/
abbrev boundedAbovePostnikovXMap (n : ℕ) :
    boundedAbovePostnikovX K (n + 1) ⟶ boundedAbovePostnikovX K n :=
  (DerivedCategory.singleFunctor 𝒜 (0 : ℤ)).map
    (K.d (-((n + 1 : ℕ) : ℤ)) (-((n : ℕ) : ℤ)))

/-- The source stage object
obtained from the brutal truncation stage. Under `[K.IsStrictlyLE 0]`, this is the source stage
object `Y_n = (A_n ⟶ A_{n - 1} ⟶ ⋯ ⟶ A_0)[-n]`, and equivalently `Y_n[n]` is
`brutalLeftTruncationStage K n`. -/
abbrev boundedAbovePostnikovY (n : ℕ) : DerivedCategory 𝒜 :=
  (Q.obj (brutalLeftTruncationStage K n))⟦(-((n : ℕ) : ℤ))⟧

/-- Shifting the single complex `A_n[-n]` by `-n` identifies it with the stage object
`X_n = A_n[0]`. -/
private noncomputable def boundedAbovePostnikovXShiftIso (n : ℕ) :
    (Q.obj (boundedAbovePostnikovXComplex K n))⟦(-((n : ℕ) : ℤ))⟧ ≅
      boundedAbovePostnikovX K n :=
  ((DerivedCategory.singleFunctors 𝒜).shiftIso (-((n : ℕ) : ℤ)) 0
      (-((n : ℕ) : ℤ)) (by simp)).app (K.X (-((n : ℕ) : ℤ)))

/-- The finite row
attached to the terms `A_n, …, A_0` of a cochain complex. Under `[K.IsStrictlyLE 0]`, this is
the finite row appearing in Example 13.41.2. -/
private abbrev boundedAboveTermSequenceMap
    (n : ℕ) (i : Fin n) :
    boundedAbovePostnikovX K (boundedAboveTermIndex n i.castSucc) ⟶
      boundedAbovePostnikovX K (boundedAboveTermIndex n i.succ) :=
  cast
    (by rw [← boundedAboveTermIndex_succ_add_one n i])
    (boundedAbovePostnikovXMap K (boundedAboveTermIndex n i.succ))

def boundedAboveTermSequence (n : ℕ) :
    ComposableArrows (DerivedCategory 𝒜) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ boundedAbovePostnikovX K (boundedAboveTermIndex n i))
    (fun i ↦ boundedAboveTermSequenceMap K n i)

/-- The canonical shifted-and-rotated triangle
`Y_{n + 1} ⟶ A_{n + 1}[0] ⟶ Y_n ⟶ Y_{n + 1}[1]`
attached to consecutive brutal left-truncation stages. -/
private noncomputable def boundedAbovePostnikovStageTriangle (n : ℕ) :
    Triangle (DerivedCategory 𝒜) :=
  (((shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).obj
      (DerivedCategory.triangleOfSES (boundedAbovePostnikovStageShortExact K n))).rotate)

/-- The third object of the shifted-and-rotated stage triangle is canonically `Y_n`. -/
private noncomputable def boundedAbovePostnikovStageTriangleObj3Iso (n : ℕ) :
    (boundedAbovePostnikovStageTriangle K n).obj₃ ≅ boundedAbovePostnikovY K n :=
  ((shiftFunctorAdd' (DerivedCategory 𝒜) (-((n + 1 : ℕ) : ℤ)) (1 : ℤ)
      (-((n : ℕ) : ℤ)) (by omega)).app (Q.obj (brutalLeftTruncationStage K n))).symm

/-- The canonical comparison map `Y_n ⟶ X_n` attached to the brutal left-truncation stage of `K`. -/
noncomputable def boundedAbovePostnikovToX (n : ℕ) :
    boundedAbovePostnikovY K n ⟶ boundedAbovePostnikovX K n :=
  (Q.map (brutalLeftTruncationToSingle K n))⟦(-((n : ℕ) : ℤ))⟧' ≫
    (boundedAbovePostnikovXShiftIso K n).hom

/-- The canonical map `X_{n + 1} ⟶ Y_n` attached to consecutive brutal left-truncation stages
of `K`. -/
noncomputable def boundedAbovePostnikovToNext (n : ℕ) :
    boundedAbovePostnikovX K (n + 1) ⟶ boundedAbovePostnikovY K n :=
  (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
    (boundedAbovePostnikovStageTriangle K n).mor₂ ≫
    (boundedAbovePostnikovStageTriangleObj3Iso K n).hom

/-- The canonical connecting map `Y_n ⟶ Y_{n + 1}[1]` attached to consecutive brutal
left-truncation stages of `K`. -/
noncomputable def boundedAbovePostnikovConnecting (n : ℕ) :
    boundedAbovePostnikovY K n ⟶ (boundedAbovePostnikovY K (n + 1))⟦(1 : ℤ)⟧ :=
  (boundedAbovePostnikovStageTriangleObj3Iso K n).inv ≫
    (boundedAbovePostnikovStageTriangle K n).mor₃

/-- Helper for Example 13.41.2: the shifted-and-rotated triangle of the stage short exact
sequence is exactly the source-facing stage triangle
`Y_{n + 1} ⟶ X_{n + 1} ⟶ Y_n ⟶ Y_{n + 1}[1]`. -/
private noncomputable def boundedAbovePostnikovStageTriangleIso (n : ℕ) :
    boundedAbovePostnikovStageTriangle K n ≅
      Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) := by
  -- Route correction: isolate the stage-triangle identification once, then reuse it for
  -- distinguishedness and the later naturality computation.
  refine Triangle.isoMk _ _
    (Iso.refl _)
    (boundedAbovePostnikovXShiftIso K (n + 1))
    (boundedAbovePostnikovStageTriangleObj3Iso K n)
    ?_ ?_ ?_
  · -- The first edge is the shifted quotient projection to the new cutoff term.
    simp [boundedAbovePostnikovStageTriangle, boundedAbovePostnikovToX]
  · -- The second edge is the rotated middle map rewritten through the chosen object isomorphism.
    simp [boundedAbovePostnikovStageTriangle, boundedAbovePostnikovToNext]
  · -- The third edge is the rotated connecting morphism rewritten through the third-object
    -- identification.
    simp [boundedAbovePostnikovStageTriangle, boundedAbovePostnikovConnecting, Category.assoc]

section

variable [K.IsStrictlyLE 0]

-- Proof sketch: the brutal left-truncation stages and their canonical short exact sequences define the
-- maps `Y_n ⟶ X_n`, `X_{n + 1} ⟶ Y_n`, and `Y_n ⟶ Y_{n + 1}[1]`; the shifted truncation triangles
-- give the distinguished triangles of the infinite Postnikov system, and the composites recover
-- the differentials `X_{n + 1} ⟶ X_n`.

/-- The right end of the canonical bounded-above Postnikov system identifies `Y₀` with `X₀`. -/
theorem boundedAbovePostnikovToX_zero_isIso :
    IsIso (boundedAbovePostnikovToX K 0) := by
  let π := brutalLeftTruncationToSingle K 0
  letI : ∀ i : ℤ, IsIso (π.f i) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      -- At the unique retained degree, the projection is the canonical identification with the
      -- single complex.
      simpa [π] using
        (show IsIso ((brutalLeftTruncationToSingle K 0).f 0) by
          rw [brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := 0)]
          infer_instance)
    · by_cases hi_neg : i < 0
      · have hsrc : IsZero ((brutalLeftTruncationStage K 0).X i) := by
          -- Below degree `0`, the brutal left-truncation stage is zero.
          exact (brutalLeftTruncationStage K 0).isZero_of_isStrictlyGE 0 i hi_neg
        have htgt : IsZero ((boundedAbovePostnikovXComplex K 0).X i) := by
          -- The single complex is supported only at degree `0`.
          simpa [boundedAbovePostnikovXComplex] using
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) (K.X 0) i hi0)
        simpa [π] using IsZero.isIso hsrc htgt ((brutalLeftTruncationToSingle K 0).f i)
      · have hi_pos : 0 < i := by
          omega
        have hsrc : IsZero ((brutalLeftTruncationStage K 0).X i) := by
          -- Above degree `0`, the bounded-above hypothesis forces the stage term to vanish.
          exact (brutalLeftTruncationStage K 0).isZero_of_isStrictlyLE 0 i hi_pos
        have htgt : IsZero ((boundedAbovePostnikovXComplex K 0).X i) := by
          -- The single complex is supported only at degree `0`.
          simpa [boundedAbovePostnikovXComplex] using
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) (K.X 0) i hi0)
        simpa [π] using IsZero.isIso hsrc htgt ((brutalLeftTruncationToSingle K 0).f i)
  letI : IsIso π := HomologicalComplex.Hom.isIso_of_components π
  -- Passing to the derived category and reidentifying the zero shift preserves the isomorphism.
  dsimp [boundedAbovePostnikovToX, π]
  infer_instance

/-- Each stage of the canonical bounded-above Postnikov system is a distinguished triangle. -/
theorem boundedAbovePostnikov_distinguished (n : ℕ) :
    Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) ∈
      distTriang (DerivedCategory 𝒜) := by
  -- Route correction: first identify the shifted-and-rotated short-exact-sequence triangle, then
  -- transport distinguishedness across that fixed identification.
  have hstage :
      boundedAbovePostnikovStageTriangle K n ∈ distTriang (DerivedCategory 𝒜) := by
    -- Shift the canonical short exact sequence triangle, then rotate once.
    dsimp [boundedAbovePostnikovStageTriangle]
    refine rot_of_distTriang _ ?_
    simpa using
      Triangle.shift_distinguished
        (T := DerivedCategory.triangleOfSES (boundedAbovePostnikovStageShortExact K n))
        (hT := DerivedCategory.triangleOfSES_distinguished
          (boundedAbovePostnikovStageShortExact K n))
        (-((n + 1 : ℕ) : ℤ))
  -- The source-facing triangle is the transported stage triangle.
  exact isomorphic_distinguished _ hstage _ (boundedAbovePostnikovStageTriangleIso K n)

/-- Helper for Example 13.41.2: the left degree of the two-term complex encoding the raw
differential `A_{n + 1} ⟶ A_n`. -/
private abbrev boundedAbovePostnikovSingleDifferentialLeftDegree (n : ℕ) : ℤ :=
  -(((n + 1 : ℕ)) : ℤ)

/-- Helper for Example 13.41.2: the right degree of the two-term complex encoding the raw
differential `A_{n + 1} ⟶ A_n`. -/
private abbrev boundedAbovePostnikovSingleDifferentialRightDegree (n : ℕ) : ℤ :=
  -((n : ℕ) : ℤ)

/-- Helper for Example 13.41.2: the left degree of the two-term differential complex is one step
below the right degree. -/
private theorem boundedAbovePostnikovSingleDifferential_left_add_one
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialLeftDegree n + 1 =
      boundedAbovePostnikovSingleDifferentialRightDegree n := by
  omega

/-- Helper for Example 13.41.2: the two distinguished degrees of the two-term differential complex
are distinct. -/
private theorem boundedAbovePostnikovSingleDifferential_left_ne_right
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialLeftDegree n ≠
      boundedAbovePostnikovSingleDifferentialRightDegree n := by
  omega

/-- Helper for Example 13.41.2: the degreewise object function of the two-term complex whose only
nonzero differential is `K.d (-(n + 1)) (-n)`. -/
private abbrev boundedAbovePostnikovSingleDifferentialObj
    (n : ℕ) (i : ℤ) : 𝒜 :=
  if hi : i = boundedAbovePostnikovSingleDifferentialLeftDegree n then
    K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n)
  else if hi' : i = boundedAbovePostnikovSingleDifferentialRightDegree n then
    K.X (boundedAbovePostnikovSingleDifferentialRightDegree n)
  else
    0

/-- Helper for Example 13.41.2: the two-term differential complex has `K.X (-(n + 1))` in its
left degree. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_left
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialObj K n
        (boundedAbovePostnikovSingleDifferentialLeftDegree n) =
      K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n) := by
  simp [boundedAbovePostnikovSingleDifferentialObj]

/-- Helper for Example 13.41.2: the two-term differential complex has `K.X (-n)` in its right
degree. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_right
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialObj K n
        (boundedAbovePostnikovSingleDifferentialRightDegree n) =
      K.X (boundedAbovePostnikovSingleDifferentialRightDegree n) := by
  simp [boundedAbovePostnikovSingleDifferentialObj,
    boundedAbovePostnikovSingleDifferential_left_ne_right]

/-- Helper for Example 13.41.2: at a general index identified with the left degree, the two-term
complex recovers the left endpoint object. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_eq_left
    (n : ℕ) {i : ℤ}
    (hi : i = boundedAbovePostnikovSingleDifferentialLeftDegree n) :
    boundedAbovePostnikovSingleDifferentialObj K n i =
      K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n) := by
  subst hi
  exact boundedAbovePostnikovSingleDifferentialObj_left (K := K) n

/-- Helper for Example 13.41.2: at a general index identified with the right degree, the two-term
complex recovers the right endpoint object. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_eq_right
    (n : ℕ) {i : ℤ}
    (hi : i = boundedAbovePostnikovSingleDifferentialRightDegree n) :
    boundedAbovePostnikovSingleDifferentialObj K n i =
      K.X (boundedAbovePostnikovSingleDifferentialRightDegree n) := by
  subst hi
  exact boundedAbovePostnikovSingleDifferentialObj_right (K := K) n

/-- Helper for Example 13.41.2: one step above the left degree, the two-term differential complex
lands in its right endpoint object. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_left_succ
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialObj K n
        (boundedAbovePostnikovSingleDifferentialLeftDegree n + 1) =
      K.X (boundedAbovePostnikovSingleDifferentialRightDegree n) := by
  rw [boundedAbovePostnikovSingleDifferential_left_add_one]
  exact boundedAbovePostnikovSingleDifferentialObj_right (K := K) n

/-- Helper for Example 13.41.2: outside the left degree, the differential component of the
two-term complex vanishes. -/
private theorem boundedAbovePostnikovSingleDifferentialD_eq_zero
    (n : ℕ) {i : ℤ}
    (hi : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n) :
    (if hi' : i = boundedAbovePostnikovSingleDifferentialLeftDegree n then
      eqToHom (boundedAbovePostnikovSingleDifferentialObj_eq_left (K := K) (n := n) hi') ≫
        K.d (boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
            eqToHom
              (boundedAbovePostnikovSingleDifferentialObj_left_succ (K := K) n).symm
    else
      0) = 0 := by
  simp [hi]

/-- Helper for Example 13.41.2: the degreewise differential data of the two-term complex whose
only nonzero differential is `K.d (-(n + 1)) (-n)`. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialD
    (n : ℕ) (i : ℤ) :
    boundedAbovePostnikovSingleDifferentialObj K n i ⟶
      boundedAbovePostnikovSingleDifferentialObj K n (i + 1) :=
  if hi : i = boundedAbovePostnikovSingleDifferentialLeftDegree n then
    eqToHom (boundedAbovePostnikovSingleDifferentialObj_eq_left (K := K) (n := n) hi) ≫
      K.d (boundedAbovePostnikovSingleDifferentialLeftDegree n)
        (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_left_succ (K := K) n).symm
  else
    0

/-- Helper for Example 13.41.2: the unique nonzero differential of the two-term complex is the
raw differential of `K` between the two adjacent cutoff degrees. -/
private theorem boundedAbovePostnikovSingleDifferentialD_left
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialD K n
        (boundedAbovePostnikovSingleDifferentialLeftDegree n) =
      eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n) ≫
        K.d (boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
            eqToHom
              (boundedAbovePostnikovSingleDifferentialObj_left_succ (K := K) n).symm := by
  simp [boundedAbovePostnikovSingleDifferentialD]

/-- Helper for Example 13.41.2: the differential in the right endpoint degree of the two-term
complex is zero. -/
private theorem boundedAbovePostnikovSingleDifferentialD_right
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialD K n
        (boundedAbovePostnikovSingleDifferentialRightDegree n) = 0 := by
  apply boundedAbovePostnikovSingleDifferentialD_eq_zero (K := K) (n := n)
  exact boundedAbovePostnikovSingleDifferential_left_ne_right n

/-- Helper for Example 13.41.2: the differential of the two-term complex squares to zero. -/
private theorem boundedAbovePostnikovSingleDifferential_d_sq
    (n : ℕ) (i : ℤ) :
    boundedAbovePostnikovSingleDifferentialD K n i ≫
      boundedAbovePostnikovSingleDifferentialD K n (i + 1) = 0 := by
  by_cases hi : i = boundedAbovePostnikovSingleDifferentialLeftDegree n
  · subst hi
    rw [boundedAbovePostnikovSingleDifferentialD_left,
      boundedAbovePostnikovSingleDifferential_left_add_one, boundedAbovePostnikovSingleDifferentialD_right]
    simp
  · rw [boundedAbovePostnikovSingleDifferentialD_eq_zero (K := K) (n := n) hi, zero_comp]

/-- Helper for Example 13.41.2: the two-term cochain complex whose only nonzero differential is
`K.d (-(n + 1)) (-n)`. -/
private noncomputable abbrev boundedAbovePostnikovSingleDifferentialMiddle
    (n : ℕ) : CochainComplex 𝒜 ℤ :=
  CochainComplex.of
    (boundedAbovePostnikovSingleDifferentialObj K n)
    (boundedAbovePostnikovSingleDifferentialD K n)
    (boundedAbovePostnikovSingleDifferential_d_sq (K := K) n)

/-- Helper for Example 13.41.2: away from its two endpoint degrees, the two-term differential
complex is zero. -/
private theorem boundedAbovePostnikovSingleDifferentialObj_eq_zero
    (n : ℕ) {i : ℤ}
    (hleft : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n)
    (hright : i ≠ boundedAbovePostnikovSingleDifferentialRightDegree n) :
    boundedAbovePostnikovSingleDifferentialObj K n i = 0 := by
  simp [boundedAbovePostnikovSingleDifferentialObj, hleft, hright]

/-- Helper for Example 13.41.2: the right endpoint degree of the two-term differential complex is
different from the left endpoint degree. -/
private theorem boundedAbovePostnikovSingleDifferential_right_ne_left
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialRightDegree n ≠
      boundedAbovePostnikovSingleDifferentialLeftDegree n := by
  intro h
  exact boundedAbovePostnikovSingleDifferential_left_ne_right n h.symm

/-- Helper for Example 13.41.2: outside the left endpoint degree, the differential of the two-term
complex vanishes. -/
private theorem boundedAbovePostnikovSingleDifferentialD_ne_left
    (n : ℕ) {i : ℤ}
    (hi : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n) :
    boundedAbovePostnikovSingleDifferentialD K n i = 0 := by
  simpa [boundedAbovePostnikovSingleDifferentialD] using
    boundedAbovePostnikovSingleDifferentialD_eq_zero (K := K) (n := n) hi

/-- Helper for Example 13.41.2: the canonical inclusion of the single complex `A_n[-n]` into the
two-term differential complex lands in the right endpoint degree. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialFromX
    (n : ℕ) :
    boundedAbovePostnikovXComplex K n ⟶
      boundedAbovePostnikovSingleDifferentialMiddle K n :=
  HomologicalComplex.mkHomFromSingle
    (eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm)
    (fun q hq ↦ by
      -- The target two-term complex has no outgoing differential from its right endpoint.
      have hq' :
          q = boundedAbovePostnikovSingleDifferentialRightDegree n + 1 := by
        simpa using hq
      subst hq'
      have hD :
          boundedAbovePostnikovSingleDifferentialD K n
            (boundedAbovePostnikovSingleDifferentialRightDegree n) = 0 := by
        exact boundedAbovePostnikovSingleDifferentialD_ne_left (K := K) (n := n)
          (boundedAbovePostnikovSingleDifferential_right_ne_left n)
      simpa [boundedAbovePostnikovSingleDifferentialMiddle, Category.assoc] using
        congrArg
          (fun f ↦
            eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm ≫ f)
          hD

/-- Helper for Example 13.41.2: away from the right endpoint degree, the map from the single
complex `A_n[-n]` into the two-term differential complex vanishes. -/
private theorem boundedAbovePostnikovSingleDifferentialFromX_component_eq_zero
    (n : ℕ) {i : ℤ}
    (hi : i ≠ boundedAbovePostnikovSingleDifferentialRightDegree n) :
    (boundedAbovePostnikovSingleDifferentialFromX K n).f i = 0 := by
  -- The source single complex is supported only in degree `-n`.
  simp [boundedAbovePostnikovSingleDifferentialFromX, HomologicalComplex.mkHomFromSingle_f, hi]

/-- Helper for Example 13.41.2: at the right endpoint degree, the inclusion from `A_n[-n]` into
the two-term differential complex is the canonical endpoint identification. -/
private theorem boundedAbovePostnikovSingleDifferentialFromX_component_eq_right
    (n : ℕ) :
    (boundedAbovePostnikovSingleDifferentialFromX K n).f
        (boundedAbovePostnikovSingleDifferentialRightDegree n) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
          (boundedAbovePostnikovSingleDifferentialRightDegree n)
          (K.X (boundedAbovePostnikovSingleDifferentialRightDegree n))).hom ≫
        eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm := by
  -- Evaluating `mkHomFromSingle` at the supported degree recovers the defining endpoint map.
  simp [boundedAbovePostnikovSingleDifferentialFromX, HomologicalComplex.mkHomFromSingle_f]

/-- Helper for Example 13.41.2: the canonical projection from the two-term differential complex to
`A_{n + 1}[-(n + 1)]` reads off the left endpoint degree. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialToNext
    (n : ℕ) :
    boundedAbovePostnikovSingleDifferentialMiddle K n ⟶
      boundedAbovePostnikovXComplex K (n + 1) :=
  HomologicalComplex.mkHomToSingle
    (eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
        (boundedAbovePostnikovSingleDifferentialLeftDegree n)
        (K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n))).inv)
    (fun i hi ↦ by
      -- Any differential feeding the left endpoint comes from a degree where the two-term
      -- differential already vanishes.
      have hi' : i + 1 = boundedAbovePostnikovSingleDifferentialLeftDegree n := by
        simpa using hi
      have hi_ne :
          i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n := by
        intro h
        have : i + 1 = boundedAbovePostnikovSingleDifferentialLeftDegree n := hi'
        omega
      have hD :
          boundedAbovePostnikovSingleDifferentialD K n i = 0 := by
        exact boundedAbovePostnikovSingleDifferentialD_ne_left (K := K) (n := n) hi_ne
      simpa [boundedAbovePostnikovSingleDifferentialMiddle, Category.assoc] using
        congrArg
          (fun f ↦
            f ≫ eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
                (boundedAbovePostnikovSingleDifferentialLeftDegree n)
                (K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n))).inv)
          hD

/-- Helper for Example 13.41.2: away from the left endpoint degree, the projection from the
two-term differential complex to `A_{n + 1}[-(n + 1)]` vanishes. -/
private theorem boundedAbovePostnikovSingleDifferentialToNext_component_eq_zero
    (n : ℕ) {i : ℤ}
    (hi : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n) :
    (boundedAbovePostnikovSingleDifferentialToNext K n).f i = 0 := by
  -- The target single complex is supported only in degree `-(n + 1)`.
  simp [boundedAbovePostnikovSingleDifferentialToNext, HomologicalComplex.mkHomToSingle_f, hi]

/-- Helper for Example 13.41.2: at the left endpoint degree, the projection from the two-term
differential complex is the canonical endpoint identification. -/
private theorem boundedAbovePostnikovSingleDifferentialToNext_component_eq_left
    (n : ℕ) :
    (boundedAbovePostnikovSingleDifferentialToNext K n).f
        (boundedAbovePostnikovSingleDifferentialLeftDegree n) =
      eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
          (boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n))).inv := by
  -- Evaluating `mkHomToSingle` at the supported degree recovers the defining endpoint map.
  simp [boundedAbovePostnikovSingleDifferentialToNext, HomologicalComplex.mkHomToSingle_f]

/-- Helper for Example 13.41.2: the canonical two-term differential short complex compares the
raw differential short exact sequence with the brutal-truncation stage short exact sequence. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialShortComplex
    (n : ℕ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (boundedAbovePostnikovSingleDifferentialFromX K n)
    (boundedAbovePostnikovSingleDifferentialToNext K n)
    (by
      -- The left and right endpoint maps land in disjoint supported degrees, so their composite
      -- into the left single complex is zero.
      apply HomologicalComplex.to_single_hom_ext
      rw [HomologicalComplex.comp_f,
        boundedAbovePostnikovSingleDifferentialFromX_component_eq_zero (K := K) (n := n)
          (i := boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (boundedAbovePostnikovSingleDifferential_left_ne_right n),
        zero_comp]
      simp)

/-- Helper for Example 13.41.2: evaluating the two-term differential short complex in any degree
yields one of the split short complexes `0 ⟶ 0 ⟶ 0`, `0 ⟶ K.X i ⟶ K.X i`, or
`K.X i ⟶ K.X i ⟶ 0`. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialDegreewiseSplitting
    (n : ℕ) (i : ℤ) :
    ((boundedAbovePostnikovSingleDifferentialShortComplex K n).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)).Splitting := by
  let S : ShortComplex 𝒜 :=
    (boundedAbovePostnikovSingleDifferentialShortComplex K n).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  by_cases hi_left : i = boundedAbovePostnikovSingleDifferentialLeftDegree n
  · subst hi_left
    change S.Splitting
    have hX₁ : IsZero S.X₁ := by
      -- The source single complex `A_n[-n]` vanishes at the left endpoint degree.
      dsimp [S, boundedAbovePostnikovXComplex]
      exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
        (boundedAbovePostnikovSingleDifferentialRightDegree n)
        (K.X (boundedAbovePostnikovSingleDifferentialRightDegree n))
        (boundedAbovePostnikovSingleDifferentialLeftDegree n)
        (boundedAbovePostnikovSingleDifferential_left_ne_right n)
    have hg : IsIso S.g := by
      -- At the left endpoint, the projection is exactly the canonical identification.
      dsimp [S, boundedAbovePostnikovSingleDifferentialShortComplex]
      rw [boundedAbovePostnikovSingleDifferentialToNext_component_eq_left (K := K) (n := n)]
      exact IsIso.comp_isIso
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · by_cases hi_right : i = boundedAbovePostnikovSingleDifferentialRightDegree n
    · subst hi_right
      change S.Splitting
      have hX₃ : IsZero S.X₃ := by
        -- The target single complex `A_{n + 1}[-(n + 1)]` vanishes at the right endpoint degree.
        dsimp [S, boundedAbovePostnikovXComplex]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n))
          (boundedAbovePostnikovSingleDifferentialRightDegree n)
          (boundedAbovePostnikovSingleDifferential_right_ne_left n)
      have hf : IsIso S.f := by
        -- At the right endpoint, the inclusion is exactly the canonical identification.
        dsimp [S, boundedAbovePostnikovSingleDifferentialShortComplex]
        rw [boundedAbovePostnikovSingleDifferentialFromX_component_eq_right (K := K) (n := n)]
        exact IsIso.comp_isIso
      exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃
    · change S.Splitting
      have hX₁ : IsZero S.X₁ := by
        -- Outside degree `-n`, the source single complex is zero.
        dsimp [S, boundedAbovePostnikovXComplex]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (boundedAbovePostnikovSingleDifferentialRightDegree n)
          (K.X (boundedAbovePostnikovSingleDifferentialRightDegree n)) i hi_right
      have hX₂ : IsZero S.X₂ := by
        -- Away from both endpoints, the two-term middle complex is zero.
        simpa [S, boundedAbovePostnikovSingleDifferentialMiddle,
          boundedAbovePostnikovSingleDifferentialObj_eq_zero (K := K) (n := n) hi_left hi_right]
          using (show IsZero (0 : 𝒜) by infer_instance)
      have hX₃ : IsZero S.X₃ := by
        -- Outside degree `-(n + 1)`, the target single complex is zero.
        dsimp [S, boundedAbovePostnikovXComplex]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (boundedAbovePostnikovSingleDifferentialLeftDegree n)
          (K.X (boundedAbovePostnikovSingleDifferentialLeftDegree n)) i hi_left
      have hg : IsIso S.g := by
        -- In the off-support region, the projection is the zero map between zero objects.
        dsimp [S, boundedAbovePostnikovSingleDifferentialShortComplex]
        rw [boundedAbovePostnikovSingleDifferentialToNext_component_eq_zero
          (K := K) (n := n) (i := i) hi_left]
        exact hX₂.isIso hX₃ 0

/-- Helper for Example 13.41.2: the two-term differential short complex is short exact. -/
private theorem boundedAbovePostnikovSingleDifferentialShortExact
    (n : ℕ) :
    (boundedAbovePostnikovSingleDifferentialShortComplex K n).ShortExact := by
  -- Evaluate degreewise and use the canonical splittings in the left-endpoint, right-endpoint,
  -- and off-support regions.
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i ↦
      (boundedAbovePostnikovSingleDifferentialDegreewiseSplitting (K := K) n i).shortExact)

/-- Helper for Example 13.41.2: the right endpoint degree of the two-term differential complex
still lies in the retained range of stage `n + 1`. -/
private theorem boundedAbovePostnikovSingleDifferentialRight_mem_stage
    (n : ℕ) :
    -(((n + 1 : ℕ)) : ℤ) ≤ boundedAbovePostnikovSingleDifferentialRightDegree n := by
  omega

/-- Helper for Example 13.41.2: the middle comparison map from the stage short exact sequence to
the explicit two-term differential short exact sequence is supported only in the two endpoint
degrees. -/
private noncomputable def boundedAbovePostnikovStageToSingleDifferentialMiddleComponent
    (n : ℕ) (i : ℤ) :
    (brutalLeftTruncationStage K (n + 1)).X i ⟶
      (boundedAbovePostnikovSingleDifferentialMiddle K n).X i :=
  if hi_left : i = boundedAbovePostnikovSingleDifferentialLeftDegree n then
    by
      subst hi_left
      exact
        (brutalLeftTruncationXIso K (n + 1)
          (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n).symm
  else if hi_right : i = boundedAbovePostnikovSingleDifferentialRightDegree n then
    by
      subst hi_right
      exact
        (brutalLeftTruncationXIso K (n + 1)
          (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm
  else
    0

/-- Helper for Example 13.41.2: at the left endpoint degree, the middle comparison map is the
canonical stage-term identification. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_left
    (n : ℕ) :
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n
        (boundedAbovePostnikovSingleDifferentialLeftDegree n) =
      (brutalLeftTruncationXIso K (n + 1)
        (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n).symm := by
  -- At the new cutoff, only the left supported branch survives.
  simp [boundedAbovePostnikovStageToSingleDifferentialMiddleComponent,
    boundedAbovePostnikovSingleDifferential_left_ne_right]

/-- Helper for Example 13.41.2: at the right endpoint degree, the middle comparison map is the
canonical stage-term identification. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_right
    (n : ℕ) :
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n
        (boundedAbovePostnikovSingleDifferentialRightDegree n) =
      (brutalLeftTruncationXIso K (n + 1)
        (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm := by
  -- At degree `-n`, only the right supported branch survives.
  simp [boundedAbovePostnikovStageToSingleDifferentialMiddleComponent,
    boundedAbovePostnikovSingleDifferential_right_ne_left]

/-- Helper for Example 13.41.2: away from the two endpoint degrees, the middle comparison map
vanishes. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_zero
    (n : ℕ) {i : ℤ}
    (hleft : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n)
    (hright : i ≠ boundedAbovePostnikovSingleDifferentialRightDegree n) :
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n i = 0 := by
  -- Outside the support of the two-term target, the comparison map is zero by definition.
  simp [boundedAbovePostnikovStageToSingleDifferentialMiddleComponent, hleft, hright]

/-- Helper for Example 13.41.2: the degreewise middle comparison map commutes with
differentials. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddle_comm
    (n : ℕ) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) :
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n i ≫
        (boundedAbovePostnikovSingleDifferentialMiddle K n).d i j =
      (brutalLeftTruncationStage K (n + 1)).d i j ≫
        boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n j := by
  have hij' : i + 1 = j := by
    simpa using hij
  by_cases hi : i = boundedAbovePostnikovSingleDifferentialLeftDegree n
  · subst hi
    have hj : j = boundedAbovePostnikovSingleDifferentialRightDegree n := by
      simpa [boundedAbovePostnikovSingleDifferential_left_add_one] using hij'
    subst hj
    -- The unique nonzero differential in the two-term target is the raw differential of `K`.
    rw [dNext_eq (boundedAbovePostnikovSingleDifferentialMiddle K n)
        (show
          (ComplexShape.up ℤ).Rel
            (boundedAbovePostnikovSingleDifferentialLeftDegree n)
            (boundedAbovePostnikovSingleDifferentialRightDegree n) by
              simpa [boundedAbovePostnikovSingleDifferential_left_add_one]),
      boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_left,
      boundedAbovePostnikovSingleDifferentialD_left,
      boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_right]
    have hd :
        (brutalLeftTruncationXIso K (n + 1)
            (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
            K.d (boundedAbovePostnikovSingleDifferentialLeftDegree n)
              (boundedAbovePostnikovSingleDifferentialRightDegree n) =
          (brutalLeftTruncationStage K (n + 1)).d
              (boundedAbovePostnikovSingleDifferentialLeftDegree n)
              (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
            (brutalLeftTruncationXIso K (n + 1)
              (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom := by
      -- Compare the stage differential with the ambient differential through the structural
      -- identifications of the retained endpoint degrees.
      calc
        (brutalLeftTruncationXIso K (n + 1)
            (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
            K.d (boundedAbovePostnikovSingleDifferentialLeftDegree n)
              (boundedAbovePostnikovSingleDifferentialRightDegree n) =
          (brutalLeftTruncationXIso K (n + 1)
              (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
            ((brutalLeftTruncationXIso K (n + 1)
                (brutalLeftTruncation_cutoff_le (n + 1))).inv ≫
              (brutalLeftTruncationStage K (n + 1)).d
                (boundedAbovePostnikovSingleDifferentialLeftDegree n)
                (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
              (brutalLeftTruncationXIso K (n + 1)
                (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom) := by
              rw [brutalLeftTruncation_d_via_x_iso (K := K) (n := n + 1)
                (i := boundedAbovePostnikovSingleDifferentialLeftDegree n)
                (j := boundedAbovePostnikovSingleDifferentialRightDegree n)
                (brutalLeftTruncation_cutoff_le (n + 1))
                (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n)))]
        _ =
          (brutalLeftTruncationStage K (n + 1)).d
              (boundedAbovePostnikovSingleDifferentialLeftDegree n)
              (boundedAbovePostnikovSingleDifferentialRightDegree n) ≫
            (brutalLeftTruncationXIso K (n + 1)
              (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom := by
              simp [Category.assoc]
    simpa [Category.assoc, boundedAbovePostnikovSingleDifferential_left_add_one] using
      congrArg
        (fun f ↦
          f ≫ eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm)
        hd
  · rw [dNext_eq (boundedAbovePostnikovSingleDifferentialMiddle K n) hij,
      boundedAbovePostnikovSingleDifferentialD_ne_left (K := K) (n := n) hi, comp_zero]
    by_cases hj_left : j = boundedAbovePostnikovSingleDifferentialLeftDegree n
    · subst hj_left
      have hi_lt :
          i < boundedAbovePostnikovSingleDifferentialLeftDegree n := by
        omega
      have hzero :
          IsZero ((brutalLeftTruncationStage K (n + 1)).X i) := by
        exact
          (brutalLeftTruncationStage K (n + 1)).isZero_of_isStrictlyGE
            (boundedAbovePostnikovSingleDifferentialLeftDegree n) i hi_lt
      -- A differential feeding the new cutoff starts from a zero stage term.
      exact hzero.eq_of_src _ _
    · by_cases hj_right : j = boundedAbovePostnikovSingleDifferentialRightDegree n
      · exfalso
        omega
      · -- Outside the two supported endpoint degrees, the comparison map already vanishes.
        rw [boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_zero
          (K := K) (n := n) (i := j) hj_left hj_right, comp_zero]

/-- Helper for Example 13.41.2: the middle chain map from the stage short exact sequence to the
explicit two-term differential short exact sequence. -/
private noncomputable def boundedAbovePostnikovStageToSingleDifferentialMiddle
    (n : ℕ) :
    brutalLeftTruncationStage K (n + 1) ⟶
      boundedAbovePostnikovSingleDifferentialMiddle K n where
  f := boundedAbovePostnikovStageToSingleDifferentialMiddleComponent K n
  comm' := boundedAbovePostnikovStageToSingleDifferentialMiddle_comm (K := K) n

/-- Helper for Example 13.41.2: at the left endpoint degree, the middle chain map agrees with the
canonical stage-term identification. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_left
    (n : ℕ) :
    (boundedAbovePostnikovStageToSingleDifferentialMiddle K n).f
        (boundedAbovePostnikovSingleDifferentialLeftDegree n) =
      (brutalLeftTruncationXIso K (n + 1)
        (brutalLeftTruncation_cutoff_le (n + 1))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_left (K := K) n).symm := by
  -- Unfold the chain map once and reuse the endpoint component formula already proved.
  simpa [boundedAbovePostnikovStageToSingleDifferentialMiddle] using
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_left (K := K) n

/-- Helper for Example 13.41.2: at the right endpoint degree, the middle chain map agrees with
the canonical stage-term identification. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_right
    (n : ℕ) :
    (boundedAbovePostnikovStageToSingleDifferentialMiddle K n).f
        (boundedAbovePostnikovSingleDifferentialRightDegree n) =
      (brutalLeftTruncationXIso K (n + 1)
        (boundedAbovePostnikovSingleDifferentialRight_mem_stage (n := n))).hom ≫
          eqToHom (boundedAbovePostnikovSingleDifferentialObj_right (K := K) n).symm := by
  -- Unfold the chain map once and reuse the endpoint component formula already proved.
  simpa [boundedAbovePostnikovStageToSingleDifferentialMiddle] using
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_right (K := K) n

/-- Helper for Example 13.41.2: away from the two endpoint degrees, the middle chain map
vanishes. -/
private theorem boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_zero
    (n : ℕ) {i : ℤ}
    (hleft : i ≠ boundedAbovePostnikovSingleDifferentialLeftDegree n)
    (hright : i ≠ boundedAbovePostnikovSingleDifferentialRightDegree n) :
    (boundedAbovePostnikovStageToSingleDifferentialMiddle K n).f i = 0 := by
  -- Unfold the chain map once and reuse the off-support vanishing formula.
  simpa [boundedAbovePostnikovStageToSingleDifferentialMiddle] using
    boundedAbovePostnikovStageToSingleDifferentialMiddleComponent_eq_zero
      (K := K) (n := n) hleft hright

/-- Helper for Example 13.41.2: the stage short exact sequence maps to the explicit two-term
differential short exact sequence by the canonical quotient, middle comparison map, and identity on
the new cutoff term. -/
private noncomputable def boundedAbovePostnikovStageToSingleDifferentialHom
    (n : ℕ) :
    boundedAbovePostnikovStageShortComplex K n ⟶
      boundedAbovePostnikovSingleDifferentialShortComplex K n :=
  ShortComplex.Hom.mk
    (brutalLeftTruncationToSingle K n)
    (boundedAbovePostnikovStageToSingleDifferentialMiddle K n)
    (𝟙 _)
    (by
      -- The left square is supported only in degrees `-(n + 1)` and `-n`.
      ext i
      by_cases hi_right : i = boundedAbovePostnikovSingleDifferentialRightDegree n
      · subst hi_right
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
          brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := n),
          boundedAbovePostnikovSingleDifferentialFromX_component_eq_right (K := K) (n := n),
          brutalLeftTruncationStep_component_eq_iso (K := K) (n := n)
            (i := boundedAbovePostnikovSingleDifferentialRightDegree n)
            (by simp [boundedAbovePostnikovSingleDifferentialRightDegree]),
          boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_right (K := K) (n := n)]
        simp [Category.assoc]
      · by_cases hi_left : i = boundedAbovePostnikovSingleDifferentialLeftDegree n
        · subst hi_left
          rw [HomologicalComplex.comp_f,
            brutalLeftTruncationToSingle_component_eq_zero (K := K) (n := n)
              (i := boundedAbovePostnikovSingleDifferentialLeftDegree n) (by omega),
            zero_comp, HomologicalComplex.comp_f,
            brutalLeftTruncationStep_component_eq_zero (K := K) (n := n)
              (i := boundedAbovePostnikovSingleDifferentialLeftDegree n) (by omega),
            zero_comp]
        · rw [HomologicalComplex.comp_f,
            boundedAbovePostnikovSingleDifferentialFromX_component_eq_zero
              (K := K) (n := n) (i := i) hi_right,
            comp_zero, HomologicalComplex.comp_f,
            boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_zero
              (K := K) (n := n) (i := i) hi_left hi_right,
            comp_zero])
    (by
      -- The right square is determined by the left endpoint degree of the target single complex.
      apply HomologicalComplex.to_single_hom_ext
      rw [HomologicalComplex.comp_f,
        boundedAbovePostnikovStageToSingleDifferentialMiddle_f_eq_left (K := K) (n := n),
        boundedAbovePostnikovSingleDifferentialToNext_component_eq_left (K := K) (n := n),
        brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := n + 1)]
      simp [Category.assoc]))

/-- Helper for Example 13.41.2: shifting the explicit two-term differential short exact sequence
by `-(n + 1)` and rotating once produces the target comparison triangle used to identify the raw
differential. -/
private noncomputable def boundedAbovePostnikovSingleDifferentialTriangle
    (n : ℕ) :
    Triangle (DerivedCategory 𝒜) :=
  (((shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).obj
      (DerivedCategory.triangleOfSES (boundedAbovePostnikovSingleDifferentialShortExact K n))).rotate)

/-- Helper for Example 13.41.2: after the standard shift-and-rotate transport, the second edge of
the explicit two-term differential triangle is the shifted connecting morphism. -/
private theorem boundedAbovePostnikov_singleDifferential_rotated_mor₂
    (n : ℕ) :
    (boundedAbovePostnikovSingleDifferentialTriangle K n).mor₂ =
      (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
        (-((n + 1 : ℕ) : ℤ))⟧' := by
  -- Shifting preserves the connecting morphism, and one rotation moves it into the second edge.
  simp [boundedAbovePostnikovSingleDifferentialTriangle]

/-- The canonical bounded-above Postnikov maps recover the differentials
`X_{n + 1} ⟶ X_n`. -/
theorem boundedAbovePostnikov_comp (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      boundedAbovePostnikovXMap K n := by
  -- Route correction: the target short exact sequence has now been stabilized as the explicit
  -- two-term differential complex. The chain-level comparison `τ₂` is now explicit; what
  -- remains is to normalize the shifted-and-rotated connecting morphism for the target short exact
  -- sequence to the raw differential and then apply `triangleOfSESδ_naturality`.
  -- TODO: specialize `DerivedCategory.triangleOfSESδ_naturality` to
  -- `boundedAbovePostnikovStageToSingleDifferentialHom K n`, then identify the target connecting
  -- morphism after the shift/rotation transport with `boundedAbovePostnikovXMap K n`.
  sorry

private theorem boundedAboveTermSequence_delta₀ (n : ℕ) :
    (boundedAboveTermSequence K (n + 1)).δ₀ = boundedAboveTermSequence K n := by
  ext i
  · -- On objects, deleting the leftmost term shifts the `n + 1 - i` indexing by one step.
    simp [boundedAboveTermSequence, boundedAboveTermIndex]
  · -- The successor maps agree after the same index shift.
    simp [boundedAboveTermSequence, boundedAboveTermSequenceMap, boundedAboveTermIndex,
      boundedAboveTermIndex_succ_add_one]

private noncomputable def boundedAboveTermSequencePostnikovSystemZero :
    PostnikovSystem (boundedAboveTermSequence K 0) :=
  @PostnikovSystem.mk₀ _ _ _ _ _ _ _
    (boundedAboveTermSequence K 0)
    (boundedAbovePostnikovY K 0)
    (boundedAbovePostnikovToX K 0)
    (boundedAbovePostnikovToX_zero_isIso K)

/-- Example 13.41.2 (2): each finite row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
inherits the canonical finite `PostnikovSystem` coming from the brutal truncation tower. -/
noncomputable def boundedAboveTermSequencePostnikovSystem :
    (n : ℕ) → PostnikovSystem (boundedAboveTermSequence K n)
  | 0 =>
      boundedAboveTermSequencePostnikovSystemZero K
  | n + 1 =>
      let tail : PostnikovSystem ((boundedAboveTermSequence K (n + 1)).δ₀) :=
        cast (by rw [boundedAboveTermSequence_delta₀ K n])
          (boundedAboveTermSequencePostnikovSystem n)
      let headEq : tail.head = boundedAbovePostnikovY K n := by
        -- Rewriting the casted tail along `boundedAboveTermSequence_delta₀` recovers the recursive
        -- stage object from the previous finite row.
        cases boundedAboveTermSequence_delta₀ K n
        rfl
      PostnikovSystem.mkSucc tail
        (boundedAbovePostnikovY K (n + 1))
        (boundedAbovePostnikovToX K (n + 1))
        (cast (by
          simp [boundedAboveTermSequence, boundedAboveTermIndex, headEq])
          (boundedAbovePostnikovToNext K n))
        (cast (by
          simp [boundedAboveTermSequence, boundedAboveTermIndex, headEq])
          (boundedAbovePostnikovConnecting K n))
        (by
          -- The new stage triangle is exactly the distinguished triangle already attached to the
          -- brutal left-truncation stage.
          simpa [headEq] using boundedAbovePostnikov_distinguished K n)
        (by
          -- The new stage maps recover the next differential in the finite row.
          simpa [headEq] using boundedAbovePostnikov_comp K n)

/-- The canonical finite `PostnikovSystem` on the row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
has auxiliary object `Y_{n - i}` at index `i`. -/
@[simp] theorem boundedAboveTermSequencePostnikovSystem_apply
    (n : ℕ) (i : Fin (n + 1)) :
    boundedAboveTermSequencePostnikovSystem K n i =
      boundedAbovePostnikovY K (n - i.1) := by
  induction n generalizing i with
  | zero =>
      fin_cases i
      rfl
  | succ n ih =>
      refine Fin.cases ?_ ?_ i
      · -- At the leftmost index, the recursive constructor stores the new head object.
        rfl
      · intro j
        -- Successor indices are read from the recursively stored tail.
        dsimp [boundedAboveTermSequencePostnikovSystem]
        cases boundedAboveTermSequence_delta₀ K n
        simpa [boundedAboveTermIndex] using ih j

end

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (K : CochainComplex 𝒜 ℤ)
variable [HasColimitsOfShape ℕ 𝒜]

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

section

variable [HasExactColimitsOfShape ℕ 𝒜]

/-- The shifted brutal left-truncation tower has the countable coproduct needed to form its
telescope in `D(𝒜)`, obtained by combining the Chapter `13` countable-coproduct bridge in `𝒜`
with the termwise-coproduct bridge for `DerivedCategory.Q`. -/
noncomputable local instance brutalLeftTruncationTower_hasCoproduct
    :
    HasCoproduct (brutalLeftTruncationTower K ⋙ Q).obj := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  let _ : CountableAB4 𝒜 := CountableAB4.of_countableAB5 𝒜
  infer_instance

-- Proof sketch: apply `termwise_colimit_is_homotopy_colimit` to the canonical brutal
-- left-truncation tower,
-- and use `brutalLeftTruncationColimitComparison_isIso` to identify its termwise colimit
-- with the source complex `K`.
/-- Under exact sequential colimits, every cochain complex is a homotopy colimit of its brutal
left-truncation tower. Under `[K.IsStrictlyLE 0]`, this recovers the source tower
`Q(Y_0[0]) ⟶ Q(Y_1[1]) ⟶ Q(Y_2[2]) ⟶ ⋯` from Example 13.41.2 (3). -/
theorem brutalLeftTruncation_isHomotopyColimitOf :
    IsHomotopyColimitOf
      (brutalLeftTruncationTower K ⋙ Q)
      (Q.obj K) := by
  rcases termwise_colimit_is_homotopy_colimit (𝒜 := 𝒜) (S := brutalLeftTruncationTower K) with
    ⟨g, h, htriangle⟩
  let e : Q.obj (colimit (brutalLeftTruncationTower K)) ≅ Q.obj K :=
    asIso (Q.map (brutalLeftTruncationColimitComparison K))
  refine ⟨g ≫ e.hom, e.inv ≫ h, ?_⟩
  -- Transport the canonical telescope presentation along the comparison isomorphism.
  refine isomorphic_distinguished _ htriangle _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · simp
  · simp [Category.assoc]
  · simp [Category.assoc]

end

end

end

end CategoryTheory
