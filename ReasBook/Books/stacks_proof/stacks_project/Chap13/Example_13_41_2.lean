import StacksProject_2024.Chap04.Definition_4_22_1
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Lemma_13_33_6
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

/-- Helper for Example 13.41.2: forgetting the first arrow in the finite row shifts the
reversed source index by one, so the remaining object labels are unchanged. -/
private theorem boundedAboveTermIndex_succ
    (n : ℕ) (i : Fin (n + 1)) :
    boundedAboveTermIndex (n + 1) i.succ = boundedAboveTermIndex n i := by
  -- Both sides are the same reversed natural-number index after removing the first term.
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
    (brutalLeftTruncation_stage_index_eq n hi)

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
    simpa [e, i₀] using brutalLeftTruncation_stage_index_eq n hi
  have hj₀ : e.f j₀ = j := by
    simpa [e, j₀] using brutalLeftTruncation_stage_index_eq n hj
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
    (n : ℕ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
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
    simp only [brutalLeftTruncationStepComponent, dif_pos hi, dif_pos hj, Category.assoc]
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
      simp only [brutalLeftTruncationStepComponent, dif_neg hi, dif_pos hj, zero_comp]
      exact hzero.eq_of_src _ _
    · -- Strictly below the shared range, both components of the inclusion are zero.
      simp [brutalLeftTruncationStepComponent, hi, hj]

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
    (n : ℕ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    brutalLeftTruncationInclusionComponent K n i ≫ K.d i j =
      (brutalLeftTruncationStage K n).d i j ≫ brutalLeftTruncationInclusionComponent K n j := by
  have hij' : i + 1 = j := by
    simpa using hij
  by_cases hi : -((n : ℕ) : ℤ) ≤ i
  · have hj : -((n : ℕ) : ℤ) ≤ j := by
      omega
    -- On retained degrees, the inclusion is identified with the identity on `K`.
    apply (cancel_epi (brutalLeftTruncationXIso K n hi).inv).1
    simp only [brutalLeftTruncationInclusionComponent, dif_pos hi, dif_pos hj, Category.assoc]
    rw [Iso.inv_hom_id_assoc]
    exact (brutalLeftTruncation_d_via_x_iso (K := K) (n := n) hi hj).symm
  · by_cases hj : -((n : ℕ) : ℤ) ≤ j
    · have hi_lt : i < -((n : ℕ) : ℤ) := by
        omega
      have hzero :
          IsZero ((brutalLeftTruncationStage K n).X i) := by
        exact
          (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) i hi_lt
      -- Below the cutoff, the source term is zero, so the compatibility square is trivial.
      simp only [brutalLeftTruncationInclusionComponent, dif_neg hi, dif_pos hj, zero_comp]
      exact hzero.eq_of_src _ _
    · -- Outside the retained range, both components of the inclusion vanish.
      simp [brutalLeftTruncationInclusionComponent, hi, hj]

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
    (n : ℕ) (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (-((n : ℕ) : ℤ))) :
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
    rw [HomologicalComplex.comp_f]
    simp [brutalLeftTruncationStep, brutalLeftTruncationStepComponent,
      not_le_of_gt (show (-((n + 1 : ℕ) : ℤ)) < -((n : ℕ) : ℤ) by omega)]
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
  by_cases hi_left : i = -((n + 1 : ℕ) : ℤ)
  · change S.Splitting
    subst i
    have hX₁ : IsZero S.X₁ := by
      -- At the new cutoff, the previous brutal stage has already vanished.
      dsimp [S]
      exact (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
        (-((n : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
    have hg : IsIso S.g := by
      -- The quotient map at the new cutoff is the canonical identification with the new term.
      dsimp [S, boundedAbovePostnikovStageShortComplex]
      have hdeg : (-(↑n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) := by
        omega
      rw [hdeg, brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := n + 1)]
      exact IsIso.comp_isIso
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · by_cases hi_right : -((n : ℕ) : ℤ) ≤ i
    · change S.Splitting
      have hX₃ : IsZero S.X₃ := by
        -- Away from the new cutoff, the target single complex is zero.
        dsimp [S, boundedAbovePostnikovXComplex]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (-((n + 1 : ℕ) : ℤ)) (K.X (-((n + 1 : ℕ) : ℤ))) i hi_left
      have hf : IsIso S.f := by
        -- On the shared retained range, the stage inclusion is the transported identity.
        simpa [S, boundedAbovePostnikovStageShortComplex, brutalLeftTruncationStep] using
          (show IsIso (brutalLeftTruncationStepComponent K n i) by
            rw [brutalLeftTruncationStep_component_eq_iso (K := K) (n := n) (i := i) hi_right]
            exact IsIso.comp_isIso)
      exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃
    · change S.Splitting
      have hi_lt : i < -((n : ℕ) : ℤ) := by
        omega
      have hi_lt' : i < -((n + 1 : ℕ) : ℤ) := by
        omega
      have hX₁ : IsZero S.X₁ := by
        -- Below the old cutoff, the previous stage is zero.
        dsimp [S]
        exact (brutalLeftTruncationStage K n).isZero_of_isStrictlyGE
          (-((n : ℕ) : ℤ)) i hi_lt
      have hX₂ : IsZero S.X₂ := by
        -- Away from the new cutoff and below the shared range, the next stage is zero as well.
        dsimp [S]
        exact (brutalLeftTruncationStage K (n + 1)).isZero_of_isStrictlyGE
          (-((n + 1 : ℕ) : ℤ)) i hi_lt'
      have hX₃ : IsZero S.X₃ := by
        -- The target single complex is still zero outside its supported cutoff degree.
        dsimp [S, boundedAbovePostnikovXComplex]
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (-((n + 1 : ℕ) : ℤ)) (K.X (-((n + 1 : ℕ) : ℤ))) i hi_left
      have hg : IsIso S.g := by
        -- In the off-support region, the quotient map is the zero map between zero objects.
        dsimp [S, boundedAbovePostnikovStageShortComplex]
        rw [brutalLeftTruncationToSingle_component_eq_zero
          (K := K) (n := n + 1) (i := i) hi_left]
        exact hX₂.isIso hX₃ 0
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg

/-- The stage short complex is short exact. -/
private theorem boundedAbovePostnikovStageShortExact (n : ℕ) :
    (boundedAbovePostnikovStageShortComplex K n).ShortExact := by
  -- Evaluate degreewise and use the canonical stage splittings in the endpoint and off-support
  -- regions.
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i ↦
      (boundedAbovePostnikovStageDegreewiseSplitting (K := K) n i).shortExact)

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
  -- Compare both morphisms degreewise: they are the transported identity on retained terms and
  -- vanish below the old cutoff.
  ext i
  by_cases hi : -((n : ℕ) : ℤ) ≤ i
  · dsimp [brutalLeftTruncationStep, brutalLeftTruncationInclusion]
    rw [brutalLeftTruncationStep_component_eq_iso (K := K) (n := n) (i := i) hi,
      brutalLeftTruncationInclusion_component_eq_iso (K := K) (n := n + 1) (i := i)
        (brutalLeftTruncation_next_le (n := n) hi),
      brutalLeftTruncationInclusion_component_eq_iso (K := K) (n := n) (i := i) hi]
    simp [Category.assoc]
  · have hi' : i < -((n : ℕ) : ℤ) := by
      omega
    dsimp [brutalLeftTruncationStep, brutalLeftTruncationInclusion]
    rw [brutalLeftTruncationStep_component_eq_zero (K := K) (n := n) (i := i) hi',
      zero_comp,
      brutalLeftTruncationInclusion_component_eq_zero (K := K) (n := n) (i := i) hi']

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
  -- Proof comment: compose the universal cocone-leg formula with the inverse comparison to expose
  -- the component of the complex-level colimit cocone.
  simpa [brutalLeftTruncationEvalColimitIso, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Example 13.41.2: the complex-level colimit comparison evaluates on each cocone leg
to the canonical inclusion of that stage into `K`. -/
private theorem brutalLeftTruncationColimitComparison_f_ι
    (n : ℕ) (i : ℤ) :
    (colimit.ι (brutalLeftTruncationTower K) n).f i ≫
      (brutalLeftTruncationColimitComparison K).f i =
        brutalLeftTruncationInclusionComponent K n i := by
  -- Proof comment: this is the defining cocone equation for `colimit.desc`, read degreewise.
  simpa [brutalLeftTruncationColimitComparison, brutalLeftTruncationCocone] using
    congrArg (fun f ↦ f.f i)
      (colimit.ι_desc (brutalLeftTruncationCocone K) n)

/-- Helper for Example 13.41.2: after replacing the complex colimit by the evaluated colimit, the
comparison to `K.X i` is still read off on cocone legs by the stage inclusion component. -/
private theorem brutalLeftTruncation_eval_colimitComparison_hom_ι
    (i : ℤ) (n : ℕ) :
    colimit.ι
        (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) n ≫
          (brutalLeftTruncationEvalColimitIso (K := K) i).hom ≫
            (brutalLeftTruncationColimitComparison K).f i =
      brutalLeftTruncationInclusionComponent K n i := by
  -- Proof comment: first identify the evaluated cocone leg with the degreewise component, then use
  -- the defining `colimit.desc` equation for the complex-level comparison.
  have h₁ :
      colimit.ι
          (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) n ≫
            (brutalLeftTruncationEvalColimitIso (K := K) i).hom ≫
              (brutalLeftTruncationColimitComparison K).f i =
        (colimit.ι (brutalLeftTruncationTower K) n).f i ≫
          (brutalLeftTruncationColimitComparison K).f i := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (brutalLeftTruncationColimitComparison K).f i)
        (brutalLeftTruncation_eval_colimit_iso_hom_ι (K := K) i n)
  exact h₁.trans (by simpa using brutalLeftTruncationColimitComparison_f_ι (K := K) n i)

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
private noncomputable def brutalLeftTruncation_eval_stabilized_isColimit
    (i : ℤ) (n : ℕ) (hn : -((n : ℕ) : ℤ) ≤ i) :
    IsColimit (brutalLeftTruncationEvalCocone K i) := by
  -- Proof comment: from stage `n` onward every leg into `K.X i` is an isomorphism, so the
  -- evaluated cocone is essentially constant.
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
    -- Proof comment: postcompose with the stabilized leg at stage `k`; cocone naturality reduces
    -- the equality to the section-retraction identity at the chosen stable stage.
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
    rw [hjk, Category.assoc, hnk]
    simpa [Category.assoc]

/-

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
      (colimit.ι_desc (brutalLeftTruncationCocone K) n)

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
  simpa [Category.assoc] using
    (brutalLeftTruncationColimitComparison_f_ι (K := K) n i).trans
      (brutalLeftTruncation_eval_colimit_iso_hom_ι (K := K) i n).symm

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
    rw [hjk, Category.assoc, hnk]
    simpa [Category.assoc]

section

-- Proof sketch: the tower consists of the intrinsic inclusions of the brutal left-truncation stages into
-- one another. Degreewise, every term stabilizes after finitely many stages, so the termwise
-- colimit is exactly the source complex `K`.
/-- Helper for Example 13.41.2: in each degree `i`, the evaluated brutal left-truncation tower
stabilizes and identifies its colimit with `K.X i`. -/
theorem brutalLeftTruncationColimitComparison_isIso :
    IsIso (brutalLeftTruncationColimitComparison K) := by
  -- TODO: reuse the commented degreewise stabilization argument for the evaluated cocones and then
  -- apply `HomologicalComplex.Hom.isIso_of_components`.
  sorry

-/

/-- The brutal left-truncation tower stabilizes degreewise, so its colimit maps isomorphically to
the source complex `K`. Under `[K.IsStrictlyLE 0]`, this is the source tower
`Y_0[0] ⟶ Y_1[1] ⟶ Y_2[2] ⟶ ⋯` from Example 13.41.2 (3). -/
theorem brutalLeftTruncationColimitComparison_isIso :
    IsIso (brutalLeftTruncationColimitComparison K) := by
  -- Proof comment: evaluate the tower in each degree, identify the resulting colimit with `K.X i`
  -- via stabilization, and then assemble the degreewise isomorphisms back into a complex map.
  have hcomponent : ∀ i : ℤ, IsIso ((brutalLeftTruncationColimitComparison K).f i) := fun i ↦ by
    let n : ℕ := Int.toNat (-i)
    have hn : -((n : ℕ) : ℤ) ≤ i :=
      brutalLeftTruncation_eventual_stage_le i
    let e :
        colimit (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) ≅
          K.X i :=
      IsColimit.coconePointUniqueUpToIso
        (colimit.isColimit
          (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))
        (brutalLeftTruncation_eval_stabilized_isColimit (K := K) i n hn)
    have hcolim :
        IsColimit (brutalLeftTruncationEvalCocone K i) :=
      brutalLeftTruncation_eval_stabilized_isColimit (K := K) i n hn
    have hcomp :
        (brutalLeftTruncationEvalColimitIso (K := K) i).hom ≫
            (brutalLeftTruncationColimitComparison K).f i =
          e.hom := by
      apply colimit.hom_ext
      intro m
      have hleg :
          colimit.ι
              (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) m ≫
                e.hom =
            brutalLeftTruncationInclusionComponent K m i := by
        simpa [e] using
          IsColimit.comp_coconePointUniqueUpToIso_hom
            (colimit.isColimit
              (brutalLeftTruncationTower K ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i))
            hcolim m
      exact (brutalLeftTruncation_eval_colimitComparison_hom_ι (K := K) i m).trans hleg.symm
    have hcomp' :
        (brutalLeftTruncationColimitComparison K).f i =
          (brutalLeftTruncationEvalColimitIso (K := K) i).inv ≫ e.hom := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦ (brutalLeftTruncationEvalColimitIso (K := K) i).inv ≫ t)
          hcomp
    rw [hcomp']
    infer_instance
  letI : ∀ i : ℤ, IsIso ((brutalLeftTruncationColimitComparison K).f i) := hcomponent
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

/-- Helper for Example 13.41.2: after shifting and rotating the stage short exact sequence, the
first edge is exactly the source-facing map `Y_{n + 1} ⟶ X_{n + 1}`. -/
private theorem boundedAbovePostnikovStageTriangleIso_comm₁ (n : ℕ) :
    (boundedAbovePostnikovStageTriangle K n).mor₁ ≫
        (boundedAbovePostnikovXShiftIso K (n + 1)).hom =
      (Iso.refl (boundedAbovePostnikovStageTriangle K n).obj₁).hom ≫
        (Triangle.mk
          (boundedAbovePostnikovToX K (n + 1))
          (boundedAbovePostnikovToNext K n)
          (boundedAbovePostnikovConnecting K n)).mor₁ := by
  -- Proof comment: after expanding the shifted-and-rotated stage triangle once, the first edge is
  -- literally the quotient map `Y_{n + 1} ⟶ X_{n + 1}` followed by the fixed shift isomorphism.
  simp [boundedAbovePostnikovStageTriangle, boundedAbovePostnikovToX, Category.assoc]

/-- Helper for Example 13.41.2: the second edge of the shifted-and-rotated stage triangle is the
source-facing map `X_{n + 1} ⟶ Y_n` after the canonical vertex identifications. -/
private theorem boundedAbovePostnikovStageTriangleIso_comm₂ (n : ℕ) :
    (boundedAbovePostnikovStageTriangle K n).mor₂ ≫
        (boundedAbovePostnikovStageTriangleObj3Iso K n).hom =
      (boundedAbovePostnikovXShiftIso K (n + 1)).hom ≫
        (Triangle.mk
          (boundedAbovePostnikovToX K (n + 1))
          (boundedAbovePostnikovToNext K n)
          (boundedAbovePostnikovConnecting K n)).mor₂ := by
  -- Proof comment: the second edge is just the stored rotated morphism once the third vertex is
  -- rewritten by `boundedAbovePostnikovStageTriangleObj3Iso`.
  simp [boundedAbovePostnikovToNext, Category.assoc]

/-- Helper for Example 13.41.2: the third edge of the shifted-and-rotated stage triangle is the
source-facing connecting map after the third-vertex identification. -/
private theorem boundedAbovePostnikovStageTriangleIso_comm₃ (n : ℕ) :
    (boundedAbovePostnikovStageTriangle K n).mor₃ ≫
        (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map (𝟙 _) =
      (boundedAbovePostnikovStageTriangleObj3Iso K n).hom ≫
        (Triangle.mk
          (boundedAbovePostnikovToX K (n + 1))
          (boundedAbovePostnikovToNext K n)
          (boundedAbovePostnikovConnecting K n)).mor₃ := by
  -- Proof comment: the third edge is definitionally the connecting map after inserting the
  -- identity shift on the first vertex.
  simp [boundedAbovePostnikovConnecting, Category.assoc]

/-- Helper for Example 13.41.2: the shifted-and-rotated triangle of the stage short exact
sequence is exactly the source-facing stage triangle
`Y_{n + 1} ⟶ X_{n + 1} ⟶ Y_n ⟶ Y_{n + 1}[1]`. -/
private noncomputable def boundedAbovePostnikovStageTriangleIso (n : ℕ) :
    boundedAbovePostnikovStageTriangle K n ≅
      Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) :=
  -- Proof comment: the stage triangle already has the right three objects after one shift and one
  -- rotation; only the second and third objects need to be rewritten by the fixed source-facing
  -- identifications `X_{n + 1}` and `Y_n`.
  Triangle.isoMk _ _
    (Iso.refl _)
    (boundedAbovePostnikovXShiftIso K (n + 1))
    (boundedAbovePostnikovStageTriangleObj3Iso K n)
    (boundedAbovePostnikovStageTriangleIso_comm₁ K n)
    (boundedAbovePostnikovStageTriangleIso_comm₂ K n)
    (boundedAbovePostnikovStageTriangleIso_comm₃ K n)

section

variable [K.IsStrictlyLE 0]

-- Proof sketch: the brutal left-truncation stages and their canonical short exact sequences define the
-- maps `Y_n ⟶ X_n`, `X_{n + 1} ⟶ Y_n`, and `Y_n ⟶ Y_{n + 1}[1]`; the shifted truncation triangles
-- give the distinguished triangles of the infinite Postnikov system, and the composites recover
-- the differentials `X_{n + 1} ⟶ X_n`.

/-

/-- The right end of the canonical bounded-above Postnikov system identifies `Y₀` with `X₀`. -/
/-- Helper for Example 13.41.2: when `K` is concentrated in degrees `≤ 0`, the stage-`0`
projection from the brutal truncation to the single complex is already an isomorphism of
cochain complexes. -/
private theorem brutalLeftTruncationToSingle_zero_isIso [K.IsStrictlyLE 0] :
    IsIso (brutalLeftTruncationToSingle K 0) := by
  let hcomponent : ∀ i : ℤ, IsIso ((brutalLeftTruncationToSingle K 0).f i) := fun i ↦ by
    by_cases hi : i = 0
    · subst hi
      -- At degree `0`, the projection is the canonical term identification followed by the
      -- single-complex self-isomorphism.
      rw [brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := 0)]
      exact IsIso.comp_isIso
    · rw [brutalLeftTruncationToSingle_component_eq_zero (K := K) (n := 0) hi]
      have hsrc : IsZero ((brutalLeftTruncationStage K 0).X i) := by
        by_cases hnonneg : 0 ≤ i
        · -- Above degree `0`, the source stage agrees with `K`, which vanishes by boundedness.
          refine IsZero.of_iso (K.isZero_of_isStrictlyLE 0 i (by omega)) ?_
          exact (brutalLeftTruncationXIso K 0 hnonneg).symm
        · -- Below degree `0`, the brutal truncation already vanishes.
          exact (brutalLeftTruncationStage K 0).isZero_of_isStrictlyGE 0 i (by omega)
      have htgt :
          IsZero
            ((boundedAbovePostnikovXComplex K 0).X i) := by
        -- Away from its support degree, the single complex is zero.
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) i hi
      exact hsrc.isIso htgt 0
  -- Proof comment: a cochain-complex map is an isomorphism once all of its degreewise components
  -- are isomorphisms.
  letI : ∀ i : ℤ, IsIso ((brutalLeftTruncationToSingle K 0).f i) := hcomponent
  exact HomologicalComplex.Hom.isIso_of_components (brutalLeftTruncationToSingle K 0)

/-- The right end of the canonical bounded-above Postnikov system identifies `Y₀` with `X₀`. -/
theorem boundedAbovePostnikovToX_zero_isIso :
    IsIso (boundedAbovePostnikovToX K 0) := sorry

/-- Each stage of the canonical bounded-above Postnikov system is a distinguished triangle. -/
theorem boundedAbovePostnikov_distinguished (n : ℕ) :
    Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) ∈
      distTriang (DerivedCategory 𝒜) := by
  -- Proof comment: first shift the standard short-exact-sequence triangle, then rotate once to
  -- match the stage-triangle ordering, and finally transport along the explicit stage comparison.
  refine isomorphic_distinguished _ ?_ _ (boundedAbovePostnikovStageTriangleIso K n).symm
  exact
    rot_of_distTriang _ <|
      Triangle.shift_distinguished _
        (DerivedCategory.triangleOfSES_distinguished
          (boundedAbovePostnikovStageShortExact K n))
        (-((n + 1 : ℕ) : ℤ))

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

/-- Helper for Example 13.41.2: the Postnikov composite agrees with the second edge of the
explicit shifted two-term differential triangle. -/
private theorem boundedAbovePostnikovComp_eq_singleDifferentialMor₂
    (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
        (boundedAbovePostnikovSingleDifferentialTriangle K n).mor₂ ≫
        (boundedAbovePostnikovXShiftIso K n).hom := by
  -- Route correction: read the stage-to-explicit comparison from the rotated triangle morphism,
  -- where the middle component is already the identity on the quotient term.
  let φ :
      DerivedCategory.triangleOfSES (boundedAbovePostnikovStageShortExact K n) ⟶
        DerivedCategory.triangleOfSES
          (boundedAbovePostnikovSingleDifferentialShortExact K n) :=
    DerivedCategory.triangleOfSES.map
      (boundedAbovePostnikovStageShortExact K n)
      (boundedAbovePostnikovSingleDifferentialShortExact K n)
      (boundedAbovePostnikovStageToSingleDifferentialHom K n)
  let φshift :
      ((shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).obj
          (DerivedCategory.triangleOfSES (boundedAbovePostnikovStageShortExact K n))) ⟶
        ((shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).obj
          (DerivedCategory.triangleOfSES
            (boundedAbovePostnikovSingleDifferentialShortExact K n))) :=
    (shiftFunctor (Triangle (DerivedCategory 𝒜)) (-((n + 1 : ℕ) : ℤ))).map φ
  let φrot :
      boundedAbovePostnikovStageTriangle K n ⟶
        boundedAbovePostnikovSingleDifferentialTriangle K n :=
    (Pretriangulated.rotate (DerivedCategory 𝒜)).map φshift
  have hφ := φrot.comm₂
  dsimp [φrot, φshift, φ] at hφ
  -- Postcompose the triangle identity with the fixed source/target identifications `X_{n+1}` and
  -- `Y_n ⟶ X_n` to recover the desired composite in source notation.
  simpa [boundedAbovePostnikovToNext, boundedAbovePostnikovToX,
    boundedAbovePostnikovStageTriangleObj3Iso, boundedAbovePostnikovStageTriangle,
    boundedAbovePostnikovSingleDifferentialTriangle, Category.assoc] using
    congrArg
      (fun k ↦
        (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
          k ≫
            (boundedAbovePostnikovXShiftIso K n).hom)
      hφ

/-- Helper for Example 13.41.2: rewriting the explicit triangle edge exposes the shifted
connecting morphism of the two-term short exact sequence. -/
private theorem boundedAbovePostnikovSingleDifferentialMor₂_eq_shiftedConnecting
    (n : ℕ) :
    (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
        (boundedAbovePostnikovSingleDifferentialTriangle K n).mor₂ ≫
        (boundedAbovePostnikovXShiftIso K n).hom =
      (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
        (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
          (-((n + 1 : ℕ) : ℤ))⟧' ≫
        (boundedAbovePostnikovXShiftIso K n).hom := by
  -- Rewrite the rotated triangle edge once; the remaining transport to `boundedAbovePostnikovXMap`
  -- is the only explicit differential computation left.
  rw [boundedAbovePostnikov_singleDifferential_rotated_mor₂]

/-- Helper for Example 13.41.2: after comparing the stage triangle with the explicit two-term
triangle, the Postnikov composite is already the shifted connecting morphism of the explicit
short exact sequence. -/
private theorem boundedAbovePostnikovComp_eq_shiftedConnecting
    (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
        (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
          (-((n + 1 : ℕ) : ℤ))⟧' ≫
        (boundedAbovePostnikovXShiftIso K n).hom := by
  -- First pass from the source-facing stage triangle to the explicit two-term triangle, then
  -- rewrite its second edge as the shifted connecting morphism.
  calc
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
        (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
          (boundedAbovePostnikovSingleDifferentialTriangle K n).mor₂ ≫
          (boundedAbovePostnikovXShiftIso K n).hom :=
      boundedAbovePostnikovComp_eq_singleDifferentialMor₂ (K := K) n
    _ =
        (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
          (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
            (-((n + 1 : ℕ) : ℤ))⟧' ≫
          (boundedAbovePostnikovXShiftIso K n).hom :=
      boundedAbovePostnikovSingleDifferentialMor₂_eq_shiftedConnecting (K := K) n

/-- The canonical bounded-above Postnikov maps recover the differentials
`X_{n + 1} ⟶ X_n`. -/
theorem boundedAbovePostnikov_comp (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      boundedAbovePostnikovXMap K n := by
  -- Route correction: the structural triangle comparison is now isolated in
  -- `boundedAbovePostnikovComp_eq_singleDifferentialMor₂`, so only the explicit shifted
  -- connecting morphism still needs to be normalized to the raw differential.
  calc
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
        (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
          (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
            (-((n + 1 : ℕ) : ℤ))⟧' ≫
          (boundedAbovePostnikovXShiftIso K n).hom :=
      boundedAbovePostnikovComp_eq_shiftedConnecting (K := K) n
    _ = boundedAbovePostnikovXMap K n := by
      -- TODO: compute the shifted connecting morphism of the explicit two-term short exact
      -- sequence via `DerivedCategory.descShortComplex_triangleOfSESδ`, then rewrite the result
      -- through `boundedAbovePostnikovXShiftIso` to recover the raw differential `K.d`.
      sorry

-/

/-- Helper for Example 13.41.2: when `K` is concentrated in degrees `≤ 0`, the stage-`0`
projection from the brutal truncation to the single complex is already an isomorphism of
cochain complexes. -/
private theorem brutalLeftTruncationToSingle_zero_isIso [K.IsStrictlyLE 0] :
    IsIso (brutalLeftTruncationToSingle K 0) := by
  -- Proof comment: check the canonical projection degreewise. At degree `0` it is the obvious
  -- identification, and away from degree `0` both source and target are zero.
  let hcomponent : ∀ i : ℤ, IsIso ((brutalLeftTruncationToSingle K 0).f i) := fun i ↦ by
    by_cases hi : i = 0
    · subst hi
      rw [brutalLeftTruncationToSingle_component_eq_cutoff (K := K) (n := 0)]
      exact IsIso.comp_isIso
    · rw [brutalLeftTruncationToSingle_component_eq_zero (K := K) (n := 0) hi]
      have hsrc : IsZero ((brutalLeftTruncationStage K 0).X i) := by
        by_cases hnonneg : 0 ≤ i
        · refine IsZero.of_iso (K.isZero_of_isStrictlyLE 0 i (by omega)) ?_
          exact (brutalLeftTruncationXIso K 0 hnonneg).symm
        · exact (brutalLeftTruncationStage K 0).isZero_of_isStrictlyGE 0 i (by omega)
      have htgt :
          IsZero
            ((boundedAbovePostnikovXComplex K 0).X i) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) i hi
      exact hsrc.isIso htgt 0
  -- Proof comment: a cochain-complex morphism is an isomorphism once all degreewise components
  -- are isomorphisms.
  letI : ∀ i : ℤ, IsIso ((brutalLeftTruncationToSingle K 0).f i) := hcomponent
  exact HomologicalComplex.Hom.isIso_of_components (brutalLeftTruncationToSingle K 0)

/-- The right end of the canonical bounded-above Postnikov system identifies `Y₀` with `X₀`. -/
theorem boundedAbovePostnikovToX_zero_isIso :
    IsIso (boundedAbovePostnikovToX K 0) := by
  -- Proof comment: `boundedAbovePostnikovToX K 0` is the quotient map to the cutoff term,
  -- followed by the fixed shift identification with `X₀`.
  dsimp [boundedAbovePostnikovToX]
  infer_instance

/-- Each stage of the canonical bounded-above Postnikov system is a distinguished triangle. -/
theorem boundedAbovePostnikov_distinguished (n : ℕ) :
    Triangle.mk
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n) ∈
      distTriang (DerivedCategory 𝒜) := by
  -- Proof comment: first shift the standard short-exact-sequence triangle, then rotate once to
  -- match the source ordering, and finally transport along the explicit stage comparison.
  refine isomorphic_distinguished _ ?_ _ (boundedAbovePostnikovStageTriangleIso K n).symm
  exact
    rot_of_distTriang _ <|
      Triangle.shift_distinguished _
        (DerivedCategory.triangleOfSES_distinguished
          (boundedAbovePostnikovStageShortExact K n))
        (-((n + 1 : ℕ) : ℤ))

/-- The canonical bounded-above Postnikov maps recover the differentials
`X_{n + 1} ⟶ X_n`. -/
theorem boundedAbovePostnikov_comp (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      boundedAbovePostnikovXMap K n := by
  -- Route correction: the structural triangle comparison is already isolated above, so the only
  -- remaining step is to normalize the explicit shifted connecting morphism to the raw
  -- differential map `K.d (-(n + 1)) (-n)`.
  calc
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
        (boundedAbovePostnikovXShiftIso K (n + 1)).inv ≫
          (triangleOfSESδ (boundedAbovePostnikovSingleDifferentialShortExact K n))⟦
            (-((n + 1 : ℕ) : ℤ))⟧' ≫
          (boundedAbovePostnikovXShiftIso K n).hom :=
      boundedAbovePostnikovComp_eq_shiftedConnecting (K := K) n
    _ = boundedAbovePostnikovXMap K n := by
      -- TODO: compute the shifted connecting morphism of the explicit two-term short exact
      -- sequence via `DerivedCategory.descShortComplex_triangleOfSESδ_assoc`, then rewrite the
      -- resulting map through `boundedAbovePostnikovXShiftIso` to recover the raw differential.
      sorry

private theorem boundedAboveTermSequence_delta₀ (n : ℕ) :
    (boundedAboveTermSequence K (n + 1)).δ₀ = boundedAboveTermSequence K n := by
  -- Proof comment: forgetting the first arrow in the reversed finite row exactly shifts the
  -- bookkeeping index by one.
  apply ComposableArrows.ext
  · intro i
    simp [boundedAboveTermSequence, boundedAboveTermIndex_succ]
  · intro i hi
    simp [boundedAboveTermSequence, boundedAboveTermSequenceMap, boundedAboveTermIndex_succ,
      ComposableArrows.mkOfObjOfMapSucc_map_succ]

/-- Helper for Example 13.41.2: the leftmost differential of the finite row
`boundedAboveTermSequence K (n + 1)` is the source-facing map `X_{n + 1} ⟶ X_n`. -/
private theorem boundedAboveTermSequence_head_comp (n : ℕ) :
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
      (boundedAboveTermSequence K (n + 1)).map' 0 1 := by
  -- Proof comment: the leftmost arrow in `boundedAboveTermSequence K (n + 1)` is by definition
  -- the differential `X_{n + 1} ⟶ X_n`.
  calc
    boundedAbovePostnikovToNext K n ≫ boundedAbovePostnikovToX K n =
        boundedAbovePostnikovXMap K n :=
      boundedAbovePostnikov_comp (K := K) n
    _ = (boundedAboveTermSequence K (n + 1)).map' 0 1 := by
      simp [boundedAboveTermSequence, boundedAboveTermSequenceMap,
        ComposableArrows.mkOfObjOfMapSucc_map_succ]

private noncomputable def boundedAboveTermSequencePostnikovSystemZero :
    PostnikovSystem (boundedAboveTermSequence K 0) := by
  letI : IsIso (boundedAbovePostnikovToX K 0) := by
    exact boundedAbovePostnikovToX_zero_isIso (K := K)
  exact PostnikovSystem.mk₀ (boundedAbovePostnikovY K 0) (boundedAbovePostnikovToX K 0)

/-- Example 13.41.2 (1): each finite row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
inherits the canonical finite `PostnikovSystem` coming from the brutal truncation tower. -/
@[stacks 0D8Z]
noncomputable def boundedAboveTermSequencePostnikovSystem :
    (n : ℕ) → PostnikovSystem (boundedAboveTermSequence K n)
  | 0 => boundedAboveTermSequencePostnikovSystemZero (K := K)
  | n + 1 =>
      let tail : PostnikovSystem ((boundedAboveTermSequence K (n + 1)).δ₀) := by
        rw [boundedAboveTermSequence_delta₀ (K := K) n]
        exact boundedAboveTermSequencePostnikovSystem n
      PostnikovSystem.mkSucc tail
        (boundedAbovePostnikovY K (n + 1))
        (boundedAbovePostnikovToX K (n + 1))
        (boundedAbovePostnikovToNext K n)
        (boundedAbovePostnikovConnecting K n)
        (boundedAbovePostnikov_distinguished (K := K) n)
        (by
          -- Proof comment: after rewriting the forgotten-tail row by `boundedAboveTermSequence_delta₀`,
          -- the recursive head comparison is exactly `boundedAboveTermSequence_head_comp`.
          simpa [tail] using boundedAboveTermSequence_head_comp (K := K) n)

/-- The canonical finite `PostnikovSystem` on the row
`X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0`
has auxiliary object `Y_{n - i}` at index `i`. -/
@[simp] theorem boundedAboveTermSequencePostnikovSystem_apply
    (n : ℕ) (i : Fin (n + 1)) :
    boundedAboveTermSequencePostnikovSystem K n i =
      boundedAbovePostnikovY K (n - i.1) := by
  induction n generalizing i with
  | zero =>
      -- Proof comment: the zero-length row has a single auxiliary object `Y₀`.
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      simp [boundedAboveTermSequencePostnikovSystem, boundedAboveTermSequencePostnikovSystemZero]
  | succ n ih =>
      -- Proof comment: at the head we read off `Y_{n + 1}`, and on successor indices the claim
      -- is inherited from the tail Postnikov system.
      cases i using Fin.cases with
      | zero =>
          simp [boundedAboveTermSequencePostnikovSystem]
      | succ j =>
          simpa [boundedAboveTermIndex_succ, boundedAboveTermSequencePostnikovSystem] using ih j

end

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (K : CochainComplex 𝒜 ℤ)
variable [HasColimitsOfShape ℕ 𝒜]

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

section

variable [HasExactColimitsOfShape ℕ 𝒜]

/-- Helper for Example 13.41.2: exact sequential colimits imply the `CountableAB4` condition
needed to form countable coproducts after passing to `DerivedCategory.Q`. -/
local instance exactSequentialColimits_countableAB4 : CountableAB4 𝒜 := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 𝒜

/-- Helper for Example 13.41.2: the localized brutal left-truncation tower has a coproduct under
exact sequential colimits. -/
local noncomputable instance brutalLeftTruncationTower_hasCoproduct :
    HasCoproduct (brutalLeftTruncationTower K ⋙ Q).obj := by
  -- TODO: this is the precise missing Chapter 13 coproduct owner packaged in
  -- `derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts` from the earlier
  -- telescope file. That prerequisite is currently unavailable in this dependency-closed slice.
  sorry

/-- Companion for Example 13.41.2: once the localized tower coproduct exists, the termwise
colimit of a sequential system of cochain complexes is a homotopy colimit of the induced diagram
in the derived category. -/
theorem termwise_colimit_is_homotopy_colimit
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasCoproduct (S ⋙ Q).obj] :
    IsHomotopyColimitOf (S ⋙ Q) (Q.obj (colimit S)) := by
  -- TODO: the missing ingredient is the telescope presentation from Lemma 13.33.7, which depends
  -- on the unavailable Chapter 13 coproduct-preservation owner for `Q`.
  sorry

/-- Example 13.41.2 (2): under exact sequential colimits, every cochain complex concentrated in
degrees `≤ 0` is a homotopy colimit of its brutal left-truncation tower, i.e. of the source tower
`Q(Y_0[0]) ⟶ Q(Y_1[1]) ⟶ Q(Y_2[2]) ⟶ ⋯`. -/
@[stacks 0D8Z]
theorem brutalLeftTruncation_isHomotopyColimitOf [K.IsStrictlyLE 0] :
    let _ : HasCoproduct (brutalLeftTruncationTower K ⋙ Q).obj := by infer_instance
    IsHomotopyColimitOf
      (brutalLeftTruncationTower K ⋙ Q)
      (Q.obj K) := by
  let _ : HasCoproduct (brutalLeftTruncationTower K ⋙ Q).obj := by infer_instance
  let e : Q.obj (colimit (brutalLeftTruncationTower K)) ≅ Q.obj K :=
    asIso (Q.map (brutalLeftTruncationColimitComparison K))
  rcases termwise_colimit_is_homotopy_colimit
      (𝒜 := 𝒜) (K := brutalLeftTruncationTower K) with ⟨g, h, hdist⟩
  refine ⟨g ≫ e.hom, e.inv ≫ h, ?_⟩
  -- Proof comment: once the telescope presentation is available for the termwise colimit, the
  -- brutal-truncation colimit comparison transports it to `Q.obj K`.
  refine isomorphic_distinguished _ hdist _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · simp [Category.assoc]
  · simp [Category.assoc]
  · simp [Category.assoc]

end

end

end CategoryTheory
