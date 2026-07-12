import Mathlib
import StacksProject_2024.Chap13.Lemma_13_9_5
import StacksProject_2024.Chap13.Lemma_13_10_7
import StacksProject_2024.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CochainComplex

noncomputable section

universe v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/-
Domain-style sampling for Lemma `13.29.1`.
- primary domain: sequential upper truncation towers of cochain complexes together with compatible
  bounded-above resolutions in an object property;
- sampled owner declarations:
  `Over` for objects over a fixed diagram in a functor category,
  `Functor.ofSequence` / `NatTrans.ofSequence` for sequential diagrams and cocones,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn` from `Lemma_13_15_4` for the stagewise bounded-above
  resolution predicate,
  `LowerTruncationResolutionSystem` from `Lemma_13_29_3` as the nearby dual source-facing pattern;
- best owner abstraction: the intrinsic tower data is an object of
  `Over (upperTruncationDiagram K)`, i.e. a sequential diagram together with a natural
  transformation into the canonical upper truncation tower;
- primitive-vs-derived split:
  primitive data: the over-object `T : Over (upperTruncationDiagram K)` together with the proof
    fields that each stage and each transition map satisfy the textbook conditions;
  derived API: the source-facing accessors `T.diagram` and `T.comparison`, then the stage complex
    `T.stage n`, the step map `T.step n`, the stage map `T.toTarget n`, and the cocone/colimit
    comparison built from the owner abstraction.

Source/core/bridge triage:
- source-facing: `UpperTruncationResolutionTower` and the existence theorem below;
- core/canonical: `Over (upperTruncationDiagram K)` and
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- bridge/view: the accessors `diagram`, `comparison`, `stage`, `step`, `toTarget`, `cocone`, and
  `fromColimit`.
-/

/-- The stage `τ_{\le n + 1} K^•` in the upper truncation tower of a cochain complex. The index
`0` corresponds to `τ_{\le 1} K^•`. -/
abbrev upperTruncationStage (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  K.truncLE ((n : ℤ) + 1)

/-- The canonical transition map `τ_{\le n + 1} K^• ⟶ τ_{\le n + 2} K^•` in the upper truncation
tower of a cochain complex. -/
noncomputable abbrev truncLEStep (K : CochainComplex A ℤ) (n : ℕ) :
    upperTruncationStage K n ⟶ upperTruncationStage K (n + 1) :=
  letI : (upperTruncationStage K n).IsStrictlyLE ((n : ℤ) + 2) :=
    (upperTruncationStage K n).isStrictlyLE_of_le ((n : ℤ) + 1) ((n : ℤ) + 2) (by simp)
  inv ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2)

/-- The canonical inclusion of the `n`th stage of the upper truncation tower into `K^•`. -/
abbrev upperTruncationInclusion (K : CochainComplex A ℤ) (n : ℕ) :
    upperTruncationStage K n ⟶ K :=
  K.ιTruncLE ((n : ℤ) + 1)

/-- Helper for Lemma 13.29.1: the inclusion of the `n`th upper truncation into `K^•` is
compatible with truncating once more. -/
theorem upperTruncationInclusion_succ_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫ K.ιTruncLE ((n : ℤ) + 1) =
      CochainComplex.truncLEMap (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2) ≫
        K.ιTruncLE ((n : ℤ) + 2) := by
  -- Proof comment: this is the standard naturality square for `ιTruncLE` specialized to the
  -- canonical map `τ_{\le n + 1} K^• ⟶ K^•`.
  simpa [upperTruncationStage] using
    (ιTruncLE_naturality (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2)).symm

-- Proof sketch: rewrite the composite after the inserted inverse by the specialized naturality
-- lemma, and then cancel the inverse against the higher truncation inclusion.
/-- The truncation transition map and the canonical inclusions into `K^•` form a commutative
square. -/
theorem truncLEStep_comp_ιTruncLE (K : CochainComplex A ℤ) (n : ℕ) :
    CommSq
      (upperTruncationInclusion K n)
      (truncLEStep K n)
      (𝟙 K)
      (upperTruncationInclusion K (n + 1)) := by
  letI : (upperTruncationStage K n).IsStrictlyLE ((n : ℤ) + 2) :=
    (upperTruncationStage K n).isStrictlyLE_of_le ((n : ℤ) + 1) ((n : ℤ) + 2) (by simp)
  refine CommSq.mk ?_
  -- Proof comment: replace the truncated comparison by the naturality square from the helper
  -- lemma, then cancel the inserted inverse against the higher truncation inclusion.
  dsimp [upperTruncationInclusion, truncLEStep]
  have hstage : K.ιTruncLE (((n : ℤ) + 1) + 1) = K.ιTruncLE ((n : ℤ) + 2) := by
    rfl
  rw [Category.comp_id, hstage]
  calc
    K.ιTruncLE ((n : ℤ) + 1)
        = inv ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫
            (((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫ K.ιTruncLE ((n : ℤ) + 1)) := by
          simp
    _ = inv ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫
          (CochainComplex.truncLEMap (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2) ≫
            K.ιTruncLE ((n : ℤ) + 2)) := by
          rw [upperTruncationInclusion_succ_naturality]
    _ = (inv ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫
          CochainComplex.truncLEMap (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2)) ≫
          K.ιTruncLE ((n : ℤ) + 2) := by
          rw [Category.assoc]

/-- The direct system `τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ ⋯` of upper truncations of `K^•`. -/
noncomputable abbrev upperTruncationDiagram (K : CochainComplex A ℤ) :
    ℕ ⥤ CochainComplex A ℤ :=
  Functor.ofSequence (truncLEStep K)

/-- A tower resolving the upper truncations `τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ ⋯` by bounded-above
cochain complexes with terms in an object property `P`. The index `0` corresponds to the textbook
complex `P_1^•`. -/
structure UpperTruncationResolutionTower
    (P : ObjectProperty A) (K : CochainComplex A ℤ) extends Over (upperTruncationDiagram K) where
  /-- Each stage is a bounded-above complex with terms in `P`, and the comparison to the
  corresponding truncation is termwise epimorphic and a quasi-isomorphism. -/
  isResolutionStage (n : ℕ) :
    IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P ((n : ℤ) + 1)
      (upperTruncationStage K n) (left.obj n) (hom.app n)
  /-- Each transition map `P_{n + 1}^• ⟶ P_{n + 2}^•` is termwise split monomorphic. -/
  termwiseSplitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((left.map (homOfLE (Nat.le_add_right n 1))).f i)
  /-- Each degreewise cokernel `P_{n + 2}^i / P_{n + 1}^i` again lies in `P`. -/
  cokernel_mem (n : ℕ) (i : ℤ) :
    P (cokernel ((left.map (homOfLE (Nat.le_add_right n 1))).f i))

namespace UpperTruncationResolutionTower

section

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Helper for Lemma 13.29.1: explicit stagewise data over the upper truncation diagram packages
into an `UpperTruncationResolutionTower`. -/
noncomputable def ofSequence
    (stage : ℕ → CochainComplex A ℤ)
    (step : ∀ n : ℕ, stage n ⟶ stage (n + 1))
    (comparison : ∀ n : ℕ, stage n ⟶ upperTruncationStage K n)
    (isResolutionStage : ∀ n : ℕ,
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P ((n : ℤ) + 1)
        (upperTruncationStage K n) (stage n) (comparison n))
    (step_comp_comparison : ∀ n : ℕ,
      CommSq (comparison n) (step n) (truncLEStep K n) (comparison (n + 1)))
    (termwiseSplitMono : ∀ n : ℕ, ∀ i : ℤ, IsSplitMono ((step n).f i))
    (cokernel_mem : ∀ n : ℕ, ∀ i : ℤ, P (cokernel ((step n).f i))) :
    UpperTruncationResolutionTower P K := by
  -- Proof comment: build the underlying sequential diagram and its comparison to the canonical
  -- upper-truncation tower directly from the supplied data.
  refine
    { left := Functor.ofSequence step
      right := ⟨⟨⟩⟩
      hom := NatTrans.ofSequence comparison (fun n ↦ by
        simpa [upperTruncationDiagram, Functor.ofSequence_map_homOfLE_succ] using
          (step_comp_comparison n).w.symm)
      isResolutionStage := isResolutionStage
      termwiseSplitMono := ?_
      cokernel_mem := ?_ }
  · intro n i
    -- Proof comment: the successor map in `Functor.ofSequence step` is definitionally `step n`.
    simpa [Functor.ofSequence_map_homOfLE_succ] using termwiseSplitMono n i
  · intro n i
    -- Proof comment: the same definitional identification rewrites the cokernel condition.
    simpa [Functor.ofSequence_map_homOfLE_succ] using cokernel_mem n i

/-- The underlying direct system `P_1^• ⟶ P_2^• ⟶ \cdots` of an upper truncation resolution
tower. -/
abbrev diagram
    (T : UpperTruncationResolutionTower P K) :
    ℕ ⥤ CochainComplex A ℤ :=
  T.left

/-- The natural comparison from a chosen upper truncation resolution tower to the canonical upper
truncation tower. -/
abbrev comparison
    (T : UpperTruncationResolutionTower P K) :
    T.diagram ⟶ upperTruncationDiagram K :=
  T.hom

/-- The `n`th stage `P_{n + 1}^•` of an upper truncation resolution tower. -/
abbrev stage
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CochainComplex A ℤ :=
  T.diagram.obj n

/-- The transition map `P_{n + 1}^• ⟶ P_{n + 2}^•` at stage `n` of the resolution tower. -/
abbrev step
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    T.stage n ⟶ T.stage (n + 1) :=
  T.diagram.map (homOfLE (Nat.le_add_right n 1))

/-- The stage map `P_{n + 1}^• ⟶ K^•` obtained by composing the comparison with the canonical
upper truncation inclusion. -/
abbrev toTarget
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    T.stage n ⟶ K :=
  T.comparison.app n ≫ upperTruncationInclusion K n

/-- Helper for Lemma 13.29.1: the `n`th stage comparison in an upper truncation resolution tower
is a quasi-isomorphism. -/
theorem comparison_quasiIso
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    QuasiIso (T.comparison.app n) := by
  -- Read off the quasi-isomorphism field from the stored stagewise resolution data.
  exact (T.isResolutionStage n).quasiIso

/-- Helper for Lemma 13.29.1: the `n`th stage of an upper truncation resolution tower is bounded
above by degree `n + 1`. -/
theorem stage_isStrictlyLE
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    (T.stage n).IsStrictlyLE ((n : ℤ) + 1) := by
  -- This is the bounded-above part of the stagewise resolution package.
  exact (T.isResolutionStage n).strictlyLE

/-- Helper for Lemma 13.29.1: every term of the `n`th stage belongs to the object property `P`. -/
theorem stage_term_mem
    (T : UpperTruncationResolutionTower P K) (n : ℕ) (i : ℤ) :
    P ((T.stage n).X i) := by
  -- The resolution datum stores the source-faithful termwise membership in `P`.
  exact (T.isResolutionStage n).term_mem i

/-- Helper for Lemma 13.29.1: the `n`th stage comparison is termwise epimorphic. -/
theorem comparison_epi
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    Epi (T.comparison.app n) := by
  -- Promote the stored termwise epimorphy to an epimorphism of cochain complexes.
  exact (T.isResolutionStage n).epi

/-- Helper for Lemma 13.29.1: each successor map in the tower is termwise split monic. -/
theorem step_f_isSplitMono
    (T : UpperTruncationResolutionTower P K) (n : ℕ) (i : ℤ) :
    IsSplitMono ((T.step n).f i) := by
  -- Rewrite the successor map back to the owner field recording degreewise split monomorphy.
  simpa [UpperTruncationResolutionTower.step] using T.termwiseSplitMono n i

/-- Helper for Lemma 13.29.1: the degreewise cokernel of a successor map again belongs to `P`. -/
theorem step_cokernel_mem
    (T : UpperTruncationResolutionTower P K) (n : ℕ) (i : ℤ) :
    P (cokernel ((T.step n).f i)) := by
  -- Rewrite the successor map back to the owner field recording the cokernel condition.
  simpa [UpperTruncationResolutionTower.step] using T.cokernel_mem n i

-- Proof sketch: this is the naturality square of `T.comparison` for the successor morphism
-- `n ⟶ n + 1`, rewritten using `upperTruncationDiagram`.
/-- The transition maps of an upper truncation resolution tower are compatible with the canonical
upper truncation tower. -/
theorem step_comp_comparison
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CommSq (T.comparison.app n) (T.step n) (truncLEStep K n) (T.comparison.app (n + 1)) := by
  refine CommSq.mk ?_
  simpa [UpperTruncationResolutionTower.step, upperTruncationDiagram] using
    (T.comparison.naturality (homOfLE (Nat.le_add_right n 1))).symm

-- Proof sketch: compose `step_comp_comparison` with `truncLEStep_comp_ιTruncLE`.
/-- The stage maps `P_{n + 1}^• ⟶ K^•` and the transition maps of the tower form commutative
squares. -/
theorem step_comp_toTarget
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CommSq
      (T.toTarget n)
      (T.step n)
      (𝟙 K)
      (T.toTarget (n + 1)) := by
  simpa [UpperTruncationResolutionTower.toTarget] using
    CommSq.horiz_comp
      (UpperTruncationResolutionTower.step_comp_comparison T n)
      (truncLEStep_comp_ιTruncLE K n)

/-- The canonical cocone from an upper truncation resolution tower to `K^•`. -/
noncomputable def cocone
    (T : UpperTruncationResolutionTower P K) :
    Cocone T.diagram where
  pt := K
  ι := NatTrans.ofSequence
    (fun n ↦ T.toTarget n)
    (fun n ↦ by
      simpa [UpperTruncationResolutionTower.step] using
        (UpperTruncationResolutionTower.step_comp_toTarget T n).w.symm)

/-- The canonical morphism from the sequential colimit of an upper truncation resolution tower to
`K^•`. -/
noncomputable abbrev fromColimit
    (T : UpperTruncationResolutionTower P K) [HasColimit T.diagram] :
    colimit T.diagram ⟶ K :=
  colimit.desc T.diagram T.cocone

-- Proof sketch: apply `colimit.ι_desc` to the canonical cocone `T.cocone`.
/-- Composing the `n`th colimit inclusion with the canonical map to `K^•` recovers the stagewise
comparison to the `n`th upper truncation followed by the truncation inclusion. -/
theorem ι_comp_fromColimit
    (T : UpperTruncationResolutionTower P K) [HasColimit T.diagram] (n : ℕ) :
    colimit.ι T.diagram n ≫ T.fromColimit = T.toTarget n := by
  -- Read the defining leg of `colimit.desc` on the `n`th cocone morphism.
  rw [UpperTruncationResolutionTower.fromColimit]
  change colimit.ι T.diagram n ≫ colimit.desc T.diagram T.cocone = T.cocone.ι.app n
  exact colimit.ι_desc (c := T.cocone) (j := n)

end

end UpperTruncationResolutionTower

/-- Helper for Lemma 13.29.1: one resolved stage over `τ_{\le n + 1} K^•`. -/
structure UpperTruncationStageData
    (P : ObjectProperty A) (K : CochainComplex A ℤ) (n : ℕ) where
  complex : CochainComplex A ℤ
  comparison : complex ⟶ upperTruncationStage K n
  isResolution :
    IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P ((n : ℤ) + 1)
      (upperTruncationStage K n) complex comparison

/-- Helper for Lemma 13.29.1: Lemma `13.15.4` provides the initial stage over `τ_{\le 1} K^•`.
-/
theorem exists_zeroUpperTruncationStageData
    (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]
    (K : CochainComplex A ℤ) :
    Nonempty (UpperTruncationStageData P K 0) := by
  -- Proof comment: resolve the first upper truncation directly with the bounded-above
  -- termwise-epimorphic replacement theorem.
  have htrunc : (upperTruncationStage K 0).IsStrictlyLE 1 := by
    simpa [upperTruncationStage] using (show (K.truncLE 1).IsStrictlyLE 1 by infer_instance)
  obtain ⟨Q, α, hα⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
      P 1 (upperTruncationStage K 0) htrunc
  refine ⟨⟨Q, α, ?_⟩⟩
  simpa using hα

/-- Helper for Lemma 13.29.1: a chosen initial stage over `τ_{\le 1} K^•`. -/
noncomputable def zeroUpperTruncationStageData
    (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]
    (K : CochainComplex A ℤ) :
    UpperTruncationStageData P K 0 :=
  Classical.choice (exists_zeroUpperTruncationStageData P K)

/-- Helper for Lemma 13.29.1: the mapping cone of a map between complexes bounded above by `a`
and `b` is bounded above by `max a b`. -/
private theorem mappingCone_isStrictlyLE_of_isStrictlyLE
    {K L : CochainComplex A ℤ} (f : K ⟶ L) {a b : ℤ}
    (hK : K.IsStrictlyLE a) (hL : L.IsStrictlyLE b) :
    (mappingCone f).IsStrictlyLE (max a b) := by
  -- Proof comment: a cone term is the biproduct of `K.X (i + 1)` and `L.X i`, so once `i` is
  -- above both cutoffs both summands vanish.
  rw [isStrictlyLE_iff]
  intro i hi
  let _ : K.IsStrictlyLE a := hK
  let _ : L.IsStrictlyLE b := hL
  rw [mappingCone.isZero_X_iff]
  refine ⟨?_, ?_⟩
  · exact K.isZero_of_isStrictlyLE a (i + 1) (by omega)
  · exact L.isZero_of_isStrictlyLE b i (lt_of_le_of_lt (le_max_right _ _) hi)

/-- Helper for Lemma 13.29.1: resolving the actual cone of the successor comparison reduces the
remaining successor step to a triangle comparison problem. -/
private theorem successorConeResolution
    (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n) :
    ∃ (Q : CochainComplex A ℤ)
      (ρ : Q ⟶ mappingCone (D.comparison ≫ truncLEStep K n)),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P ((n : ℤ) + 2)
        (mappingCone (D.comparison ≫ truncLEStep K n)) Q ρ := by
  let a : D.complex ⟶ upperTruncationStage K (n + 1) := D.comparison ≫ truncLEStep K n
  have hsource : D.complex.IsStrictlyLE ((n : ℤ) + 1) := D.isResolution.strictlyLE
  have htarget : (upperTruncationStage K (n + 1)).IsStrictlyLE ((n : ℤ) + 2) := by
    -- Proof comment: the next upper truncation is definitionally cut off above `n + 2`.
    simpa [upperTruncationStage] using
      (show (K.truncLE ((n : ℤ) + 2)).IsStrictlyLE ((n : ℤ) + 2) by infer_instance)
  have hcone : (mappingCone a).IsStrictlyLE ((n : ℤ) + 2) := by
    -- Proof comment: here the larger cutoff is already `n + 2`, so the maximum collapses.
    simpa [max_eq_right (by omega : ((n : ℤ) + 1) ≤ ((n : ℤ) + 2))] using
      (mappingCone_isStrictlyLE_of_isStrictlyLE a hsource htarget)
  -- Proof comment: Lemma `13.15.4` now resolves the cone by a bounded-above termwise-epic
  -- quasi-isomorphism with terms in `P`.
  obtain ⟨Q, ρ, hρ⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
      P ((n : ℤ) + 2) (mappingCone a) hcone
  exact ⟨Q, ρ, hρ⟩

/-- Helper for Lemma 13.29.1: the resolved cone over the successor comparison determines the
comparison of distinguished triangles in the homotopy category. -/
private theorem successorTriangleComparison
    {P : ObjectProperty A} [P.ContainsZero] [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n)
    {R : CochainComplex A ℤ}
    (ρ : R ⟶ mappingCone (D.comparison ≫ truncLEStep K n)) :
    ∃ (Y : HomotopyCategory A (ComplexShape.up ℤ))
      (stepQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj D.complex) ⟶ Y)
      (qQ : Y ⟶ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R))
      (βQ : Y ⟶
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          (upperTruncationStage K (n + 1)))),
      Triangle.mk stepQ qQ
          (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ρ) ≫
            (CochainComplex.mappingCone.triangleh (D.comparison ≫ truncLEStep K n)).mor₃) ∈
        distTriang (HomotopyCategory A (ComplexShape.up ℤ)) ∧
      stepQ ≫ βQ =
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (D.comparison ≫ truncLEStep K n) ∧
      qQ ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ρ =
        βQ ≫ (CochainComplex.mappingCone.triangleh (D.comparison ≫ truncLEStep K n)).mor₂ := by
  let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let a : D.complex ⟶ upperTruncationStage K (n + 1) := D.comparison ≫ truncLEStep K n
  let δ : (HoQ.obj R) ⟶ ((HoQ.obj D.complex)⟦(1 : ℤ)⟧) :=
    HoQ.map ρ ≫ (CochainComplex.mappingCone.triangleh a).mor₃
  -- Proof comment: complete the third morphism `δ` to a distinguished triangle in `K(A)`.
  obtain ⟨Y, stepQ, qQ, hTδ⟩ := Pretriangulated.distinguished_cocone_triangle₂ δ
  have hTcone :
      CochainComplex.mappingCone.triangleh a ∈
        distTriang (HomotopyCategory A (ComplexShape.up ℤ)) := by
    -- Proof comment: the canonical mapping-cone triangle is distinguished.
    simpa using HomotopyCategory.mappingCone_triangleh_distinguished a
  have hcomm₃ :
      (Triangle.mk stepQ qQ δ).mor₃ ≫
          (shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)).map
            (𝟙 (HoQ.obj D.complex)) =
        HoQ.map ρ ≫ (CochainComplex.mappingCone.triangleh a).mor₃ := by
    -- Proof comment: this is exactly how `δ` was defined.
    simp [δ]
  -- Proof comment: `TR3` supplies the middle comparison map to the mapping-cone triangle.
  obtain ⟨βQ, hβ₁, hβ₂⟩ :=
    complete_distinguished_triangle_morphism₂
      (Triangle.mk stepQ qQ δ)
      (CochainComplex.mappingCone.triangleh a)
      hTδ hTcone
      (𝟙 (HoQ.obj D.complex))
      (HoQ.map ρ)
      hcomm₃
  exact ⟨Y, stepQ, qQ, βQ, by simpa [a, δ] using hTδ,
    by simpa [a] using hβ₁,
    by simpa [a, δ] using hβ₂⟩

/-- Helper for Lemma 13.29.1: the middle object in the successor-triangle comparison can be
chosen to be the homotopy-category image of an actual cochain complex. -/
private theorem successorTriangleComparisonRepresentableMiddle
    {P : ObjectProperty A} [P.ContainsZero] [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n)
    {R : CochainComplex A ℤ}
    (ρ : R ⟶ mappingCone (D.comparison ≫ truncLEStep K n)) :
    ∃ (Yc : CochainComplex A ℤ)
      (stepQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj D.complex) ⟶
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc))
      (qQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc) ⟶
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R))
      (βQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc) ⟶
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          (upperTruncationStage K (n + 1)))),
      Triangle.mk stepQ qQ
          (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ρ) ≫
            (CochainComplex.mappingCone.triangleh (D.comparison ≫ truncLEStep K n)).mor₃) ∈
        distTriang (HomotopyCategory A (ComplexShape.up ℤ)) ∧
      stepQ ≫ βQ =
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (D.comparison ≫ truncLEStep K n) ∧
      qQ ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ρ =
        βQ ≫ (CochainComplex.mappingCone.triangleh (D.comparison ≫ truncLEStep K n)).mor₂ := by
  -- Proof comment: first build the abstract triangle comparison in the homotopy category.
  obtain ⟨Y, stepQ, qQ, βQ, hTQ, hβ₁, hβ₂⟩ := successorTriangleComparison D ρ
  -- Proof comment: then rewrite the middle vertex by choosing a literal cochain-complex
  -- representative of `Y`.
  obtain ⟨Yc, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  exact ⟨Yc, stepQ, qQ, βQ, hTQ, hβ₁, hβ₂⟩

/-- Helper for Lemma 13.29.1: the middle object of a degreewise split short complex inherits the
termwise object property from its two endpoint complexes. -/
private theorem degreewiseSplitMiddle_term_mem
    {P : ObjectProperty A} [P.IsClosedUnderFiniteCoproducts] [P.IsClosedUnderIsomorphisms]
    {K L M : CochainComplex A ℤ}
    {f : K ⟶ L} {g : L ⟶ M} {hfg : f ≫ g = 0}
    (σ : ∀ i : ℤ,
      ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)
    (hK : ∀ i : ℤ, P (K.X i))
    (hM : ∀ i : ℤ, P (M.X i)) :
    ∀ i : ℤ, P (L.X i) := by
  intro i
  -- Proof comment: the chosen splitting identifies the middle term with the biproduct of the
  -- two endpoint terms in degree `i`.
  let e : L.X i ≅ K.X i ⊞ M.X i := by
    simpa using (σ i).isoBinaryBiproduct
  exact P.prop_of_iso e.symm <|
    P.prop_of_iso (biprod.isoCoprod (K.X i) (M.X i)).symm <|
      P.prop_coprod (K.X i) (M.X i) (hK i) (hM i)

/-- Helper for Lemma 13.29.1: the middle complex of a degreewise split short complex is bounded
above by a common bound for the endpoint complexes. -/
private theorem degreewiseSplitMiddle_isStrictlyLE
    {K L M : CochainComplex A ℤ}
    {f : K ⟶ L} {g : L ⟶ M} {hfg : f ≫ g = 0}
    (σ : ∀ i : ℤ,
      ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)
    {a : ℤ} (hK : K.IsStrictlyLE a) (hM : M.IsStrictlyLE a) :
    L.IsStrictlyLE a := by
  rw [isStrictlyLE_iff]
  intro i hi
  -- Proof comment: the same splitting identifies `L.X i` with a biproduct whose two summands
  -- already vanish above the common cutoff.
  let e : L.X i ≅ K.X i ⊞ M.X i := by
    simpa using (σ i).isoBinaryBiproduct
  exact IsZero.of_iso
    ((biprod_isZero_iff (K.X i) (M.X i)).2
      ⟨K.isZero_of_isStrictlyLE a i hi, M.isZero_of_isStrictlyLE a i hi⟩)
    e

/-- Helper for Lemma 13.29.1: in a degreewise split short complex, each degreewise cokernel of
the first map is canonically the third term. -/
private theorem degreewiseSplitStep_cokernel_mem
    (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms]
    {K L M : CochainComplex A ℤ}
    {f : K ⟶ L} {g : L ⟶ M} {hfg : f ≫ g = 0}
    (σ : ∀ i : ℤ,
      ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)
    (hM : ∀ i : ℤ, P (M.X i)) :
    ∀ i : ℤ, P (cokernel (f.f i)) := by
  intro i
  let S : ShortComplex A :=
    ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i))
  let σi : S.Splitting := by
    simpa [S] using σ i
  have hS : S.ShortExact := σi.shortExact
  let _ : Epi S.g := hS.epi_g
  have hCoker :
      Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
    exact (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hS.exact, inferInstance⟩
  let e : cokernel (f.f i) ≅ M.X i := by
    let hc : IsColimit (CokernelCofork.ofπ S.g S.zero) := Classical.choice hCoker
    simpa [S] using IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hc
  -- Proof comment: uniqueness of cokernels identifies the categorical cokernel with the
  -- degreewise quotient object already sitting in the split row.
  exact P.prop_of_iso e.symm (hM i)

/-- Helper for Lemma 13.29.1: once the raw comparison map in the homotopy category is chosen,
termwise split monomorphy of the first map strictifies the square on the nose. -/
private theorem strictifiedSuccessorComparison
    {P : ObjectProperty A} [P.ContainsZero] [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n)
    {Draw R : CochainComplex A ℤ}
    (stepRaw : D.complex ⟶ Draw)
    {qRaw : Draw ⟶ R} {hzero : stepRaw ≫ qRaw = 0}
    (σ : ∀ i : ℤ,
      ((ShortComplex.mk stepRaw qRaw hzero).map
        (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)
    (βpre : Draw ⟶ upperTruncationStage K (n + 1))
    (hβpre :
      let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
      HoQ.map stepRaw ≫ HoQ.map βpre =
        HoQ.map (D.comparison ≫ truncLEStep K n)) :
    ∃ βraw : Draw ⟶ upperTruncationStage K (n + 1),
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map βraw =
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map βpre ∧
      CommSq stepRaw D.comparison βraw (truncLEStep K n) := by
  let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hsq :
      CommSq (HoQ.map stepRaw) (HoQ.map D.comparison) (HoQ.map βpre)
        (HoQ.map (truncLEStep K n)) := by
    refine CommSq.mk ?_
    -- Proof comment: rewrite the raw square in the homotopy category into the four-map shape
    -- required by the strictification lemma.
    simpa [Functor.map_comp] using hβpre
  obtain ⟨βraw, hβraw, hsqraw⟩ :=
    exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
      (f := stepRaw) (a := D.comparison) (b := βpre) (g := truncLEStep K n)
      hsq
      (fun i ↦ (σ i).isSplitMono_f)
  exact ⟨βraw, hβraw.symm, hsqraw⟩

/-- Helper for Lemma 13.29.1: transport the first `TR3` comparison square across the chosen
degreewise-split model. -/
private theorem successorSplitComparisonSquare
    {P : ObjectProperty A} [P.ContainsZero] [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n)
    {R Yc Draw : CochainComplex A ℤ}
    (stepQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj D.complex) ⟶
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc))
    (βQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc) ⟶
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (upperTruncationStage K (n + 1))))
    (hβ₁ : stepQ ≫ βQ =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (D.comparison ≫ truncLEStep K n))
    (stepRaw : D.complex ⟶ Draw)
    {qRaw : Draw ⟶ R} {hzero : stepRaw ≫ qRaw = 0}
    (σ : ∀ i : ℤ,
      ((ShortComplex.mk stepRaw qRaw hzero).map
        (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)
    {ρ : R ⟶ mappingCone (D.comparison ≫ truncLEStep K n)}
    {qQ : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Yc) ⟶
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R)}
    (eT : Triangle.mk stepQ qQ
        (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ρ) ≫
          (CochainComplex.mappingCone.triangleh (D.comparison ≫ truncLEStep K n)).mor₃) ≅
      CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk stepRaw qRaw hzero) σ)
    (heT₁ : eT.hom.hom₁ =
      𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj D.complex))
    (βpre : Draw ⟶ upperTruncationStage K (n + 1))
    (hβpreQ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map βpre =
      eT.inv.hom₂ ≫ βQ) :
    let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    HoQ.map stepRaw ≫ HoQ.map βpre =
      HoQ.map (D.comparison ≫ truncLEStep K n) := by
  let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have heTinv₁ :
      eT.inv.hom₁ = 𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj D.complex) := by
    -- Proof comment: the chosen triangle isomorphism is the identity on the first vertex.
    simpa [heT₁] using Iso.inv_hom_id_triangle_hom₁ eT
  have htransport :
      HoQ.map stepRaw ≫ eT.inv.hom₂ = eT.inv.hom₁ ≫ stepQ := by
    -- Proof comment: this is the first square of the inverse triangle isomorphism rewritten on
    -- the split-model triangle.
    simpa [CochainComplex.trianglehOfDegreewiseSplit] using eT.inv.comm₁
  calc
    HoQ.map stepRaw ≫ HoQ.map βpre = HoQ.map stepRaw ≫ (eT.inv.hom₂ ≫ βQ) := by
      simpa [Category.assoc, hβpreQ]
    _ = (HoQ.map stepRaw ≫ eT.inv.hom₂) ≫ βQ := by simp [Category.assoc]
    _ = (eT.inv.hom₁ ≫ stepQ) ≫ βQ := by rw [htransport]
    _ = HoQ.map (D.comparison ≫ truncLEStep K n) := by
      simpa [heTinv₁, Category.assoc] using hβ₁

/-- Helper for Lemma 13.29.1: one resolved stage can be extended across the next truncation map
by the mapping-cone construction from the source proof. -/
theorem extendUpperTruncationStageData
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts]
    [P.HasEpiCover]
    {K : CochainComplex A ℤ} {n : ℕ}
    (D : UpperTruncationStageData P K n) :
    ∃ D' : UpperTruncationStageData P K (n + 1),
      ∃ step : D.complex ⟶ D'.complex,
        CommSq D.comparison step (truncLEStep K n) D'.comparison ∧
          (∀ i : ℤ, IsSplitMono (step.f i)) ∧
          (∀ i : ℤ, P (cokernel (step.f i))) := by
  -- Route correction: the whole theorem should recurse through a stage-extension API, so the
  -- only remaining blocker is the source-faithful successor construction.
  let a : D.complex ⟶ upperTruncationStage K (n + 1) := D.comparison ≫ truncLEStep K n
  obtain ⟨R, ρ, hρ⟩ := successorConeResolution P D
  obtain ⟨Yc, stepQ, qQ, βQ, hTQ, hβ₁, hβ₂⟩ :=
    successorTriangleComparisonRepresentableMiddle D ρ
  let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let δ : (HoQ.obj R) ⟶ ((HoQ.obj D.complex)⟦(1 : ℤ)⟧) :=
    HoQ.map ρ ≫ (CochainComplex.mappingCone.triangleh a).mor₃
  -- Proof comment: with a represented middle object in hand, Lemma `13.10.7` now produces the
  -- degreewise split short complex promised by the source proof.
  obtain ⟨Draw, stepRaw, qRaw, hzero, σ, eT, heT₁, heT₃⟩ :=
    distinguished_triangle_iso_to_degreewiseSplit
      (A := D.complex) (B := Yc) (C := R) (a := stepQ) (b := qQ) (c := δ) hTQ
  let Tsplit : Triangle (HomotopyCategory A (ComplexShape.up ℤ)) :=
    CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk stepRaw qRaw hzero) σ
  have hTsplit :
      Tsplit ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) := by
    -- Proof comment: the split-model triangle is distinguished because it is isomorphic to the
    -- distinguished triangle already produced in the homotopy category.
    exact isomorphic_distinguished _ hTQ _ eT.symm
  have hTsplit_mor₃ : Tsplit.mor₃ = δ := by
    -- Proof comment: the comparison isomorphism is the identity on the outer vertices, so it
    -- transports the connecting morphism without change.
    simpa [Tsplit, heT₁, heT₃] using eT.hom.comm₃.symm
  let βdrawQ : HoQ.obj Draw ⟶ HoQ.obj (upperTruncationStage K (n + 1)) :=
    eT.inv.hom₂ ≫ βQ
  -- Proof comment: choose a cochain-level representative of the raw homotopy-category map out of
  -- the split middle complex.
  obtain ⟨βpre, hβpreQ⟩ := HoQ.map_surjective βdrawQ
  letI : P.IsClosedUnderIsomorphisms := by
    letI : P.IsClosedUnderBinaryCoproducts := by infer_instance
    letI : P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty) := by infer_instance
    exact ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have hDraw_term_mem : ∀ i : ℤ, P (Draw.X i) := by
    -- Proof comment: degreewise splitness identifies each middle term with a finite coproduct of
    -- the old stage term and the resolved cone term.
    exact degreewiseSplitMiddle_term_mem σ D.isResolution.term_mem hρ.term_mem
  have hDraw_strictlyLE : Draw.IsStrictlyLE ((n : ℤ) + 2) := by
    -- Proof comment: the same degreewise split description shows the middle complex is bounded
    -- above by the common cutoff `n + 2`.
    let _ : D.complex.IsStrictlyLE ((n : ℤ) + 1) := D.isResolution.strictlyLE
    have hD : D.complex.IsStrictlyLE ((n : ℤ) + 2) := by
      exact D.complex.isStrictlyLE_of_le ((n : ℤ) + 1) ((n : ℤ) + 2) (by omega)
    exact degreewiseSplitMiddle_isStrictlyLE σ hD hρ.strictlyLE
  have hstepRaw_split : ∀ i : ℤ, IsSplitMono (stepRaw.f i) := by
    -- Proof comment: this is one of the structural outputs of the split short exact model.
    intro i
    exact (σ i).isSplitMono_f
  have hstepRaw_cokernel_mem : ∀ i : ℤ, P (cokernel (stepRaw.f i)) := by
    -- Proof comment: each degreewise cokernel identifies with the resolved cone term `R.X i`.
    exact degreewiseSplitStep_cokernel_mem P σ hρ.term_mem
  have hβpre_square :
      let HoQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
      HoQ.map stepRaw ≫ HoQ.map βpre =
        HoQ.map (D.comparison ≫ truncLEStep K n) := by
    -- Proof comment: the split-model triangle already records the homotopy-category square
    -- needed to strictify the chosen representative `βpre`.
    exact successorSplitComparisonSquare D stepQ βQ hβ₁ stepRaw σ eT heT₁ βpre hβpreQ
  obtain ⟨βraw, hβraw, hsqraw⟩ :=
    strictifiedSuccessorComparison D stepRaw σ βpre hβpre_square
  let _ := hDraw_term_mem
  let _ := hDraw_strictlyLE
  let _ := hstepRaw_split
  let _ := hstepRaw_cokernel_mem
  let _ := hβpre_square
  let _ := βraw
  let _ := hsqraw
  -- TODO: the raw successor data is now fully strictified: `βraw` commutes on the nose with the
  -- stage map `stepRaw`, and the split short complex still controls terms in `P`, boundedness,
  -- and cokernels. The remaining source-faithful steps are to prove that this strictified map is
  -- a quasi-isomorphism and then add the explicit two-term correction supported in degrees
  -- `((n : ℤ) + 1)` and `((n : ℤ) + 2)` to repair termwise epimorphy only in those top degrees,
  -- after which the final stage data can be packaged directly.
  sorry

-- Proof sketch: apply the bounded-above resolution lemma to each truncation `τ_{\le n} K^•`, and
-- then inductively compare consecutive stages inside the homotopy category. Lemma `13.10.7`
-- replaces the relevant distinguished triangle by a degreewise split short exact sequence, giving
-- termwise split transition maps with cokernels in `P`; a final two-term correction restores
-- surjectivity in the top degrees.
/-- Lemma 13.29.1: if `P` contains `0`, is closed under finite direct sums, and every object of an
abelian category is a quotient of an object of `P`, then every cochain complex `K^•` admits a
compatible tower `P_1^• ⟶ P_2^• ⟶ \cdots` over the upper truncation tower
`τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ \cdots` such that each comparison
`P_{n + 1}^• ⟶ τ_{\le n + 1} K^•` is termwise epimorphic and a quasi-isomorphism, each
`P_{n + 1}^•` is bounded above with terms in `P`, each transition map is termwise split
monomorphic, and each degreewise cokernel again lies in `P`. -/
@[stacks 06XX]
theorem exists_upperTruncationResolutionTower
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts]
    [P.HasEpiCover]
    (K : CochainComplex A ℤ) :
    Nonempty (UpperTruncationResolutionTower P K) := by
  classical
  -- Proof comment: recurse on the truncation index using the explicit stage-data carrier, then
  -- package the chosen stages and successor maps with `UpperTruncationResolutionTower.ofSequence`.
  let stageData : (n : ℕ) → UpperTruncationStageData P K n :=
    Nat.rec
      (motive := fun n ↦ UpperTruncationStageData P K n)
      (zeroUpperTruncationStageData P K)
      (fun n D ↦ (extendUpperTruncationStageData P D).choose)
  let stepData (n : ℕ) :
      ∃ step : (stageData n).complex ⟶ (stageData (n + 1)).complex,
        CommSq (stageData n).comparison step (truncLEStep K n) (stageData (n + 1)).comparison ∧
          (∀ i : ℤ, IsSplitMono (step.f i)) ∧
          (∀ i : ℤ, P (cokernel (step.f i))) :=
    by
      simpa [stageData] using (extendUpperTruncationStageData P (stageData n)).choose_spec
  refine
    ⟨UpperTruncationResolutionTower.ofSequence
      (fun n ↦ (stageData n).complex)
      (fun n ↦ (stepData n).choose)
      (fun n ↦ (stageData n).comparison)
      (fun n ↦ (stageData n).isResolution)
      ?_
      ?_
      ?_⟩
  · intro n
    -- Proof comment: the chosen successor data already records strict compatibility with the
    -- canonical truncation map.
    exact (stepData n).choose_spec.1
  · intro n i
    -- Proof comment: the chosen successor data also records degreewise split monomorphy.
    exact ((stepData n).choose_spec.2.1) i
  · intro n i
    -- Proof comment: the same successor data records that each degreewise cokernel remains in
    -- the object property `P`.
    exact ((stepData n).choose_spec.2.2) i

end

end CategoryTheory
