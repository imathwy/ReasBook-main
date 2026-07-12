import Mathlib
import StacksProject_2024.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
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
theorem exists_upperTruncationResolutionTower
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts]
    [P.HasEpiCover]
    (K : CochainComplex A ℤ) :
    Nonempty (UpperTruncationResolutionTower P K) := by
  -- The owner statement is kept unchanged; only the proof remains open.
  sorry

end

end CategoryTheory
