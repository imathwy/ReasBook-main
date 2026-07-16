import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_13_9
import stacks_proof.stacks_project.Chap13.Lemma_13_9_5
import stacks_proof.stacks_project.Chap13.Lemma_13_9_8
import stacks_proof.stacks_project.Chap15.Lemma_15_88_1_Base

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

attribute [local instance] seqRingMod_abelian seqRingMod_categoryWithHomology

/-- Helper for Lemma 15.88.7: the ring at stage `n` of the canonical sheaf attached to the
inverse system `A₀ ← A₁ ← A₂ ← ⋯`. -/
private abbrev sequentialRingedModuleStageRing (n : ℕ) :=
  (((sequentialRingSystemRingSheaf A ρ).obj.obj (Opposite.op n)) : Type u)

/-- Helper for Lemma 15.88.7: the structure ring map for the successor transition in the
canonical sheaf attached to the inverse system `A₀ ← A₁ ← A₂ ← ⋯`. -/
private abbrev sequentialRingedModuleStageStepRingHom (n : ℕ) :
    sequentialRingedModuleStageRing (A := A) (ρ := ρ) (n + 1) →+*
      sequentialRingedModuleStageRing (A := A) (ρ := ρ) n :=
  CommRingCat.Hom.hom ((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ n)).op))

/-- Helper for Lemma 15.88.7: evaluate a cochain complex of module systems at stage `n` by
applying stagewise evaluation in every degree. This is the lower-universe adapter needed to
compare the canonical derived preimage complex with the stagewise transition maps. -/
private theorem sequentialRingedModuleCochainEvalLow_shape
    (n : ℕ) (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    ∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel i j →
      (M.d i j).val.app (Opposite.op n) = 0 := by
  intro i j hij
  -- Evaluate the zero differential identity of `M` at stage `n`.
  simpa using congrArg (fun f ↦ f.val.app (Opposite.op n)) (M.shape i j hij)

/-- Helper for Lemma 15.88.7: stagewise evaluation preserves the identity `d ∘ d = 0`. -/
private theorem sequentialRingedModuleCochainEvalLow_d_comp_d
    (n : ℕ) (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    ∀ i j k : ℤ, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      (M.d i j).val.app (Opposite.op n) ≫ (M.d j k).val.app (Opposite.op n) = 0 := by
  intro i j k hij hjk
  -- Evaluate the cochain identity `d ≫ d = 0` at the `n`-th stage.
  change
    (M.d i j ≫ M.d j k).val.app (Opposite.op n) =
      (0 : M.X i ⟶ M.X k).val.app (Opposite.op n)
  simpa using congrArg (fun f ↦ f.val.app (Opposite.op n)) (M.d_comp_d' i j k hij hjk)

/-- Helper for Lemma 15.88.7: the stage-`n` evaluated complex of a complex in
`\mathrm{Mod}(\mathbf N, (A_n))`, spelled in a universe-compatible way for this file. -/
private def sequentialRingedModuleCochainEvalLow
    (n : ℕ) (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)) ℤ :=
  { X := fun i ↦ (M.X i).val.obj (Opposite.op n)
    d := fun i j ↦ (M.d i j).val.app (Opposite.op n)
    shape := sequentialRingedModuleCochainEvalLow_shape (A := A) (ρ := ρ) n M
    d_comp_d' := sequentialRingedModuleCochainEvalLow_d_comp_d (A := A) (ρ := ρ) n M }

/-- Helper for Lemma 15.88.7: the stagewise restriction maps commute with the differentials after
evaluating a complex degreewise. -/
private theorem sequentialRingedModuleCochainEvaluationStepLow_comm
    (n : ℕ) (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i j : ℤ)
  (_hij : (ComplexShape.up ℤ).Rel i j) :
    (M.X i).val.map ((homOfLE (Nat.le_succ n)).op) ≫
        (ModuleCat.restrictScalars
          (sequentialRingedModuleStageStepRingHom (A := A) (ρ := ρ) n)).map
          ((M.d i j).val.app (Opposite.op n)) =
      (M.d i j).val.app (Opposite.op (n + 1)) ≫
        (M.X j).val.map ((homOfLE (Nat.le_succ n)).op) := by
  -- This is naturality of the morphism of systems `M.d i j` along the successor arrow.
  simpa [sequentialRingedModuleStageStepRingHom, sequentialRingSystem] using
    (M.d i j).val.naturality ((homOfLE (Nat.le_succ n)).op)

/-- Helper for Lemma 15.88.7: the evaluated successor morphism of a complex in
`\mathrm{Mod}(\mathbf N, (A_n))`, written with the lower-universe stage evaluation used in this
file. -/
private def sequentialRingedModuleCochainEvaluationStepLow
    (n : ℕ) (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (n + 1) M ⟶
      ((ModuleCat.restrictScalars
          (sequentialRingedModuleStageStepRingHom (A := A) (ρ := ρ) n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n M) :=
  { f := fun i ↦ (M.X i).val.map ((homOfLE (Nat.le_succ n)).op)
    comm' := sequentialRingedModuleCochainEvaluationStepLow_comm (A := A) (ρ := ρ) n M }

/-- Helper for Lemma 15.88.7: restrict a stage-`n` evaluated complex along the successor ring map
`A_{n + 1} → A_n`. -/
private abbrev sequentialRingedModuleCochainRestrictFunctor
    (n : ℕ) :
    CochainComplex
        (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)) ℤ ⥤
      CochainComplex
        (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) (n + 1))) ℤ :=
  ((ModuleCat.restrictScalars
      (sequentialRingedModuleStageStepRingHom (A := A) (ρ := ρ) n)).mapHomologicalComplex
      (ComplexShape.up ℤ))

/-- Helper for Lemma 15.88.7: the stage-`n` complex after restriction of scalars to stage
`n + 1`. -/
private abbrev sequentialRingedModuleCochainRestrict
    (n : ℕ)
    (M : CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)) ℤ) :
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) (n + 1))) ℤ :=
  (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).obj M

/-- Helper for Lemma 15.88.7: one successor stage of the source-faithful split-epimorphic
strictification. Starting from a stage-`n` retract of the evaluated canonical preimage complex,
the standard biproduct-mapping-cocone factorization produces a stage-`n + 1` complex with a
termwise split-epimorphic successor map, together with the strict inclusion map and the raw
projection map that still commutes with the previous stage up to homotopy. -/
private theorem successor_strictification_step
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ)
    (n : ℕ)
    (M : CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)) ℤ)
    (β : sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N ⟶ M)
    (α : M ⟶ sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N)
    (hβα : β ≫ α = 𝟙 _) :
    ∃ (M' : CochainComplex
          (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) (n + 1))) ℤ)
      (β' : sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (n + 1) N ⟶ M')
      (α' : M' ⟶ sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (n + 1) N)
      (σ : M' ⟶ sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) n M),
      (∀ i : ℤ, IsSplitEpi (σ.f i)) ∧
      β' ≫ α' = 𝟙 _ ∧
      β' ≫ σ =
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map β ∧
      Nonempty (Homotopy (α' ≫ β') (𝟙 _)) ∧
      Nonempty
        (Homotopy
          (α' ≫ sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N)
          (σ ≫ (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map α)) := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n
  let t :
      sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (n + 1) N ⟶ F.obj M :=
    sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N ≫ F.map β
  obtain ⟨hproj, hsplit, hβσ, hβα'⟩ :=
    CochainComplex.splitEpi_factorization_through_biproduct_mappingCocone_id t
  refine ⟨_,
    Limits.biprod.inl,
    Limits.biprod.fst,
    Limits.biprod.desc t (CochainComplex.mappingCocone.fst (𝟙 (F.obj M))),
    ?_⟩
  have hβα_restrict :
      F.map β ≫ F.map α =
        𝟙 (F.obj (sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N)) := by
    -- Apply restriction of scalars to the retract identity at stage `n`.
    simpa [Functor.map_comp] using congrArg (fun k ↦ F.map k) hβα
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    -- Each degree of the canonical factorization map is split epic.
    simpa [t] using hsplit i
  · -- The new inclusion still splits the raw projection strictly.
    simpa using hβα'
  · -- The successor square on the `β`-side commutes strictly by construction.
    exact hβσ.trans (by rfl)
  · -- The projection to the old stage is a homotopy inverse to the inclusion.
    exact ⟨by simpa using hproj⟩
  · -- Compose the homotopy inverse relation with the candidate successor square to obtain the
    -- desired compatibility of the raw projection family up to homotopy.
    refine ⟨?_⟩
    simpa [t, Category.assoc, hβσ, hβα_restrict] using
      hproj.compRight
        ((Limits.biprod.desc t (CochainComplex.mappingCocone.fst (𝟙 (F.obj M)))) ≫ F.map α)

/-- Helper for Lemma 15.88.7: a finite strict prefix stores the stagewise complexes chosen for the
first `length + 1` stages of the canonical preimage complex, together with strict successor maps,
strict comparison maps back to the canonical evaluations, and the retract/homotopy data needed for
the later diagonal reassembly. -/
private structure StrictPreimagePrefix
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (length : ℕ) where
  /-- The chosen strict stage complex at each index of the finite prefix. -/
  L : (m : Fin (length + 1)) →
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) m.1)) ℤ
  /-- The inclusion from the canonical stage evaluation into the chosen strict stage complex. -/
  β : (m : Fin (length + 1)) →
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) m.1 N ⟶ L m
  /-- The projection from the chosen strict stage complex back to the canonical stage evaluation. -/
  α : (m : Fin (length + 1)) →
    L m ⟶ sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) m.1 N
  /-- The strict successor map between consecutive chosen stage complexes. -/
  τ : (m : Fin length) →
    L (Fin.succ m) ⟶
      sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) m.1 (L (Fin.castSucc m))
  /-- The inclusion maps commute strictly with the chosen successor maps. -/
  β_compat : (m : Fin length) →
    β (Fin.succ m) ≫ τ m =
      sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) m.1 N ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) m.1).map
          (β (Fin.castSucc m))
  /-- The projection maps commute strictly with the chosen successor maps. -/
  α_compat : (m : Fin length) →
    α (Fin.succ m) ≫
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) m.1 N =
      τ m ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) m.1).map
          (α (Fin.castSucc m))
  /-- Each chosen successor map is termwise split epic. -/
  τ_splitEpi : (m : Fin length) → ∀ i : ℤ, IsSplitEpi ((τ m).f i)
  /-- Each stage is a strict retract of the canonical stage evaluation. -/
  β_α : (m : Fin (length + 1)) → β m ≫ α m = 𝟙 _
  /-- The reverse composite is homotopic to the identity at every stage. -/
  α_β_homotopy : (m : Fin (length + 1)) → Nonempty (Homotopy (α m ≫ β m) (𝟙 _))

/-- Helper for Lemma 15.88.7: the recursion starts at stage `0` with the canonical stage-`0`
evaluation itself, so all comparison maps are identities and no successor data are required yet. -/
private noncomputable abbrev StrictPreimagePrefix.base
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    StrictPreimagePrefix (A := A) (ρ := ρ) N 0 :=
  { L := fun
      | ⟨0, _⟩ => sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) 0 N
    β := fun
      | ⟨0, _⟩ => 𝟙 _
    α := fun
      | ⟨0, _⟩ => 𝟙 _
    τ := fun m ↦ nomatch m
    β_compat := fun m ↦ nomatch m
    α_compat := fun m ↦ nomatch m
    τ_splitEpi := fun m ↦ nomatch m
    β_α := fun
      | ⟨0, _⟩ => by simp
    α_β_homotopy := fun
      | ⟨0, _⟩ => ⟨Homotopy.refl _⟩ }

/-- Helper for Lemma 15.88.7: when extending a strict prefix, the source of the new one-step
strictification is the previously chosen terminal stage complex. -/
private noncomputable abbrev StrictPreimagePrefix.last_complex
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) length)) ℤ :=
  S.L (Fin.last length)

/-- Helper for Lemma 15.88.7: the inclusion map at the terminal stage of a strict prefix. -/
private noncomputable abbrev StrictPreimagePrefix.last_beta
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) length N ⟶ S.last_complex :=
  S.β (Fin.last length)

/-- Helper for Lemma 15.88.7: the projection map at the terminal stage of a strict prefix. -/
private noncomputable abbrev StrictPreimagePrefix.last_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.last_complex ⟶ sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) length N :=
  S.α (Fin.last length)

/-- Helper for Lemma 15.88.7: the terminal stage of a strict prefix is already a strict retract of
the corresponding canonical evaluation. -/
private theorem StrictPreimagePrefix.last_beta_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.last_beta ≫ S.last_alpha = 𝟙 _ := by
  -- This is the terminal component of the retract data stored in the prefix.
  simpa [StrictPreimagePrefix.last_beta, StrictPreimagePrefix.last_alpha] using
    S.β_α (Fin.last length)

/-- Helper for Lemma 15.88.7: apply the one-step split-epimorphic strictification to the terminal
stage of a strict prefix. This packages the raw new stage, the new inclusion/projection pair, and
the raw successor map before the alpha-side strictification is corrected. -/
private noncomputable abbrev StrictPreimagePrefix.extension_raw_data
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :=
  successor_strictification_step (A := A) (ρ := ρ) N length
    S.last_complex S.last_beta S.last_alpha S.last_beta_alpha

/-- Helper for Lemma 15.88.7: the raw next stage complex returned by the one-step
strictification. -/
private noncomputable abbrev StrictPreimagePrefix.extension_raw_complex
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) (length + 1))) ℤ :=
  Classical.choose S.extension_raw_data

/-- Helper for Lemma 15.88.7: the raw inclusion into the next-stage complex returned by the
one-step strictification. -/
private noncomputable abbrev StrictPreimagePrefix.extension_raw_beta
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N ⟶
      S.extension_raw_complex :=
  Classical.choose (Classical.choose_spec S.extension_raw_data)

/-- Helper for Lemma 15.88.7: the raw projection from the next-stage complex returned by the
one-step strictification. -/
private noncomputable abbrev StrictPreimagePrefix.extension_raw_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_complex ⟶
      sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec S.extension_raw_data))

/-- Helper for Lemma 15.88.7: the raw successor map from the next-stage complex back to the
restricted previous stage, before the alpha-side square is strictified. -/
private noncomputable abbrev StrictPreimagePrefix.extension_raw_step
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_complex ⟶
      sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) length S.last_complex :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec S.extension_raw_data)))

/-- Helper for Lemma 15.88.7: the raw one-step strictification data satisfy exactly the package
returned by `successor_strictification_step` at the terminal stage of the prefix. -/
private theorem StrictPreimagePrefix.extension_raw_spec
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    (∀ i : ℤ, IsSplitEpi ((S.extension_raw_step).f i)) ∧
      S.extension_raw_beta ≫ S.extension_raw_alpha = 𝟙 _ ∧
      S.extension_raw_beta ≫ S.extension_raw_step =
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_beta ∧
      Nonempty (Homotopy (S.extension_raw_alpha ≫ S.extension_raw_beta) (𝟙 _)) ∧
      Nonempty
        (Homotopy
          (S.extension_raw_alpha ≫
            sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N)
          (S.extension_raw_step ≫
            (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
              S.last_alpha)) := by
  -- This is exactly the witness extracted from the one-step strictification applied at the last
  -- stage of the prefix.
  exact Classical.choose_spec <|
    Classical.choose_spec <|
      Classical.choose_spec <|
        Classical.choose_spec <|
          S.extension_raw_data

/-- Helper for Lemma 15.88.7: every degree of the raw successor map returned by the one-step
strictification is split epic. -/
private theorem StrictPreimagePrefix.extension_raw_step_splitEpi
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (i : ℤ) :
    IsSplitEpi ((S.extension_raw_step).f i) := by
  -- Read off the first component of the chosen one-step strictification data.
  exact S.extension_raw_spec.1 i

/-- Helper for Lemma 15.88.7: the raw next-stage inclusion still splits the raw next-stage
projection strictly. -/
private theorem StrictPreimagePrefix.extension_raw_beta_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_beta ≫ S.extension_raw_alpha = 𝟙 _ := by
  -- This is the retract identity returned by `successor_strictification_step`.
  exact S.extension_raw_spec.2.1

/-- Helper for Lemma 15.88.7: the raw next-stage inclusion already commutes strictly with the
new successor map. -/
private theorem StrictPreimagePrefix.extension_raw_beta_compat
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_beta ≫ S.extension_raw_step =
      sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
          S.last_beta := by
  -- This is the strict `β`-compatibility packaged by the one-step strictification.
  exact S.extension_raw_spec.2.2.1

/-- Helper for Lemma 15.88.7: the raw next-stage projection remains homotopy inverse to the raw
next-stage inclusion. -/
private theorem StrictPreimagePrefix.extension_raw_alpha_beta_homotopy
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    Nonempty (Homotopy (S.extension_raw_alpha ≫ S.extension_raw_beta) (𝟙 _)) := by
  -- This is the homotopy-inverse part of the chosen strictification witness.
  exact S.extension_raw_spec.2.2.2.1

/-- Helper for Lemma 15.88.7: before correcting the new projection map, the raw next-stage
projection only commutes with the previous stage up to homotopy. This isolates the precise
remaining blocker in the source-faithful recursion. -/
private theorem StrictPreimagePrefix.extension_raw_alpha_projection_homotopy
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    Nonempty
      (Homotopy
        (S.extension_raw_alpha ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N)
        (S.extension_raw_step ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha)) := by
  -- The one-step strictification provides the successor square for the raw projection map only up
  -- to homotopy; the next helper must strictify exactly this square.
  exact S.extension_raw_spec.2.2.2.2

/-- Helper for Lemma 15.88.7: after restricting scalars to stage `length + 1`, the previous
terminal retract identity remains strict. This is the compatibility needed in the explicit
normalization formula for the new projection. -/
private theorem StrictPreimagePrefix.restrict_last_beta_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map S.last_beta ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map S.last_alpha =
      𝟙 _ := by
  -- Apply restriction of scalars to the terminal retract identity of the previous stage.
  simpa [Functor.map_comp] using congrArg
    (fun k ↦
      (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map k)
    S.last_beta_alpha

/-- Helper for Lemma 15.88.7: after restricting scalars, the old terminal projection remains
termwise split epic because the old terminal inclusion is still a strict section. This is the
orientation in which Chapter 13 already strictifies the raw successor square. -/
private theorem StrictPreimagePrefix.restrict_last_alpha_splitEpi
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (i : ℤ) :
    IsSplitEpi
      (((sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
          S.last_alpha).f i) := by
  -- The restricted old inclusion is still a chosen section of the restricted old projection.
  refine IsSplitEpi.mk' ⟨
    (((sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
      S.last_beta).f i), ?_⟩
  have hcomponent :=
    congrArg (fun k ↦ k.f i) S.restrict_last_beta_alpha
  simpa using hcomponent

/-- Helper for Lemma 15.88.7: Chapter 13 strictifies the raw terminal square on the successor-map
side because the restricted old projection is termwise split epic. This closes the dual
orientation that is available without further transport. -/
private theorem StrictPreimagePrefix.strictify_raw_successor_square
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    ∃ (τStrict :
        S.extension_raw_complex ⟶
          sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) length S.last_complex),
      Nonempty (Homotopy S.extension_raw_step τStrict) ∧
      S.extension_raw_alpha ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        τStrict ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length
  let step := sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N
  -- Route correction: the currently available Chapter 13 strictification acts on the left map
  -- because `F.map S.last_alpha` is split epic, so we record that exact dual square first.
  obtain ⟨hcomm⟩ := S.extension_raw_alpha_projection_homotopy
  obtain ⟨τStrict, hτ, hsq⟩ :=
    CochainComplex.exists_homotopic_leftMap_of_termwiseSplitEpi
      hcomm
      (fun i ↦ S.restrict_last_alpha_splitEpi i)
  refine ⟨τStrict, ⟨hτ⟩, ?_⟩
  -- Unpack the resulting strict commutative square in the exact shape used later in the file.
  simpa [F, step] using hsq.w

/-- Helper for Lemma 15.88.7: the evaluated successor map on the new stage is termwise split epic
because it is a retract of the raw split-epimorphic successor map returned by the one-step
strictification. -/
private theorem StrictPreimagePrefix.terminal_evaluation_step_splitEpi
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (i : ℤ) :
    IsSplitEpi
      ((sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N).f i) := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length
  let step := sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N
  let rawStep := (S.extension_raw_step).f i
  letI : IsSplitEpi rawStep := S.extension_raw_step_splitEpi i
  -- Route correction: no additional strictification is needed here. The strict `β`-compatibility
  -- and strict retract identity already show that the evaluated successor map is a retract of the
  -- raw split-epimorphic successor map produced by the one-step strictification.
  refine IsSplitEpi.mk' ⟨((F.map S.last_beta).f i) ≫ section_ rawStep ≫
      (S.extension_raw_alpha).f i, ?_⟩
  have hβσ :
      (S.extension_raw_beta).f i ≫ rawStep = step.f i ≫ (F.map S.last_beta).f i := by
    -- Read the strict `β`-compatibility on degree `i`.
    simpa [rawStep, step] using congrArg (fun k ↦ k.f i) S.extension_raw_beta_compat
  have hβα :
      (S.extension_raw_beta).f i ≫ (S.extension_raw_alpha).f i = 𝟙 _ := by
    -- Read the strict retract identity on degree `i`.
    simpa using congrArg (fun k ↦ k.f i) S.extension_raw_beta_alpha
  -- Compose the raw section with the two strict comparison maps to obtain a section of the
  -- evaluated successor map.
  calc
    step.f i ≫ (((F.map S.last_beta).f i) ≫ section_ rawStep ≫ (S.extension_raw_alpha).f i) =
        ((step.f i ≫ (F.map S.last_beta).f i) ≫ section_ rawStep) ≫
          (S.extension_raw_alpha).f i := by
            simp [Category.assoc]
    _ = (((S.extension_raw_beta).f i ≫ rawStep) ≫ section_ rawStep) ≫
          (S.extension_raw_alpha).f i := by
            rw [hβσ]
    _ = ((S.extension_raw_beta).f i ≫ (rawStep ≫ section_ rawStep)) ≫
          (S.extension_raw_alpha).f i := by
            simp [Category.assoc]
    _ = (S.extension_raw_beta).f i ≫ (S.extension_raw_alpha).f i := by
            simp [Category.assoc]
    _ = 𝟙 _ := hβα

/-- Helper for Lemma 15.88.7: once a strict replacement `αStrict` of the raw terminal projection
is available, the explicit source normalization
`rawα + αStrict - rawα ≫ rawβ ≫ αStrict` restores the retract identity and preserves the strict
successor compatibility. -/
private theorem StrictPreimagePrefix.normalize_terminal_projection
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length)
    (αStrict :
      S.extension_raw_complex ⟶
        sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N)
    (hαStrict :
      αStrict ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        S.extension_raw_step ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha) :
    S.extension_raw_beta ≫
        (S.extension_raw_alpha + αStrict -
          S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) = 𝟙 _ ∧
      (S.extension_raw_alpha + αStrict -
          S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        S.extension_raw_step ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length
  let step := sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N
  let αNew :=
    S.extension_raw_alpha + αStrict -
      S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict
  refine ⟨?_, ?_⟩
  · -- Expand the normalization formula and cancel the duplicated `rawβ ≫ αStrict` term using
    -- the strict retract identity `rawβ ≫ rawα = 1`.
    calc
      S.extension_raw_beta ≫
          (S.extension_raw_alpha + αStrict -
            S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) =
          S.extension_raw_beta ≫ S.extension_raw_alpha +
            S.extension_raw_beta ≫ αStrict -
              ((S.extension_raw_beta ≫ S.extension_raw_alpha) ≫
                S.extension_raw_beta ≫ αStrict) := by
            rw [Preadditive.comp_sub, Preadditive.comp_add]
            simp [Category.assoc]
      _ = 𝟙 _ + S.extension_raw_beta ≫ αStrict -
            (𝟙 _ ≫ S.extension_raw_beta ≫ αStrict) := by
            rw [S.extension_raw_beta_alpha]
      _ = 𝟙 _ := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · -- The correction term maps to the same successor square because
    -- `rawβ ≫ rawStep = step ≫ F.map lastβ` and `F.map lastβ ≫ F.map lastα = 1`.
    have hcorrection :
        (S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫ step =
          S.extension_raw_alpha ≫ step := by
      calc
        (S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫ step =
            S.extension_raw_alpha ≫ S.extension_raw_beta ≫
              (αStrict ≫ step) := by simp [Category.assoc]
        _ =
            S.extension_raw_alpha ≫ S.extension_raw_beta ≫
              (S.extension_raw_step ≫ F.map S.last_alpha) := by
                rw [hαStrict]
        _ =
            S.extension_raw_alpha ≫
              (S.extension_raw_beta ≫ S.extension_raw_step) ≫
                F.map S.last_alpha := by simp [Category.assoc]
        _ =
            S.extension_raw_alpha ≫
              (step ≫ F.map S.last_beta) ≫
                F.map S.last_alpha := by
                  rw [S.extension_raw_beta_compat]
        _ =
            S.extension_raw_alpha ≫ step ≫
              (F.map S.last_beta ≫ F.map S.last_alpha) := by simp [Category.assoc]
        _ = S.extension_raw_alpha ≫ step := by
          rw [S.restrict_last_beta_alpha]
          simp
    -- After substituting the strict square for `αStrict`, the same cancellation shows that the
    -- normalized map still satisfies the strict compatibility equation.
    calc
      (S.extension_raw_alpha + αStrict -
          S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫ step =
          S.extension_raw_alpha ≫ step +
            αStrict ≫ step -
              ((S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫ step) := by
            rw [Preadditive.sub_comp, Preadditive.add_comp]
      _ = S.extension_raw_alpha ≫ step +
            (S.extension_raw_step ≫ F.map S.last_alpha) -
              (S.extension_raw_alpha ≫ step) := by
            rw [hαStrict, hcorrection]
      _ = S.extension_raw_step ≫ F.map S.last_alpha := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.88.7: strictify the raw terminal projection square by replacing the raw
projection with a homotopic map that commutes strictly with the previously chosen terminal
projection after restricting scalars. -/
private theorem StrictPreimagePrefix.terminal_projection_correction
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length)
    (τStrict :
      S.extension_raw_complex ⟶
        sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) length S.last_complex)
    (hτ : Homotopy S.extension_raw_step τStrict)
    (hsq :
      S.extension_raw_alpha ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        τStrict ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha) :
    ∃ (δ :
        S.extension_raw_complex ⟶
          sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N),
      Nonempty (Homotopy δ 0) ∧
      δ ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        (S.extension_raw_step - τStrict) ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length
  let step := sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N
  let p := F.map S.last_alpha
  -- Route correction: isolate the exact missing source-faithful correction term `δ` instead of
  -- asking for another abstract transfer lemma with the same semantic content. The raw defect is
  -- first strictified on the `α`-side, and the actual correction term is then the explicit
  -- difference between the strictified map and the raw projection.
  have hstepSplit : ∀ i : ℤ, IsSplitEpi (step.f i) := fun i ↦
    S.terminal_evaluation_step_splitEpi i
  have hcomm :
      Homotopy (S.extension_raw_step ≫ p) (S.extension_raw_alpha ≫ step) := by
    -- Compose the homotopy on the left edge with `p` and then rewrite the strictified square.
    exact (hτ.compRight p).trans (Homotopy.ofEq hsq.symm)
  obtain ⟨αStrict, hαStrict, hsqStrict⟩ :=
    CochainComplex.exists_homotopic_leftMap_of_termwiseSplitEpi hcomm hstepSplit
  refine ⟨αStrict - S.extension_raw_alpha, ?_, ?_⟩
  · -- The correction term is null-homotopic because it is the difference of homotopic maps.
    refine ⟨?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Homotopy.refl αStrict).add (hαStrict.smul (-1 : ℤ))
  · -- Expanding the difference turns the strict replacement into the required defect equation.
    calc
      (αStrict - S.extension_raw_alpha) ≫ step =
          αStrict ≫ step - S.extension_raw_alpha ≫ step := by
            rw [Preadditive.sub_comp]
      _ = S.extension_raw_step ≫ p - τStrict ≫ p := by
            rw [hsqStrict.w.symm, hsq]
      _ = (S.extension_raw_step - τStrict) ≫ p := by
            rw [Preadditive.sub_comp]

/-- Helper for Lemma 15.88.7: strictify the raw terminal projection square by replacing the raw
projection with a homotopic map that commutes strictly with the previously chosen terminal
projection after restricting scalars. -/
private theorem StrictPreimagePrefix.strictify_terminal_projection_square
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    ∃ (αStrict :
        S.extension_raw_complex ⟶
          sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N),
      Nonempty (Homotopy S.extension_raw_alpha αStrict) ∧
      αStrict ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        S.extension_raw_step ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha := by
  let F := sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length
  let step := sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N
  obtain ⟨τStrict, ⟨hτ⟩, hsq⟩ := S.strictify_raw_successor_square
  obtain ⟨δ, ⟨hδ⟩, hδeq⟩ := S.terminal_projection_correction τStrict hτ hsq
  let αStrict := S.extension_raw_alpha + δ
  refine ⟨αStrict, ?_, ?_⟩
  · -- The corrected terminal projection differs from the raw one by a null-homotopic term.
    refine ⟨?_⟩
    simpa [αStrict] using (Homotopy.refl S.extension_raw_alpha).add hδ
  · -- Add the correction term to the already strictified left edge to recover the desired top
    -- square with `S.extension_raw_step` fixed.
    calc
      αStrict ≫ step = (S.extension_raw_alpha + δ) ≫ step := by rfl
      _ = S.extension_raw_alpha ≫ step + δ ≫ step := by
            rw [Preadditive.add_comp]
      _ = τStrict ≫ F.map S.last_alpha +
            ((S.extension_raw_step - τStrict) ≫ F.map S.last_alpha) := by
            rw [hsq, hδeq]
      _ = τStrict ≫ F.map S.last_alpha +
            (S.extension_raw_step ≫ F.map S.last_alpha -
              τStrict ≫ F.map S.last_alpha) := by
            rw [Preadditive.sub_comp]
      _ = S.extension_raw_step ≫ F.map S.last_alpha := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.88.7: after the explicit normalization
`rawα + αStrict - rawα ≫ rawβ ≫ αStrict`, the new projection is still homotopy inverse to the raw
inclusion. -/
private theorem StrictPreimagePrefix.normalized_terminal_projection_homotopy
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length)
    (αStrict :
      S.extension_raw_complex ⟶
        sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N) :
    Nonempty
      (Homotopy
        ((S.extension_raw_alpha + αStrict -
            S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict) ≫
          S.extension_raw_beta)
        (𝟙 _)) := by
  let αNew :=
    S.extension_raw_alpha + αStrict -
      S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict
  obtain ⟨hαβ⟩ := S.extension_raw_alpha_beta_homotopy
  have hcomp :
      Homotopy
        (S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict)
        αStrict := by
    -- Postcompose the stored homotopy inverse relation with `αStrict`.
    simpa [Category.assoc] using hαβ.compRight αStrict
  have hdiff :
      Homotopy
        (αStrict - S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict)
        0 := by
    -- The correction term is null-homotopic because `rawα ≫ rawβ` is homotopic to the identity.
    simpa [sub_eq_add_neg] using
      (Homotopy.refl αStrict).add (hcomp.smul (-1 : ℤ))
  have hαNew :
      Homotopy αNew S.extension_raw_alpha := by
    -- Hence the normalized projection differs from the raw projection by a null-homotopic term.
    simpa [αNew, add_assoc] using
      (Homotopy.refl S.extension_raw_alpha).add hdiff
  refine ⟨?_⟩
  -- Postcompose with the raw inclusion and reuse the stored homotopy inverse package.
  simpa [αNew, Category.assoc] using (hαNew.compRight S.extension_raw_beta).trans hαβ

/-- Helper for Lemma 15.88.7: normalize the strictified terminal projection by the explicit source
formula `rawα + αStrict - rawα ≫ β ≫ αStrict`; this restores the strict retract identity
`β ≫ α = 1` without disturbing the strict successor square. -/
private theorem StrictPreimagePrefix.corrected_terminal_projection
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    ∃ (αNew :
        S.extension_raw_complex ⟶
          sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N),
      S.extension_raw_beta ≫ αNew = 𝟙 _ ∧
      αNew ≫
          sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
        S.extension_raw_step ≫
          (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
            S.last_alpha ∧
      Nonempty (Homotopy (αNew ≫ S.extension_raw_beta) (𝟙 _)) := by
  obtain ⟨αStrict, -, hαStrict⟩ := S.strictify_terminal_projection_square
  let αNew :=
    S.extension_raw_alpha + αStrict -
      S.extension_raw_alpha ≫ S.extension_raw_beta ≫ αStrict
  have hnorm := S.normalize_terminal_projection αStrict hαStrict
  refine ⟨αNew, ?_, ?_, ?_⟩
  · -- The explicit normalization restores the strict retract identity.
    simpa [αNew] using hnorm.1
  · -- The same normalization preserves the strict successor compatibility.
    simpa [αNew] using hnorm.2
  · -- The normalized projection remains homotopy inverse to the raw inclusion.
    simpa [αNew] using S.normalized_terminal_projection_homotopy αStrict

/-- Helper for Lemma 15.88.7: the recursively corrected terminal projection is the projection map
chosen for the new last stage when a strict prefix is extended by one step. -/
private noncomputable abbrev StrictPreimagePrefix.extension_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_complex ⟶
      sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) (length + 1) N :=
  Classical.choose S.corrected_terminal_projection

/-- Helper for Lemma 15.88.7: the corrected terminal projection restores the strict retract
identity with the raw inclusion at the new stage. -/
private theorem StrictPreimagePrefix.extension_beta_alpha
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_raw_beta ≫ S.extension_alpha = 𝟙 _ := by
  -- This is the first component of the normalized projection package.
  exact (Classical.choose_spec S.corrected_terminal_projection).1

/-- Helper for Lemma 15.88.7: the corrected terminal projection now commutes strictly with the
previous stage along the raw successor map. -/
private theorem StrictPreimagePrefix.extension_alpha_compat
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    S.extension_alpha ≫
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) length N =
      S.extension_raw_step ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) length).map
          S.last_alpha := by
  -- This is the strict compatibility component of the normalized projection package.
  exact (Classical.choose_spec S.corrected_terminal_projection).2.1

/-- Helper for Lemma 15.88.7: the corrected terminal projection remains homotopy inverse to the
raw inclusion at the new stage. -/
private theorem StrictPreimagePrefix.extension_alpha_beta_homotopy
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    Nonempty (Homotopy (S.extension_alpha ≫ S.extension_raw_beta) (𝟙 _)) := by
  -- This is the final component of the normalized projection package.
  exact (Classical.choose_spec S.corrected_terminal_projection).2.2

/-- Helper for Lemma 15.88.7: when a strict prefix is extended by one stage, every old successor
map is preserved on the `castSucc` part and the new last successor map is the chosen raw
split-epimorphic step. -/
private theorem StrictPreimagePrefix.extend_transition_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    (Fin.lastCases S.extension_raw_complex S.L (Fin.succ m)) ⟶
      sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) m.1
        (Fin.lastCases S.extension_raw_complex S.L (Fin.castSucc m)) := by
  cases m using Fin.lastCases with
  | last =>
      -- The new terminal transition is exactly the chosen raw strictification step.
      simpa using S.extension_raw_step
  | cast j =>
      -- All earlier transitions are inherited unchanged from the shorter prefix.
      simpa [Fin.succ_castSucc] using S.τ j

/-- Helper for Lemma 15.88.7: the extended prefix preserves the inclusion compatibility on the
`castSucc` part and inserts the newly strictified terminal square at the last index. -/
private theorem StrictPreimagePrefix.extend_beta_compat_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    (Fin.lastCases S.extension_raw_beta S.β (Fin.succ m)) ≫
        S.extend_transition_at m =
      sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) m.1 N ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) m.1).map
          (Fin.lastCases S.extension_raw_beta S.β (Fin.castSucc m)) := by
  cases m using Fin.lastCases with
  | last =>
      -- The last component is the strict `β`-compatibility produced by one-step strictification.
      simpa [StrictPreimagePrefix.extend_transition_at] using S.extension_raw_beta_compat
  | cast j =>
      -- Earlier components are exactly the stored `β`-compatibilities of the old prefix.
      simpa [Fin.succ_castSucc, StrictPreimagePrefix.extend_transition_at] using S.β_compat j

/-- Helper for Lemma 15.88.7: the extended prefix preserves the projection compatibility on the
`castSucc` part and uses the corrected terminal projection at the new last index. -/
private theorem StrictPreimagePrefix.extend_alpha_compat_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    (Fin.lastCases S.extension_alpha S.α (Fin.succ m)) ≫
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) m.1 N =
      S.extend_transition_at m ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) m.1).map
          (Fin.lastCases S.extension_alpha S.α (Fin.castSucc m)) := by
  cases m using Fin.lastCases with
  | last =>
      -- The new terminal component is the strict square satisfied by the corrected projection.
      simpa [StrictPreimagePrefix.extend_transition_at] using S.extension_alpha_compat
  | cast j =>
      -- Earlier components are unchanged from the shorter prefix.
      simpa [Fin.succ_castSucc, StrictPreimagePrefix.extend_transition_at] using S.α_compat j

/-- Helper for Lemma 15.88.7: the extended prefix preserves split epimorphy on the old
transitions and inserts the split-epimorphic raw strictification step at the new last index. -/
private theorem StrictPreimagePrefix.extend_transition_splitEpi_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) (i : ℤ) :
    IsSplitEpi ((S.extend_transition_at m).f i) := by
  cases m using Fin.lastCases with
  | last =>
      -- The last transition is the raw strictification step, already known to be split epic.
      simpa [StrictPreimagePrefix.extend_transition_at] using S.extension_raw_step_splitEpi i
  | cast j =>
      -- The old split-epimorphic transitions are preserved verbatim.
      simpa [Fin.succ_castSucc, StrictPreimagePrefix.extend_transition_at] using S.τ_splitEpi j i

/-- Helper for Lemma 15.88.7: the extended prefix preserves the retract identities on the old
stages and inserts the corrected terminal retract identity at the new last stage. -/
private theorem StrictPreimagePrefix.extend_beta_alpha_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    (Fin.lastCases S.extension_raw_beta S.β m) ≫
        (Fin.lastCases S.extension_alpha S.α m) = 𝟙 _ := by
  cases m using Fin.lastCases with
  | last =>
      -- The corrected terminal projection restores the new retract identity.
      simpa using S.extension_beta_alpha
  | cast j =>
      -- All earlier retract identities are unchanged.
      simpa using S.β_α j

/-- Helper for Lemma 15.88.7: the extended prefix preserves the stored homotopy inverses on the
old stages and inserts the corrected terminal homotopy inverse at the new last stage. -/
private theorem StrictPreimagePrefix.extend_alpha_beta_homotopy_at
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    Nonempty
      (Homotopy
        ((Fin.lastCases S.extension_alpha S.α m) ≫
          (Fin.lastCases S.extension_raw_beta S.β m))
        (𝟙 _)) := by
  cases m using Fin.lastCases with
  | last =>
      -- The last stage uses the normalized projection homotopy inverse.
      simpa using S.extension_alpha_beta_homotopy
  | cast j =>
      -- Earlier stage homotopies are inherited from the old prefix.
      simpa using S.α_β_homotopy j

/-- Helper for Lemma 15.88.7: extend a finite strict prefix by keeping all old stages unchanged
and inserting the corrected terminal stage obtained from the one-step strictification. -/
private noncomputable abbrev StrictPreimagePrefix.extend
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) :
    StrictPreimagePrefix (A := A) (ρ := ρ) N (length + 1) :=
  { L := Fin.lastCases S.extension_raw_complex S.L
    β := Fin.lastCases S.extension_raw_beta S.β
    α := Fin.lastCases S.extension_alpha S.α
    τ := S.extend_transition_at
    β_compat := S.extend_beta_compat_at
    α_compat := S.extend_alpha_compat_at
    τ_splitEpi := S.extend_transition_splitEpi_at
    β_α := S.extend_beta_alpha_at
    α_β_homotopy := S.extend_alpha_beta_homotopy_at }

/-- Helper for Lemma 15.88.7: after extension, every earlier stage complex is recovered verbatim
on the `castSucc` part of the larger prefix. -/
@[simp] private theorem StrictPreimagePrefix.extend_L_castSucc
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    S.extend.L (Fin.castSucc m) = S.L m := by
  -- `Fin.lastCases` is definitionally the old data away from the new final index.
  simp [StrictPreimagePrefix.extend]

/-- Helper for Lemma 15.88.7: after extension, every earlier inclusion map is recovered verbatim
on the `castSucc` part of the larger prefix. -/
@[simp] private theorem StrictPreimagePrefix.extend_beta_castSucc
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    S.extend.β (Fin.castSucc m) = S.β m := by
  -- The extension only changes the newly appended terminal stage.
  simp [StrictPreimagePrefix.extend]

/-- Helper for Lemma 15.88.7: after extension, every earlier projection map is recovered verbatim
on the `castSucc` part of the larger prefix. -/
@[simp] private theorem StrictPreimagePrefix.extend_alpha_castSucc
    {N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : StrictPreimagePrefix (A := A) (ρ := ρ) N length) (m : Fin (length + 1)) :
    S.extend.α (Fin.castSucc m) = S.α m := by
  -- The extension only changes the newly appended terminal stage.
  simp [StrictPreimagePrefix.extend]

/-- Helper for Lemma 15.88.7: recursively strictify every finite initial segment of the canonical
preimage complex by repeating the one-step extension procedure. -/
private noncomputable def strictPreimagePrefix
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    (length : ℕ) → StrictPreimagePrefix (A := A) (ρ := ρ) N length
  | 0 => StrictPreimagePrefix.base (A := A) (ρ := ρ) N
  | length + 1 => (strictPreimagePrefix N length).extend

/-- Helper for Lemma 15.88.7: the diagonal strict complex at stage `n` is the terminal complex of
the recursively strictified prefix of length `n`. -/
private noncomputable abbrev diagonal_complex
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    CochainComplex
      (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)) ℤ :=
  (strictPreimagePrefix (A := A) (ρ := ρ) N n).L (Fin.last n)

/-- Helper for Lemma 15.88.7: the diagonal inclusion at stage `n` compares the canonical
evaluation of the preimage complex with the diagonal strict complex. -/
private noncomputable abbrev diagonal_beta
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N ⟶
      diagonal_complex (A := A) (ρ := ρ) N n :=
  (strictPreimagePrefix (A := A) (ρ := ρ) N n).β (Fin.last n)

/-- Helper for Lemma 15.88.7: the diagonal projection at stage `n` compares the diagonal strict
complex back to the canonical evaluation of the preimage complex. -/
private noncomputable abbrev diagonal_alpha
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_complex (A := A) (ρ := ρ) N n ⟶
      sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N :=
  (strictPreimagePrefix (A := A) (ρ := ρ) N n).α (Fin.last n)

/-- Helper for Lemma 15.88.7: the last successor map in the `(n + 1)`-prefix is the raw diagonal
transition before transport-cleaning the copied stage `n` in that prefix. -/
private noncomputable abbrev diagonal_step_to_prefix_target
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).L (Fin.succ (Fin.last n)) ⟶
      sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) n
        ((strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).L (Fin.castSucc (Fin.last n))) :=
  (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).τ (Fin.last n)

/-- Helper for Lemma 15.88.7: the copy of stage `n` sitting inside the `(n + 1)`-prefix is
literally the same complex as the diagonal stage `n`. -/
@[simp] private theorem strictPreimagePrefix_castSucc_last_complex
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).L (Fin.castSucc (Fin.last n)) =
      diagonal_complex (A := A) (ρ := ρ) N n := by
  -- The recursive extension preserves the old terminal complex under `castSucc`.
  simpa [diagonal_complex, strictPreimagePrefix] using
    (StrictPreimagePrefix.extend_L_castSucc
      (A := A) (ρ := ρ) (S := strictPreimagePrefix (A := A) (ρ := ρ) N n) (m := Fin.last n))

/-- Helper for Lemma 15.88.7: the copied stage-`n` inclusion inside the `(n + 1)`-prefix is
literally the diagonal inclusion of stage `n`. -/
@[simp] private theorem strictPreimagePrefix_castSucc_last_beta
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).β (Fin.castSucc (Fin.last n)) =
      diagonal_beta (A := A) (ρ := ρ) N n := by
  -- The recursive extension preserves the old terminal inclusion under `castSucc`.
  simpa [diagonal_beta, strictPreimagePrefix] using
    (StrictPreimagePrefix.extend_beta_castSucc
      (A := A) (ρ := ρ) (S := strictPreimagePrefix (A := A) (ρ := ρ) N n) (m := Fin.last n))

/-- Helper for Lemma 15.88.7: the copied stage-`n` projection inside the `(n + 1)`-prefix is
literally the diagonal projection of stage `n`. -/
@[simp] private theorem strictPreimagePrefix_castSucc_last_alpha
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).α (Fin.castSucc (Fin.last n)) =
      diagonal_alpha (A := A) (ρ := ρ) N n := by
  -- The recursive extension preserves the old terminal projection under `castSucc`.
  simpa [diagonal_alpha, strictPreimagePrefix] using
    (StrictPreimagePrefix.extend_alpha_castSucc
      (A := A) (ρ := ρ) (S := strictPreimagePrefix (A := A) (ρ := ρ) N n) (m := Fin.last n))

/-- Helper for Lemma 15.88.7: the last strict successor map in the `(n + 1)`-prefix already
satisfies the diagonal inclusion compatibility, before the copied target stage is transport-cleaned
to the literal diagonal stage `n`. -/
private theorem diagonal_step_to_prefix_target_beta_compat
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_beta (A := A) (ρ := ρ) N (n + 1) ≫
        diagonal_step_to_prefix_target (A := A) (ρ := ρ) N n =
      sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map
          ((strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).β
            (Fin.castSucc (Fin.last n))) := by
  -- Read the stored compatibility at the last index of the `(n + 1)`-prefix.
  simpa [diagonal_beta, diagonal_step_to_prefix_target, strictPreimagePrefix, Fin.succ_last] using
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).β_compat (Fin.last n)

/-- Helper for Lemma 15.88.7: the same last successor map also satisfies the diagonal projection
compatibility before transport-cleaning the copied target stage. -/
private theorem diagonal_step_to_prefix_target_alpha_compat
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_alpha (A := A) (ρ := ρ) N (n + 1) ≫
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N =
      diagonal_step_to_prefix_target (A := A) (ρ := ρ) N n ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map
          ((strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).α
            (Fin.castSucc (Fin.last n))) := by
  -- Read the stored compatibility at the last index of the `(n + 1)`-prefix.
  simpa [diagonal_alpha, diagonal_step_to_prefix_target, strictPreimagePrefix, Fin.succ_last] using
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).α_compat (Fin.last n)

/-- Helper for Lemma 15.88.7: each degree of the last successor map in the `(n + 1)`-prefix is
already split epic, before the copied target stage is transport-cleaned to the literal diagonal
stage `n`. -/
private theorem diagonal_step_to_prefix_target_splitEpi
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) (i : ℤ) :
    IsSplitEpi ((diagonal_step_to_prefix_target (A := A) (ρ := ρ) N n).f i) := by
  -- This is the stored split-epimorphicity of the last transition in the `(n + 1)`-prefix.
  simpa [diagonal_step_to_prefix_target, strictPreimagePrefix] using
    (strictPreimagePrefix (A := A) (ρ := ρ) N (n + 1)).τ_splitEpi (Fin.last n) i

/-- Helper for Lemma 15.88.7: the literal diagonal transition map is obtained by transport-cleaning
the copied stage `n` inside the `(n + 1)`-prefix to the actual diagonal stage `n`. -/
private noncomputable abbrev diagonal_step
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_complex (A := A) (ρ := ρ) N (n + 1) ⟶
      sequentialRingedModuleCochainRestrict (A := A) (ρ := ρ) n
        (diagonal_complex (A := A) (ρ := ρ) N n) :=
  diagonal_step_to_prefix_target (A := A) (ρ := ρ) N n ≫
    ((sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).mapIso
      (eqToIso (strictPreimagePrefix_castSucc_last_complex (A := A) (ρ := ρ) N n))).hom

/-- Helper for Lemma 15.88.7: after transport-cleaning the copied target stage, the literal
diagonal transition still satisfies the diagonal inclusion compatibility. -/
private theorem diagonal_step_beta_compat
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_beta (A := A) (ρ := ρ) N (n + 1) ≫
        diagonal_step (A := A) (ρ := ρ) N n =
      sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map
          (diagonal_beta (A := A) (ρ := ρ) N n) := by
  -- The transport-cleaning only replaces the copied target stage by the literal diagonal stage.
  simpa [diagonal_step] using diagonal_step_to_prefix_target_beta_compat (A := A) (ρ := ρ) N n

/-- Helper for Lemma 15.88.7: after the same transport-cleaning, the literal diagonal transition
also satisfies the diagonal projection compatibility. -/
private theorem diagonal_step_alpha_compat
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    diagonal_alpha (A := A) (ρ := ρ) N (n + 1) ≫
        sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n N =
      diagonal_step (A := A) (ρ := ρ) N n ≫
        (sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).map
          (diagonal_alpha (A := A) (ρ := ρ) N n) := by
  -- The same transport-cleaning converts the copied terminal projection into the literal diagonal
  -- projection of stage `n`.
  simpa [diagonal_step] using diagonal_step_to_prefix_target_alpha_compat (A := A) (ρ := ρ) N n

/-- Helper for Lemma 15.88.7: each degree of the literal diagonal transition map is split epic. -/
private theorem diagonal_step_splitEpi
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) (i : ℤ) :
    IsSplitEpi ((diagonal_step (A := A) (ρ := ρ) N n).f i) := by
  -- Transport-cleaning along an identity-on-components equality does not change the split-epi
  -- witness.
  simpa [diagonal_step] using diagonal_step_to_prefix_target_splitEpi (A := A) (ρ := ρ) N n i

/-- Helper for Lemma 15.88.7: the underlying additive presheaf of the reassembled diagonal term in
degree `i`, obtained by the source-faithful `Functor.ofOpSequence` construction from the strict
diagonal stage objects and successor maps. -/
private abbrev diagonal_reassembled_X_presheaf
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat :=
  CategoryTheory.Functor.ofOpSequence
    (fun n ↦ AddCommGrpCat.ofHom ((diagonal_step (A := A) (ρ := ρ) N n).f i).hom)

/-- Helper for Lemma 15.88.7: the `n`-th stage of the reassembled degree-`i` presheaf is exactly
the `i`-th term of the `n`-th diagonal stage complex. -/
@[simp] private theorem diagonal_reassembled_X_presheaf_obj
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) (n : ℕᵒᵖ) :
    (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).obj n =
      AddCommGrpCat.of ((diagonal_complex (A := A) (ρ := ρ) N n.unop).X i) := by
  cases n
  rfl

/-- Helper for Lemma 15.88.7: the successor map in the reassembled degree-`i` presheaf is the
chosen diagonal transition map in degree `i`. -/
@[simp] private theorem diagonal_reassembled_X_presheaf_map_succ
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) (n : ℕ) :
    (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map
        ((homOfLE (Nat.le_succ n)).op) =
      AddCommGrpCat.ofHom ((diagonal_step (A := A) (ρ := ρ) N n).f i).hom := by
  rfl

/-- Helper for Lemma 15.88.7: every longer transition in the reassembled degree-`i` presheaf
factors through the final successor map, exactly as in the underlying `Functor.ofOpSequence`
construction. -/
private theorem diagonal_reassembled_X_presheaf_map_homOfLE_succ
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) {m k : ℕ} (h : m ≤ k) :
    (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map
        (homOfLE (Nat.le_succ_of_le h)).op =
      (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map
          ((homOfLE (Nat.le_succ k)).op) ≫
        (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map (homOfLE h).op := by
  let F := diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i
  -- In `ℕᵒᵖ`, the longer arrow uniquely factors through the final successor arrow.
  have hh :
      (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := by
    subsingleton
  simpa [F, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 15.88.7: every transition map in the reassembled degree-`i` additive
presheaf is linear with respect to the corresponding ring transition map. -/
private theorem diagonal_reassembled_X_presheaf_map_smul
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) :
    ∀ {m n : ℕ} (h : m ≤ n)
      (r : sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)
      (x : (diagonal_complex (A := A) (ρ := ρ) N n).X i),
      AddCommGrpCat.Hom.hom
          ((diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map (homOfLE h).op)
          (r • x) =
        (((sequentialRingSystem A ρ).map (homOfLE h).op).hom r) •
          AddCommGrpCat.Hom.hom
            ((diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i).map (homOfLE h).op) x := by
  intro m n h
  induction h with
  | refl =>
      intro r x
      -- The identity transition is linear over the identity ring map.
      simp [sequentialRingSystem]
  | @step k h ih =>
      intro r x
      let F := diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i
      -- First expose the final successor map, whose linearity is inherited from `diagonal_step`.
      have hsucc :
          AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) (r • x) =
            (((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r) •
              AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x := by
        simpa [F, diagonal_reassembled_X_presheaf_map_succ, sequentialRingSystem] using
          (((diagonal_step (A := A) (ρ := ρ) N k).f i).hom.map_smul r x)
      have hRing :
          (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) =
            ((sequentialRingSystem A ρ).map (homOfLE h).op).hom
              ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)) := by
        -- The ring-system transition maps factor through the same final successor arrow.
        have hh :
            (homOfLE (Nat.le_succ_of_le h)).op =
              (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := by
          subsingleton
        simpa [sequentialRingSystem, Functor.map_comp, RingHom.comp_apply] using
          congrArg
            (fun f ↦ CommRingCat.Hom.hom ((sequentialRingSystem A ρ).map f) r)
            hh
      -- Now apply the induction hypothesis to the shorter tail after rewriting the long arrow.
      rw [diagonal_reassembled_X_presheaf_map_homOfLE_succ (A := A) (ρ := ρ) N i h]
      calc
        AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op) ≫ F.map (homOfLE h).op)
            (r • x) =
            AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
              (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) (r • x)) := by
              rfl
        _ =
            AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
              ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r) •
                AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              rw [hsucc]
        _ =
            ((sequentialRingSystem A ρ).map (homOfLE h).op).hom
                ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)) •
              AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
                (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              simpa using
                ih
                  (((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)
                  (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x)
        _ =
            (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) •
              AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
                (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              rw [← hRing]
        _ =
            (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) •
              AddCommGrpCat.Hom.hom
                (F.map ((homOfLE (Nat.le_succ k)).op) ≫ F.map (homOfLE h).op) x := by
              rfl

/-- Helper for Lemma 15.88.7: the source-faithful reassembled degree-`i` object of
`\mathrm{Mod}(\mathbf N, (A_n))`, whose stage `n` is the degree-`i` term of the diagonal stage
complex and whose successor map is the degree-`i` component of `diagonal_step`. -/
private def diagonal_reassembled_X
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) :
    SeqRingMod A ρ :=
  { val :=
      PresheafOfModules.ofPresheaf
        (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i)
        (fun {X Y} f r m ↦ by
          cases X using Opposite.rec
          cases Y using Opposite.rec
          let h : Y ≤ X := by
            simpa using f.unop
          have hf : f = (homOfLE h).op := by
            subsingleton
          subst hf
          simpa using
            diagonal_reassembled_X_presheaf_map_smul (A := A) (ρ := ρ) N i h r m)
    isSheaf := by
      -- The indexing topology is chaotic, so every underlying additive presheaf is already a
      -- sheaf; we transport that owner fact through `PresheafOfModules.ofPresheaf`.
      simpa [PresheafOfModules.ofPresheaf_presheaf] using
        (Presheaf.isSheaf_bot (diagonal_reassembled_X_presheaf (A := A) (ρ := ρ) N i)) }

/-- Helper for Lemma 15.88.7: evaluating the reassembled degree-`i` object at stage `n` recovers
the `i`-th term of the `n`-th diagonal stage complex. -/
@[simp] private theorem diagonal_reassembled_X_obj
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) (n : ℕ) :
    (diagonal_reassembled_X (A := A) (ρ := ρ) N i).val.obj (Opposite.op n) =
      (diagonal_complex (A := A) (ρ := ρ) N n).X i := by
  rfl

/-- Helper for Lemma 15.88.7: the successor map of the reassembled degree-`i` object is exactly
the degree-`i` component of the diagonal transition map. -/
@[simp] private theorem diagonal_reassembled_X_map_succ
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) (n : ℕ) :
    (diagonal_reassembled_X (A := A) (ρ := ρ) N i).val.map ((homOfLE (Nat.le_succ n)).op) =
      (diagonal_step (A := A) (ρ := ρ) N n).f i := by
  rfl

/-- Helper for Lemma 15.88.7: the reassembled differential `d : X^i → X^j` is the stagewise
family of diagonal differentials, assembled as a morphism in `SeqRingMod`. -/
private def diagonal_reassembled_d
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i j : ℤ) :
    diagonal_reassembled_X (A := A) (ρ := ρ) N i ⟶
      diagonal_reassembled_X (A := A) (ρ := ρ) N j :=
  { val :=
      PresheafOfModules.homMk
        (NatTrans.ofOpSequence
          (fun n ↦ AddCommGrpCat.ofHom ((diagonal_complex (A := A) (ρ := ρ) N n).d i j).hom)
          (fun n ↦ by
            -- Each diagonal transition is a chain map, so the stagewise differentials commute
            -- with the successor maps.
            simpa [diagonal_reassembled_X_presheaf_map_succ] using
              (diagonal_step (A := A) (ρ := ρ) N n).comm i j))
        (fun X r m ↦ by
          -- The stagewise differential is linear over the ring at stage `X`.
          cases X using Opposite.rec
          rfl) }

/-- Helper for Lemma 15.88.7: evaluating the reassembled differential at stage `n` gives the
ordinary differential of the `n`-th diagonal stage complex. -/
@[simp] private theorem diagonal_reassembled_d_app
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i j : ℤ) (n : ℕ) :
    (diagonal_reassembled_d (A := A) (ρ := ρ) N i j).val.app (Opposite.op n) =
      (diagonal_complex (A := A) (ρ := ρ) N n).d i j := by
  rfl

/-- Helper for Lemma 15.88.7: the diagonal stages reassemble into a single cochain complex in
`\mathrm{Mod}(\mathbf N, (A_n))`, degreewise by `diagonal_reassembled_X` and with differentials
assembled from the stagewise diagonal differentials. -/
private def diagonal_reassembled_complex
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    CochainComplex.{0} (SeqRingMod A ρ) ℤ :=
  { X := diagonal_reassembled_X (A := A) (ρ := ρ) N
    d := diagonal_reassembled_d (A := A) (ρ := ρ) N
    shape := by
      intro i j hij
      -- The reassembled differential has the same shape relation because every diagonal stage is
      -- already a cochain complex.
      ext n x
      change ((diagonal_complex (A := A) (ρ := ρ) N n.unop).d i j).hom x = 0
      simpa using
        congrArg
          (fun f :
            (diagonal_complex (A := A) (ρ := ρ) N n.unop).X i ⟶
              (diagonal_complex (A := A) (ρ := ρ) N n.unop).X j ↦ f.hom x)
          ((diagonal_complex (A := A) (ρ := ρ) N n.unop).shape i j hij)
    d_comp_d' := by
      intro i j k hij hjk
      -- The cochain identity `d ≫ d = 0` is checked stagewise against the diagonal stage
      -- complexes.
      ext n x
      change
        (((diagonal_complex (A := A) (ρ := ρ) N n.unop).d i j ≫
            (diagonal_complex (A := A) (ρ := ρ) N n.unop).d j k).hom x) = 0
      simpa using
        congrArg
          (fun f :
            (diagonal_complex (A := A) (ρ := ρ) N n.unop).X i ⟶
              (diagonal_complex (A := A) (ρ := ρ) N n.unop).X k ↦ f.hom x)
          ((diagonal_complex (A := A) (ρ := ρ) N n.unop).d_comp_d' i j k hij hjk) }

/-- Helper for Lemma 15.88.7: evaluating the reassembled complex at stage `n` literally recovers
the `n`-th diagonal stage complex. -/
private noncomputable def diagonal_reassembled_eval_iso
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n
        (diagonal_reassembled_complex (A := A) (ρ := ρ) N) ≅
      diagonal_complex (A := A) (ρ := ρ) N n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ eqToIso (by simp [diagonal_reassembled_complex]))
    (fun i j hij ↦ by
      -- Evaluation identifies both differentials with the same stagewise diagonal differential.
      change (𝟙 _) ≫ (diagonal_complex (A := A) (ρ := ρ) N n).d i j =
        (diagonal_complex (A := A) (ρ := ρ) N n).d i j ≫ 𝟙 _
      simp)

/-- Helper for Lemma 15.88.7: after conjugating by the evaluation isomorphisms, the evaluated
successor map of the reassembled complex is exactly the diagonal transition map. -/
private theorem diagonal_reassembled_eval_iso_naturality
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n
        (diagonal_reassembled_complex (A := A) (ρ := ρ) N) ≫
      ((sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).mapIso
        (diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N n)).hom =
        (diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N (n + 1)).hom ≫
          diagonal_step (A := A) (ρ := ρ) N n := by
  -- The source-faithful reassembly was chosen so that the successor map is definitionally the
  -- original diagonal transition on every cochain degree.
  ext i x
  simpa [diagonal_reassembled_complex]

/-- Helper for Lemma 15.88.7: the stagewise diagonal projections reassemble into a global chain
map from the reassembled diagonal complex back to the original complex. -/
private def diagonal_reassembled_alpha
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) :
    diagonal_reassembled_complex (A := A) (ρ := ρ) N ⟶ N :=
  { f := fun i ↦
      { val :=
          PresheafOfModules.homMk
            (NatTrans.ofOpSequence
              (fun n ↦ AddCommGrpCat.ofHom ((diagonal_alpha (A := A) (ρ := ρ) N n).f i).hom)
              (fun n ↦ by
                -- The stagewise projection squares are exactly the compatibility needed for the
                -- underlying presheaf natural transformation.
                simpa [diagonal_reassembled_X_presheaf_map_succ, Category.assoc] using
                  congrArg
                    (fun k ↦ k.f i)
                    (diagonal_step_alpha_compat (A := A) (ρ := ρ) N n)))
            (fun X r m ↦ by
              -- Each stagewise projection component is linear over the local stage ring.
              cases X using Opposite.rec
              rfl) }
    comm' := by
      intro i j hij
      -- Chain-map compatibility is checked stagewise against the diagonal projection maps.
      ext n x
      change
        (((diagonal_complex (A := A) (ρ := ρ) N n.unop).d i j ≫
            (diagonal_alpha (A := A) (ρ := ρ) N n.unop).f j).hom x) =
          (((diagonal_alpha (A := A) (ρ := ρ) N n.unop).f i ≫ (N.d i j).val.app n).hom x)
      simpa using
        congrArg
          (fun f :
            (diagonal_complex (A := A) (ρ := ρ) N n.unop).X i ⟶
              (sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n.unop N).X j ↦
                f.hom x)
          ((diagonal_alpha (A := A) (ρ := ρ) N n.unop).comm i j) }

/-- Helper for Lemma 15.88.7: evaluating the global diagonal projection at stage `n` recovers the
stagewise diagonal projection map. -/
@[simp] private theorem diagonal_reassembled_alpha_app
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (i : ℤ) (n : ℕ) :
    ((diagonal_reassembled_alpha (A := A) (ρ := ρ) N).f i).val.app (Opposite.op n) =
      (diagonal_alpha (A := A) (ρ := ρ) N n).f i := by
  rfl

/-- Helper for Lemma 15.88.7: evaluate a morphism of complexes degreewise at stage `n` using the
same lower-universe model as `sequentialRingedModuleCochainEvalLow`. -/
private theorem sequentialRingedModuleCochainEvalMapLow_comm
    (n : ℕ)
    {M N : CochainComplex.{0} (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    (α.f i).val.app (Opposite.op n) ≫ (N.d i j).val.app (Opposite.op n) =
      (M.d i j).val.app (Opposite.op n) ≫ (α.f j).val.app (Opposite.op n) := by
  -- This is the stagewise evaluation of chain-map commutativity.
  simpa using congrArg (fun f ↦ f.val.app (Opposite.op n)) (α.comm i j)

/-- Helper for Lemma 15.88.7: evaluate a morphism of complexes degreewise at stage `n` using the
lower-universe stagewise model fixed in this file. -/
private def sequentialRingedModuleCochainEvalMapLow
    (n : ℕ) {M N : CochainComplex.{0} (SeqRingMod A ρ) ℤ} (α : M ⟶ N) :
    sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n M ⟶
      sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N :=
  { f := fun i ↦ (α.f i).val.app (Opposite.op n)
    comm' := sequentialRingedModuleCochainEvalMapLow_comm (A := A) (ρ := ρ) n α }

/-- Helper for Lemma 15.88.7: the stagewise evaluation family on `Mod(\mathbf N, (A_n))` is
conservative because a morphism of sheaves on the chaotic site is an isomorphism exactly when all
components are isomorphisms. -/
private theorem sequentialRingedModuleEvaluation_jointly_reflects_isomorphisms :
    JointlyReflectIsomorphisms (fun n : ℕ ↦ sequentialRingedModuleEvaluation A ρ n) := by
  refine ⟨fun {X Y} f _hf ↦ ?_⟩
  -- Unpack the sheaf morphism to the underlying natural transformation and check componentwise.
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  simpa [sequentialRingedModuleEvaluation] using
    (inferInstance : IsIso (((sequentialRingedModuleEvaluation A ρ n).map f)))

/-- Helper for Lemma 15.88.7: exactness of a short complex in `Mod(\mathbf N, (A_n))` can be
checked stagewise after evaluating at every ring `A_n`. -/
private theorem sequentialRingedModule_shortComplex_exact_iff_eval
    (S : ShortComplex (SeqRingMod A ρ)) :
    S.Exact ↔ ∀ n : ℕ, (S.map (sequentialRingedModuleEvaluation A ρ n)).Exact := by
  -- The evaluation family is conservative on `SeqRingMod`, so exactness is reflected and
  -- detected on the stagewise module short complexes.
  exact (sequentialRingedModuleEvaluation_jointly_reflects_isomorphisms
    (A := A) (ρ := ρ)).exact_iff S

/-- Helper for Lemma 15.88.7: every stagewise diagonal projection is already a quasi-isomorphism
because the finite strict prefix data provide a homotopy inverse and the two homotopies at the
terminal stage. -/
private theorem diagonal_alpha_stagewise_quasiIso
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    QuasiIso (diagonal_alpha (A := A) (ρ := ρ) N n) := by
  let e :
      HomotopyEquiv
        (diagonal_complex (A := A) (ρ := ρ) N n)
        (sequentialRingedModuleCochainEvalLow (A := A) (ρ := ρ) n N) :=
    { hom := diagonal_alpha (A := A) (ρ := ρ) N n
      inv := diagonal_beta (A := A) (ρ := ρ) N n
      homotopyHomInvId := by
        -- The terminal stage of the strict prefix already stores the homotopy
        -- `diagonal_alpha ≫ diagonal_beta ∼ 𝟙`.
        simpa [diagonal_alpha, diagonal_beta] using
          (strictPreimagePrefix (A := A) (ρ := ρ) N n).α_β_homotopy (Fin.last n)
      homotopyInvHomId := by
        -- The opposite composite is the stored strict retract identity, viewed as a constant
        -- homotopy.
        refine Homotopy.ofEq ?_
        simpa [diagonal_alpha, diagonal_beta] using
          (strictPreimagePrefix (A := A) (ρ := ρ) N n).β_α (Fin.last n) }
  -- The standard owner bridge upgrades a homotopy equivalence to a quasi-isomorphism.
  exact (show QuasiIso e.hom from inferInstance)

/-- Helper for Lemma 15.88.7: after evaluating at stage `n`, the global diagonal projection is the
stagewise diagonal projection preceded by the canonical evaluation isomorphism. -/
private theorem diagonal_reassembled_alpha_evalLow_comp
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n
        (diagonal_reassembled_alpha (A := A) (ρ := ρ) N) =
      (diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N n).hom ≫
        diagonal_alpha (A := A) (ρ := ρ) N n := by
  -- Both maps have the same degreewise components after evaluation at stage `n`.
  ext i x
  rfl

/-- Helper for Lemma 15.88.7: every evaluated stage of the global diagonal projection is a
quasi-isomorphism because it is the composition of the evaluation isomorphism with the known
stagewise diagonal quasi-isomorphism. -/
private theorem diagonal_reassembled_alpha_evalLow_quasiIso
    (N : CochainComplex.{0} (SeqRingMod A ρ) ℤ) (n : ℕ) :
    QuasiIso
      (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n
        (diagonal_reassembled_alpha (A := A) (ρ := ρ) N)) := by
  letI : QuasiIso ((diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N n).hom) := inferInstance
  letI : QuasiIso (diagonal_alpha (A := A) (ρ := ρ) N n) :=
    diagonal_alpha_stagewise_quasiIso (A := A) (ρ := ρ) N n
  -- Rewrite the evaluated map as the canonical composite and use closure of quasi-isomorphisms
  -- under composition.
  simpa [diagonal_reassembled_alpha_evalLow_comp] using
    (quasiIso_comp
      ((diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N n).hom)
      (diagonal_alpha (A := A) (ρ := ρ) N n))

/-- Helper for Lemma 15.88.7: evaluating the degree-`i` short-complex morphism of `α` is
definitionally the same as taking the degree-`i` short-complex morphism of the evaluated chain
map. -/
private theorem sequentialRingedModuleEvalLow_shortComplex_map
    (n : ℕ) {M N : CochainComplex.{0} (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N) (i : ℤ) :
    (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor (SeqRingMod A ρ) (ComplexShape.up ℤ) i).map α)) =
      ((HomologicalComplex.shortComplexFunctor
          (ModuleCat.{0} (sequentialRingedModuleStageRing (A := A) (ρ := ρ) n))
          (ComplexShape.up ℤ) i).map
        (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n α)) := by
  -- Each component of the mapped short-complex morphism is definitionally the evaluated
  -- component of `α`.
  ext <;> rfl

/-- Helper for Lemma 15.88.7: if every evaluated short-complex map is a quasi-isomorphism, then
the evaluated homology map of the original short-complex morphism is an isomorphism at every
stage. -/
private theorem sequentialRingedModule_shortComplex_homologyMap_isIso_of_eval
    {S₁ S₂ : ShortComplex (SeqRingMod A ρ)}
    (φ : S₁ ⟶ S₂)
    (hφ : ∀ n : ℕ,
      ShortComplex.QuasiIso
        (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) :
    ∀ n : ℕ,
      IsIso
        ((sequentialRingedModuleEvaluation A ρ n).map (ShortComplex.homologyMap φ)) := by
  intro n
  let F := sequentialRingedModuleEvaluation A ρ n
  have hφn :
      IsIso (ShortComplex.homologyMap (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) := by
    -- The stagewise hypothesis already says that the evaluated short-complex homology map is an
    -- isomorphism.
    rw [← ShortComplex.quasiIso_iff]
    exact hφ n
  have hrewrite :
      F.map (ShortComplex.homologyMap φ) =
        (S₁.mapHomologyIso F).inv ≫
          ShortComplex.homologyMap ((F.mapShortComplex).map φ) ≫
          (S₂.mapHomologyIso F).hom := by
    -- Move the global homology map across stagewise evaluation using the canonical homology
    -- comparison isomorphisms.
    calc
      F.map (ShortComplex.homologyMap φ) =
          F.map (ShortComplex.homologyMap φ) ≫
            (S₂.mapHomologyIso F).inv ≫
              (S₂.mapHomologyIso F).hom := by
        simp [Category.assoc]
      _ =
          (S₁.mapHomologyIso F).inv ≫
            ShortComplex.homologyMap ((F.mapShortComplex).map φ) ≫
              (S₂.mapHomologyIso F).hom := by
        rw [ShortComplex.mapHomologyIso_inv_naturality]
        simp [Category.assoc]
  -- After this rewrite, the evaluated homology map is a composition of isomorphisms.
  rw [hrewrite]
  infer_instance

/-- Helper for Lemma 15.88.7: a morphism of short complexes in `\mathrm{Mod}(\mathbf N, (A_n))`
is a quasi-isomorphism once all of its stagewise evaluations are quasi-isomorphisms. -/
private theorem sequentialRingedModule_shortComplex_quasiIso_of_eval
    {S₁ S₂ : ShortComplex (SeqRingMod A ρ)}
    (φ : S₁ ⟶ S₂)
    (hφ : ∀ n : ℕ,
      ShortComplex.QuasiIso
        (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) :
    ShortComplex.QuasiIso φ := by
  -- Reflect the short-complex homology map across the conservative family of stagewise
  -- evaluations.
  rw [ShortComplex.quasiIso_iff]
  exact
    ((sequentialRingedModuleEvaluation_jointly_reflects_isomorphisms
        (A := A) (ρ := ρ)).isIso_iff (ShortComplex.homologyMap φ)).2
      (sequentialRingedModule_shortComplex_homologyMap_isIso_of_eval
        (A := A) (ρ := ρ) φ hφ)

/-- Helper for Lemma 15.88.7: stagewise quasi-isomorphy of the evaluated chain maps implies
degreewise quasi-isomorphy of the original chain map. -/
private theorem quasiIsoAt_of_stagewise_evalLow_quasiIso
    {M N : CochainComplex.{0} (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N) (i : ℤ)
    (hα : ∀ n : ℕ,
      QuasiIso (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n α)) :
    QuasiIsoAt α i := by
  -- Reduce the degree-`i` quasi-isomorphism claim to the corresponding short-complex morphism and
  -- reflect it from all stagewise evaluations.
  rw [_root_.quasiIsoAt_iff]
  refine
    sequentialRingedModule_shortComplex_quasiIso_of_eval
      (A := A) (ρ := ρ)
      ((HomologicalComplex.shortComplexFunctor
          (SeqRingMod A ρ) (ComplexShape.up ℤ) i).map α) ?_
  intro n
  have hαn : QuasiIsoAt
      (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n α) i :=
    ((_root_.quasiIso_iff
      (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n α)).1 (hα n)) i
  -- The evaluated degree-`i` short-complex map is definitionally the short-complex map of the
  -- evaluated chain map.
  rw [_root_.quasiIsoAt_iff] at hαn
  simpa [sequentialRingedModuleEvalLow_shortComplex_map] using hαn

/-- Helper for Lemma 15.88.7: if a morphism of complexes in `\mathrm{Mod}(\mathbf N, (A_n))` is a
quasi-isomorphism after evaluating at every stage, then it is already a global quasi-isomorphism.
-/
private theorem quasiIso_of_stagewise_evalLow_quasiIso
    {M N : CochainComplex.{0} (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N)
    (hα : ∀ n : ℕ,
      QuasiIso (sequentialRingedModuleCochainEvalMapLow (A := A) (ρ := ρ) n α)) :
    QuasiIso α := by
  -- Route correction: instead of invoking the global reflection theorem directly, reduce to each
  -- degree and reflect the corresponding short-complex homology map across evaluations.
  rw [_root_.quasiIso_iff]
  intro i
  exact quasiIsoAt_of_stagewise_evalLow_quasiIso (A := A) (ρ := ρ) α i hα

/- Domain-style sampling for Lemma 15.88.7:
- primary domain: cochain-complex representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`, together with their stagewise restriction maps;
- sampled declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `DerivedCategory.Q.objObjPreimageIso`,
  `sequentialRingedModuleCochainEvaluationStep`,
  `cochainComplex_epi_iff_degreewise_epi`;
- best owner abstraction: a representative complex `M` together with its canonical identification
  `DerivedCategory.Q.obj M ≅ K`; the chosen preimage `DerivedCategory.Q.objPreimage K` is only an
  internal bridge to that owner surface;
- target layer here: the `source-facing` existence of a representative whose stagewise transition
  maps are termwise epimorphic, together with the bridge/view expressing the same condition as a
  complex-level `Epi`;
- primitive data: the representative complex `M` and its isomorphism `DerivedCategory.Q.obj M ≅
  K`;
- derived API: the stagewise evaluation complexes and their restriction maps; the complex-level
  `Epi` formulation is derived from the source-facing degreewise condition via
  `cochainComplex_epi_iff_degreewise_epi`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise transition maps are
  termwise surjective;
- `core/canonical`: the derived-category realization owner `DerivedCategory.Q.obj`;
- `bridge/view`: the internal preimage comparison `DerivedCategory.Q.objObjPreimageIso K` and the
  cochain-level evaluation-step morphisms `sequentialRingedModuleCochainEvaluationStep A ρ n`. -/

-- Proof sketch: start from the canonical preimage complex `DerivedCategory.Q.objPreimage K`.
-- Evaluating it at each stage `n` gives the system of complexes `M_n^•`, and the structural
-- restriction maps in `\mathrm{Mod}(\mathbf N, (A_n))` induce the transition morphisms
-- `M_{n + 1}^• → M_n^•` after restriction of scalars. Apply Lemma `13.9.8` inductively to replace
-- this canonical preimage by a quasi-isomorphic complex with termwise surjective transition maps.
private theorem exists_complex_representation_with_surjective_transition_maps_to_preimage
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ)
      (α : M ⟶ DerivedCategory.Q.objPreimage K),
      QuasiIso α ∧
      ∀ n i,
        Epi ((sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n M).f i) := by
  let N := DerivedCategory.Q.objPreimage K
  let M := diagonal_reassembled_complex (A := A) (ρ := ρ) N
  let α := diagonal_reassembled_alpha (A := A) (ρ := ρ) N
  refine ⟨M, α, ?_, ?_⟩
  -- Route correction: the imported evaluation-step natural transformation lives in a higher
  -- universe than `DerivedCategory.Q.objPreimage K`, so this file uses the equivalent local
  -- lower-universe adapter above before carrying out the source-faithful strictification argument.
  -- The new prefix structure `StrictPreimagePrefix` now packages the stagewise complexes, both
  -- strict comparison squares, and the recursive extension step built above. The literal diagonal
  -- transition maps `diagonal_step` and their strict compatibility/split-epimorphicity lemmas are
  -- now in place; the remaining work is the global reassembly of the diagonal tower into a single
  -- `SeqRingMod` complex and the packaging of the stagewise homotopy-equivalence data into one
  -- quasi-isomorphism to `DerivedCategory.Q.objPreimage K`.
  · -- Each evaluated map is the known diagonal projection up to the canonical evaluation
    -- isomorphism, so the stagewise quasi-isomorphisms reflect back to a global quasi-isomorphism.
    exact quasiIso_of_stagewise_evalLow_quasiIso (A := A) (ρ := ρ) α
      (fun n ↦ diagonal_reassembled_alpha_evalLow_quasiIso (A := A) (ρ := ρ) N n)
  · intro n i
    let step :=
      ((sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n M).f i)
    let diag := ((diagonal_step (A := A) (ρ := ρ) N n).f i)
    let eSource := ((diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N (n + 1)).hom.f i)
    let eTarget :=
      (((sequentialRingedModuleCochainRestrictFunctor (A := A) (ρ := ρ) n).mapIso
          (diagonal_reassembled_eval_iso (A := A) (ρ := ρ) N n)).hom.f i)
    have hstep :
        step ≫ eTarget = eSource ≫ diag := by
      -- The reassembled evaluation isomorphisms identify the degree-`i` evaluated successor map
      -- with the degree-`i` diagonal transition map.
      simpa [M, step, diag, eSource, eTarget] using
        congrArg (fun k ↦ k.f i)
          (diagonal_reassembled_eval_iso_naturality (A := A) (ρ := ρ) N n)
    letI : IsIso eSource := by
      dsimp [eSource]
      infer_instance
    letI : IsIso eTarget := by
      dsimp [eTarget]
      infer_instance
    letI : IsSplitEpi step := by
      -- Conjugate the chosen section of the split-epimorphic diagonal map across the two
      -- evaluation isomorphisms.
      refine IsSplitEpi.mk' ⟨eTarget ≫ section_ diag ≫ inv eSource, ?_⟩
      calc
        step ≫ (eTarget ≫ section_ diag ≫ inv eSource) =
            (step ≫ eTarget) ≫ section_ diag ≫ inv eSource := by
              simp [Category.assoc]
        _ = (eSource ≫ diag) ≫ section_ diag ≫ inv eSource := by
              rw [hstep]
        _ = eSource ≫ (diag ≫ section_ diag) ≫ inv eSource := by
              simp [Category.assoc]
        _ = eSource ≫ inv eSource := by
              simp [Category.assoc]
        _ = 𝟙 _ := by
              simp
    infer_instance

/-- Lemma 15.88.7: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object
`K ∈ D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a cochain-complex representative `M^•` in
`\mathrm{Mod}(\mathbf N, (A_n))` whose evaluated transition maps
`M_{n + 1}^• → M_n^•` are termwise epimorphic, equivalently termwise surjective after
restriction of scalars along `A_{n + 1} → A_n`. -/
@[stacks 091F]
theorem exists_complex_representation_with_surjective_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n i,
        Epi ((sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n M).f i) := by
  obtain ⟨M, α, hα, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps_to_preimage K
  letI : QuasiIso α := hα
  refine ⟨M, asIso (DerivedCategory.Q.map α) ≪≫ DerivedCategory.Q.objObjPreimageIso K, hM⟩

/-- Companion bridge for Lemma 15.88.7: the same representative may be chosen so that every
evaluated transition map `M_{n + 1}^• → M_n^•` is an epimorphism of cochain complexes. -/
theorem exists_complex_representation_with_epi_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex.{0} (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n,
        Epi (sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n M) := by
  obtain ⟨M, e, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps K
  refine ⟨M, e, ?_⟩
  intro n
  exact (cochainComplex_epi_iff_degreewise_epi
    (sequentialRingedModuleCochainEvaluationStepLow (A := A) (ρ := ρ) n M)).2 (hM n)

end
