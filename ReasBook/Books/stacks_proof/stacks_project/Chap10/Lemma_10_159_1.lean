import StacksProject_2024.Chap10.Lemma_10_159_1.Index

universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Chap10 Lemma 10 159 1: a top residue-extension stage equipped with a morphism from
the base stage already yields the required residue-field `AlgEquiv` over `ResidueField R`. -/
noncomputable def topStageResidueAlgEquivOfBaseHom
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (T : ResidueExtensionStage.{u, v, max u v} (R := R) K
      (⊤ : IntermediateField (ResidueField R) K))
    (f : ResidueExtensionStage.Hom
      (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
      (ResidueExtensionStage.base (R := R) K) T) :
    ResidueField T.A ≃ₐ[ResidueField R] K := by
  let eRing : ResidueField T.A ≃+* K :=
    T.residueEquiv.trans IntermediateField.topEquiv.toRingEquiv
  refine
    { toRingEquiv := eRing
      commutes' := ?_ }
  intro a
  -- Proof comment: reduce the algebra-compatibility check to residues of elements of `R`.
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective a
  have hcomm :
      T.residueToAmbient
          (ResidueField.map (algebraMap R T.A) (residue R r)) =
        algebraMap (ResidueField R) K (residue R r) := by
    have hbasecomm :
        T.residueToAmbient
            (ResidueField.map (algebraMap R T.A) (residue R r)) =
          (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
      have hbasecomm₀ :
          T.residueToAmbient (ResidueField.map f.toAlgHom.toRingHom (residue R r)) =
            (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
        simpa [RingHom.comp_apply] using
          congrArg (fun φ : ResidueField R →+* K ↦ φ (residue R r)) f.residue_comm
      have hbasecomm₁ :
          T.residueToAmbient (residue T.A (f.toAlgHom r)) =
            (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
        simpa [IsLocalRing.ResidueField.map_residue] using hbasecomm₀
      -- Proof comment: the stage morphism from the base stage is an `R`-algebra map, so it
      -- carries `r` to the same element as the structural map `R → T.A`.
      calc
        T.residueToAmbient (ResidueField.map (algebraMap R T.A) (residue R r))
            = T.residueToAmbient (residue T.A ((algebraMap R T.A) r)) := by
                rw [IsLocalRing.ResidueField.map_residue]
        _ = T.residueToAmbient
              (residue T.A
                (f.toAlgHom ((algebraMap R (ResidueExtensionStage.base (R := R) K).A) r))) := by
              rw [← f.toAlgHom.commutes r]
        _ = T.residueToAmbient (residue T.A (f.toAlgHom r)) := by
              rfl
        _ = (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := hbasecomm₁
    -- Proof comment: the base stage residue map is the original scalar map from `ResidueField R`.
    simpa [ResidueExtensionStage.base_residueToAmbient_eq_algebraMap] using hbasecomm
  -- Proof comment: the top-stage residue-field equivalence commutes with the base residue-field
  -- algebra map after rewriting through `ResidueExtensionStage.top_residueToAmbient_eq`.
  calc
    eRing (algebraMap (ResidueField R) (ResidueField T.A) a)
        = eRing (algebraMap (ResidueField R) (ResidueField T.A) (residue R r)) := by
            rw [hr]
    _ = algebraMap (ResidueField R) K (residue R r) := by
          simpa [eRing, ResidueExtensionStage.top_residueToAmbient_eq, RingHom.comp_apply] using
            hcomm
    _ = algebraMap (ResidueField R) K a := by
          rw [hr]

/-- Helper for Chap10 Lemma 10 159 1: once the source-proof recursion produces a top
residue-extension stage over `⊤`, the public theorem is only an unpacking step. -/
theorem existsFlatLocalAlgebraWithResidueFieldEquivOfTopStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (hT :
      ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
          (⊤ : IntermediateField (ResidueField R) K),
        Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
            (ResidueExtensionStage.base (R := R) K) T)) :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : ResidueField R' ≃ₐ[ResidueField R] K),
        Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R' := by
  rcases hT with ⟨T, ⟨f⟩⟩
  -- Proof comment: unpack the stage record itself as the witness ring and use the base-stage map
  -- only for the residue-field algebra compatibility.
  refine ⟨T.A, inferInstance, inferInstance, inferInstance, inferInstance, T.flat, ?_, ?_⟩
  · exact topStageResidueAlgEquivOfBaseHom (R := R) K T f
  · exact T.map_maximalIdeal

/-- Helper for Chap10 Lemma 10 159 1: the terminal closed prefix field in the well-ordered
construction is `⊤`. This isolates the final field-side rewrite used when extracting the top
stage. -/
theorem closedPrefixField_top_eq_top
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    closedPrefixField (R := R) K le_rfl
      (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
        Set.Iic (Ordinal.type (@WellOrderingRel K))) =
      (⊤ : IntermediateField (ResidueField R) K) := by
  -- Proof comment: rewrite the proof-dependent closed-prefix field to the terminal well-ordered
  -- prefix field, where the imported field-side theorem already identifies the result with `⊤`.
  dsimp [closedPrefixField]
  rw [wellOrder_prefixField_proof_irrel (R := R) (K := K)
    (h₁ := le_trans (show Ordinal.type (@WellOrderingRel K) ≤
      Ordinal.type (@WellOrderingRel K) by exact le_rfl) le_rfl)
    (h₂ := le_rfl)]
  simpa using wellOrder_prefixField_top (R := R) (K := K)

/-- Helper for Chap10 Lemma 10 159 1: once the recursive construction reaches a stage over a field
equal to `⊤`, the final theorem only needs a single transport of that stage and the base map. -/
theorem stage_transport_to_top
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (hL : L = (⊤ : IntermediateField (ResidueField R) K))
    {hbaseL : (⊥ : IntermediateField (ResidueField R) K) ≤ L}
    (T : ResidueExtensionStage.{u, v, max u v} (R := R) K L)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T)) :
    ∃ Ttop : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) Ttop) := by
  -- Proof comment: after substituting the target field, the ring and the base-stage morphism do
  -- not change; only the proof-irrelevant index needs rewriting.
  subst L
  refine ⟨T, ?_⟩
  simpa using hbase

/-- Helper for Chap10 Lemma 10 159 1: a stage over `⊥` can be transported to any
proof-irrelevantly equal field without changing the underlying ring or its base-stage morphism. -/
theorem stage_transport_from_bot
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (hL : L = (⊥ : IntermediateField (ResidueField R) K))
    {hbaseL : (⊥ : IntermediateField (ResidueField R) K) ≤ L}
    (T : ResidueExtensionStage.{u, v, max u v} (R := R) K
      (⊥ : IntermediateField (ResidueField R) K))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by rfl)
          (ResidueExtensionStage.base (R := R) K) T)) :
    ∃ T' : ResidueExtensionStage.{u, v, max u v} (R := R) K L,
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T') := by
  -- Proof comment: after rewriting the target field to `⊥`, only the proof-irrelevant inclusion
  -- witness on the base morphism changes.
  subst L
  exact ⟨T, by simpa using hbase⟩

/-- Helper for Chap10 Lemma 10 159 1: deterministic finite-word data for iterating the
one-element extension theorem. This packages the realized intermediate field, the corresponding
stage, and the inherited morphism from the base stage. -/
structure WordStageData
    (K : Type v) [Field K] [Algebra (ResidueField R) K] where
  L : IntermediateField (ResidueField R) K
  stage : ResidueExtensionStage.{u, v, max u v} (R := R) K L
  baseHom :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤ L by simp)
        (ResidueExtensionStage.base (R := R) K) stage)

/-- Helper for Chap10 Lemma 10 159 1: the empty word realizes the bottom field by the base stage
itself, using the already available universe-lifted zero-stage helper. -/
noncomputable def wordStageDataNilStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ResidueExtensionStage.{u, v, max u v} (R := R) K
      (⊥ : IntermediateField (ResidueField R) K) :=
  Classical.choose (exists_zero_prefix_stage (R := R) (K := K))

/-- Helper for Chap10 Lemma 10 159 1: the empty word inherits its base-stage morphism from the
universe-lifted zero-stage package. -/
theorem wordStageDataNil_baseHom
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            (⊥ : IntermediateField (ResidueField R) K) by simp)
        (ResidueExtensionStage.base (R := R) K)
        (wordStageDataNilStage (R := R) K)) := by
  -- Proof comment: the imported zero-stage theorem already provides exactly the needed base map.
  simpa [wordStageDataNilStage] using
    (Classical.choose_spec (exists_zero_prefix_stage (R := R) (K := K)))

/-- Helper for Chap10 Lemma 10 159 1: the empty word realizes the bottom field by the existing
zero-stage package. -/
noncomputable def wordStageDataNil
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    WordStageData (R := R) K :=
  { L := ⊥
    stage := wordStageDataNilStage (R := R) K
    baseHom := wordStageDataNil_baseHom (R := R) K }

/-- Helper for Chap10 Lemma 10 159 1: appending one generator to a finite word applies the
one-element extension theorem to the stage already realized by that word, while composing the
stored base-stage morphism forward. -/
noncomputable def extendWordStageStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (x : K) :
    ResidueExtensionStage.{u, v, max u v} (R := R) K
      ((IntermediateField.adjoin D.L ({x} : Set K)).restrictScalars (ResidueField R)) :=
  Classical.choose (ResidueExtensionStage.extend_stage_by_element (S := D.stage) x)

/-- Helper for Chap10 Lemma 10 159 1: the chosen one-step extension stage carries the canonical
morphism from the previous word stage. -/
theorem extendWordStageStage_hom
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (x : K) :
    Nonempty
      (ResidueExtensionStage.Hom
        (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) D.L x)
        D.stage
        (extendWordStageStage (R := R) (K := K) D x)) := by
  -- Proof comment: this is exactly the morphism bundled by the one-element extension theorem.
  simpa [extendWordStageStage] using
    (Classical.choose_spec (ResidueExtensionStage.extend_stage_by_element (S := D.stage) x))

/-- Helper for Chap10 Lemma 10 159 1: composing the stored base-stage morphism with the chosen
one-step extension map gives a base-stage morphism for the longer word. -/
theorem extendWordStage_baseHom
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (x : K) :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            (IntermediateField.adjoin D.L ({x} : Set K)).restrictScalars (ResidueField R) by
              simp)
        (ResidueExtensionStage.base (R := R) K)
        (extendWordStageStage (R := R) (K := K) D x)) := by
  -- Proof comment: the old base-stage map and the new one-element extension map compose along the
  -- finite word fold.
  rcases D.baseHom with ⟨f⟩
  rcases extendWordStageStage_hom (R := R) (K := K) D x with ⟨g⟩
  refine ⟨?_⟩
  simpa using ResidueExtensionStage.Hom.comp f g

/-- Helper for Chap10 Lemma 10 159 1: appending one generator to a finite word applies the
one-element extension theorem to the stage already realized by that word, while composing the
stored base-stage morphism forward. -/
noncomputable def extendWordStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (x : K) :
    WordStageData (R := R) K :=
  { L := (IntermediateField.adjoin D.L ({x} : Set K)).restrictScalars (ResidueField R)
    stage := extendWordStageStage (R := R) (K := K) D x
    baseHom := extendWordStage_baseHom (R := R) (K := K) D x }

/-- Helper for Chap10 Lemma 10 159 1: folding `extendWordStage` along a finite word gives a
deterministic iterated one-element extension owner for that word. -/
noncomputable def wordStageData
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) :
    WordStageData (R := R) K :=
  xs.foldl (fun D x ↦ extendWordStage (R := R) (K := K) D x) (wordStageDataNil (R := R) K)

/-- Helper for Chap10 Lemma 10 159 1: folding `extendWordStage` from an arbitrary starting stage
data packages the canonical append-tail growth of finite words. This is the deterministic owner
for the append-only part of the planned finite-support system. -/
noncomputable def wordStageDataFrom
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (xs : List K) :
    WordStageData (R := R) K :=
  xs.foldl (fun E x ↦ extendWordStage (R := R) (K := K) E x) D

/-- Helper for Chap10 Lemma 10 159 1: the original finite-word owner is the arbitrary-start fold
specialized to the empty-word data. -/
theorem wordStageData_eq_wordStageDataFrom
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) :
    wordStageData (R := R) (K := K) xs =
      wordStageDataFrom (R := R) (K := K) (wordStageDataNil (R := R) K) xs := by
  rfl

/-- Helper for Chap10 Lemma 10 159 1: the intermediate field realized by a finite word. -/
noncomputable def wordField
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) :
    IntermediateField (ResidueField R) K :=
  (wordStageData (R := R) (K := K) xs).L

/-- Helper for Chap10 Lemma 10 159 1: the residue-extension stage carried by a finite word. -/
noncomputable def wordStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) :
    ResidueExtensionStage.{u, v, max u v} (R := R) K (wordField (R := R) (K := K) xs) :=
  (wordStageData (R := R) (K := K) xs).stage

/-- Helper for Chap10 Lemma 10 159 1: every finite word carries a morphism from the base stage,
inherited from the fold that builds its stage. -/
theorem wordBaseHom
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            wordField (R := R) (K := K) xs by simp [wordField])
        (ResidueExtensionStage.base (R := R) K)
        (wordStage (R := R) (K := K) xs)) := by
  -- Proof comment: this is exactly the third component stored in `wordStageData`.
  simpa [wordField, wordStage] using
    (wordStageData (R := R) (K := K) xs).baseHom

/-- Helper for Chap10 Lemma 10 159 1: appending a singleton word performs one further
`extendWordStage` step after the data for the initial word. -/
theorem wordStageData_append_singleton
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) (x : K) :
    wordStageData (R := R) (K := K) (xs ++ [x]) =
      extendWordStage (R := R) (K := K) (wordStageData (R := R) (K := K) xs) x := by
  -- Proof comment: `List.foldl` over an appended singleton first folds over `xs` and then applies
  -- the final extension step for `x`.
  simpa [wordStageData, List.foldl_append]

/-- Helper for Chap10 Lemma 10 159 1: appending a singleton after an arbitrary starting stage
data performs one more `extendWordStage` step after the fold over the initial word. -/
theorem wordStageDataFrom_append_singleton
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (D : WordStageData (R := R) K) (xs : List K) (x : K) :
    wordStageDataFrom (R := R) (K := K) D (xs ++ [x]) =
      extendWordStage (R := R) (K := K)
        (wordStageDataFrom (R := R) (K := K) D xs) x := by
  -- Proof comment: `List.foldl` from any starting owner behaves the same way on appended
  -- singletons as the original empty-start fold.
  simpa [wordStageDataFrom, List.foldl_append]

/-- Helper for Chap10 Lemma 10 159 1: the field attached to an appended singleton word is exactly
the previous word field with one more element adjoined. -/
theorem wordField_append_singleton
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (xs : List K) (x : K) :
    wordField (R := R) (K := K) (xs ++ [x]) =
      (IntermediateField.adjoin (wordField (R := R) (K := K) xs) ({x} : Set K)).restrictScalars
        (ResidueField R) := by
  -- Proof comment: read the field component of the previous fold identity.
  rw [wordField, wordStageData_append_singleton]
  rfl

/-- Helper for Chap10 Lemma 10 159 1: the one-letter word already realizes a field containing its
generator. This is the first stagewise ingredient for any later direct-limit surjectivity proof. -/
theorem mem_wordField_singleton
    (K : Type v) [Field K] [Algebra (ResidueField R) K] (x : K) :
    x ∈ wordField (R := R) (K := K) [x] := by
  -- Proof comment: after unfolding the singleton fold once, the target field is just the adjoin
  -- of `x` over the bottom field.
  simpa using
    (show x ∈ wordField (R := R) (K := K) ([] ++ [x]) from by
      rw [wordField_append_singleton (R := R) (K := K) [] x]
      exact
        IntermediateField.mem_adjoin_of_mem
          (F := (⊥ : IntermediateField (ResidueField R) K))
          (S := ({x} : Set K))
          (by simpa using Set.mem_singleton x))

/-- Helper for Chap10 Lemma 10 159 1: if one finite support is contained in another, then the
sorted word for the smaller support is a subpermutation of the sorted word for the larger
support. This is the first finite-support bridge from set inclusion to list combinatorics. -/
theorem sortedWordSubpermOfSubset
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (s t : Finset K) (hst : s ⊆ t) :
    letI : LinearOrder K := WellOrderingRel.isWellOrder.linearOrder
    List.Subperm s.sort t.sort := by
  classical
  letI : LinearOrder K := WellOrderingRel.isWellOrder.linearOrder
  -- Proof comment: the sorted words are nodup, so subset containment of their elements upgrades
  -- directly to a `Subperm` statement.
  exact (Finset.sort_nodup (s := s) (r := fun a b : K ↦ a ≤ b)).subperm <| by
    intro a ha
    exact
      (Finset.mem_sort (s := t) (r := fun a b : K ↦ a ≤ b)).2 <|
        hst ((Finset.mem_sort (s := s) (r := fun a b : K ↦ a ≤ b)).1 ha)

/-- Helper for Chap10 Lemma 10 159 1: if one finite support is contained in another, then the
deterministic sorted word for the smaller support occurs as a sublist of the larger sorted word.
This isolates the finite-support-to-word comparison needed by the planned directed-system pivot. -/
theorem sortedWordSublistOfSubset
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (s t : Finset K) (hst : s ⊆ t) :
    letI : LinearOrder K := WellOrderingRel.isWellOrder.linearOrder
    List.Sublist s.sort t.sort := by
  classical
  letI : LinearOrder K := WellOrderingRel.isWellOrder.linearOrder
  have hsubperm :
      List.Subperm s.sort t.sort :=
    sortedWordSubpermOfSubset (R := R) (K := K) s t hst
  -- Proof comment: both sorted words are pairwise ordered by the ambient well-order relation, so
  -- the generic `subperm + pairwise` comparison theorem upgrades the set-theoretic inclusion to a
  -- literal ordered sublist.
  exact List.sublist_of_subperm_of_pairwise hsubperm
    (Finset.pairwise_sort (s := s) (r := fun a b : K ↦ a ≤ b))
    (Finset.pairwise_sort (s := t) (r := fun a b : K ↦ a ≤ b))

/-- Helper for Chap10 Lemma 10 159 1: the zero prefix chain has a single stage, namely the
already constructed zero stage, and the base-stage morphism lands in that unique stage. -/
theorem existsZeroPrefixStageChainWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (h0 : (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ C : PrefixStageChain (R := R) K 0 h0,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K h0
                ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩ by
                  simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩)) := by
  let βzero : Set.Iic (0 : Ordinal) :=
    ⟨0, show (0 : Ordinal) ≤ (0 : Ordinal) from le_rfl⟩
  rcases exists_zero_prefix_stage (R := R) (K := K) with ⟨Tzero₀, hbase₀⟩
  rcases stage_transport_from_bot (R := R) (K := K)
      (L := closedPrefixField (R := R) K h0 βzero)
      (hL := by
        simpa [βzero, closedPrefixField, wellOrder_prefixField_zero])
      (hbaseL := by
        simpa [βzero, closedPrefixField, wellOrder_prefixField_zero])
      Tzero₀ hbase₀ with ⟨Tzero, hbase⟩
  have hsubsingleton : ∀ β : Set.Iic (0 : Ordinal), β = βzero := by
    intro β
    apply Subtype.ext
    exact le_antisymm β.2 bot_le
  -- Proof comment: on the zero ordinal there is only one index, so every stage map is the
  -- identity on the already constructed zero stage.
  refine ⟨?_, ?_⟩
  · refine
      { stage := ?_
        hom := ?_
        hom_id := ?_
        hom_comp := ?_ }
    · intro β
      have hβ : β = βzero := hsubsingleton β
      subst β
      exact Tzero
    · intro β γ hβγ
      have hβ : β = βzero := hsubsingleton β
      have hγ : γ = βzero := hsubsingleton γ
      subst β
      subst γ
      simpa using ResidueExtensionStage.Hom.id (R := R) (K := K) Tzero
    · intro β
      have hβ : β = βzero := hsubsingleton β
      subst β
      rfl
    · intro β γ δ hβγ hγδ
      have hβ : β = βzero := hsubsingleton β
      have hγ : γ = βzero := hsubsingleton γ
      have hδ : δ = βzero := hsubsingleton δ
      subst β
      subst γ
      subst δ
      rfl
  · -- Proof comment: after normalizing the zero prefix field to `⊥`, the imported zero-stage map
    -- is exactly the required base morphism.
    exact hbase

/-- Helper for Chap10 Lemma 10 159 1: a coherent prefix-stage tower stores, for every
initial segment `β ≤ α`, a closed prefix chain up to `β` together with the base-stage map into
its zero stage and the literal restriction compatibilities between larger and smaller chains. This
is the value-level recursion owner needed to avoid comparing independently chosen lower chains in
the succ-limit step. -/
structure PrefixStageTower
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  chain :
    (β : Set.Iic α) →
      PrefixStageChain (R := R) K β.1 (le_trans β.2 hα)
  base :
    ∀ β : Set.Iic α,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_trans β.2 hα)
                ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩ by
                simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          ((chain β).stage ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩))
  stage_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) (δ : Set.Iic β.1),
      (chain γ).stage
          ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩ =
        (chain β).stage δ
  hom_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) {δ ε : Set.Iic β.1} (hδε : δ ≤ ε),
      HEq
        (((chain γ).hom
          (β := ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩)
          (γ := ⟨ε.1, show ε.1 ≤ γ.1 from
            le_trans ε.2 (show β.1 ≤ γ.1 from hβγ)⟩) hδε).toAlgHom)
        (((chain β).hom (β := δ) (γ := ε) hδε).toAlgHom)

/-- Helper for Chap10 Lemma 10 159 1: a single closed prefix chain already determines the whole
restriction tower of its initial segments. This packages the solved part of the source-proof route
into the value-level owner needed later for transfinite recursion. -/
theorem existsPrefixStageTowerOfPrefixStageChain
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α hα)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
                simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩))) :
    Nonempty (PrefixStageTower (R := R) K α hα) := by
  -- Proof comment: each tower component is just the literal restriction of the ambient chain `C`,
  -- so the restriction equalities are definitional after unpacking `PrefixStageChain.restrict`.
  refine ⟨{
      chain := ?_
      base := ?_
      stage_restrict := ?_
      hom_restrict := ?_ }⟩
  · intro β
    exact C.restrict β.2
  · intro β
    -- Proof comment: the zero-stage base map of a restriction is the original base map with only
    -- proof-irrelevant ordinal witnesses changed.
    simpa using hbase
  · intro β γ hβγ δ
    -- Proof comment: restricting first to `γ` and then reading the `δ` stage is exactly the same
    -- as restricting directly to `β` and reading `δ`.
    dsimp [PrefixStageChain.restrict, PrefixStageChain.restrictStage]
  · intro β γ hβγ δ ε hδε
    -- Proof comment: the transition morphism seen inside the larger restricted chain is the same
    -- ambient morphism as the one stored in the smaller restriction.
    exact HEq.rfl

/-- Helper for Chap10 Lemma 10 159 1: the zero closed-prefix chain immediately yields the zero
prefix-stage tower, which is the base case for the source-faithful transfinite recursion. -/
theorem existsZeroPrefixStageTowerWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (h0 : (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K)) :
    Nonempty (PrefixStageTower (R := R) K 0 h0) := by
  rcases existsZeroPrefixStageChainWithBase (R := R) K h0 with ⟨C, hbase⟩
  -- Proof comment: the zero tower is just the restriction tower of the already constructed zero
  -- chain.
  exact existsPrefixStageTowerOfPrefixStageChain (R := R) (K := K) h0 C hbase

/-- Helper for Chap10 Lemma 10 159 1: the top chain stored in a coherent prefix-stage tower
induces the open-stage system below a succ-limit ordinal by reading off its top closed chain. This
stabilizes the direct-limit input without rebuilding lower-stage coherence ad hoc. -/
theorem PrefixStageTower.existsOpenPrefixStageSystem
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (hlimit : Order.IsSuccLimit α)
    (T : PrefixStageTower (R := R) K α hα) :
    Nonempty (OpenPrefixStageSystem (R := R) K hα hlimit) := by
  let top : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  refine ⟨{
      stage := ?_
      hom := ?_
      hom_id := ?_
      hom_comp := ?_
      base := ?_ }⟩
  · intro β
    -- Proof comment: the open stage at `β < α` is the corresponding stage inside the top closed
    -- chain of the tower.
    simpa [top, openPrefixField, closedPrefixField] using
      (T.chain top).stage ⟨β.1, show β.1 ≤ α from β.2.le⟩
  · intro β γ hβγ
    -- Proof comment: open-stage transition maps are exactly the transition maps of the top closed
    -- chain restricted to indices below `α`.
    simpa [top, openPrefixField, closedPrefixField] using
      (T.chain top).hom
        (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
        (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩) hβγ
  · intro β
    -- Proof comment: the identity law is inherited verbatim from the top closed chain.
    simpa [top, openPrefixField, closedPrefixField] using
      (T.chain top).hom_id ⟨β.1, show β.1 ≤ α from β.2.le⟩
  · intro β γ δ hβγ hγδ
    -- Proof comment: the composition law is likewise the stored composition law of the top chain.
    simpa [top, openPrefixField, closedPrefixField] using
      (T.chain top).hom_comp
        (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
        (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩)
        (δ := ⟨δ.1, show δ.1 ≤ α from δ.2.le⟩) hβγ hγδ
  · -- Proof comment: the base-stage map of the open system is the zero-stage base map stored in
    -- the top chain of the tower.
    simpa [top, openPrefixField, closedPrefixField, wellOrder_prefixField_zero] using T.base top

/-- Helper for Chap10 Lemma 10 159 1: composing inclusions of intermediate fields agrees with the
direct inclusion along the transitive containment. This is the field-side normalization needed
before comparing limit-stage quotient maps. -/
theorem intermediateField_inclusion_comp_toRingHom
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {L M N : IntermediateField (ResidueField R) K}
    (hLM : L ≤ M) (hMN : M ≤ N) :
    ((IntermediateField.inclusion hMN).toRingHom.comp
        (IntermediateField.inclusion hLM).toRingHom) =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom := by
  -- Proof comment: both sides are just the ambient inclusion into `N`, so they agree pointwise.
  apply RingHom.ext
  intro x
  rfl

/-- Helper for Chap10 Lemma 10 159 1: evaluating the compatibility square of a stage morphism at
an element shows that both quotient maps have the same image in the ambient field `K`. -/
theorem ResidueExtensionStage.Hom.toIntermediateFieldHom_commVal
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K} {hLM : L ≤ M}
    {S : ResidueExtensionStage.{u, v, max u v} (R := R) K L}
    {T : ResidueExtensionStage.{u, v, max u v} (R := R) K M}
    (f : ResidueExtensionStage.Hom hLM S T) (x : S.A) :
    (((T.toIntermediateFieldHom (f.toAlgHom x) : M) : K) =
      ((S.toIntermediateFieldHom x : L) : K)) := by
  -- Proof comment: specialize the stored ring-hom commutativity relation and then forget the
  -- intermediate-field subtypes to the common ambient field.
  have h :=
    congrArg (fun φ : S.A →+* M ↦ φ x) f.toIntermediateFieldHom_comm
  simpa [RingHom.comp_apply] using congrArg Subtype.val h

/-- Helper for Chap10 Lemma 10 159 1: a stage morphism remains compatible with quotient maps after
both sides are composed with an inclusion into a larger intermediate field. -/
theorem ResidueExtensionStage.Hom.toIntermediateFieldHom_commCompInclusion
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {L M N : IntermediateField (ResidueField R) K}
    {hLM : L ≤ M} (hMN : M ≤ N)
    {S : ResidueExtensionStage.{u, v, max u v} (R := R) K L}
    {T : ResidueExtensionStage.{u, v, max u v} (R := R) K M}
    (f : ResidueExtensionStage.Hom hLM S T) :
    ((IntermediateField.inclusion hMN).toRingHom.comp T.toIntermediateFieldHom).comp
        f.toAlgHom.toRingHom =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom.comp
        S.toIntermediateFieldHom := by
  -- Proof comment: first rewrite by the intrinsic stage-morphism square, then collapse the two
  -- successive intermediate-field inclusions to the direct inclusion.
  calc
    ((IntermediateField.inclusion hMN).toRingHom.comp T.toIntermediateFieldHom).comp
        f.toAlgHom.toRingHom
        =
      (IntermediateField.inclusion hMN).toRingHom.comp
        (T.toIntermediateFieldHom.comp f.toAlgHom.toRingHom) := by
          rfl
    _ =
      (IntermediateField.inclusion hMN).toRingHom.comp
        ((IntermediateField.inclusion hLM).toRingHom.comp S.toIntermediateFieldHom) := by
          rw [f.toIntermediateFieldHom_comm]
    _ =
      ((IntermediateField.inclusion hMN).toRingHom.comp
        (IntermediateField.inclusion hLM).toRingHom).comp S.toIntermediateFieldHom := by
          rfl
    _ =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom.comp
        S.toIntermediateFieldHom := by
          rw [intermediateField_inclusion_comp_toRingHom (R := R) (K := K) hLM hMN]

/-- Helper for Chap10 Lemma 10 159 1: the open-stage morphisms of a coherent open system already
form the directed system on the underlying stage rings required by `Ring.DirectLimit`. -/
theorem OpenPrefixStageSystem.directedSystem
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    {hlimit : Order.IsSuccLimit α}
    (S : OpenPrefixStageSystem (R := R) K hα hlimit) :
    DirectedSystem
      (fun β : Set.Iio α ↦ (S.stage β).A)
      (fun β γ hβγ ↦ (S.hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom) := by
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro β x
    -- Proof comment: the stored self-map is the identity ring endomorphism of the stage.
    change (S.hom (β := β) (γ := β) le_rfl).toAlgHom x = x
    simpa using congrArg (fun f : (S.stage β).A →ₐ[R] (S.stage β).A ↦ f x) (S.hom_id β)
  · intro δ γ β hβγ hγδ x
    -- Proof comment: the directed-system composition law is the ring-hom shadow of the stored
    -- algebra-hom composition law in the open system.
    change (S.hom (β := γ) (γ := δ) hγδ).toAlgHom
        ((S.hom (β := β) (γ := γ) hβγ).toAlgHom x) =
      (S.hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom x
    exact congrArg (fun f : (S.stage β).A →ₐ[R] (S.stage δ).A ↦ f x) (S.hom_comp hβγ hγδ)

/-- Helper for Chap10 Lemma 10 159 1: after composing each open-stage quotient map with the
canonical inclusion into the closed limit field, the resulting maps are compatible with the
open-stage transition morphisms. This is the field-side descent datum for the limit-stage map. -/
theorem OpenPrefixStageSystem.limitStageToIntermediateFieldHomComm
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    {hlimit : Order.IsSuccLimit α}
    (S : OpenPrefixStageSystem (R := R) K hα hlimit)
    {β γ : Set.Iio α} (hβγ : β ≤ γ) :
    (((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans γ.2.le hα) hα γ.2.le)).toRingHom).comp
        (S.stage γ).toIntermediateFieldHom).comp
          (S.hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom
      =
    ((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) hα β.2.le)).toRingHom).comp
        (S.stage β).toIntermediateFieldHom := by
  -- Proof comment: this is exactly the generic "compose with a larger inclusion" compatibility
  -- specialized to the open-system transition morphism.
  simpa using
    ResidueExtensionStage.Hom.toIntermediateFieldHom_commCompInclusion (R := R) (K := K)
      (hMN := wellOrder_prefixField_mono (R := R) (K := K)
        (le_trans γ.2.le hα) hα γ.2.le)
      (S.hom (β := β) (γ := γ) hβγ)

/-- Helper for Chap10 Lemma 10 159 1: a closed-prefix index at a limit stage is either the top
index itself or a genuinely smaller open index. -/
theorem limitIndex_eq_top_or_lt
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic α) :
    β.1 = α ∨ β.1 < α := by
  -- Proof comment: split on equality with the endpoint; otherwise the closed bound upgrades to a
  -- strict inequality.
  by_cases hβ : β.1 = α
  · exact Or.inl hβ
  · exact Or.inr (lt_of_le_of_ne β.2 hβ)

/-- Helper for Chap10 Lemma 10 159 1: at a limit stage, a closed-prefix field indexed strictly
below the endpoint is just the corresponding open-prefix field. -/
theorem closedPrefixField_limit_lt_eq_openPrefixField
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic α) (hβ : β.1 < α) :
    closedPrefixField (R := R) K hα β =
      openPrefixField (R := R) K hα ⟨β.1, hβ⟩ := by
  -- Proof comment: both sides are the same well-ordered prefix field; only the ambient-bound
  -- proof differs.
  simpa [closedPrefixField, openPrefixField] using
    (wellOrder_prefixField_proof_irrel (R := R) (K := K)
      (α := β.1)
      (h₁ := le_trans β.2 hα)
      (h₂ := le_trans hβ.le hα))

/-- Helper for Chap10 Lemma 10 159 1: a base-stage morphism into the zero stage of a coherent
prefix chain composes with the chain map to the top stage. This isolates the final extraction step
from the still-missing transfinite recursion owner. -/
theorem PrefixStageChain.topBaseHom
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
                  simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩))) :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            closedPrefixField (R := R) K hα
              ⟨α, show α ≤ α from le_rfl⟩ by
                simpa [closedPrefixField] using
                  (base_le_prefixField (R := R) (K := K) (hα := hα)))
        (ResidueExtensionStage.base (R := R) K)
        C.topStage) := by
  let βzero : Set.Iic α := ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩
  let βtop : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  rcases hbase with ⟨f₀⟩
  -- Proof comment: move from the base stage to the zero stage first, then follow the coherent
  -- chain map from the zero index to the top index.
  refine ⟨?_⟩
  simpa [βzero, βtop, PrefixStageChain.topStage, closedPrefixField, wellOrder_prefixField_zero] using
    (ResidueExtensionStage.Hom.comp f₀ (C.hom (β := βzero) (γ := βtop) bot_le))

/-- Helper for Chap10 Lemma 10 159 1: once the source-proof recursion has produced a coherent
terminal closed prefix chain, the target theorem is only the extraction of its top stage. -/
theorem existsTerminalClosedPrefixStageWithBase_ofPrefixStageChain
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (hC :
      ∃ C : PrefixStageChain (R := R) K (Ordinal.type (@WellOrderingRel K)) le_rfl,
        Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤
                closedPrefixField (R := R) K le_rfl
                  ⟨0, show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) from bot_le⟩ by
                    simpa [closedPrefixField, wellOrder_prefixField_zero])
            (ResidueExtensionStage.base (R := R) K)
            (C.stage
              ⟨0, show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) from bot_le⟩))) :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl
                (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
                  Set.Iic (Ordinal.type (@WellOrderingRel K))) by
                  simpa [closedPrefixField] using
                    (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K) T) := by
  rcases hC with ⟨C, hbase⟩
  -- Proof comment: the required stage is the top stage of the coherent chain, and the base map is
  -- the extracted top-stage morphism proved just above.
  exact ⟨C.topStage, C.topBaseHom hbase⟩

/-- Helper for Chap10 Lemma 10 159 1: a chain-history owner stores the coherent closed prefix
chain together with the base-stage map into its zero stage. This is the compile-stable payload
currently consumed by the terminal extraction theorems. -/
structure PrefixStageChainHistory
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  chain :
    PrefixStageChain (R := R) K α hα
  base :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            closedPrefixField (R := R) K hα
              ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
                simpa [closedPrefixField, wellOrder_prefixField_zero])
        (ResidueExtensionStage.base (R := R) K)
        (chain.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩))

/-- Helper for Chap10 Lemma 10 159 1: any coherent prefix chain with its base-stage morphism
packages into a chain-history owner immediately. This separates the already-solved terminal-chain
bookkeeping from the still-missing recursive owner needed for the source-faithful succ-limit
construction. -/
theorem existsPrefixStageChainHistoryOfChain
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α hα)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
                  simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩))) :
    ∃ H : PrefixStageChainHistory (R := R) K α hα, H.chain = C := by
  -- Proof comment: the compile-stable history owner is exactly the pair of the chain and its
  -- base-stage morphism.
  exact ⟨{ chain := C, base := hbase }, rfl⟩

/-- Helper for Chap10 Lemma 10 159 1: the zero prefix-chain package already gives the zero
history owner, because the compile-stable history payload is only the zero chain plus its base map.
This fixes the base case of the reduced owner used by the extraction lemmas. -/
theorem existsZeroPrefixStageChainHistoryWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (h0 : (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K)) :
    Nonempty (PrefixStageChainHistory (R := R) K 0 h0) := by
  rcases existsZeroPrefixStageChainWithBase (R := R) K h0 with ⟨C, hbase⟩
  -- Proof comment: the zero history is just the zero chain equipped with its existing base map.
  exact ⟨{ chain := C, base := hbase }⟩

/-- Helper for Chap10 Lemma 10 159 1: once the transfinite recursion produces a terminal
chain-history owner, the target theorem is just the extraction of its stored terminal chain. -/
theorem existsTerminalClosedPrefixStageWithBase_ofPrefixStageChainHistory
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (hH :
      Nonempty
        (PrefixStageChainHistory (R := R) K
          (Ordinal.type (@WellOrderingRel K)) le_rfl)) :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl
                (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
                  Set.Iic (Ordinal.type (@WellOrderingRel K))) by
                  simpa [closedPrefixField] using
                    (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K) T) := by
  rcases hH with ⟨H⟩
  -- Proof comment: forget the recursive lower-history payload and reuse the existing extraction
  -- theorem from the stored terminal coherent chain.
  exact
    existsTerminalClosedPrefixStageWithBase_ofPrefixStageChain (R := R) (K := K)
      ⟨H.chain, H.base⟩

/-- Helper for Chap10 Lemma 10 159 1: the source-proof well-order recursion should construct a
coherent chain-history owner up to any ordinal stage. Isolating this existence theorem keeps the
public terminal-chain statements as pure extraction lemmas while the remaining succ-limit
direct-limit package is finished separately. -/
theorem existsPrefixStageChainHistoryByWellOrderRecursion
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    Nonempty (PrefixStageChainHistory (R := R) K α hα) := by
  -- Route correction: the public chain theorem should not carry the recursion hole. The missing
  -- work is exactly the owner-level well-order recursion on `PrefixStageChainHistory`.
  -- TODO: prove this by ordinal recursion, using `existsZeroPrefixStageChainHistoryWithBase` at
  -- zero, `exists_adjoin_singleton_stage_of_prefix_stage` for successors, and the still-missing
  -- direct-limit constructor `existsLimitTopStageOfOpenPrefixStageSystem` at succ-limits.
  sorry

/-- Helper for Chap10 Lemma 10 159 1: once the owner-level recursion produces a terminal coherent
prefix chain together with its base-stage map, the history owner follows formally by packaging the
literal restrictions of that chain. -/
theorem existsTerminalPrefixStageChainWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ C : PrefixStageChain (R := R) K (Ordinal.type (@WellOrderingRel K)) le_rfl,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl
                ⟨0, show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) from bot_le⟩ by
                  simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage
            ⟨0, show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) from bot_le⟩)) := by
  rcases
      existsPrefixStageChainHistoryByWellOrderRecursion (R := R) (K := K)
        (Ordinal.type (@WellOrderingRel K)) le_rfl with
    ⟨H⟩
  -- Proof comment: after isolating the recursive owner, the terminal chain theorem just forgets
  -- the lower-history payload and keeps the stored terminal chain with its base map.
  exact ⟨H.chain, H.base⟩

/-- Helper for Chap10 Lemma 10 159 1: the remaining owner-level gap is now isolated as the
source-faithful transfinite recursion producing a terminal chain-history owner. The public theorem
only needs this existence statement and no longer mentions the obsolete tower route. -/
theorem existsTerminalPrefixStageChainHistoryWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    Nonempty
      (PrefixStageChainHistory (R := R) K
        (Ordinal.type (@WellOrderingRel K)) le_rfl) := by
  -- Proof comment: the recursive owner theorem already returns the terminal history object, so no
  -- further packaging is needed here.
  exact
    existsPrefixStageChainHistoryByWellOrderRecursion (R := R) (K := K)
      (Ordinal.type (@WellOrderingRel K)) le_rfl

/-- Helper for Chap10 Lemma 10 159 1: once the transfinite recursion has produced a terminal
prefix-stage tower, the target theorem is just the extraction of the top closed chain from that
tower. -/
theorem existsTerminalClosedPrefixStageWithBase_ofPrefixStageTower
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (hT :
      Nonempty
        (PrefixStageTower (R := R) K (Ordinal.type (@WellOrderingRel K)) le_rfl)) :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl
                (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
                  Set.Iic (Ordinal.type (@WellOrderingRel K))) by
                  simpa [closedPrefixField] using
                    (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K) T) := by
  let βtop : Set.Iic (Ordinal.type (@WellOrderingRel K)) :=
    ⟨Ordinal.type (@WellOrderingRel K), by simp⟩
  rcases hT with ⟨T⟩
  -- Proof comment: apply the existing top-stage extraction theorem to the top closed chain stored
  -- in the tower.
  exact
    existsTerminalClosedPrefixStageWithBase_ofPrefixStageChain (R := R) (K := K)
      ⟨T.chain βtop, T.base βtop⟩

/-- Helper for Chap10 Lemma 10 159 1: the remaining owner-level gap is the construction of the
terminal closed-prefix stage together with its base-stage morphism, before the final transport to
`⊤`. -/
theorem existsTerminalClosedPrefixStageWithBase
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl
                (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
                  Set.Iic (Ordinal.type (@WellOrderingRel K))) by
                  simpa [closedPrefixField] using
                    (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K) T) := by
  -- Route correction: the tower-based owner was still one layer too indirect. The public theorem
  -- now reduces immediately to the terminal chain-history owner, and the unresolved recursion is
  -- isolated in that dedicated helper theorem.
  exact
    existsTerminalClosedPrefixStageWithBase_ofPrefixStageChainHistory (R := R) (K := K)
      (existsTerminalPrefixStageChainHistoryWithBase (R := R) K)

/-- Helper for Chap10 Lemma 10 159 1: the source-proof transfinite recursion should produce a top
residue-extension stage over `⊤` together with a morphism from the base stage. -/
theorem existsTopStageViaWellOrderRecursion
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) T) := by
  let βtop : Set.Iic (Ordinal.type (@WellOrderingRel K)) :=
    ⟨Ordinal.type (@WellOrderingRel K), by simp⟩
  -- Route correction: isolate the unresolved recursion owner as a terminal closed-prefix stage,
  -- then use a single field transport to convert that terminal stage into a stage over `⊤`.
  rcases existsTerminalClosedPrefixStageWithBase (R := R) K with ⟨T, hT⟩
  exact
    stage_transport_to_top (R := R) (K := K)
      (L := closedPrefixField (R := R) K le_rfl βtop)
      (hL := closedPrefixField_top_eq_top (R := R) (K := K))
      (T := T) hT

/-- Chap10 Lemma 10 159 1: for any field extension `K / ResidueField R`, there exists a
commutative local `R`-algebra `R'` such that `R → R'` is flat and local, the maximal ideal of
`R` extends to the maximal ideal of `R'`, and the residue field of `R'` is isomorphic to `K` over
`ResidueField R`. -/
@[stacks 03C3]
theorem exists_flat_localAlgebra_with_residueField_equiv
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : ResidueField R' ≃ₐ[ResidueField R] K),
        Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R' := by
  -- Proof comment: the public theorem reduces to the structural existence of a top stage over
  -- the full field `K`; all ring-theoretic data are already stored in that stage.
  exact
    existsFlatLocalAlgebraWithResidueFieldEquivOfTopStage (R := R) K
      (existsTopStageViaWellOrderRecursion (R := R) K)

end
