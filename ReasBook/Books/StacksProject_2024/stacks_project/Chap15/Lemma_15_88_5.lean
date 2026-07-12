import StacksProject_2024.Chap15.Lemma_15_88_5_Bridge

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 15.88.5:
- primary domain: derived module objects on the chaotic ringed site attached to a sequential
  inverse system of commutative rings;
- sampled owner declarations:
  `sequentialRingSystem`,
  `SeqRingMod`,
  `DerivedModuleTower`,
  `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.Realization`;
- best owner abstraction: the chapter owner `DerivedCategory (SeqRingMod A ρ)` together with the
  bridge/view owner `DerivedModuleTower A ρ` from `Lemma_15_88_5_Bridge.lean`;
- primitive data: the inverse-system functor `sequentialRingSystem A ρ` and the compatible tower
  `DerivedModuleTower A ρ`;
- derived API: only the realization-existence statement below, phrased directly in terms of the
  bridge owner declarations already defined upstream.

Source/core/bridge triage:
- `source-facing`: the existence of an object of
  `D(Mod(ℕ, (A_n))) = D(SeqRingMod A ρ)`
  realizing prescribed stagewise derived data;
- `core/canonical`: `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: `DerivedModuleTower`, `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.ofDerivedObject`, and
  `DerivedModuleTower.Realization`.

This file is source-facing only: the tower bridge/view API now lives in
`Lemma_15_88_5_Bridge.lean`, and the theorem below reuses that owner-level bridge directly. -/

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [CategoryWithHomology (SeqRingMod A ρ)]

namespace DerivedModuleTower

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

local notation "CpxSeq" => CochainComplex (SeqRingMod A ρ) ℤ
local notation "dStep" n => sequentialRingedModuleTransitionFunctor A ρ n
-- Proof sketch: represent the desired object of
-- `D(naturalNumbersRingedModules (sequentialRingSystem A ρ))` by a complex of module sheaves on
-- the chaotic site of `ℕ`, choose right-fraction representatives of the transition morphisms
-- `φ_n`, and inductively modify the representing complex so that its stagewise evaluations realize
-- the given `K_n` with the prescribed compatibility.
/-- Helper for Lemma 15.88.5: it is enough to construct the realizing object already at the
cochain-complex level, because applying `DerivedCategory.Q.obj` turns such a representative into
the required derived object. -/
private theorem exists_realization_of_complex_realization
    (T : DerivedModuleTower A ρ)
    (hT : ∃ (M : CpxSeq), Nonempty (T.Realization (DerivedCategory.Q.obj M))) :
    ∃ (M : DModSeq), Nonempty (T.Realization M) := by
  -- The source proof constructs a strict complex representative first, so the final existential
  -- statement is obtained by forgetting that chosen representative after applying `Q`.
  rcases hT with ⟨M, hM⟩
  exact ⟨DerivedCategory.Q.obj M, hM⟩

/-- Helper for Lemma 15.88.5: a finite strict prefix records chosen complex representatives for
the first `length + 1` stages of the tower, together with strict successor maps and the exact
compatibility equation obtained after transporting the tower map through
`mapDerivedCategoryFactors`. -/
private structure StrictRealizationPrefix
    (T : DerivedModuleTower A ρ) (length : ℕ) where
  /-- The chosen strict complex representing stage `m`. -/
  complex :
    (m : Fin (length + 1)) → CochainComplex (ModuleCat (A m.1)) ℤ
  /-- The chosen identification between the strict stage complex and the target stage object. -/
  stageIso :
    (m : Fin (length + 1)) → DerivedCategory.Q.obj (complex m) ≅ T.obj m.1
  /-- The strict successor map between consecutive chosen complexes. -/
  step :
    (m : Fin length) →
      complex (Fin.succ m) ⟶
        ((ModuleCat.restrictScalars (ρ m.1)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (complex (Fin.castSucc m))
  /-- The strict successor map realizes the tower transition after transporting through the
  canonical derived comparison isomorphism. -/
  compat :
    (m : Fin length) →
      DerivedCategory.Q.map (step m) ≫
          ((ModuleCat.restrictScalars (ρ m.1)).mapDerivedCategoryFactors.app
            (complex (Fin.castSucc m))).hom ≫
          (dStep m.1).map (stageIso (Fin.castSucc m)).hom =
        (stageIso (Fin.succ m)).hom ≫ T.stepMap m.1

/-- Helper for Lemma 15.88.5: the recursive construction starts at stage `0` with the chosen
canonical preimage complex of `T.obj 0`. -/
private noncomputable abbrev StrictRealizationPrefix.base
    (T : DerivedModuleTower A ρ) :
    StrictRealizationPrefix (A := A) (ρ := ρ) T 0 :=
  { complex := fun
      | ⟨0, _⟩ => DerivedCategory.Q.objPreimage (T.obj 0)
    stageIso := fun
      | ⟨0, _⟩ => DerivedCategory.Q.objObjPreimageIso (T.obj 0)
    step := fun m ↦ nomatch m
    compat := fun m ↦ nomatch m }

/-- Helper for Lemma 15.88.5: the terminal strict complex in a finite prefix. -/
private noncomputable abbrev StrictRealizationPrefix.last_complex
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    CochainComplex (ModuleCat (A length)) ℤ :=
  S.complex (Fin.last length)

/-- Helper for Lemma 15.88.5: the terminal stage identification in a finite prefix. -/
private noncomputable abbrev StrictRealizationPrefix.last_stageIso
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    DerivedCategory.Q.obj S.last_complex ≅ T.obj length :=
  S.stageIso (Fin.last length)

/-- Helper for Lemma 15.88.5: transport the next tower map so that `DerivedCategory.right_fac`
can replace it by a strict map into the restricted previous-stage complex. -/
private noncomputable abbrev StrictRealizationPrefix.extension_transport
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage (T.obj (length + 1))) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (ρ length)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj S.last_complex) :=
  (DerivedCategory.Q.objObjPreimageIso (T.obj (length + 1))).hom ≫
    T.stepMap length ≫
    (dStep length).map S.last_stageIso.inv.hom ≫
    ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app S.last_complex).inv

/-- Helper for Lemma 15.88.5: applying `DerivedCategory.right_fac` to the transported successor
map produces a new strict source complex together with a strict successor map into the restricted
previous stage. -/
private noncomputable abbrev StrictRealizationPrefix.extension_data
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :=
  DerivedCategory.right_fac S.extension_transport

/-- Helper for Lemma 15.88.5: the new strict source complex produced by the recursive step. -/
private noncomputable abbrev StrictRealizationPrefix.extension_complex
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    CochainComplex (ModuleCat (A (length + 1))) ℤ :=
  Classical.choose S.extension_data

/-- Helper for Lemma 15.88.5: the denominator quasi-isomorphism chosen by
`DerivedCategory.right_fac` in the recursive extension step. -/
private noncomputable abbrev StrictRealizationPrefix.extension_denominator
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    S.extension_complex ⟶ DerivedCategory.Q.objPreimage (T.obj (length + 1)) :=
  Classical.choose (Classical.choose_spec S.extension_data)

/-- Helper for Lemma 15.88.5: the strict successor map produced by the recursive extension step.
-/
private noncomputable abbrev StrictRealizationPrefix.extension_step
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    S.extension_complex ⟶
      ((ModuleCat.restrictScalars (ρ length)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj S.last_complex :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec S.extension_data)).2

/-- Helper for Lemma 15.88.5: the chosen denominator becomes an isomorphism after applying `Q`.
-/
private theorem StrictRealizationPrefix.extension_denominator_isIso
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    IsIso (DerivedCategory.Q.map S.extension_denominator) := by
  exact (Classical.choose_spec (Classical.choose_spec S.extension_data)).1

/-- Helper for Lemma 15.88.5: the transported successor map is equal to the roof furnished by
`DerivedCategory.right_fac`. -/
private theorem StrictRealizationPrefix.extension_roof
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    S.extension_transport =
      inv (DerivedCategory.Q.map S.extension_denominator) ≫
        DerivedCategory.Q.map S.extension_step := by
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec S.extension_data)).2

/-- Helper for Lemma 15.88.5: the new stage is identified with `T.obj (length + 1)` by the
chosen denominator followed by the canonical `Q.objPreimage` comparison. -/
private theorem StrictRealizationPrefix.extension_stageIso
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    DerivedCategory.Q.obj S.extension_complex ≅ T.obj (length + 1) := by
  -- The recursive step replaces the target by a quasi-isomorphic source denominator and then
  -- restores the original target through the canonical `Q.objPreimage` isomorphism.
  letI : IsIso (DerivedCategory.Q.map S.extension_denominator) :=
    S.extension_denominator_isIso
  exact asIso (DerivedCategory.Q.map S.extension_denominator) ≪≫
    DerivedCategory.Q.objObjPreimageIso (T.obj (length + 1))

/-- Helper for Lemma 15.88.5: the strict map produced by the recursive step realizes the next
tower transition after transporting through the canonical derived comparison. -/
private theorem StrictRealizationPrefix.extension_step_compat
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    DerivedCategory.Q.map S.extension_step ≫
        ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app
          S.last_complex).hom ≫
        (dStep length).map S.last_stageIso.hom =
      (S.extension_stageIso).hom ≫ T.stepMap length := by
  -- Cancel the denominator introduced by `right_fac`, then unwind the transport used to define
  -- the recursive target morphism.
  letI : IsIso (DerivedCategory.Q.map S.extension_denominator) :=
    S.extension_denominator_isIso
  have hroof' :
      DerivedCategory.Q.map S.extension_denominator ≫ S.extension_transport =
        DerivedCategory.Q.map S.extension_step := by
    calc
      DerivedCategory.Q.map S.extension_denominator ≫ S.extension_transport =
          DerivedCategory.Q.map S.extension_denominator ≫
            (inv (DerivedCategory.Q.map S.extension_denominator) ≫
              DerivedCategory.Q.map S.extension_step) := by
              rw [S.extension_roof]
      _ = DerivedCategory.Q.map S.extension_step := by
            simp [Category.assoc]
  calc
    DerivedCategory.Q.map S.extension_step ≫
        ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app
          S.last_complex).hom ≫
        (dStep length).map S.last_stageIso.hom =
      DerivedCategory.Q.map S.extension_denominator ≫
        S.extension_transport ≫
        ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app
          S.last_complex).hom ≫
        (dStep length).map S.last_stageIso.hom := by
          rw [hroof']
    _ =
      DerivedCategory.Q.map S.extension_denominator ≫
        (DerivedCategory.Q.objObjPreimageIso (T.obj (length + 1))).hom ≫
        T.stepMap length ≫
        (dStep length).map S.last_stageIso.inv.hom ≫
        ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app
          S.last_complex).inv ≫
        ((ModuleCat.restrictScalars (ρ length)).mapDerivedCategoryFactors.app
          S.last_complex).hom ≫
        (dStep length).map S.last_stageIso.hom := by
          simp [StrictRealizationPrefix.extension_transport, Category.assoc]
    _ =
      DerivedCategory.Q.map S.extension_denominator ≫
        (DerivedCategory.Q.objObjPreimageIso (T.obj (length + 1))).hom ≫
        T.stepMap length ≫
        (dStep length).map S.last_stageIso.inv.hom ≫
        (dStep length).map S.last_stageIso.hom := by
          simp [Category.assoc]
    _ =
      DerivedCategory.Q.map S.extension_denominator ≫
        (DerivedCategory.Q.objObjPreimageIso (T.obj (length + 1))).hom ≫
        T.stepMap length := by
          simp [Category.assoc]
    _ = (S.extension_stageIso).hom ≫ T.stepMap length := by
          simp [StrictRealizationPrefix.extension_stageIso, Category.assoc]

/-- Helper for Lemma 15.88.5: when a strict prefix is extended, the old successor maps stay in
place and the new last successor map is the strict map produced by `right_fac`. -/
private theorem StrictRealizationPrefix.extend_step_at
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) (m : Fin (length + 1)) :
    (Fin.lastCases S.extension_complex S.complex (Fin.succ m)) ⟶
      ((ModuleCat.restrictScalars (ρ m.1)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (Fin.lastCases S.extension_complex S.complex (Fin.castSucc m)) := by
  cases m using Fin.lastCases with
  | last =>
      -- The new terminal transition is exactly the strict map returned by the roof construction.
      simpa using S.extension_step
  | cast j =>
      -- Earlier transitions are inherited verbatim from the shorter prefix.
      simpa [Fin.succ_castSucc] using S.step j

/-- Helper for Lemma 15.88.5: the transported compatibility equations are preserved on the old
indices and the new terminal equation is exactly the roof identity proved above. -/
private theorem StrictRealizationPrefix.extend_compat_at
    {T : DerivedModuleTower A ρ} {length : ℕ}
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) (m : Fin (length + 1)) :
    DerivedCategory.Q.map (S.extend_step_at m) ≫
        ((ModuleCat.restrictScalars (ρ m.1)).mapDerivedCategoryFactors.app
          (Fin.lastCases S.extension_complex S.complex (Fin.castSucc m))).hom ≫
        (dStep m.1).map
          (Fin.lastCases (S.extension_stageIso) S.stageIso (Fin.castSucc m)).hom =
      (Fin.lastCases (S.extension_stageIso) S.stageIso (Fin.succ m)).hom ≫ T.stepMap m.1 := by
  cases m using Fin.lastCases with
  | last =>
      -- At the new terminal index this is exactly the compatibility of the strict roof.
      simpa [StrictRealizationPrefix.extend_step_at] using S.extension_step_compat
  | cast j =>
      -- Earlier components are unchanged from the shorter prefix.
      simpa [Fin.succ_castSucc, StrictRealizationPrefix.extend_step_at] using S.compat j

/-- Helper for Lemma 15.88.5: extend a finite strict prefix by one more stage using the
source-faithful roof construction supplied by `DerivedCategory.right_fac`. -/
private theorem strictRealizationPrefix_succ
    (T : DerivedModuleTower A ρ) (length : ℕ)
    (S : StrictRealizationPrefix (A := A) (ρ := ρ) T length) :
    StrictRealizationPrefix (A := A) (ρ := ρ) T (length + 1) := by
  -- The new last stage is the source denominator chosen by `right_fac`; all older data are kept
  -- unchanged.
  refine
    { complex := fun m ↦ Fin.lastCases S.extension_complex S.complex m
      stageIso := fun m ↦ Fin.lastCases (S.extension_stageIso) S.stageIso m
      step := S.extend_step_at
      compat := S.extend_compat_at }

/-- Helper for Lemma 15.88.5: recursively choose strict representatives and strict successor maps
for every finite initial segment of the tower. -/
private noncomputable def strictRealizationPrefix
    (T : DerivedModuleTower A ρ) : (length : ℕ) →
      StrictRealizationPrefix (A := A) (ρ := ρ) T length
  | 0 => StrictRealizationPrefix.base (A := A) (ρ := ρ) T
  | length + 1 =>
      strictRealizationPrefix_succ (A := A) (ρ := ρ) T length
        (strictRealizationPrefix T length)

/-- Helper for Lemma 15.88.5: source-faithfully strictify the tower to a single cochain complex
of sequential modules whose derived image realizes the given stagewise tower. -/
private theorem exists_complex_realization
    (T : DerivedModuleTower A ρ) :
    ∃ (M : CpxSeq), Nonempty (T.Realization (DerivedCategory.Q.obj M)) := by
  -- Proof comment: the strict finite-prefix recursion is now in place via
  -- `strictRealizationPrefix`. The remaining blocker is the final bridge from the reassembled
  -- strict cochain tower to the opaque owner constant `sequentialRingedModuleDerivedEvaluationStep`
  -- used in `DerivedModuleTower.Realization.naturality`.
  -- TODO: prove a bridge theorem identifying the derived evaluation transition on `Q.obj M`
  -- with the standard `Functor.rightDerivedNatTrans` square for
  -- `sequentialRingedModuleEvaluationStep`; then reassemble the strict stage complexes coming from
  -- `strictRealizationPrefix T n` into one `SeqRingMod` complex and apply that bridge.
  sorry

/-- Lemma 15.88.5: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, objects
`K_n ∈ D(A_n)` together with compatible transition maps
`φ_n : K_{n + 1} ⟶ K_n` viewed in `D(A_{n + 1})` by restriction of scalars, encoded here by a
compatible tower `T`, there exists an object of `D(Mod(ℕ, (A_n)))` whose stagewise evaluations
recover the stages of `T` compatibly with its tower maps, together with compatible stagewise
identifications. -/
theorem exists_realization
    (T : DerivedModuleTower A ρ) : ∃ (M : DModSeq), Nonempty (T.Realization M) := by
  -- Route correction: isolate the final theorem from the source-faithful strictification step.
  -- Once a single cochain-complex representative is built, the desired derived object is its
  -- image under `DerivedCategory.Q.obj`.
  exact exists_realization_of_complex_realization (T := T)
    (exists_complex_realization (T := T))

end DerivedModuleTower

end
