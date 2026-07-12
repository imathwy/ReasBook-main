import Mathlib
import Mathlib.Algebra.BigOperators.Intervals
import StacksProject_2024.Chap13.Remark_13_33_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped BigOperators

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 13.33.4: a strictly increasing sequence on `ℕ` dominates the identity. -/
theorem le_strictMono_self {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s n := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (hs (Nat.lt_succ_self n)))

/-- Helper for Lemma 13.33.4: every stage lies below some selected subsequence stage. -/
theorem exists_selected_ge {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    ∃ i, n ≤ s i :=
  ⟨n, le_strictMono_self hs n⟩

/-- Helper for Lemma 13.33.4: the least selected subsequence index whose stage is at least `n`. -/
def nextSelectedIndex (s : ℕ → ℕ) (hs : StrictMono s) (n : ℕ) : ℕ :=
  Nat.find (exists_selected_ge hs n)

/-- Helper for Lemma 13.33.4: the chosen selected stage really lies above the original stage. -/
theorem le_nextSelectedStage {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s (nextSelectedIndex s hs n) :=
  Nat.find_spec (exists_selected_ge hs n)

/-- Helper for Lemma 13.33.4: the chosen selected index is minimal among indices whose stage lies
above `n`. -/
theorem nextSelectedIndex_minimal {s : ℕ → ℕ} (hs : StrictMono s) (n i : ℕ)
    (hi : n ≤ s i) :
    nextSelectedIndex s hs n ≤ i :=
  Nat.find_min' (exists_selected_ge hs n) hi

/-- Helper for Lemma 13.33.4: at a selected stage `s i`, the least selected index above it is
exactly `i`. -/
theorem nextSelectedIndex_of_stage {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    nextSelectedIndex s hs (s i) = i := by
  apply le_antisymm
  · exact nextSelectedIndex_minimal hs (s i) i le_rfl
  · exact Nat.le_of_not_lt fun hlt ↦
      not_lt_of_ge (le_nextSelectedStage hs (s i)) (hs hlt)

/-- Helper for Lemma 13.33.4: if `s i = n`, then the chosen selected index above `n` is `i`. -/
theorem nextSelectedIndex_eq_of_eq {s : ℕ → ℕ} (hs : StrictMono s) {i n : ℕ}
    (h : s i = n) :
    nextSelectedIndex s hs n = i := by
  simpa [h] using nextSelectedIndex_of_stage hs i

/-- Helper for Lemma 13.33.4: once a stage is not selected, the next stage has the same chosen
selected index. -/
theorem nextSelectedIndex_succ_of_not_selected {s : ℕ → ℕ} (hs : StrictMono s) {n : ℕ}
    (hsel : ¬ ∃ i, s i = n) :
    nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n := by
  apply le_antisymm
  · apply nextSelectedIndex_minimal hs (n + 1) (nextSelectedIndex s hs n)
    have hlt : n < s (nextSelectedIndex s hs n) := by
      exact lt_of_le_of_ne (le_nextSelectedStage hs n) fun hEq ↦
        hsel ⟨nextSelectedIndex s hs n, hEq.symm⟩
    exact Nat.succ_le_of_lt hlt
  · apply nextSelectedIndex_minimal hs n (nextSelectedIndex s hs (n + 1))
    exact le_trans (Nat.le_succ n) (le_nextSelectedStage hs (n + 1))

/-- Helper for Lemma 13.33.4: the stage immediately after `s i` is controlled by the next
selected index `i + 1`. -/
theorem nextSelectedIndex_of_stage_succ {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    nextSelectedIndex s hs (s i + 1) = i + 1 := by
  apply le_antisymm
  · apply nextSelectedIndex_minimal hs (s i + 1) (i + 1)
    exact Nat.succ_le_of_lt (hs (Nat.lt_succ_self i))
  · exact Nat.le_of_not_lt fun hlt ↦
      let hle : nextSelectedIndex s hs (s i + 1) ≤ i := Nat.lt_succ_iff.mp hlt
      have hstage := le_nextSelectedStage hs (s i + 1)
      have hsle : s (nextSelectedIndex s hs (s i + 1)) ≤ s i := hs.monotone hle
      Nat.not_succ_le_self (s i) (le_trans hstage hsle)

/-- Helper for Lemma 13.33.4: the stage-to-stage transition inside a selected interval block. -/
private theorem intervalBlock_successor_factor
    (K : ℕ ⥤ D) {a j k : ℕ} (h₁ : a ≤ j) (h₂ : j ≤ k) :
    K.map (homOfLE h₁) ≫ K.map (homOfLE h₂) =
      K.map (homOfLE (le_trans h₁ h₂)) := by
  simpa using (K.map_comp (homOfLE h₁) (homOfLE h₂)).symm

/-- Helper for Lemma 13.33.4: the path from stage `a` to the `j`th coproduct summand. -/
private noncomputable def pathToSummand
    (K : ℕ ⥤ D) [HasCoproduct K.obj] (a j : ℕ) :
    K.obj a ⟶ ∐ K.obj :=
  if h : a ≤ j then
    K.map (homOfLE h) ≫ Sigma.ι K.obj j
  else
    0

/-- Helper for Lemma 13.33.4: the path term is the expected composite when `a ≤ j`. -/
private theorem pathToSummand_of_le
    (K : ℕ ⥤ D) [HasCoproduct K.obj] {a j : ℕ} (h : a ≤ j) :
    pathToSummand K a j = K.map (homOfLE h) ≫ Sigma.ι K.obj j := by
  simp [pathToSummand, h]

/-- Helper for Lemma 13.33.4: the path term vanishes when `a ≤ j` fails. -/
private theorem pathToSummand_of_not_le
    (K : ℕ ⥤ D) [HasCoproduct K.obj] {a j : ℕ} (h : ¬ a ≤ j) :
    pathToSummand K a j = 0 := by
  simp [pathToSummand, h]

/-- Helper for Lemma 13.33.4: the finite interval path sum from `a` up to, but not including,
`b`. -/
private noncomputable def intervalPathSum
    (K : ℕ ⥤ D) [HasCoproduct K.obj] (a b : ℕ) :
    K.obj a ⟶ ∐ K.obj :=
  Finset.sum (Finset.Ico a b) (fun j ↦ pathToSummand K a j)

/-- Helper for Lemma 13.33.4: the path sum telescopes against the sequential telescope map. -/
private theorem intervalPathSum_comp_sequentialTelescopeMap
    (K : ℕ ⥤ D) [HasCoproduct K.obj] (a b : ℕ) (hab : a ≤ b) :
    intervalPathSum K a b ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj a - pathToSummand K a b := by
  refine Nat.le_induction ?_ ?_ b hab
  · simp [intervalPathSum, pathToSummand]
  · intro b hab' ih
    have hstep :
        pathToSummand K a b ≫ sequentialTelescopeMap K =
          pathToSummand K a b - pathToSummand K a (b + 1) := by
      have hcomp :
          K.map (homOfLE hab') ≫ K.map (homOfLE (Nat.le_succ b)) =
            K.map (homOfLE (Nat.le_trans hab' (Nat.le_succ b))) :=
        intervalBlock_successor_factor K hab' (Nat.le_succ b)
      calc
        pathToSummand K a b ≫ sequentialTelescopeMap K =
            (K.map (homOfLE hab') ≫ Sigma.ι K.obj b) ≫ sequentialTelescopeMap K := by
              rw [pathToSummand_of_le K hab']
        _ = K.map (homOfLE hab') ≫ (Sigma.ι K.obj b ≫ sequentialTelescopeMap K) := by
              simp [Category.assoc]
        _ =
            K.map (homOfLE hab') ≫
              (Sigma.ι K.obj b - K.map (homOfLE (Nat.le_succ b)) ≫ Sigma.ι K.obj (b + 1)) := by
              rw [Sigma.ι_comp_sequentialTelescopeMap]
        _ =
            K.map (homOfLE hab') ≫ Sigma.ι K.obj b -
              (K.map (homOfLE hab') ≫ K.map (homOfLE (Nat.le_succ b))) ≫
                Sigma.ι K.obj (b + 1) := by
                  simp [Preadditive.comp_sub, Category.assoc]
        _ = pathToSummand K a b - pathToSummand K a (b + 1) := by
              simp [hcomp, pathToSummand_of_le K hab',
                pathToSummand_of_le K (Nat.le_trans hab' (Nat.le_succ b))]
    calc
      intervalPathSum K a (b + 1) ≫ sequentialTelescopeMap K =
          (intervalPathSum K a b + pathToSummand K a b) ≫ sequentialTelescopeMap K := by
            simp [intervalPathSum, Finset.sum_Ico_succ_top hab']
      _ = (Sigma.ι K.obj a - pathToSummand K a b) +
            (pathToSummand K a b - pathToSummand K a (b + 1)) := by
              rw [Preadditive.add_comp, ih, hstep]
      _ = Sigma.ι K.obj a - pathToSummand K a (b + 1) := by
            abel

/-- Helper for Lemma 13.33.4: the finite interval path sum starts with the obvious first term and
the remaining tail factors through the successor map. -/
private theorem intervalPathSum_succ_factor
    (K : ℕ ⥤ D) [HasCoproduct K.obj] {a b : ℕ} (hab : a < b) :
    intervalPathSum K a b =
      Sigma.ι K.obj a +
        K.map (homOfLE (Nat.le_succ a)) ≫ intervalPathSum K (a + 1) b := by
  have htail :
      Finset.sum (Finset.Ico (a + 1) b) (fun j ↦ pathToSummand K a j) =
        K.map (homOfLE (Nat.le_succ a)) ≫ intervalPathSum K (a + 1) b := by
    rw [intervalPathSum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have haj : a + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hcomp :
        K.map (homOfLE (Nat.le_succ a)) ≫ K.map (homOfLE haj) =
          K.map (homOfLE (Nat.le_trans (Nat.le_succ a) haj)) :=
      intervalBlock_successor_factor K (Nat.le_succ a) haj
    rw [pathToSummand_of_le K (Nat.le_trans (Nat.le_succ a) haj), pathToSummand_of_le K haj]
    rw [← Category.assoc, ← hcomp]
  calc
    intervalPathSum K a b =
        pathToSummand K a a + Finset.sum (Finset.Ico (a + 1) b) (fun j ↦ pathToSummand K a j) := by
          rw [intervalPathSum, Finset.sum_eq_sum_Ico_succ_bot hab]
    _ = Sigma.ι K.obj a + Finset.sum (Finset.Ico (a + 1) b) (fun j ↦ pathToSummand K a j) := by
          rw [pathToSummand_of_le K (Nat.le_refl a)]
          simp
    _ = Sigma.ι K.obj a + K.map (homOfLE (Nat.le_succ a)) ≫ intervalPathSum K (a + 1) b := by
          rw [htail]

/-- Helper for Lemma 13.33.4: the correction summand attached to stage `n`. -/
private noncomputable def correctionSummand
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] (n : ℕ) :
    K.obj n ⟶ ∐ K.obj :=
  if _hsel : ∃ i, s i = n then
    0
  else
    intervalPathSum K n (s (nextSelectedIndex s hs n))

/-- Helper for Lemma 13.33.4: the coproduct inclusion of a selected stage into the full system. -/
noncomputable def subsequenceCoproductInclusion
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ (hs.monotone.functor ⋙ K).obj ⟶ ∐ K.obj :=
  Limits.Sigma.desc fun i ↦ Sigma.ι K.obj (s i)

/-- Helper for Lemma 13.33.4: the selected coproduct inclusion evaluates to the corresponding
full coproduct summand. -/
private theorem sigma_ι_comp_subsequenceCoproductInclusion
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ subsequenceCoproductInclusion K s hs =
      Sigma.ι K.obj (s i) := by
  -- Proof comment: evaluate the coproduct desc exactly at the selected summand.
  rw [subsequenceCoproductInclusion, Limits.Sigma.ι_desc]

/-- Helper for Lemma 13.33.4: the interval-block map from the selected telescope source to the
full telescope source. -/
noncomputable def subsequenceIntervalBlockMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ (hs.monotone.functor ⋙ K).obj ⟶ ∐ K.obj :=
  Limits.Sigma.desc fun i ↦
    Sigma.ι K.obj (s i) +
      K.map (homOfLE (Nat.le_succ (s i))) ≫ correctionSummand K s hs (s i + 1)

/-- Helper for Lemma 13.33.4: the extension map from the full coproduct back to the selected
coproduct. -/
noncomputable def extendAlongSubsequenceCoproductDesc
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ K.obj ⟶ ∐ (hs.monotone.functor ⋙ K).obj :=
  Limits.Sigma.desc fun n ↦
    K.map (homOfLE (le_nextSelectedStage hs n)) ≫
      Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n)

/-- Helper for Lemma 13.33.4: if `n` is selected, the canonical selected index reproduces `n`. -/
private theorem selectedStage_eq_nextSelectedStage
    {s : ℕ → ℕ} (hs : StrictMono s) {n : ℕ} (hsel : ∃ i, s i = n) :
    s (nextSelectedIndex s hs n) = n := by
  rcases hsel with ⟨i, hi⟩
  simpa [hi] using congrArg s (nextSelectedIndex_eq_of_eq hs hi)

/-- Helper for Lemma 13.33.4: if `s j = s i + 1`, then `j` is the immediate successor `i + 1`. -/
private theorem selectedIndex_eq_succ_of_stageSucc
    {s : ℕ → ℕ} (hs : StrictMono s) {i j : ℕ} (h : s j = s i + 1) :
    j = i + 1 := by
  have hij : i < j := by
    by_contra hij
    have hji : j ≤ i := Nat.le_of_not_gt hij
    have hsle : s j ≤ s i := hs.monotone hji
    rw [h] at hsle
    exact Nat.not_succ_le_self _ hsle
  have hsucc_le : s i + 1 ≤ s (i + 1) := Nat.succ_le_of_lt (hs (Nat.lt_succ_self i))
  have hsji : s (i + 1) ≤ s j := hs.monotone (Nat.succ_le_of_lt hij)
  exact hs.injective (by
    rw [h] at hsji
    rw [h]
    exact le_antisymm hsucc_le hsji)

/-- Helper for Lemma 13.33.4: if some selected stage equals `s i + 1`, then it is exactly
`s (i + 1)`. -/
private theorem selectedStageSucc_eq
    {s : ℕ → ℕ} (hs : StrictMono s) {i : ℕ} (hsel : ∃ j, s j = s i + 1) :
    s (i + 1) = s i + 1 := by
  rcases hsel with ⟨j, hj⟩
  simpa [selectedIndex_eq_succ_of_stageSucc hs hj] using hj

/-- Helper for Lemma 13.33.4: transport `K.map (homOfLE p)` across an equality of target
stages. -/
private theorem map_homOfLE_comp_eqToHom
    (K : ℕ ⥤ D) {a b c : ℕ} (p : a ≤ b) (q : a ≤ c) (hbc : b = c)
    (hhom : homOfLE p ≫ eqToHom hbc = homOfLE q) :
    K.map (homOfLE p) ≫ eqToHom (by simpa using congrArg K.obj hbc) =
      K.map (homOfLE q) := by
  calc
    K.map (homOfLE p) ≫ eqToHom (by simpa using congrArg K.obj hbc) =
        K.map (homOfLE p) ≫ K.map (eqToHom hbc) := by
          simp [CategoryTheory.eqToHom_map]
    _ = K.map (homOfLE p ≫ eqToHom hbc) := by
          simpa using (K.map_comp (homOfLE p) (eqToHom hbc)).symm
    _ = K.map (homOfLE q) := by
          rw [hhom]

/-- Helper for Lemma 13.33.4: transport a stage map into an equal full coproduct summand. -/
private theorem map_homOfLE_comp_sigma_ι_eq
    (K : ℕ ⥤ D) [HasCoproduct K.obj]
    {a b c : ℕ} (p : a ≤ b) (q : a ≤ c) (hbc : b = c)
    (hpq : Nat.le_trans p (le_of_eq hbc) = q) :
    K.map (homOfLE p) ≫ Sigma.ι K.obj b =
      K.map (homOfLE q) ≫ Sigma.ι K.obj c := by
  have hhom : homOfLE p ≫ eqToHom hbc = homOfLE q := by
    simpa [hpq] using (homOfLE_comp_eqToHom p hbc)
  have hmap :
      K.map (homOfLE p) ≫ eqToHom (by simpa using congrArg K.obj hbc) =
        K.map (homOfLE q) := by
    -- Proof comment: delegate the object transport to the functorial bridge lemma.
    exact map_homOfLE_comp_eqToHom K p q hbc hhom
  calc
    K.map (homOfLE p) ≫ Sigma.ι K.obj b =
      K.map (homOfLE p) ≫ eqToHom (by simpa using congrArg K.obj hbc) ≫ Sigma.ι K.obj c := by
        simpa [Category.assoc] using
          congrArg (fun f ↦ K.map (homOfLE p) ≫ f)
            (Limits.Sigma.eqToHom_comp_ι (f := K.obj) (w := hbc)).symm
    _ = K.map (homOfLE q) ≫ Sigma.ι K.obj c := by
        simpa [Category.assoc] using
          congrArg (fun f ↦ f ≫ Sigma.ι K.obj c) hmap

/-- Helper for Lemma 13.33.4: transport a stage map into an equal subsequence coproduct summand. -/
private theorem map_homOfLE_comp_subsequenceSigma_ι_eq
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {a i j : ℕ} (p : a ≤ s i) (q : a ≤ s j) (hij : i = j)
    (hpq : Nat.le_trans p (by simpa [hij] using le_rfl : s i ≤ s j) = q) :
    K.map (homOfLE p) ≫ Sigma.ι (hs.monotone.functor ⋙ K).obj i =
      K.map (homOfLE q) ≫ Sigma.ι (hs.monotone.functor ⋙ K).obj j := by
  have hstage : s i = s j := congrArg s hij
  have hhom : homOfLE p ≫ eqToHom hstage = homOfLE q := by
    simpa [hstage, hpq] using (homOfLE_comp_eqToHom p hstage)
  have hmap :
      K.map (homOfLE p) ≫
          eqToHom (by simpa [Functor.comp_obj, Monotone.functor_obj] using congrArg K.obj hstage) =
        K.map (homOfLE q) := by
    -- Proof comment: use the same functorial transport bridge after identifying the equal
    -- subsequence stages.
    exact map_homOfLE_comp_eqToHom K p q hstage hhom
  calc
    K.map (homOfLE p) ≫ Sigma.ι (hs.monotone.functor ⋙ K).obj i =
      K.map (homOfLE p) ≫
        eqToHom (by simpa [Functor.comp_obj, Monotone.functor_obj] using congrArg K.obj hstage) ≫
          Sigma.ι (hs.monotone.functor ⋙ K).obj j := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ K.map (homOfLE p) ≫ f)
                (Limits.Sigma.eqToHom_comp_ι
                  (f := (hs.monotone.functor ⋙ K).obj)
                  (w := hij)).symm
    _ = K.map (homOfLE q) ≫ Sigma.ι (hs.monotone.functor ⋙ K).obj j := by
        simpa [Category.assoc] using
          congrArg (fun f ↦ f ≫ Sigma.ι (hs.monotone.functor ⋙ K).obj j) hmap

/-- Helper for Lemma 13.33.4: the selected-stage projection from the full telescope source to the
subsequence source. -/
noncomputable def subsequenceCoproductProjection
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ K.obj ⟶ ∐ (hs.monotone.functor ⋙ K).obj :=
  Limits.Sigma.desc fun n ↦
    dite (∃ i, s i = n) (fun hsel ↦
      eqToHom (by
        simpa [Functor.comp_obj, selectedStage_eq_nextSelectedStage hs hsel]) ≫
        Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n))
      (fun _ ↦ 0)

/-- Helper for Lemma 13.33.4: the correction homotopy from the full telescope source to itself. -/
noncomputable def subsequenceCorrectionHomotopy
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] :
    ∐ K.obj ⟶ ∐ K.obj :=
  Limits.Sigma.desc fun n ↦ correctionSummand K s hs n

/-- Helper for Lemma 13.33.4: the correction summand vanishes on selected stages. -/
private theorem correctionSummand_of_selected
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] {n : ℕ} (hsel : ∃ i, s i = n) :
    correctionSummand K s hs n = 0 := by
  simp [correctionSummand, hsel]

/-- Helper for Lemma 13.33.4: off the subsequence, the correction summand is the interval path
sum up to the next selected stage. -/
private theorem correctionSummand_of_not_selected
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] {n : ℕ} (hsel : ¬ ∃ i, s i = n) :
    correctionSummand K s hs n =
      intervalPathSum K n (s (nextSelectedIndex s hs n)) := by
  simp [correctionSummand, hsel]

/-- Helper for Lemma 13.33.4: the projection picks out the canonical selected summand on a
selected stage. -/
private theorem sigma_ι_comp_subsequenceCoproductProjection_of_stage
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    Sigma.ι K.obj (s i) ≫ subsequenceCoproductProjection K s hs =
      Sigma.ι (hs.monotone.functor ⋙ K).obj i := by
  -- Proof comment: evaluate the coproduct desc on the selected summand and normalize the chosen
  -- selected index `nextSelectedIndex s hs (s i)` to `i`.
  rw [subsequenceCoproductProjection, Limits.Sigma.ι_desc, dif_pos ⟨i, rfl⟩]
  simpa [Functor.comp_obj, selectedStage_eq_nextSelectedStage hs ⟨i, rfl⟩] using
    (Limits.Sigma.eqToHom_comp_ι (f := (hs.monotone.functor ⋙ K).obj)
      (w := (nextSelectedIndex_of_stage hs i).symm))

/-- Helper for Lemma 13.33.4: the projection kills a nonselected stage. -/
private theorem sigma_ι_comp_subsequenceCoproductProjection_of_not_selected
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] {n : ℕ}
    (hsel : ¬ ∃ i, s i = n) :
    Sigma.ι K.obj n ≫ subsequenceCoproductProjection K s hs = 0 := by
  -- Proof comment: evaluate the coproduct desc on the nonselected summand and force the zero
  -- branch of the `dite`.
  rw [subsequenceCoproductProjection, Limits.Sigma.ι_desc]
  simp [hsel]

/-- Helper for Lemma 13.33.4: evaluating the extension map on the `n`th coproduct summand gives
the direct stage-to-selected-stage morphism. -/
private theorem sigma_ι_comp_extendAlongSubsequenceCoproductDesc
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ extendAlongSubsequenceCoproductDesc K s hs =
      K.map (homOfLE (le_nextSelectedStage hs n)) ≫
        Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n) := by
  -- Proof comment: evaluate the coproduct desc on the `n`th summand.
  rw [extendAlongSubsequenceCoproductDesc, Limits.Sigma.ι_desc]

/-- Helper for Lemma 13.33.4: on a selected stage, the extension map lands in the matching
subsequence summand. -/
private theorem sigma_ι_comp_extendAlongSubsequenceCoproductDesc_of_stage
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    Sigma.ι K.obj (s i) ≫ extendAlongSubsequenceCoproductDesc K s hs =
      Sigma.ι (hs.monotone.functor ⋙ K).obj i := by
  -- Proof comment: the selected-stage endpoint is exactly `i`, so the extension component is the
  -- identity map into the `i`th subsequence summand.
  have hnext : nextSelectedIndex s hs (s i) = i := nextSelectedIndex_of_stage hs i
  have hstage : s i = s (nextSelectedIndex s hs (s i)) := by
    simpa [hnext]
  have hhom : homOfLE (le_nextSelectedStage hs (s i)) = eqToHom hstage := by
    apply Subsingleton.elim
  have hmap :
      K.map (homOfLE (le_nextSelectedStage hs (s i))) =
        eqToHom (by
          simpa using congrArg K.obj hstage) := by
    simpa [CategoryTheory.eqToHom_map] using congrArg K.map hhom
  calc
    Sigma.ι K.obj (s i) ≫ extendAlongSubsequenceCoproductDesc K s hs =
      K.map (homOfLE (le_nextSelectedStage hs (s i))) ≫
        Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (s i)) := by
          rw [sigma_ι_comp_extendAlongSubsequenceCoproductDesc]
    _ =
        eqToHom (by
          simpa using congrArg K.obj hstage) ≫
          Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (s i)) := by
            simpa [hmap]
    _ = Sigma.ι (hs.monotone.functor ⋙ K).obj i := by
        simpa using
          (Limits.Sigma.eqToHom_comp_ι
            (f := (hs.monotone.functor ⋙ K).obj)
            (w := hnext.symm))

/-- Helper for Lemma 13.33.4: after reinserting the subsequence coproduct, the extension map
component is the terminal stage map in the selected interval. -/
private theorem sigma_ι_comp_extendAlongSubsequenceCoproductDesc_comp_subsequenceCoproductInclusion
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ extendAlongSubsequenceCoproductDesc K s hs ≫
        subsequenceCoproductInclusion K s hs =
      K.map (homOfLE (le_nextSelectedStage hs n)) ≫
        Sigma.ι K.obj (s (nextSelectedIndex s hs n)) := by
  -- Proof comment: evaluate the extension component first, then reinsert the reached selected
  -- summand into the full coproduct.
  calc
    Sigma.ι K.obj n ≫ extendAlongSubsequenceCoproductDesc K s hs ≫
        subsequenceCoproductInclusion K s hs =
      (Sigma.ι K.obj n ≫ extendAlongSubsequenceCoproductDesc K s hs) ≫
        subsequenceCoproductInclusion K s hs := by
          simp [Category.assoc]
    _ =
        (K.map (homOfLE (le_nextSelectedStage hs n)) ≫
          Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n)) ≫
            subsequenceCoproductInclusion K s hs := by
              simpa [Category.assoc] using
                congrArg (fun f ↦ f ≫ subsequenceCoproductInclusion K s hs)
                  (sigma_ι_comp_extendAlongSubsequenceCoproductDesc K s hs n)
    _ = K.map (homOfLE (le_nextSelectedStage hs n)) ≫
          (Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n) ≫
            subsequenceCoproductInclusion K s hs) := by
            simp [Category.assoc]
    _ = K.map (homOfLE (le_nextSelectedStage hs n)) ≫
          Sigma.ι K.obj (s (nextSelectedIndex s hs n)) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ K.map (homOfLE (le_nextSelectedStage hs n)) ≫ f)
                (sigma_ι_comp_subsequenceCoproductInclusion
                  K s hs (nextSelectedIndex s hs n))

/-- Helper for Lemma 13.33.4: on a selected stage, extending and reincluding is the identity on
that coproduct summand. -/
private theorem sigma_ι_comp_extendAlongSubsequenceCoproductDesc_comp_subsequenceCoproductInclusion_of_stage
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    Sigma.ι K.obj (s i) ≫ extendAlongSubsequenceCoproductDesc K s hs ≫
        subsequenceCoproductInclusion K s hs =
      Sigma.ι K.obj (s i) := by
  -- Proof comment: specialize the terminal-stage formula to a selected stage and collapse the
  -- resulting identity map on that stage.
  rw [← Category.assoc, sigma_ι_comp_extendAlongSubsequenceCoproductDesc_of_stage]
  exact sigma_ι_comp_subsequenceCoproductInclusion K s hs i

/-- Helper for Lemma 13.33.4: the interval-block map component is the displayed selected summand
plus its correction term. -/
private theorem sigma_ι_comp_subsequenceIntervalBlockMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ subsequenceIntervalBlockMap K s hs =
      Sigma.ι K.obj (s i) +
        K.map (homOfLE (Nat.le_succ (s i))) ≫ correctionSummand K s hs (s i + 1) := by
  -- Proof comment: evaluate the coproduct desc of the interval-block map on the selected summand.
  rw [subsequenceIntervalBlockMap, Limits.Sigma.ι_desc]

/-- Helper for Lemma 13.33.4: the correction homotopy component is exactly the correction summand
for that stage. -/
private theorem sigma_ι_comp_subsequenceCorrectionHomotopy
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ subsequenceCorrectionHomotopy K s hs =
      correctionSummand K s hs n := by
  -- Proof comment: evaluate the coproduct desc of the correction homotopy on the `n`th summand.
  rw [subsequenceCorrectionHomotopy, Limits.Sigma.ι_desc]

/-- Helper for Lemma 13.33.4: no selected stage lies strictly before the next selected stage
above `n`. -/
private theorem not_selected_between_stage_and_nextSelectedStage
    {s : ℕ → ℕ} (hs : StrictMono s) {n j : ℕ}
    (hnj : n ≤ j) (hj : j < s (nextSelectedIndex s hs n)) :
    ¬ ∃ i, s i = j := by
  intro hsel
  rcases hsel with ⟨i, hi⟩
  have hmin : nextSelectedIndex s hs n ≤ i := by
    apply nextSelectedIndex_minimal hs n i
    simpa [hi] using hnj
  have hstage : s (nextSelectedIndex s hs n) ≤ s i := hs.monotone hmin
  rw [hi] at hstage
  exact Nat.not_lt_of_ge hstage hj

/-- Helper for Lemma 13.33.4: every interval-path term before the next selected stage is killed by
the selected-stage projection. -/
private theorem pathToSummand_comp_subsequenceCoproductProjection_eq_zero
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {n j : ℕ} (hnj : n ≤ j) (hj : j < s (nextSelectedIndex s hs n)) :
    pathToSummand K n j ≫ subsequenceCoproductProjection K s hs = 0 := by
  rw [pathToSummand_of_le K hnj, Category.assoc]
  have hsel : ¬ ∃ i, s i = j := not_selected_between_stage_and_nextSelectedStage hs hnj hj
  simpa using
    congrArg (fun f ↦ K.map (homOfLE hnj) ≫ f)
      (sigma_ι_comp_subsequenceCoproductProjection_of_not_selected
        (K := K) (s := s) (hs := hs) hsel)

/-- Helper for Lemma 13.33.4: every correction summand is killed by the selected-stage
projection. -/
private theorem correctionSummand_comp_subsequenceCoproductProjection_eq_zero
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (n : ℕ) :
    correctionSummand K s hs n ≫ subsequenceCoproductProjection K s hs = 0 := by
  by_cases hsel : ∃ i, s i = n
  · rw [correctionSummand_of_selected K s hs hsel]
    simp
  · rw [correctionSummand_of_not_selected K s hs hsel, intervalPathSum, Preadditive.sum_comp]
    refine Finset.sum_eq_zero ?_
    intro j hj
    exact pathToSummand_comp_subsequenceCoproductProjection_eq_zero
      (K := K) (s := s) (hs := hs) (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
/-- Helper for Lemma 13.33.4: the reverse first square is the textbook identity
`(1 - f) ≫ c = d ≫ (1 - g)`. -/
theorem sequentialTelescopeMap_comp_extendAlongSubsequenceCoproductDesc
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    sequentialTelescopeMap K ≫ extendAlongSubsequenceCoproductDesc K s hs =
      subsequenceCoproductProjection K s hs ≫
        sequentialTelescopeMap (hs.monotone.functor ⋙ K) := by
  apply Limits.Sigma.hom_ext
  intro n
  by_cases hsel : ∃ i, s i = n
  · rcases hsel with ⟨i, rfl⟩
    have hsecond :
        (K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1)) ≫
            extendAlongSubsequenceCoproductDesc K s hs =
          K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫
            Sigma.ι (hs.monotone.functor ⋙ K).obj (i + 1) := by
      have hnext : nextSelectedIndex s hs (s i + 1) = i + 1 :=
        nextSelectedIndex_of_stage_succ hs i
      calc
        (K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1)) ≫
            extendAlongSubsequenceCoproductDesc K s hs =
          K.map (homOfLE (Nat.le_succ (s i))) ≫
            (Sigma.ι K.obj (s i + 1) ≫ extendAlongSubsequenceCoproductDesc K s hs) := by
              simp [Category.assoc]
        _ = K.map (homOfLE (Nat.le_succ (s i))) ≫
              (K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
                Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (s i + 1))) := by
                  rw [sigma_ι_comp_extendAlongSubsequenceCoproductDesc]
        _ = (K.map (homOfLE (Nat.le_succ (s i))) ≫
              K.map (homOfLE (le_nextSelectedStage hs (s i + 1)))) ≫
                Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (s i + 1)) := by
                  simp [Category.assoc]
        _ = K.map (homOfLE (Nat.le_trans (Nat.le_succ (s i))
              (le_nextSelectedStage hs (s i + 1)))) ≫
                Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (s i + 1)) := by
                  rw [intervalBlock_successor_factor K (Nat.le_succ (s i))
                    (le_nextSelectedStage hs (s i + 1))]
        _ = K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫
              Sigma.ι (hs.monotone.functor ⋙ K).obj (i + 1) := by
                exact map_homOfLE_comp_subsequenceSigma_ι_eq
                  (K := K) (s := s) (hs := hs)
                  (p := Nat.le_trans (Nat.le_succ (s i)) (le_nextSelectedStage hs (s i + 1)))
                  (q := hs.monotone (Nat.le_succ i))
                  (hij := hnext)
                  (by apply Subsingleton.elim)
    calc
      Sigma.ι K.obj (s i) ≫ sequentialTelescopeMap K ≫ extendAlongSubsequenceCoproductDesc K s hs =
          (show K.obj (s i) ⟶ ∐ (hs.monotone.functor ⋙ K).obj from
            Sigma.ι (hs.monotone.functor ⋙ K).obj i) -
            K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫
              Sigma.ι (hs.monotone.functor ⋙ K).obj (i + 1) := by
            rw [← Category.assoc, Sigma.ι_comp_sequentialTelescopeMap]
            rw [Preadditive.sub_comp]
            rw [sigma_ι_comp_extendAlongSubsequenceCoproductDesc_of_stage, hsecond]
      _ =
          Sigma.ι K.obj (s i) ≫
            subsequenceCoproductProjection K s hs ≫
              sequentialTelescopeMap (hs.monotone.functor ⋙ K) := by
            rw [← Category.assoc, sigma_ι_comp_subsequenceCoproductProjection_of_stage]
            simpa [Functor.comp_obj, Monotone.functor_obj] using
              (Sigma.ι_comp_sequentialTelescopeMap (K := hs.monotone.functor ⋙ K) i).symm
  · have hstable :
        nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n :=
      nextSelectedIndex_succ_of_not_selected hs hsel
    have hsecond :
        (K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1)) ≫
            extendAlongSubsequenceCoproductDesc K s hs =
          K.map (homOfLE (le_nextSelectedStage hs n)) ≫
            Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n) := by
      let hstep : n + 1 ≤ s (nextSelectedIndex s hs n) := by
        simpa [hstable] using le_nextSelectedStage hs (n + 1)
      calc
        (K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1)) ≫
            extendAlongSubsequenceCoproductDesc K s hs =
          K.map (homOfLE (Nat.le_succ n)) ≫
            (Sigma.ι K.obj (n + 1) ≫ extendAlongSubsequenceCoproductDesc K s hs) := by
              simp [Category.assoc]
        _ = K.map (homOfLE (Nat.le_succ n)) ≫
              (K.map (homOfLE (le_nextSelectedStage hs (n + 1))) ≫
                Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (n + 1))) := by
                  rw [sigma_ι_comp_extendAlongSubsequenceCoproductDesc]
        _ = (K.map (homOfLE (Nat.le_succ n)) ≫
              K.map (homOfLE (le_nextSelectedStage hs (n + 1)))) ≫
                Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (n + 1)) := by
                  simp [Category.assoc]
        _ = K.map (homOfLE (Nat.le_trans (Nat.le_succ n) (le_nextSelectedStage hs (n + 1)))) ≫
              Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs (n + 1)) := by
                rw [intervalBlock_successor_factor K (Nat.le_succ n) (le_nextSelectedStage hs (n + 1))]
        _ = K.map (homOfLE (le_nextSelectedStage hs n)) ≫
              Sigma.ι (hs.monotone.functor ⋙ K).obj (nextSelectedIndex s hs n) := by
                exact map_homOfLE_comp_subsequenceSigma_ι_eq
                  (K := K) (s := s) (hs := hs)
                  (p := Nat.le_trans (Nat.le_succ n) (le_nextSelectedStage hs (n + 1)))
                  (q := le_nextSelectedStage hs n)
                  (hij := hstable)
                  (by apply Subsingleton.elim)
    calc
      Sigma.ι K.obj n ≫ sequentialTelescopeMap K ≫ extendAlongSubsequenceCoproductDesc K s hs =
          0 := by
            rw [← Category.assoc, Sigma.ι_comp_sequentialTelescopeMap]
            rw [Preadditive.sub_comp]
            rw [sigma_ι_comp_extendAlongSubsequenceCoproductDesc]
            rw [← hsecond]
            abel
      _ =
          Sigma.ι K.obj n ≫
            subsequenceCoproductProjection K s hs ≫
              sequentialTelescopeMap (hs.monotone.functor ⋙ K) := by
            rw [← Category.assoc, sigma_ι_comp_subsequenceCoproductProjection_of_not_selected
              (K := K) (s := s) (hs := hs) hsel]
            simp

/-- Helper for Lemma 13.33.4: the correction identity
`h ≫ (1 - f) = 𝟙 - c ≫ a`. -/
theorem subsequenceCorrectionHomotopy_comp_sequentialTelescopeMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    subsequenceCorrectionHomotopy K s hs ≫ sequentialTelescopeMap K =
      𝟙 _ -
        extendAlongSubsequenceCoproductDesc K s hs ≫ subsequenceCoproductInclusion K s hs := by
  apply Limits.Sigma.hom_ext
  intro n
  by_cases hsel : ∃ i, s i = n
  · rcases hsel with ⟨i, rfl⟩
    rw [← Category.assoc, sigma_ι_comp_subsequenceCorrectionHomotopy]
    rw [correctionSummand_of_selected K s hs ⟨i, rfl⟩]
    simp [Preadditive.comp_sub,
      sigma_ι_comp_extendAlongSubsequenceCoproductDesc_comp_subsequenceCoproductInclusion_of_stage]
  · rw [← Category.assoc, sigma_ι_comp_subsequenceCorrectionHomotopy]
    rw [correctionSummand_of_not_selected K s hs hsel]
    rw [intervalPathSum_comp_sequentialTelescopeMap K n (s (nextSelectedIndex s hs n))
      (le_nextSelectedStage hs n)]
    simp [Preadditive.comp_sub,
      sigma_ι_comp_extendAlongSubsequenceCoproductDesc_comp_subsequenceCoproductInclusion,
      pathToSummand_of_le K (le_nextSelectedStage hs n)]

/-- Helper for Lemma 13.33.4: one step after a selected stage, the correction summand has the
standard telescoping composite with the sequential telescope map. -/
private theorem correctionSummandStageSuccCompSequentialTelescopeMap
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] (i : ℕ) :
    correctionSummand K s hs (s i + 1) ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj (s i + 1) -
        K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
          Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1))) := by
  -- Proof comment: split on whether `s i + 1` is itself selected; the nonselected branch is
  -- exactly the interval-path telescope identity.
  by_cases hsel : ∃ j, s j = s i + 1
  · rw [correctionSummand_of_selected K s hs hsel]
    simp
    calc
      (0 : K.obj (s i + 1) ⟶ ∐ K.obj) =
          Sigma.ι K.obj (s i + 1) - Sigma.ι K.obj (s i + 1) := by
            simp
      _ =
          Sigma.ι K.obj (s i + 1) -
            K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
              Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1))) := by
                have hmap :
                    K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
                        Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1))) =
                      Sigma.ι K.obj (s i + 1) := by
                  -- Proof comment: identify the reached selected stage with `i + 1` and then
                  -- transport the terminal coproduct summand back to `s i + 1`.
                  simpa using
                    map_homOfLE_comp_sigma_ι_eq
                      (K := K)
                      (p := le_nextSelectedStage hs (s i + 1))
                      (q := le_rfl)
                      (hbc := by
                        simpa [nextSelectedIndex_of_stage_succ hs i] using
                          selectedStageSucc_eq hs hsel)
                      (by apply Subsingleton.elim)
                rw [hmap]
  · rw [correctionSummand_of_not_selected K s hs hsel]
    simpa [pathToSummand_of_le K (le_nextSelectedStage hs (s i + 1))] using
      intervalPathSum_comp_sequentialTelescopeMap K (s i + 1)
        (s (nextSelectedIndex s hs (s i + 1))) (le_nextSelectedStage hs (s i + 1))

/-- Helper for Lemma 13.33.4: off the subsequence, the correction summand splits into the obvious
first summand plus the successor correction term. -/
private theorem correctionSummandStepOfNotSelected
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] {n : ℕ} (hsel : ¬ ∃ i, s i = n) :
    correctionSummand K s hs n =
      Sigma.ι K.obj n +
        K.map (homOfLE (Nat.le_succ n)) ≫ correctionSummand K s hs (n + 1) := by
  have hstable : nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n :=
    nextSelectedIndex_succ_of_not_selected hs hsel
  -- Proof comment: split on whether the successor stage is selected; both branches reduce to the
  -- interval-path recursion after normalizing the chosen selected index.
  by_cases hsel' : ∃ i, s i = n + 1
  · rw [correctionSummand_of_not_selected K s hs hsel,
      correctionSummand_of_selected K s hs hsel']
    have hnext : s (nextSelectedIndex s hs n) = n + 1 := by
      simpa [hstable] using selectedStage_eq_nextSelectedStage hs hsel'
    have hlt : n < s (nextSelectedIndex s hs n) := by
      rw [hnext]
      exact Nat.lt_succ_self n
    rw [intervalPathSum_succ_factor K hlt]
    simp [hnext, intervalPathSum]
  · rw [correctionSummand_of_not_selected K s hs hsel,
      correctionSummand_of_not_selected K s hs hsel']
    have hlt : n < s (nextSelectedIndex s hs n) := by
      exact lt_of_le_of_ne (le_nextSelectedStage hs n) fun hEq ↦
        hsel ⟨nextSelectedIndex s hs n, hEq.symm⟩
    simpa [hstable] using intervalPathSum_succ_factor K hlt

/-- Helper for Lemma 13.33.4: the forward interval-block square is the textbook map identity
`(1 - g) ≫ a = b ≫ (1 - f)`. -/
theorem subsequence_interval_block_forward_square
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    sequentialTelescopeMap (hs.monotone.functor ⋙ K) ≫
        subsequenceCoproductInclusion K s hs =
      subsequenceIntervalBlockMap K s hs ≫ sequentialTelescopeMap K := by
  apply Limits.Sigma.hom_ext
  intro i
  have hsecond :
      K.map (homOfLE (Nat.le_succ (s i))) ≫
          correctionSummand K s hs (s i + 1) ≫
            sequentialTelescopeMap K =
        K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
          K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫
            Sigma.ι K.obj (s (i + 1)) := by
    have hnext : nextSelectedIndex s hs (s i + 1) = i + 1 :=
      nextSelectedIndex_of_stage_succ hs i
    calc
      K.map (homOfLE (Nat.le_succ (s i))) ≫
          correctionSummand K s hs (s i + 1) ≫
            sequentialTelescopeMap K =
        K.map (homOfLE (Nat.le_succ (s i))) ≫
          (correctionSummand K s hs (s i + 1) ≫ sequentialTelescopeMap K) := by
            simp
      _ =
          K.map (homOfLE (Nat.le_succ (s i))) ≫
            (Sigma.ι K.obj (s i + 1) -
              K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
                Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1)))) := by
              rw [correctionSummandStageSuccCompSequentialTelescopeMap]
      _ =
          K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
            K.map (homOfLE (Nat.le_succ (s i))) ≫
              (K.map (homOfLE (le_nextSelectedStage hs (s i + 1))) ≫
                Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1)))) := by
              simp [Preadditive.comp_sub]
      _ =
          K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
            K.map (homOfLE
              (Nat.le_trans (Nat.le_succ (s i)) (le_nextSelectedStage hs (s i + 1)))) ≫
                Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1))) := by
              simpa [Category.assoc] using congrArg
                (fun f ↦
                  K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
                    f ≫ Sigma.ι K.obj (s (nextSelectedIndex s hs (s i + 1))))
                (intervalBlock_successor_factor K (Nat.le_succ (s i))
                  (le_nextSelectedStage hs (s i + 1)))
      _ =
          K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
            K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫
              Sigma.ι K.obj (s (i + 1)) := by
              exact congrArg
                (fun f ↦
                  K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) - f)
                (map_homOfLE_comp_sigma_ι_eq
                  (K := K)
                  (p := Nat.le_trans (Nat.le_succ (s i))
                    (le_nextSelectedStage hs (s i + 1)))
                  (q := hs.monotone (Nat.le_succ i))
                  (hbc := by simpa [hnext])
                  (by apply Subsingleton.elim))
  have hsecond' :
      (K.map (homOfLE (Nat.le_succ (s i))) ≫ correctionSummand K s hs (s i + 1)) ≫
          sequentialTelescopeMap K =
        K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1) -
          K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫ Sigma.ι K.obj (s (i + 1)) := by
    simpa [Category.assoc] using hsecond
  have hιsucc :
      ((hs.monotone.functor ⋙ K).map (homOfLE (Nat.le_succ i)) ≫
          Sigma.ι (hs.monotone.functor ⋙ K).obj (i + 1)) ≫
            subsequenceCoproductInclusion K s hs =
        K.map (homOfLE (hs.monotone (Nat.le_succ i))) ≫ Sigma.ι K.obj (s (i + 1)) := by
    simpa [Functor.comp_obj, Monotone.functor_obj, Category.assoc] using
      congrArg
        (fun f ↦ (hs.monotone.functor ⋙ K).map (homOfLE (Nat.le_succ i)) ≫ f)
        (sigma_ι_comp_subsequenceCoproductInclusion K s hs (i + 1))
  have hinterval :
      (Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ subsequenceIntervalBlockMap K s hs) ≫
          sequentialTelescopeMap K =
        (Sigma.ι K.obj (s i) +
            K.map (homOfLE (Nat.le_succ (s i))) ≫
              correctionSummand K s hs (s i + 1)) ≫
          sequentialTelescopeMap K := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ f ≫ sequentialTelescopeMap K)
        (sigma_ι_comp_subsequenceIntervalBlockMap K s hs i)
  have hinterval' :
      Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ subsequenceIntervalBlockMap K s hs ≫
          sequentialTelescopeMap K =
        (Sigma.ι K.obj (s i) +
            K.map (homOfLE (Nat.le_succ (s i))) ≫
              correctionSummand K s hs (s i + 1)) ≫
          sequentialTelescopeMap K := by
    simpa [Category.assoc] using hinterval
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp]
  rw [sigma_ι_comp_subsequenceCoproductInclusion, hιsucc]
  rw [hinterval', Preadditive.add_comp, Sigma.ι_comp_sequentialTelescopeMap]
  rw [hsecond']
  abel

/-- Helper for Lemma 13.33.4: the forward interval-block map followed by the selected projection
is the identity on the subsequence telescope source. -/
theorem subsequenceIntervalBlockMap_comp_subsequenceCoproductProjection
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    subsequenceIntervalBlockMap K s hs ≫ subsequenceCoproductProjection K s hs =
      𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro i
  calc
    Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫
        subsequenceIntervalBlockMap K s hs ≫
          subsequenceCoproductProjection K s hs =
      Sigma.ι (hs.monotone.functor ⋙ K).obj i := by
        rw [← Category.assoc, sigma_ι_comp_subsequenceIntervalBlockMap]
        simp [Preadditive.add_comp, Category.assoc]
        rw [sigma_ι_comp_subsequenceCoproductProjection_of_stage]
        simp [correctionSummand_comp_subsequenceCoproductProjection_eq_zero]
    _ = Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ 𝟙 _ := by
        simp

/-- Helper for Lemma 13.33.4: the selected inclusion followed by the extension map is the identity
on the subsequence coproduct. -/
theorem subsequenceCoproductInclusion_comp_extendAlongSubsequenceCoproductDesc
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    subsequenceCoproductInclusion K s hs ≫ extendAlongSubsequenceCoproductDesc K s hs =
      𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro i
  calc
    Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫
        subsequenceCoproductInclusion K s hs ≫
          extendAlongSubsequenceCoproductDesc K s hs =
      Sigma.ι (hs.monotone.functor ⋙ K).obj i := by
        rw [subsequenceCoproductInclusion, Limits.Sigma.ι_desc_assoc]
        exact sigma_ι_comp_extendAlongSubsequenceCoproductDesc_of_stage K s hs i
    _ = Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ 𝟙 _ := by
        simp

/-- Helper for Lemma 13.33.4: the correction identity
`(1 - f) ≫ h = 𝟙 - b ≫ d`. -/
theorem sequentialTelescopeMap_comp_subsequenceCorrectionHomotopy
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    sequentialTelescopeMap K ≫ subsequenceCorrectionHomotopy K s hs =
      𝟙 _ -
        subsequenceCoproductProjection K s hs ≫ subsequenceIntervalBlockMap K s hs := by
  apply Limits.Sigma.hom_ext
  intro n
  by_cases hsel : ∃ i, s i = n
  · rcases hsel with ⟨i, rfl⟩
    calc
      Sigma.ι K.obj (s i) ≫ sequentialTelescopeMap K ≫
          subsequenceCorrectionHomotopy K s hs =
        0 - K.map (homOfLE (Nat.le_succ (s i))) ≫
          correctionSummand K s hs (s i + 1) := by
            have hcorr :
                (K.map (homOfLE (Nat.le_succ (s i))) ≫ Sigma.ι K.obj (s i + 1)) ≫
                    subsequenceCorrectionHomotopy K s hs =
                  K.map (homOfLE (Nat.le_succ (s i))) ≫
                    correctionSummand K s hs (s i + 1) := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    K.map (homOfLE (Nat.le_succ (s i))) ≫ f)
                  (sigma_ι_comp_subsequenceCorrectionHomotopy K s hs (s i + 1))
            rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp]
            rw [sigma_ι_comp_subsequenceCorrectionHomotopy]
            rw [hcorr]
            rw [correctionSummand_of_selected K s hs ⟨i, rfl⟩]
      _ =
          Sigma.ι K.obj (s i) ≫
            (𝟙 _ - subsequenceCoproductProjection K s hs ≫
              subsequenceIntervalBlockMap K s hs) := by
              have hinterval :
                  Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫
                      subsequenceIntervalBlockMap K s hs =
                    Sigma.ι K.obj (s i) +
                      K.map (homOfLE (Nat.le_succ (s i))) ≫
                        correctionSummand K s hs (s i + 1) :=
                sigma_ι_comp_subsequenceIntervalBlockMap K s hs i
              symm
              calc
                Sigma.ι K.obj (s i) ≫
                    (𝟙 _ - subsequenceCoproductProjection K s hs ≫
                      subsequenceIntervalBlockMap K s hs) =
                  Sigma.ι K.obj (s i) -
                    (Sigma.ι K.obj (s i) +
                      K.map (homOfLE (Nat.le_succ (s i))) ≫
                        correctionSummand K s hs (s i + 1)) := by
                        rw [Preadditive.comp_sub]
                        rw [← Category.assoc, sigma_ι_comp_subsequenceCoproductProjection_of_stage]
                        simpa using
                          congrArg
                            (fun f ↦ Sigma.ι K.obj (s i) ≫ 𝟙 _ - f)
                            hinterval
                _ = 0 - K.map (homOfLE (Nat.le_succ (s i))) ≫
                      correctionSummand K s hs (s i + 1) := by
                        abel
  · calc
      Sigma.ι K.obj n ≫ sequentialTelescopeMap K ≫
          subsequenceCorrectionHomotopy K s hs =
        Sigma.ι K.obj n := by
          have hcorr :
              (K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1)) ≫
                  subsequenceCorrectionHomotopy K s hs =
                K.map (homOfLE (Nat.le_succ n)) ≫ correctionSummand K s hs (n + 1) := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ K.map (homOfLE (Nat.le_succ n)) ≫ f)
                (sigma_ι_comp_subsequenceCorrectionHomotopy K s hs (n + 1))
          rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp]
          rw [sigma_ι_comp_subsequenceCorrectionHomotopy]
          rw [hcorr]
          rw [correctionSummandStepOfNotSelected K s hs hsel]
          abel
      _ =
          Sigma.ι K.obj n ≫
            (𝟙 _ - subsequenceCoproductProjection K s hs ≫
              subsequenceIntervalBlockMap K s hs) := by
              rw [Preadditive.comp_sub]
              rw [← Category.assoc,
                sigma_ι_comp_subsequenceCoproductProjection_of_not_selected
                  (K := K) (s := s) (hs := hs) hsel]
              simp

end

end CategoryTheory
