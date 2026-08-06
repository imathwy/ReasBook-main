import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open CategoryTheory Bundle

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a ready-made mathlib owner for
-- universal Stiefel-Whitney classes on `BO(n)`. Local Chapter 23 precedent already uses
-- `characteristicClassEvalOnUniversalBundle` for universal-bundle evaluation and the
-- `Universal...Family` / `IsUniversal...` pattern in `Theorem_23_7_11`, so this file follows
-- that representation directly.

/-- A family of degree-`i` universal Stiefel-Whitney classes on `BO(n)` in the chosen ambient
mod-`2` cohomology theory `H2`. -/
abbrev UniversalStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (BO : Type) [TopologicalSpace BO] :=
  ∀ i : ℕ, (H2.cohomology i).obj (Opposite.op (TopCat.of BO))

/-- The degree-`i` universal Stiefel-Whitney class on `BO(n)` obtained by evaluating the
degree-`i` Stiefel-Whitney characteristic class on the universal real `n`-plane bundle `γ`. -/
abbrev universalStiefelWhitneyClass
    (H2 : ModTwoCohomologyTheory) (n i : ℕ) (BO : Type) [TopologicalSpace BO]
    (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ]
    (w : StiefelWhitneyClassFamily H2) :
    (H2.cohomology i).obj (Opposite.op (TopCat.of BO)) :=
  characteristicClassEvalOnUniversalBundle γ (w n i)

/-- A family of classes on `BO(n)` is the universal Stiefel-Whitney family when it is obtained by
evaluating a Stiefel-Whitney theory on the universal real `n`-plane bundle `γ`. -/
def IsUniversalBOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    (n : ℕ) (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ]
    (universalW : UniversalStiefelWhitneyFamily H2 BO) : Prop :=
  ∃ w : StiefelWhitneyClassFamily H2,
    IsStiefelWhitneyTheory H2 normalizationData w ∧
      ∀ i : ℕ, universalW i = universalStiefelWhitneyClass H2 n i BO γ w

/-- Unfolding `IsUniversalBOStiefelWhitneyFamily` says that the displayed classes on `BO(n)` are
obtained by evaluating a Stiefel-Whitney theory on the universal real `n`-plane bundle `γ`. -/
theorem isUniversalBOStiefelWhitneyFamily_iff
    {H2 : ModTwoCohomologyTheory} {normalizationData : StiefelWhitneyNormalization H2}
    {n : ℕ} {BO : Type} [TopologicalSpace BO] {γ : BO → Type}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ]
    {universalW : UniversalStiefelWhitneyFamily H2 BO} :
    IsUniversalBOStiefelWhitneyFamily H2 normalizationData n BO γ universalW ↔
      ∃ w : StiefelWhitneyClassFamily H2,
        IsStiefelWhitneyTheory H2 normalizationData w ∧
          ∀ i : ℕ, universalW i = universalStiefelWhitneyClass H2 n i BO γ w :=
  Iff.rfl

/-- Any Stiefel-Whitney theory yields its associated universal family on `BO(n)` by evaluation on
the universal real `n`-plane bundle `γ`. -/
theorem isUniversalBOStiefelWhitneyFamily_of_isStiefelWhitneyTheory
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    {n : ℕ} (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ]
    (w : StiefelWhitneyClassFamily H2)
    (hw : IsStiefelWhitneyTheory H2 normalizationData w) :
    IsUniversalBOStiefelWhitneyFamily H2 normalizationData n BO γ
      (fun i ↦ universalStiefelWhitneyClass H2 n i BO γ w) := by
  exact ⟨w, hw, fun _ ↦ rfl⟩

/-- Theorem 23.3.2. For each real rank-`n` classifying space `BO(n)` with universal bundle `γ`,
there is a family of universal classes `w_i ∈ H^i(BO(n); Z_2)` coming from a Stiefel-Whitney
theory satisfying the Stiefel-Whitney axioms for the chosen standard normalization data from
Theorem 23.3.1. Here
`IsUniversalBOStiefelWhitneyFamily H2 normalizationData.toStiefelWhitneyNormalization n BO γ
universalW` records that the degree-`i` class `universalW i` is obtained by evaluating the
degree-`i` Stiefel-Whitney characteristic class on `γ`. -/
theorem exists_universalBOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ} (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ] :
    ∃ universalW : UniversalStiefelWhitneyFamily H2 BO,
      IsUniversalBOStiefelWhitneyFamily
        H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalW := by
  rcases exists_stiefelWhitneyTheory H2 normalizationData with ⟨w, hw⟩
  refine ⟨fun i ↦ universalStiefelWhitneyClass H2 n i BO γ w, ?_⟩
  exact
    isUniversalBOStiefelWhitneyFamily_of_isStiefelWhitneyTheory
      H2 normalizationData.toStiefelWhitneyNormalization BO γ w hw

/-- For fixed normalization data, the universal Stiefel-Whitney families on `BO(n)` form a
subsingleton. -/
theorem universalBOStiefelWhitneyFamily_subsingleton
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    {n : ℕ} (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ] :
    Subsingleton { universalW : UniversalStiefelWhitneyFamily H2 BO //
      IsUniversalBOStiefelWhitneyFamily H2 normalizationData n BO γ universalW } := by
  refine ⟨?_⟩
  intro a b
  apply Subtype.ext
  funext i
  rcases a.property with ⟨w, hw, ha⟩
  rcases b.property with ⟨w', hw', hb⟩
  have hww' :
      w = w' :=
    subsingleton_stiefelWhitneyTheory_of_normalization H2 normalizationData hw hw'
  subst hww'
  exact (ha i).trans (hb i).symm

instance instSubsingletonUniversalBOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    {n : ℕ} (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ] :
    Subsingleton { universalW : UniversalStiefelWhitneyFamily H2 BO //
      IsUniversalBOStiefelWhitneyFamily H2 normalizationData n BO γ universalW } :=
  universalBOStiefelWhitneyFamily_subsingleton H2 normalizationData BO γ

/-- Theorem 23.3.2 together with Theorem 23.3.1(2): for fixed normalization data, the universal
Stiefel-Whitney family on `BO(n)` exists and is unique. -/
theorem existsUnique_universalBOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ} (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [hγ : RealPlaneBundleClassifyingSpace n BO γ] :
    ∃! universalW : UniversalStiefelWhitneyFamily H2 BO,
      IsUniversalBOStiefelWhitneyFamily
        H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalW := by
  have hExists :
      ∃ universalW : UniversalStiefelWhitneyFamily H2 BO,
        IsUniversalBOStiefelWhitneyFamily
          H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalW :=
    exists_universalBOStiefelWhitneyFamily H2 normalizationData BO γ
  rcases hExists with
    ⟨universalW, hUniversalW⟩
  refine ⟨universalW, hUniversalW, ?_⟩
  intro universalW' hUniversalW'
  exact
    congrArg Subtype.val
      (Subsingleton.elim ⟨universalW', hUniversalW'⟩ ⟨universalW, hUniversalW⟩)
