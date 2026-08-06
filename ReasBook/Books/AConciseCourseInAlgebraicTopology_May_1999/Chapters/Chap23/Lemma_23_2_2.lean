import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Principle_1_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_2_1

open CategoryTheory Bundle

noncomputable section

universe u v w

section

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}
variable {BO : Type u} [TopologicalSpace BO]
variable {γ : BO → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)]
variable [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)]
variable [∀ b, Module ℝ (γ b)]

/-- Evaluating a degree-`q` characteristic class on the universal real `n`-plane bundle `γ`. -/
abbrev characteristicClassEvalOnUniversalBundle
    (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace n BO γ] :
    CharacteristicClass n q k →
      (k q).obj (Opposite.op (TopCat.of BO)) :=
  fun c ↦ c.onBundle γ

@[simp] theorem characteristicClassEvalOnUniversalBundle_apply
    [RealPlaneBundleClassifyingSpace n BO γ] (c : CharacteristicClass n q k) :
    characteristicClassEvalOnUniversalBundle γ c =
      c.onBundle γ :=
  rfl

/-- Lemma 23.2.2. Evaluation on the universal bundle `γ` identifies degree-`q` characteristic
classes of real `n`-plane bundles with `k^q(BO(n))`. Here the classification input from Theorem
23.1.5 is packaged by `[RealPlaneBundleClassifyingSpace n BO γ]`. -/
theorem characteristicClassEvalOnUniversalBundle_bijective
    [RealPlaneBundleClassifyingSpace n BO γ]
    [(k q).rightOp.IsHomotopyInvariant] :
    Function.Bijective
      (characteristicClassEvalOnUniversalBundle γ :
        CharacteristicClass n q k → (k q).obj (Opposite.op (TopCat.of BO))) := sorry

end
