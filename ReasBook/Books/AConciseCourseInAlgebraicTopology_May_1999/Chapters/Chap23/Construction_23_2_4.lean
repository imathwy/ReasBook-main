import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Bundle

universe u v w

-- Semantic recall via `lean_leansearch` did not expose an existing imported owner for the
-- universal-to-bundle characteristic-class construction. Chapter 23 already packages the needed
-- classification input as `characteristicClassEvalOnUniversalBundle_bijective` in
-- `Lemma_23_2_2`, so the construction below is recorded as the existence-and-uniqueness
-- statement for the characteristic class with prescribed value on the universal bundle, together
-- with the resulting pullback formula.

section

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}
variable {BO : Type u} [TopologicalSpace BO]
variable (γ : BO → Type v)
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)]
variable [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)]
variable [∀ b, Module ℝ (γ b)]
variable [hγ : RealPlaneBundleClassifyingSpace n BO γ]

namespace CharacteristicClass

@[simp] theorem pullbackValue_eq_map_of_evalOnUniversalBundle_eq
    (c : CharacteristicClass n q k)
    {u : (k q).obj (Opposite.op (TopCat.of BO))}
    (hu : characteristicClassEvalOnUniversalBundle γ c = u)
    {X : Type u} [TopologicalSpace X]
    (f : C(X, BO)) :
    c.pullbackValue f γ = (k q).map (TopCat.ofHom f).op u := by
  simpa [hu] using (c.naturality f γ).symm

end CharacteristicClass

variable [hk : (k q).rightOp.IsHomotopyInvariant]

/-- Construction 23.2.4. A universal degree-`q` cohomology class on `BO(n)` determines a unique
degree-`q` characteristic class of real `n`-plane bundles, characterized by its value on the
universal bundle `γ`. -/
theorem existsUnique_characteristicClass_of_universalClass
    (u : (k q).obj (Opposite.op (TopCat.of BO))) :
    ∃! c : CharacteristicClass n q k,
      characteristicClassEvalOnUniversalBundle γ c = u := by
  have hbij :
      Function.Bijective
        (characteristicClassEvalOnUniversalBundle γ :
          CharacteristicClass n q k → (k q).obj (Opposite.op (TopCat.of BO))) :=
    characteristicClassEvalOnUniversalBundle_bijective
  rcases hbij.2 u with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact hbij.1 (hc'.trans hc.symm)

end
