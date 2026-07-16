import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_14
import StacksProject_2024.stacks_project.Chap22.AdmissibleShortExact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.CochainComplex

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "Q" => HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)

-- Semantic recall hit: `lean_leansearch` returned the canonical degreewise-split owner
-- `CochainComplex.trianglehOfDegreewiseSplit` and the mapping-cone comparison API; local
-- precedent is the Chapter 13 analogue `exists_mappingCone_triangleh_iso_of_degreewiseSplit`.

/-- Helper for Lemma 22.9.4 (1): for an admissible short exact sequence
`0 ⟶ K ⟶ L ⟶ M ⟶ 0` of differential graded `A`-modules, there exists a degreewise splitting of
the underlying short complex for which the standard mapping-cone triangle of the first map is
isomorphic in the homotopy category of differential graded `A`-modules to the triangle associated
to the admissible short exact sequence, through the identity maps on `K` and `L`. -/
theorem existsMappingConeTrianglehIsoOfAdmissibleShortExact
    (S : ShortComplex DGMod)
    (hS : IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S) :
    ∃ (σ : ∀ n : ℤ,
        (S.map (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)).Splitting)
      (e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ),
      e.hom.hom₁ = 𝟙 ((Q).obj S.X₁) ∧
        e.hom.hom₂ = 𝟙 ((Q).obj S.X₂) := by
  rcases (isAdmissibleShortExact_iff_nonempty_degreewiseSplitting S).1 hS with ⟨σ₀⟩
  let σ :
      ∀ n : ℤ,
        (S.map (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)).Splitting :=
    fun n ↦ by
      simpa [degreewiseShortComplex] using σ₀ n
  obtain ⟨e, he⟩ := exists_mappingCone_triangleh_iso_of_degreewiseSplit S σ
  exact ⟨σ, e, he⟩

/-- Companion bridge for Lemma 22.9.4 (2): the canonical split-mono factorization short complex of
`f` is an admissible short exact sequence of differential graded `A`-modules. -/
instance splitMonoFactorizationShortComplex_isAdmissibleShortExact
    {K L : DGMod} (f : K ⟶ L) :
    IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem
      (splitMonoFactorizationShortComplex f) :=
  (isAdmissibleShortExact_iff_nonempty_degreewiseSplitting (splitMonoFactorizationShortComplex f)).2
      ⟨splitMonoFactorizationSplitting f⟩

/-- Lemma 22.9.4 (2): every morphism of differential graded `A`-modules
fits into the canonical admissible short exact sequence
`splitMonoFactorizationShortComplex f`, and the associated triangle is isomorphic to the
mapping-cone triangle of `f`. -/
@[stacks 09KF]
theorem existsAdmissibleShortExactTrianglehIsoMappingCone
    {K L : DGMod} (f : K ⟶ L) :
    ∃ (_hS : IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem
        (splitMonoFactorizationShortComplex f))
      (σ : ∀ n : ℤ,
        ((splitMonoFactorizationShortComplex f).map
          (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)).Splitting)
      (e : trianglehOfDegreewiseSplit (splitMonoFactorizationShortComplex f) σ ≅
        mappingCone.triangleh f),
      e.hom.hom₁ = 𝟙 ((Q).obj K) := by
  -- Route correction: package the canonical Chapter 13 split factorization instead of rebuilding
  -- the admissible short exact sequence by hand.
  have hS :
      IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem
        (splitMonoFactorizationShortComplex f) :=
    inferInstance
  -- The imported Chapter 13 theorem already supplies the triangle comparison for this witness.
  rcases exists_degreewiseSplit_triangleh_iso_mappingCone f with ⟨e, he⟩
  exact ⟨hS, splitMonoFactorizationSplitting f, e, he⟩

end

end CochainComplex
