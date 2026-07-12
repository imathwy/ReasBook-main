import StacksProject_2024.Chap22.AdmissibleShortExact
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe u

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "KDGMod" => HomotopyCategory (ModuleCat A) (up ℤ)

-- Source/core/bridge triage for 22.8.2:
-- - `source-facing`: distinguished triangles described via admissible short exact sequences of
--   differential graded `A`-modules;
-- - `core/canonical`: the homotopy-category owner
--   `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`;
-- - `bridge/view`: the admissibility data induced by a degreewise splitting of the underlying
--   short complex, together with the canonical characterization
--   `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`.

/-- Definition 22.8.2: in the homotopy category of differential graded `A`-modules, a triangle is
distinguished exactly when it is isomorphic to the triangle `22.8.1.1` associated to an
admissible short exact sequence of differential graded `A`-modules. On the canonical Lean owner
side, this associated triangle is `CochainComplex.trianglehOfDegreewiseSplit S σ` for some
auxiliary degreewise splitting `σ` supplied by admissibility; any other choice is canonically
isomorphic. -/
@[stacks 09K8]
theorem mem_distTriang_iff_exists_iso_trianglehOfAdmissibleShortExact
    (T : Triangle KDGMod) :
    T ∈ distTriang KDGMod ↔
      ∃ S : ShortComplex DGMod,
        IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ∧
          ∃ σ : ∀ n : ℤ, (S.map (eval (ModuleCat A) (up ℤ) n)).Splitting,
            IsIsomorphic T (CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  constructor
  · intro hT
    -- Unpack distinguishedness through the canonical degreewise-split owner theorem.
    rcases (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).1 hT with
      ⟨S, σ, e⟩
    refine ⟨S, ?_, σ, e⟩
    -- The chosen degreewise splitting already gives the source-facing admissible short exactness.
    exact (CochainComplex.isAdmissibleShortExact_iff_nonempty_degreewiseSplitting S).2 ⟨σ⟩
  · rintro ⟨S, _hAdm, σ, e⟩
    -- The source-facing witness is already exactly the data required by the owner theorem.
    exact (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2 ⟨S, σ, e⟩

end
