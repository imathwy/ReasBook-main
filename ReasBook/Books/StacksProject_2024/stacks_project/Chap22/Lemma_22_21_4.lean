import StacksProject_2024.Chap22.PropertyI

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

-- The shared Chapter 22 owner for property `(I)` now lives in `Chap22.PropertyI`; this file keeps
-- only the source-facing existence theorem for the resulting notion.

namespace DGModuleContext

/-- Lemma 22.21.4: every differential graded `A`-module admits a quasi-isomorphism to a
differential graded `A`-module with property `(I)`. -/
@[stacks 09KU]
theorem exists_quasiIso_to_hasPropertyI
    (𝒜 : DGModuleContext) (M : 𝒜.moduleCat) :
    ∃ (I : 𝒜.moduleCat) (f : M ⟶ I), 𝒜.quasiIso f ∧ HasPropertyI 𝒜 I := sorry

end DGModuleContext
