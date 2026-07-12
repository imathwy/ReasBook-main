import Mathlib
import StacksProject_2024.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ChainComplex
open HomologicalComplex

universe u v

section

variable {R : Type u} [Ring R]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Lemma 10.71.4 (1): for a map `M ⟶ N`, a resolution `πG : G ⟶ N`, and a chain complex
`πF : F ⟶ M` of free `R`-modules, there exists a chain map `F ⟶ G` compatible with the
augmentations. -/
-- Proof sketch: construct the lift degreewise using projectivity of the free source terms.
-- This is the same inductive lifting pattern as the owner construction
-- `ProjectiveResolution.lift`, specialized to a source complex that need not itself resolve `M`.
-- Since `F.X 0` is free, lift the composite `F.X 0 ⟶ M ⟶ N` through `πG.f 0`. Inductively,
-- exactness of `G` in positive degrees shows that the obstruction to extending the partial lift
-- lands in the image of the next differential, and the termwise-free hypothesis on `F` allows one
-- to lift through that differential in each degree.
lemma free_complex_lift_to_resolution_exists
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    ∃ α : F ⟶ G, α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f := sorry

/-- Lemma 10.71.4 (2): any two augmentation-compatible lifts from a free chain complex to a
resolution are homotopic. -/
-- Proof sketch: subtract the two lifts to reduce to a chain map `γ : F ⟶ G` with `γ ≫ πG = 0`.
-- The same inductive construction that underlies `ProjectiveResolution.liftHomotopy` then
-- yields a homotopy between `α` and `β`. Lift `γ.f 0` through `G.d 1 0` using exactness at
-- degree `0`, then inductively correct `γ.f (n + 1)` by the previously constructed homotopy
-- component and lift the remainder through `G.d (n + 2) (n + 1)` using exactness and the
-- termwise-free hypothesis on `F`.
theorem free_complex_lifts_to_resolution_are_homotopic
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    {α β : F ⟶ G}
    (hα : α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f)
    (hβ : β ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f) :
    homotopic (ModuleCat R) (ComplexShape.down ℕ) α β := sorry

end
