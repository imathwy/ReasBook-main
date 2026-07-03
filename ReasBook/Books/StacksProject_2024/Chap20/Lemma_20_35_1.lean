import Mathlib
import StacksProject_2024.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 20.35.1:
- primary domain: sheaf cohomology towers of `A`-module sheaves on a topological space, controlled
  by the associated graded ring of an ideal and the canonical Mittag-Leffler predicate on the
  underlying inverse system of abelian groups;
- sampled owners:
  * `idealAssociatedGradedRing` from `Chap10/10_69_0_1`;
  * `CategoryTheory.Functor.IsMittagLeffler`;
  * `Sheaf.cohomologyPresheafFunctor`.
- owner choice: this lemma is `source-facing`; its `core/canonical` owners are
  `idealAssociatedGradedRing` for the graded ring and `Functor.IsMittagLeffler` for the
  stabilization condition.
- primitive data: the chosen tower `ℱ`, the chosen models `powSheaf n`, and the chosen short exact
  sequences `ses n`.
- derived API: the cohomology tower and the direct sum of the degree-`p + 1` cohomology groups.
  Those are used only as canonical functor/type expressions here, so they should not survive as
  separate local public wrappers.
-/

open CategoryTheory
open Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} A)
local notation "AbSheaf" => Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The forgetful functor from sheaves of `A`-modules on `X` to sheaves of abelian groups. -/
abbrev topologicalSpaceModuleSheafUnderlyingAbelian : ModSheaf ⥤ AbSheaf :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- The degree-`p` cohomology functor on sheaves of `A`-modules on `X`, computed on the
underlying abelian sheaf and then evaluated on the top open. -/
abbrev topologicalSpaceModuleCohomologyFunctor (p : ℕ) : ModSheaf ⥤ AddCommGrpCat.{u} :=
  topologicalSpaceModuleSheafUnderlyingAbelian ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

/-- The inverse system `n ↦ H^p(X, \mathcal F_n)` attached to a sequential tower of sheaves of
`A`-modules on `X`. -/
abbrev topologicalSpaceModuleCohomologyTower
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (p : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ℱ ⋙ topologicalSpaceModuleCohomologyFunctor p

/-- The graded direct sum `\bigoplus_n H^p(X,\mathcal G_n)` attached to a family of sheaves of
`A`-modules on `X`. -/
abbrev topologicalSpaceModuleCohomologyDirectSum
    (𝒢 : ℕ → ModSheaf) (p : ℕ) : Type u :=
  DirectSum ℕ fun n ↦ (topologicalSpaceModuleCohomologyFunctor p).obj (𝒢 n)

-- Proof sketch: for each `n`, the short exact sequence
-- `0 → powSheaf n → \mathcal F_{n+1} → \mathcal F_n → 0` gives a boundary map
-- `H^p(X, \mathcal F_n) → H^{p+1}(X, powSheaf n)`. The direct sum of the images of these boundary
-- maps is stable under the action of the associated graded ring, so the Noetherian hypothesis
-- yields finite generation in bounded degree. The long exact sequence then shows that the images
-- of the transition maps in the tower `H^p(X, \mathcal F_n)` stabilize, which is exactly the
-- Mittag-Leffler condition `1`.
/-- Lemma 20.35.1: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X` such that
`0 → I^n \mathcal F_{n + 1} → \mathcal F_{n + 1} → \mathcal F_n → 0` is represented by the chosen
short exact sequence `ses n`. If the direct sum
`\bigoplus_{n \ge 0} H^{p + 1}(X, I^n \mathcal F_{n + 1})`, encoded here by the direct sum
`DirectSum ℕ fun n ↦ H^{p + 1}(X, powSheaf n)`, is Noetherian over the associated graded ring of
`I`, then the inverse system `M_n = H^p(X, \mathcal F_n)` satisfies Mittag-Leffler condition `1`.
-/
theorem topologicalSpace_moduleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ModSheaf)
    (ses : ∀ n : ℕ, ShortComplex ModSheaf)
    (hses : ∀ n : ℕ, (ses n).ShortExact)
    (ses_left_iso : ∀ n : ℕ, (ses n).X₁ ≅ powSheaf n)
    (ses_middle_iso : ∀ n : ℕ, (ses n).X₂ ≅ ℱ.obj (op (n + 1)))
    (ses_right_iso : ∀ n : ℕ, (ses n).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    [Module (idealAssociatedGradedRing I)
      (topologicalSpaceModuleCohomologyDirectSum powSheaf (p + 1))]
    [IsNoetherian (idealAssociatedGradedRing I)
      (topologicalSpaceModuleCohomologyDirectSum powSheaf (p + 1))] :
    ((topologicalSpaceModuleCohomologyTower ℱ p) ⋙
      forget AddCommGrpCat.{u}).IsMittagLeffler := sorry

end

end CategoryTheory
