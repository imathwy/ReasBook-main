import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Modules

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the canonical morphism predicate `LocallyOfFiniteType`;
- local Chapter 28/29 precedent fixes absolute ampleness as `Scheme.Modules.IsAmple`, tensor
  powers as `Scheme.Modules.Invertible.tensorPow`, and relative projective `n`-space as the
  Chapter 29 owner `ProjectiveSpaceOver S n` with tautological sheaf
  `ProjectiveSpaceOver.tautologicalSheaf`;
- a fresh semantic search for the repair recalled `IsImmersion`, and local search verified the
  reusable `ProjectiveSpaceOver.tautologicalSheaf` declaration in Lemma 29.39.1.
- The Stacks tag evidence is consistent: item tag `01VS` and source URL
  `https://stacks.math.columbia.edu/tag/01VS`.
-/

/-- Lemma 29.39.3: if `f : X ⟶ S` is locally of finite type and `L` is an ample invertible
`\mathcal O_X`-module, then all sufficiently high tensor powers of `L` come from immersions of
`X` over `S` into some relative projective space `\mathbf P^n_S`.  Here `\mathbf P^n_S` is
represented by the Chapter 29 owner `ProjectiveSpaceOver S n`; for every `d ≥ d₀`, there are
such a projective-space presentation and an immersion `i` over `S` such that
`L^{\otimes d}` is isomorphic to the pullback of the tautological sheaf. -/
@[stacks 01VS]
theorem isAmple_exists_eventual_projectiveSpaceImmersion_pullbackIso_of_locallyOfFiniteType
    {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
    [MonoidalCategory X.Modules]
    [Invertible L] [IsAmple L] [LocallyOfFiniteType f] :
    ∃ d₀ : {d₀ : ℕ // 1 ≤ d₀},
      ∀ d : ℕ, d₀.1 ≤ d →
        ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
          ∃ e : (Invertible.tensorPow L d ≅
              (pullback i).obj P.tautologicalSheaf),
            IsImmersion i ∧ (i ≫ (P.hom) = f) := sorry

end AlgebraicGeometry
