import StacksProject_2024.stacks_project.Chap10.Definition_10_104_6
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_2
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

/- Semantic recall / verified owner check:
- `lean_leansearch` recalled the general clopen/disjoint-open infrastructure, and
- local project inspection verified the scheme-side owners
  the Cohen-Macaulay affine-local condition from `Chap28/Definition_28_8_1.lean` and
  `Scheme.Hom.RelativeDimension` from `Chap29/Definition_29_29_1.lean`;
- clopen subschemes are therefore represented by clopen opens `U : S.Opens`, with the restricted
  morphism written `f ∣_ U`.
-/

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/-- A morphism of schemes has Cohen-Macaulay fibers if every scheme-theoretic fiber is
locally Cohen-Macaulay. -/
abbrev FiberwiseCohenMacaulay (f : X ⟶ S) : Prop :=
  ∀ s : S,
    (f.fiber s).HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)

/-- Lemma 29.29.4: if `f : X ⟶ S` is flat, locally of finite presentation, and every fiber
`X_s = f.fiber s` is Cohen-Macaulay, then `S` admits a decomposition into pairwise disjoint open
and closed subschemes `S_d` indexed by `d : ℕ` whose union is all of `S`, and the restricted
morphism `f|_{S_d}` is of relative dimension `d`. Here the clopen subscheme `S_d` is represented
by the open subset `U d : S.Opens`, and `f|_{S_d}` is the restriction `f ∣_ (U d)`. -/
@[stacks 02NM]
theorem exists_clopen_stratification_by_relativeDimension_of_flat_of_locallyOfFinitePresentation_of_cohenMacaulayFibers
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : FiberwiseCohenMacaulay f) :
    ∃ U : ℕ → S.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun d e ↦ Disjoint (U d : Set S) (U e : Set S)) ∧
        (∀ d, IsClopen (U d : Set S)) ∧
        ∀ d, RelativeDimension (f ∣_ (U d)) d := sorry

end Scheme.Hom

end

end AlgebraicGeometry
