import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap31.Lemma_31_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `Scheme.Hom.fiber` and
-- `genericPointsOfIrreducibleComponents`. Local Chapter 31 precedent fixes the source-facing
-- relative-assassin owner as `Scheme.Modules.relativeAssassin`; the fiber of the base-change
-- projection `g'` over `x = g' x'` is the scheme-theoretic form of
-- `Spec(kappa(s') tensor_[kappa(s)] kappa(x))`.

/-- Lemma 31.7.3: let `f : X ⟶ S` be a locally finite type morphism of schemes, let `ℱ` be a
quasi-coherent `𝒪_X`-module, and let
```
X' --g'--> X
|          |
f'         f
v          v
S' --g--> S
```
be a base-change square. For `x' : X'`, membership of `x'` in
`Ass_{X'/S'}((g')^*ℱ)` is equivalent to membership of its image `x = g' x'` in
`Ass_{X/S}(ℱ)` and to `x'` being a generic point of an irreducible component of the fiber of
`g'` over `x`, i.e. the scheme representing
`Spec(kappa(s') tensor_[kappa(s)] kappa(x))` for `s' = f' x'` and `s = f x`. -/
@[stacks 05DC]
theorem mem_relativeAssassin_pullback_iff_mem_relativeAssassin_and_genericPoint_baseChangeFiber
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X') :
    x' ∈ relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) ↔
      g' x' ∈ relativeAssassin f ℱ ∧
        Scheme.Hom.asFiber g' x' ∈
          genericPointsOfIrreducibleComponents (Scheme.Hom.fiber g' (g' x')) := sorry

end AlgebraicGeometry.Scheme.Modules
