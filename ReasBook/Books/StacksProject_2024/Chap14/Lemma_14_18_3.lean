import StacksProject_2024.Chap14.Lemma_14_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SimplicialObject
open SimplicialObject.Splitting
open scoped Simplicial

universe u

noncomputable section

namespace SSet

variable {U V : SSet.{u}} (f : U ⟶ V)

/- Domain-style sampling for 14.18.3:
- primary domain: simplicial-set morphisms acting on nondegenerate simplices
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.φ`,
  `SimplicialObject.Split.mk'`,
  `SimplicialObject.Split.Hom`,
  `SSet.nonDegenerateSplitting`
- best owner abstraction: the split simplicial sets `Split.mk' U.nonDegenerateSplitting` and
  `Split.mk' V.nonDegenerateSplitting`, together with the canonical bridge
  `toNonDegenerateSplitHom f hPreserves`
- primitive data: the canonical splittings, the underlying simplicial-set morphism `f`, and the
  proof that `f` sends nondegenerate simplices to nondegenerate simplices
- derived API: the induced degreewise maps on nondegenerate simplices
  `(toNonDegenerateSplitHom f hPreserves).f n`
- source/core/bridge triage: the degreewise injective, surjective, and bijective consequences are
  the `source-facing` statements; the induced maps on nondegenerate summands are only a
  `bridge/view`, so the public statements should use the canonical split-owner bridge rather than
  a parallel local wrapper
-/

section

variable
  (hPreserves :
    ∀ ⦃n : ℕ⦄ (x : U.nonDegenerate n),
      (U.nonDegenerateSplitting.φ f n) x ∈ V.nonDegenerate n)

/-- The canonical morphism between the split simplicial sets attached to the nondegenerate
splittings of `U` and `V`, induced by a simplicial-set morphism that preserves nondegenerate
simplices. -/
abbrev toNonDegenerateSplitHom :
    Split.mk' U.nonDegenerateSplitting ⟶ Split.mk' V.nonDegenerateSplitting where
  F := f
  f := fun n x ↦ ⟨U.nonDegenerateSplitting.φ f n x, hPreserves x⟩
  comm := fun _ ↦ rfl

-- Proof sketch: apply the canonical splittings `U.nonDegenerateSplitting` and
-- `V.nonDegenerateSplitting` by nondegenerate simplices. Hypothesis `hPreserves` makes the
-- canonical split morphism `toNonDegenerateSplitHom f hPreserves` land in the distinguished
-- nondegenerate summands of `V`, and injectivity on those summands implies injectivity on each
-- coproduct component, hence on every degree map `f.app (op ⦋n⦌)`.
/-- Lemma 14.18.3: if a morphism of simplicial sets sends nondegenerate simplices to
nondegenerate simplices and the induced map on nondegenerate simplices is injective, then each
degree map `f_n` is injective. -/
theorem degreewise_injective_of_nondegenerate_injective
    (hInjective :
      ∀ n : ℕ, Function.Injective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Injective (f.app (op ⦋n⦌)) := sorry

-- Proof sketch: use the same splitting argument as in the injective case. Surjectivity of the map
-- on nondegenerate summands implies surjectivity on each coproduct decomposition coming from
-- `U.nonDegenerateSplitting` and `V.nonDegenerateSplitting`, so every degree map of `f` is
-- surjective.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is surjective on the
nondegenerate simplices, then it is surjective in every degree. -/
theorem degreewise_surjective_of_nondegenerate_surjective
    (hSurjective :
      ∀ n : ℕ, Function.Surjective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)) := sorry

-- Proof sketch: combine the injective and surjective arguments for the induced map on the
-- nondegenerate summands. The canonical splitting decompositions then yield bijectivity of each
-- degree map.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is bijective on the
nondegenerate simplices, then it is bijective in every degree. -/
theorem degreewise_bijective_of_nondegenerate_bijective
    (hBijective :
      ∀ n : ℕ, Function.Bijective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Bijective (f.app (op ⦋n⦌)) := sorry

end

end SSet
