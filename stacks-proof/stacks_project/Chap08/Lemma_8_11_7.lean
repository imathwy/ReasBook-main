import Mathlib
import stacks_project.Chap04.Definition_4_31_2
import stacks_project.Chap04.Definition_4_35_6
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap08.Definition_8_11_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable {X Y Y' X' : StackInGroupoidsOver J}
variable (F : X ⟶ Y)
variable (G : Y' ⟶ Y)
variable (F' : X' ⟶ Y')
variable (G' : X' ⟶ X)
variable (α : F' ≫ G ≅ G' ≫ F)

/-
Domain-style sampling for Lemma 8.11.7:
- primary domain: gerbes over morphisms of stacks in groupoids and their behavior under
  bicategorical `2`-cartesian squares;
- inspected owner-level declarations:
  `IsGerbeOver`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing theorem should be stated directly in terms of stack
  morphisms and the chapter's square owner `BicategoricalTwoCommutativeSquare G F`; the
  based-functor coercions are only bridge/view data and should not appear in the public statement;
- primitive data: the four stack morphisms, the comparison `2`-isomorphism `α`, the
  `2`-cartesian hypothesis on the resulting square, the local essential-image hypothesis on `G`,
  and the gerbe hypothesis on `F'`;
- derived API: descent of the gerbe-over property to `F`.

Source/core/bridge triage:
- `source-facing`: the gerbe descent statement of Lemma `8.11.7`;
- `core/canonical`: `IsGerbeOver`, `LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare G F`, and `Bicategory.IsFinal`;
- `bridge/view`: the coercions from stack morphisms to based functors, which are not part of the
  refined theorem surface. -/

-- Proof sketch: the `2`-cartesian square identifies `X'` with the pullback `Y' ×_Y X`. Prove
-- conditions `(2)(a)` and `(2)(b)` of Lemma `8.11.3` for `F : X ⟶ Y`: first lift target objects
-- locally along `G`, then use that `F'` is a gerbe over `Y'`; for morphisms, pull the source
-- object back to `Y'`, form the corresponding objects of `X'`, and apply the local lifting
-- condition supplied by the gerbe structure on `F'`.
/-- Lemma 8.11.7: let
`X' --G'--> X`,
`X' --F'--> Y'`,
`Y' --G--> Y`,
and `X --F--> Y`
be a `2`-cartesian square of stacks in groupoids over a site `(C, J)`. If every object of every
fiber of `Y` is locally in the essential image of `G`, and if `X'` is a gerbe over `Y'`, then
`X` is a gerbe over `Y`. -/
theorem isGerbeOver_of_twoCartesian_of_locallyEssentiallySurjective
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := F'
           q := G'
           ψ := α } :
          BicategoricalTwoCommutativeSquare G F))
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G)
    (hF' : StackInGroupoidsOver.Hom.IsGerbeOver F') :
    StackInGroupoidsOver.Hom.IsGerbeOver F := by
  sorry

end

end CategoryTheory
