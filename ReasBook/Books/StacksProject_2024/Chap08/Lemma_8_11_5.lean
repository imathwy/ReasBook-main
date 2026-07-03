import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap08.Definition_8_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Y' : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.11.5:
- primary domain: gerbes over morphisms of stacks in groupoids and their stability under
  bicategorical `2`-cartesian base change;
- sampled owner-level declarations:
  `StackInGroupoidsOver.Hom.IsGerbeOver`,
  `StackInGroupoidsOver.Hom.isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- sampled bridge/model declaration:
  `StackInGroupoidsOver.twoFibreProductSquare`;
- best owner abstraction: the source-facing theorem should use the stack-morphism square owner
  `BicategoricalTwoCommutativeSquare F G`; the explicit pullback square from Lemma `8.5.6`
  remains only the bridge/model used in the proof;
- primitive-vs-derived split:
  primitive data: the four stack morphisms, the invertible `2`-morphism on stack morphisms,
    the `2`-cartesian hypothesis on the resulting stack-level square, and the gerbe hypothesis
    on `F`;
  derived API: transport of `IsGerbeOver` to the base-changed morphism `F'`.

Source/core/bridge triage:
- `source-facing`: the gerbe base-change statement of Lemma `8.11.5`;
- `core/canonical`: `F.IsGerbeOver`, `BicategoricalTwoCommutativeSquare F G`,
  and `Bicategory.IsFinal`;
- `bridge/view`: the explicit pullback square from Lemma `8.5.6`, used only in the proof. -/

-- Proof sketch: replace the given stack-level `2`-cartesian square by the canonical explicit
-- `2`-fibre product from Lemma `8.5.6`. Check the local essential-surjectivity and local lifting
-- conditions of Lemma `8.11.3` on that explicit pullback object, then transport them back across
-- the equivalence of `2`-fibre product squares.
/-- Lemma 8.11.5: in a `2`-cartesian square of stacks in groupoids over `(C, J)`,
`X' --G'--> X`, `X' --F'--> Y'`, `Y' --G--> Y`, `X --F--> Y`, if `F` is a gerbe over `Y`,
then `F'` is a gerbe over `Y'`. -/
theorem isGerbeOver_of_twoCartesian
    {X' : StackInGroupoidsOver J}
    (F : X ⟶ Y)
    (G : Y' ⟶ Y)
    (F' : X' ⟶ Y')
    (G' : X' ⟶ X)
    (α : G' ≫ F ≅ F' ≫ G)
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := G'
           q := F'
           ψ := α } :
          BicategoricalTwoCommutativeSquare F G))
    (hF : StackInGroupoidsOver.Hom.IsGerbeOver F) :
    StackInGroupoidsOver.Hom.IsGerbeOver F' := by
  sorry

end

end CategoryTheory
