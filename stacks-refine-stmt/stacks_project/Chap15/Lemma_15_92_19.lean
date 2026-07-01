import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Definition_15_28_2
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.Situation_15_92_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorProduct KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling:
- primary domain: derived-complete objects in `D(A)`, tested against the canonical quotient object
  `(A / I)[0]` and the first powered Koszul stage `K_1^•` in the derived category;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.derivedTensorProduct`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: the source-facing owner is still the derived-completeness predicate
  `K.IsDerivedCompleteWithRespectTo I`, while the positivity conditions are expressed by the
  canonical t-structure owner `DerivedCategory.IsLE 0` on the relevant derived tensor products
  with the degree-zero quotient object and the stage-`0` Koszul-power object from Situation
  `15.92.15`;
- primitive data: the generator family `f : Fin r → A`, the derived object `K`, and the owner
  hypothesis of derived completeness with respect to `Ideal.span (Set.range f)`;
- derived API: the degree-zero embedding `single₀`, the powered Koszul tower owner
  `derivedCompletionKoszulPowersDerivedInverseSystem`, and the derived tensor notation
  `K ⊗[A]^L L`, so the theorem should not expose raw functor-application or
  extension-localization internals.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion for nonpositive cohomology under derived completeness;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`, `DerivedCategory.IsLE 0`,
  `DerivedCategory.singleFunctor`, `derivedTensorProduct`, and
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the stage-`0` powered-Koszul object realizing the textbook first Koszul complex
  `K_1^•`. -/

-- Proof sketch: `(1) → (2)` is exactness of derived tensor with the degree-zero quotient object.
-- `(2) → (3)` is the tensor-with-Koszul implication from Lemma `15.89.7`, using that the first
-- powered Koszul stage computes a bounded `I`-power-torsion object with zeroth homology `A / I`.
-- For `(3) → (1)`, descend on the Koszul length as in the textbook proof, using the
-- distinguished triangles for successive partial Koszul complexes together with derived
-- completeness and Lemmas `15.92.6` and `15.92.7` to force the positive cohomology groups to
-- vanish.
/-- Lemma 15.92.19: let `I = (f₁, \ldots, fᵣ)` and let `K` be derived complete with respect to
`I`. Then the following are equivalent: `K` has no positive cohomology; the derived tensor product
`K \otimes_A^{\mathbf L} (A / I)[0]` has no positive cohomology; and the derived tensor product
with the first Koszul complex `K_1^•` from Situation `15.92.15`, represented by the stage `0`
object of the powered Koszul inverse system, has no positive cohomology. -/
theorem derivedComplete_isLE_zero_tfae_of_span_range
    (f : Fin r → A) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    List.TFAE [
      K.IsLE 0,
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))).IsLE 0,
      (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0
    ] := sorry

end

end CategoryTheory
