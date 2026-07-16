import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_82_1
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

namespace CategoryTheory.ShortComplex

/- Domain triage:
- primary domain: universally exact short complexes of modules and the owner property
  `Module.MittagLeffler`;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`;
- primitive data vs. derived API: `UniversallyExact S` is the primitive short-complex datum, and
  propagation of the owner property `Module.MittagLeffler` along it is derived API belonging in
  the `UniversallyExact` namespace.
-/

namespace UniversallyExact

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for every family `(Q α)` of `R`-modules, tensor the universally exact short exact
-- sequence `S` with `∏ α, Q α` and compare it with the product of the tensor sequences. The top
-- horizontal map is injective by universal exactness, and the right vertical map is injective by
-- Proposition `10.89.5` for `S.X₂`, so the left vertical map is injective as well.
/-- Lemma 10.89.7 (1): in a universally exact short exact sequence of `R`-modules, if the middle
term is Mittag-Leffler, then the left term is Mittag-Leffler. -/
theorem mittagLeffler_X₁ [Module.MittagLeffler R S.X₂] (hS : UniversallyExact S) :
    Module.MittagLeffler R S.X₁ := sorry

-- Proof sketch: for every family `(Q α)`, compare the tensor sequence with `∏ α, Q α` to the
-- product of the tensor sequences with each `Q α`. If an element of the middle tensor maps to zero
-- in the product, its image in the right tensor also maps to zero, hence vanishes by
-- Mittag-Leffler for `S.X₃`. Exactness of the tensor sequence lifts it from the left tensor, and
-- injectivity on the left term from universal exactness plus Mittag-Leffler for `S.X₁` forces the
-- original element to vanish.
/-- Lemma 10.89.7 (2): in a universally exact short exact sequence of `R`-modules, if the left and
right terms are Mittag-Leffler, then the middle term is Mittag-Leffler. -/
theorem mittagLeffler_X₂ [Module.MittagLeffler R S.X₁] [Module.MittagLeffler R S.X₃]
    (hS : UniversallyExact S) : Module.MittagLeffler R S.X₂ := sorry

end

end UniversallyExact
end CategoryTheory.ShortComplex
