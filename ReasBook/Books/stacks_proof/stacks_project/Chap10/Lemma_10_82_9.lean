import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

-- Proof sketch: for any `R`-module `Q`, tensoring commutes with composition, so
-- `(g.comp f).rTensor Q = (g.rTensor Q).comp (f.rTensor Q)`. The composition of the
-- injective tensor maps supplied by `hf` and `hg` is injective.
/-- Lemma 10.82.9: a composition of universally injective `R`-module maps is universally
injective. -/
@[stacks 05CI]
theorem universallyInjective_comp {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hg : UniversallyInjective.{u, w, x, max v w x} g)
    (hf : UniversallyInjective.{u, v, w, max v w x} f) :
    UniversallyInjective.{u, v, x, max v w x} (g.comp f) := by
  intro Q _ _
  simpa [LinearMap.rTensor_comp] using
    Function.Injective.comp (hg Q (inferInstance) (inferInstance))
      (hf Q (inferInstance) (inferInstance))

end

end LinearMap
