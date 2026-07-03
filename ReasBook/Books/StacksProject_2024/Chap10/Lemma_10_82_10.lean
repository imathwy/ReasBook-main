import Mathlib
import stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {M'' : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup M''] [Module R M'']

-- Proof sketch: tensoring commutes with composition, so for every `R`-module `Q` the map
-- `(g.comp f).rTensor Q` factors as `(g.rTensor Q).comp (f.rTensor Q)`. If the composition is
-- injective, then `f.rTensor Q` is injective; hence `f` is universally injective.
/-- Lemma 10.82.10: if the composition `M → M''` of two `R`-linear maps `M → M'` and
`M' → M''` is universally injective, then the first map `M → M'` is universally injective. -/
theorem universallyInjective_of_comp {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hgf : UniversallyInjective.{u, v, w, w} (g.comp f)) : UniversallyInjective.{u, v, w, w} f := by
  intro Q _ _
  have hcomp : Function.Injective ((g.rTensor Q).comp (f.rTensor Q)) := by
    simpa [LinearMap.rTensor_comp] using hgf Q inferInstance inferInstance
  intro x y hxy
  apply hcomp
  exact congrArg (g.rTensor Q) hxy

end

end LinearMap
