import Mathlib
import stacks_project.Chap10.Definition_10_82_1
import stacks_project.Chap10.Definition_10_88_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {M' : Type v} [AddCommGroup M'] [Module R M']

-- Proof sketch: identify the pushout of `f` and `g` with the cokernel of the map
-- `x ↦ (g x, -f x)` from `M` to `M' ⊕ N`. After tensoring with any `R`-module `Q`, the kernel of
-- the induced map from `M' ⊗[R] Q` is the quotient of `ker (f.rTensor Q)` by
-- `ker (f.rTensor Q) ∩ ker (g.rTensor Q)`. Thus the pushout map is injective after tensoring with
-- `Q` exactly when `ker (f.rTensor Q) ≤ ker (g.rTensor Q)`, which is the domination condition.
/-- Lemma 10.88.4: for maps `f : M →ₗ[R] N` and `g : M →ₗ[R] M'`, the map `g` dominates `f` if
and only if the canonical map `f' : M' → N'` in the pushout square of `f` and `g` is universally
injective. -/
theorem dominates_iff_universallyInjective_pushout_inr (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    g.Dominates f ↔
      ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).UniversallyInjective := sorry

end

end LinearMap
