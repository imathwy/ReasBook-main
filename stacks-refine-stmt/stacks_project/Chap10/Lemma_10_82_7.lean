import Mathlib
import stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open LinearMap

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: apply the owner abstraction `UniversallyExact S`. Its short exactness gives the
-- exact sequence, and its universal injectivity for `S.f` supplies the tensor-injectivity input.
-- Then use the tensor criterion for flatness together with exactness preservation for the flat
-- middle term `S.X₂` to deduce flatness of `S.X₁` and `S.X₃`.
/-- Lemma 10.82.7: if `S : ShortComplex (ModuleCat R)` is universally exact and the middle module
`S.X₂` is flat, then the first and third modules are flat. -/
theorem flat_X₁_and_X₃_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ ∧ Module.Flat R S.X₃ := sorry

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the first term. -/
theorem UniversallyExact.flat_X₁ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ :=
  (flat_X₁_and_X₃_of_universallyExact hS).1

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the third term. -/
theorem UniversallyExact.flat_X₃ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ :=
  (flat_X₁_and_X₃_of_universallyExact hS).2

end
