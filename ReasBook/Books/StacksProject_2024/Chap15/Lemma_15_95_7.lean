import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.95.7:
- primary domain: derived `I`-adic completion and derived tensor products in `D(A)`, with
  pseudo-coherent right tensor factors;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  the notation owner `K^∧[I, hI]` from `Remark_15_92_11`,
  `CategoryTheory.derivedTensorProduct` together with the notation `K ⊗[A]^L L`,
  `DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the source-facing content is the compatibility of the canonical derived
  completion owner with the canonical derived tensor owner, so the public statements should use
  `K^∧[I, hI]`, `K ⊗[A]^L L`, and the chapter pseudo-coherence predicates directly rather than
  the raw functor-application spelling;
- primitive vs. derived:
  primitive data are the ideal `I`, the bounded-above object `K`, and the finite module or
  pseudo-coherent object on the right;
  derived API is the resulting `IsIsomorphic` comparison in `D(A)`.

Source/core/bridge triage:
- `source-facing`: the two completion-vs-tensor compatibility statements below;
- `core/canonical`: `derivedCompletionOf`, the notation `K^∧[I, hI]`, the tensor owner
  `derivedTensorProduct`, the notation `K ⊗[A]^L L`, and `IsPseudoCoherent`;
- `bridge/view`: the degree-zero embedding `ModuleCat.single0Functor` for a finite module `M`. -/

-- Proof sketch: part `(1)` is the finite-module case of part `(2)`, viewing `M` as the degree-zero
-- derived object `(single₀).obj M`. Over the Noetherian ring `A`, finite modules are
-- pseudo-coherent, so the pseudo-coherent tensor-commutation statement applies to `L = M[0]`.
/-- Lemma 15.95.7 (1): if `K ∈ D^-(A)` and `M` is a finite `A`-module, then derived `I`-adic
completion commutes with tensoring `K` by `M`, viewed in degree `0`. -/
theorem derivedCompletionOf_derivedTensorProduct_module_isomorphic_of_finite
    (I : Ideal A) (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M) :
    IsIsomorphic
      ((K.obj ⊗[A]^L (single₀).obj M)^∧[I, I.fg_of_isNoetherianRing])
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L (single₀).obj M) := sorry

-- Proof sketch: represent the bounded-above complex `K` by a bounded-above complex of free
-- modules, represent the pseudo-coherent object `L` by a bounded-above complex of finite free
-- modules, compute the derived tensor product by totalization, and apply the termwise
-- compatibility of derived completion with tensoring by finite free modules from the preceding
-- completion lemmas.
/-- Lemma 15.95.7 (2): if `K ∈ D^-(A)` and `L ∈ D(A)` is pseudo-coherent, then derived
`I`-adic completion commutes with the derived tensor product `K \otimes_A^{\mathbf L} L`. -/
theorem derivedCompletionOf_derivedTensorProduct_isomorphic_of_isPseudoCoherent
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    IsIsomorphic
      ((K.obj ⊗[A]^L L)^∧[I, I.fg_of_isNoetherianRing])
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L L) := sorry

end

end DerivedCategory
