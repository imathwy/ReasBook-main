import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_66_1
import stacks_project.Chap15.Lemma_15_102_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

open scoped IdealPowerSubmodule

local notation "DMod" => DerivedCategory (ModuleCat A)
variable (K : DMod) (p : ℤ)
local notation "Extp" => derivedExtModuleFunctor K p

/- Domain-style sampling:
- primary domain: functorial derived `Ext` for a pseudo-coherent object against finite modules,
  with Artin-Rees control on the image of the restriction map `I^[n] M ↪ M`;
- sampled owner declarations:
  `derivedExtModuleFunctor`,
  `idealPowerSubmodule`,
  `idealPowerSubtypeNatTrans`;
- best owner abstraction: the canonical Ext module owner here is
  `(Extp).obj M`, and the source-facing map is the induced `A`-linear morphism
  `(Extp).map ((idealPowerSubtypeNatTrans I n).app M)` coming from the chapter owner
  `idealPowerSubtypeNatTrans`;
- primitive data: the ideal `I`, the pseudo-coherent complex `K`, the finite module `M`, the
  inclusion `I^[n] M ↪ M`, and the ambient Ext module `(Extp).obj M`;
- derived API: the range containment in the ideal-power submodule of `(Extp).obj M`.

Source/core/bridge triage:
- `source-facing`: the eventual Artin-Rees containment for the image of
  `Ext^p_A(K, I^[n] M) → Ext^p_A(K, M)`;
- `core/canonical`: `(Extp).obj M`;
- `bridge/view`: the induced `ModuleCat` morphism `(Extp).map ((idealPowerSubtypeNatTrans I n).app M)`.
-/

-- Proof sketch: represent the pseudo-coherent complex `K` by a bounded-above complex of finite
-- free `A`-modules. Then `Ext^p_A(K, M)` is computed by a finite three-term Hom complex, and the
-- restriction map from `I^[n] M` to `M` is induced by multiplying those finite modules by `I^n`.
-- Apply Lemma `15.102.1` to this finite complex to obtain a uniform Artin-Rees constant `c`
-- controlling the image in cohomology.
/-- Lemma 15.102.4: if `A` is Noetherian, `K ∈ D(A)` is pseudo-coherent, and `M` is a finite
`A`-module, then for every integer `p` there is a constant `c` such that for `n ≥ c` the image of
`Ext^p_A(K, I^[n] M) → Ext^p_A(K, M)` is contained in `I^[n - c] Ext^p_A(K, M)`. -/
theorem exists_derivedExt_image_le_idealPower_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (M : ModuleCat A) [Module.Finite A M]
    (p : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      LinearMap.range
          (((Extp).map ((idealPowerSubtypeNatTrans I n).app M)).hom) ≤
        I^[n - c] ((Extp).obj M) := sorry

end

end CategoryTheory
