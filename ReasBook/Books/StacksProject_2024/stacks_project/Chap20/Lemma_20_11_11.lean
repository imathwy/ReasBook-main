import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksProject_2024.Chap12.Lemma_12_29_1
import StacksProject_2024.Chap17.Lemma_17_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.11:
- primary domain: adjunctions, exactness, and injective-object preservation for module-sheaf
  functors on ringed spaces;
- sampled owner declarations:
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `IsFlat.pullback_exact`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.injective_obj_of_injective`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical pushforward
  functor `f _*`, derived from the adjunction `f^* ⊣ f _*`;
- primitive data: only the morphism `f : X ⟶ Y` and the flatness hypothesis;
- derived API: preservation of injective objects by `f _*`, and the objectwise injectivity
  consequence for `(f _*).obj ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a flat direct image sends injective
  `𝒪_X`-modules to injective `𝒪_Y`-modules;
- `core/canonical`: `Functor.PreservesInjectiveObjects` together with
  `Functor.injective_obj_of_injective`;
- `bridge/view`: this ringed-space specialization built from
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `IsFlat.pullback_exact`, and the owner theorem
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`.
-/

-- Proof sketch: Lemma `17.20.2` makes `f^*` exact for a flat morphism, and the canonical
-- adjunction criterion `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint` upgrades
-- the adjunction `f^* ⊣ f _*` to preservation of injective objects by `f _*`.
/-- For a flat morphism of ringed spaces, direct image on module sheaves preserves injective
objects. -/
instance modulePushforward_preservesInjectiveObjects_of_isFlat
    (f : X ⟶ Y) [IsFlat f] :
    (f _*).PreservesInjectiveObjects := by
  simpa using CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
    (SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f))
    (IsFlat.pullback_exact f)

/-- Lemma 20.11.11: if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is flat and `ℐ` is an injective
`𝒪_X`-module, then `(f _*).obj ℐ` is an injective `𝒪_Y`-module. -/
@[stacks 02N5]
theorem modulePushforward_injective_of_isFlat
    (f : X ⟶ Y) (hf : IsFlat f) (ℐ : X.Modules) (hℐ : Injective ℐ) :
    Injective ((f _*).obj ℐ) := by
  let _ : IsFlat f := hf
  exact (f _*).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace
