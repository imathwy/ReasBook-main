import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import stacks_project.Chap20.Definition_20_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- An `\mathcal O_X`-module sheaf, regarded as a presheaf of modules over the underlying
presheaf of commutative rings. -/
abbrev asCommModulePresheaf (ℱ : ModX) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) :=
  ℱ.val

/-- The stalk of an `\mathcal O_X`-module sheaf, bundled as a module over `\mathcal O_{X, x}`. -/
abbrev stalkModule (ℱ : ModX) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (asCommModulePresheaf ℱ).presheaf x)

/-- A sheaf of `\mathcal O_X`-modules is flat if each stalk is a flat module over the
corresponding stalk of the structure sheaf. -/
def IsFlatModuleSheaf (ℱ : ModX) : Prop :=
  ∀ x : X, Module.Flat (X.presheaf.stalk x) (stalkModule ℱ x)

/-- A flat representative of a derived `\mathcal O_X`-module in the degree range `[a, b]` is a
cochain complex of flat `\mathcal O_X`-modules concentrated in `[a, b]` whose image in the
derived category is isomorphic to the given object. -/
def HasFlatRepresentativeInRange (E : DMod) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex ModX ℤ,
    K.IsStrictlyGE a ∧
      K.IsStrictlyLE b ∧
      (∀ i : ℤ, IsFlatModuleSheaf (K.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj K)

-- Proof sketch: for the forward implication, replace `E` by a bounded-above K-flat complex of
-- flat `\mathcal O_X`-modules, truncate away the terms above `b`, and then truncate below `a`;
-- Lemma `20.48.2` shows the new degree-`a` term remains flat. For the reverse implication,
-- compute derived tensor products using the flat representative and read off the vanishing of
-- homology outside `[a, b]` from the strict support of the representing complex.
/-- Lemma 20.48.3: for a ringed space `(X, \mathcal O_X)` and `a ≤ b`, an object `E` of
`D(\mathcal O_X)` has tor-amplitude in `[a, b]` if and only if it is represented by a complex of
flat `\mathcal O_X`-modules vanishing outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeInRange
    (E : DMod) (a b : ℤ) (_hab : a ≤ b) :
    HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeInRange E a b := sorry

end

end AlgebraicGeometry.RingedSpace
