import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}

-- Semantic recall: the source only uses quasi-coherent modules, but the stalkwise Chapter 10
-- owner makes sense for every `\mathcal O_X`-module, so the source-facing quasi-coherent case is
-- exposed through the more reusable stalkwise owner below.

/-- Definition 31.5.1 (1): for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme
`X`, a point `x ∈ X` is weakly associated to `\mathcal F` if the maximal ideal of the local ring
`\mathcal O_{X, x}` is weakly associated to the stalk module `\mathcal F_x`. -/
def weaklyAssociatedAt (ℱ : X.Modules) (x : X) : Prop :=
  Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk x)
    (@RingedSpace.stalkModuleCat X.toRingedSpace ℱ x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- Definition 31.5.1 (2): `WeakAss(\mathcal F)` is the set of weakly associated points of a
quasi-coherent `\mathcal O_X`-module `\mathcal F` on `X`. -/
def weakAss (ℱ : X.Modules) : Set X :=
  ℱ.weaklyAssociatedAt

/-- Membership in `WeakAss(\mathcal F)` means being weakly associated to `\mathcal F` at that
point. -/
theorem mem_weakAss_iff (ℱ : X.Modules) (x : X) :
    x ∈ ℱ.weakAss ↔ ℱ.weaklyAssociatedAt x :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.RingedSpace

variable (X : Scheme.{u})

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- Definition 31.5.1 (3): the weakly associated points of a scheme `X` are the weakly associated
points of its structure sheaf `\mathcal O_X`. -/
abbrev weakAss : Set X :=
  Scheme.Modules.weakAss 𝒪X

/-- Membership in the weakly associated points of `X` is membership in the weakly associated
points of its structure sheaf. -/
theorem mem_weakAss_iff (x : X) :
    x ∈ X.weakAss ↔ Scheme.Modules.weaklyAssociatedAt 𝒪X x :=
  Scheme.Modules.mem_weakAss_iff 𝒪X x

/-- Membership in the weakly associated points of `X` is equivalent to the weak-association
condition for the maximal ideal of the stalk of `\mathcal O_X`. -/
theorem mem_weakAss_iff_isWeaklyAssociatedToModule (x : X) :
    x ∈ X.weakAss ↔
      Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk x)
        (@RingedSpace.stalkModuleCat X.toRingedSpace 𝒪X x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  Scheme.Modules.mem_weakAss_iff 𝒪X x

end AlgebraicGeometry.Scheme
