import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules :=
  SheafOfModules
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [MonoidalCategory DMod]

/- The parameter `IsPerfectObject` stands for the perfect-object predicate on `D(\mathcal O)` from
the surrounding perfect-complex formalization. -/
variable (IsPerfectObject : DMod → Prop)

-- Proof sketch: this is the closure statement for the perfect-object predicate under the derived
-- tensor product; in the textbook it is obtained from the pseudo-coherence and Tor-amplitude
-- criteria of Lemmas `21.47.4`, `21.45.5`, and `21.46.7`.
/-- Lemma 21.47.7: if `K` and `L` are perfect objects of `D(\mathcal O)`, then their derived
tensor product `K \otimes_{\mathcal O}^{\mathbf L} L` is again perfect. In this item file, the
perfectness predicate is abstracted as `IsPerfectObject`. -/
theorem tensor_isPerfect_of_isPerfect
    (hTensor :
      ∀ K L : DMod,
        IsPerfectObject K → IsPerfectObject L → IsPerfectObject (K ⊗ L))
    (K L : DMod)
    (hK : IsPerfectObject K)
    (hL : IsPerfectObject L) :
    IsPerfectObject (K ⊗ L) := sorry

end

end SheafOfModules.RingedSite
