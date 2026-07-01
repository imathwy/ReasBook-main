import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Tensoring on the left by `K ⊗ L` is naturally isomorphic to first tensoring on the left by
`K` and then by `L`, after reordering the tensor factors into the Stacks Project convention. -/
noncomputable abbrev ringedSiteDerivedTensorLeftTensorIso
    (K L : RingedSiteDerived J 𝒪) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((MonoidalCategory.tensoringLeft (RingedSiteDerived J 𝒪)).mapIso (β_ K L)) ≪≫
    MonoidalCategory.tensorLeftTensor L K

/-- The functorial currying isomorphism identifying iterated derived internal Hom with derived
internal Hom out of the derived tensor product on a ringed site. -/
noncomputable def ringedSiteDerivedInternalHomTensorNatIso
    (K L : RingedSiteDerived J 𝒪) :
    ihom L ⋙ ihom K ≅ ihom (K ⊗ L) :=
  (Adjunction.rightAdjointUniq
      (ihom.adjunction (K ⊗ L))
      (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
        (ringedSiteDerivedTensorLeftTensorIso K L).symm)).symm

/-- Lemma 21.35.2: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical isomorphism
`R\mathcal H\!\mathit{om}(K, R\mathcal H\!\mathit{om}(L, M)) \cong
R\mathcal H\!\mathit{om}(K \otimes_\mathcal O^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. Taking `H^0(\mathcal C, -)` recovers `21.35.0.1`. -/
noncomputable def ringedSiteDerivedInternalHomTensorIso
    (K L M : RingedSiteDerived J 𝒪) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  (ringedSiteDerivedInternalHomTensorNatIso K L).app M

-- Proof sketch: both sides are definitionally the component at `M` of the functorial natural
-- isomorphism `ringedSiteDerivedInternalHomTensorNatIso K L`.
/-- The textbook isomorphism is the component at `M` of the functorial currying isomorphism. -/
theorem ringedSiteDerivedInternalHomTensorIso_eq_app
    (K L M : RingedSiteDerived J 𝒪) :
    ringedSiteDerivedInternalHomTensorIso K L M =
      (ringedSiteDerivedInternalHomTensorNatIso K L).app M := sorry

end

end SheafOfModules.RingedSite
