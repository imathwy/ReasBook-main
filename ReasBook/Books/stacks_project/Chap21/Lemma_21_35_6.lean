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

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the given ringed site. -/
private abbrev RingedSiteModules (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
private abbrev RingedSiteDerived (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.6: for objects `K`, `L`, and `M` of `D(\mathcal O)` on a ringed site, there is a
canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_\mathcal O^{\mathbf L}
  R\mathcal H\!\mathit{om}(K, L) \to R\mathcal H\!\mathit{om}(K, M)`.
In Lean, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the map is obtained by
braiding the two internal-Hom factors into the order required by the closed-monoidal composition
map. -/
noncomputable def ringedSiteDerivedInternalHomComposition
    (K L M : RingedSiteDerived J 𝒪) :
    ((ihom L).obj M ⊗ (ihom K).obj L) ⟶ (ihom K).obj M :=
  (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫
    MonoidalClosed.comp K L M

-- Proof sketch: unfold the definition; the morphism is exactly the braiding
-- `R\mathcal H\!\mathit{om}(L,M) ⊗ R\mathcal H\!\mathit{om}(K,L)
--   ⟶ R\mathcal H\!\mathit{om}(K,L) ⊗ R\mathcal H\!\mathit{om}(L,M)`
-- followed by the canonical closed-monoidal composition map
-- `[K,L] ⊗ [L,M] ⟶ [K,M]`.
/-- The canonical derived internal-Hom composition morphism is the braiding followed by the
closed-monoidal composition map. -/
theorem ringedSiteDerivedInternalHomComposition_def
    (K L M : RingedSiteDerived J 𝒪) :
    ringedSiteDerivedInternalHomComposition K L M =
      (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫
        MonoidalClosed.comp K L M := sorry

end

end SheafOfModules.RingedSite
