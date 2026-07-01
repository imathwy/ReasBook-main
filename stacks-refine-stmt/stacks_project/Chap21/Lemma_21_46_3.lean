import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap21.Definition_21_46_1

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable [Abelian (RingedSiteModules 𝒪)]
variable [CategoryWithHomology (RingedSiteModules 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules 𝒪))]

local notation "Mod" => RingedSiteModules 𝒪
local notation "DMod" => DerivedCategory (RingedSiteModules 𝒪)

/-- An object of `D(\mathcal O)` admits a representative by a cochain complex of flat
`\mathcal O`-modules concentrated in degrees `[a, b]`. -/
def HasFlatRepresentativeInRange (E : DMod) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex Mod ℤ,
    K.IsStrictlyGE a ∧
      K.IsStrictlyLE b ∧
      (∀ i : ℤ,
        IsFlat 𝒪
          (show SheafOfModules (ringSheaf J 𝒪) from K.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj K)

-- Proof sketch: if `E` is represented by such a flat complex, derived tensor products are computed
-- termwise, so tor-amplitude is immediate from the degree support. Conversely, start from a
-- K-flat replacement with flat terms as in Lemma `21.17.11`, trim the complex from above using
-- vanishing of the top cohomology and flat-kernel preservation from Lemma `18.28.10`, and then
-- truncate below `a`; Lemma `21.46.2` gives flatness in the new degree `a` term.
/-- Lemma 21.46.3: an object `E` of `D(\mathcal O)` has tor-amplitude in `[a, b]` if and only if
it is isomorphic in `D(\mathcal O)` to a cochain complex `\mathcal E^\bullet` of flat
`\mathcal O`-modules with `\mathcal E^i = 0` for `i ∉ [a, b]`. -/
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeInRange
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeInRange E a b := sorry

end

end SheafOfModules.RingedSite
