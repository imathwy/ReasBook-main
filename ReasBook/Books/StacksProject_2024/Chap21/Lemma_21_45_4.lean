import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]

/- The parameter `IsMPseudoCoherent` stands for the site-level `m`-pseudo-coherence predicate on
`D(\mathcal O)` from Definition `21.45.1`. -/
variable (IsMPseudoCoherent : DMod → ℤ → Prop)

variable {J 𝒪 IsMPseudoCoherent}
variable {m : ℤ}

-- Proof sketch: choose strictly perfect local models for `T.obj₁` in degree `m + 1` and for
-- `T.obj₂` in degree `m`, lift the morphism `T.mor₁ : T.obj₁ ⟶ T.obj₂` locally to a morphism of
-- complexes, and compare the cone triangle with `T`. The cone stays strictly perfect, and the
-- long exact homology sequence shows the third vertex is `m`-pseudo-coherent.
/-- Lemma 21.45.4 (1): in a distinguished triangle in `D(\mathcal O)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsMPseudoCoherent T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherent T.obj₂ m) :
    IsMPseudoCoherent T.obj₃ m := sorry

-- Proof sketch: rotate the distinguished triangle once and apply part `(1)` to the rotated
-- triangle, where the hypotheses on the first and third vertices become the required first-two
-- hypotheses after rotation.
/-- Lemma 21.45.4 (2): in a distinguished triangle in `D(\mathcal O)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsMPseudoCoherent T.obj₁ m)
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₂ m := sorry

-- Proof sketch: rotate the distinguished triangle so that the original third vertex becomes the
-- second and the original first vertex becomes the shifted first term, then apply part `(1)` to
-- conclude that the original first term is `(m + 1)`-pseudo-coherent.
/-- Lemma 21.45.4 (3): in a distinguished triangle in `D(\mathcal O)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : IsMPseudoCoherent T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₁ (m + 1) := sorry

end

end SheafOfModules.RingedSite
