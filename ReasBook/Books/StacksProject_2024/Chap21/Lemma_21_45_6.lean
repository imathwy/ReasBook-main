import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

/-
The parameter `IsMPseudoCoherent` stands for the site-level `m`-pseudo-coherence predicate from
Definition `21.45.1`, used here as the ambient notion on `D(\mathcal O)`.
-/
variable (IsMPseudoCoherent : DerivedCategory (ringedSiteModuleCategory J 𝒪) → ℤ → Prop)

/-- A derived `\mathcal O`-module on a ringed site is pseudo-coherent if it is
`m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent K m

-- Proof sketch: represent the biproduct by the split distinguished triangle from Derived
-- Categories, Lemma `13.4.10`, use Lemma `21.45.4` to show that the iterated shifts
-- `L[n] ⊞ L[n + 1]` remain `m`-pseudo-coherent, and then work backwards through the split
-- triangles to conclude that the left summand is `m`-pseudo-coherent.
/-- Lemma 21.45.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m := sorry

-- Proof sketch: the same split-triangle argument, now exchanging the two summands, proves that
-- `m`-pseudo-coherence also descends to the right direct summand.
/-- Lemma 21.45.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent L m := sorry

-- Proof sketch: unfold pseudo-coherence as `m`-pseudo-coherence for every integer and apply part
-- `(1)` degreewise.
/-- Lemma 21.45.6 (3): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O)`, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DMod)
    (hKL : IsPseudoCoherent J 𝒪 IsMPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent J 𝒪 IsMPseudoCoherent K := sorry

-- Proof sketch: unfold pseudo-coherence as `m`-pseudo-coherence for every integer and apply part
-- `(2)` degreewise.
/-- Lemma 21.45.6 (4): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O)`, then `L` is
pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DMod)
    (hKL : IsPseudoCoherent J 𝒪 IsMPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent J 𝒪 IsMPseudoCoherent L := sorry

end

end SheafOfModules.RingedSite
