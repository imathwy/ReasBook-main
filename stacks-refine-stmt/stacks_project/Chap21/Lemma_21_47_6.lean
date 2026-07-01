import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]

/- The parameter `IsPerfect` stands for perfectness on `D(\mathcal O)` from the preceding
development of perfect complexes on ringed sites. -/
variable (IsPerfect : DMod → Prop)

-- Proof sketch: combine Lemma `21.47.4`, which characterizes perfect objects by pseudo-coherence
-- and local finite Tor dimension, with Lemma `21.45.4 (1)` for pseudo-coherence and Lemma
-- `21.46.6 (1)` for Tor-amplitude in a distinguished triangle.
/-- Lemma 21.47.6 (1): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `K` and `L` are
perfect, then `M` is perfect. -/
theorem isPerfect_obj₃_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := sorry

-- Proof sketch: reduce perfectness using Lemma `21.47.4`, then apply Lemma `21.45.4 (2)` to the
-- pseudo-coherent part and Lemma `21.46.6 (2)` to the local finite Tor-dimension part.
/-- Lemma 21.47.6 (2): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `K` and `M` are
perfect, then `L` is perfect. -/
theorem isPerfect_obj₂_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsPerfect T.obj₁) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₂ := sorry

-- Proof sketch: once more use Lemma `21.47.4` to express perfectness as pseudo-coherence plus
-- local finite Tor dimension, then apply Lemma `21.45.4 (3)` and Lemma `21.46.6 (3)` to the
-- distinguished triangle.
/-- Lemma 21.47.6 (3): let `(\mathcal C, \mathcal O)` be a ringed site and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O)`. If `L` and `M` are
perfect, then `K` is perfect. -/
theorem isPerfect_obj₁_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₁ := sorry

end

end SheafOfModules.RingedSite
