import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

-- Proof sketch: apply the localization functor `K(\mathcal A) ⥤ D(\mathcal A)` at
-- quasi-isomorphisms to the given morphism of distinguished triangles. The first two components
-- become isomorphisms, so Lemma `13.4.3` in its canonical mathlib form
-- `Pretriangulated.isIso₃_of_isIso₁₂` forces the third component to become an isomorphism as
-- well. Translating back across the localization identifies that third component as a
-- quasi-isomorphism.
/-- If the first two components of a morphism of distinguished triangles in `K(\mathcal A)` are
quasi-isomorphisms, then the third component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₃_of_quasiIso_hom₁_hom₂
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₂ : Qis φ.hom₂) :
    Qis φ.hom₃ := sorry

-- Proof sketch: apply the localization `K(\mathcal A) ⥤ D(\mathcal A)` to the morphism of
-- distinguished triangles. The first and third components become isomorphisms, hence the second
-- component is an isomorphism by `Pretriangulated.isIso₂_of_isIso₁₃`. By the characterization of
-- the localization at quasi-isomorphisms, this means that the original second component is a
-- quasi-isomorphism.
/-- If the first and third components of a morphism of distinguished triangles in `K(\mathcal A)`
are quasi-isomorphisms, then the second component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₂_of_quasiIso_hom₁_hom₃
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₂ := sorry

-- Proof sketch: localize the morphism of distinguished triangles to `D(\mathcal A)`, where the
-- second and third components become isomorphisms. Then `Pretriangulated.isIso₁_of_isIso₂₃`
-- gives that the first localized component is an isomorphism, and the defining property of the
-- localization translates this back to quasi-isomorphism of the original first component.
/-- If the second and third components of a morphism of distinguished triangles in `K(\mathcal A)`
are quasi-isomorphisms, then the first component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₁_of_quasiIso_hom₂_hom₃
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₂ : Qis φ.hom₂) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₁ := sorry

-- Proof sketch: combine the three directional two-out-of-three lemmas above. For the Mayer-
-- Vietoris comparison morphism whose components are the maps `c^{K_i}_{X,Z,Y,E}`, these three
-- clauses say exactly that if two of the comparison maps are quasi-isomorphisms, then so is the
-- third.
/-- Lemma 21.26.2: for the morphism of distinguished triangles in `K(\mathcal A)` whose
components are the comparison maps `c^{K_i}_{X,Z,Y,E}`, the three component maps satisfy
two-out-of-three for quasi-isomorphisms; equivalently, the conditions that the first, second, and
third comparison maps are quasi-isomorphisms are all equivalent. -/
theorem triangleMorphism_quasiIso_tfae_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom) :
    List.TFAE [Qis φ.hom₁, Qis φ.hom₂, Qis φ.hom₃] := sorry

end

end CategoryTheory
