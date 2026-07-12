import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

-- Semantic recall: the source-facing morphism of Lemma 28.26.9 is the specialized
-- invertible-sheaf instance of the generic `Proj.fromOfGlobalSections` construction. Nearby
-- Chapter 28 files already reuse the Chapter 17 owner `Γ_*(ℒ)` and the source-facing
-- nonvanishing-open owner `hℒ.nonvanishingOpen s`, but the exact canonical morphism
-- `X ⟶ Proj(Γ_*(X, ℒ))`, its `X_s = f ⁻¹(D₊(s))` compatibility, and the graded comparison maps
-- `f^*𝒪(n) → ℒ^{\otimes n}` are not yet packaged in a dependency-closed local API.

/- Lemma 28.26.9: let `X` be a scheme and let `\mathcal L` be an invertible
`\mathcal O_X`-module. If the nonvanishing opens `X_s` attached to positive homogeneous sections
of `Γ_*(X, \mathcal L)` cover `X`, then there is a canonical morphism
`f : X → Proj(Γ_*(X, \mathcal L))` with
`f^{-1}(D_+(s)) = X_s`, comparison maps `f^*\mathcal O_Y(n) → \mathcal L^{\otimes n}` compatible
with multiplication, identity on the degree-`n` global sections, and a local isomorphism property
after replacing `n` by a positive multiple. The current dependency-closed API reaches this lemma
through the generic `Proj.fromOfGlobalSections` owner and its basic-open preimage theorem, but not
yet through a dedicated Chapter 28 construction for invertible sheaves. -/
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
#check fun (ℒ : ModX) [Invertible ℒ] ↦ Γ_*(ℒ)
#check fun (ℒ : ModX) [hℒ : Invertible ℒ] {n : ℕ} (s : Γ(hℒ n, ⊤)) ↦ hℒ.nonvanishingOpen s

end AlgebraicGeometry.Scheme.Modules
