import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` was unavailable here (HTTP 429). Local precedent in
-- `Chap17/Example_17_18_1.lean` and `Chap19/Lemma_19_8_2.lean` shows that the `\mathcal O_X`-dual
-- on the scheme module category `X.Modules` is modeled by `CategoryTheory.ihom` with target
-- `𝟙_`.

section

variable {X : Scheme.{u}}
variable [MonoidalCategory X.Modules]
variable [MonoidalClosed X.Modules]
local notation "ModX" => X.Modules
local notation "𝒪X" => (𝟙_ ModX : ModX)

/-- The `\mathcal O_X`-dual of a module sheaf on `X`. -/
abbrev dual (ℱ : ModX) : ModX :=
  (ihom ℱ).obj 𝒪X

postfix:max "ᵛ" => dual

/-- Definition 31.12.1 (1): for an integral locally Noetherian scheme `X` and a coherent
`\mathcal O_X`-module `ℱ`, the reflexive hull `ℱ^{**}` is the double `\mathcal O_X`-dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}
  (\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X), \mathcal O_X)`. -/
abbrev reflexiveHull (ℱ : ModX) : ModX :=
  ℱᵛᵛ

/-- Contravariant functoriality of the `\mathcal O_X`-dual. -/
noncomputable abbrev dualMap {ℱ 𝒢 : ModX} (f : ℱ ⟶ 𝒢) :
    𝒢ᵛ ⟶ ℱᵛ :=
  (MonoidalClosed.pre f).app 𝒪X

/-- Functoriality of the reflexive hull construction. -/
noncomputable abbrev reflexiveHullMap {ℱ 𝒢 : ModX} (f : ℱ ⟶ 𝒢) :
    reflexiveHull ℱ ⟶ reflexiveHull 𝒢 :=
  dualMap (dualMap f)

variable [BraidedCategory X.Modules]

/-- The canonical morphism from a module to its reflexive hull. -/
noncomputable def toReflexiveHull (ℱ : ModX) :
    ℱ ⟶ reflexiveHull ℱ :=
  MonoidalClosed.curry ((β_ ℱᵛ ℱ).hom ≫ (ihom.ev ℱ).app 𝒪X)

/-- Definition 31.12.1 (2): a coherent `\mathcal O_X`-module is reflexive when the canonical map
to its reflexive hull is an isomorphism. -/
abbrev IsReflexive (ℱ : ModX) : Prop :=
  IsIso (toReflexiveHull ℱ)

end

end AlgebraicGeometry.Scheme.Modules
