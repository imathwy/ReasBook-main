import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.Definition_17_20_3
import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap17.Lemma_17_18_3
import StacksProject_2024.Chap17.Lemma_17_26_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.26.2:
- primary domain: determinant subsheaves of flat finitely presented module sheaves on a ringed
  space and their invertibility;
- inspected owner declarations:
  `determinantSheaf`,
  `Module.det`,
  `IsFlat`,
  `SheafOfModules.IsFinitePresentation`,
  `isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat`,
  `isInvertible_of_isFiniteLocallyFreeOfRank_one`;
- best owner abstraction: the source-facing owner is the determinant subsheaf `det(ℱ)` from
  `Lemma_17_26_1`, defined intrinsically inside `Λ(ℱ)`; flatness and finite presentation are the
  primitive hypotheses, while the constant-rank top exterior-power results are bridge API;
- primitive data: a module sheaf `ℱ : ModX` together with `ℱ.IsFinitePresentation` and
  `IsFlat X.sheaf ℱ`;
- derived API: invertibility of `det(ℱ)`, transport of invertibility along determinant
  presentations, and the finite-locally-free specialization to `Λ^[r] ℱ`.

Source/core/bridge triage:
- `source-facing`: the invertibility of the determinant sheaf of a flat finitely presented
  `\mathcal O_X`-module;
- `core/canonical`: `determinantSheaf`, `IsFlat`,
  `SheafOfModules.IsFinitePresentation`, and `IsInvertible`;
- `bridge/view`: the constant-rank top exterior model `Λ^[r] ℱ`, its rank-one specialization, and
  transport along an isomorphism `𝒟 ≅ det(ℱ)`.

The determinant owner `det(ℱ)` is defined using the closed monoidal structure from
`Lemma_17_26_1`, so the determinant-sheaf theorems below genuinely live in that stronger ambient
context. Their public content stays at the invertible-owner layer on an arbitrary ringed space.
By contrast, the top-exterior companions are separate constant-rank bridge results stated over the
weaker canonical context from `Definition_17_14_1` and `Lemma_17_25_4`. -/

section Determinant

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

-- Proof sketch: by Lemma `17.18.3`, a flat finitely presented sheaf is locally a direct summand
-- of a finite free sheaf. On such a neighbourhood the determinant subsheaf identifies with the
-- determinant line of the corresponding finite projective module, which is an invertible module.
-- These local determinant-line identifications give the invertibility of `det(ℱ)`.
/-- Lemma 17.26.2: if `\mathcal F` is a flat finitely presented `\mathcal O_X`-module, then its
annihilator-defined determinant sheaf `det(\mathcal F) \subset \bigwedge \mathcal F` is
invertible. -/
theorem determinantSheaf_isInvertible
    (ℱ : ModX) [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ] :
    IsInvertible (det(ℱ)) := by
  sorry

-- Proof sketch: transport the invertible structure along the comparison isomorphism.
/-- Any presentation of the determinant sheaf of a flat finitely presented module is invertible. -/
theorem isInvertible_of_determinantSheafIso
    (ℱ 𝒟 : ModX)
    [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ]
    (e𝒟 : 𝒟 ≅ det(ℱ)) :
    IsInvertible 𝒟 := by
  sorry

end Determinant

section TopExterior

-- Proof sketch: around each point, trivialize `ℱ` by the free rank-`r` module sheaf
-- `\mathcal O_U^{\oplus r}`. On that neighbourhood, `Λ^[r] ℱ` identifies with the top exterior
-- power of a free rank-`r` module, hence with the free rank-one module sheaf `\mathcal O_U`.
/-- For a finite locally free sheaf of constant rank `r`, the top exterior power
`\bigwedge^r \mathcal F` is finite locally free of rank `1`. -/
theorem topExteriorPower_isFiniteLocallyFreeOfRank_one
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Λ^[r] ℱ) := by
  sorry

section Invertible

variable [MonoidalCategory (RingedSpace.Modules X)]

-- Proof sketch: apply Lemma `17.25.4` to the rank-one locally free sheaf
-- `\bigwedge^r \mathcal F`.
/-- The constant-rank top exterior-power model `\bigwedge^r \mathcal F` of a finite locally free
rank-`r` sheaf is invertible. -/
theorem topExteriorPower_isInvertible
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    IsInvertible (Λ^[r] ℱ) := by
  sorry

end Invertible

end TopExterior

end AlgebraicGeometry.RingedSpace
