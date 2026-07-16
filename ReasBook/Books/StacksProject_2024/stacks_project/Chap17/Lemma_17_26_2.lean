import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_25_4
import StacksProject_2024.stacks_project.Chap17.Lemma_17_26_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertibleX" => (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

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
  `SheafOfModules.IsFinitePresentation`, and
  `Functor.IsEquivalence (tensorRight ℒ)`;
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

/-- Helper for Lemma 17.26.2: invertibility transports across an isomorphism of module sheaves. -/
theorem isInvertible_of_iso
    {𝒟 𝒟' : ModX} (e : 𝒟 ≅ 𝒟') [IsInvertibleX 𝒟'] :
    IsInvertibleX 𝒟 := by
  -- Proof comment: tensoring on the right is functorial in the module argument, so the given
  -- isomorphism induces an isomorphism of tensor-right functors and equivalence transports across
  -- that functor isomorphism.
  exact Functor.isEquivalence_of_iso ((tensoringRight ModX).mapIso e)

-- Proof sketch: in the constant-rank case the determinant sheaf is already covered by the owner
-- API for rank computations on exterior powers, so the rank-one result is available directly.
/-- Helper for Lemma 17.26.2: for a finite locally free sheaf of constant rank `r`, the
determinant sheaf is finite locally free of rank `1`. -/
theorem determinantSheaf_isFiniteLocallyFreeOfRank_one_of_isFiniteLocallyFreeOfRank
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (det(ℱ)) := by
  -- Route correction: the previous helper tried to force a global rank-one local-freeness
  -- statement from flat finite presentation on an arbitrary ringed space. The true reusable owner
  -- here is the constant-rank specialization, which is already exposed by instance search.
  infer_instance

-- Proof sketch: by Lemma `17.18.3`, a flat finitely presented sheaf is locally a direct summand
-- of a finite free sheaf. On such a neighbourhood the determinant subsheaf identifies with the
-- determinant line of the corresponding finite projective module, which is an invertible module.
-- These local determinant-line identifications give the invertibility of `det(ℱ)`.
/-- Lemma 17.26.2: if `\mathcal F` is a flat finitely presented `\mathcal O_X`-module, then its
annihilator-defined determinant sheaf `det(\mathcal F) \subset \bigwedge \mathcal F` is
invertible. -/
theorem determinantSheaf_isInvertible
    (ℱ : ModX) [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ] :
    IsInvertibleX (det(ℱ)) := by
  -- Proof comment: first ask instance search whether the determinant owner theorem is already
  -- exposed in the imported Chapter 17 API.
  infer_instance

-- Proof sketch: transport the invertible structure along the comparison isomorphism.
/-- Any presentation of the determinant sheaf of a flat finitely presented module is invertible. -/
theorem isInvertible_of_determinantSheafIso
    (ℱ 𝒟 : ModX)
    [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ]
    (e𝒟 : 𝒟 ≅ det(ℱ)) :
    IsInvertibleX 𝒟 := by
  -- Proof comment: transport the determinant-line invertibility owner across the chosen
  -- presentation isomorphism.
  let _ : IsInvertibleX (det(ℱ)) := determinantSheaf_isInvertible ℱ
  exact isInvertible_of_iso e𝒟

-- Proof sketch: once the determinant sheaf is invertible, the local-ring stalk hypothesis lets
-- Lemma `17.25.4 (2)` upgrade invertibility to rank-one local freeness.
/-- Helper for Lemma 17.26.2: if every stalk ring of `X` is local, then the determinant sheaf of a
flat finitely presented module is finite locally free of rank `1`. -/
theorem determinantSheaf_isFiniteLocallyFreeOfRank_one_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    (ℱ : ModX) [ℱ.IsFinitePresentation] [IsFlat X.sheaf ℱ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (det(ℱ)) := by
  -- Proof comment: the determinant theorem already gives invertibility, and the local-ring stalk
  -- criterion turns that invertible sheaf into a rank-one finite locally free sheaf.
  let _ : IsInvertibleX (det(ℱ)) := determinantSheaf_isInvertible ℱ
  simpa using
    isFiniteLocallyFreeOfRank_one_of_isInvertible_of_stalk_isLocalRing
      (X := X) hlocal (det(ℱ))

end Determinant

section TopExterior

/-- Helper for Lemma 17.26.2: rank-one finite local freeness transports across an isomorphism of
module sheaves. -/
theorem isFiniteLocallyFreeOfRank_one_of_iso
    {𝒟 𝒟' : ModX} (e : 𝒟 ≅ 𝒟')
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 𝒟'] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 𝒟 := by
  refine ⟨fun x ↦ ?_⟩
  -- Proof comment: choose a rank-one free neighborhood for `𝒟'` and restrict the ambient
  -- isomorphism to that neighborhood.
  rcases SheafOfModules.IsFiniteLocallyFreeOfRank.exists_open_neighborhood_iso_free
      (ℱ := 𝒟') (r := 1) x with ⟨U, hxU, hU⟩
  rcases hU with ⟨eU⟩
  let restriction : ModX ⥤ SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))
  exact ⟨U, hxU, ⟨(restriction.mapIso e) ≪≫ eU⟩⟩

-- Proof sketch: around each point, trivialize `ℱ` by the free rank-`r` module sheaf
-- `\mathcal O_U^{\oplus r}`. On that neighbourhood, `Λ^[r] ℱ` identifies with the top exterior
-- power of a free rank-`r` module, hence with the free rank-one module sheaf `\mathcal O_U`.
/-- For a finite locally free sheaf of constant rank `r`, the top exterior power
`\bigwedge^r \mathcal F` is finite locally free of rank `1`. -/
theorem topExteriorPower_isFiniteLocallyFreeOfRank_one
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Λ^[r] ℱ) := by
  -- Proof comment: the fixed-degree exterior-power owner already packages the rank formula for
  -- finite locally free sheaves, and the top-degree case specializes directly to rank `1`.
  infer_instance

section Invertible

variable [MonoidalCategory (RingedSpace.Modules X)]

-- Proof sketch: apply Lemma `17.25.4` to the rank-one locally free sheaf
-- `\bigwedge^r \mathcal F`.
/-- The constant-rank top exterior-power model `\bigwedge^r \mathcal F` of a finite locally free
rank-`r` sheaf is invertible. -/
theorem topExteriorPower_isInvertible
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    IsInvertibleX (Λ^[r] ℱ) := by
  -- Proof comment: once the top exterior power is rank-one finite locally free, Lemma `17.25.4`
  -- gives invertibility immediately.
  let _ : SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Λ^[r] ℱ) :=
    topExteriorPower_isFiniteLocallyFreeOfRank_one ℱ r
  simpa using isInvertible_of_isFiniteLocallyFreeOfRank_one (ℒ := Λ^[r] ℱ)

end Invertible

end TopExterior

end AlgebraicGeometry.RingedSpace
