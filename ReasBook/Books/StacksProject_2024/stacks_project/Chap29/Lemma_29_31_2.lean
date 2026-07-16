import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_3

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Ideal.Cotangent` and
-- `AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`, while local project inspection
-- verified `immersionConormalSheaf` and `RingedSpace.closedImmersionIdealSheaf` as the relevant
-- scheme-side owners. The source is therefore recorded by the closed-immersion local model for
-- the conormal sheaf together with its affine quotient-chart sections.

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

open RingedSpace

local notation "𝓘" => closedImmersionIdealSheaf i.toShHom

/-- Lemma 29.31.2 (1): if an immersion is viewed on an open subscheme where it becomes a closed
immersion `i : Z ⟶ X` with ideal sheaf `\mathcal I`, then its conormal sheaf is canonically the
pullback `i^* \mathcal I`. This is the closed-immersion local form of the source statement
`\mathcal C_{Z / X} = i^* \mathcal I`. -/
theorem closedImmersion_conormalSheaf_iso_pullbackIdeal :
    ((Scheme.Modules.pullback i).obj 𝓘) ≅ immersionConormalSheaf i := sorry

end

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable [HasWeakSheafify
  (Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))) (Type u)]
variable [HasWeakSheafify
  (Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))).HasSheafCompose
  (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify
  (Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf
    (Opens.grothendieckTopology ↥(Spec (CommRingCat.of (R ⧸ I)))) CommRingCat.{u})]

/-- Lemma 29.31.2 (2): on the affine quotient chart cut out by an ideal `I ⊆ R`, the global
sections of the conormal sheaf of the canonical closed immersion `Spec(R / I) ⟶ Spec(R)` are
canonically identified with `I / I^2`, formalized by `Ideal.Cotangent I`. -/
def specTop_conormalSheaf_equiv_idealCotangent :
    Γ(immersionConormalSheaf
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))), ⊤) ≃
      I.Cotangent := by
  sorry

end

end AlgebraicGeometry
