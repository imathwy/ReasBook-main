import StacksProject_2024.Chap15.Lemma_15_59_5
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/- Domain-style sampling for Lemma 21.17.6:
- primary domain: K-flat cochain complexes of `𝒪`-modules on a ringed site in distinguished
  triangles in the homotopy category `K(𝒪)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the canonical owner remains the Chapter 15 distinguished-triangle
  two-out-of-three theorems for `CochainComplex.IsKFlat`, while this file is the ringed-site
  specialization to `ringedSiteModuleCategory J 𝒪`;
- primitive vs derived: primitive data are a distinguished triangle in `KHom` and K-flatness
  of two of its vertices; the three closure implications are derived API from the generic owner
  theorems, specialized here to the ringed-site module category.

Source/core/bridge triage:
- `source-facing`: the K-flat two-out-of-three statements for distinguished triangles of
  cochain complexes of `𝒪`-modules on a ringed site `(C, 𝒪)`;
- `core/canonical`: `CochainComplex.IsKFlat` together with
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file's specialization of those owner theorems from an arbitrary monoidal
  category to `ringedSiteModuleCategory J 𝒪`. -/

-- Proof sketch: Definition `21.17.2` identifies K-flatness on complexes of `𝒪`-modules with the
-- Chapter 15 owner predicate `CochainComplex.IsKFlat`. Lemma `21.17.1` supplies the tensor
-- functoriality needed in that owner, so the generic two-out-of-three theorems from
-- `Lemma_15_59_5` apply unchanged after specializing the ambient category to
-- `ringedSiteModuleCategory J 𝒪`.
/-- Lemma 21.17.6 (1): if `T` is a distinguished triangle in `K(𝒪)` and the first two terms are
K-flat, then the third term is K-flat. This is the ringed-site specialization of
`CochainComplex.isKFlat_obj₃_of_distinguished_triangle`. -/
@[stacks 07A3]
theorem isKFlat_obj₃_of_distinguished_triangle
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (h₁ : T.obj₁.IsKFlat) (h₂ : T.obj₂.IsKFlat) :
    T.obj₃.IsKFlat := by
  exact CochainComplex.isKFlat_obj₃_of_distinguished_triangle T hT h₁ h₂

/-- Lemma 21.17.6 (2): if `T` is a distinguished triangle in `K(𝒪)` and the first and third terms
are K-flat, then the second term is K-flat. This is the ringed-site specialization of
`CochainComplex.isKFlat_obj₂_of_distinguished_triangle`. -/
@[stacks 07A3]
theorem isKFlat_obj₂_of_distinguished_triangle
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (h₁ : T.obj₁.IsKFlat) (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := by
  exact CochainComplex.isKFlat_obj₂_of_distinguished_triangle T hT h₁ h₃

/-- Lemma 21.17.6 (3): if `T` is a distinguished triangle in `K(𝒪)` and the second and third terms
are K-flat, then the first term is K-flat. This is the ringed-site specialization of
`CochainComplex.isKFlat_obj₁_of_distinguished_triangle`. -/
@[stacks 07A3]
theorem isKFlat_obj₁_of_distinguished_triangle
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)))
    (h₂ : T.obj₂.IsKFlat) (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := by
  exact CochainComplex.isKFlat_obj₁_of_distinguished_triangle T hT h₂ h₃

end

end SheafOfModules.RingedSite
