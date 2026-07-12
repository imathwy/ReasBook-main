import StacksProject_2024.Chap20.Lemma_20_26_12
import StacksProject_2024.Chap21.Lemma_21_17_17

open AlgebraicGeometry
open CategoryTheory HomologicalComplex
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "SiteModX" => ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf
local notation "IsTermwiseFlat" =>
  @IsTermwiseFlat _ _ (Opens.grothendieckTopology X) _ X.sheaf _

/- Domain-style sampling for Lemma 20.26.17:
- primary domain: factorization up to homotopy of morphisms of cochain complexes of
  `𝒪_X`-modules through quasi-isomorphisms with K-flat source;
- sampled owner declarations:
  `SheafOfModules.RingedSite.exists_homotopy_factorization_through_kFlat_quasiIso`,
  `SheafOfModules.RingedSite.exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isTermwiseFlat_iff`,
  `Homotopy`, and `QuasiIso`;
- best owner abstraction: the ringed-site theorems from Chapter `21` are the canonical core
  owners, while this file should expose only the opens-site specialization to a ringed space and
  the bridge from the canonical ringed-space owner `IsTermwiseFlat K` to the source wording that
  each term `K.X n` is flat;
- primitive vs derived: primitive data are the intermediate complex `N` and the comparison maps
  `b`, `c`; the homotopy, K-flatness, quasi-isomorphism, and termwise-flatness clauses remain on
  their canonical owners.

Source/core/bridge triage:
- `source-facing`: the ringed-space factorization statement and its flat-terms refinement;
- `core/canonical`: the Chapter `21` ringed-site factorization theorems together with
  `K.IsKFlat`, `IsTermwiseFlat K`, `Homotopy a (b ≫ c)`, and `QuasiIso c`;
- `bridge/view`: specialization from the opens ringed site of `X` to `RingedSpace.Modules X`, and
  the translation between `IsTermwiseFlat` and degreewise flatness via
  `CochainComplex.isTermwiseFlat_iff`. -/

/-- Lemma 20.26.17: if `a : K ⟶ L` is a morphism of cochain complexes of `𝒪_X`-modules on a
ringed space and `K` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism
`c : N ⟶ L` with K-flat source `N`. -/
@[stacks 0G6V]
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex ModX ℤ) (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex ModX ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := by
  let K' : CochainComplex SiteModX ℤ := K
  let L' : CochainComplex SiteModX ℤ := L
  obtain ⟨N, b, c, hHom, hN, hc⟩ :=
    SheafOfModules.RingedSite.exists_homotopy_factorization_through_kFlat_quasiIso
      K' L' a (by simpa [K'] using hK)
  exact ⟨N, b, c, hHom, by simpa using hN, by simpa [L'] using hc⟩

/-- Canonical termwise-flat companion to Lemma 20.26.17: if `K` is K-flat and termwise flat in
the owner sense `IsTermwiseFlat K`, then the intermediate complex `N` can also be chosen
termwise flat. -/
theorem exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex ModX ℤ) (a : K ⟶ L) (hK : K.IsKFlat) (hFlatK : IsTermwiseFlat K) :
    ∃ (N : CochainComplex ModX ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      IsTermwiseFlat N ∧
      QuasiIso c := by
  let K' : CochainComplex SiteModX ℤ := K
  let L' : CochainComplex SiteModX ℤ := L
  obtain ⟨N, b, c, hHom, hN, hFlatN, hc⟩ :=
    SheafOfModules.RingedSite.exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
      K' L' a (by simpa [K'] using hK) (by simpa [K'] using hFlatK)
  exact ⟨N, b, c, hHom, by simpa using hN, by simpa using hFlatN, by simpa [L'] using hc⟩

/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms
as well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (K L : CochainComplex ModX ℤ) (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    ∃ (N : CochainComplex ModX ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      (∀ n : ℤ, SheafOfModules.IsFlat (N.X n)) ∧
      QuasiIso c := by
  obtain ⟨N, b, c, hHom, hN, hFlatN, hc⟩ :=
    exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
      K L a hK ((CochainComplex.isTermwiseFlat_iff K).2 hFlatK)
  exact ⟨N, b, c, hHom, hN, (CochainComplex.isTermwiseFlat_iff N).1 hFlatN, hc⟩

end AlgebraicGeometry.RingedSpace
