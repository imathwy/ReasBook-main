import Mathlib
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Remark_17_13_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

open RingedSpace

-- Semantic recall: the source sheaf of sections supported on a closed subset is the kernel of the
-- restriction map to the open complement, and the affine-local ideal-power torsion statement is
-- the source-facing companion API.

/-- The open complement of a closed subset of a scheme. -/
abbrev openComplement (Z : TopologicalSpace.Closeds X) : X.Opens :=
  RingedSpace.ClosedSubsetSectionsWithSupport.openComplement Z.2

open RingedSpace.ClosedSubsetSectionsWithSupport

/-- A point lies in the open complement exactly when it does not lie in the closed subset. -/
@[simp] theorem mem_openComplement_iff (Z : TopologicalSpace.Closeds X) (x : X) :
    x ∈ openComplement Z ↔ x ∉ (Z : Set X) :=
  Iff.rfl

/-- The module sheaf of sections of `ℱ` whose restriction to the open complement of `Z` vanishes.
-/
abbrev sectionsWithSupportIn (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) : X.Modules :=
  ((subsheaf Z.2 ℱ : Subobject ℱ) : X.Modules)

/-- The canonical inclusion of sections supported in `Z` into the ambient module sheaf `ℱ`. -/
abbrev sectionsWithSupportInι (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) :
    sectionsWithSupportIn Z ℱ ⟶ ℱ :=
  (subsheaf Z.2 ℱ).arrow

/-- On any open `U ⊆ X`, the image of the inclusion of sections supported in `Z` is exactly the
sections whose support is contained in `Z ∩ U`. -/
theorem range_sectionsWithSupportInι_app_eq
    (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) (U : X.Opens) :
    Set.range ((sectionsWithSupportInι Z ℱ).app U) =
      { s : Γ(ℱ, U) | moduleSectionSupport s ⊆ { x : U | x.1 ∈ (Z : Set X) } } := by
  simpa [sectionsWithSupportInι] using subsheaf_app_range (X := X) (Z := (Z : Set X)) Z.2 ℱ U

/-- A section on `U` comes from the sheaf of sections supported in `Z` exactly when its support is
contained in `Z ∩ U`. -/
theorem mem_range_sectionsWithSupportInι_app_iff
    (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) (U : X.Opens) (s : Γ(ℱ, U)) :
    s ∈ Set.range ((sectionsWithSupportInι Z ℱ).app U) ↔
      moduleSectionSupport s ⊆ { x : U | x.1 ∈ (Z : Set X) } := by
  simpa [sectionsWithSupportInι] using
    subsheaf_app_iff (X := X) (Z := (Z : Set X)) Z.2 ℱ U s

/-- The support of the sheaf of sections of `ℱ` supported in `Z` is contained in `Z`. -/
theorem moduleSupport_sectionsWithSupportIn_subset
    (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) :
    moduleSupport (sectionsWithSupportIn Z ℱ) ⊆ (Z : Set X) := by
  simpa [sectionsWithSupportIn] using
    subsheaf_support_subset (X := X) (Z := (Z : Set X)) Z.2 ℱ

/-- Lemma 28.24.5 (1): if the open complement of `Z` is retrocompact, then every affine open
`U ⊆ X` admits a finitely generated ideal of `Γ(X, U)` cutting out `Z ∩ U`. -/
theorem exists_fg_ideal_of_isRetrocompact_openComplement
    (Z : TopologicalSpace.Closeds X)
    (hretro : IsRetrocompact (openComplement Z : Set X))
    (U : X.affineOpens) :
    ∃ I : Ideal Γ(X, U.1), I.FG ∧
      ((Z : Set X) ∩ (U.1 : Set X) = X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)) := sorry

/-- Lemma 28.24.5 (2): on an affine open cut out by `I`, the sections with support in `Z` are
exactly the sections annihilated by some power of `I`. -/
theorem range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion
    (Z : TopologicalSpace.Closeds X)
    (ℱ : X.Modules)
    (U : X.affineOpens)
    (I : Ideal Γ(X, U.1))
    (hI : (Z : Set X) ∩ (U.1 : Set X) = X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)) :
    Set.range ((sectionsWithSupportInι Z ℱ).app U.1) =
      {x : Γ(ℱ, U.1) |
        ∃ n : ℕ, ∀ a : Γ(X, U.1), a ∈ (I ^ n : Ideal Γ(X, U.1)) → a • x = 0} := sorry

/-- Lemma 28.24.5 (3): if the open complement of `Z` is retrocompact, then the sheaf of sections
of `ℱ` supported on `Z` is quasi-coherent. -/
theorem sectionsWithSupportIn_isQuasicoherent
    (Z : TopologicalSpace.Closeds X)
    (hretro : IsRetrocompact (openComplement Z : Set X))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (sectionsWithSupportIn Z ℱ).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
