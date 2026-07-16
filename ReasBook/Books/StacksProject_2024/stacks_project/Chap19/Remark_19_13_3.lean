import Mathlib
import StacksProject_2024.stacks_project.Chap13.Remark_13_11_4
import StacksProject_2024.stacks_project.Chap19.Theorem_19_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Localization
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Remark 19.13.3:
- primary domain: derived categories of Grothendieck abelian categories, localized at
  quasi-isomorphisms;
- sampled owner declarations:
  `Localization.HasSmallLocalizedHom`,
  `DerivedCategory.Qh`,
  `hasSmallLocalizedHom_of_quasiIso_to_isKInjective`,
  `CochainComplex.exists_functorial_kInjective_resolution`;
- best owner abstraction: smallness is controlled by the localization functor `DerivedCategory.Qh`,
  while the Grothendieck-specific K-injective resolution statement is already owned by Chapter 19;
- primitive data: the Grothendieck-abelian hypothesis on `A`;
- derived API: the homotopy-category presentation of small morphism types in `D(A)`.

Source/core/bridge triage:
- `source-facing`: `derived_hom_small_of_isGrothendieckAbelian`;
- `core/canonical`: `HasSmallLocalizedHom`, `DerivedCategory.Q`, `DerivedCategory.Qh`, and the
  Chapter 13 bridge theorem `hasSmallLocalizedHom_of_quasiIso_to_isKInjective`;
- `bridge/view`: the theorem below transports Chapter 13 smallness from complexes to the
  homotopy-category localization through `quotientCompQhIso`. -/

/- Reuse the Chapter 19 Grothendieck-abelian K-injective resolution theorem directly rather than
restating it with a local wrapper. -/
#check CochainComplex.exists_functorial_kInjective_resolution

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- Remark 19.13.3: in a Grothendieck abelian category, the localization of the homotopy category
at quasi-isomorphisms has `w`-small Hom-types, so morphisms in the derived category are sets. -/
theorem derived_hom_small_of_isGrothendieckAbelian
    (K L : HomotopyCategory A (ComplexShape.up ℤ)) :
    HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K L := by
  letI : HasDerivedCategory.{max u v} A := HasDerivedCategory.standard A
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  rw [Localization.hasSmallLocalizedHom_iff
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh]
  letI : HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K L :=
    by
      obtain ⟨J, -, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution A
      let _ : (J.toFunctor.obj L).IsKInjective := hKinj L
      exact _root_.hasSmallLocalizedHom_of_quasiIso_to_isKInjective K
        (J.ι.app L) (J.quasiIso_app L)
  let h :=
    Localization.small_of_hasSmallLocalizedHom
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Q K L
  exact (small_congr
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app K)
      ((DerivedCategory.quotientCompQhIso A).app L))).2 h

end

end CategoryTheory
