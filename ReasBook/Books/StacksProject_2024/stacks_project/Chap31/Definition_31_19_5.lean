import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.AlgebraSheafConstructions
import StacksProject_2024.Chap17.Definition_17_31_6
import StacksProject_2024.Chap29.Lemma_29_31_3
import StacksProject_2024.Chap31.Definition_31_19_1
import StacksProject_2024.Chap31.Lemma_31_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopCat.Sheaf
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Source/core/bridge triage for Definition 31.19.5:
-- - `source-facing`: the normal cone `C_{Z/X}` and normal bundle `N_{Z/X}` of an immersion
--   `i : Z ⟶ X`, each viewed as a scheme over `Z`;
-- - `core/canonical`: the Chapter 31 conormal-algebra owner `Scheme.ConormalAlgebra i`, the
--   conormal sheaf owner `immersionConormalSheaf i`, and the symmetric-algebra sheaf owner
--   `RingedSpace.moduleSymmetricAlgebra`;
-- - `bridge/view`: affine-chart section-ring descriptions of the relative-`Spec_Z` constructions.
--
-- The current project still lacks a single reusable relative-`Spec_Z` constructor for these
-- quasi-coherent algebra sheaves. To preserve the source-facing scheme owners, this file therefore
-- records `C_{Z/X}` and `N_{Z/X}` as schemes over `Z` equipped with the affine-local
-- relative-`Spec_Z` section-ring data that characterizes the source constructions.

section

variable {X Z : Scheme.{u}}

/-- Bridge owner for Definition 31.19.5 (1): the conormal algebra whose relative `Spec_Z`
realization is the normal cone `C_{Z/X}`. -/
abbrev normalConeConormalAlgebra (i : Z ⟶ X) [IsImmersion i] :=
  Scheme.ConormalAlgebra i

/-- Companion expansion for `normalConeConormalAlgebra`. -/
theorem normalConeConormalAlgebra_def (i : Z ⟶ X) [IsImmersion i] :
    normalConeConormalAlgebra i = Scheme.ConormalAlgebra i :=
  rfl

/-- Definition 31.19.5 (1): for an immersion `i : Z ⟶ X`, the normal cone `C_{Z/X}` is a scheme
over `Z` whose affine charts are the relative spectra of the affine conormal algebras
`⊕_{n ≥ 0} I^n / I^(n + 1)`. -/
structure NormalCone (i : Z ⟶ X) [IsImmersion i] extends Over Z where
  /-- On an affine chart `U ⊆ X`, the inverse image of `U ∩ Z` in `C_{Z/X}` has section ring the
  associated graded algebra of the kernel ideal cutting out `Z ∩ U`. -/
  affineChart (U : X.affineOpens) :
    Γ(left, (TopologicalSpace.Opens.map hom.base).obj (i ⁻¹ᵁ (U : X.Opens))) ≃+*
      immersionAffineConormalAlgebra i (U : X.Opens)

namespace NormalCone

/-- The underlying scheme of the normal cone. -/
abbrev scheme {i : Z ⟶ X} [IsImmersion i] (C : NormalCone i) : Scheme.{u} :=
  C.left

/-- The structural morphism `C_{Z/X} ⟶ Z`. -/
abbrev π {i : Z ⟶ X} [IsImmersion i] (C : NormalCone i) : C.scheme ⟶ Z :=
  C.hom

/-- The affine-chart section ring of the normal cone over an affine open of `X`. -/
abbrev affineChartRing {i : Z ⟶ X} [IsImmersion i] (_ : NormalCone i) (U : X.affineOpens) :
    Type u :=
  immersionAffineConormalAlgebra i (U : X.Opens)

/-- Unfolding the defining affine chart of the normal cone. -/
theorem affineChart_def {i : Z ⟶ X} [IsImmersion i] (C : NormalCone i) (U : X.affineOpens) :
    C.affineChart U =
      (C.affineChart U : Γ(C.scheme, (TopologicalSpace.Opens.map C.π.base).obj
        (i ⁻¹ᵁ (U : X.Opens))) ≃+*
        immersionAffineConormalAlgebra i (U : X.Opens)) :=
  rfl

end NormalCone

end

section

variable {X Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- Bridge owner for Definition 31.19.5 (2): the symmetric algebra sheaf whose relative `Spec_Z`
realization is the normal bundle `N_{Z/X}`. -/
abbrev normalBundleSymmetricAlgebraSheaf (i : Z ⟶ X) [IsImmersion i] : Z.Modules :=
  RingedSpace.moduleSymmetricAlgebra (immersionConormalSheaf i)

/-- Companion expansion for `normalBundleSymmetricAlgebraSheaf`. -/
theorem normalBundleSymmetricAlgebraSheaf_def (i : Z ⟶ X) [IsImmersion i] :
    normalBundleSymmetricAlgebraSheaf i =
      RingedSpace.moduleSymmetricAlgebra (immersionConormalSheaf i) :=
  rfl

/-- The affine symmetric algebra describing the normal bundle over an affine chart of `X`. -/
abbrev normalBundleAffineAlgebra (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens) : Type u :=
  SymmetricAlgebra
    (Γ(Z, i ⁻¹ᵁ (U : X.Opens)))
    (Γ(immersionConormalSheaf i, i ⁻¹ᵁ (U : X.Opens)))

/-- Definition 31.19.5 (2): the normal bundle `N_{Z/X}` is a scheme over `Z` whose affine charts
are the relative spectra of the symmetric algebras of the conormal sheaf. -/
structure NormalBundle (i : Z ⟶ X) [IsImmersion i] extends Over Z where
  /-- On an affine chart `U ⊆ X`, the inverse image of `U ∩ Z` in `N_{Z/X}` has section ring the
  symmetric algebra of the conormal module on `U ∩ Z`. -/
  affineChart (U : X.affineOpens) :
    Γ(left, (TopologicalSpace.Opens.map hom.base).obj (i ⁻¹ᵁ (U : X.Opens))) ≃+*
      normalBundleAffineAlgebra i U

namespace NormalBundle

/-- The underlying scheme of the normal bundle. -/
abbrev scheme {i : Z ⟶ X} [IsImmersion i] (N : NormalBundle i) : Scheme.{u} :=
  N.left

/-- The structural morphism `N_{Z/X} ⟶ Z`. -/
abbrev π {i : Z ⟶ X} [IsImmersion i] (N : NormalBundle i) : N.scheme ⟶ Z :=
  N.hom

/-- Unfolding the defining affine chart of the normal bundle. -/
theorem affineChart_def {i : Z ⟶ X} [IsImmersion i] (N : NormalBundle i) (U : X.affineOpens) :
    N.affineChart U =
      (N.affineChart U : Γ(N.scheme, (TopologicalSpace.Opens.map N.π.base).obj
        (i ⁻¹ᵁ (U : X.Opens))) ≃+*
        normalBundleAffineAlgebra i U) :=
  rfl

end NormalBundle

/- The defining bridge for the normal bundle is built from the canonical conormal-sheaf owner
`immersionConormalSheaf`; the lower-level `NL[i]` identification remains available through
`immersionConormalSheaf_def`, while `normalBundleSymmetricAlgebraSheaf` records the underlying
symmetric-algebra sheaf. -/

end

end AlgebraicGeometry
