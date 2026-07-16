import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import stacks_proof.stacks_project.Chap13.Remark_13_10_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

local instance : CategoryTheory.Limits.HasBinaryBiproducts (CochainComplex (ModuleCat R) ℤ) :=
  cochainComplexHasBinaryBiproducts (ModuleCat R)

/- Domain-style sampling for Lemma 15.58.4:
- primary domain: homological algebra of totalized tensor-product functors on homotopy categories
  of cochain complexes;
- sampled owner API:
  `curriedTensor`,
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the project-level owners for fixed-factor tensoring on homotopy
  categories are the canonical fixed-factor homotopy descents
  `((((curriedTensor (ModuleCat R)).map₂CochainComplex).obj P).mapHomotopyCategory (up ℤ))` and
  `(((((curriedTensor (ModuleCat R)).map₂CochainComplex).flip).obj P).mapHomotopyCategory
    (up ℤ))`,
  and exactness is encoded by `Functor.IsTriangulated`;
- primitive vs derived:
  primitive data are the bilinear tensor bifunctor `curriedTensor (ModuleCat R)` and the fixed
  complex `P`;
  the induced homotopy-category endofunctors and their triangulated structure are derived API
  already provided upstream in Chapter 13 through `Functor.mapHomotopyCategory`, so this file
  should specialize that owner rather than rebuild a parallel public quotient-lift theorem;
- source/core/bridge triage:
  the textbook lemma is source-facing exactness for the two tensor endofunctors on `K(R)`,
  the core/canonical owners are the two fixed-factor tensor homotopy descents above, and the
  declarations below are the thin Chapter 15 specialization recall;
- layer: `bridge/view`, since this file only records the Chapter 15 specialization of the
  Chapter 13 owner instances and introduces no new owner object. -/
variable (P : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.58.4: for a complex `P^\bullet` of `R`-modules, the endofunctor of `K(R)` given by
`L^\bullet ↦ \mathrm{Tot}(P^\bullet ⊗_R L^\bullet)` is exact. This is the specialized canonical
instance on the fixed-left-factor homotopy descent from Remark `13.10.9`. -/
#check
  (inferInstance :
    ((((curriedTensor (ModuleCat R)).map₂CochainComplex).obj P).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

/- The symmetric fixed-right-factor form in Lemma `15.58.4` is likewise the specialized
canonical `Functor.IsTriangulated` instance on the corresponding homotopy descent. -/
#check
  (inferInstance :
    (((((curriedTensor (ModuleCat R)).map₂CochainComplex).flip).obj P).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

end
