import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap15.Lemma_15_84_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 15.84.4:
- primary domain: relative perfectness in the derived category `D(A)` and its description by
  bounded cochain representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `CochainComplex.IsTermwiseFlat`,
  `Compᵇ((ModuleCat A))`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem belongs on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the representative-side condition should live on the
  bounded owner `P : Compᵇ((ModuleCat A))` through its ambient complex `P.obj`, together with the
  canonical restriction-of-scalars functor
  `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` and the genuinely
  extra termwise `Module.FinitePresentation A` hypothesis;
- primitive vs. derived:
  primitive data are the bounded representative `P : Compᵇ((ModuleCat A))`, canonical termwise
  `R`-flatness of the restricted ambient complex
  `((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj P.obj`,
  termwise finite presentation over `A`, and the isomorphism class of the represented derived
  object `DerivedCategory.Q.obj P.obj`;
  derived API is the iff-criterion identifying `DerivedCategory.IsPerfectOver R` with the
  existence of such a representative;
- source/core/bridge triage:
  `source-facing`: the representative criterion of Lemma 15.84.4;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `Compᵇ((ModuleCat A))`, and
    `CategoryTheory.IsIsomorphic`, together with the owner predicate
    `CochainComplex.IsTermwiseFlat`;
  `bridge/view`: the ambient restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` acting on the
    underlying ambient complex `P.obj`.
-/

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "BoundedCpxA" => Compᵇ((ModuleCat A))
local notation "DModA" => DerivedCategory (ModuleCat A)

-- Proof sketch: for `(→)`, represent `K` by a bounded-above finite-free complex using
-- pseudo-coherence, then truncate it using the finite tor-amplitude bounds and Lemma `15.67.2`
-- to obtain a bounded representative with termwise `R`-flat finitely presented terms. For `(←)`,
-- each term of a bounded representative is pseudo-coherent over `A` and has finite tor dimension
-- over `R`, hence is perfect over `R`; closure of `R`-perfect objects under shifts and cones from
-- Lemma `15.84.2` gives perfection of the whole complex.
variable (R) in
/-- Lemma 15.84.4: for a flat ring map `R → A` of finite presentation, an object `K` of `D(A)` is
perfect over `R` if and only if it is isomorphic in `D(A)` to a bounded cochain complex of
`A`-modules with `R`-flat finitely presented terms. -/
theorem isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
    (K : DModA) :
    DerivedCategory.IsPerfectOver R K ↔
      ∃ P : BoundedCpxA,
        CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
            P.obj) ∧
          (∀ i : ℤ, Module.FinitePresentation A (P.obj.X i)) ∧
          IsIsomorphic K (DerivedCategory.Q.obj P.obj) := sorry

end

end
end CategoryTheory
