import stacks_project.Chap15.Lemma_15_60_1
import stacks_project.Chap15.Lemma_15_92_16
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open MvPolynomial
open Opposite
open scoped DerivedTensorChangeOfRings DerivedTensorProduct DerivedTensorWithAlgebra

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "Rxy" => MvPolynomial (Fin 2) k

/-- The quotient ring `A = k[x, y] / (xy)` from Remark `15.60.4`. -/
abbrev Ring : Type _ :=
  Rxy ⧸ principalIdeal ((X (0 : Fin 2) : Rxy) * (X (1 : Fin 2) : Rxy))

local notation "A" => Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
private abbrev single₀ : ModuleCat A ⥤ DModA := ModuleCat.single0Functor

/-- The class of `x` in the quotient ring `A = k[x, y] / (xy)`. -/
abbrev x : Ring k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2) : Rxy)

/-- The object `N = A / (x)` viewed in `D(A)`. -/
abbrev N : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A (A ⧸ principalIdeal (x k)))

/-- The object `N' = A` viewed in `D(A)`. -/
abbrev NPrime : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A A)

end

end Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "R" => MvPolynomial (Fin 2) k
local notation "A" => Remark15604Warning.Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "x" => Remark15604Warning.x k
local notation "N" => Remark15604Warning.N k
local notation "N'" => Remark15604Warning.NPrime k

/- Domain-style sampling for Remark 15.60.4:
- primary domain: change-of-rings derived tensor products in derived categories of modules over a
  quotient of a polynomial ring, together with the chapter's one-variable powered-Koszul stage
  owner for the two-term complex `A ⟶ A`;
- sampled owner declarations of the same kind:
  `ModuleCat.single0Functor`,
  `principalIdeal`,
  `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: `derivedTensorChangeOfRings` owns the two change-of-rings tensor
  objects, `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory` owns the derived
  restriction-of-scalars operation, `ModuleCat.single0Functor` owns the degree-zero derived
  objects, `principalIdeal` owns the one-generator ideals `(xy)` and `(x)`, while the
  source-facing objects of the warning itself are the public abbreviations
  `Remark15604Warning.Ring k`, `Remark15604Warning.x k`, `Remark15604Warning.N k`, and
  `Remark15604Warning.NPrime k`; the canonical stage
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`
  from Lemma `15.92.16` represents the two-term complex `A \xrightarrow{x} A`;
- primitive data: the ring `A = k[x, y] / (xy)`, the element `x ∈ A`, and the degree-zero derived
  objects `N = (A / (x))[0]` and `N' = A[0]`;
- derived API: the canonical degree-zero owner `ModuleCat.single0Functor`, the derived
  restriction-of-scalars images of `N` and `N'`, the two change-of-rings tensor objects, the
  canonical Koszul model
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`,
  the split model `N[1] ⊞ N`, and the comparison/non-isomorphism theorems.

Source/core/bridge triage:
- `source-facing`: the warning counterexample objects `N`, `N'`, their restriction-of-scalars
  images, their two change-of-rings tensor products, and the statement that the resulting objects
  of `D(A)` are not isomorphic;
- `core/canonical`: `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`, the powered Koszul tower
  `K^•[n](f)`, and `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the two comparison theorems identifying the source-facing tensors with the
  canonical two-term Koszul model and the split object. -/

-- Proof sketch: in the warning example `N = A/(x)` and `N' = A`. The remark computes
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) \otimes_R^{\mathbf L}
-- N'` as the two-term complex `A \xrightarrow{x} A`, while
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') \otimes_R^{\mathbf L}
-- N` is computed as `N[1] ⊞ N`.
/-- The change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
is represented by the two-term complex `A \xrightarrow{x} A`, namely the canonical derived
powered-Koszul stage. -/
theorem Remark15604Warning.nTensorNPrime_iso_koszulStage0 :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (op 0)) := sorry

/-- The second change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
is represented by `N[1] ⊞ N`. -/
theorem Remark15604Warning.nPrimeTensorN_iso_shiftBiproduct :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N)
      (N⟦(1 : ℤ)⟧ ⊞ N) := sorry

section

variable [Nontrivial k]

/- Remark 15.60.4 (Warning): for any nontrivial commutative ring `k`, with `R = k[x,y]`,
`A = R/(xy)`, `N = A/(x)`, and `N' = A`, the two change-of-rings derived tensor products
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
and
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
are not isomorphic in `D(A)`.
-/
theorem Remark15604Warning.counterexample :
    ¬ IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N) :=
  sorry

end

end

end CategoryTheory
