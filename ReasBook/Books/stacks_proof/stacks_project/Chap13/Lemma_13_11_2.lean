import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Lemma_13_6_9
import stacks_proof.stacks_project.Chap13.Lemma_13_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe w v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 13.11.2:
- primary domain: Verdier localization of triangulated categories, specialized to the homotopy
  category of cochain complexes and the homological kernel of `H^0`;
- sampled owner declarations:
  `HomotopyCategory.subcategoryAcyclic`,
  `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`,
  `Functor.homologicalKernel`,
  `CategoryTheory.kernel_triangulatedLocalization_eq_retractClosure`,
  `ObjectProperty.retractClosure_eq_self`,
  `Localization.equivalenceFromModel`,
  `Localization.compEquivalenceFromModelInverseIso`,
  `Localization.qCompEquivalenceFromModelFunctorIso`;
- `source-facing`: the bridge statement identifying the kernel of `DerivedCategory.Qh` with the
  acyclic subcategory;
- `core/canonical`: the homological-kernel owner `HomotopyCategory.subcategoryAcyclic A` and the
  retract-closure fixed-point API for its Verdier quotient kernel, together with the localization
  equivalence owner attached to `DerivedCategory.Qh.IsLocalization`;
- `bridge/view`: transport the canonical kernel statement from the constructed localization
  `(subcategoryAcyclic A).trW.Q` to the chosen derived-category localization `DerivedCategory.Qh`
  using `Localization.equivalenceFromModel`.

Primitive data are only the acyclic object property and the chosen localization functor.
Retract-stability is derived API from the generic homological-kernel owner and should not remain a
parallel local instance.
-/

/- Lemma 13.11.2: in the homotopy category `K(\mathcal A)` of cochain complexes in an abelian
category `\mathcal A`, the saturated multiplicative system attached to the strictly full
triangulated subcategory of acyclic complexes is exactly the class of quasi-isomorphisms. -/
recall HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W

/- Companion recall: the acyclic complexes form a triangulated subcategory of
`K(\mathcal A)`. -/
#check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsTriangulated)

/- Companion recall: the acyclic complexes form a strictly full subcategory of
`K(\mathcal A)`. -/
#check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsClosedUnderIsomorphisms)

/- Companion recall: the acyclic complexes are stable under retracts/direct summands. This is the
owner-facing retract-stability instance for `HomotopyCategory.subcategoryAcyclic A`, inherited
from the generic homological-kernel owner. -/
#check (show ObjectProperty.IsStableUnderRetracts (HomotopyCategory.subcategoryAcyclic A) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

section

variable [HasDerivedCategory.{w} A]

local notation "Ac" => HomotopyCategory.subcategoryAcyclic A
local notation "Q" =>
  (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)

-- Proof sketch: identify the kernel of the canonical Verdier quotient `Ac.trW.Q` with the
-- retract closure of `Ac`, collapse that retract closure using the owner theorem
-- `retractClosure_eq_self`, and transport the resulting kernel equality to
-- `DerivedCategory.Qh` through the canonical localization equivalence
-- `Localization.equivalenceFromModel`.
/-- The kernel of the localization functor from the homotopy category to the derived category is
the subcategory of acyclic complexes. -/
theorem subcategoryAcyclic_kernel_Qh :
    Functor.kernel Q = Ac := by
  letI : ObjectProperty.IsStableUnderRetracts Ac := by
    dsimp [HomotopyCategory.subcategoryAcyclic]
    infer_instance
  let W := (HomotopyCategory.subcategoryAcyclic A).trW
  let E := Localization.equivalenceFromModel Q W
  let η := Localization.qCompEquivalenceFromModelFunctorIso Q W
  let ε := Localization.compEquivalenceFromModelInverseIso Q W
  have hkernel :
      Functor.kernel W.Q = Ac := by
    rw [kernel_triangulatedLocalization_eq_retractClosure Ac]
    simpa using (HomotopyCategory.subcategoryAcyclic A).retractClosure_eq_self
  ext X
  constructor
  · intro hX
    have hX' : IsZero (E.inverse.obj (DerivedCategory.Qh.obj X)) :=
      E.inverse.map_isZero hX
    have hX'' : IsZero (W.Q.obj X) :=
      (ε.app X).isZero_iff.1 hX'
    have hker : Functor.kernel W.Q X := hX''
    rw [hkernel] at hker
    exact hker
  · intro hX
    have hker : Functor.kernel W.Q X := by
      rw [hkernel]
      exact hX
    have hX' : IsZero (E.functor.obj (W.Q.obj X)) :=
      E.functor.map_isZero hker
    exact (η.app X).isZero_iff.1 hX'

/- Companion recall: the degree-zero homology functor on the homotopy category factors through the
localization `Q : K(\mathcal A) ⥤ D(\mathcal A)`. -/
#check (DerivedCategory.homologyFunctorFactorsh A 0)

end
