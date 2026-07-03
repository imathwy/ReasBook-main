import Mathlib
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe uA vA uB vB

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization
open CategoryTheory.Functor (kernel)
open CategoryTheory.Limits
open CategoryTheory.Localization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

noncomputable section

local notation "Q" => P.isoModSerre.Q

/- Domain-style sampling for Lemma 12.10.6:
- primary domain: LinearRepresentations_Serre_1977 quotients of abelian categories and exact functors out of them;
- sampled canonical declarations:
  `ObjectProperty.SerreClassLocalization.isZero_obj_iff`,
  `ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff`,
  `ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft`,
  `Localization.essSurj`;
- owner abstraction: the localization functor `Q`, the exact-functor whiskering owner
  `whiskeringLeft Q P B`, together with the canonical localization interface;
- primitive data: the LinearRepresentations_Serre_1977 class `P`, the exact functor `G`, and the kernel-containment witness
  `P ≤ G.obj.kernel`;
- derived API in this file: exactness of `Q`, identification of its kernel, the source-facing
  essential surjectivity of `Q`, and the source-facing essential-image criterion for exact
  functors out of the LinearRepresentations_Serre_1977 quotient;
- source/core/bridge triage:
  `source-facing`: essential surjectivity of `Q` and the kernel criterion for exact factorization
    through the LinearRepresentations_Serre_1977 quotient;
  `core/canonical`: `Q`, `whiskeringLeft Q P B`, `Localization.essSurj`, `Localization.lift`,
    and `essImage_whiskeringLeft Q P B`;
  `bridge/view`: `P.isoModSerre_isInvertedBy_iff`, which rewrites inversion of
    `P.isoModSerre` as containment in the kernel.
-/

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

-- Proof sketch: the localization of an abelian category at the morphisms that are isomorphisms
-- modulo a LinearRepresentations_Serre_1977 class preserves finite limits and finite colimits, hence is exact.
/-- The canonical functor to the LinearRepresentations_Serre_1977 quotient is exact. -/
theorem toSerreQuotient_exact :
    exactFunctor A P.isoModSerre.Localization Q :=
  ⟨preservesFiniteLimits Q P, preservesFiniteColimits Q P⟩

-- Proof sketch: an object maps to zero in the LinearRepresentations_Serre_1977 quotient exactly when its identity morphism
-- becomes an isomorphism modulo `P`, and this is equivalent to the object lying in `P`.
/-- The kernel of the canonical functor to the LinearRepresentations_Serre_1977 quotient is the original LinearRepresentations_Serre_1977 class. -/
theorem toSerreQuotient_kernel_eq :
    kernel Q = P := by
  ext X
  simpa using isZero_obj_iff Q P X

-- Proof sketch: every object of the LinearRepresentations_Serre_1977 quotient has the canonical localization-preimage
-- supplied by `Localization.essSurj`.
/-- Lemma 12.10.6: the quotient functor to the LinearRepresentations_Serre_1977 quotient is essentially surjective. -/
theorem toSerreQuotient_essSurj :
    Functor.EssSurj Q :=
  Localization.essSurj Q P.isoModSerre

-- Proof sketch: combine the canonical essential-image theorem for whiskering by a LinearRepresentations_Serre_1977
-- localization functor with the canonical criterion that exact functors invert `P.isoModSerre`
-- exactly when their kernels contain `P`.
/-- Lemma 12.10.6: an exact functor `G : A ⥤ₑ B` lies in the essential image of precomposition
with the quotient functor exactly when its kernel contains `P`. -/
theorem exactFunctor_mem_essImage_whiskeringLeft_iff
    (B : Type uB) [Category.{vB} B] [Abelian B] (G : A ⥤ₑ B) :
    (whiskeringLeft Q P B).essImage G ↔ P ≤ G.obj.kernel := by
  simpa [essImage_whiskeringLeft Q P B] using P.isoModSerre_isInvertedBy_iff G.obj

/-- Any exact functor whose kernel contains `P` factors through the LinearRepresentations_Serre_1977 quotient. -/
theorem exactFunctor_factors_through_toSerreQuotient
    (B : Type uB) [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hG : P ≤ G.obj.kernel) :
    (whiskeringLeft Q P B).essImage G :=
  (exactFunctor_mem_essImage_whiskeringLeft_iff P B G).2 hG

end

end _root_.CategoryTheory.ObjectProperty
