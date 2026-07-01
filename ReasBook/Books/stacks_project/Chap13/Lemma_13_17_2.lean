import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe wA wQ uA vA

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits Q :=
  preservesFiniteLimits Q P

local instance : PreservesFiniteColimits Q :=
  preservesFiniteColimits Q P

variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} (P.isoModSerre.Localization)]

/- Domain-style sampling for 13.17.2:
- primary domain: Serre localizations of abelian categories and the induced functor on derived
  categories;
- sampled owner declarations:
  `ObjectProperty.SerreClassLocalization.abelian`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteLimits`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteColimits`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `CategoryTheory.Functor.EssSurj`;
- best owner abstraction: the derived functor owner `Q.mapDerivedCategory` of the
  canonical Serre quotient functor `Q := P.isoModSerre.Q`;
- primitive data: the Serre class `P` and the quotient functor `Q`;
- derived API: the abelian structure on `P.isoModSerre.Localization` and the finite-limit and
  finite-colimit preservation instances for `Q`, supplied canonically by the Serre-localization
  owner API and consumed directly by `Q.mapDerivedCategory`;
- source/core/bridge triage:
  `source-facing`: the essential-surjectivity statement for the derived Serre quotient functor;
  `core/canonical`: `Q.mapDerivedCategory`;
  `bridge/view`: objectwise preimages in the underived Serre quotient, transported to the derived
  category through complex representatives and the localization map `DerivedCategory.Q`.

This file therefore uses the Serre-localization owner instances directly instead of repackaging
them through a local exactness wrapper. -/

-- Proof sketch: represent an object of `D(A / P)` by a complex in the Serre quotient, then use
-- Lemma 12.10.6 degreewise to lift the differential data to a quasi-isomorphic complex in `A`.
-- The lifted complex becomes isomorphic to the original object after applying the derived functor,
-- producing the canonical owner witness `Q.mapDerivedCategory.EssSurj`.
/-- Lemma 13.17.2: if `P` is a Serre subcategory of an abelian category `A`, then the canonical
functor `D(A) ⟶ D(A/P)` induced by the Serre quotient functor is essentially surjective. -/
theorem serreQuotientDerivedFunctor_essSurj :
    Functor.EssSurj ((Q).mapDerivedCategory) := sorry

end _root_.CategoryTheory.ObjectProperty
