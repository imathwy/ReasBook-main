import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.CochainComplex (IsStrictlyPerfect)
open RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite

section PerfectComplex

/- Domain-style sampling for Definition 21.47.1:
- primary domain: perfect complexes and perfect derived objects of sheaves of modules on a ringed
  site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `RingedSite.Hom.localizedRestriction`,
  `CochainComplex.IsStrictlyPerfect`,
  `DerivedCategory.Q`,
  `ObjectProperty.IsClosedUnderIsomorphisms`;
- best owner abstraction:
  `source-facing`: `RingedSite.CochainComplex.IsPerfect` and
    `RingedSite.Hom.ModuleDerived.IsPerfect`;
  `core/canonical`: `ModuleCat X`, `ModuleDerived X`, `localizedRestriction X U`, and
    `CochainComplex.IsStrictlyPerfect`;
  `bridge/view`: the representative criterion and isomorphism-invariance theorems in
    `RingedSite.DerivedCategory`.
- primitive data: for each localized object, a cover together with a strictly perfect local model
  and a quasi-isomorphism to the localized restriction;
- derived API: the perfect derived-object owner, the constructor from a chosen perfect
  representative, the elimination companion `exists_perfect_representative`, and stability under
  isomorphism. -/

variable {X : RingedSite.{u, v}}
variable [HasBinaryProducts X.carrier]

variable [∀ U : X, (localizedRestriction X U).Additive]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "Mod" => ModuleCat X
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ModLoc" U => ModuleCat (X.localization U)

namespace CochainComplex

/-- Definition 21.47.1: a complex of `𝒪_X`-modules on a ringed site is perfect if every localized
restriction is quasi-isomorphic, on a covering, to a strictly perfect complex. -/
@[stacks 08G5]
def IsPerfect (E : Cpx) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      ∃ α :
        E' ⟶ ((localizedRestriction X I.Y).mapHomologicalComplex (up ℤ)).obj E,
        IsStrictlyPerfect E' ∧ QuasiIso α

omit [∀ U : X, (localizedRestriction X U).Additive] [CategoryWithHomology (ModuleCat X)] in
/-- Helper for Definition 21.47.1: a perfect complex admits a strictly perfect local model over
every localization. -/
theorem exists_strictlyPerfect_localModel {E : Cpx} (hE : IsPerfect E) (U : X) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
        ∃ α :
          E' ⟶ ((localizedRestriction X I.Y).mapHomologicalComplex (up ℤ)).obj E,
          IsStrictlyPerfect E' ∧ QuasiIso α := by
  -- Proof comment: unfold the definition at the chosen object `U`.
  -- Evaluate the defining local perfectness condition at the chosen object `U`.
  exact hE U

end CochainComplex

end PerfectComplex

section PerfectDerived

variable {X : RingedSite.{u, v}}
variable [HasBinaryProducts X.carrier]

-- Route correction: reuse the canonical owner surface from `RingedSite.Hom` instead of private
-- local aliases, so `X.localization`, `ModuleCat`, and `ModuleDerived` come from their owner API.
local notation "Mod" => ModuleCat X
local notation "Cpx" => CochainComplex Mod ℤ
local notation "DMod" => ModuleDerived X

namespace Hom.ModuleDerived

/-- A derived-object form of Definition 21.47.1: an object of `D(𝒪_X)` on a ringed site is perfect
if it is
represented by a perfect
complex. -/
@[stacks 08G5]
def IsPerfect (K : DMod) : Prop :=
  ∃ E : Cpx,
    ∃ _ : K ≅ DerivedCategory.Q.obj E,
      RingedSite.CochainComplex.IsPerfect E

/-- Helper for Definition 21.47.1: a chosen perfect representative complex presents a perfect
object of `D(𝒪_X)`. -/
theorem of_iso_q_obj {K : DMod} {E : Cpx} (e : K ≅ DerivedCategory.Q.obj E)
    (hE : RingedSite.CochainComplex.IsPerfect E) :
    IsPerfect K :=
by
  -- Proof comment: package the chosen representative and its perfectness witness.
  exact ⟨E, e, hE⟩

/-- Helper for Definition 21.47.1: a perfect object of `D(𝒪_X)` admits a perfect representative
complex. -/
theorem exists_perfect_representative {K : DMod} (hK : IsPerfect K) :
    ∃ E : Cpx,
      ∃ _ : K ≅ DerivedCategory.Q.obj E,
        RingedSite.CochainComplex.IsPerfect E := by
  -- Proof comment: the defining predicate already stores the desired representative data.
  exact hK

end Hom.ModuleDerived

namespace DerivedCategory

open _root_.RingedSite.Hom.ModuleDerived

local notation "PerfectObj" => (RingedSite.Hom.ModuleDerived.IsPerfect : ObjectProperty DMod)

/-- Helper for Definition 21.47.1: perfect objects of `D(𝒪_X)` are stable under isomorphism. -/
instance isPerfect_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms PerfectObj where
  of_iso e hK := by
    -- Proof comment: pick a perfect representative for the source object.
    -- Unpack one perfect representative of `K`.
    rcases hK with ⟨E, eE, hE⟩
    -- Proof comment: transport the representative along the ambient isomorphism.
    -- Compose the chosen representative isomorphism with the ambient isomorphism.
    exact of_iso_q_obj (e.symm ≪≫ eE) hE

end DerivedCategory

end PerfectDerived

end RingedSite
