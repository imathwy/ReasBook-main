import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Lemma_21_20_4

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.Hom
  (ModuleCat ModuleDerived localizedRestriction localizedRestrictionComplex
    localizedRestrictionDerived)
open RingedSite.CochainComplex (IsStrictlyPerfect)
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

section

/- Domain-style sampling for Definition 21.45.1:
- primary domain: pseudo-coherence for derived objects of module sheaves on a ringed site;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent`,
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent`,
  `RingedSite.CochainComplex.IsStrictlyPerfect`,
  `j[U]⁻¹`;
- best owner abstraction: the ambient owner is the bundled ringed site `X`, with
  `RingedSite.CochainComplex.IsStrictlyPerfect` supplying the local approximation objects, the
  source-facing complex predicates `CochainComplex.IsMPseudoCoherent` /
  `CochainComplex.IsPseudoCoherent`, the local comparison predicate
  `HasStrictlyPerfectApproximationInDegree`, and the derived predicates as the canonical bridge
  from `ModuleDerived X` to the complex owners via `DerivedCategory.Q` and the localized
  restriction surface `j[U]⁻¹`;
- primitive data: the ringed site `X`, a complex or derived object of `𝒪_X`-modules, the
  localized object `U`, and the integer `m`;
- derived API: the complex predicates, the representative-based derived predicates, the
  representative bridge theorems, and the local approximation criterion, all reused directly by
  later closure and pullback theorems.

Source/core/bridge triage:
- `source-facing`: the complex pseudo-coherence predicates and the local comparison predicate
  `HasStrictlyPerfectApproximationInDegree`;
- `core/canonical`: `ModuleCat X`, `ModuleDerived X`, `DerivedCategory.Q`,
  `RingedSite.CochainComplex.IsStrictlyPerfect`, `localizedRestrictionDerived` with notation
  `j[U]⁻¹`,
  `CochainComplex.IsMPseudoCoherent`,
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent`, and
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent`;
- `bridge/view`: the local criterion
  `isPseudoCoherent_iff`,
  `isPseudoCoherent_iff_exists_pseudoCoherent_representative`,
  `isMPseudoCoherent_iff_forall_hasStrictlyPerfectApproximationInDegree`, which relates the
  representative-based owner to the source-facing localized approximation condition.
-/

variable {X : RingedSite.{u, v}}

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "Cpx" => CochainComplex (ModuleCat X) ℤ
local notation "DMod" => ModuleDerived X

namespace CochainComplex

/-- Definition 21.45.1 (complex `m`-version): a complex of `𝒪_X`-modules is
`m`-pseudo-coherent if, after passing to a covering of every object `U`, each restricted complex
admits a morphism from a strictly perfect complex inducing cohomology isomorphisms in degrees
`> m` and an epimorphism in degree `m`. -/
@[stacks 08FT]
def IsMPseudoCoherent (E : Cpx) (m : ℤ) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModuleCat (X.localization I.Y)) ℤ,
      IsStrictlyPerfect E' ∧
        ∃ α : E' ⟶ (localizedRestrictionComplex X I.Y).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
@[stacks 08FT]
def IsPseudoCoherent (E : Cpx) : Prop :=
  ∀ m : ℤ, E.IsMPseudoCoherent m

end CochainComplex

namespace RingedSite.Hom
namespace ModuleDerived

open _root_.CochainComplex

/-- Definition 21.45.1 (derived `m`-version): an object of `D(𝒪_X)` is
`m`-pseudo-coherent if it admits an `m`-pseudo-coherent representative complex. The local
strict-perfect approximation criterion remains available as the companion bridge theorem
`RingedSite.DerivedCategory.isMPseudoCoherent_iff_forall_hasStrictlyPerfectApproximationInDegree`.
-/
@[stacks 08FT]
def IsMPseudoCoherent (K : DMod) (m : ℤ) : Prop :=
  ∃ E : Cpx, ∃ _ : K ≅ DerivedCategory.Q.obj E,
    E.IsMPseudoCoherent m

/-- Definition 21.45.1 (derived version): an object of `D(𝒪_X)` is pseudo-coherent if it
is represented by a pseudo-coherent complex. -/
@[stacks 08FT]
def IsPseudoCoherent (K : DMod) : Prop :=
  ∃ E : Cpx, ∃ _ : K ≅ DerivedCategory.Q.obj E,
    E.IsPseudoCoherent

end ModuleDerived
end RingedSite.Hom

namespace RingedSite
namespace DerivedCategory

open _root_.CochainComplex
open _root_.RingedSite.Hom.ModuleDerived

section

omit [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

/-- Definition 21.45.1 (derived `m`-version): the owner predicate is equivalently the existence
of an `m`-pseudo-coherent representative complex. -/
@[stacks 08FT]
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (K : DMod) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∃ E : Cpx, ∃ _ : K ≅ DerivedCategory.Q.obj E,
        E.IsMPseudoCoherent m :=
  Iff.rfl

/-- A derived object of `D(𝒪_X)` is pseudo-coherent exactly when it is represented by a
pseudo-coherent complex. This is the source-facing bridge from the derived owner to the complex
owner. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (K : DMod) :
    K.IsPseudoCoherent ↔
      ∃ E : Cpx, ∃ _ : K ≅ DerivedCategory.Q.obj E,
        E.IsPseudoCoherent :=
  Iff.rfl

/-- A derived object of `D(𝒪_X)` is pseudo-coherent exactly when it is `m`-pseudo-coherent
for every integer `m`. The representative-based definition remains the owner, and this theorem is
its degreewise characterization. -/
theorem isPseudoCoherent_iff
    (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m :=
  sorry

end

/-- A localized derived object `j[U]⁻¹ K` admits a strict-perfect approximation in degree `m`
when it is represented by a strictly perfect complex whose comparison morphism induces cohomology
isomorphisms above `m` and an epimorphism in degree `m`. -/
def HasStrictlyPerfectApproximationInDegree (K : DMod) (U : X) (m : ℤ) : Prop :=
  ∃ E' : CochainComplex (ModuleCat (X.localization U)) ℤ,
    IsStrictlyPerfect E' ∧
      ∃ α : DerivedCategory.Q.obj E' ⟶ (localizedRestrictionDerived X U).obj K,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat (X.localization U)) j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (ModuleCat (X.localization U)) m).map α)

/-- Strict-perfect approximation data in degree `m` transports across an isomorphism in the
ambient derived category. -/
theorem HasStrictlyPerfectApproximationInDegree.of_iso
    {K L : DMod} (e : K ≅ L) {U : X} {m : ℤ}
    (hK : HasStrictlyPerfectApproximationInDegree K U m) :
    HasStrictlyPerfectApproximationInDegree L U m := by
  sorry

section

variable [∀ U : X, HasBinaryProducts (X.localization U).carrier]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{max u v}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, ∀ V : X.localization U,
  (localizedRestriction (X.localization U) V).Additive]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteLimits (localizedRestriction (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteColimits (localizedRestriction (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  CategoryWithHomology (ModuleCat (((X.localization U).localization V)))]

/-- Relocalizing along an arrow `ρ : U ⟶ V` identifies strict-perfect approximation data for the
restriction of `K` to `X/U` with the corresponding approximation data for the restriction of
`j[V]⁻¹ K` to the composite object `W ⟶ U ⟶ V` of `X/V`. This is the witness-level bridge behind
the relocalization step in Lemma `21.45.3`. -/
theorem HasStrictlyPerfectApproximationInDegree.relocalization_iff
    {U V : X} (ρ : U ⟶ V) (K : DMod) (m : ℤ) (W : X.localization U) :
    HasStrictlyPerfectApproximationInDegree
        ((localizedRestrictionDerived X V).obj K) (Over.mk (W.hom ≫ ρ)) m ↔
      HasStrictlyPerfectApproximationInDegree
        ((localizedRestrictionDerived X U).obj K) W m := by
  sorry

end

/-- An object of `D(𝒪_X)` is `m`-pseudo-coherent exactly when every localized restriction
`j[I.Y]⁻¹ K` admits, after passing to a covering, a strict-perfect approximation in degree `m`.
This is the source-facing local criterion corresponding to the representative-based owner. -/
theorem isMPseudoCoherent_iff_forall_hasStrictlyPerfectApproximationInDegree
    (K : DMod) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasStrictlyPerfectApproximationInDegree K I.Y m :=
  sorry

end DerivedCategory
end RingedSite
