import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap18.Definition_18_43_1_Finite
import StacksProject_2024.Chap21.SheafModuleDerivedRestriction

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
variable [Abelian (Sheaf J (ModuleCat Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat Λ))]

local notation "Mod" => Sheaf J (ModuleCat Λ)

/- Domain-style sampling for Lemma 21.53.1:
- primary domain: bounded derived objects of sheaves of `Λ`-modules whose cohomology
  sheaves are locally constant of finite type, together with restriction to slice sites;
- sampled owner declarations:
  `Compᵇ(𝒜)`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `DerivedCategory.TStructure.t.bounded`,
  `CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `CategoryTheory.Functor.mapDerivedCategoryFactors`,
  `CategoryTheory.DerivedCategory.Q`;
- best owner abstraction:
  `source-facing`: after passing to a cover, the restricted derived object is represented by a
    bounded complex of finite-type locally constant sheaves;
  `core/canonical`: `Compᵇ(𝒜)`, `CochainComplex.bounded`, `t.bounded`, the slice restriction
    owner `J.overPullback (ModuleCat Λ) U`, the Chapter 13 cohomology owner
    `derivedCategoryCohomologyInProperty (finiteTypeLocallyConstantModule J Λ)`, and the derived
    quotient owner `DerivedCategory.Q.obj`;
  `bridge/view`: a local isomorphism
    `DerivedCategory.Q.obj P.obj ≅ (J.overPullback (ModuleCat Λ) U).mapDerivedCategory.obj K`.
- primitive data: the ambient derived object `K`, a cover arrow `I`, and a slice complex
  `P : Compᵇ(Sheaf (J.over I.Y) (ModuleCat Λ))`;
- derived API: the finite-type local constancy predicates on the terms `P.X n`, together with the
  canonical boundedness owners on `P` and `K`, plus the local derived representation isomorphism
  `DerivedCategory.Q.obj P.obj ≅ restrictedDerivedObject K U`.

This item stays `source-facing`: the tagged theorem keeps the textbook final-object statement,
now expressed at the canonical terminal object `⊤_ C`, while the arbitrary-object form is kept
only as a companion bridge. Its theorem surface uses the canonical derived restriction owner
together with the canonical Chapter 13 cohomology owner specialized to
`finiteTypeLocallyConstantModule J Λ`. The reusable local representation data is exposed through
the source-facing predicate `HasBoundedFiniteTypeLocallyConstantRestrictionModel`, rather than
being left only as a nested existential in the final theorem. -/

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
variable [Abelian (Sheaf J (ModuleCat Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat Λ))]

local notation "DMod" => DerivedCategory (Sheaf J (ModuleCat Λ))
local notation "ModOver[" U "]" => Sheaf (J.over U) (ModuleCat Λ)
local notation "res[" U "]" => (J.overPullback (ModuleCat Λ) U)

/-- The canonical restriction of a derived sheaf object to the slice site over `U`. This is a
thin bridge/view that supplies the exact-functor instances locally so the source-facing local-model
predicate can use an ordinary object-level API. -/
abbrev restrictedDerivedObject (K : DMod) (U : C)
    [Abelian (ModOver[U])] [CategoryWithHomology (ModOver[U])]
    [(res[U]).Additive] [PreservesFiniteLimits (res[U])] [PreservesFiniteColimits (res[U])] :
    DerivedCategory (ModOver[U]) :=
  (res[U]).mapDerivedCategory.obj K

/-- The restriction of `K` to the slice site over `U` is represented by a bounded complex whose
terms are locally constant sheaves of finite-type `Λ`-modules. -/
def HasBoundedFiniteTypeLocallyConstantRestrictionModel (K : DMod) (U : C)
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat Λ)]
    [Abelian (ModOver[U])] [CategoryWithHomology (ModOver[U])]
    [(res[U]).Additive] [PreservesFiniteLimits (res[U])] [PreservesFiniteColimits (res[U])] :
    Prop :=
  ∃ P : Compᵇ(ModOver[U]),
    (∃ _ : DerivedCategory.Q.obj P.obj ≅ restrictedDerivedObject K U,
      ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (P.obj.X n))

omit [HasWeakSheafify J (ModuleCat Λ)]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
  [CategoryWithHomology (Sheaf J (ModuleCat Λ))] in
/-- A local bounded-model witness for the restriction of `K` can be unpacked into its bounded
slice complex, derived comparison isomorphism, and finite-type locally constant termwise property.
-/
theorem HasBoundedFiniteTypeLocallyConstantRestrictionModel.exists_model
    {K : DMod} {U : C}
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat Λ)]
    [Abelian (ModOver[U])] [CategoryWithHomology (ModOver[U])]
    [(res[U]).Additive] [PreservesFiniteLimits (res[U])] [PreservesFiniteColimits (res[U])]
    (hK : HasBoundedFiniteTypeLocallyConstantRestrictionModel K U) :
    ∃ P : Compᵇ(ModOver[U]),
      (∃ _ : DerivedCategory.Q.obj P.obj ≅ restrictedDerivedObject K U,
        ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (P.obj.X n)) :=
  hK

variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat Λ))]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat Λ)]
variable [∀ U : C, (J.overPullback (ModuleCat Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat Λ) U)]

local notation "Bounded" => (t.bounded : ObjectProperty DMod)
local notation "FiniteTypeLCoh" =>
  derivedCategoryCohomologyInProperty (finiteTypeLocallyConstantModule J Λ)

-- Proof sketch: argue by induction on the cohomological amplitude of `K`. After refining to a
-- cover of the final object `X`, make the top nonzero cohomology sheaf constant of finite type,
-- choose a surjection from a finite free constant sheaf, and form the cone to reduce the
-- amplitude. The weak-Serre closure of locally constant finite-type sheaves keeps the cone in the
-- same class, so on each member of the cover one obtains a bounded complex of locally constant
-- finite-type sheaves together with an explicit comparison isomorphism to the restricted derived
-- object.
/-- Companion bridge to Lemma 21.53.1 for an arbitrary object `X`. This is not the tagged textbook
statement; it is the reusable generalization obtained by applying the final-object theorem in the
slice-site situation over `X`. -/
theorem exists_cover_restriction_represented_by_bounded_finite_type_locally_constant_complex_over_object
    (X : C)
    (K : DMod) (hKbounded : Bounded K)
    (hK : FiniteTypeLCoh K) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      HasBoundedFiniteTypeLocallyConstantRestrictionModel K I.Y := by
  sorry

/-- Lemma 21.53.1: if `C` has a final object and `K ∈ Dᵇ(𝒞, Λ)` has cohomology sheaves locally
constant of finite type, then there exists a covering of the canonical terminal object `⊤_ C`
such that on each slice site `(𝒞/I.Y, J.over I.Y)` the restricted derived object
`restrictedDerivedObject K I.Y` admits a bounded model by locally constant finite-type sheaves of
`Λ`-modules, expressed by the source-facing owner
`HasBoundedFiniteTypeLocallyConstantRestrictionModel K I.Y`. -/
@[stacks 094G]
theorem exists_cover_restriction_represented_by_bounded_finite_type_locally_constant_complex
    [HasTerminal C] (K : DMod) (hKbounded : Bounded K) (hK : FiniteTypeLCoh K) :
    ∃ T : J.Cover (⊤_ C), ∀ I : T.Arrow,
      HasBoundedFiniteTypeLocallyConstantRestrictionModel K I.Y := by
  simpa using
    exists_cover_restriction_represented_by_bounded_finite_type_locally_constant_complex_over_object
      (⊤_ C) K hKbounded hK

end

end CategoryTheory.Sheaf
