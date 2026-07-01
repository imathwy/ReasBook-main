import Mathlib
import stacks_project.Chap18.Definition_18_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace CategoryTheory

namespace Sheaf

/- Domain-style sampling for Lemma 18.43.3:
- primary domain: locally constant sheaves and morphisms that become maps between constant sheaf
  models after restricting to a cover.
- sampled owner-level declarations:
  `CategoryTheory.CommSq`,
  `CategoryTheory.constantSheaf`,
  `CategoryTheory.Sheaf.IsConstant`,
  `CategoryTheory.Sheaf.IsLocallyConstant`,
  `CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp`.
- best owner abstraction: `CategoryTheory.CommSq` for the comparison between a sheaf morphism and
  a chosen map of constant models; the local constant-data predicates remain source-facing owners
  for the covering statements.
- primitive data: chosen constant models for the source and target together with a morphism
  between their constant values.
- derived API: the commuting square relating the original sheaf morphism to that map of constant
  sheaves, and the existence of coverings on which such squares exist.

Source/core/bridge triage:
- `source-facing`: the three existence theorems below.
- `core/canonical`: `CommSq`, `constantSheaf`, and the locally constant owners from
  `Definition_18_43_1`.
- `bridge/view`: the local witnesses showing that a restricted morphism is induced by a map
  between chosen constant models. -/

section MainStatements

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

-- Proof sketch: trivialize the finite locally constant source and the locally constant target on a
-- common covering family of the terminal object. Because the chosen source value is finite, one
-- can refine further so that the restricted morphism is locally determined by a single function on
-- that finite set, yielding a morphism of constant sheaves on each member of the refined cover.
/-- Lemma 18.43.3 (1): for a morphism of locally constant sheaves of sets whose source is finite
locally constant, there is a covering of the terminal object on which the restriction fits into a
commutative square with a map of constant sheaves associated with a map of sets. -/
theorem exists_coversTop_restriction_isConstantSheafMap_type
    {F G : Sheaf J (Type w)} (φ : F ⟶ G) [IsFiniteLocallyConstant F]
    [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (A B : Type w) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj B),
            CommSq ((J.overPullback (Type w) (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) (Type w)).map f) := sorry

end Types

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

-- Proof sketch: trivialize the finite locally constant source and the locally constant target on a
-- common covering family of the terminal object. The source has finite underlying set locally, so
-- after refining the cover the restricted morphism is determined by one homomorphism on the chosen
-- constant model, and hence is a morphism of constant abelian sheaves on each covering object.
/-- Lemma 18.43.3 (2): for a morphism of locally constant sheaves of abelian groups whose source
is finite locally constant, there is a covering of the terminal object on which the restriction is
part of a commutative square with a map of constant abelian sheaves associated with a homomorphism
of abelian groups. -/
theorem exists_coversTop_restriction_isConstantSheafMap_addCommGrp
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (A B : AddCommGrpCat.{w}) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj B),
            CommSq ((J.overPullback AddCommGrpCat.{w} (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) AddCommGrpCat.{w}).map f) := sorry

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

-- Proof sketch: choose a cover on which the source is constant with finitely generated module
-- value and the target is constant. After refining, finitely many generators of the source have
-- images coming from fixed sections of the constant target model, which defines a single
-- `\Lambda`-linear map inducing the restricted morphism on each member of the cover.
/-- Lemma 18.43.3 (3): for a morphism of locally constant sheaves of `\Lambda`-modules whose
source is locally constant of finite type, there is a covering of the terminal object on which the
restriction fits into a commutative square with a map of constant sheaves of `\Lambda`-modules
associated with a `\Lambda`-linear map. -/
theorem exists_coversTop_restriction_isConstantSheafMap_module
    {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (M N : ModuleCat.{w} Λ) (f : M ⟶ N)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj M)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj N),
            CommSq ((J.overPullback (ModuleCat.{w} Λ) (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).map f) := sorry

end Modules

end MainStatements

end Sheaf

end CategoryTheory
