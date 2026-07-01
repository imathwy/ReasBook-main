import Mathlib
import stacks_project.Chap18.Definition_18_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace CategoryTheory

namespace Sheaf

section FinitePresentationLocallyConstantModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- A locally constant sheaf of `\Lambda`-modules is of finite presentation if locally it is
isomorphic to a constant sheaf with finitely presented module value. -/
class IsFinitePresentationLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop
    extends IsLocallyConstant (J := J) (D := ModuleCat.{w} Λ) F where
  /-- Every object admits a covering on which the restriction of the sheaf is constant with
  finitely presented `\Lambda`-module value. -/
  exists_finitePresentation_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ M : ModuleCat.{w} Λ, Module.FinitePresentation Λ M ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M)

-- Proof sketch: use the identity covering of each object `U`; the restriction of a constant
-- sheaf with value `M` remains constant with the same value, and the given finite-presentation
-- instance on `M` supplies the local finite-presentation condition.
/-- A constant sheaf with finitely presented value is finite-presentation locally constant. -/
instance isFinitePresentationLocallyConstantModule_of_constant
    (M : ModuleCat.{w} Λ) [Module.FinitePresentation Λ M] :
    IsFinitePresentationLocallyConstantModule
      ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := sorry

end FinitePresentationLocallyConstantModules

end Sheaf

section IsoSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]

-- Proof sketch: restriction along the identity functor on `Over X` is the identity, so the map
-- on local isomorphisms is pointwise the identity.
/-- Restriction along the identity morphism acts trivially on local isomorphisms. -/
theorem sheafIsoPresheaf_map_id
    (F G : Sheaf J (ModuleCat.{w} Λ)) (X : Cᵒᵖ)
    (φ : (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
      (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G) :
    (J.overMapPullback (ModuleCat.{w} Λ) (𝟙 X.unop)).mapIso φ = φ := sorry

-- Proof sketch: restriction of local isomorphisms is functorial, so restricting first along `g`
-- and then along `f` agrees with restricting once along `f ≫ g`.
/-- Restriction of local isomorphisms is compatible with composition. -/
theorem sheafIsoPresheaf_map_comp
    (F G : Sheaf J (ModuleCat.{w} Λ)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
      (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G) :
    (J.overMapPullback (ModuleCat.{w} Λ) ((f ≫ g).unop)).mapIso φ =
      (J.overMapPullback (ModuleCat.{w} Λ) g.unop).mapIso
        ((J.overMapPullback (ModuleCat.{w} Λ) f.unop).mapIso φ) := sorry

/-- The presheaf of local isomorphisms between two sheaves of `\Lambda`-modules on a site. -/
def sheafIsoPresheaf
    (F G : Sheaf J (ModuleCat.{w} Λ)) : Cᵒᵖ ⥤ Type (max u v w) where
  obj X := (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
    (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G
  map f := fun φ ↦ (J.overMapPullback (ModuleCat.{w} Λ) f.unop).mapIso φ
  map_id := by
    intro X
    funext φ
    exact sheafIsoPresheaf_map_id (Λ := Λ) F G X φ
  map_comp := by
    intro X Y Z f g
    funext φ
    exact sheafIsoPresheaf_map_comp (Λ := Λ) F G f g φ

-- Proof sketch: local isomorphisms glue by applying the sheaf condition to the forward and
-- inverse morphisms in the sheaves `sheafHom F G` and `sheafHom G F`; the glued maps remain
-- inverse by uniqueness of gluing.
/-- The presheaf of local isomorphisms satisfies the sheaf condition. -/
theorem sheafIsoPresheaf_isSheaf (F G : Sheaf J (ModuleCat.{w} Λ)) :
    Presheaf.IsSheaf J (sheafIsoPresheaf (J := J) F G) := sorry

/-- The sheaf of local isomorphisms between two sheaves of `\Lambda`-modules on a site. -/
def sheafIso (F G : Sheaf J (ModuleCat.{w} Λ)) : Sheaf J (Type (max u v w)) :=
  ⟨sheafIsoPresheaf (J := J) F G, sheafIsoPresheaf_isSheaf (J := J) F G⟩

end IsoSheaf

section MainStatements

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section ConstantHom

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]

-- Proof sketch: present `M` by a finite free module, apply the sheaf of local
-- `\Lambda`-linear maps from the corresponding constant sheaves into `\underline N`, and reduce
-- to the finite free case where this sheaf is visibly the constant sheaf with value
-- `\operatorname{Hom}_\Lambda(M, N)`.
/-- Lemma 18.43.4 (1): if `M` is finitely presented, then the sheaf of local
`\Lambda`-linear maps from the constant sheaf `\underline M` to the constant sheaf `\underline N`
is a constant sheaf, namely the constant sheaf with value `\operatorname{Hom}_\Lambda(M, N)`. -/
theorem sheafHom_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{w} Λ) [Module.FinitePresentation Λ M] :
    Sheaf.IsConstant J
      (sheafHom
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{w} Λ)).obj N)) := sorry

end ConstantHom

section ConstantIso

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]

-- Proof sketch: by the previous clause the local Hom sheaf between `\underline M` and
-- `\underline N` is constant; the local isomorphism sheaf is the subsheaf of those sections whose
-- inverses lie in the corresponding constant Hom sheaf in the opposite direction, so it is again
-- constant with value `\operatorname{Isom}_\Lambda(M, N)`.
/-- Lemma 18.43.4 (2): if `M` and `N` are finitely presented, then the sheaf of local
isomorphisms between the constant sheaves `\underline M` and `\underline N` is a constant sheaf,
namely the constant sheaf with value `\operatorname{Isom}_\Lambda(M, N)`. -/
theorem sheafIso_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{w} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    Sheaf.IsConstant J
      (sheafIso
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{w} Λ)).obj N)) := sorry

end ConstantIso

section LocallyConstantHom

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]

-- Proof sketch: the assertion is local on the site. On a covering where `F` is identified with a
-- constant sheaf of a finitely presented module and `G` with a constant sheaf, apply clause (1)
-- to identify the restricted sheaf of local `\Lambda`-linear maps with a constant sheaf; these
-- local identifications give local constancy of the whole Hom sheaf.
/-- Lemma 18.43.4 (3): if `\mathcal F` is a locally constant sheaf of `\Lambda`-modules of finite
presentation and `\mathcal G` is locally constant, then the sheaf of local `\Lambda`-linear maps
from `\mathcal F` to `\mathcal G` is locally constant. -/
theorem sheafHom_isLocallyConstant_of_finitePresentationLocallyConstant
    (F G : Sheaf J (ModuleCat.{w} Λ))
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) F]
    [Sheaf.IsLocallyConstant (J := J) (D := ModuleCat.{w} Λ) G] :
    Sheaf.IsLocallyConstant (J := J) (D := Type (max u v w)) (sheafHom F G) := sorry

end LocallyConstantHom

section LocallyConstantIso

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]

-- Proof sketch: apply clause (3) in both directions to obtain local constancy of the Hom sheaves
-- `\mathcal H\!om(\mathcal F, \mathcal G)` and `\mathcal H\!om(\mathcal G, \mathcal F)`. The
-- local isomorphism sheaf is the subsheaf cut out by the equations expressing that a section and
-- its inverse compose to the identity, hence it is locally constant as well.
/-- Lemma 18.43.4 (4): if `\mathcal F` and `\mathcal G` are locally constant sheaves of
`\Lambda`-modules of finite presentation, then the sheaf of local isomorphisms
`\mathit{Isom}_{\underline{\Lambda}}(\mathcal F, \mathcal G)` is locally constant. -/
theorem sheafIso_isLocallyConstant_of_finitePresentationLocallyConstant
    (F G : Sheaf J (ModuleCat.{w} Λ))
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) F]
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) G] :
    Sheaf.IsLocallyConstant
      (J := J) (D := Type (max u v w)) (sheafIso F G) := sorry

end LocallyConstantIso

end MainStatements

end CategoryTheory
