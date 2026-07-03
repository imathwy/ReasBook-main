import Mathlib
import StacksProject_2024.Chap07.Lemma_7_29_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open CochainComplex
open CochainComplex.HomComplex

noncomputable section

universe u v u₁ v₁ u₂ v₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable (τ τ' : GrothendieckTopology C)
variable [HasWeakSheafify τ (Type (max u v))]

/-- Membership in the essential image of a functor. -/
private abbrev IsInEssentialImage
    {SourceDerived : Type u₁} {TargetDerived : Type u₂}
    [Category.{v₁} SourceDerived] [Category.{v₂} TargetDerived]
    (F : SourceDerived ⥤ TargetDerived) (K' : TargetDerived) : Prop :=
  ∃ K : SourceDerived, Nonempty (F.obj K ≅ K')

-- Proof sketch: the defining relation for `mappingCocone.lift` with the zero `(-1)`-cochain
-- reduces to the chain-map identity `α ≫ β = 0`.
/-- The zero `(-1)`-cochain satisfies the cocycle relation needed to define the canonical
comparison map into `mappingCocone β`. -/
private theorem mayerVietorisComparisonMap_condition
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    δ (-1) 0 (0 : Cochain IX IE (-1)) +
        Cochain.ofHom (α ≫ β) =
      0 := sorry

/-- The canonical comparison morphism from the left term of a short exact sequence of complexes
to the mapping cocone of the right-hand map. -/
noncomputable def mayerVietorisComparisonMap
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    IX ⟶ mappingCocone β :=
  mappingCocone.lift β α (0 : Cochain IX IE (-1))
    (mayerVietorisComparisonMap_condition α β hαβ)

-- Proof sketch: choose `K` and an isomorphism `derivedPushforward.obj K ≅ K'` from the essential
-- image hypothesis. Lemma `21.20.10` upgrades a K-injective representative of `K` to a
-- K-injective representative on the `τ'`-side, and Lemma `21.26.3` gives the short exact sequence
-- of complexes computing the Mayer-Vietoris comparison. The chosen identifications with
-- `RGammaX`, `RGammaZY`, and `RGammaE` show that the resulting canonical lift is exactly the
-- comparison map `c^{K'}_{X,Z,Y,E}`, hence it becomes an isomorphism in `D(\mathbf Z)`.
/-- Lemma 21.29.3: with `\epsilon : (\mathcal C_\tau, \mathcal O_\tau) \to
(\mathcal C_{\tau'}, \mathcal O_{\tau'})` as above, assume that `h_X^\#` is the pushout of
`h_E^\# \to h_Y^\#` and `h_E^\# \to h_Z^\#` for `\tau`-sheafification and that
`h_E^\# \to h_Y^\#` is injective. If `K'` lies in the essential image of the derived pushforward
formalizing `R \epsilon_*`, then the Mayer-Vietoris comparison map
`c^{K'}_{X,Z,Y,E}` of Lemma `21.26.1`, here modeled by the canonical
`mayerVietorisComparisonMap α β hαβ`, is an isomorphism in the derived category of abelian
groups. -/
theorem mayerVietorisComparison_isIso_of_mem_essentialImage
    {SourceDerived : Type u₁} {TargetDerived : Type u₂}
    [Category.{v₁} SourceDerived] [Category.{v₂} TargetDerived]
    {X Y Z E : C}
    (f : E ⟶ Y) (g : E ⟶ Z)
    (cocone :
      PushoutCocone (τ.sheafifiedRepresentableMap f) (τ.sheafifiedRepresentableMap g))
    (hX : cocone.pt ≅ τ.sheafifiedRepresentable X)
    (hcocone : IsColimit cocone)
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (derivedPushforward : SourceDerived ⥤ TargetDerived)
    {K' : TargetDerived}
    (hK' : IsInEssentialImage derivedPushforward K')
    (RGammaX RGammaY RGammaZ RGammaE :
      TargetDerived ⥤ DerivedCategory AddCommGrpCat)
    (RGammaZY : TargetDerived ⥤ DerivedCategory AddCommGrpCat)
    (middleIso : ∀ K : TargetDerived, RGammaZY.obj K ≅ RGammaZ.obj K ⨯ RGammaY.obj K)
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0)
    (hexact : (ShortComplex.mk α β hαβ).ShortExact)
    (eX : Q.obj IX ≅ RGammaX.obj K')
    (eZY : Q.obj IZY ≅ RGammaZY.obj K')
    (eE : Q.obj IE ≅ RGammaE.obj K') :
    IsIso (Q.map (mayerVietorisComparisonMap α β hαβ)) := sorry

end

end CategoryTheory.GrothendieckTopology
