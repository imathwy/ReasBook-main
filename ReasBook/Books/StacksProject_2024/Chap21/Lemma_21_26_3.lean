import Mathlib
import StacksProject_2024.Chap07.Lemma_7_29_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- The abelian category of sheaves of abelian groups on the site `(C, J)`. -/
private abbrev AbSheaf :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The unbounded derived category of sheaves of abelian groups on the site `(C, J)`. -/
private abbrev AbSheafDerived :=
  DerivedCategory (AbSheaf J)

/-- The unbounded derived category of abelian groups. -/
private abbrev AbDerived :=
  DerivedCategory AddCommGrpCat.{max u v}

-- Proof sketch: use the pushout description of `h_X^#` together with the monomorphism
-- `h_E^# ⟶ h_Y^#` to show that for every injective abelian sheaf `ℐ`, the sequence
-- `0 ⟶ ℐ(X) ⟶ ℐ(Z) ⊞ ℐ(Y) ⟶ ℐ(E) ⟶ 0` is short exact. Applying this to a K-injective
-- representative of each `K ∈ D(\mathcal C)` gives comparison morphisms to the mapping cocone
-- from Lemma `21.26.1`, and those comparisons are quasi-isomorphisms. Lemma `21.26.1` then
-- yields the distinguished triangle, while the construction is natural in `K`.
/-- Lemma 21.26.3: if the sheafified representable `h_X^#` is a pushout of
`h_E^# ⟶ h_Y^#` and `h_E^# ⟶ h_Z^#`, and if `h_E^# ⟶ h_Y^#` is a monomorphism, then there is a
functorial Mayer-Vietoris triangle on `D(\mathcal C)` whose terms are `R\Gamma(X, K)`,
`R\Gamma(Z, K) ⊕ R\Gamma(Y, K)`, and `R\Gamma(E, K)`, and this triangle is distinguished for
every `K`. Here the derived-sections functors `RGammaX`, `RGammaY`, `RGammaZ`, and `RGammaE`
formalize `R\Gamma(X,-)`, `R\Gamma(Y,-)`, `R\Gamma(Z,-)`, and `R\Gamma(E,-)`, while `RGammaZY`
formalizes the biproduct functor `K ↦ R\Gamma(Z, K) ⊕ R\Gamma(Y, K)`. -/
theorem exists_functorial_mayerVietoris_triangle_of_sheafifiedRepresentable_pushout
    {X Y Z E : C}
    (f : E ⟶ Y) (g : E ⟶ Z)
    (cocone :
      PushoutCocone (J.sheafifiedRepresentableMap f) (J.sheafifiedRepresentableMap g))
    (hX : cocone.pt ≅ J.sheafifiedRepresentable X)
    (hcocone : IsColimit cocone)
    (hmono : Mono (J.sheafifiedRepresentableMap f))
    (RGammaX RGammaY RGammaZ RGammaE : AbSheafDerived J ⥤ AbDerived)
    :
    ∃ (RGammaZY : AbSheafDerived J ⥤ AbDerived)
      (alpha : RGammaX ⟶ RGammaZY)
      (beta : RGammaZY ⟶ RGammaE)
      (middleIso : ∀ K : AbSheafDerived J, RGammaZY.obj K ≅ RGammaZ.obj K ⨯ RGammaY.obj K)
      (delta : RGammaE ⟶ RGammaX ⋙ shiftFunctor (AbDerived) (1 : ℤ)),
      ∀ K : AbSheafDerived J,
        Triangle.mk (alpha.app K) (beta.app K) (delta.app K) ∈ distTriang (AbDerived) := sorry

end

end CategoryTheory.GrothendieckTopology
