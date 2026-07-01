import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Sheaf
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- The sheafification of a presheaf of sets on the site `(C, J)`. -/
private abbrev sheafifiedPresheaf
    (P : Cᵒᵖ ⥤ Type (max u v)) : Sheaf J (Type (max u v)) :=
  (presheafToSheaf J (Type (max u v))).obj P

/-- The morphism of sheafifications induced by a morphism of presheaves of sets. -/
private abbrev sheafifiedPresheafMap
    {P Q : Cᵒᵖ ⥤ Type (max u v)} (f : P ⟶ Q) :
    sheafifiedPresheaf J P ⟶ sheafifiedPresheaf J Q :=
  (presheafToSheaf J (Type (max u v))).map f

/-- The abelian category of sheaves of abelian groups on `(C, J)`. -/
private abbrev AbSheaf :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The unbounded derived category of abelian sheaves on `(C, J)`. -/
private abbrev AbSheafDerived :=
  DerivedCategory (AbSheaf J)

/-- The unbounded derived category of abelian groups. -/
private abbrev AbDerived :=
  DerivedCategory AddCommGrpCat.{max u v}

section

variable {D E F G : Cᵒᵖ ⥤ Type (max u v)}
variable {a : D ⟶ E} {b : D ⟶ F} {c : E ⟶ G} {d : F ⟶ G}

-- Proof sketch: replace the presheaves by their sheafifications, so the hypotheses become a
-- pushout square of sheaves with monic left leg. Then pass to a site presentation from Lemma
-- `7.29.5` in which the four sheaves become representable; Lemma `21.26.3` gives the distinguished
-- triangle on that larger site. Finally transport the result back along the equivalence of topoi,
-- using that the cohomology over a sheaf of sets depends only on the localized topos.
/-- Lemma 21.26.4: for a commutative square of presheaves of sets on a site `(C, J)`,
if the induced cocone
`E^# ⟶ G^# ← F^#` is a pushout of `D^# ⟶ E^#` and `D^# ⟶ F^#`, and if
`D^# ⟶ F^#` is a monomorphism, then derived cohomology functors formalizing
`R\Gamma(D,-)`, `R\Gamma(E,-)`, `R\Gamma(F,-)`, and `R\Gamma(G,-)` fit into a functorial
distinguished Mayer-Vietoris triangle
`R\Gamma(G,K) ⟶ R\Gamma(E,K) \oplus R\Gamma(F,K) ⟶ R\Gamma(D,K) ⟶ R\Gamma(G,K)[1]`
for every `K` in the derived category of abelian sheaves on `(C, J)`. In the Lean statement,
these are represented by the functor parameters `RGammaD`, `RGammaE`, `RGammaF`, and `RGammaG`.
-/
theorem exists_functorial_mayerVietoris_triangle_of_sheafified_presheaf_pushout
    (sq : CommSq a b c d)
    (hpushout :
      IsColimit
        (PushoutCocone.mk
          (sheafifiedPresheafMap J c)
          (sheafifiedPresheafMap J d)
          ((sq.map (presheafToSheaf J (Type (max u v)))).w)))
    (hmono : Mono (sheafifiedPresheafMap J b))
    (RGammaD RGammaE RGammaF RGammaG : AbSheafDerived J ⥤ AbDerived) :
    ∃ (RGammaEF : AbSheafDerived J ⥤ AbDerived)
      (alpha : RGammaG ⟶ RGammaEF)
      (beta : RGammaEF ⟶ RGammaD)
      (middleIso :
        ∀ K : AbSheafDerived J,
          RGammaEF.obj K ≅ RGammaE.obj K ⨯ RGammaF.obj K)
      (delta : RGammaD ⟶ RGammaG ⋙ shiftFunctor (AbDerived) (1 : ℤ)),
      ∀ K : AbSheafDerived J,
        Triangle.mk (alpha.app K) (beta.app K) (delta.app K) ∈ distTriang (AbDerived) := sorry

end

end

end CategoryTheory.GrothendieckTopology
