import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_26_1 (from Chap21) -/
/-
Domain-style sampling for Lemma 21.26.1:
- primary domain: distinguished triangles in the derived category of abelian groups coming from
  the canonical mapping-cocone triangle;
- inspected canonical declarations:
  `DerivedCategory.mappingCocone_triangle_distinguished`,
  `CochainComplex.mappingCocone.triangle`,
  `Triangle.isoMk`,
  `Pretriangulated.isomorphic_distinguished`;
- owner abstraction: `DerivedCategory.mappingCocone_triangle_distinguished`;
- primitive data: a morphism `β : IZY ⟶ IE` of cochain complexes and a comparison morphism
  `c : IX ⟶ mappingCocone β` whose image in the derived category is an isomorphism;
- derived API: transport of the canonical distinguished triangle along `asIso (Q.map c)`, and the
  induced canonical identification between two such comparison choices.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris triangle obtained by replacing `C(β)[-1]` with a quasi-isomorphic
  complex `IX`;
- `core/canonical`: `DerivedCategory.mappingCocone_triangle_distinguished`;
- `bridge/view`: the triangle isomorphism built from `asIso (Q.map c)`.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory
open CochainComplex

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section

/-- The category of `\mathbf Z`-indexed cochain complexes of abelian groups. -/
private abbrev AbCochain :=
  CochainComplex AddCommGrpCat ℤ

/-- The unbounded derived category of abelian groups. -/
private abbrev AbDerived :=
  DerivedCategory AddCommGrpCat

-- Proof sketch: the standard triangle
-- `Q(C(\beta)[-1]) ⟶ Q(I(Z) \oplus I(Y)) ⟶ Q(I(E)) ⟶ Q(C(\beta)[-1])[1]`
-- is distinguished by `DerivedCategory.mappingCocone_triangle_distinguished β`. If
-- `Q(c)` is an isomorphism, transport that distinguished triangle across the induced triangle
-- isomorphism whose first component is `Q(c)` and whose other two components are identities.
/-- Lemma 21.26.1: if the canonical comparison map
`c^K_{X,Z,Y,E} : \mathcal I^\bullet(X) \to C(\beta)^\bullet[-1]` is an isomorphism in the derived
category of abelian groups, then the induced triangle
`R\Gamma(X,K) \to R\Gamma(Z,K) \oplus R\Gamma(Y,K) \to R\Gamma(E,K) \to R\Gamma(X,K)[1]`
is distinguished. Here the first arrow is the composite of the comparison map with the canonical
projection `C(\beta)^\bullet[-1] \to \mathcal I^\bullet(Z) \oplus \mathcal I^\bullet(Y)`. -/
theorem derived_mayer_vietoris_triangle_of_comparison_distinguished
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (Q.map c)] :
    Triangle.mk
        (Q.map (c ≫ mappingCocone.fst β))
        (Q.map β)
        ((Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫ (asIso (Q.map c)).inv⟦(1 : ℤ)⟧') ∈
      distTriang AbDerived := by
  let T : Triangle AbDerived :=
    Triangle.mk
      (Q.map (c ≫ mappingCocone.fst β))
      (Q.map β)
      ((Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫ (asIso (Q.map c)).inv⟦(1 : ℤ)⟧')
  let e : Q.obj IX ≅ Q.obj (mappingCocone β) := asIso (Q.map c)
  change T ∈ distTriang AbDerived
  refine isomorphic_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished β) _ ?_
  refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [T, e, Functor.map_comp]
  · simp [T]
  · simp [T, e]

-- Proof sketch: when both `Q(c₁)` and `Q(c₂)` are isomorphisms to the same mapping cocone, their
-- sources are canonically isomorphic in `D(\mathbf Z)` via
-- `asIso (Q.map c₁) ≪≫ (asIso (Q.map c₂)).symm`. Rewriting gives an isomorphism of the arrows
-- into the fixed target `Q(C(\beta)[-1])`.
/-- If two comparison maps into the same mapping cocone both become isomorphisms in
`D(\mathbf Z)`, then they determine isomorphic arrows into that fixed mapping cocone. This
records the common-target special case of the independence-of-resolution statement in the source.
-/
theorem comparison_choices_yield_isomorphic_arrows
    {IX₁ IX₂ IZY IE : AbCochain} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β)
    (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (Q.map c₁)] [IsIso (Q.map c₂)] :
    Q.map c₁ = ((asIso (Q.map c₁)) ≪≫ (asIso (Q.map c₂)).symm).hom ≫ Q.map c₂ := by
  simp

end

/-! ### Lemma_21_26_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

-- Proof sketch: apply the localization functor `K(\mathcal A) ⥤ D(\mathcal A)` at
-- quasi-isomorphisms to the given morphism of distinguished triangles. The first two components
-- become isomorphisms, so Lemma `13.4.3` in its canonical mathlib form
-- `Pretriangulated.isIso₃_of_isIso₁₂` forces the third component to become an isomorphism as
-- well. Translating back across the localization identifies that third component as a
-- quasi-isomorphism.
/-- If the first two components of a morphism of distinguished triangles in `K(\mathcal A)` are
quasi-isomorphisms, then the third component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₃_of_quasiIso_hom₁_hom₂
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₂ : Qis φ.hom₂) :
    Qis φ.hom₃ := sorry

-- Proof sketch: apply the localization `K(\mathcal A) ⥤ D(\mathcal A)` to the morphism of
-- distinguished triangles. The first and third components become isomorphisms, hence the second
-- component is an isomorphism by `Pretriangulated.isIso₂_of_isIso₁₃`. By the characterization of
-- the localization at quasi-isomorphisms, this means that the original second component is a
-- quasi-isomorphism.
/-- If the first and third components of a morphism of distinguished triangles in `K(\mathcal A)`
are quasi-isomorphisms, then the second component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₂_of_quasiIso_hom₁_hom₃
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₁ : Qis φ.hom₁) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₂ := sorry

-- Proof sketch: localize the morphism of distinguished triangles to `D(\mathcal A)`, where the
-- second and third components become isomorphisms. Then `Pretriangulated.isIso₁_of_isIso₂₃`
-- gives that the first localized component is an isomorphism, and the defining property of the
-- localization translates this back to quasi-isomorphism of the original first component.
/-- If the second and third components of a morphism of distinguished triangles in `K(\mathcal A)`
are quasi-isomorphisms, then the first component is a quasi-isomorphism. -/
theorem triangleMorphism_quasiIso_hom₁_of_quasiIso_hom₂_hom₃
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom)
    (h₂ : Qis φ.hom₂) (h₃ : Qis φ.hom₃) :
    Qis φ.hom₁ := sorry

-- Proof sketch: combine the three directional two-out-of-three lemmas above. For the Mayer-
-- Vietoris comparison morphism whose components are the maps `c^{K_i}_{X,Z,Y,E}`, these three
-- clauses say exactly that if two of the comparison maps are quasi-isomorphisms, then so is the
-- third.
/-- Lemma 21.26.2: for the morphism of distinguished triangles in `K(\mathcal A)` whose
components are the comparison maps `c^{K_i}_{X,Z,Y,E}`, the three component maps satisfy
two-out-of-three for quasi-isomorphisms; equivalently, the conditions that the first, second, and
third comparison maps are quasi-isomorphisms are all equivalent. -/
theorem triangleMorphism_quasiIso_tfae_of_distinguished
    {T T' : Triangle KHom} (φ : T ⟶ T')
    (hT : T ∈ distTriang KHom) (hT' : T' ∈ distTriang KHom) :
    List.TFAE [Qis φ.hom₁, Qis φ.hom₂, Qis φ.hom₃] := sorry

end

end CategoryTheory

/-! ### Lemma_21_26_3 (from Chap21) -/
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

/-! ### Lemma_21_26_4 (from Chap21) -/
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
