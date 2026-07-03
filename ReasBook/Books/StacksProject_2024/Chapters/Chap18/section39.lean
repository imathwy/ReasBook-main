import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_39_1 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')
variable (ℱ : SheafOfModules (ringSheaf JC 𝒪))

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings over a continuous functor of sites. -/
abbrev ringedSiteUnderlyingStructureMap :
    ringSheaf JC 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

-- Proof sketch: reduce to the site-presented case of the textbook proof. The inverse-image
-- module is computed by `SheafOfModules.pullback`; locally it is
-- `\mathcal O_{\mathcal C} \otimes_{f^{-1}\mathcal O_{\mathcal D}} f^{-1}\mathcal F`.
-- First show `f^{-1}\mathcal F` is flat over `f^{-1}\mathcal O_{\mathcal D}` by the local
-- factorization criterion for flatness, then apply the flat base-change statement for extension of
-- scalars along `f^{-1}\mathcal O_{\mathcal D} \to \mathcal O_{\mathcal C}`.
/-- Lemma 18.39.1: in the site-presented formalization of a morphism of ringed topoi or ringed
sites, the pullback `f^*\mathcal F` of a flat `\mathcal O_{\mathcal D}`-module `\mathcal F` is a
flat `\mathcal O_{\mathcal C}`-module. Here `f^*\mathcal F` is the canonical module pullback
`(SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj ℱ`. -/
theorem pullback_isFlat_of_isFlat
    [IsFlat 𝒪 ℱ] :
    IsFlat 𝒪'
      ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj ℱ) := sorry

end

/-! ### Lemma_18_39_2 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (p : GrothendieckTopology.Point J)
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/-- The stalk functor on `\mathcal O`-modules at the point `p`, obtained by forgetting to sheaves
of abelian groups and then applying the point fiber functor. -/
abbrev point_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber

/-- Tensoring on the right by `ℱ` and then taking the stalk at `p`. This is the categorical form
of tensoring with the stalk `ℱ_p`. -/
abbrev point_tensor_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  sheafModuleTensorRightFunctor ℱ ⋙ point_stalk_functor 𝒪 p

/-- Flatness of `ℱ` at the point `p`, expressed as exactness of the tensor-then-stalk functor.
This packages the textbook statement that the stalk `ℱ_p` is flat over the stalk ring
`\mathcal O_p` in the available site-theoretic API. -/
def IsFlatAtPoint : Prop :=
  exactFunctor
    (SheafOfModules (ringSheaf J 𝒪))
    AddCommGrpCat.{u}
    (point_tensor_stalk_functor 𝒪 p ℱ)

-- Proof sketch: flatness of `ℱ` means tensoring with `ℱ` is exact on `\mathcal O`-modules. The
-- point fiber functor `p.sheafFiber` is exact on sheaves of abelian groups, so the composite
-- tensor-then-stalk functor is exact. This is the canonical categorical rendering of the
-- textbook claim that `ℱ_p` is a flat `\mathcal O_p`-module.
/-- Lemma 18.39.2: if `ℱ` is a flat `\mathcal O`-module on a ringed site and `p` is a point of
the site, then `ℱ` is flat at `p`, i.e. the stalkwise tensor functor at `p` is exact. This is
the canonical site-theoretic formulation of the statement that the stalk `ℱ_p` is a flat
`\mathcal O_p`-module. -/
theorem isFlatAtPoint_of_isFlat [IsFlat 𝒪 ℱ] :
    IsFlatAtPoint 𝒪 p ℱ := sorry

end

/-! ### Lemma_18_39_3 (from Chap18) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u w

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {I : Type w}
variable (p : I → GrothendieckTopology.Point J)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

-- Proof sketch: the forward implication is Lemma 18.39.2 applied pointwise. For the converse,
-- flatness means exactness of tensoring with `ℱ`, and exactness of the resulting short complexes
-- of abelian sheaves can be checked on the conservative family `p` by Lemma 18.14.4. The stalk
-- identification for tensor products from Lemma 18.26.2 matches those stalkwise exactness
-- conditions with `IsFlatAtPoint`.
/-- Lemma 18.39.3: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if it is
flat at every point of a conservative family, expressed here by exactness of tensoring with
`\mathcal F` followed by taking the fiber functor at each `p_i`; this is the site-theoretic form
of saying that each stalk `\mathcal F_{p_i}` is a flat `\mathcal O_{p_i}`-module. -/
theorem isFlat_iff_isFlatAtPoint_of_conservativeFamily
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    IsFlat 𝒪 ℱ ↔
      ∀ i : I,
        exactFunctor
          (SheafOfModules (ringSheaf J 𝒪))
          AddCommGrpCat.{u}
          (sheafModuleTensorRightFunctor ℱ ⋙
            SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
              (p i).sheafFiber) := sorry

end

/-! ### Lemma_18_39_4 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪')

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings over a continuous functor of sites. -/
abbrev ringedSiteUnderlyingStructureMap :
    ringSheaf JC 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪') :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

-- Proof sketch: apply exactness of the inverse-image functor to obtain a short exact sequence of
-- `f⁻¹𝒪`-modules, use Lemma `18.39.1` to see that the pulled-back quotient remains flat over
-- `f⁻¹𝒪`, and then apply the short-exactness preservation under tensoring with a flat quotient from
-- Lemma `18.28.9` to the extension-of-scalars description of `f^*`.
/-- Lemma 18.39.4: for a site-presented morphism of ringed topoi or ringed sites, pulling back a
short exact sequence of `\mathcal O`-modules along `f^*` preserves short exactness provided the
quotient term is flat. -/
theorem pullback_shortExact_of_flat_quotient
    (S : ShortComplex (SheafOfModules (ringSheaf JC 𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ))).ShortExact := sorry

end
