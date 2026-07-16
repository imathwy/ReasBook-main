import StacksProject_2024.stacks_project.Chap31.Definition_31_14_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` did not surface a divisor-specific owner for
-- `\mathcal O_S(D_1) \otimes \mathcal O_S(D_2) \cong \mathcal O_S(D)`. This file therefore uses
-- the Chapter 31 ideal-sheaf owner already chosen for `\mathcal O_S(D)`, namely a subobject of
-- `\mathcal O_S` whose underlying module is invertible.

variable {S : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules S.ringCatSheaf)]
variable [SymmetricCategory (SheafOfModules S.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules S.ringCatSheaf)]

local notation "ModS" => SheafOfModules S.ringCatSheaf
local notation "𝒪S" => (SheafOfModules.unit S.ringCatSheaf : ModS)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModS)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪S ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

/-- The multiplication morphism from the tensor product of two ideal sheaves into
`\mathcal O_S`. -/
noncomputable def effectiveCartierDivisorNegSheafMul
    (I₁ I₂ : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)] :
    (effectiveCartierDivisorNegSheaf I₁ ⊗ₘ effectiveCartierDivisorNegSheaf I₂ : ModS) ⟶ 𝒪S :=
  let η : 𝒪S ≅ 𝟙_ ModS := SheafOfModules.unitIsoTensorUnit
  tensorHom (I₁.arrow ≫ η.hom) (I₂.arrow ≫ η.hom) ≫
    (λ_ (𝟙_ ModS)).hom ≫ η.inv

/-- The tensor of the canonical sections `1_{D_1}` and `1_{D_2}` as a global section of
`\mathcal O_S(D_1) \otimes_{\mathcal O_S} \mathcal O_S(D_2)`. -/
noncomputable def effectiveCartierDivisorTensorCanonicalSection
    (I₁ I₂ : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)] :
    ((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
        (effectiveCartierDivisorAssociatedSheaf I₂) : ModS).sections :=
  let η : 𝒪S ≅ 𝟙_ ModS := SheafOfModules.unitIsoTensorUnit
  (((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
      (effectiveCartierDivisorAssociatedSheaf I₂) : ModS)).unitHomEquiv
    (η.hom ≫ (λ_ (𝟙_ ModS)).inv ≫
      tensorHom
        (η.inv ≫
          (effectiveCartierDivisorAssociatedSheaf I₁).unitHomEquiv.symm
            (effectiveCartierDivisorCanonicalSection I₁))
        (η.inv ≫
          (effectiveCartierDivisorAssociatedSheaf I₂).unitHomEquiv.symm
            (effectiveCartierDivisorCanonicalSection I₂)))

/-- The comparison property from Lemma 31.14.4: an isomorphism
`\mathcal O_S(D_1) \otimes_{\mathcal O_S} \mathcal O_S(D_2) \cong \mathcal O_S(D)` carries the
tensor of the canonical sections `1_{D_1} \otimes 1_{D_2}` to `1_D`. -/
abbrev IsAssociatedSheafTensorIsoOfSum
    (I₁ I₂ I : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)]
    [Fact (EffectiveCartierIdeal I)]
    (e :
      ((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
          (effectiveCartierDivisorAssociatedSheaf I₂) : ModS) ≅
        effectiveCartierDivisorAssociatedSheaf I) : Prop :=
  SheafOfModules.sectionsMap e.hom
      (effectiveCartierDivisorTensorCanonicalSection I₁ I₂) =
    effectiveCartierDivisorCanonicalSection I

/-- Lemma 31.14.4: if `D = D_1 + D_2` is the sum of two effective Cartier divisors on `S`, then
there is a unique isomorphism
`\mathcal O_S(D_1) \otimes_{\mathcal O_S} \mathcal O_S(D_2) \to \mathcal O_S(D)` sending
`1_{D_1} \otimes 1_{D_2}` to `1_D`. Here the divisors are represented by their ideal sheaf
subobjects `I₁`, `I₂`, and `I`, and the hypothesis `negSheafIso` records that the ideal sheaf
of `D` is the product of the ideal sheaves of `D_1` and `D_2`. -/
@[stacks 02OP]
theorem existsUnique_associatedSheafTensorIso_of_sum
    (I₁ I₂ I : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)]
    [Fact (EffectiveCartierIdeal I)]
    (negSheafIso :
      effectiveCartierDivisorNegSheaf I ≅
        (effectiveCartierDivisorNegSheaf I₁ ⊗ₘ effectiveCartierDivisorNegSheaf I₂ : ModS))
    (hmul : negSheafIso.hom ≫ effectiveCartierDivisorNegSheafMul I₁ I₂ = I.arrow) :
    ∃! e :
      ((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
          (effectiveCartierDivisorAssociatedSheaf I₂) : ModS) ≅
        effectiveCartierDivisorAssociatedSheaf I,
      IsAssociatedSheafTensorIsoOfSum I₁ I₂ I e := sorry

/-- Companion to `existsUnique_associatedSheafTensorIso_of_sum`: the required isomorphism exists
as soon as the ideal sheaf of `D` is identified with the product of the ideal sheaves of `D_1`
and `D_2` in a way compatible with multiplication into `\mathcal O_S`. -/
theorem exists_associatedSheafTensorIso_of_sum
    (I₁ I₂ I : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)]
    [Fact (EffectiveCartierIdeal I)]
    (negSheafIso :
      effectiveCartierDivisorNegSheaf I ≅
        (effectiveCartierDivisorNegSheaf I₁ ⊗ₘ effectiveCartierDivisorNegSheaf I₂ : ModS))
    (hmul : negSheafIso.hom ≫ effectiveCartierDivisorNegSheafMul I₁ I₂ = I.arrow) :
    ∃ e :
      ((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
          (effectiveCartierDivisorAssociatedSheaf I₂) : ModS) ≅
        effectiveCartierDivisorAssociatedSheaf I,
      IsAssociatedSheafTensorIsoOfSum I₁ I₂ I e := by
  rcases existsUnique_associatedSheafTensorIso_of_sum I₁ I₂ I negSheafIso hmul with
    ⟨e, he, -⟩
  exact ⟨e, he⟩

/-- Companion to `existsUnique_associatedSheafTensorIso_of_sum`: the image of
`1_{D_1} \otimes 1_{D_2}` determines the comparison isomorphism uniquely. -/
theorem associatedSheafTensorIso_of_sum_unique
    (I₁ I₂ I : Subobject 𝒪S)
    [Fact (EffectiveCartierIdeal I₁)]
    [Fact (EffectiveCartierIdeal I₂)]
    [Fact (EffectiveCartierIdeal I)]
    (negSheafIso :
      effectiveCartierDivisorNegSheaf I ≅
        (effectiveCartierDivisorNegSheaf I₁ ⊗ₘ effectiveCartierDivisorNegSheaf I₂ : ModS))
    (hmul : negSheafIso.hom ≫ effectiveCartierDivisorNegSheafMul I₁ I₂ = I.arrow)
    (e e' :
      ((effectiveCartierDivisorAssociatedSheaf I₁) ⊗ₘ
          (effectiveCartierDivisorAssociatedSheaf I₂) : ModS) ≅
        effectiveCartierDivisorAssociatedSheaf I)
    (he : IsAssociatedSheafTensorIsoOfSum I₁ I₂ I e)
    (he' : IsAssociatedSheafTensorIsoOfSum I₁ I₂ I e') :
    e = e' := by
  rcases existsUnique_associatedSheafTensorIso_of_sum I₁ I₂ I negSheafIso hmul with
    ⟨e₀, he₀, huniq⟩
  calc
    e = e₀ := huniq e he
    _ = e' := (huniq e' he').symm

end AlgebraicGeometry.Scheme
