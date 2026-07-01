import Mathlib

open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable (DC : Type u) [Category.{v} DC]
variable (DC' : Type u) [Category.{v} DC']
variable (DD : Type u) [Category.{v} DD]
variable (DD' : Type u) [Category.{v} DD']

variable [MonoidalCategory DC]
variable [BraidedCategory DC]
variable [MonoidalClosed DC]
variable [MonoidalCategory DC']
variable [BraidedCategory DC']
variable [MonoidalClosed DC']

variable (leftDerivedPullback_h : DC ⥤ DC')
variable (leftDerivedPullback_g : DD ⥤ DD')
variable (leftDerivedPullback_f : DD ⥤ DC)
variable (leftDerivedPullback_f' : DD' ⥤ DC')
variable (rightDerivedPushforward_f : DC ⥤ DD)
variable (rightDerivedPushforward_f' : DC' ⥤ DD')

/-- Remark 21.35.12: for a commutative square of ringed topoi, encoded here by the four derived
categories `D(\mathcal O_\mathcal C)`, `D(\mathcal O_{\mathcal C'})`, `D(\mathcal O_\mathcal D)`,
`D(\mathcal O_{\mathcal D'})`, chosen derived pullbacks `Lh^*`, `Lg^*`, `Lf^*`, `L(f')^*`,
chosen derived pushforwards `Rf_*`, `R(f')_*`, the pullback comparison
`Lh^* R\mathcal H\!\mathit{om}(K,L) \to R\mathcal H\!\mathit{om}(Lh^*K,Lh^*L)` from
Remark `21.35.11`, and a commutativity isomorphism `L(f')^* ∘ Lg^* ≅ Lh^* ∘ Lf^*`, there is a
canonical base-change morphism
`Lg^* Rf_* R\mathcal H\!\mathit{om}(K, L) ⟶
R(f')_* R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def derivedPushforwardInternalHomBaseChangeMap
    (internalHomPullbackComparison_h :
      ∀ (K L : DC),
        leftDerivedPullback_h.obj ((ihom K).obj L) ⟶
          (ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)) ⟶
      rightDerivedPushforward_f'.obj
        ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L)) :=
  (adj_f'.homEquiv
      (leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)))
      ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L)))
    ((hpull.app (rightDerivedPushforward_f.obj ((ihom K).obj L))).hom ≫
      leftDerivedPullback_h.map (adj_f.counit.app ((ihom K).obj L)) ≫
      internalHomPullbackComparison_h K L)

-- Proof sketch: by definition, transpose across the adjunction `L(f')^* ⊣ R(f')_*` the
-- composite obtained from the pullback commutativity isomorphism
-- `L(f')^* Lg^* ≅ Lh^* Lf^*`, then the counit `Lf^* Rf_* → id`, and finally the internal-Hom
-- pullback comparison from Remark `21.35.11`.
/-- Applying the adjunction `L(f')^* ⊣ R(f')_*` to
`derivedPushforwardInternalHomBaseChangeMap` recovers the composite used to define it. -/
theorem derivedPushforwardInternalHomBaseChangeMap_spec
    (internalHomPullbackComparison_h :
      ∀ (K L : DC),
        leftDerivedPullback_h.obj ((ihom K).obj L) ⟶
          (ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    (adj_f'.homEquiv
        (leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj ((ihom K).obj L)))
        ((ihom (leftDerivedPullback_h.obj K)).obj (leftDerivedPullback_h.obj L))
        ).symm
        (derivedPushforwardInternalHomBaseChangeMap
          DC DC' DD DD'
          leftDerivedPullback_h leftDerivedPullback_g
          leftDerivedPullback_f leftDerivedPullback_f'
          rightDerivedPushforward_f rightDerivedPushforward_f'
          internalHomPullbackComparison_h hpull adj_f adj_f' K L) =
      (hpull.app (rightDerivedPushforward_f.obj ((ihom K).obj L))).hom ≫
        leftDerivedPullback_h.map (adj_f.counit.app ((ihom K).obj L)) ≫
        internalHomPullbackComparison_h K L := sorry

end

end SheafOfModules.RingedSite
