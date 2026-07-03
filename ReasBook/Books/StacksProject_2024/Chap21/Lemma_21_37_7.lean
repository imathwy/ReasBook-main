import Mathlib
import stacks_project.Chap21.Remark_21_19_3

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe w u v

namespace RingedSite.Hom

/-- Exactness of the abelian lower shriek attached to a morphism of ringed sites, expressed on the
underlying abelian-sheaf categories by the site-level functor realizing `g_!`. -/
abbrev abelianLowerShriekExact {X Y : RingedSite.{u, v}} (g : RingedSite.Hom X Y) : Prop :=
  CategoryTheory.exactFunctor
    (Sheaf X.siteTopology AddCommGrpCat.{max u v})
    (Sheaf Y.siteTopology AddCommGrpCat.{max u v})
    (g.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology)

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]

-- Proof sketch: use Lemma `18.41.3 (1)` to identify the underived composites
-- `(g')^* ⋙ (f')_*` and `f_* ⋙ g^*` on module sheaves. Then apply the bounded-below
-- right-derived-functor formalism to a bounded-below object. Under the source hypotheses, the
-- derived pullbacks along `g` and `g'` compute the ordinary inverse-image functors on such
-- objects.
/-- Lemma 21.37.7 (1): for a commutative square of ringed topoi presented by ringed-site morphisms
`g'`, `f'`, `f`, and `g` as in `18.41.3`, the bounded-below derived functors satisfy the base
change isomorphism
`Rf'_* \circ (g')^* K \cong g^* \circ Rf_* K`
for every bounded-below object `K` of `D(\mathcal O_\mathcal C)`. This is the objectwise form of
the textbook equality of functors on `D^+(\mathcal O_\mathcal C)`. -/
theorem boundedBelow_derived_pushforward_pullback_object_isomorphic
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (K : ModuleDerived X)
    (hbounded : ∃ n : ℤ, K.IsGE n) :
    IsIsomorphic
      ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K))
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)) := sorry

-- Proof sketch: compute `Rf_*` and `R(f')_*` on K-injective representatives. The additional
-- exactness hypothesis on `g'_!` is the source condition used to ensure that the pullback along
-- `g'` preserves K-injective representatives on the underlying abelian-sheaf categories, so the
-- underived base-change equality from Lemma `18.41.3 (1)` upgrades to the unbounded derived
-- categories.
/-- Lemma 21.37.7 (2): with the same square and hypotheses as in clause (1), if the abelian lower
shriek `g'_! : \mathrm{Ab}(\mathcal C') \to \mathrm{Ab}(\mathcal C)` is exact, then the same base
change comparison holds on the unbounded derived categories. In the library-facing formulation,
this is the unbounded isomorphism
`Rf'_* \circ L(g')^* \cong Lg^* \circ Rf_*`,
which agrees with the textbook statement because the horizontal pullbacks are exact in this
site-presented situation. -/
theorem unbounded_derived_pushforward_pullback_square_iso_of_exact_abelian_lowerShriek
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hexact_g'_shriek : abelianLowerShriekExact g') :
    IsIsomorphic
      (modulePullbackDerived g' ⋙ modulePushforwardDerived f')
      (modulePushforwardDerived f ⋙ modulePullbackDerived g) := sorry

end

end RingedSite.Hom
