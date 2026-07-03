import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]

/-- The pullback functor on derived categories induced by an exact pullback on module sheaves. -/
private noncomputable abbrev modulePullbackDerivedOfExact
    {A B : RingedSite.{u, v}} (h : RingedSite.Hom A B)
    [h.modulePullback.Additive]
    (hexact : CategoryTheory.exactFunctor (ModuleCat B) (ModuleCat A) h.modulePullback) :
    ModuleDerived B ⥤ ModuleDerived A :=
  let _ : PreservesFiniteLimits h.modulePullback :=
    ((CategoryTheory.exactFunctor_iff h.modulePullback).mp hexact).1
  let _ : PreservesFiniteColimits h.modulePullback :=
    ((CategoryTheory.exactFunctor_iff h.modulePullback).mp hexact).2
  Functor.mapDerivedCategory h.modulePullback

-- Proof sketch: choose K-injective representatives for objects of `D(\mathcal O_\mathcal C)`.
-- Exactness of `(g')^*` lets the left composite be computed by first applying `(g')^*` on the
-- chosen representative, and the source hypothesis identifies the resulting underived composite
-- with `g^* \circ f_*`. Exactness of `g^*` then upgrades this objectwise comparison to a natural
-- isomorphism of the two derived composites.
/-- Lemma 21.37.6: for a commutative square of ringed topoi
`\xymatrix{
(\operatorname{Sh}(\mathcal C'), \mathcal O_{\mathcal C'}) \ar[r]^{g'} \ar[d]_{f'} &
(\operatorname{Sh}(\mathcal C), \mathcal O_{\mathcal C}) \ar[d]^{f} \\
(\operatorname{Sh}(\mathcal D'), \mathcal O_{\mathcal D'}) \ar[r]_{g} &
(\operatorname{Sh}(\mathcal D), \mathcal O_{\mathcal D})
}`
in the situation where the underived module square satisfies
`f'_* \circ (g')^* = g^* \circ f_*` and the pullback functors along `g` and `g'` are exact on
module sheaves, the induced derived functors satisfy the canonical functor isomorphism
`Rf'_* \circ (g')^* \cong g^* \circ Rf_*`. This is the library-facing form of the textbook
equality of functors on `D(\mathcal O_{\mathcal C})`. -/
theorem derived_pushforward_pullback_iso_of_exact_pullback_square
    (hunderived :
      g'.modulePullback ⋙ f'.modulePushforward =
        f.modulePushforward ⋙ g.modulePullback)
    (hexact_g :
      CategoryTheory.exactFunctor (ModuleCat Y) (ModuleCat Y') g.modulePullback)
    (hexact_g' :
      CategoryTheory.exactFunctor (ModuleCat X) (ModuleCat X') g'.modulePullback) :
    ∃ comparison :
      modulePullbackDerivedOfExact g' hexact_g' ⋙ modulePushforwardDerived f' ⟶
        modulePushforwardDerived f ⋙ modulePullbackDerivedOfExact g hexact_g,
      IsIso comparison := sorry

end

end RingedSite.Hom
