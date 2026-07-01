import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- Restriction of `\mathcal O_X`-modules to the open subspace `U`. -/
abbrev moduleSheafRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Modules X ⥤ Modules (X.restrict U.isOpenEmbedding) :=
  SheafOfModules.pullback
    (⟨Functor.whiskerRight (X.ofRestrict U.isOpenEmbedding).hom.c
        (forget₂ CommRingCat RingCat.{u})⟩ :
      ringCatSheaf X ⟶
        (TopCat.Sheaf.pushforward RingCat.{u} (X.ofRestrict U.isOpenEmbedding).hom.base).obj
          (ringCatSheaf (X.restrict U.isOpenEmbedding)))

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- Restriction to an open subspace is additive on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_additive :
    (moduleSheafRestrictionToOpen X U).Additive := sorry

/-- Restriction to an open subspace preserves finite limits on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen X U) := sorry

/-- Restriction to an open subspace preserves finite colimits on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen X U) := sorry

/-- The derived category `D(\mathcal O_U)` attached to the open subspace `U \subset X`. -/
abbrev moduleDerivedOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (Modules (X.restrict U.isOpenEmbedding))

/-- Restriction of a derived `\mathcal O_X`-module to the open subspace `U`. -/
abbrev moduleRestrictionToOpenDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (Modules X) ⥤ moduleDerivedOnOpen X U :=
  Functor.mapDerivedCategory (moduleSheafRestrictionToOpen X U)

/-- The open subset of the restricted ringed space `X|_V` cut out by an inclusion `U \subseteq V`.
-/
abbrev openSubsetOfLE {X : RingedSpace.{u}} {U V : Opens X.carrier} (_h : U ≤ V) :
    Opens ((X.restrict V.isOpenEmbedding : RingedSpace).carrier) :=
  (Opens.map V.inclusion').obj U

-- Restriction along `U ⊆ V` is implemented by first restricting to `V` and then transporting the
-- codomain back to the direct open subspace `U`.
-- Proof sketch: both sides are the derived categories of the same restricted ringed space; the
-- two presentations differ only by whether one first restricts to `V` and then to the open cut
-- out by `U ⊆ V`, or restricts directly to `U`.
/-- Identifies the derived category of `U` inside `X|_V` with the derived category of `U` inside
`X`. -/
theorem nested_moduleDerivedOnOpen_eq (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    moduleDerivedOnOpen (X.restrict V.isOpenEmbedding) (openSubsetOfLE h) =
      moduleDerivedOnOpen X U := sorry

-- Proof sketch: apply `nested_moduleDerivedOnOpen_eq` to the codomain of the restriction functor
-- from `X|_V` to `U`, leaving the domain unchanged.
/-- The functor type of restriction from `V` to `U` matches the direct `D(\mathcal O_V) ⥤
D(\mathcal O_U)` interface. -/
theorem derivedRestrictionBetweenOpens_type_eq
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    (moduleDerivedOnOpen X V ⥤
      moduleDerivedOnOpen (X.restrict V.isOpenEmbedding) (openSubsetOfLE h)) =
        (moduleDerivedOnOpen X V ⥤ moduleDerivedOnOpen X U) := sorry

/-- Restriction on derived categories along an inclusion `U \subseteq V` of open subsets of a
ringed space. -/
abbrev derivedRestrictionBetweenOpens
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    moduleDerivedOnOpen X V ⥤ moduleDerivedOnOpen X U :=
  cast (derivedRestrictionBetweenOpens_type_eq X h)
    (moduleRestrictionToOpenDerived (X.restrict V.isOpenEmbedding) (openSubsetOfLE h))

/-- The derived Ext group `\operatorname{Ext}^i(A, B)` on an open subspace, written as morphisms
`A \to B[i]` in the derived category. -/
abbrev derivedExtGroupOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier)
    (A B : moduleDerivedOnOpen X U) (i : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (A ⟶ B⟦i⟧)

-- Proof sketch: restricting from `W` to `V` and then from `V` to `U` yields the same restricted
-- ringed space as restricting directly from `W` to `U`, so the two derived restriction objects
-- coincide after transport across the identification of codomains.
/-- Iterated restriction along `U \subseteq V \subseteq W` gives the same restricted object as
direct restriction from `W` to `U`. -/
theorem nestedRestriction_obj_eq
    (X : RingedSpace.{u}) {U V W : Opens X.carrier} (hUV : U ≤ V) (hVW : V ≤ W)
    (K : moduleDerivedOnOpen X W) :
    (derivedRestrictionBetweenOpens X hUV).obj ((derivedRestrictionBetweenOpens X hVW).obj K) =
      ((derivedRestrictionBetweenOpens X (hUV.trans hVW)).obj K) := sorry

-- Proof sketch: this is the special case of `nestedRestriction_obj_eq` where the first step comes
-- from restricting a global derived object to `V`; the resulting object on `U` agrees with direct
-- restriction from `X` to `U`.
/-- Restricting a global derived object first to `V` and then to `U` agrees with direct
restriction to `U`. -/
theorem globalRestriction_obj_eq
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V)
    (K : DerivedCategory (Modules X)) :
    (derivedRestrictionBetweenOpens X h).obj ((moduleRestrictionToOpenDerived X V).obj K) =
      ((moduleRestrictionToOpenDerived X U).obj K) := sorry

-- Proof sketch: choose K-injective representatives of the local objects and construct compatible
-- extension-by-zero transition morphisms by transfinite recursion. At successor stages, extend
-- across the new open using the given restriction isomorphism. At successor limits, take the
-- filtered colimit of the previously glued complexes and use vanishing of negative self-Ext to
-- identify this colimit with the prescribed local object. A final filtered colimit over the whole
-- well-ordered cover produces the global derived object.
/-- Lemma 20.45.7: for a ringed space `X`, a well-ordered increasing open cover `(W_\alpha)` that
is continuous at successor limits, and a compatible family of objects
`K_\alpha \in D(\mathcal O_{W_\alpha})` with `\operatorname{Ext}^i(K_\alpha, K_\alpha) = 0` for
`i < 0`, there exists an object `K \in D(\mathcal O_X)` whose restriction to each `W_\alpha` is
identified with `K_\alpha` and is compatible with the given restriction isomorphisms. -/
theorem exists_glued_derived_object_of_wellOrdered_open_cover
    {X : RingedSpace.{u}} {E : Type v} [LinearOrder E] [SuccOrder E] [WellFoundedLT E]
    (W : E → Opens X.carrier) (hcover : iSup W = ⊤) (hmono : Monotone W)
    (hlimit : ∀ ⦃α : E⦄, Order.IsSuccLimit α → W α = ⨆ β : Set.Iio α, W β.1)
    (Kα : ∀ α : E, moduleDerivedOnOpen X (W α))
    (hExt : ∀ α : E, ∀ i : ℤ, i < 0 → IsZero (derivedExtGroupOnOpen X (W α) (Kα α) (Kα α) i))
    (rho : ∀ {β α : E} (hβα : β < α),
      ((derivedRestrictionBetweenOpens X (hmono hβα.le)).obj (Kα α)) ≅ Kα β)
    (hrho : ∀ {γ β α : E} (hγβ : γ < β) (hβα : β < α),
      Eq.mp
        (congrArg (fun T ↦ T ⟶ Kα γ)
          (nestedRestriction_obj_eq X (hmono hγβ.le) (hmono hβα.le) (Kα α)))
        ((derivedRestrictionBetweenOpens X (hmono hγβ.le)).map (rho hβα).hom ≫
          (rho hγβ).hom) =
            (rho (lt_trans hγβ hβα)).hom) :
    ∃ (K : DerivedCategory (Modules X))
      (iso : ∀ α : E,
        ((moduleRestrictionToOpenDerived X (W α)).obj K) ≅ Kα α),
      ∀ {β α : E} (hβα : β < α),
        Eq.mp
          (congrArg (fun T ↦ T ⟶ Kα β)
            (globalRestriction_obj_eq X (hmono hβα.le) K))
          ((derivedRestrictionBetweenOpens X (hmono hβα.le)).map (iso α).hom ≫
            (rho hβα).hom) =
              (iso β).hom := sorry

end AlgebraicGeometry.RingedSpace
