import Mathlib
import stacks_project.Chap20.Lemma_20_32_2
import stacks_project.Chap20.Lemma_20_34_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ambient unbounded derived category `D(\mathcal O_X)`. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The unbounded derived category of abelian groups used for derived global sections. -/
abbrev abelianDerived :=
  DerivedCategory AddCommGrpCat.{u}

/-- The derived global-sections functor `RΓ(X, -)` after forgetting the module structure on
`Γ(X, \mathcal O_X)`. -/
abbrev derivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The derived sections functor `RΓ(U, -)` on an open subset `U`, viewed in `D(\mathrm{Ab})`. -/
abbrev derivedSectionsAtOpenToAbelian (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedSectionsAtOpen X U ⋙
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The derived global-sections object `RΓ(X, E)` in `D(\mathrm{Ab})`. -/
abbrev derivedGlobalSectionsObject (X : RingedSpace.{u}) (E : ringedSpaceModuleDerived X) :
    abelianDerived :=
  (derivedGlobalSectionsToAbelian X).obj E

/-- The derived sections object `RΓ(U, E)` in `D(\mathrm{Ab})`. -/
abbrev derivedSectionsAtOpenObject (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  (derivedSectionsAtOpenToAbelian X U).obj E

/-- The middle biproduct `RΓ(U, E) \oplus RΓ(V, E)` in the Mayer-Vietoris triangle. -/
abbrev derivedSectionsBiprodObject (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  derivedSectionsAtOpenObject X U E ⊞ derivedSectionsAtOpenObject X V E

/-- The intersection term `RΓ(U \cap V, E)` in the Mayer-Vietoris triangle. -/
abbrev derivedSectionsIntersectionObject (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  derivedSectionsAtOpenObject X (U ⊓ V) E

/-- The functorial map on the middle biproduct term induced by a morphism in `D(\mathcal O_X)`.
-/
abbrev derivedSectionsBiprodMap {X : RingedSpace.{u}} (U V : Opens X.carrier)
    {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E') :
    derivedSectionsBiprodObject X U V E ⟶ derivedSectionsBiprodObject X U V E' :=
  biprod.map ((derivedSectionsAtOpenToAbelian X U).map φ)
    ((derivedSectionsAtOpenToAbelian X V).map φ)

/-- The hypercohomology object `H^n(X, E)` computed from derived global sections in
`D(\mathrm{Ab})`. -/
abbrev derivedGlobalSectionsCohomology (X : RingedSpace.{u}) (E : ringedSpaceModuleDerived X)
    (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    (derivedGlobalSectionsObject X E)

/-- The hypercohomology object `H^n(U, E)` for an open subset `U`. -/
abbrev derivedSectionsAtOpenCohomology (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    (derivedSectionsAtOpenObject X U E)

/-- The biproduct cohomology object `H^n(U, E) \oplus H^n(V, E)`. -/
abbrev derivedSectionsBiprodCohomology (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  derivedSectionsAtOpenCohomology X U E n ⊞ derivedSectionsAtOpenCohomology X V E n

/-- The cohomology object `H^n(U \cap V, E)` of the intersection term. -/
abbrev derivedSectionsIntersectionCohomology (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  derivedSectionsAtOpenCohomology X (U ⊓ V) E n

section

variable {X : RingedSpace.{u}}

-- Proof sketch: start from the Mayer-Vietoris distinguished triangle of
-- `Lemma_20_33_1` in `D(\mathcal O_X)`, then apply the additive derived global-sections functor
-- of `20_14_1_1` together with the open-section comparison of `Lemma_20_32_2` to rewrite the
-- three vertices as `RΓ(X, E)`, `RΓ(U, E) \oplus RΓ(V, E)`, and `RΓ(U ∩ V, E)` in
-- `D(\mathrm{Ab})`.
/-- Lemma 20.33.4: for a ringed space `(X, \mathcal O_X)` covered by two opens `U` and `V`, every
object `E` of `D(\mathcal O_X)` fits into a distinguished triangle
`RΓ(X, E) ⟶ RΓ(U, E) \oplus RΓ(V, E) ⟶ RΓ(U \cap V, E) ⟶ RΓ(X, E)[1]`
in the derived category of abelian groups. -/
theorem derivedGlobalSections_mayerVietoris_triangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : ringedSpaceModuleDerived X) :
    ∃ α : derivedGlobalSectionsObject X E ⟶ derivedSectionsBiprodObject X U V E,
        ∃ β : derivedSectionsBiprodObject X U V E ⟶
          derivedSectionsIntersectionObject X U V E,
        ∃ δ : derivedSectionsIntersectionObject X U V E ⟶
            (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧,
          Triangle.mk α β δ ∈ distTriang abelianDerived := sorry

-- Proof sketch: apply the homology functors `H^n` and `H^(n + 1)` on `D(\mathrm{Ab})` to the
-- distinguished triangle of `derivedGlobalSections_mayerVietoris_triangle`; the standard long
-- exact homology sequence yields the displayed five-arrow exact segment.
/-- The Mayer-Vietoris distinguished triangle on derived global sections yields the standard
cohomology exact segment
`H^n(X, E) ⟶ H^n(U, E) \oplus H^n(V, E) ⟶ H^n(U \cap V, E) ⟶ H^{n+1}(X, E) ⟶
H^{n+1}(U, E) \oplus H^{n+1}(V, E) ⟶ H^{n+1}(U \cap V, E)`. -/
theorem derivedGlobalSections_mayerVietoris_cohomology_sequence
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : ringedSpaceModuleDerived X) (n : ℤ) :
    ∃ f : derivedGlobalSectionsCohomology X E n ⟶
        derivedSectionsBiprodCohomology X U V E n,
      ∃ g : derivedSectionsBiprodCohomology X U V E n ⟶
          derivedSectionsIntersectionCohomology X U V E n,
        ∃ δ : derivedSectionsIntersectionCohomology X U V E n ⟶
            derivedGlobalSectionsCohomology X E (n + 1),
          ∃ f' : derivedGlobalSectionsCohomology X E (n + 1) ⟶
              derivedSectionsBiprodCohomology X U V E (n + 1),
            ∃ g' : derivedSectionsBiprodCohomology X U V E (n + 1) ⟶
                derivedSectionsIntersectionCohomology X U V E (n + 1),
              (ComposableArrows.mk₅ f g δ f' g').Exact := sorry

-- Proof sketch: choose the triangle maps functorially by applying derived global sections to a
-- functorial K-injective resolution model for `E`. Naturality of the resolution, of restriction
-- to opens, and of the triangle attached to the short exact sequence of complexes gives the three
-- naturality identities.
/-- The Mayer-Vietoris triangle on derived global sections can be chosen functorially in the
derived object `E`. -/
theorem derivedGlobalSections_mayerVietoris_functorial
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) :
    ∃ α : ∀ E : ringedSpaceModuleDerived X,
        derivedGlobalSectionsObject X E ⟶ derivedSectionsBiprodObject X U V E,
      ∃ β : ∀ E : ringedSpaceModuleDerived X,
          derivedSectionsBiprodObject X U V E ⟶
            derivedSectionsIntersectionObject X U V E,
        ∃ δ : ∀ E : ringedSpaceModuleDerived X,
            derivedSectionsIntersectionObject X U V E ⟶
              (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧,
          (∀ E : ringedSpaceModuleDerived X,
            Triangle.mk (α E) (β E) (δ E) ∈ distTriang abelianDerived) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            (derivedGlobalSectionsToAbelian X).map φ ≫ α E' =
              α E ≫ derivedSectionsBiprodMap U V φ) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            derivedSectionsBiprodMap U V φ ≫ β E' =
              β E ≫ (derivedSectionsAtOpenToAbelian X (U ⊓ V)).map φ) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            (derivedSectionsAtOpenToAbelian X (U ⊓ V)).map φ ≫ δ E' =
              δ E ≫
                (shiftFunctor abelianDerived (1 : ℤ)).map
                  ((derivedGlobalSectionsToAbelian X).map φ)) := sorry

end

end AlgebraicGeometry.RingedSpace
