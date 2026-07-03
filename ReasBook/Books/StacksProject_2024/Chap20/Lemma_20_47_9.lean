import Mathlib
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The category of `\mathcal O_U`-modules on the open subset `U \subset X`. -/
abbrev OpenSubsetSheafModules (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

/-- The derived category `D(\mathcal O_U)` on the open subset `U \subset X`. -/
abbrev OpenSubsetModuleDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (OpenSubsetSheafModules X U)

/-- Restriction of `\mathcal O_X`-modules to an open subset. -/
noncomputable abbrev moduleSheafRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ OpenSubsetSheafModules X U :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (RingedSpace.ringCatSheaf X))

/-- Restriction to an open subset is additive on module sheaves. -/
instance moduleSheafRestrictionToOpen_additive {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U).Additive := sorry

/-- Restriction to an open subset preserves finite limits on module sheaves. -/
instance moduleSheafRestrictionToOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U) := sorry

/-- Restriction to an open subset preserves finite colimits on module sheaves. -/
instance moduleSheafRestrictionToOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen U) := sorry

/-- Restriction on derived categories to an open subset. -/
noncomputable abbrev moduleDerivedRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    ModuleDerived X ⥤ OpenSubsetModuleDerived X U :=
  (moduleSheafRestrictionToOpen U).mapDerivedCategory

/-- A complex of modules over a sheaf of rings is strictly perfect if it is bounded and each term
is a retract of a finite free module sheaf. -/
def CochainComplex.IsStrictlyPerfect
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (E : CochainComplex (SheafOfModules R) ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty (Retract (E.X i) (SheafOfModules.free.{u} I : SheafOfModules R))

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`; the right-hand side is exactly the
-- boundedness condition together with the termwise finite-free retract condition.
/-- Unfolding `CochainComplex.IsStrictlyPerfect` yields boundedness together with the requirement
that every term is a retract of a finite free module sheaf. -/
theorem cochainComplex_isStrictlyPerfect_iff
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (E : CochainComplex (SheafOfModules R) ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, ∃ I : Type u, Finite I ∧
          Nonempty (Retract (E.X i) (SheafOfModules.free.{u} I : SheafOfModules R)) := sorry

/-- The cohomology `\mathcal O_X`-module `H^i(K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev derivedCohomologyModule
    (X : RingedSpace.{u}) (K : ModuleDerived X) (i : ℤ) : Modules X :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj K

-- Proof sketch: unfold `derivedCohomologyModule`; it is defined to be the value of the
-- homology functor in degree `i` on the derived object `K`.
/-- Unfolding `derivedCohomologyModule` identifies it with the degree-`i` homology object of `K`
in `\operatorname{Mod}(\mathcal O_X)`. -/
theorem derivedCohomologyModule_def
    (X : RingedSpace.{u}) (K : ModuleDerived X) (i : ℤ) :
    derivedCohomologyModule X K i =
      (DerivedCategory.homologyFunctor (Modules X) i).obj K := sorry

/-- A neighborhoodwise strict-perfect approximation of a derived `\mathcal O_X`-module at a point
`x`, controlling cohomology above degree `m`. -/
structure MPseudoCoherentNeighborhoodApproximation
    {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) (x : X) where
  /-- The chosen open neighborhood of `x`. -/
  U : Opens X.carrier
  /-- The chosen open contains `x`. -/
  mem_U : x ∈ U
  /-- The strict-perfect complex on the open neighborhood. -/
  complex : CochainComplex (OpenSubsetSheafModules X U) ℤ
  /-- The comparison map from the strict-perfect model to the restriction of `K` to `U`. -/
  hom :
    ((DerivedCategory.Q :
      CochainComplex (OpenSubsetSheafModules X U) ℤ ⥤
        OpenSubsetModuleDerived X U).obj complex) ⟶
      (moduleDerivedRestrictionToOpen U).obj K
  /-- The local model is strictly perfect. -/
  isStrictlyPerfect : CochainComplex.IsStrictlyPerfect complex
  /-- The comparison is an isomorphism on cohomology in degrees strictly above `m`. -/
  isIso_above :
    ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor
        (OpenSubsetSheafModules X U) i).map hom)
  /-- The comparison is surjective on cohomology in degree `m`. -/
  epi_at :
    Epi ((DerivedCategory.homologyFunctor
      (OpenSubsetSheafModules X U) m).map hom)

/-- A derived `\mathcal O_X`-module is `m`-pseudo-coherent if every point admits a neighborhood on
which the restriction is approximated by a strict-perfect complex inducing cohomology
isomorphisms above degree `m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ x : X, Nonempty (MPseudoCoherentNeighborhoodApproximation K m x)

-- Proof sketch: unfold `IsMPseudoCoherent`; it is exactly the pointwise existence of the
-- neighborhoodwise strict-perfect approximations packaged above.
/-- The predicate `IsMPseudoCoherent` is the local existence of strict-perfect approximations with
the required cohomological control above degree `m`. -/
theorem isMPseudoCoherent_iff
    {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherent K m ↔
      ∀ x : X, Nonempty (MPseudoCoherentNeighborhoodApproximation K m x) := sorry

-- Proof sketch: work Zariski-locally on `X`. On a neighborhood of each point, choose the
-- strict-perfect approximation from `hK`, replace it inductively by one concentrated in degrees
-- at most `m`, and identify the top surviving cohomology as a quotient of the degree-`m` term,
-- which is locally a retract of a finite free module sheaf. Local finite generation then glues.
/-- Lemma 20.47.9 (1): if `K` is `m`-pseudo-coherent and `H^i(K) = 0` for `i > m`, then
`H^m(K)` is a finite type `\mathcal O_X`-module. -/
theorem derivedCohomologyModule_isFiniteType_of_isMPseudoCoherent
    {X : RingedSpace.{u}} {K : ModuleDerived X} {m : ℤ}
    (hK : IsMPseudoCoherent K m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (derivedCohomologyModule X K i)) :
    (derivedCohomologyModule X K m).IsFiniteType := sorry

-- Proof sketch: again work locally and choose a strict-perfect approximation from `hK`. Use the
-- stronger vanishing bound to truncate the local model so that only degrees up to `m + 1`
-- remain, then identify `H^{m+1}(K)` with the cokernel of a morphism between finite free local
-- terms. Such cokernels are locally finitely presented, and the local data glue.
/-- Lemma 20.47.9 (2): if `K` is `m`-pseudo-coherent and `H^i(K) = 0` for `i > m + 1`, then
`H^{m + 1}(K)` is a finitely presented `\mathcal O_X`-module. -/
theorem derivedCohomologyModule_isFinitePresentation_of_isMPseudoCoherent
    {X : RingedSpace.{u}} {K : ModuleDerived X} {m : ℤ}
    (hK : IsMPseudoCoherent K m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (derivedCohomologyModule X K i)) :
    (derivedCohomologyModule X K (m + 1)).IsFinitePresentation := sorry

end AlgebraicGeometry.RingedSpace
