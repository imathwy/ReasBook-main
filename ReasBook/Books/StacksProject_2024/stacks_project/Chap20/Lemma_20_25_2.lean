import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]

/- Domain-style sampling for Lemma 20.25.2:
- primary domain: Čech-to-derived-global-sections comparison for bounded-below complexes of
  `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `moduleCechDerivedFunctor`,
  `boundedBelowDerivedSectionsAtOpen`,
  `Functor.totalRightDerived`,
  `exists_moduleCechToDerivedGlobalSections`,
  `IsModuleCechToDerivedGlobalSectionsComparison`,
  `exists_moduleCechToDerivedGlobalSectionsSpectralSequence`;
- best owner abstraction: the canonical functors
  `moduleCechDerivedFunctor X 𝒰` and the canonical bounded-below derived-sections owner
  `boundedBelowDerivedSectionsAtOpen (X := X) (⊤ : Opens X.carrier)`, with this file keeping only
  the source-facing objectwise comparison theorem under the acyclicity hypothesis.

Source/core/bridge triage:
- `source-facing`: the objectwise isomorphism
  `Tot(Čech^•(𝒰, K)) ≅ RΓ(X, K)` under the vanishing-on-intersections hypothesis;
- `core/canonical`: `moduleCechDerivedFunctor X 𝒰`,
  `boundedBelowDerivedSectionsAtOpen (X := X) (⊤ : Opens X.carrier)`,
  `Functor.totalRightDerived` on
  `mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X)`, the comparison
  predicate
  `IsModuleCechToDerivedGlobalSectionsComparison X 𝒰`, and the spectral-sequence owners from
  `Lemma_20_25_1`;
- `bridge/view`: the passage from a module to its underlying additive sheaf on each Čech
  intersection via the canonical owner `moduleUnderlyingSheaf`.

Primitive data versus derived API:
- primitive data: the cover `𝒰`, the cover equality `h𝒰`, the bounded-below complex `K`, and the
  vanishing hypothesis on the terms of `K` over each finite Čech intersection;
- derived API: the source-facing theorem `Lemma 20.25.2`, stating that any comparison morphism
  with the injective-case computation property from `Lemma_20_25_1` is an isomorphism on `K`,
  together with the thin existential corollary obtained by choosing such a comparison from
  `exists_moduleCechToDerivedGlobalSections`. No extra local comparison morphism owner is
  introduced.
-/

section

variable (𝒰 : ι → Opens X.carrier)

local notation "Kplus" => CochainComplex.Plus X.Modules
local notation "CechF" => moduleCechDerivedFunctor X 𝒰
local notation "QplusModX" =>
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 (RingedSpace.Modules X))
local notation "KplusToDplusModX" =>
  HomotopyCategory.Plus.quotient (RingedSpace.Modules X) ⋙ QplusModX
local notation "RΓplus" =>
  boundedBelowDerivedGlobalSections X
local notation "AbSheaf" => moduleUnderlyingSheaf X

/-- The terms of `K` are cohomologically acyclic on every finite Čech intersection of `𝒰`. -/
def acyclicOnIntersections (K : Kplus) : Prop :=
  ∀ (i : ℕ) (_ : 0 < i) (p : ℕ) (σ : Fin (p + 1) → ι) (q : ℤ),
    IsZero (((AbSheaf).obj (K.obj.X q)).H' i (cechIntersection 𝒰 σ))

-- Proof sketch: apply the Čech-to-hypercohomology spectral sequence from Lemma `20.25.1`. The
-- hypothesis says that for every fixed internal degree `q`, the higher cohomology of `K.X q` on
-- every finite intersection of the cover vanishes, so the spectral sequence is concentrated on the
-- `p = 0` row. Therefore any comparison of Lemma `20.25.1` is an isomorphism on `K`.
/-- Lemma 20.25.2: if `τ` is a comparison morphism of Lemma `20.25.1` and every
positive-degree cohomology group of each term `K.obj.X q` vanishes on every finite intersection of
the open cover `𝒰`, then `τ.app K` is an isomorphism. -/
@[stacks 0FLH]
instance isIso_app_of_acyclic_on_intersections
    (τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus)
    (K : Kplus)
    (hτ : IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (hacyclic : acyclicOnIntersections 𝒰 K) :
    IsIso (τ.app K) := by
  sorry

/-- Companion corollary to Lemma `20.25.2`: one may choose a comparison morphism of
Lemma `20.25.1` whose component at `K` is an isomorphism. -/
theorem exists_moduleCechToDerivedGlobalSections_isIso_app_of_acyclic_on_intersections
    (h𝒰 : iSup 𝒰 = ⊤)
    (K : Kplus)
    (hacyclic : acyclicOnIntersections 𝒰 K) :
    ∃ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧ IsIso (τ.app K) := by
  obtain ⟨τ, hτ⟩ := exists_moduleCechToDerivedGlobalSections X 𝒰 h𝒰
  exact ⟨τ, hτ, isIso_app_of_acyclic_on_intersections 𝒰 τ K hτ hacyclic⟩

end

end AlgebraicGeometry.RingedSpace
