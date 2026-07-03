import Mathlib
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap20.Lemma_20_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The Čech complex functor on presheaves of `\mathcal O_X`-modules is additive. -/
noncomputable instance ringedSpaceModuleCechComplexFunctor_additive :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).Additive := sorry

/-- The Čech complex functor on presheaves of `\mathcal O_X`-modules preserves zero morphisms. -/
instance ringedSpaceModuleCechComplexFunctor_preservesZeroMorphisms :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).PreservesZeroMorphisms := inferInstance

/-- The degree-`n` Čech cohomology functor on presheaves of `\mathcal O_X`-modules for the cover
`𝒰`. -/
abbrev ringedSpaceCechCohomologyDegree (n : ℕ) :
    ringedSpacePresheafModules X ⥤+ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  AdditiveFunctor.of
    (ringedSpaceModuleCechComplexFunctor U 𝒰 ⋙
      HomologicalComplex.homologyFunctor
        (ModuleCat.{u} (X.presheaf.obj (op U))) (ComplexShape.up ℕ) n)

-- Proof sketch: apply Lemma `20.10.1`, which states that
-- `ringedSpaceModuleCechComplexFunctor U 𝒰` is exact. In an abelian category, exact functors send
-- short exact sequences to short exact sequences.
/-- A short exact sequence of presheaves of `\mathcal O_X`-modules induces a short exact sequence
of Čech complexes of `\mathcal O_X(U)`-modules. -/
theorem ringedSpaceCechComplex_map_shortExact
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) :
    (S.map (ringedSpaceModuleCechComplexFunctor U 𝒰)).ShortExact := sorry

/-- The connecting morphism in degree `n` for the Čech cohomology of a short exact sequence of
presheaves of `\mathcal O_X`-modules. -/
noncomputable def ringedSpaceCechCohomologyConnectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.obj S.X₃ ⟶
      (ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.obj S.X₁ :=
  (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

-- Proof sketch: by construction
-- `ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n` is the boundary morphism in the long
-- exact homology sequence of the short exact sequence of Čech complexes from
-- `ringedSpaceCechComplex_map_shortExact U 𝒰 hS`.
/-- The Čech cohomology connecting morphism is the boundary map of the mapped short exact sequence
of Čech complexes. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_def
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n =
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl) := sorry

-- Proof sketch: use the leftmost exactness statement of the homology long exact sequence attached
-- to the short exact sequence of Čech complexes from `ringedSpaceCechComplex_map_shortExact`.
/-- In degree `0`, the map induced by the first arrow of a short exact sequence is a monomorphism
on Čech cohomology. -/
theorem ringedSpaceCechCohomology_mono_map_f_zero
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) :
    Mono ((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.map S.f) := sorry

-- Proof sketch: this is the relation
-- `\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
-- \check H^{n+1}(\mathcal U, S.X₁) = 0`
-- in the long exact homology sequence of the mapped short exact sequence of Čech complexes.
/-- The Čech connecting morphism annihilates the image of the middle map in the long exact
sequence. -/
theorem ringedSpaceCechCohomology_map_g_comp_connectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g ≫
        ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n =
      0 := sorry

-- Proof sketch: this is the next exactness relation in the same long exact homology sequence.
/-- The Čech connecting morphism factors through the kernel of the next map induced by `f`. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_comp_map_f
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n ≫
        (ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f =
      0 := sorry

-- Proof sketch: exactness at the middle term
-- `\check H^n(\mathcal U, S.X₁) ⟶ \check H^n(\mathcal U, S.X₂) ⟶
-- \check H^n(\mathcal U, S.X₃)`
-- in the long exact homology sequence gives the exactness of the mapped short complex.
/-- In every degree, the short complex obtained by applying Čech cohomology is exact. -/
theorem ringedSpaceCechCohomology_map_exact
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (ringedSpaceCechCohomologyDegree U 𝒰 n).obj).Exact := sorry

-- Proof sketch: this is exactness at `\check H^n(\mathcal U, S.X₃)` in the long exact homology
-- sequence of the mapped short exact sequence of Čech complexes.
/-- The short complex
`\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
\check H^{n+1}(\mathcal U, S.X₁)`. -/
abbrev ringedSpaceCechCohomologyMapGConnectingShortComplex
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex (ModuleCat.{u} (X.presheaf.obj (op U))) :=
  ShortComplex.mk
    ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
    (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
    (ringedSpaceCechCohomology_map_g_comp_connectingMorphism U 𝒰 hS n)

/-- The sequence
`\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
\check H^{n+1}(\mathcal U, S.X₁)` is exact. -/
-- Proof sketch: this is exactness at `\check H^n(\mathcal U, S.X₃)` in the long exact homology
-- sequence of the mapped short exact sequence of Čech complexes.
theorem ringedSpaceCechCohomology_exact_map_g_connectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyMapGConnectingShortComplex U 𝒰 hS n).Exact := sorry

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, S.X₁)` in the same long exact
-- homology sequence.
/-- The short complex
`\check H^n(\mathcal U, S.X₃) ⟶ \check H^{n+1}(\mathcal U, S.X₁) ⟶
\check H^{n+1}(\mathcal U, S.X₂)`. -/
abbrev ringedSpaceCechCohomologyConnectingMapFShortComplex
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex (ModuleCat.{u} (X.presheaf.obj (op U))) :=
  ShortComplex.mk
    (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
    ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
    (ringedSpaceCechCohomologyConnectingMorphism_comp_map_f U 𝒰 hS n)

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, S.X₁)` in the same long exact
-- homology sequence.
/-- The sequence
`\check H^n(\mathcal U, S.X₃) ⟶ \check H^{n+1}(\mathcal U, S.X₁) ⟶
\check H^{n+1}(\mathcal U, S.X₂)` is exact. -/
theorem ringedSpaceCechCohomology_exact_connectingMorphism_map_f
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyConnectingMapFShortComplex U 𝒰 hS n).Exact := sorry

/-- The five-term window in the long exact Čech cohomology sequence is exact. -/
theorem ringedSpaceCechCohomology_exact₅
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.g)).Exact :=
  CohomologicalDeltaFunctor.exact₅_of_adjacent_exactness
    (fun {_} hS n ↦ ringedSpaceCechCohomology_map_g_comp_connectingMorphism U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomologyConnectingMorphism_comp_map_f U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_map_exact U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_exact_map_g_connectingMorphism U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_exact_connectingMorphism_map_f U 𝒰 hS n)
    hS n

-- Proof sketch: a morphism of short exact sequences of presheaves of `\mathcal O_X`-modules maps
-- to a morphism of short exact sequences of Čech complexes, and the naturality of the homology
-- boundary morphism gives the resulting commutative square.
/-- The Čech cohomology connecting morphisms are natural in morphisms of short exact sequences of
presheaves of `\mathcal O_X`-modules. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_naturality
    {S T : ShortComplex (ringedSpacePresheafModules X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map φ.τ₃)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hT n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map φ.τ₁) := sorry

/-- Lemma 20.10.2: for an open covering `𝒰` of `U` on a ringed space `X`, the functors
`ℱ ↦ \check H^n(𝒰, ℱ)` form a cohomological `δ`-functor from presheaves of
`\mathcal O_X`-modules to `\mathcal O_X(U)`-modules. -/
noncomputable def ringedSpaceCechCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor
      (ringedSpacePresheafModules X)
      (ModuleCat.{u} (X.presheaf.obj (op U))) where
  F := ringedSpaceCechCohomologyDegree U 𝒰
  δ := fun {_} hS n ↦ ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n
  mono_map_f_zero := fun {_} hS ↦ ringedSpaceCechCohomology_mono_map_f_zero U 𝒰 hS
  exact₅ := fun {_} hS n ↦ ringedSpaceCechCohomology_exact₅ U 𝒰 hS n
  δ_naturality := fun {_ _} hS hT φ n ↦
    ringedSpaceCechCohomologyConnectingMorphism_naturality U 𝒰 hS hT φ n

-- Proof sketch: unfold `ringedSpaceCechCohomologyDeltaFunctor`; the degree-`n` term is defined to
-- be `ringedSpaceCechCohomologyDegree U 𝒰 n`.
/-- The degree-`n` term of the Čech cohomology `δ`-functor is the degree-`n` Čech cohomology
functor. -/
theorem ringedSpaceCechCohomologyDeltaFunctor_F_eq (n : ℕ) :
    (ringedSpaceCechCohomologyDeltaFunctor U 𝒰 n).obj =
      (ringedSpaceCechCohomologyDegree U 𝒰 n).obj := sorry

end AlgebraicGeometry.RingedSpace
