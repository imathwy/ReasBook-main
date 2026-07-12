import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap20.Lemma_20_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomologicalComplex
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]

local notation "ModU" => ModuleCat (X.presheaf.obj (op U))
local notation "PModX" => RingedSpace.PresheafModules X

/- Domain-style sampling for Lemma 20.10.2:
- primary domain: cohomological `δ`-functors obtained from the long exact homology sequence of
  short exact sequences of cochain complexes;
- sampled owner declarations:
  `CategoryTheory.CohomologicalDeltaFunctor`,
  `CategoryTheory.ShortComplex.ShortExact.δ`,
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₁`,
  `HomologicalComplex.HomologySequence.δ_naturality`;
- best owner abstraction:
  `source-facing`: the existence of a cohomological `δ`-functor structure on the degreewise Čech
    cohomology functors associated to the cover `𝒰`;
  `core/canonical`: `CohomologicalDeltaFunctor` together with the homology-sequence owners
    `ShortComplex.ShortExact.δ`, `homology_exact₁`, `homology_exact₂`, `homology_exact₃`, and
    `HomologicalComplex.HomologySequence.δ_naturality`;
  `bridge/view`: the mapped short exact sequence of Čech complexes and the induced connecting
    morphisms used internally to build the public `δ`-functor owner below.
- primitive data: the exact Čech complex functor from `Lemma_20_10_1`, the mapped short exact
  sequence of cochain complexes, and its canonical homology boundary maps;
- derived API: the public bridge `ringedSpaceCechComplex_map_shortExact`, the source-facing owner
  `ringedSpaceCechCohomologyDeltaFunctor`, and its companion lemmas for degreewise values,
  connecting morphisms, exactness, and naturality. The adjacent exactness windows are already
  owned by the short-exact homology API and should be reused rather than repackaged publicly.

Source/core/bridge triage:
- `source-facing`: the degreewise Čech cohomology functors and the connecting morphism attached to
  a short exact sequence of presheaf modules;
- `core/canonical`: `CohomologicalDeltaFunctor` and the short-exact homology-sequence API for
  cochain complexes;
- `bridge/view`: the theorem `ringedSpaceCechComplex_map_shortExact`, which specializes the exact
  Čech complex functor to short exact sequences in `RingedSpace.PresheafModules X`.
-/

private theorem ringedSpaceModuleCechComplexFunctor_additive :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).Additive :=
  (exactFunctor_le_additiveFunctor (RingedSpace.PresheafModules X) (CochainComplex ModU ℕ))
    (ringedSpaceModuleCechComplexFunctor U 𝒰) (ringedSpaceModuleCechComplexFunctor_exact U 𝒰)

/-- The additive degree-`n` Čech cohomology functor on presheaves of `𝒪_X`-modules for the cover
`𝒰`. -/
abbrev ringedSpaceCechCohomologyDegree
    (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U) [HasFiniteProducts (Over U)] (n : ℕ) :
    RingedSpace.PresheafModules X ⥤+ ModuleCat (X.presheaf.obj (op U)) := by
  let _ := ringedSpaceModuleCechComplexFunctor_additive U 𝒰
  exact AdditiveFunctor.of
    (ringedSpaceModuleCechComplexFunctor U 𝒰 ⋙
      homologyFunctor (ModuleCat (X.presheaf.obj (op U))) (ComplexShape.up ℕ) n)

private instance ringedSpaceModuleCechComplexFunctor_preservesZeroMorphisms :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).PreservesZeroMorphisms := by
  let _ := ringedSpaceModuleCechComplexFunctor_additive U 𝒰
  infer_instance

/-- Evaluating `ringedSpaceCechCohomologyDegree U 𝒰 n` at a presheaf module recovers the
degree-`n` Čech cohomology module owned by `ringedSpaceModuleCechCohomology`. -/
@[simp] theorem ringedSpaceCechCohomologyDegree_obj_obj (n : ℕ) (M : PModX) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.obj M =
      ringedSpaceModuleCechCohomology U 𝒰 M n :=
  rfl

/-- A short exact sequence of presheaves of `𝒪_X`-modules induces a short exact sequence of Čech
complexes of `𝒪_X(U)`-modules. -/
theorem ringedSpaceCechComplex_map_shortExact
    {S : ShortComplex PModX} (hS : S.ShortExact) :
    (S.map (ringedSpaceModuleCechComplexFunctor U 𝒰)).ShortExact := by
  let hExact := ringedSpaceModuleCechComplexFunctor_exact U 𝒰
  let hPres := (exactFunctor_iff (ringedSpaceModuleCechComplexFunctor U 𝒰)).1 hExact
  letI : PreservesFiniteLimits (ringedSpaceModuleCechComplexFunctor U 𝒰) := hPres.1
  letI : PreservesFiniteColimits (ringedSpaceModuleCechComplexFunctor U 𝒰) := hPres.2
  exact hS.map_of_exact (ringedSpaceModuleCechComplexFunctor U 𝒰)

private noncomputable def ringedSpaceCechCohomologyConnectingMorphism
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    ringedSpaceModuleCechCohomology U 𝒰 S.X₃ n ⟶
      ringedSpaceModuleCechCohomology U 𝒰 S.X₁ (n + 1) :=
  (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

private theorem ringedSpaceCechCohomology_mono_map_f_zero
    {S : ShortComplex PModX} (hS : S.ShortExact) :
    Mono ((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.map S.f) := by
  change Mono (HomologicalComplex.homologyMap ((ringedSpaceModuleCechComplexFunctor U 𝒰).map S.f) 0)
  let hShortExact := ringedSpaceCechComplex_map_shortExact U 𝒰 hS
  let _ : Mono ((ringedSpaceModuleCechComplexFunctor U 𝒰).map S.f) := by
    simpa using hShortExact.mono_f
  let _ : Mono (((ringedSpaceModuleCechComplexFunctor U 𝒰).map S.f).f 0) := by infer_instance
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    ((ringedSpaceModuleCechComplexFunctor U 𝒰).map S.f) 0 (by
      intro i h
      simpa using h)

private theorem ringedSpaceCechCohomology_exact₅
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.g)).Exact := by
  simpa [ringedSpaceCechCohomologyDegree] using
    HomologicalComplex.HomologySequence.composableArrows₅_exact
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hS) n (n + 1)
      (ComplexShape.up_mk n (n + 1) rfl)

private theorem ringedSpaceCechCohomologyConnectingMorphism_naturality_aux
    {S T : ShortComplex PModX} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map φ.τ₃)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hT n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map φ.τ₁) := by
  refine CommSq.mk ?_
  simpa [ringedSpaceCechCohomologyDegree, Category.assoc] using
    (HomologicalComplex.HomologySequence.δ_naturality
      ((ringedSpaceModuleCechComplexFunctor U 𝒰).mapShortComplex.map φ)
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hS)
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hT)
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)).symm

/-- Lemma 20.10.2, canonical owner form: the degreewise Čech cohomology functors assemble into a
cohomological `δ`-functor on presheaves of `𝒪_X`-modules. -/
@[stacks 01EK]
noncomputable def ringedSpaceCechCohomologyDeltaFunctor (𝒰 : ι → Over U) :
    CohomologicalDeltaFunctor PModX ModU where
  F := ringedSpaceCechCohomologyDegree U 𝒰
  δ {_} hS n := ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n
  mono_map_f_zero {_} hS := ringedSpaceCechCohomology_mono_map_f_zero U 𝒰 hS
  exact₅ {_} hS n := ringedSpaceCechCohomology_exact₅ U 𝒰 hS n
  δ_naturality {_ _} hS hT φ n :=
    ringedSpaceCechCohomologyConnectingMorphism_naturality_aux U 𝒰 hS hT φ n

@[simp] theorem ringedSpaceCechCohomologyDeltaFunctor_obj_obj (n : ℕ) (M : PModX) :
    (ringedSpaceCechCohomologyDeltaFunctor U 𝒰 n).obj.obj M =
      ringedSpaceModuleCechCohomology U 𝒰 M n :=
by
  change (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.obj M =
    ringedSpaceModuleCechCohomology U 𝒰 M n
  rfl

@[simp] theorem ringedSpaceCechCohomologyDeltaFunctor_δ
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hS n =
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl) :=
  rfl

@[simp, reassoc] theorem ringedSpaceCechCohomologyDeltaFunctor_map_g_comp_δ
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g ≫
        (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hS n =
      0 := by
  simpa using (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).map_g_comp_δ hS n

@[simp, reassoc] theorem ringedSpaceCechCohomologyDeltaFunctor_δ_comp_map_f
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hS n ≫
        (ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f =
      0 := by
  simpa using (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ_comp_map_f hS n

theorem ringedSpaceCechCohomologyDeltaFunctor_exact₅
    {S : ShortComplex PModX} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
      ((ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hS n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.g)).Exact := by
  simpa using (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).exact₅ hS n

theorem ringedSpaceCechCohomologyDeltaFunctor_δ_naturality
    {S T : ShortComplex PModX} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map φ.τ₃)
      ((ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hS n)
      ((ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ hT n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map φ.τ₁) := by
  simpa using (ringedSpaceCechCohomologyDeltaFunctor U 𝒰).δ_naturality hS hT φ n

/-- Companion existence form of Lemma 20.10.2. -/
theorem exists_ringedSpaceCechCohomologyDeltaFunctor :
    ∃ T : CohomologicalDeltaFunctor PModX ModU,
      ∀ n : ℕ, (T n).obj = (ringedSpaceCechCohomologyDegree U 𝒰 n).obj := by
  refine ⟨ringedSpaceCechCohomologyDeltaFunctor U 𝒰, ?_⟩
  intro n
  rfl

end AlgebraicGeometry.RingedSpace
