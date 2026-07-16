import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Preadditive.Basic
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Definition_17_4_1
import stacks_proof.stacks_project.Chap17.Definition_17_5_1
import stacks_proof.stacks_project.Chap17.Definition_17_12_1
import stacks_proof.stacks_project.Chap17.Lemma_17_9_5
import stacks_proof.stacks_project.Chap17.Lemma_17_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Lemma 17.12.6:
- primary domain: local injectivity criteria for morphisms of `\mathcal O_X`-modules on a ringed
  space;
- inspected owner declarations:
  `RingedSpace.moduleStalkHom`,
  `RingedSpace.moduleStalkMap`,
  `RingedSpace.moduleRestrictionMap`,
  `RingedSpace.isFiniteType_kernel_of_finiteType_to_coherent`,
  `exists_open_neighborhood_restriction_isZero_of_stalk_isZero`,
  `TopCat.Presheaf.mono_iff_stalk_mono`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, with stalkwise and local-restriction behavior
  expressed by the bundled stalk morphism `RingedSpace.moduleStalkHom x φ`, its underlying map
  `RingedSpace.moduleStalkMap x φ`, and the owner notation `φ |_ U` for
  `RingedSpace.moduleRestrictionMap U φ`; the canonical
  neighborhood-level bridge is `Mono (φ |_ U)`, while the numbered
  source-facing statement remains sectionwise injectivity of `φ |_ U` on all opens inside `U`;
- primitive data:
  a morphism `φ : 𝒢 ⟶ ℱ`, a point `x : X`, finite type of `𝒢`, coherence of `ℱ`, and
  injectivity of the induced stalk map at `x`;
- derived API:
  after shrinking around `x`, the restricted morphism is a monomorphism, hence every map on
  sections over opens inside that neighbourhood is injective.

Source/core/bridge triage:
- `source-facing`: injectivity of `φ` on all sections over opens `V ⊆ U`;
- `core/canonical`: `RingedSpace.moduleStalkHom`, `RingedSpace.moduleRestrictionMap`, and the
  kernel object `kernel φ` in `RingedSpace.Modules X`, together with the owner predicates
  `Mono (RingedSpace.moduleStalkHom x φ)` and `Mono (φ |_ U)`;
- `bridge/view`: the underlying-function stalk injectivity
  `Function.Injective (RingedSpace.moduleStalkMap x φ)` and the passage from local monomorphy of
  `φ |_ U` to sectionwise injectivity of `φ.val.app (op V)` on all `V ≤ U`.
-/

variable {X : RingedSpace.{u}} {𝒢 ℱ : RingedSpace.Modules X}

-- Proof sketch: let `𝒦 = kernel φ`. Lemma `17.12.4` makes `𝒦` finite type because `𝒢` is finite
-- type and `ℱ` is coherent. The stalk injectivity assumption forces `𝒦_x = 0`, so Lemma `17.9.5`
-- gives an open neighbourhood `U` of `x` with `𝒦|_U = 0`. Restriction preserves kernels, hence
-- `kernel (φ|_U)` is zero and `φ|_U` is mono.
/-- Owner-level companion to Lemma 17.12.6: under the usual finite type/coherent hypotheses, if
the stalk morphism `RingedSpace.moduleStalkHom x φ : 𝒢_x ⟶ ℱ_x` is a monomorphism, then after
shrinking around `x` the restricted morphism `φ |_ U : 𝒢|_U ⟶ ℱ|_U` is a monomorphism. -/
theorem exists_open_neighborhood_mono_restriction_of_stalk_mono
    (φ : 𝒢 ⟶ ℱ) (x : X) [𝒢.IsFiniteType] [ℱ.IsCoherent]
    (hφx : Mono (RingedSpace.moduleStalkHom x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (φ |_ U) := by
  have hφx' : Function.Injective (RingedSpace.moduleStalkMap x φ) := by
    simpa [RingedSpace.moduleStalkHom] using
      (ModuleCat.mono_iff_injective (RingedSpace.moduleStalkHom x φ)).1 hφx
  have hkernel_x : IsZero (RingedSpace.stalkModuleCat (kernel φ) x) := by
    have hιx : Function.Injective (RingedSpace.moduleStalkMap x (kernel.ι φ)) := by
      have hmono : Mono ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ)) := by
        infer_instance
      have hstalk_mono :
          Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ)).hom) :=
        (TopCat.Presheaf.mono_iff_stalk_mono
          ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map (kernel.ι φ))).1 hmono x
      simpa [RingedSpace.moduleStalkMap] using
        (AddCommGrpCat.mono_iff_injective _).1 hstalk_mono
    have hkernel_map_eq_zero (m : RingedSpace.stalkModuleCat (kernel φ) x) :
        RingedSpace.moduleStalkMap x φ (RingedSpace.moduleStalkMap x (kernel.ι φ) m) = 0 := by
      let i : kernel φ ⟶ 𝒢 := kernel.ι φ
      have hcomp :
          RingedSpace.moduleStalkMap x i ≫ RingedSpace.moduleStalkMap x φ =
            RingedSpace.moduleStalkMap x (i ≫ φ) := by
        change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map i.val) ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) =
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map i.val) ≫
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val))
        exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map i.val)
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)).symm
      have hzero : RingedSpace.moduleStalkMap x (i ≫ φ) = 0 := by
        rw [show i ≫ φ = 0 by simpa [i] using kernel.condition φ]
        change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
        exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj (kernel φ).val)
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj ℱ.val)
      have hm :
          (RingedSpace.moduleStalkMap x i ≫ RingedSpace.moduleStalkMap x φ) m = 0 := by
        rw [hcomp, hzero]
        rfl
      simpa [i, ConcreteCategory.comp_apply] using hm
    letI : Subsingleton (RingedSpace.stalkModuleCat (kernel φ) x) := ⟨fun m n ↦ by
      apply hιx
      apply hφx'
      rw [hkernel_map_eq_zero m, hkernel_map_eq_zero n]⟩
    exact ModuleCat.isZero_of_subsingleton (RingedSpace.stalkModuleCat (kernel φ) x)
  let 𝒦 := kernel φ
  haveI : 𝒦.IsFiniteType := RingedSpace.isFiniteType_kernel_of_finiteType_to_coherent φ
  have h𝒦x : IsZero (RingedSpace.stalkModuleCat 𝒦 x) := by
    simpa [𝒦] using hkernel_x
  rcases exists_open_neighborhood_restriction_isZero_of_stalk_isZero 𝒦 x h𝒦x with
    ⟨U, hxU, hU_zero⟩
  let restriction : RingedSpace.Modules X ⥤ SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))
  have hkernel_zero : IsZero (kernel (φ |_ U)) := by
    let e := PreservesKernel.iso restriction φ
    have hrestriction_zero : IsZero (restriction.obj (kernel φ)) := by
      simpa [restriction, SheafOfModules.over, 𝒦] using hU_zero
    exact (e.isZero_iff).1 hrestriction_zero
  exact ⟨U, hxU, CategoryTheory.Preadditive.mono_of_isZero_kernel _ hkernel_zero⟩

-- Proof sketch: apply the owner-level monomorphism theorem above, then use the standard
-- objectwise mono criterion for the underlying presheaf of modules on `U`.
/-- Lemma 17.12.6: if `φ : 𝒢 ⟶ ℱ` is a morphism of `\mathcal O_X`-modules with `𝒢` finite type,
`ℱ` coherent, and the stalk map `φ_x : 𝒢_x → ℱ_x` injective, then there exists an open
neighbourhood `U` of `x` such that for every open `V ⊆ U` the induced map on sections
`φ(V) : 𝒢(V) → ℱ(V)` is injective. Equivalently, `φ |_ U` is injective on sections over every
open of `U`. -/
@[stacks 01C0]
theorem exists_open_neighborhood_sectionwise_injective_of_stalk_injective
    (φ : 𝒢 ⟶ ℱ) (x : X) [𝒢.IsFiniteType] [ℱ.IsCoherent]
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U),
      ∀ (V : Opens X) (_ : V ≤ U), Function.Injective (φ.val.app (op V)) := by
  have hφx' : Mono (RingedSpace.moduleStalkHom x φ) := by
    refine (ModuleCat.mono_iff_injective _).2 ?_
    simpa [RingedSpace.moduleStalkHom] using hφx
  rcases exists_open_neighborhood_mono_restriction_of_stalk_mono φ x hφx' with
    ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  intro V hVU
  letI : Mono (φ |_ U) := hU
  let ψ := (SheafOfModules.forget (X.ringCatSheaf.over U)).map (φ |_ U)
  letI : Mono ψ := by
    infer_instance
  simpa [RingedSpace.moduleRestrictionMap, SheafOfModules.forget] using
    (PresheafOfModules.injective_of_mono ψ (op (Over.mk (homOfLE hVU))))

end AlgebraicGeometry
