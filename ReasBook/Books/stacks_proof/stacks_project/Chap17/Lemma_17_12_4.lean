import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Lemma_17_9_3
import StacksProject_2024.Chap17.Lemma_17_11_3
import StacksProject_2024.Chap17.Lemma_17_11_4
import StacksProject_2024.Chap17.Lemma_17_12_2
import StacksProject_2024.Chap17.Lemma_17_9_8
import StacksProject_2024.Chap12.Lemma_12_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open TopologicalSpace

noncomputable section

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u}}

namespace AlgebraicGeometry.RingedSpace

namespace SheafOfModules

/-- Helper for Lemma 17.12.4: coherence transports across isomorphisms of `\mathcal O_X`-modules.
-/
theorem IsCoherent.of_iso
    {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) [𝒢.IsCoherent] :
    ℱ.IsCoherent := by
  refine SheafOfModules.IsCoherent.mk ?_ ?_
  · -- Proof comment: finite type is already stable under isomorphism.
    exact
      (SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms
        (R := X.ringCatSheaf)).of_iso e.symm inferInstance
  · intro U r φ
    -- Proof comment: compose the local relation map with the restricted isomorphism and transport
    -- the resulting kernel back along `kernelCompMono`.
    let eU :
        ℱ.over U ⟶ 𝒢.over U :=
      (SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))).map e.hom
    exact
      (SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms
        (R := X.ringCatSheaf.over U)).of_iso
      (kernelCompMono φ eU)
      (SheafOfModules.IsCoherent.isFiniteType_kernel
        (ℱ := 𝒢) U r (φ ≫ eU))

end SheafOfModules

/- Domain-style sampling for Lemma 17.12.4:
- primary domain: coherent module sheaves on a ringed space and the weak-Serre closure formalism
  for the object property `SheafOfModules.isCoherent X`;
- inspected owner declarations:
  `SheafOfModules.IsCoherent`,
  `RingedSpace.Coh`,
  `CategoryTheory.ObjectProperty.IsWeakSerreClass`,
  `CategoryTheory.ObjectProperty.weakSerreSubcategory_inclusion_exact`;
- best owner abstraction:
  the ambient owner is `X.Modules`, with `SheafOfModules.IsCoherent` as the primitive property and
  the weak-Serre / abelian / exactness package as derived `ObjectProperty` API;
- primitive data:
  coherent modules, finite-type modules, and short exact sequences in `X.Modules`;
- derived API:
  closure under kernels, cokernels, and extensions, the weak-Serre instance on
  `SheafOfModules.isCoherent X`, the abelian structure on `RingedSpace.Coh X`, and exactness of
  the inclusion functor.

Source/core/bridge triage:
- `source-facing`: the coherence theorems for submodules, kernels, cokernels, and short exact
  sequences;
- `core/canonical`: the owner property `SheafOfModules.IsCoherent` on `X.Modules` and the generic
  `ObjectProperty` closure classes;
- `bridge/view`: the abelian structure on `RingedSpace.Coh X` and exactness of the canonical
  inclusion functor. -/

-- Proof sketch: factor the subsheaf as a monomorphism into the coherent sheaf; coherence is
-- stable under kernels and extensions inside the weak Serre subcategory, and finite type provides
-- the local generators needed for the source sheaf.
/-- Lemma 17.12.4 (1): a finite type subsheaf of a coherent `\mathcal O_X`-module is coherent. -/
@[stacks 01BY]
theorem isCoherent_of_mono_of_isFiniteType
    {ℱ 𝒢 : X.Modules} (i : ℱ ⟶ 𝒢) [Mono i] [ℱ.IsFiniteType] [𝒢.IsCoherent] :
    ℱ.IsCoherent := by
  refine SheafOfModules.IsCoherent.mk ?_ ?_
  · -- Proof comment: the finite-type hypothesis on the subsheaf is already part of the input.
    infer_instance
  · intro U r φ
    -- Proof comment: a monomorphism stays monic after restriction, so the relation kernel for
    -- `φ` is the same as the relation kernel for the composite into the coherent target.
    let iU :
        ℱ.over U ⟶ 𝒢.over U :=
      (SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))).map i
    exact
      (SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms
        (R := X.ringCatSheaf.over U)).of_iso
      (kernelCompMono φ iU)
      (SheafOfModules.IsCoherent.isFiniteType_kernel
        (ℱ := 𝒢) U r (φ ≫ iU))

-- Proof sketch: locally choose finitely many generators of `ℱ`; map a finite free module onto
-- those generators and identify `kernel φ` as an image of the finite type relation sheaf coming
-- from coherence of `𝒢`.
/-- Lemma 17.12.4 (2): if `φ : ℱ ⟶ 𝒢` with `ℱ` finite type and `𝒢` coherent, then `kernel φ` is of
finite type. -/
@[stacks 01BY]
theorem isFiniteType_kernel_of_finiteType_to_coherent
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsCoherent] :
    (kernel φ).IsFiniteType := by
  let himageFiniteType : (Abelian.image φ).IsFiniteType :=
    SheafOfModules.isFiniteType_image φ
  letI : (Abelian.image φ).IsFiniteType := himageFiniteType
  have himageCoherent : (Abelian.image φ).IsCoherent := by
    -- Proof comment: the image is a finite-type submodule of the coherent target `𝒢`.
    exact isCoherent_of_mono_of_isFiniteType (Abelian.image.ι φ)
  letI : (Abelian.image φ).IsCoherent := himageCoherent
  letI : (Abelian.image φ).IsFinitePresentation := inferInstance
  have hfactorKernel : (kernel (Abelian.factorThruImage φ)).IsFiniteType := by
    -- Proof comment: the factor map to the image is epic, so the finite-presentation kernel
    -- theorem applies directly.
    letI : Epi (Abelian.factorThruImage φ) := inferInstance
    simpa using
      (SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation
        (Abelian.factorThruImage φ))
  -- Proof comment: `φ` factors through its image monomorphism, so the original kernel is the
  -- same kernel up to the standard `kernelCompMono` comparison.
  exact
    (SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms
      (R := X.ringCatSheaf)).of_iso
      (kernelCompMono (Abelian.factorThruImage φ) (Abelian.image.ι φ)).symm
      hfactorKernel

-- Proof sketch: part `(2)` gives that the kernel of a morphism between coherent modules is of
-- finite type, and then part `(1)` upgrades that finite type subsheaf of `ℱ` to a coherent one.
/-- Lemma 17.12.4 (3): the kernel of a morphism of coherent `\mathcal O_X`-modules is coherent. -/
@[stacks 01BY]
theorem isCoherent_kernel
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (kernel φ).IsCoherent := by
  -- Proof comment: part `(2)` gives finite type for the kernel, and then part `(1)` upgrades the
  -- kernel monomorphism into the coherent source `ℱ` to coherence.
  letI : (kernel φ).IsFiniteType := isFiniteType_kernel_of_finiteType_to_coherent φ
  exact isCoherent_of_mono_of_isFiniteType (kernel.ι φ)

/-- Helper for Lemma 17.12.4: over any open `U`, the kernel of a morphism from a finite-type
module sheaf into a finitely presented module sheaf is finite type. -/
private theorem isFiniteType_kernel_of_finiteType_to_finitePresentation_over
    {U : Opens X}
    {𝒢 ℱ : SheafOfModules (X.ringCatSheaf.over U)} (θ : 𝒢 ⟶ ℱ)
    [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel θ).IsFiniteType := by
  -- TODO: restore the restricted image-factorization argument after the finite-type image and
  -- kernel-of-epi owners are back in scope over slice categories.
  sorry

-- Proof sketch: the cokernel is a quotient of the finite type sheaf `𝒢`, hence finite type; its
-- local relation sheaves are controlled by a snake-lemma comparison with a finite free presentation
-- of the image of `φ`, reducing to coherence of `𝒢`.
/-- Lemma 17.12.4 (4): the cokernel of a morphism of coherent `\mathcal O_X`-modules is coherent.
-/
@[stacks 01BY]
theorem isCoherent_cokernel
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (cokernel φ).IsCoherent := by
  -- TODO: either recover the finitely presented cokernel instance or revert to the source
  -- snake-lemma proof once the finite-type support lemmas are restored.
  sorry

/-- Helper for Lemma 17.12.4: restricting a short exact row of `\mathcal O_X`-modules to an open
subspace remains short exact. -/
private theorem shortExact_over
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (U : Opens X) :
    (S.map (SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U)))).ShortExact := by
  -- Proof comment: restriction to an open is the identity-ring pushforward functor, so exactness
  -- transports directly via `ShortExact.map_of_exact`.
  simpa using hS.map_of_exact (SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U)))

/-- Helper for Lemma 17.12.4: if an exact row lifts the relation map
`kernel (ψ ≫ g) ⟶ X₂`, then the original relation kernel `kernel ψ` identifies with the kernel of
the lifted map into `X₁`. -/
private noncomputable def kernelIso_of_exactLift
    {U : Opens X}
    {T : ShortComplex (SheafOfModules (X.ringCatSheaf.over U))}
    (hT : T.ShortExact) (r : ℕ)
    (ψ :
      SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) (ULift.{u} (Fin r)) ⟶
        T.X₂)
    (ρ : kernel (ψ ≫ T.g) ⟶ T.X₁)
    (hρ : ρ ≫ T.f = kernel.ι (ψ ≫ T.g) ≫ ψ) :
    kernel ψ ≅ kernel ρ := sorry

/-- Helper for Lemma 17.12.4: over any open `U`, the relation sheaf of a finite free map into the
middle term of a short exact row with coherent outer terms is finite type. -/
private theorem isFiniteType_relationKernel_of_shortExact_over
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₃.IsCoherent]
    (U : Opens X) (r : ℕ)
    (ψ :
      SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) (ULift.{u} (Fin r)) ⟶
        S.X₂.over U) :
    (kernel ψ).IsFiniteType := by
  -- TODO: after restoring localized exactness and the over-open finite-presentation helper, lift
  -- `kernel (ψ ≫ g)` to the left term and compare kernels via `kernelIso_of_exactLift`.
  sorry

-- Proof sketch: local finite generators for `ℱ₁` and `ℱ₃` combine to generate `ℱ₂`, and the
-- relation sheaf of any finite generating family on `ℱ₂` fits into a short exact sequence with the
-- relation sheaf on `ℱ₃` and the coherent module `ℱ₁`; then part `(2)` yields finite type of the
-- relations.
/-- Lemma 17.12.4 (5): in a short exact sequence of `\mathcal O_X`-modules, if the left and right
terms are coherent, then the middle term is coherent. -/
@[stacks 01BY]
theorem isCoherent_of_shortExact_of_outer
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₃.IsCoherent] :
    S.X₂.IsCoherent := by
  -- TODO: once finite type in short exact rows is restored, finish by applying the localized
  -- relation-kernel helper to each restricted finite free map.
  sorry

-- Proof sketch: the zero `\mathcal O_X`-module is finitely generated and every kernel against it
-- is again zero, so it satisfies the defining coherence conditions.
/-- Lemma 17.12.4 (6): the coherent `\mathcal O_X`-modules contain the zero object, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
@[stacks 01BY]
instance isCoherent_containsZero (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).ContainsZero where
  exists_zero := by
    -- TODO: once the finite-free finite-type owner from Lemma 17.11.4 is available again without
    -- pulling in the broken Chapter 17 dependency chain, identify `kernel φ` with the finite free
    -- source via `kernelZeroIsoSource` and transport finite type from that source.
    sorry

-- Proof sketch: for a morphism between coherent modules, part `(3)` identifies its kernel as a
-- coherent module, which is exactly closure under kernels for the coherent-object property.
/-- Lemma 17.12.4 (7): coherent `\mathcal O_X`-modules are closed under kernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
@[stacks 01BY]
instance isCoherent_isClosedUnderKernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderKernels where
  kernels_le := by
    intro A hA
    rcases hA with ⟨f, k, hk, hFG⟩
    -- Proof comment: any kernel object is isomorphic to the canonical kernel, so part `(3)`
    -- transfers coherence from the canonical kernel back to the chosen kernel fork.
    exact
      (SheafOfModules.isCoherent X).prop_of_iso
        (IsLimit.conePointUniqueUpToIso hk (kernelIsKernel f)).symm
        (isCoherent_kernel f)

-- Proof sketch: part `(4)` shows that the cokernel of any morphism between coherent modules is
-- coherent, which is exactly closure under cokernels for the coherent-object property.
/-- Lemma 17.12.4 (8): coherent `\mathcal O_X`-modules are closed under cokernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
@[stacks 01BY]
instance isCoherent_isClosedUnderCokernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderCokernels where
  cokernels_le := by
    intro A hA
    rcases hA with ⟨f, q, hq, hFG⟩
    -- Proof comment: any cokernel object is isomorphic to the canonical cokernel, so part `(4)`
    -- transfers coherence from the canonical cokernel back to the chosen cokernel cofork.
    exact
      (SheafOfModules.isCoherent X).prop_of_iso
        (IsColimit.coconePointUniqueUpToIso hq (cokernelIsCokernel f)).symm
        (isCoherent_cokernel f)

-- Proof sketch: part `(5)` supplies the extension step in a short exact sequence, giving closure
-- under extensions for the coherent-object property.
/-- Lemma 17.12.4 (9): coherent `\mathcal O_X`-modules are closed under extensions, completing the
weak Serre closure conditions for `Coh(\mathcal O_X) ⊂ Mod(\mathcal O_X)`. -/
@[stacks 01BY]
instance isCoherent_isClosedUnderExtensions (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    -- Proof comment: part `(5)` is exactly the extension-closure statement for coherent modules.
    letI : S.X₁.IsCoherent := h₁
    letI : S.X₃.IsCoherent := h₃
    exact isCoherent_of_shortExact_of_outer hS

/-- The coherent `\mathcal O_X`-modules form a weak Serre subcategory of `Mod(\mathcal O_X)`. -/
instance isCoherent_isWeakSerreClass (X : RingedSpace.{u}) :
    IsWeakSerreClass (SheafOfModules.isCoherent X) :=
  isWeakSerreClass_of_closure _

variable (X : RingedSpace.{u})

/- Lemma 17.12.4 (10): the category `Coh(\mathcal O_X)` of coherent `\mathcal O_X`-modules is
abelian. This is the canonical abelian instance on `RingedSpace.Coh X`. -/
example : Abelian (RingedSpace.Coh X) := by
  letI : (SheafOfModules.isCoherent X).IsClosedUnderFiniteProducts := inferInstance
  change Abelian (SheafOfModules.isCoherent X).FullSubcategory
  infer_instance

-- Proof sketch: once coherent modules form a weak Serre subcategory and their full subcategory is
-- abelian, the inclusion creates kernels and cokernels and therefore preserves the exactness data
-- required for an exact functor.
/- Lemma 17.12.4 (11): the inclusion functor `Coh(\mathcal O_X) ⥤ Mod(\mathcal O_X)` is exact. -/
#check
  (weakSerreSubcategory_inclusion_exact (SheafOfModules.isCoherent X) :
    exactFunctor (RingedSpace.Coh X) (RingedSpace.Modules X)
      (SheafOfModules.isCoherent X).ι)

end AlgebraicGeometry.RingedSpace
