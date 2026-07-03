import Mathlib
import stacks_project.Chap17.Definition_17_12_1
import stacks_project.Chap12.Lemma_12_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

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

variable {X : RingedSpace.{u}}

-- Proof sketch: factor the subsheaf as a monomorphism into the coherent sheaf; coherence is
-- stable under kernels and extensions inside the weak Serre subcategory, and finite type provides
-- the local generators needed for the source sheaf.
/-- Lemma 17.12.4 (1): a finite type subsheaf of a coherent `\mathcal O_X`-module is coherent. -/
theorem isCoherent_of_mono_of_isFiniteType
    {ℱ 𝒢 : X.Modules} (i : ℱ ⟶ 𝒢) [Mono i] [ℱ.IsFiniteType] [𝒢.IsCoherent] :
    ℱ.IsCoherent := sorry

-- Proof sketch: locally choose finitely many generators of `ℱ`; map a finite free module onto
-- those generators and identify `kernel φ` as an image of the finite type relation sheaf coming
-- from coherence of `𝒢`.
/-- Lemma 17.12.4 (2): if `φ : ℱ ⟶ 𝒢` with `ℱ` finite type and `𝒢` coherent, then `kernel φ` is of
finite type. -/
theorem isFiniteType_kernel_of_finiteType_to_coherent
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsCoherent] :
    (kernel φ).IsFiniteType := sorry

-- Proof sketch: part `(2)` gives that the kernel of a morphism between coherent modules is of
-- finite type, and then part `(1)` upgrades that finite type subsheaf of `ℱ` to a coherent one.
/-- Lemma 17.12.4 (3): the kernel of a morphism of coherent `\mathcal O_X`-modules is coherent. -/
theorem isCoherent_kernel
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (kernel φ).IsCoherent := sorry

-- Proof sketch: the cokernel is a quotient of the finite type sheaf `𝒢`, hence finite type; its
-- local relation sheaves are controlled by a snake-lemma comparison with a finite free presentation
-- of the image of `φ`, reducing to coherence of `𝒢`.
/-- Lemma 17.12.4 (4): the cokernel of a morphism of coherent `\mathcal O_X`-modules is coherent.
-/
theorem isCoherent_cokernel
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (cokernel φ).IsCoherent := sorry

-- Proof sketch: local finite generators for `ℱ₁` and `ℱ₃` combine to generate `ℱ₂`, and the
-- relation sheaf of any finite generating family on `ℱ₂` fits into a short exact sequence with the
-- relation sheaf on `ℱ₃` and the coherent module `ℱ₁`; then part `(2)` yields finite type of the
-- relations.
/-- Lemma 17.12.4 (5): in a short exact sequence of `\mathcal O_X`-modules, if the left and right
terms are coherent, then the middle term is coherent. -/
theorem isCoherent_of_shortExact_of_outer
    {ℱ₁ ℱ₂ ℱ₃ : X.Modules}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [ℱ₁.IsCoherent] [ℱ₃.IsCoherent] :
    ℱ₂.IsCoherent := sorry

-- Proof sketch: the zero `\mathcal O_X`-module is finitely generated and every kernel against it
-- is again zero, so it satisfies the defining coherence conditions.
/-- Lemma 17.12.4 (6): the coherent `\mathcal O_X`-modules contain the zero object, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_containsZero (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).ContainsZero := sorry

-- Proof sketch: for a morphism between coherent modules, part `(3)` identifies its kernel as a
-- coherent module, which is exactly closure under kernels for the coherent-object property.
/-- Lemma 17.12.4 (7): coherent `\mathcal O_X`-modules are closed under kernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderKernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderKernels := sorry

-- Proof sketch: part `(4)` shows that the cokernel of any morphism between coherent modules is
-- coherent, which is exactly closure under cokernels for the coherent-object property.
/-- Lemma 17.12.4 (8): coherent `\mathcal O_X`-modules are closed under cokernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak Serre subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderCokernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderCokernels := sorry

-- Proof sketch: part `(5)` supplies the extension step in a short exact sequence, giving closure
-- under extensions for the coherent-object property.
/-- Lemma 17.12.4 (9): coherent `\mathcal O_X`-modules are closed under extensions, completing the
weak Serre closure conditions for `Coh(\mathcal O_X) ⊂ Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderExtensions (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderExtensions := sorry

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
