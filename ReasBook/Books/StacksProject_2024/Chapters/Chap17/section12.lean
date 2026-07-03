import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Preadditive.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_12_1 (from Chap17) -/
open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- 
Domain-style sampling for coherence of `\mathcal O_X`-modules on a ringed space:
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsCoherent`
- best owner abstraction:
  the ambient owner is `(RingedSpace.Modules X)`
- primitive data:
  a module sheaf `ℱ : (RingedSpace.Modules X)`, finite type on `X`, and
  finite-type kernels for maps from finite free modules on restrictions `ℱ.over U`
- derived API:
  the object property `SheafOfModules.isCoherent X`, the finite-presentation consequence, and the
  full subcategory `RingedSpace.Coh X`

Layer triage:
- `source-facing`: the textbook coherence condition on `\mathcal O_X`-modules
- `core/canonical`: the owner category `(RingedSpace.Modules X)`
- `bridge/view`: the object property and the coherent full subcategory
-/

namespace SheafOfModules

variable {X : RingedSpace.{u}}

-- Lean miselaborates the direct owner reference `SheafOfModules.IsFiniteType ℱ` in a class field
-- over `RingedSpace.Modules X`; keep a private alias so the public owner remains canonical.
private abbrev FiniteTypeProp (ℱ : RingedSpace.Modules X) : Prop :=
  SheafOfModules.IsFiniteType ℱ

/-- Definition 17.12.1: a sheaf of `\mathcal O_X`-modules on a ringed space is coherent if it is
of finite type and for every open `U ⊆ X` and every morphism from a finite free
`\mathcal O_U`-module to `ℱ |_U`, the kernel is of finite type. -/
class IsCoherent (ℱ : RingedSpace.Modules X) : Prop where
  /-- A coherent sheaf of modules is of finite type. -/
  toIsFiniteType : FiniteTypeProp ℱ
  /-- Kernels of morphisms from finite free modules into restrictions of a coherent sheaf are of
  finite type. -/
  isFiniteType_kernel (U : Opens X) (r : ℕ)
      (φ :
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules (X.ringCatSheaf.over U)) ⟶
          ℱ.over U) :
      (kernel φ).IsFiniteType

variable (X)

/-- The object property of coherent `\mathcal O_X`-modules. -/
abbrev isCoherent : ObjectProperty (RingedSpace.Modules X) :=
  SheafOfModules.IsCoherent

variable {X}

instance (ℱ : RingedSpace.Modules X) [h : ℱ.IsCoherent] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

-- Proof sketch: choose on a neighbourhood `U` a finite generating family of `ℱ|_U`; the induced
-- epimorphism from a finite free `\mathcal O_U`-module onto `ℱ|_U` has finite type kernel by
-- coherence, yielding a local finite presentation.
/-- A coherent `\mathcal O_X`-module is finitely presented. -/
instance (ℱ : RingedSpace.Modules X) [ℱ.IsCoherent] :
    ℱ.IsFinitePresentation := sorry

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

/-- The category `Coh(\mathcal O_X)` of coherent `\mathcal O_X`-modules on a ringed space `X`. -/
abbrev Coh (X : RingedSpace.{u}) :=
  (SheafOfModules.isCoherent X).FullSubcategory

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_12_2 (from Chap17) -/
open AlgebraicGeometry

universe u

/- 
Domain-style sampling for Lemma 17.12.2:
- primary domain: coherent sheaves of modules on ringed spaces and their canonical downstream
  finiteness predicates;
- sampled owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsCoherent` from `Definition_17_12_1`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsQuasicoherent`,
  the canonical instance `[M.IsFinitePresentation] → M.IsQuasicoherent`;
- best owner abstraction: the ambient owner category `(RingedSpace.Modules X)`,
  with `SheafOfModules.IsCoherent` as the source-facing hypothesis and
  `SheafOfModules.IsFinitePresentation` / `SheafOfModules.IsQuasicoherent` as derived owner-level
  properties;
- primitive data: the sheaf `ℱ` together with the coherence structure;
- derived API: finite presentation and quasi-coherence, both supplied canonically by instances.

Source/core/bridge triage:
- `source-facing`: coherence of an `\mathcal O_X`-module;
- `core/canonical`: the owner predicates `SheafOfModules.IsFinitePresentation` and
  `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: instance search from coherence to finite presentation, then to quasi-coherence.

This item is a canonical-use item, not a new owner: the chapter-local coherence class already owns
the input data, while the conclusions are canonical downstream instances, so the file should reuse
those instances directly instead of introducing theorem wrappers with duplicate interfaces.
-/

variable {X : RingedSpace.{u}}
variable (ℱ : RingedSpace.Modules X) [ℱ.IsCoherent]

/- Lemma 17.12.2: a coherent `\mathcal O_X`-module on a ringed space `(X, \mathcal O_X)` is
finitely presented. This is the canonical instance provided by
`Definition_17_12_1`. -/
#check (inferInstance : ℱ.IsFinitePresentation)

/- Lemma 17.12.2: a coherent `\mathcal O_X`-module is therefore quasi-coherent, via the canonical
instance from finite presentation to quasi-coherence. -/
#check (inferInstance : ℱ.IsQuasicoherent)

/-! ### Example_17_12_3 (from Chap17) -/
open MvPolynomial
open Module.Finite

noncomputable section

local notation "Cinf" => MvPolynomial ℕ+ ℂ

/- Domain-style sampling for Example 17.12.3:
- primary domain: commutative algebra of coherence and Noetherianity for countable-variable
  polynomial rings;
- source-facing owner: the countable polynomial ring `Cinf = MvPolynomial ℕ+ ℂ`;
- inspected owner declarations:
  * `IsCoherentRing R`;
  * `Module.Coherent.finitePresentation_submodule`;
  * `countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian`.
- primitive data: the owner ring `Cinf` and finitely generated ideals in it;
- derived API: finite presentation of finitely generated ideals and the failure of
  `IsNoetherianRing`.

The coherent statement is genuinely source-facing here, so the public surface stays at
`IsCoherentRing Cinf`. The ideal-theoretic clause is a thin companion extracted from that owner
predicate, while part `(2)` directly reuses the Chapter 10 countable-variable theorem.
-/

-- Proof sketch: use the canonical countable-variable owner `Cinf`. For a commutative ring,
-- coherence of the self-module is captured by finite presentation of finitely generated ideals.
/-- Example 17.12.3 (1): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
modeled as `Cinf`, is coherent as a module over itself. -/
instance complex_countableVariablePolynomialRing_isCoherentRing :
    IsCoherentRing Cinf := by
  sorry

/-- Example 17.12.3 (1), ideal-theoretic form: every finitely generated ideal in
`\mathbf{C}[x_1, x_2, x_3, \ldots]` is finitely presented. -/
theorem complex_countableVariablePolynomialRing_fgIdeal_finitePresentation
    (I : Ideal Cinf) (hI : I.FG) :
    Module.FinitePresentation Cinf I := by
  exact
    (inferInstance : Module.Coherent Cinf Cinf).finitePresentation_submodule I (of_fg hI)

-- Proof sketch: this is exactly the non-Noetherian half of the Chapter 10 countable-variable
-- owner theorem specialized to `ℂ`.
/-- Example 17.12.3 (2): the countable polynomial ring `\mathbf{C}[x_1, x_2, x_3, \ldots]`,
viewed as a module over itself, is not Noetherian. -/
theorem complex_countableVariablePolynomialRing_not_isNoetherianRing :
    ¬ IsNoetherianRing Cinf := by
  exact (countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian ℂ).2

/-! ### Lemma_17_12_4 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.12.4:
- primary domain: coherent module sheaves on a ringed space and the weak-LinearRepresentations_Serre_1977 closure formalism
  for the object property `SheafOfModules.isCoherent X`;
- inspected owner declarations:
  `SheafOfModules.IsCoherent`,
  `RingedSpace.Coh`,
  `CategoryTheory.ObjectProperty.IsWeakSerreClass`,
  `CategoryTheory.ObjectProperty.weakSerreSubcategory_inclusion_exact`;
- best owner abstraction:
  the ambient owner is `X.Modules`, with `SheafOfModules.IsCoherent` as the primitive property and
  the weak-LinearRepresentations_Serre_1977 / abelian / exactness package as derived `ObjectProperty` API;
- primitive data:
  coherent modules, finite-type modules, and short exact sequences in `X.Modules`;
- derived API:
  closure under kernels, cokernels, and extensions, the weak-LinearRepresentations_Serre_1977 instance on
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
-- stable under kernels and extensions inside the weak LinearRepresentations_Serre_1977 subcategory, and finite type provides
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
closure conditions expressing that `Coh(\mathcal O_X)` is a weak LinearRepresentations_Serre_1977 subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_containsZero (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).ContainsZero := sorry

-- Proof sketch: for a morphism between coherent modules, part `(3)` identifies its kernel as a
-- coherent module, which is exactly closure under kernels for the coherent-object property.
/-- Lemma 17.12.4 (7): coherent `\mathcal O_X`-modules are closed under kernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak LinearRepresentations_Serre_1977 subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderKernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderKernels := sorry

-- Proof sketch: part `(4)` shows that the cokernel of any morphism between coherent modules is
-- coherent, which is exactly closure under cokernels for the coherent-object property.
/-- Lemma 17.12.4 (8): coherent `\mathcal O_X`-modules are closed under cokernels, one of the
closure conditions expressing that `Coh(\mathcal O_X)` is a weak LinearRepresentations_Serre_1977 subcategory of
`Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderCokernels (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderCokernels := sorry

-- Proof sketch: part `(5)` supplies the extension step in a short exact sequence, giving closure
-- under extensions for the coherent-object property.
/-- Lemma 17.12.4 (9): coherent `\mathcal O_X`-modules are closed under extensions, completing the
weak LinearRepresentations_Serre_1977 closure conditions for `Coh(\mathcal O_X) ⊂ Mod(\mathcal O_X)`. -/
instance isCoherent_isClosedUnderExtensions (X : RingedSpace.{u}) :
    (SheafOfModules.isCoherent X).IsClosedUnderExtensions := sorry

/-- The coherent `\mathcal O_X`-modules form a weak LinearRepresentations_Serre_1977 subcategory of `Mod(\mathcal O_X)`. -/
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

-- Proof sketch: once coherent modules form a weak LinearRepresentations_Serre_1977 subcategory and their full subcategory is
-- abelian, the inclusion creates kernels and cokernels and therefore preserves the exactness data
-- required for an exact functor.
/- Lemma 17.12.4 (11): the inclusion functor `Coh(\mathcal O_X) ⥤ Mod(\mathcal O_X)` is exact. -/
#check
  (weakSerreSubcategory_inclusion_exact (SheafOfModules.isCoherent X) :
    exactFunctor (RingedSpace.Coh X) (RingedSpace.Modules X)
      (SheafOfModules.isCoherent X).ι)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_12_5 (from Chap17) -/
open AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for coherence versus finite presentation on a ringed space:
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsCoherent`,
  `SheafOfModules.IsFinitePresentation`
- best owner abstraction:
  the ambient owner is `(RingedSpace.Modules X)`; coherence and finite presentation are object properties on
  that owner category
- primitive data:
  a ringed space `X`, a module sheaf `ℱ : (RingedSpace.Modules X)`, and coherence of the structure-sheaf
  module `SheafOfModules.unit ((RingedSpace.ringCatSheaf X))`
- derived API:
  the source-facing equivalence between coherence and finite presentation under the coherent
  structure-sheaf hypothesis

Source/core/bridge triage:
- `source-facing`: the textbook equivalence for `\mathcal O_X`-modules when `\mathcal O_X` is
  coherent
- `core/canonical`: the owner predicates `SheafOfModules.IsCoherent` and
  `SheafOfModules.IsFinitePresentation` on `(RingedSpace.Modules X)`
- `bridge/view`: this theorem, which relates the two owner predicates under the extra hypothesis on
  the unit module
-/

namespace SheafOfModules

variable {X : RingedSpace.{u}}

-- Proof sketch: finite presentation gives local exact sequences by finite free modules. Under
-- coherence of the structure sheaf module, the kernels in such local presentations are of finite
-- type, so the defining coherence condition holds.
/-- If the structure sheaf `\mathcal O_X`, viewed as an `\mathcal O_X`-module, is coherent, then
a finitely presented `\mathcal O_X`-module is coherent. -/
theorem isCoherent_of_isFinitePresentation
    [hOX : (unit (RingedSpace.ringCatSheaf X)).IsCoherent]
    (ℱ : RingedSpace.Modules X) [ℱ.IsFinitePresentation] :
    ℱ.IsCoherent := sorry

instance (ℱ : RingedSpace.Modules X)
    [hOX : (unit (RingedSpace.ringCatSheaf X)).IsCoherent] [ℱ.IsFinitePresentation] :
    ℱ.IsCoherent :=
  isCoherent_of_isFinitePresentation ℱ

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Lemma 17.12.5: if the structure sheaf `\mathcal O_X`, regarded as an `\mathcal O_X`-module,
is coherent, then an `\mathcal O_X`-module `\mathcal F` is coherent if and only if it is of
finite presentation. -/
theorem isCoherent_iff_isFinitePresentation_of_structureSheaf_isCoherent
    [hOX : (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).IsCoherent]
    (ℱ : (RingedSpace.Modules X)) :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation := by
  constructor <;> intro <;> infer_instance

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_12_6 (from Chap17) -/
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
  `RingedSpace.moduleStalkMap`,
  `RingedSpace.moduleRestrictionMap`,
  `RingedSpace.isFiniteType_kernel_of_finiteType_to_coherent`,
  `exists_open_neighborhood_restriction_isZero_of_stalk_isZero`,
  `TopCat.Presheaf.mono_iff_stalk_mono`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, with stalkwise and local-restriction behavior
  expressed by `RingedSpace.moduleStalkMap` and the owner notation `φ |_ U` for
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
- `core/canonical`: `RingedSpace.moduleStalkMap`, `RingedSpace.moduleRestrictionMap`, and the
  kernel object `kernel φ` in `RingedSpace.Modules X`, together with the owner predicate
  `Mono (φ |_ U)`;
- `bridge/view`: the passage from local monomorphy of `φ |_ U` to sectionwise injectivity of
  `φ.val.app (op V)` on all `V ≤ U`.
-/

variable {X : RingedSpace.{u}} {𝒢 ℱ : RingedSpace.Modules X}

-- Proof sketch: let `𝒦 = kernel φ`. Lemma `17.12.4` makes `𝒦` finite type because `𝒢` is finite
-- type and `ℱ` is coherent. The stalk injectivity assumption forces `𝒦_x = 0`, so Lemma `17.9.5`
-- gives an open neighbourhood `U` of `x` with `𝒦|_U = 0`. Restriction preserves kernels, hence
-- `kernel (φ|_U)` is zero and `φ|_U` is mono.
/-- Owner-level companion to Lemma 17.12.6: under the usual finite type/coherent hypotheses, if
the stalk map `φ_x : 𝒢_x → ℱ_x` is injective, then after shrinking around `x` the restricted
morphism `φ |_ U : 𝒢|_U ⟶ ℱ|_U` is a monomorphism. -/
theorem exists_open_neighborhood_mono_restriction_of_stalk_injective
    (φ : 𝒢 ⟶ ℱ) (x : X) [𝒢.IsFiniteType] [ℱ.IsCoherent]
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (φ |_ U) := by
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
      apply hφx
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
theorem exists_open_neighborhood_sectionwise_injective_of_stalk_injective
    (φ : 𝒢 ⟶ ℱ) (x : X) [𝒢.IsFiniteType] [ℱ.IsCoherent]
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U),
      ∀ (V : Opens X) (_ : V ≤ U), Function.Injective (φ.val.app (op V)) := by
  rcases exists_open_neighborhood_mono_restriction_of_stalk_injective φ x hφx with
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
