import Mathlib
import Mathlib.CategoryTheory.Sites.Abelian
import StacksProject_2024.Chap12.Definition_12_10_1
import StacksProject_2024.Chap18.Definition_18_43_1_Finite
import StacksProject_2024.Chap18.Lemma_18_43_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w u₁

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Sets

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- Helper for Lemma 18.43.5: finite locally constant set-valued sheaves stay finite locally
constant after transport along an isomorphism. -/
theorem isFiniteLocallyConstant_of_iso
    {F G : Sheaf J (Type w)} (e : F ≅ G) [IsFiniteLocallyConstant F] :
    IsFiniteLocallyConstant G := by
  refine ⟨?_⟩
  intro U
  -- Proof comment: reuse the same slice cover and transport each local constant model through the
  -- restricted isomorphism.
  obtain ⟨I, X, hX, hconst⟩ := IsFiniteLocallyConstant.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨E, hE, ⟨eF⟩⟩ := hconst i
  refine ⟨E, hE, ?_⟩
  refine ⟨((J.overPullback (Type w) (X i).left).mapIso e).symm ≪≫ eF⟩

/-- Helper for Lemma 18.43.5: the object property of finite locally constant set-valued sheaves is
stable under isomorphisms. -/
instance finiteLocallyConstant_isClosedUnderIsomorphisms :
    (finiteLocallyConstant J).IsClosedUnderIsomorphisms where
  of_iso e hF := by
    -- Proof comment: transport the chosen finite constant charts across the ambient isomorphism.
    exact isFiniteLocallyConstant_of_iso (J := J) e

-- Proof sketch: work locally on the site and use the local triviality criterion from the previous
-- lemma to reduce a finite diagram of finite locally constant sheaves to a diagram of constant
-- finite sets. Finite limits of finite sets are finite, and the associated constant sheaf computes
-- the ambient sheaf limit locally.
/-- Lemma 18.43.5 (1): finite locally constant sheaves of sets are closed under finite limits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under limits of that shape. -/
@[stacks 093U]
theorem isFiniteLocallyConstant_isClosedUnderFiniteLimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape (finiteLocallyConstant J) K := by
  -- Proof comment: after restricting to a common slice-site cover, the whole finite diagram should
  -- become a diagram of constant sheaves on finite sets, so the chosen sheaf limit is locally the
  -- constant sheaf on the finite limit of that diagram of sets.
  -- TODO: build the common finite-diagram chart promised by Lemma 18.43.3 and identify the local
  -- sheaf limit with the constant sheaf on the finite set-theoretic limit.
  sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderLimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderLimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape (finiteLocallyConstant J) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteLimits K

-- Proof sketch: after local trivialization, a finite diagram becomes a diagram of constant sheaves
-- attached to finite sets. Finite colimits of finite sets are finite, so the ambient sheaf colimit
-- is again locally a constant finite sheaf.
/-- Lemma 18.43.5 (2): finite locally constant sheaves of sets are closed under finite colimits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under colimits of that shape. -/
@[stacks 093U]
theorem isFiniteLocallyConstant_isClosedUnderFiniteColimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape (finiteLocallyConstant J) K := by
  -- Proof comment: the same common local trivialization reduces the chosen sheaf colimit to the
  -- constant sheaf on the finite colimit of a finite diagram of finite sets.
  -- TODO: reuse the common finite-diagram chart from the limit case and compare the restricted
  -- colimit with the constant sheaf on the finite set-theoretic colimit.
  sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderColimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderColimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape (finiteLocallyConstant J) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteColimits K

end Sets

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [Abelian (Sheaf J AddCommGrpCat.{w})]

/-- Helper for Lemma 18.43.5: finite locally constant sheaves of abelian groups stay finite
locally constant after transport along an isomorphism. -/
theorem isFiniteLocallyConstantAddCommGrp_of_iso
    {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) [IsFiniteLocallyConstantAddCommGrp F] :
    IsFiniteLocallyConstantAddCommGrp G := by
  refine ⟨?_⟩
  intro U
  -- Proof comment: keep the same local finite abelian-group models and move them across the
  -- restricted isomorphism.
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteLocallyConstantAddCommGrp.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨A, hA, ⟨eF⟩⟩ := hconst i
  refine ⟨A, hA, ?_⟩
  refine ⟨((J.overPullback AddCommGrpCat.{w} (X i).left).mapIso e).symm ≪≫ eF⟩

/-- Helper for Lemma 18.43.5: the object property of finite locally constant abelian sheaves is
stable under isomorphisms. -/
instance finiteLocallyConstantAddCommGrp_isClosedUnderIsomorphisms :
    (finiteLocallyConstantAddCommGrp J).IsClosedUnderIsomorphisms where
  of_iso e hF := by
    -- Proof comment: transport each local finite abelian-group chart across the ambient
    -- isomorphism.
    exact isFiniteLocallyConstantAddCommGrp_of_iso (J := J) e

/-- Helper for Lemma 18.43.5: kernels of morphisms between finite locally constant sheaves of
abelian groups remain finite locally constant. -/
theorem isFiniteLocallyConstantAddCommGrp_kernel
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsFiniteLocallyConstantAddCommGrp G] :
    IsFiniteLocallyConstantAddCommGrp (kernel φ) := by
  -- TODO: the intended route is the same as in the module case below: trivialize `φ` locally,
  -- identify the restricted kernel with the kernel of the localized constant map, and then show
  -- the kernel of a map of finite abelian groups is finite.
  sorry

/-- Helper for Lemma 18.43.5: cokernels of morphisms between finite locally constant sheaves of
abelian groups remain finite locally constant. -/
theorem isFiniteLocallyConstantAddCommGrp_cokernel
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsFiniteLocallyConstantAddCommGrp G] :
    IsFiniteLocallyConstantAddCommGrp (cokernel φ) := by
  -- TODO: trivialize `φ` locally, compare the restricted cokernel with the cokernel of the
  -- localized constant map, and use finiteness of cokernels of finite abelian groups.
  sorry

-- Proof sketch: apply the weak-Serre criterion recorded in the imported owner abstraction.
-- Kernels and cokernels are handled locally by trivializing maps, and extensions are checked after
-- refining to a cover where the end terms are constant finite abelian sheaves.
/-- Lemma 18.43.5 (3): finite locally constant abelian sheaves form a weak Serre subcategory of
`Ab(\mathcal C)`. -/
@[stacks 093U]
theorem isFiniteLocallyConstantAddCommGrp_isWeakSerreClass :
    IsWeakSerreClass (finiteLocallyConstantAddCommGrp J) :=
  by
  -- Route correction: the kernel/cokernel steps are now isolated in the dedicated helpers above.
  -- The remaining frontier is to package zero, kernel, cokernel, and extension closure into the
  -- weak-Serre criterion without adding extra assumptions to the source-facing theorem.
  -- TODO: after restoring the kernel/cokernel transport lemmas, package zero, kernel, cokernel,
  -- and the local extension lemma into `isWeakSerreClass_of_closure`.
  sorry

/-- Finite locally constant abelian sheaves carry their canonical weak-Serre instance. -/
instance isFiniteLocallyConstantAddCommGrp_instWeakSerreClass :
    IsWeakSerreClass (finiteLocallyConstantAddCommGrp J) :=
  isFiniteLocallyConstantAddCommGrp_isWeakSerreClass

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]

/-- Helper for Lemma 18.43.5: finite-type locally constant module sheaves stay finite-type
locally constant after transport along an isomorphism. -/
theorem isFiniteTypeLocallyConstantModule_of_iso
    {F G : Sheaf J (ModuleCat.{w} Λ)} (e : F ≅ G) [IsFiniteTypeLocallyConstantModule F] :
    IsFiniteTypeLocallyConstantModule G := by
  refine ⟨?_⟩
  intro U
  -- Proof comment: the same slice-site cover works after transporting each finite-type constant
  -- module chart through the restricted isomorphism.
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteTypeLocallyConstantModule.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨M, hM, ⟨eF⟩⟩ := hconst i
  refine ⟨M, hM, ?_⟩
  refine ⟨((J.overPullback (ModuleCat.{w} Λ) (X i).left).mapIso e).symm ≪≫ eF⟩

/-- Helper for Lemma 18.43.5: the object property of finite-type locally constant module sheaves
is stable under isomorphisms. -/
instance finiteTypeLocallyConstantModule_isClosedUnderIsomorphisms :
    (finiteTypeLocallyConstantModule J Λ).IsClosedUnderIsomorphisms where
  of_iso e hF := by
    -- Proof comment: transport the local finite-type constant module charts across the ambient
    -- isomorphism.
    exact isFiniteTypeLocallyConstantModule_of_iso (J := J) (Λ := Λ) e

/-- Helper for Lemma 18.43.5: kernels of morphisms between finite-type locally constant module
sheaves remain finite-type locally constant. -/
theorem isFiniteTypeLocallyConstantModule_kernel
    {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsFiniteTypeLocallyConstantModule G] :
    IsFiniteTypeLocallyConstantModule (kernel φ) := by
  -- TODO: localize `φ` to a map of constant finite-type modules, transport the restricted kernel
  -- to the kernel of that constant map, and invoke Noetherian finiteness for submodules.
  sorry

/-- Helper for Lemma 18.43.5: cokernels of morphisms between finite-type locally constant module
sheaves remain finite-type locally constant. -/
theorem isFiniteTypeLocallyConstantModule_cokernel
    {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsFiniteTypeLocallyConstantModule G] :
    IsFiniteTypeLocallyConstantModule (cokernel φ) := by
  -- TODO: localize `φ` to a map of constant finite-type modules, transport the restricted
  -- cokernel to the cokernel of that constant map, and use Noetherian finiteness for quotients.
  sorry

-- Proof sketch: again use the weak-Serre criterion. After local trivialization, kernels and
-- cokernels are kernels and cokernels of maps of finite type `\Lambda`-modules; the Noetherian
-- hypothesis guarantees these remain finite type, and the extension argument follows from the
-- pushout description in the source text.
/-- Lemma 18.43.5 (4): for a Noetherian ring `\Lambda`, locally constant sheaves of finite type
`\Lambda`-modules form a weak Serre subcategory of `Mod(\mathcal C, \Lambda)`. -/
@[stacks 093U]
theorem isFiniteTypeLocallyConstantModule_isWeakSerreClass :
    IsWeakSerreClass (finiteTypeLocallyConstantModule J Λ) :=
  by
  -- Route correction: the kernel/cokernel steps are isolated in the local helpers above. The
  -- remaining structural blocker is the source-text finite-presentation argument for extensions,
  -- together with a zero-object packaging route that does not strengthen the theorem assumptions.
  -- TODO: once the kernel/cokernel transport and the local extension lemma are restored, package
  -- the closure data through `isWeakSerreClass_of_closure`.
  sorry

/-- Finite type locally constant module sheaves carry their canonical weak-Serre instance. -/
instance isFiniteTypeLocallyConstantModule_instWeakSerreClass :
    IsWeakSerreClass (finiteTypeLocallyConstantModule J Λ) :=
  isFiniteTypeLocallyConstantModule_isWeakSerreClass

end Modules

end

end Sheaf
end CategoryTheory
