import Mathlib
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [Ring A] [Ring B] (f : A →+* B)

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)

/- Domain-style sampling for Lemma 15.65.11:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along
  a ring hom `f : A →+* B`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.IsPseudoCoherent`,
  `ModuleCat.restrictScalars`,
  `restrictScalars_exact`,
  `CategoryTheory.Functor.mapDerivedCategory`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the restriction construction itself is owned canonically by the exact derived functor
  `(ModuleCat.restrictScalars f).mapDerivedCategory`; this file should reuse that owner directly
  rather than keep an `Algebra`-specific wrapper;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived `B`-complex `K`, and the pseudo-coherence
  hypothesis on the restricted module object `((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))`;
  derived API is the equivalence between the absolute pseudo-coherence owners on `K` and on its
  image under the canonical restriction functor;
- source/core/bridge triage:
  `source-facing`: `isMPseudoCoherent_iff_restrictScalars`,
    `isPseudoCoherent_iff_restrictScalars`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, `ModuleCat.IsPseudoCoherent`,
    `ModuleCat.restrictScalars`, `restrictScalars_exact`, and
    `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `f` via
    `(ModuleCat.restrictScalars f).mapDerivedCategory`.
-/

local instance restrictScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

/-- Helper for Lemma 15.65.11: if a `B`-module becomes zero after restricting scalars to `A`,
then it was already zero as a `B`-module. -/
lemma isZero_of_restrictScalars_obj
    (M : ModuleCat B)
    (hM : IsZero ((ModuleCat.restrictScalars f).obj M)) :
    IsZero M := by
  -- Restriction of scalars does not change the underlying additive group, so zero objects reflect.
  letI : Subsingleton ↑((ModuleCat.restrictScalars f).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars f).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.65.11: restricting scalars from `B` to `A` commutes with homology on the
derived category of modules. -/
noncomputable def restrictScalars_homology_iso
    (L : DModB) (i : ℤ) :
    (HA i).obj (((ModuleCat.restrictScalars f).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars f).obj ((HB i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eB : (HB i).obj L ≅ K.homology i :=
    ((HB i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Pass to a chosen complex model of `L`, compare homology before and after restriction, and
  -- then return to the derived-category homology objects.
  exact
    (HA i).mapIso
        ((((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
      (ModuleCat.restrictScalars f).mapIso eB.symm

/-- Helper for Lemma 15.65.11: if a derived `A`-complex has zero homology in all degrees `≥ m`,
then it is `m`-pseudo-coherent. -/
lemma derived_isMPseudoCoherent_of_homology_isZero_ge
    (K : DModA) (m : ℤ)
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero ((HA i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E := DerivedCategory.Q.objPreimage K
  have hE : CochainComplex.IsMPseudoCoherent E m := by
    -- Transport the vanishing hypothesis to the chosen cochain representative of `K`.
    refine CochainComplex.isMPseudoCoherent_of_homology_isZero_ge ?_
    intro i hi
    let e :
        (HA i).obj K ≅ E.homology i :=
      ((HA i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app E
    exact (hvanish i hi).of_iso e.symm
  -- The pseudo-coherence predicate is invariant under the chosen `Q.objPreimage` isomorphism.
  exact isMPseudoCoherent_of_iso (DerivedCategory.Q.objObjPreimageIso K) m hE

/-- Helper for Lemma 15.65.11: in a distinguished triangle, if the first morphism is an
isomorphism on homology above `m` and an epimorphism in degree `m`, then the cone has zero
homology in every degree `≥ m`. -/
lemma approximation_cone_isLE_pred
    (T : Triangle DModA) (hT : T ∈ distTriang DModA) (m : ℤ)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((HA i).map T.mor₁))
    (hαepi : Epi ((HA m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : m ≤ i := by
    omega
  have hmor₁_epi : Epi ((HA i).map T.mor₁) := by
    by_cases him_eq : i = m
    · subst him_eq
      exact hαepi
    · have him_lt : m < i := lt_of_le_of_ne him (fun h ↦ him_eq h.symm)
      letI : IsIso ((HA i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hmor₁_mono : Mono ((HA (i + 1)).map T.mor₁) := by
    letI : IsIso ((HA (i + 1)).map T.mor₁) := hαiso (i + 1) (by omega)
    infer_instance
  -- Exactness first kills the middle homology map once the left one is epi.
  have hmor₂_zero : (HA i).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁_epi
  -- The next homology isomorphism forces the connecting morphism to vanish.
  have hδ_zero : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT i (i + 1) rfl).1 hmor₁_mono
  have hmor₂_epi : Epi ((HA i).map T.mor₂) := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT i (i + 1) rfl).2 hδ_zero
  -- A zero epimorphism has zero codomain, so the cone homology vanishes in degree `i`.
  exact IsZero.of_epi_eq_zero ((HA i).map T.mor₂) hmor₂_zero

-- Proof sketch: for `→`, view a bounded finite-free `B`-model for `K` termwise as a bounded-above
-- complex of pseudo-coherent `A`-modules using the hypothesis that `B` is pseudo-coherent over
-- `A` after restriction of scalars along `f`, then apply Lemma `15.65.9` and the
-- distinguished-triangle criterion of Lemma
-- `15.65.2`. For `←`, start from an `A`-linear approximation of the restricted complex, tensor it with `B`,
-- and descend on the top nonvanishing cohomology degree exactly as in the Stacks Project proof.
/-- Lemma 15.65.11: if `f : A →+* B` is a ring map and `B` is pseudo-coherent as an `A`-module,
then a
derived `B`-complex is `m`-pseudo-coherent exactly when its restriction of scalars to `A` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_restrictScalars
    (K : DModB) (m : ℤ)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  constructor
  · intro hK
    -- TODO: source-faithful forward route.
    -- Choose the bounded finite-free `B`-complex witness from `hK`, restrict it termwise to `A`,
    -- use `approximation_cone_isLE_pred` plus `derived_isMPseudoCoherent_of_homology_isZero_ge`
    -- on the restricted cone, then combine Lemmas `15.65.9`, `15.65.6`, and `15.65.2`.
    -- The remaining local work is the module-level closure step saying a finite free `B`-module is
    -- pseudo-coherent over `A` under `hB`.
    sorry
  · intro hK
    -- Route correction: the textbook reverse implication uses extension of scalars
    -- `E^• ⊗_A B → K^•`. On the current statement surface `[Ring A] [Ring B]`, the available
    -- `ModuleCat.extendScalars` / `extendRestrictScalarsAdj` API is only for commutative rings,
    -- so the source-faithful induction cannot currently be expressed from the dependency-closed
    -- earlier API without an additional noncommutative change-of-rings bridge or a corrected
    -- statement surface.
    sorry

-- Proof sketch: apply `isMPseudoCoherent_iff_restrictScalars` for every `m : ℤ` and use the
-- characterization of pseudo-coherence as `m`-pseudo-coherence for all `m` from Lemma `15.65.5`
-- on both the `B`-linear complex and its restriction to `A`.
/-- Under the same hypothesis on `B`, pseudo-coherence of a derived `B`-complex is equivalent to
pseudo-coherence after restriction of scalars to `A`. -/
theorem isPseudoCoherent_iff_restrictScalars
    (K : DModB)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsPseudoCoherent ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsPseudoCoherent := by
  -- TODO: once the main degreewise comparison is completed, rewrite both sides with
  -- `isPseudoCoherent_iff_forall_isMPseudoCoherent` and apply
  -- `isMPseudoCoherent_iff_restrictScalars` degreewise.
  sorry

end

end CategoryTheory
