import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.LeftExact
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_55_1 (from Chap15) -/
open CategoryTheory
open ModuleCat

universe u v

section

variable (R : Type u) [Ring R] (J : Type v) [AddCommGroup J] [Module R J]

namespace Module

-- Domain-style sampling:
-- * primary domain: injective objects in the abelian category `ModuleCat R`, expressed through the
--   represented contravariant Hom functor `preadditiveYonedaObj`.
-- * inspected owner declarations: `CategoryTheory.injective_iff_exact_preadditiveYonedaObj`,
--   `Module.injective_iff_injective_object`, and the underlying mathlib criterion
--   `injective_of_preservesFiniteColimits_preadditiveYonedaObj`.
-- * best owner abstraction: categorical injectivity of `of R J`.
-- * layer: `bridge/view`; the source item is the module-level reformulation of the Chapter 12
--   owner theorem.
-- * primitive data: only the `R`-module `J`.
-- * derived API: exactness of `preadditiveYonedaObj (of R J)`.

/-- Definition 15.55.1: an `R`-module `J` is injective if and only if the contravariant Hom
functor `Hom_R(-, J)`, formalized as `preadditiveYonedaObj (of R J)`, is exact. -/
theorem injective_iff_exact_preadditiveYonedaObj :
    Module.Injective R J ↔
      exactFunctor (ModuleCat R)ᵒᵖ _ (preadditiveYonedaObj (of R J)) := by
  letI := CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  simpa [Module.injective_iff_injective_object R J] using
    (CategoryTheory.injective_iff_exact_preadditiveYonedaObj (of R J))

end Module

end

/-! ### Lemma_15_55_2 (from Chap15) -/
namespace CategoryTheory.Abelian.Ext

/- Domain-style sampling for Lemma 15.55.2:
- primary domain: `Ext¹` for the abelian category of `R`-modules and its classification by short
  exact sequences;
- sampled owner declarations:
  `ExtensionClass.toExtAddEquiv`,
  `ExtensionClass.toExt_pullback`,
  `contravariantSequence`,
  `covariantSequence_exact`,
  `covariantSequence`,
  `contravariantSequence_exact`,
  `mono_precomp_mk₀_of_epi`,
  `mono_postcomp_mk₀_of_mono`,
  `addEquiv₀`;
- best owner abstraction: the source-facing extension group is `ExtensionClass`, the canonical
  owner is `Ext`, the project-level bridge is owned by
  `StacksProject_2024.Chap12.Lemma_12_6_3`, and the surrounding long exact sequences are owned by
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`;
- primitive data: the ambient module category and the two module objects;
- derived API: the additive comparison `ExtensionClass N M ≃+ Ext M N 1`, its pullback/pushout
  compatibility, the packaged long exact sequences, their exactness theorems, the leading
  degree-`0` monomorphisms, and the canonical identification `Ext⁰ ≃ Hom`.

Source/core/bridge triage:
- `source-facing`: `ExtensionClass N M`;
- `core/canonical`: `Ext M N 1`;
- `bridge/view`: `ExtensionClass.toExtAddEquiv`.

This file stays at the `bridge/view` layer: it recalls the canonical comparison and its standard
companions, without introducing any parallel module-specific wrapper API.
-/
/- Lemma 15.55.2: in the abelian category of `R`-modules, the categorical extension group
`Ext_𝒜(M, N)` is the source-facing owner `ExtensionClass N M`, and the canonical comparison with
the algebraic group `Ext¹_R(M, N)` is `ExtensionClass.toExtAddEquiv`. The source compatibility
with the long exact and six-term `Ext` sequences is expressed by the canonical owner sequence
declarations and their degree-`0` companions recalled below. -/
recall ExtensionClass.toExtAddEquiv

/- Companion recall: the comparison is compatible with pullback in the first `Ext` variable via
the canonical theorem `ExtensionClass.toExt_pullback`. -/
recall ExtensionClass.toExt_pullback

/- Companion recall: the comparison is compatible with pushout in the second `Ext` variable via
the canonical theorem `ExtensionClass.toExt_pushout`. -/
recall ExtensionClass.toExt_pushout

/- Companion recall: the contravariant six-term exact sequence is the canonical owner theorem
`contravariantSequence_exact`. -/
recall contravariantSequence_exact

/- Companion recall: the contravariant long exact sequence itself is packaged by the owner
declaration `contravariantSequence`. -/
recall contravariantSequence

/- Companion recall: the first degree-`0` map in the contravariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M'', N)` in the textbook six-term display. -/
recall mono_precomp_mk₀_of_epi

/- Companion recall: the covariant six-term exact sequence is the canonical owner theorem
`covariantSequence_exact`. -/
recall covariantSequence_exact

/- Companion recall: the covariant long exact sequence itself is packaged by the owner declaration
`covariantSequence`. -/
recall covariantSequence

/- Companion recall: the first degree-`0` map in the covariant sequence is monic, giving the
leading `0 ⟶ Hom_R(M, N')` in the textbook six-term display. -/
recall mono_postcomp_mk₀_of_mono

/- Companion recall: degree `0` `Ext` is canonically identified with `Hom` by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext

/-! ### Lemma_15_55_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Abelian

universe u

namespace CategoryTheory

section

attribute [local instance] CategoryTheory.HasExt.standard

variable (R : Type u) [Ring R]
variable (J : ModuleCat.{u} R)

/- Domain-style sampling:
- primary domain: injective objects and degree-one `Ext` in the abelian category `ModuleCat R`;
- inspected owner declarations:
  `CategoryTheory.injective_iff_ext_one_eq_zero`,
  `subsingleton_iff_forall_eq 0`;
- best owner abstraction: the canonical owner is `Injective J`, with `Ext M J 1` as the derived
  degree-one obstruction group;
- primitive data: only the ring `R` and module object `J`;
- derived API: the vanishing formulation `∀ M, ∀ e : Ext M J 1, e = 0`, exposed directly by the
  chapter-level companion theorem.
- layer: `bridge/view`; this file only specializes the Chapter 12 owner theorem to `ModuleCat R`,
  so it should recall that canonical declaration directly instead of keeping a parallel local
  theorem name.

This item is the module-category specialization of the canonical injective-versus-`Ext¹`
criterion, so the main entry should be a direct specialization of the Chapter 12 owner theorem,
not a duplicate local shell. -/

/- Lemma 15.55.3: an `R`-module `J` is injective if and only if `Ext^1_R(M, J)` vanishes for
every `R`-module `M`. This is exactly the canonical owner theorem
`injective_iff_ext_one_eq_zero`, specialized to `ModuleCat R`. -/
#check (injective_iff_ext_one_eq_zero J :
  Injective J ↔ ∀ M : ModuleCat R, ∀ e : Ext M J 1, e = 0)

end

end CategoryTheory

/-! ### Lemma_15_55_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Module
open ModuleCat
open ShortComplex

universe u

namespace CategoryTheory

attribute [local instance] CategoryTheory.HasExt.standard

section

variable (R : Type u) [Ring R]
variable (J : ModuleCat.{u} R)

-- Domain-style sampling:
-- * primary domain: injective `R`-modules, Baer's criterion, and degree-one `Ext` in `ModuleCat R`.
-- * inspected owner declarations: `CategoryTheory.injective_iff_ext_one_eq_zero`,
--   `Module.Baer.iff_injective`, and
--   `Ext.contravariant_sequence_exact₁`.
-- * best owner abstraction: the canonical owners are `Injective J` on `ModuleCat R`,
--   `Module.Baer R J`, and the `Ext` connecting morphism attached to the quotient short exact
--   sequence; the local file should specialize those owners directly rather than introduce a
--   parallel quotient-module or connecting-map wrapper.
-- * owner choice: the `Ext¹`-vanishing criterion is already owned by the chapter-12 theorem
--   `CategoryTheory.injective_iff_ext_one_eq_zero`, whose implicit source object specializes
--   directly to `ModuleCat R`; this file should use that owner rather than the local
--   module-category wrapper from the same chapter.
-- * layer: `source-facing`; the lemma is the ideal-quotient specialization of the general
--   injective-via-`Ext` criterion, compared with the source's Baer condition.
-- * primitive data: the ring `R`, the module object `J : ModuleCat R`, and an ideal `I : Ideal R`.
-- * bridge/view: the source quotient `R ⧸ I` and its short exact sequence
--   `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` are already canonical in `ModuleCat R`, built from `I.mkQ` and
--   `LinearMap.exact_subtype_mkQ I`, so the proof should use that owner directly rather than
--   introduce a parallel local short-complex wrapper.
-- * derived API: the degree-one group `Ext (ModuleCat.of R (R ⧸ I)) J 1` and the connecting map
--   from `Hom_R(I, J)`, with the degree-zero comparison handled by the primitive owner
--   `Ext.mk₀`/`Ext.homEquiv₀` rather than the linearized wrapper API.

/-- Lemma 15.55.4: for an `R`-module `J`, the following are equivalent: `J` is injective,
`Ext^1_R(R/I, J)` is trivial for every ideal `I ⊆ R`, and every `R`-linear map `I → J` extends to
an `R`-linear map `R → J` (equivalently, `J` satisfies Baer's criterion). -/
-- Proof sketch: `(1) ↔ (3)` is Baer's criterion via
-- `Module.Baer.iff_injective` and `Module.injective_iff_injective_object`. For `(1) → (2)`,
-- apply the owner theorem `CategoryTheory.injective_iff_ext_one_eq_zero`.
-- For `(2) → (3)`,
-- apply the contravariant long exact `Ext` sequence to the canonical quotient short exact sequence
-- `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0`: if `Ext¹_R(R/I, J) = 0`, then every class in
-- `Ext⁰_R(I, J) = Hom_R(I, J)` lies in the image of `Hom_R(R, J)`.
theorem injective_tfae_extOneFromIdealQuotient_eq_zero_baer :
    List.TFAE
      [ Injective J
      , ∀ I : Ideal R, ∀ e : Ext (ModuleCat.of R (R ⧸ I)) J 1, e = 0
      , Module.Baer R J
      ] := by
  tfae_have 1 ↔ 3 := by
    simpa [Module.injective_iff_injective_object R J] using
      (show Module.Injective R J ↔ Module.Baer R J from Baer.iff_injective.symm)
  tfae_have 1 → 2 := by
    intro hJ I e
    exact ((injective_iff_ext_one_eq_zero J).1 hJ) e
  tfae_have 2 → 3 := by
    intro hExt I g
    let S :=
      moduleCatMk I.subtype I.mkQ
        (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
    have hS : S.ShortExact := by
      refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
      · simpa [S] using LinearMap.exact_subtype_mkQ I
      · exact Subtype.coe_injective
      · simpa [S] using I.mkQ_surjective
    let gHom : S.X₁ ⟶ J := by
      simpa [S] using (ModuleCat.ofHom g)
    let gExt : Ext S.X₁ J 0 := Ext.mk₀ gHom
    have hgExt : hS.extClass.comp gExt (show 1 + 0 = 1 by simp) = 0 := hExt I _
    obtain ⟨g'Ext, hg'Ext⟩ := contravariant_sequence_exact₁ hS J gExt (by simp) hgExt
    obtain ⟨g'Hom, rfl⟩ := homEquiv₀.symm.surjective g'Ext
    have hg'Hom : S.f ≫ g'Hom = gHom := by
      apply homEquiv₀.symm.injective
      simpa [Ext.homEquiv₀_symm_apply, gExt, Ext.mk₀_comp_mk₀] using hg'Ext
    let g' : ModuleCat.of R R ⟶ J := by
      simpa [S] using g'Hom
    have hg' : g'.hom.comp I.subtype = g := by
      exact ModuleCat.hom_ext_iff.mp <| by
        simpa [S, g'] using hg'Hom
    refine ⟨g'.hom, ?_⟩
    intro x hx
    simpa using LinearMap.congr_fun hg' ⟨x, hx⟩
  tfae_finish

end

end CategoryTheory

/-! ### Definition_15_55_5 (from Chap15) -/
open CategoryTheory ModuleCat

universe u v

variable (R : Type u)

/-!
Domain-style sampling:
- primary domain: character modules and the free-forget adjunction on `ModuleCat R`;
- sampled owner API:
  `CharacterModule.dual`,
  `ModuleCat.free`,
  `ModuleCat.adj`,
  `Adjunction.counit`;
- owner abstraction:
  `source-facing`: the arbitrary-ring character-module functor;
  `core/canonical`: `CharacterModule.dual` on the commutative side and the counit
    `(ModuleCat.adj R).counit` of the free-forget adjunction;
  `bridge/view`: the opposite-ring linearization of `CharacterModule.dual`. The textbook
    assignment `M ↦ (F(M) → M)` is only the Arrow-valued view of the counit, so the file should
    recall `(ModuleCat.adj R).counit` directly rather than keep a parallel wrapper functor.
- primitive versus derived:
  the primitive data are only the ambient module and the canonical owners above. The
  free-presentation viewpoint is derived from the free-module counit, not a second primitive owner
  abstraction.
-/

postfix:max "^∨" => CharacterModule

section CharacterModuleGeneral

variable [Ring R]

namespace CharacterModule

instance moduleOpposite
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module Rᵐᵒᵖ M^∨ :=
  AddMonoidHom.instDomMulActModule

@[simp] theorem op_smul_apply
    {M : Type v} [AddCommGroup M] [Module R M]
    (r : Rᵐᵒᵖ) (χ : M^∨) (m : M) :
    (r • χ) m = χ (MulOpposite.unop r • m) :=
  DomMulAct.smul_addMonoidHom_apply r χ m

private instance doubleModule
    {M : Type v} [AddCommGroup M] [Module R M] :
    Module R ((M^∨)^∨) :=
  Module.compHom ((M^∨)^∨) (RingEquiv.opOp R).toRingHom

/-- The canonical evaluation map from a module to its double character module. -/
noncomputable def eval
    {M : Type v} [AddCommGroup M] [Module R M] : M →ₗ[R] (M^∨)^∨ :=
  { toFun := fun m ↦
      { toFun := fun χ ↦ χ m
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    map_add' := by
      intro m n
      ext χ
      exact χ.map_add m n
    map_smul' := by
      intro r m
      ext χ
      change χ (r • m) = ((MulOpposite.op r : Rᵐᵒᵖ) • χ) m
      simp [op_smul_apply] }

/-- The double-character evaluation map evaluates a character at the chosen module element. -/
@[simp] theorem eval_apply
    {M : Type v} [AddCommGroup M] [Module R M] (m : M) (χ : M^∨) :
    ((eval R) m) χ = χ m := rfl

end CharacterModule

/-- Definition 15.55.5: for an arbitrary ring `R`, the character-module construction is the
contravariant functor `M ↦ M^∨` from left `R`-modules to left `Rᵐᵒᵖ`-modules. -/
noncomputable def CharacterModule.functor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ where
  obj M := ModuleCat.of Rᵐᵒᵖ M.unop^∨
  map {X Y} f :=
    let f' := f.unop.hom
    ModuleCat.ofHom
      { toFun := fun χ ↦ CharacterModule.dual (f'.restrictScalars ℤ) χ
        map_add' := by
          intro χ ψ
          rfl
        map_smul' := by
          intro r χ
          ext m
          change χ (MulOpposite.unop r • f' m) = χ (f' (MulOpposite.unop r • m))
          rw [f'.map_smul] }
  map_id M := by
    ext χ m
    rfl
  map_comp f g := by
    ext χ m
    rfl

instance : (CharacterModule.functor R).PreservesZeroMorphisms where
  map_zero {X Y} := by
    ext χ
    change CharacterModule.dual ((0 : Y.unop ⟶ X.unop).hom.restrictScalars ℤ) χ = 0
    apply CharacterModule.ext
    intro m
    change
      (AddMonoidHom.comp χ (LinearMap.toAddMonoidHom (0 : Y.unop →ₗ[ℤ] X.unop))) m =
        (0 : Y.unop →+ AddCircle (1 : ℚ)) m
    simp

end CharacterModuleGeneral

section FreeModulePresentation

variable [Ring R]

/- Definition 15.55.5: the textbook assignment `M ↦ (F(M) → M)` is the counit of the
free-forget adjunction on `ModuleCat R`. The Arrow-valued functor is derived packaging of this
canonical natural transformation, so the file recalls the counit directly. -/
#check (ModuleCat.adj R).counit

end FreeModulePresentation

/-! ### Lemma_15_55_6 (from Chap15) -/
open CategoryTheory ModuleCat

universe u v

/-!
Domain-style sampling:
- primary domain: character modules as a contravariant functor on module categories;
- sampled owner declarations:
  `functor`,
  `CharacterModule.dual`,
  `LinearMap.exact_lcomp_of_exact_of_surjective`,
  `CharacterModule.dual_injective_of_surjective`,
  `CharacterModule.dual_surjective_of_injective`;
- best owner abstraction: the `source-facing` owner is the contravariant functor
  `functor : (ModuleCat R)ᵒᵖ ⥤ ModuleCat Rᵐᵒᵖ`;
- primitive data: a short exact short complex `S : ShortComplex (ModuleCat R)`;
- derived API: exactness of precomposition with a surjective linear map together with injectivity
  and surjectivity of the induced functorial maps;
- layer split: the additive exactness lemma below is an internal `bridge/view`, while
  `CharacterModule.shortExact_of_shortExact` is the `source-facing` Stacks statement.
-/

section

variable {R : Type u} [Ring R]

namespace CharacterModule

/-- Exactness of the dual maps follows from exactness of precomposition on the underlying
`ℤ`-linear maps. -/
private theorem dual_exact_of_exact_of_surjective
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hfg : Function.Exact f g)
    (hsurj : Function.Surjective g) :
    Function.Exact (dual (g.restrictScalars ℤ)) (dual (f.restrictScalars ℤ)) := by
  let D := AddCircle (1 : ℚ)
  let f' := f.restrictScalars ℤ
  let g' := g.restrictScalars ℤ
  have hExact :
      Function.Exact (LinearMap.lcomp ℤ D g') (LinearMap.lcomp ℤ D f') :=
    LinearMap.exact_lcomp_of_exact_of_surjective D hfg hsurj
  have hcomp : g'.comp f' = 0 := by
    ext x
    simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero x
  intro χ
  constructor
  · intro hχ
    have hχ' : LinearMap.lcomp ℤ D f' χ.toIntLinearMap = 0 := by
      ext x
      simpa using DFunLike.congr_fun hχ x
    rcases (hExact χ.toIntLinearMap).1 hχ' with ⟨ψ, hψ⟩
    refine ⟨ψ.toAddMonoidHom, ?_⟩
    ext x
    simpa using DFunLike.congr_fun hψ x
  · rintro ⟨ψ, rfl⟩
    ext x
    change ψ ((g'.comp f') x) = 0
    simp [hcomp]

/-- Lemma 15.55.6: if `S` is a short exact sequence of left `R`-modules, then applying the
contravariant character-module functor yields a short exact sequence of left `Rᵐᵒᵖ`-modules. -/
theorem shortExact_of_shortExact
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.op.map (functor R)).ShortExact := by
  let f := S.f.hom
  let g := S.g.hom
  have hfg : Function.Exact S.f S.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hg : Function.Surjective S.g := hS.moduleCat_surjective_g
  have hf : Function.Injective S.f := hS.moduleCat_injective_f
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact (dual (g.restrictScalars ℤ)) (dual (f.restrictScalars ℤ))
    exact dual_exact_of_exact_of_surjective f g hfg hg
  · change Function.Injective (dual (g.restrictScalars ℤ))
    exact dual_injective_of_surjective (g.restrictScalars ℤ) hg
  · change Function.Surjective (dual (f.restrictScalars ℤ))
    exact dual_surjective_of_injective (f.restrictScalars ℤ) hf

end CharacterModule

end

/-! ### Lemma_15_55_7 (from Chap15) -/
universe u v

/-!
Domain-style sampling:
- primary domain: character modules over arbitrary rings, their opposite-ring module structure, and
  the canonical evaluation map into the double character module;
- sampled owner API:
  `CharacterModule.eval`,
  `CharacterModule.eq_zero_of_character_apply`,
  `DomMulAct.smul_addMonoidHom_apply`,
  `Module.Dual.eval`;
- owner abstraction:
  `source-facing`: injectivity of the canonical evaluation map for arbitrary-ring character
    modules;
  `core/canonical`: `CharacterModule.eval R M : M → (M^∨)^∨`, where the double character module
    is viewed as an `R`-module by applying `CharacterModule.moduleOpposite` twice;
  `bridge/view`: the commutative-ring specialization `Module.Dual.eval`.
- primitive versus derived:
  the primitive data are only the ambient `R`-module `M`, while injectivity is derived from the
  canonical separation lemma `CharacterModule.eq_zero_of_character_apply`; no additional wrapper
  around the double character module or its evaluation map is mathematically needed here.
-/

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CharacterModule

-- Proof sketch: if `m` maps to `0` in the double character module, then every character
-- `φ : M^∨` vanishes on `m`. The canonical separation theorem
-- `CharacterModule.eq_zero_of_character_apply` then forces `m = 0`.
/-- Lemma 15.55.7: for any `R`-module `M`, the canonical evaluation map
`M → (M^∨)^∨`, realized as `CharacterModule.eval`, is injective. -/
theorem eval_injective : Function.Injective (eval R : M →ₗ[R] (M^∨)^∨) :=
  (injective_iff_map_eq_zero _).2 fun m hm ↦
    eq_zero_of_character_apply fun φ ↦ by
      simpa [eval_apply] using DFunLike.congr_fun hm φ

end CharacterModule

end

/-! ### Lemma_15_55_8 (from Chap15) -/
open CategoryTheory ModuleCat

universe u v

/-!
Domain-style sampling:
- primary domain: injective objects in `ModuleCat R`, obtained from injective abelian groups by the
  change-of-rings adjunction `restrictScalars ⊣ coextendScalars`;
- sampled owner declarations:
  `AddCommGrpCat.injective_of_divisible`,
  `AddCommGrpCat.injective_as_module_iff`,
  `ModuleCat.restrictCoextendScalarsAdj`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`;
- best owner abstraction:
  `source-facing`: `jModule R M`;
  `core/canonical`: categorical `Injective` in `ModuleCat`, together with preservation of
    injective objects by `coextendScalars (algebraMap ℤ R)`;
  `bridge/view`: `Module.injective_iff_injective_object`;
- primitive data: the ring `R` and the additive group `M`; the `R`-module structure on `M` does
  not enter the construction of `J(M)`;
- derived API: injectivity of `jModule R M` as an `R`-module.
-/

section

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M]

/-- The textbook module `J(M)`, realized by coextending scalars from the injective abelian group
of `ULift (ℚ/ℤ)`-valued functions on the character module `Mᵛ`. -/
noncomputable abbrev jModule : ModuleCat R :=
  (ModuleCat.coextendScalars (algebraMap ℤ R)).obj
    (ModuleCat.of ℤ (CharacterModule M → ULift.{max u v} (AddCircle (1 : ℚ))))

-- Proof sketch: the abelian group `(Mᵛ → ULift (ℚ/ℤ))` is a product of injective abelian groups,
-- so it is injective in `AddCommGrpCat`. The right adjoint `coextendScalars (algebraMap ℤ R)`
-- preserves injective objects, hence its image `jModule R M` is injective as an `R`-module.
/-- Lemma 15.55.8: for every `R`-module `M`, the module `J(M)`, formalized as `jModule R M`, is
injective. -/
theorem jModule_injective :
    Module.Injective R (jModule R M) := by
  let A := CharacterModule M → ULift.{max u v} (AddCircle (1 : ℚ))
  let source : ModuleCat.{max u v} ℤ := ModuleCat.of ℤ A
  have hSource : Injective source := by
    let hGroup : Injective (AddCommGrpCat.of A) := AddCommGrpCat.injective_of_divisible A
    simpa [source, A] using (AddCommGrpCat.injective_as_module_iff A).mpr hGroup
  let res : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} ℤ :=
    restrictScalars (algebraMap ℤ R)
  let coext : ModuleCat.{max u v} ℤ ⥤ ModuleCat.{max u v} R :=
    coextendScalars (algebraMap ℤ R)
  have adj : res ⊣ coext := by
    simpa [res, coext] using restrictCoextendScalarsAdj (algebraMap ℤ R)
  have hTarget : Injective (coext.obj source) := by
    let _ : res.PreservesMonomorphisms := by infer_instance
    let _ : coext.PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    exact coext.injective_obj_of_injective hSource
  simpa [jModule, source, A, coext, Module.injective_iff_injective_object R] using hTarget

end

/-! ### Lemma_15_55_9 (from Chap15) -/
universe u

namespace CategoryTheory

noncomputable section

open ModuleCat

/- Domain-style sampling for Lemma 15.55.9:
- primary domain: the Chapter 15 construction of functorial injective embeddings in `ModuleCat R`
  from the explicit targets `J(M)`;
- sampled owner-level declarations:
  `jModule`,
  `CharacterModule.eval`,
  `CharacterModule.eval_injective`,
  `NatTrans.arrowFunctor`,
  `ModuleCat.restrictCoextendScalarsAdj`,
  `HasFunctorialInjectiveEmbeddings`;
- best owner abstraction:
  `source-facing`: the canonical natural transformation `𝟭 ⟶ jFunctor R` whose component at `M`
    is the explicit embedding `M ⟶ J(M)` into the module `jModule R M` of Lemma `15.55.8`;
  `core/canonical`: the Chapter 12 owner `HasFunctorialInjectiveEmbeddings (ModuleCat R)`;
  `bridge/view`: the induced Arrow-valued functor `(jEmbeddingNatTrans R).arrowFunctor` and the
    resulting `HasFunctorialInjectiveEmbeddings` instance;
- primitive data: the explicit target `jModule R M` and the canonical evaluation map
  `CharacterModule.eval`, transported through `restrictCoextendScalarsAdj (algebraMap ℤ R)`;
- derived API: objectwise injectivity of the map `M ⟶ J(M)`, the Arrow-valued view provided by
  `NatTrans.arrowFunctor`, and the induced
  `HasFunctorialInjectiveEmbeddings` instance.

This file is `source-facing`: Stacks Lemma `15.55.9` is about the specific construction
`M ↦ (M ⟶ J(M))`, not merely about existence of some functorial injective embeddings. The chapter
owner `HasFunctorialInjectiveEmbeddings` is therefore derived from the explicit natural
transformation `jEmbeddingNatTrans R` via the canonical bridge `NatTrans.arrowFunctor`, rather than
used as a replacement for the source construction. -/

variable (R : Type u) [Ring R]

namespace ModuleCat

open RestrictionCoextensionAdj.HomEquiv

private noncomputable def jEvaluate (M : ModuleCat.{u} R) :
    let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (restrictScalars (algebraMap ℤ R)).obj M ⟶
      ModuleCat.of ℤ (M^∨ → ULift.{u} (AddCircle (1 : ℚ))) :=
  by
    let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    exact
      ModuleCat.ofHom
        { toFun := fun m χ ↦ ULift.up (χ m)
          map_add' := by
            sorry
          map_smul' := by
            sorry }

private noncomputable def jPrecompose {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.of ℤ (M^∨ → ULift.{u} (AddCircle (1 : ℚ))) ⟶
      ModuleCat.of ℤ (N^∨ → ULift.{u} (AddCircle (1 : ℚ))) :=
  ModuleCat.ofHom
    { toFun := fun ψ χ ↦ ψ (((CharacterModule.functor R).map f.op) χ)
      map_add' := by
        intro ψ ψ'
        ext χ
        rfl
      map_smul' := by
        intro n ψ
        ext χ
        rfl }

/-- The textbook assignment `M ↦ J(M)` of Lemma `15.55.8`, made functorial by precomposition on
the character-module variable. -/
noncomputable def jFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  { obj := fun M ↦ jModule R M
    map {M N} f := (coextendScalars (algebraMap ℤ R)).map (jPrecompose R f)
    map_id M := by
      ext ψ
      rfl
    map_comp f g := by
      ext ψ
      rfl }

/-- The explicit embedding `M ⟶ J(M)` obtained from pointwise evaluation by the
restriction/coextension adjunction. -/
noncomputable def jEmbedding (M : ModuleCat.{u} R) : M ⟶ jModule R M :=
  fromRestriction (algebraMap ℤ R) (jEvaluate R M)

@[simp] theorem jEmbedding_apply_apply (M : ModuleCat.{u} R) (m : M) (r : R)
    (χ : M^∨) :
    jEmbedding R M m r χ = ULift.up (χ (r • m)) := by
  rw [jEmbedding, fromRestriction_hom_apply_apply]
  rfl

/-- The explicit embeddings `M ⟶ J(M)` assemble into a natural transformation
`𝟭 (ModuleCat R) ⟶ jFunctor R`. -/
noncomputable def jEmbeddingNatTrans : 𝟭 (ModuleCat.{u} R) ⟶ jFunctor R where
  app M := jEmbedding R M
  naturality {X} {Y} f := by
    sorry

/-- The textbook embedding `M ⟶ J(M)` is injective on underlying elements. -/
theorem jEmbedding_injective (M : ModuleCat.{u} R) :
    Function.Injective (jEmbedding R M) := by
  sorry

/-- Lemma 15.55.9, in the Chapter 12 owner language: the explicit Arrow-valued functor
`M ↦ (M ⟶ J(M))` determines functorial injective embeddings in `ModuleCat R`. -/
noncomputable instance :
    HasFunctorialInjectiveEmbeddings (ModuleCat.{u} R) where
  J := (jEmbeddingNatTrans R).arrowFunctor
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj M := by
    change Mono (jEmbedding R M)
    exact (ModuleCat.mono_iff_injective _).2 (jEmbedding_injective R M)
  injective_obj M := by
    change Injective (jModule R M)
    exact (Module.injective_iff_injective_object R (jModule R M)).1 (jModule_injective R M)

end ModuleCat

end

end CategoryTheory
