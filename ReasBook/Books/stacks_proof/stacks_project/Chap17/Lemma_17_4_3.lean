import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Sites.Monoidal
import stacks_proof.stacks_project.Chap06.Lemma_6_16_1
import stacks_proof.stacks_project.Chap17.Definition_17_23_1
import stacks_proof.stacks_project.Chap17.Lemma_17_4_2
import stacks_proof.stacks_project.Chap17.Lemma_17_3_1
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}
variable [MonoidalCategory X.Modules]

local notation "ModX" => X.Modules
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/- 
Domain-style sampling for tensor products of globally generated `\mathcal O_X`-modules:
- inspected owner declarations:
  `SheafOfModules.GeneratingSections`,
  `SheafOfModules.GeneratingSections.π`,
  `AlgebraicGeometry.generating_sections_iff_stalkwise_span_eq_top`,
  `tensorObj`,
  the local tensor notation `⊗ₘ`;
- best owner abstraction:
  `ℱ.GeneratingSections` is the canonical owner for global generating families, and the tensor
  product owner in the chapter/project ecosystem is the ambient monoidal tensor object
  `(tensorObj ℱ 𝒢 : ModX)`, written `ℱ ⊗ₘ 𝒢`;
- primitive data:
  two generating families `σ : ℱ.GeneratingSections` and `τ : 𝒢.GeneratingSections`;
- derived API:
  the tensor-specific bridge statements below, culminating in the induced owner-level tensor
  construction on generating families for `ℱ ⊗ₘ 𝒢`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.4.3, asserting that the tensor product of two globally generated
  `\mathcal O_X`-modules is again globally generated;
- `core/canonical`: `ℱ.GeneratingSections`, `(tensorObj ℱ 𝒢 : ModX)`, and the stalkwise
  generation owner `AlgebraicGeometry.generating_sections_iff_stalkwise_span_eq_top`;
- `bridge/view`: the tensor-section construction, the stalk tensor-product comparison, and the
  stalkwise pure-tensor spanning statement.
-/

private noncomputable def tensorSection
    (s : ℱ.sections) (t : 𝒢.sections) : (ℱ ⊗ₘ 𝒢 : ModX).sections :=
  let η : SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ X.Modules :=
    SheafOfModules.unitIsoTensorUnit
  (ℱ ⊗ₘ 𝒢 : ModX).unitHomEquiv
    (η.hom ≫ (λ_ (𝟙_ X.Modules)).inv ≫
      ((η.inv ≫ ℱ.unitHomEquiv.symm s) ⊗ₘ (η.inv ≫ 𝒢.unitHomEquiv.symm t)))

/-- Helper for Lemma 17.4.3: pairwise pure tensors of two spanning families span the tensor
product. -/
lemma span_range_tmul_eq_top
    {R : Type*} [CommRing R]
    {ι κ : Type*}
    {M N : Type*}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (a : ι → M) (b : κ → N)
    (ha : Submodule.span R (Set.range a) = ⊤)
    (hb : Submodule.span R (Set.range b) = ⊤) :
    Submodule.span R (Set.range fun ij : ι × κ ↦ a ij.1 ⊗ₜ[R] b ij.2) = ⊤ := by
  let S : Submodule R (TensorProduct R M N) :=
    Submodule.span R (Set.range fun ij : ι × κ ↦ a ij.1 ⊗ₜ[R] b ij.2)
  have hmem :
      ∀ m : M, m ∈ Submodule.span R (Set.range a) →
        ∀ n : N, n ∈ Submodule.span R (Set.range b) →
          TensorProduct.tmul R m n ∈ S := by
    intro m hm n hn
    exact Submodule.span_induction₂
      (p := fun x y _ _ ↦ TensorProduct.tmul R x y ∈ S)
      (fun m n hm_range hn_range ↦ by
        rcases hm_range with ⟨i, rfl⟩
        rcases hn_range with ⟨j, rfl⟩
        exact
          Submodule.subset_span (R := R)
            (s := Set.range fun ij : ι × κ ↦ TensorProduct.tmul R (a ij.1) (b ij.2))
            (by exact ⟨(i, j), rfl⟩))
      (fun n _ ↦ by
        simpa [S, TensorProduct.zero_tmul] using
          (show (0 : TensorProduct R M N) ∈ S from Submodule.zero_mem S))
      (fun m _ ↦ by
        simpa [S, TensorProduct.tmul_zero] using
          (show (0 : TensorProduct R M N) ∈ S from Submodule.zero_mem S))
      (fun x y z _ _ _ hxz hyz ↦ by
        simpa [TensorProduct.add_tmul] using Submodule.add_mem S hxz hyz)
      (fun x y z _ _ _ hxy hxz ↦ by
        simpa [TensorProduct.tmul_add] using Submodule.add_mem S hxy hxz)
      (fun r x y _ _ hxy ↦ by
        simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem S r hxy)
      (fun r x y _ _ hxy ↦ by
        simpa [TensorProduct.tmul_smul] using Submodule.smul_mem S r hxy)
      hm hn
  rw [← top_le_iff]
  intro z hz
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact Submodule.zero_mem S
  · intro m n
    exact hmem m (by simpa [ha]) n (by simpa [hb])
  · intro z₁ z₂ hz₁ hz₂
    exact Submodule.add_mem S hz₁ hz₂

/-- Helper for Chap17 Lemma 17 4 3: stalkwise surjectivity of the underlying additive-sheaf map
detects epimorphisms. -/
private lemma addCommGrpSheafEpiIffStalkSurjectiveLocal
    {A B : TopCat.Sheaf AddCommGrpCat X} (φ : A ⟶ B) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom).hom) := by
  -- Proof comment: for sheaves of abelian groups, epimorphy is equivalent to local
  -- surjectivity, and local surjectivity is detected on stalks.
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-- Helper for Chap17 Lemma 17 4 3: if the underlying additive-sheaf map is epic, then the
original module-sheaf morphism is epic. -/
private lemma moduleEpiOfUnderlyingEpiLocal
    {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ)
    (hφ : Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)) :
    Epi φ := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : Epi (toAbelianSheaf.map φ) := hφ
  refine ⟨?_⟩
  intro Z g h hcomp
  -- Proof comment: cancel the epic image of `φ` after forgetting to additive sheaves.
  have hmapComp : toAbelianSheaf.map φ ≫ toAbelianSheaf.map g =
      toAbelianSheaf.map φ ≫ toAbelianSheaf.map h := by
    simpa using congrArg (fun f ↦ toAbelianSheaf.map f) hcomp
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_epi (toAbelianSheaf.map φ)).1 hmapComp
  -- Proof comment: equality after forgetting scalars is equality of the module morphisms.
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Chap17 Lemma 17 4 3: exact short complexes of `\mathcal O_X`-modules remain exact
after forgetting to sheaves of abelian groups. -/
private theorem toAbelianSheafMapExactLocal
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))).Exact := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let stalkAddCommGrpFunctor : X → X.Modules ⥤ AddCommGrpCat.{u} :=
    fun x ↦
      toAbelianSheaf ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : ∀ x : X, (stalkAddCommGrpFunctor x).PreservesZeroMorphisms := by
    intro x
    let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
      TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    letI : G.PreservesZeroMorphisms := by infer_instance
    simpa [stalkAddCommGrpFunctor, G] using
      (inferInstance : (toAbelianSheaf ⋙ G).PreservesZeroMorphisms)
  -- Proof comment: exactness of module sheaves is detected on stalks, and forgetting from
  -- modules over `\mathcal O_{X, x}` to abelian groups preserves exactness.
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map toAbelianSheaf)).mpr ?_
  intro x
  have hx : (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  simpa [stalkAddCommGrpFunctor] using hx

/-- Helper for Chap17 Lemma 17 4 3: an epimorphism of `\mathcal O_X`-modules remains epic on the
underlying additive sheaf. -/
private theorem underlyingEpiOfModuleEpiLocal
    {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ) [Epi φ] :
    Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf
      (fun S hS ↦ toAbelianSheafMapExactLocal (X := X) S hS)
  -- Proof comment: once exactness survives forgetting, `Functor.map_epi` applies directly.
  exact Functor.map_epi toAbelianSheaf φ

/-- Helper for Chap17 Lemma 17 4 3: a morphism whose stalk maps all have range `⊤` is epic. -/
private lemma moduleMapEpiOfStalkRangeEqTopLocal
    {𝒢 ℱ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℱ) :
    (∀ x : X, (RingedSpace.moduleStalkHom x φ).hom.range = ⊤) → Epi φ := by
  -- Proof comment: `range = ⊤` gives surjectivity on every stalk, which makes the forgotten
  -- additive-sheaf map epic and therefore the original module morphism epic.
  intro hφ
  have htoSheaf :
      Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
    refine (addCommGrpSheafEpiIffStalkSurjectiveLocal (X := X)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).2 ?_
    intro x
    have hsurj :
        Function.Surjective ((RingedSpace.moduleStalkHom x φ).hom) := by
      rw [← LinearMap.range_eq_top]
      exact hφ x
    simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using hsurj
  exact moduleEpiOfUnderlyingEpiLocal (X := X) φ htoSheaf

/-- Helper for Chap17 Lemma 17 4 3: the basis germ in the stalk of a free sheaf maps to the germ
of the corresponding chosen section. -/
private lemma moduleStalkHomFreeHomEquivSymmBasisGermLocal
    {𝒜 : RingedSpace.Modules X} {I : Type u}
    (s : I → 𝒜.sections) (x : X) (i : I) :
    (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom
        (Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection i).1 (op ⊤))) =
      Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤)) := by
  have hxTop : x ∈ (⊤ : Opens X) := by trivial
  have hsection :
      ((𝒜.freeHomEquiv.symm s).val.app (op ⊤)) ((SheafOfModules.freeSection i).1 (op ⊤)) =
        (s i).1 (op ⊤) := by
    -- Proof comment: `freeHomEquiv.symm s` sends the `i`th basis section to `s i`.
    exact congrArg (fun t : 𝒜.sections ↦ t.1 (op ⊤))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)
  have hgerm :=
    RingedSpace.moduleStalkMap_germ x (𝒜.freeHomEquiv.symm s) ⊤ hxTop
      ((SheafOfModules.freeSection i).1 (op ⊤))
  -- Proof comment: evaluate the stalk map on the explicit basis germ.
  rw [hsection] at hgerm
  simpa [TopCat.Presheaf.Γgerm, RingedSpace.moduleStalkHom] using hgerm

/-- Helper for Chap17 Lemma 17 4 3: the span of the chosen global germs sits inside the stalk
range of the associated free-to-sheaf morphism. -/
private lemma stalkwiseSpanLeFreeHomEquivSymmRangeLocal
    {𝒜 : RingedSpace.Modules X} {I : Type u}
    (s : I → 𝒜.sections) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤))) ≤
        (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom.range := by
  -- Proof comment: each generator is the image of the matching basis germ in the free stalk.
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine LinearMap.mem_range.2 ?_
  refine ⟨Γgerm (SheafOfModules.free.{u} I).val.presheaf x
      ((SheafOfModules.freeSection i).1 (op ⊤)), ?_⟩
  simpa using moduleStalkHomFreeHomEquivSymmBasisGermLocal (X := X) s x i

/-- Helper for Chap17 Lemma 17 4 3: a generating family spans each stalk. -/
/-- Helper for Chap17 Lemma 17 4 3: an epimorphism of `\mathcal O_X`-modules has stalk maps with
full range. -/
private lemma moduleStalkRangeEqTopOfEpiLocal
    {𝒢 ℱ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℱ) [Epi φ] (x : X) :
    (RingedSpace.moduleStalkHom x φ).hom.range = ⊤ := by
  have hsurj :
      Function.Surjective
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ).hom).hom) :=
    (addCommGrpSheafEpiIffStalkSurjectiveLocal (X := X)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).1
      (underlyingEpiOfModuleEpiLocal (X := X) φ) x
  -- Proof comment: the additive stalk map underlying `moduleStalkHom x φ` is surjective, hence
  -- the linear stalk map has range `⊤`.
  exact (LinearMap.range_eq_top).2 <| by
    simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using hsurj

/-- Helper for Chap17 Lemma 17 4 3: mapping the span of the free basis germs through the stalk map
of the canonical free-to-sheaf morphism gives the span of the target germs. -/
private lemma freeHomEquivSymmStalkMapSpanEqStalkwiseSpanLocal
    {𝒜 : RingedSpace.Modules X} {I : Type u}
    (s : I → 𝒜.sections) (x : X) :
    Submodule.map (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom
      (Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)))) =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤))) := by
  -- Proof comment: `Submodule.map_span` reduces the computation to the image of each basis germ,
  -- and the earlier stalk formula identifies those images with the chosen target germs.
  have himage :
      (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom ''
          (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
            ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤))) =
        Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simpa using (moduleStalkHomFreeHomEquivSymmBasisGermLocal (X := X) s x i).symm
    · rintro ⟨i, rfl⟩
      refine ⟨Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)),
        ⟨i, rfl⟩, ?_⟩
      simpa using moduleStalkHomFreeHomEquivSymmBasisGermLocal (X := X) s x i
  rw [Submodule.map_span]
  rw [himage]

/-- Helper for Chap17 Lemma 17 4 3: the free sheaf stalk should be spanned by the germs of the
tautological basis sections. -/
private lemma freeStalkSpanEqTopLocal
    (I : Type u) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i ↦ Γgerm
        (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x
        ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤))) = ⊤ := by
  -- Proof comment: this is exactly the free-sheaf stalk spanning theorem already established in
  -- the previous item, so we reuse that owner-level result rather than rebuilding the free-stalk
  -- argument locally.
  simpa using free_stalk_span_eq_top (X := X) (I := I) x

/-- Helper for Chap17 Lemma 17 4 3: the range of the stalk map of the canonical free-to-sheaf
morphism is exactly the span of the germs of the chosen sections. -/
private lemma freeHomEquivSymmStalkRangeEqSpanLocal
    {𝒜 : RingedSpace.Modules X} {I : Type u}
    (s : I → 𝒜.sections) (x : X) :
    (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom.range =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤))) := by
  -- Proof comment: rewrite the range as the image of the whole free stalk, replace that whole
  -- stalk by the span of the free basis germs, and then compute the image of that span.
  calc
    (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom.range =
        Submodule.map (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom
          (⊤ : Submodule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat (SheafOfModules.free.{u} I) x)) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z, Submodule.mem_top, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, rfl⟩
    _ = Submodule.map (RingedSpace.moduleStalkHom x (𝒜.freeHomEquiv.symm s)).hom
        (Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
            ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)))) := by
      rw [(freeStalkSpanEqTopLocal (X := X) I x).symm]
    _ = Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((s i).1 (op ⊤))) :=
      freeHomEquivSymmStalkMapSpanEqStalkwiseSpanLocal (X := X) s x

/-- Helper for Chap17 Lemma 17 4 3: a generating family spans each stalk. -/
private theorem generatingSectionsStalkwiseSpanEqTopLocal
    {𝒜 : RingedSpace.Modules X} (σ : 𝒜.GeneratingSections) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((σ.s i).1 (op ⊤))) = ⊤ := by
  let π := 𝒜.freeHomEquiv.symm σ.s
  letI : Epi π := σ.epi
  -- Route correction: keep the source-faithful `π := freeHomEquiv.symm σ.s` skeleton and read the
  -- target span off from the stalk range of `π`.
  calc
    Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm 𝒜.val.presheaf x ((σ.s i).1 (op ⊤))) =
      (RingedSpace.moduleStalkHom x π).hom.range := by
        symm
        simpa [π] using freeHomEquivSymmStalkRangeEqSpanLocal (X := X) σ.s x
    _ = ⊤ := moduleStalkRangeEqTopOfEpiLocal (X := X) (φ := π) x

/-- Helper for Chap17 Lemma 17 4 3: the ordinary stalk map induced by a morphism of module
presheaves is linear over `\mathcal O_{X, x}`. -/
private theorem presheafStalkMap_map_smul
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q)
    (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    presheafStalkMap (X := X) x φ (r • m) =
      r • presheafStalkMap (X := X) x φ m := by
  obtain ⟨U, hxU, rU, hrU⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.germ_exist P.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
  let mW : P.obj (op W) := P.map iWV.op mV
  have hrW : r = X.presheaf.germ W x hxW rW := by
    -- Proof comment: rewrite the scalar germ on the common refinement `W = U ∩ V`.
    calc
      r = X.presheaf.germ U x hxU rU := hrU.symm
      _ = X.presheaf.germ W x hxW rW := by
        rw [show rW = X.presheaf.map iWU.op rU by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply X.presheaf iWU x hxW rU
  have hmW : m = TopCat.Presheaf.germ P.presheaf W x hxW mW := by
    -- Proof comment: rewrite the module germ on the same common refinement.
    calc
      m = TopCat.Presheaf.germ P.presheaf V x hxV mV := hmV.symm
      _ = TopCat.Presheaf.germ P.presheaf W x hxW mW := by
        rw [show mW = P.map iWV.op mV by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply P.presheaf iWV x hxW mV
  rw [hrW, hmW]
  -- Proof comment: compare both sides on the common representative and use germwise
  -- compatibility of `φ` with scalar multiplication.
  calc
    presheafStalkMap (X := X) x φ
        (X.presheaf.germ W x hxW rW • TopCat.Presheaf.germ P.presheaf W x hxW mW) =
      presheafStalkMap (X := X) x φ
        (TopCat.Presheaf.germ P.presheaf W x hxW (rW • mW)) := by
          exact congrArg (presheafStalkMap (X := X) x φ)
            (PresheafOfModules.germ_smul P x W hxW rW mW).symm
    _ =
      TopCat.Presheaf.germ Q.presheaf W x hxW ((φ.app (op W)) (rW • mW)) := by
        simpa [presheafStalkMap] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ) (rW • mW))
    _ =
      TopCat.Presheaf.germ Q.presheaf W x hxW (rW • (φ.app (op W)) mW) := by
        simpa using (φ.app (op W)).hom.map_smul rW mW
    _ =
      X.presheaf.germ W x hxW rW •
        TopCat.Presheaf.germ Q.presheaf W x hxW ((φ.app (op W)) mW) := by
          exact PresheafOfModules.germ_smul Q x W hxW rW ((φ.app (op W)) mW)
    _ =
      X.presheaf.germ W x hxW rW •
        presheafStalkMap (X := X) x φ
          (TopCat.Presheaf.germ P.presheaf W x hxW mW) := by
            simpa [presheafStalkMap] using
              (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
                ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ) mW).symm

/-- Helper for Chap17 Lemma 17 4 3: a morphism of module presheaves induces a morphism of the
corresponding stalk modules over `\mathcal O_{X, x}`. -/
private noncomputable def presheafStalkHom
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk Q.presheaf x) :=
  ModuleCat.ofHom
    { toFun := presheafStalkMap (X := X) x φ
      map_add' := by
        intro m n
        exact (presheafStalkMap (X := X) x φ).hom.map_add m n
      map_smul' := by
        intro r m
        simpa using presheafStalkMap_map_smul (X := X) x φ r m }

/-- Helper for Chap17 Lemma 17 4 3: the stalk of a sheafified module presheaf identifies with the
stalk of the underlying module presheaf. -/
private noncomputable def presheafSheafificationStalkIsoLocal
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    RingedSpace.stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x ≅
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  let f :
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶
        RingedSpace.stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x :=
    presheafStalkHom (X := X) x η
  have hf_bijective : Function.Bijective f.hom := by
    -- Proof comment: this linear map is exactly the sheafification-unit stalk map with the
    -- ambient `\mathcal O_{X, x}`-module structures packaged around the same underlying function.
    simpa [f, presheafStalkHom] using
      sheafificationUnitStalkMap_bijective (X := X) P x
  -- Proof comment: turn the bijective linear map into a linear equivalence and package it as the
  -- requested categorical isomorphism in the reverse direction.
  exact (LinearEquiv.ofBijective f.hom hf_bijective).toModuleIso.symm

/-- Helper for Chap17 Lemma 17 4 3: the stalk of the presheaf tensor model should identify with
the tensor product of the two stalk modules. -/
private noncomputable def presheafTensorStalkIsoLocal
    (ℱ 𝒢 : ModX) (x : X) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).presheaf x) ≅
      RingedSpace.stalkModuleCat ℱ x ⊗ RingedSpace.stalkModuleCat 𝒢 x := by
  -- TODO: compare the colimit module of the presheaf tensor model on `OpenNhds x` with the tensor
  -- product of the two colimit modules, ideally through `PresheafOfModules.colimitFunctor` on the
  -- neighborhood category and the filtered-colimit tensor comparison.
  sorry

/-- Helper for Lemma 17.4.3: the stalk of the tensor product module sheaf is canonically
isomorphic to the tensor product of the two stalk modules. -/
noncomputable def tensor_product_stalk_iso_local
    (ℱ 𝒢 : ModX) (x : X) :
    RingedSpace.stalkModuleCat (ℱ ⊗ₘ 𝒢 : ModX) x ≅
      RingedSpace.stalkModuleCat ℱ x ⊗ RingedSpace.stalkModuleCat 𝒢 x :=
  -- Proof comment: normalize the sheaf tensor product to its sheafified presheaf model, then
  -- transport across the dedicated presheaf tensor-stalk comparison.
  presheafSheafificationStalkIsoLocal
      (P := PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val) x ≪≫
    presheafTensorStalkIsoLocal (X := X) ℱ 𝒢 x

/-- Helper for Lemma 17.4.3: under the local tensor-stalk comparison, the germ of a tensor section
becomes the pure tensor of the two corresponding germs. -/
lemma tensor_section_germ_eq_tmul
    (x : X) (s : ℱ.sections) (t : 𝒢.sections) :
    (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x).hom
        (Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x ((tensorSection s t).1 (op ⊤))) =
      Γgerm ℱ.val.presheaf x (s.1 (op ⊤)) ⊗ₜ[X.presheaf.stalk x]
        Γgerm 𝒢.val.presheaf x (t.1 (op ⊤)) := by
  -- TODO: after `tensor_product_stalk_iso_local` is reduced to the presheaf tensor/stalk
  -- comparison, this should be the computation of that comparison on the explicit tensor section.
  sorry

/-- Helper for Lemma 17.4.3: mapping the span of tensor-section germs across the canonical
stalk/tensor comparison gives the span of the corresponding pure tensors. -/
lemma map_span_tensor_generators
    (σ : ℱ.GeneratingSections) (τ : 𝒢.GeneratingSections) (x : X) :
    Submodule.map (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x).hom.hom
      (Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x
            ((tensorSection (σ.s ij.1) (τ.s ij.2)).1 (op ⊤)))) =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm ℱ.val.presheaf x ((σ.s ij.1).1 (op ⊤)) ⊗ₜ[X.presheaf.stalk x]
            Γgerm 𝒢.val.presheaf x ((τ.s ij.2).1 (op ⊤))) := by
  -- Proof comment: `Submodule.map_span` reduces the transport to the image of each range
  -- generator, and `tensor_section_germ_eq_tmul` identifies each image with the intended pure
  -- tensor generator.
  rw [Submodule.map_span]
  apply congrArg (Submodule.span (X.presheaf.stalk x))
  ext y
  constructor
  · rintro ⟨z, ⟨ij, rfl⟩, rfl⟩
    refine ⟨ij, ?_⟩
    rcases ij with ⟨i, j⟩
    exact (tensor_section_germ_eq_tmul (ℱ := ℱ) (𝒢 := 𝒢) x (σ.s i) (τ.s j)).symm
  · rintro ⟨ij, rfl⟩
    refine ⟨_, ⟨ij, rfl⟩, ?_⟩
    rcases ij with ⟨i, j⟩
    exact tensor_section_germ_eq_tmul (ℱ := ℱ) (𝒢 := 𝒢) x (σ.s i) (τ.s j)

/-- Helper for Lemma 17.4.3: the tensor family built from two generating families spans every
stalk of the tensor product. -/
lemma tensor_generating_family_stalkwise_span_eq_top
    (σ : ℱ.GeneratingSections) (τ : 𝒢.GeneratingSections) :
    ∀ x : X,
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x
            ((tensorSection (σ.s ij.1) (τ.s ij.2)).1 (op ⊤))) = ⊤ := by
  intro x
  let e := tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x
  let S :
      Submodule (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat (ℱ ⊗ₘ 𝒢 : ModX) x) :=
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun ij : σ.I × τ.I ↦
        Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x
          ((tensorSection (σ.s ij.1) (τ.s ij.2)).1 (op ⊤)))
  have hmap :
      Submodule.map e.hom.hom S =
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun ij : σ.I × τ.I ↦
            Γgerm ℱ.val.presheaf x ((σ.s ij.1).1 (op ⊤)) ⊗ₜ[X.presheaf.stalk x]
              Γgerm 𝒢.val.presheaf x ((τ.s ij.2).1 (op ⊤))) := by
    simpa [e, S] using map_span_tensor_generators (ℱ := ℱ) (𝒢 := 𝒢) σ τ x
  have hpure :
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm ℱ.val.presheaf x ((σ.s ij.1).1 (op ⊤)) ⊗ₜ[X.presheaf.stalk x]
            Γgerm 𝒢.val.presheaf x ((τ.s ij.2).1 (op ⊤))) = ⊤ := by
    -- Proof comment: once tensor-section germs are transported to pure tensors, the two
    -- previously known stalkwise spanning families generate the whole tensor-product stalk.
    exact span_range_tmul_eq_top
      (fun i : σ.I ↦ Γgerm ℱ.val.presheaf x ((σ.s i).1 (op ⊤)))
      (fun j : τ.I ↦ Γgerm 𝒢.val.presheaf x ((τ.s j).1 (op ⊤)))
      (generatingSectionsStalkwiseSpanEqTopLocal (X := X) σ x)
      (generatingSectionsStalkwiseSpanEqTopLocal (X := X) τ x)
  have he_inj : Function.Injective e.hom.hom := by
    -- Proof comment: the hom of an isomorphism is monic, and `ModuleCat.mono_iff_injective`
    -- turns that categorical mono statement into injectivity of the underlying linear map.
    exact (ModuleCat.mono_iff_injective e.hom).1 inferInstance
  apply top_unique
  intro z hz
  have hzMap : e.hom.hom z ∈ Submodule.map e.hom.hom S := by
    -- Proof comment: the mapped span is all of the tensor-product stalk, so the image of any
    -- element lies in that mapped span.
    rw [hmap, hpure]
    trivial
  rcases hzMap with ⟨y, hy, hEq⟩
  exact he_inj hEq ▸ hy

namespace SheafOfModules.GeneratingSections

/-- Tensor two chosen generating families to obtain a generating family of the ambient tensor
product `ℱ ⊗ₘ 𝒢`. -/
noncomputable def tensor (σ : ℱ.GeneratingSections) (τ : 𝒢.GeneratingSections) :
    (ℱ ⊗ₘ 𝒢 : ModX).GeneratingSections where
  I := σ.I × τ.I
  s ij := tensorSection (σ.s ij.1) (τ.s ij.2)
  epi := by
    -- Route correction: avoid the broken earlier file by proving epimorphy directly from the
    -- stalk-range criterion applied to the tensor family.
    let s : σ.I × τ.I → (ℱ ⊗ₘ 𝒢 : ModX).sections :=
      fun ij ↦ tensorSection (σ.s ij.1) (τ.s ij.2)
    let π : SheafOfModules.free (R := X.ringCatSheaf) (σ.I × τ.I) ⟶ (ℱ ⊗ₘ 𝒢 : ModX) :=
      ((ℱ ⊗ₘ 𝒢 : ModX).freeHomEquiv).symm s
    change Epi π
    refine moduleMapEpiOfStalkRangeEqTopLocal (X := X) (φ := π) ?_
    intro x
    have hspan :
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun ij : σ.I × τ.I ↦
            Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x ((s ij).1 (op ⊤))) = ⊤ := by
      simpa [s] using
        tensor_generating_family_stalkwise_span_eq_top (ℱ := ℱ) (𝒢 := 𝒢) σ τ x
    have hle :
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun ij : σ.I × τ.I ↦
            Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x ((s ij).1 (op ⊤))) ≤
          (RingedSpace.moduleStalkHom x π).hom.range := by
      simpa [π, s] using
        stalkwiseSpanLeFreeHomEquivSymmRangeLocal (X := X) (𝒜 := (ℱ ⊗ₘ 𝒢 : ModX)) s x
    apply top_unique
    rw [← hspan]
    exact hle

end SheafOfModules.GeneratingSections

/-- Lemma 17.4.3: if two `\mathcal O_X`-modules are generated by global sections, then their
tensor product `ℱ ⊗ₘ 𝒢` is also generated by global sections. -/
@[stacks 01AO]
theorem nonempty_generatingSections_tensor
    (hℱ : Nonempty ℱ.GeneratingSections) (h𝒢 : Nonempty 𝒢.GeneratingSections) :
    Nonempty ((ℱ ⊗ₘ 𝒢 : ModX).GeneratingSections) := by
  rcases hℱ with ⟨σ⟩
  rcases h𝒢 with ⟨τ⟩
  exact ⟨SheafOfModules.GeneratingSections.tensor σ τ⟩

end AlgebraicGeometry.RingedSpace
