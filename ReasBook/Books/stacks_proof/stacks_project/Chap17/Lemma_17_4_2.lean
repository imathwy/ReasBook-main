import Mathlib
import stacks_proof.stacks_project.Chap17.Lemma_17_3_1
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks
import stacks_proof.stacks_project.Chap06.Lemma_6_16_1
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for global generation versus stalkwise generation:
- inspected owner declarations:
  `SheafOfModules.GeneratingSections`,
  `SheafOfModules.GeneratingSections.π`,
  `RingedSpace.moduleStalkHom`,
  `sheaf_epi_iff_stalk_surjective`;
- best owner abstraction:
  the core owner is `ℱ.GeneratingSections`, with `ℱ.freeHomEquiv.symm s` and its stalk maps as the
  primitive bridge from a family of global sections to the sheaf itself;
- primitive data:
  a family `s : I → ℱ.sections`;
- derived API:
  the stalkwise spanning reformulation of the owner condition `Epi (ℱ.freeHomEquiv.symm s)`.

Layer triage:
- `source-facing`: a chosen family of global sections generates `ℱ`;
- `core/canonical`: `ℱ.GeneratingSections`, `ℱ.freeHomEquiv`, and `RingedSpace.moduleStalkHom`;
- `bridge/view`: the stalkwise `Submodule.span = ⊤` criterion below for a raw family, together with
  the owner-level corollary for `ℱ.GeneratingSections`.
-/

variable {X : RingedSpace.{u}}
variable {ℱ : RingedSpace.Modules X}
variable {I : Type u}

/-- Helper for Chap17 Lemma 17 4 2: the opens functor induced by restricting to an open subset is
final, which is the instance required by `SheafOfModules.pullbackObjFreeIso`. -/
private instance opensMapOfRestrictFinal (U : Opens X) :
    Functor.Final (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base) := by
  -- Proof comment: the inclusion of an open subset is an open map, and finality follows from the
  -- standard adjunction between direct and inverse image on opens.
  let hU : IsOpenMap U.inclusion' := U.isOpenEmbedding.isOpenMap
  simpa using
    (CategoryTheory.Functor.final_of_adjunction hU.adjunction :
      Functor.Final (Opens.map U.inclusion'))

/-- Helper for Lemma 17.4.2: stalkwise surjectivity of a morphism of sheaves of abelian groups
detects epimorphisms. -/
lemma addCommGrp_sheaf_epi_iff_stalk_surjective
    {A B : TopCat.Sheaf AddCommGrpCat X} (φ : A ⟶ B) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom).hom) := by
  -- Proof comment: for sheaves of abelian groups, epimorphy is equivalent to local surjectivity,
  -- and local surjectivity is detected on stalks.
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-- Helper for Lemma 17.4.2: if the underlying additive-sheaf map is epic, then the original
module-sheaf morphism is epic. -/
lemma module_epi_of_underlying_epi
    {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ)
    (hφ : Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)) :
    Epi φ := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : Epi (toAbelianSheaf.map φ) := hφ
  refine ⟨?_⟩
  intro Z g h hcomp
  -- Proof comment: cancel the epic image of `φ` after applying the faithful forgetful functor.
  have hmapComp : toAbelianSheaf.map φ ≫ toAbelianSheaf.map g =
      toAbelianSheaf.map φ ≫ toAbelianSheaf.map h := by
    simpa using congrArg (fun f ↦ toAbelianSheaf.map f) hcomp
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_epi (toAbelianSheaf.map φ)).1 hmapComp
  -- Proof comment: equality of the forgotten sheaf morphisms is equality of the original
  -- module-sheaf morphisms, since their objectwise linear maps agree.
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Lemma 17.4.2: exact short complexes of `\mathcal O_X`-modules stay exact after
forgetting to sheaves of abelian groups. -/
private theorem toAbelianSheaf_map_exact
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
  -- Proof comment: exactness of module sheaves is detected on stalks, and forgetting from modules
  -- over `\mathcal O_{X, x}` to abelian groups preserves exactness.
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map toAbelianSheaf)).mpr ?_
  intro x
  have hx : (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  simpa [stalkAddCommGrpFunctor] using hx

/-- Helper for Lemma 17.4.2: an epimorphism of `\mathcal O_X`-modules remains an epimorphism on
the underlying additive sheaf. -/
private theorem underlying_epi_of_module_epi
    {𝒢 ℋ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℋ) [Epi φ] :
    Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
  let toAbelianSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf
      (fun S hS ↦ toAbelianSheaf_map_exact (X := X) S hS)
  -- Proof comment: once exactness survives forgetting, `Functor.map_epi` applies directly.
  exact Functor.map_epi toAbelianSheaf φ

/-- Helper for Lemma 17.4.2: if every stalk map of a morphism of `\mathcal O_X`-modules has range
`⊤`, then the morphism is epic. -/
lemma module_map_epi_of_stalk_range_eq_top
    {𝒢 ℱ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℱ) :
    (∀ x : X, (RingedSpace.moduleStalkHom x φ).hom.range = ⊤) → Epi φ := by
  -- Proof comment: the intended route is to pass from the stalk-range hypothesis to surjectivity
  -- of the underlying set-valued stalk maps of
  -- `(SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ`, use
  -- `sheaf_epi_iff_stalk_surjective`, and then reflect epimorphy back along the faithful functor
  -- `SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)`.
  intro hφ
  have htoSheaf :
      Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
    -- Proof comment: `range = ⊤` on each stalk gives surjectivity of each additive stalk map.
    refine (addCommGrp_sheaf_epi_iff_stalk_surjective (X := X)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).2 ?_
    intro x
    have hsurj :
        Function.Surjective ((RingedSpace.moduleStalkHom x φ).hom) := by
      -- Proof comment: for module maps, surjectivity is equivalent to having full range.
      rw [← LinearMap.range_eq_top]
      exact hφ x
    simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using hsurj
  -- Proof comment: a faithful forgetful functor reflects epimorphisms.
  exact module_epi_of_underlying_epi (X := X) φ htoSheaf

/-- Helper for Lemma 17.4.2: an epimorphism of `\mathcal O_X`-modules has stalk maps with full
range. -/
lemma module_stalk_range_eq_top_of_epi
    {𝒢 ℱ : RingedSpace.Modules X} (φ : 𝒢 ⟶ ℱ) [Epi φ] (x : X) :
    (RingedSpace.moduleStalkHom x φ).hom.range = ⊤ := by
  have hsurj :
      Function.Surjective
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ).hom).hom) :=
    (addCommGrp_sheaf_epi_iff_stalk_surjective (X := X)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).1
      (underlying_epi_of_module_epi (X := X) φ) x
  -- Proof comment: the additive stalk map underlying `moduleStalkHom x φ` is surjective, hence
  -- the linear stalk map has range `⊤`.
  exact (LinearMap.range_eq_top).2 <| by
    simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using hsurj

/-- Helper for Lemma 17.4.2: on stalks, the canonical free-to-sheaf morphism sends the basis germ
at `i` to the germ of the chosen section `s i`. -/
lemma moduleStalkHom_freeHomEquiv_symm_basis_germ
    (s : I → ℱ.sections) (x : X) (i : I) :
    (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom
        (Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection i).1 (op ⊤))) =
      Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤)) := by
  have hxTop : x ∈ (⊤ : Opens X) := by
    trivial
  have hsection :
      ((ℱ.freeHomEquiv.symm s).val.app (op ⊤)) ((SheafOfModules.freeSection i).1 (op ⊤)) =
        (s i).1 (op ⊤) := by
    -- Proof comment: `freeHomEquiv.symm s` was defined to send the `i`th free basis section to `s i`.
    exact congrArg (fun t : ℱ.sections ↦ t.1 (op ⊤))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)
  have hgerm :=
    RingedSpace.moduleStalkMap_germ x (ℱ.freeHomEquiv.symm s) ⊤ hxTop
      ((SheafOfModules.freeSection i).1 (op ⊤))
  -- Proof comment: after evaluating the stalk map on a germ, the result is the germ of the image section.
  rw [hsection] at hgerm
  simpa [TopCat.Presheaf.Γgerm, RingedSpace.moduleStalkHom] using hgerm

/-- Helper for Lemma 17.4.2: every germ of a chosen global section lies in the image of the
corresponding stalk map from the free sheaf, hence their span lies in the stalk range. -/
lemma stalkwise_span_le_freeHomEquiv_symm_range
    (s : I → ℱ.sections) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) ≤
        (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom.range := by
  -- Proof comment: each stalk generator is the image of the matching free basis germ.
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine LinearMap.mem_range.2 ?_
  refine ⟨Γgerm (SheafOfModules.free.{u} I).val.presheaf x
      ((SheafOfModules.freeSection i).1 (op ⊤)), ?_⟩
  simpa using moduleStalkHom_freeHomEquiv_symm_basis_germ (ℱ := ℱ) s x i

/-- Helper for Lemma 17.4.2: mapping the span of the free basis germs through the stalk map of the
canonical free-to-sheaf morphism gives exactly the span of the target germs. -/
lemma freeHomEquiv_symm_stalk_map_span_eq_stalkwise_span
    (s : I → ℱ.sections) (x : X) :
    Submodule.map (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom
      (Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)))) =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) := by
  -- Proof comment: `Submodule.map_span` reduces the computation to the image of each basis germ,
  -- and those images were identified above.
  have himage :
      (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom ''
          (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
            ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤))) =
        Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simpa using (moduleStalkHom_freeHomEquiv_symm_basis_germ (ℱ := ℱ) s x i).symm
    · rintro ⟨i, rfl⟩
      refine ⟨Γgerm (SheafOfModules.free.{u} I).val.presheaf x
          ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)),
        ⟨i, rfl⟩, ?_⟩
      simpa using moduleStalkHom_freeHomEquiv_symm_basis_germ (ℱ := ℱ) s x i
  rw [Submodule.map_span]
  rw [himage]

/-- Helper for Lemma 17.4.2: the tautological sections of a free sheaf recover the identity
morphism. -/
lemma free_tautological_sections_symm :
    ((SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).freeHomEquiv).symm
        (SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X)) =
      𝟙 (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I) := by
  -- Proof comment: compare both morphisms after `freeHomEquiv`; each basis section is fixed.
  apply ((SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).freeHomEquiv).injective
  ext i
  simp

/-- Helper for Chap17 Lemma 17 4 2: the tautological basis sections form a generating family on
the free sheaf itself. -/
private noncomputable def freeTautologicalGeneratingSections :
    (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I : X.Modules).GeneratingSections where
  I := I
  s := SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X)
  epi := by
    -- Proof comment: once the universal morphism is identified with the identity, epimorphicity
    -- is immediate.
    simpa [free_tautological_sections_symm (X := X) (I := I)] using
      (inferInstance :
        Epi (𝟙 (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I : X.Modules)))

/-- Helper for Chap17 Lemma 17 4 2: evaluating the tautological free section on an open gives the
standard basis vector in the objectwise free module. -/
private theorem freeSection_app_eq_single
    (U : Opens X) (i : I) :
    ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op U)) =
      Finsupp.single i (1 : X.presheaf.obj (op U)) := by
  -- Proof comment: unfold the free-section construction until the coproduct inclusion is evaluated
  -- objectwise on `U`; comparing coordinates shows it is the standard basis vector.
  ext j
  simp [SheafOfModules.freeSection, SheafOfModules.freeHomEquiv,
    SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.ιFree, Category.comp_id]

/-- Helper for Chap17 Lemma 17 4 2: every section of the free sheaf on an open is the finite sum
of its coefficients times the evaluated basis sections. -/
private theorem freeSection_eq_sum_basis_onOpen
    (U : Opens X)
    (t : (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.obj (op U)) :
    t = t.sum fun i r ↦
      r • ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op U)) := by
  -- Proof comment: after normalizing the free sheaf on `U` to `Finsupp`, this is the standard
  -- identity expressing a finitely supported function as the sum of its basis vectors.
  change (t : I →₀ X.presheaf.obj (op U)) =
    t.sum fun i r ↦ r • (Finsupp.single i (1 : X.presheaf.obj (op U)))
  simpa [freeSection_app_eq_single] using (t.sum_single).symm

/-- Helper for Chap17 Lemma 17 4 2: the global germ of a section agrees with the germ of its
restriction to any open neighbourhood of the point. -/
private theorem gammaGerm_eq_restriction_germ
    (ℒ : X.Modules) (s : ℒ.sections) {U : Opens X} {x : X} (hx : x ∈ U) :
    TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤)) =
      TopCat.Presheaf.germ ℒ.val.presheaf U x hx (s.1 (op U)) := by
  let i : U ⟶ (⊤ : Opens X) := homOfLE le_top
  -- Proof comment: this is the standard compatibility between the global germ and the germ of a
  -- restriction to a neighbourhood of the point.
  simpa using
    (TopCat.Presheaf.Γgerm_res_apply
      ℒ.val.presheaf (i := i) (x := x) (hx := hx) (s := s.1 (op ⊤))).symm

/-- Helper for Chap17 Lemma 17 4 2: the germ of an evaluated free basis section agrees with the
global germ of the corresponding tautological section. -/
private theorem germ_freeSection_app_eq_Γgerm
    (x : X) {U : Opens X} (hxU : x ∈ U) (i : I) :
    TopCat.Presheaf.germ
        (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf
        U x hxU ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op U)) =
      Γgerm
        (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x
        ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)) := by
  -- Proof comment: the local value of a global free basis section is just its restriction, so the
  -- previous restriction-germ compatibility applies directly.
  simpa using
    (gammaGerm_eq_restriction_germ
      (ℒ := (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I : X.Modules))
      (s := SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i)
      (x := x) hxU).symm

/-- Helper for Chap17 Lemma 17 4 2: every germ in the stalk of a free sheaf lies in the span of
the germs of its tautological basis sections. -/
lemma free_germ_mem_span_freeSection_germs
    (x : X) {U : Opens X} (hxU : x ∈ U)
    (t : (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.obj (op U)) :
    TopCat.Presheaf.germ
        (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf
        U x hxU t ∈
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm
          (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x
          ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤))) := by
  -- Route correction: avoid the old stalk-isomorphism transport. Instead, decompose `t`
  -- objectwise as a finite sum of evaluated basis sections and then take germs termwise.
  have hgerm_eq_sum :
      TopCat.Presheaf.germ
          (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf
          U x hxU t =
        t.sum fun i r ↦
          X.presheaf.germ U x hxU r •
            Γgerm
              (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x
              ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)) := by
    rw [freeSection_eq_sum_basis_onOpen (X := X) (I := I) (U := U) t]
    -- Proof comment: the germ map is additive, and `PresheafOfModules.germ_smul` rewrites each
    -- summand to the stalk coefficient times the global basis germ.
    simp only [Finsupp.sum, map_sum, PresheafOfModules.germ_smul,
      germ_freeSection_app_eq_Γgerm]
  rw [hgerm_eq_sum]
  -- Proof comment: every summand is a scalar multiple of a generator of the span.
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩

/-- Helper for Lemma 17.4.2: the stalk of the free sheaf is spanned by the germs of its
tautological basis sections. -/
lemma free_stalk_span_eq_top (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i ↦ Γgerm
        (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x
        ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤))) = ⊤ := by
  -- Proof comment: every stalk element has a neighborhood representative, and the previous helper
  -- reduces the span statement to that representative-level claim.
  apply top_unique
  intro m hm
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.germ_exist
    (SheafOfModules.free.{u} (R := RingedSpace.ringCatSheaf X) I).val.presheaf x m
  exact free_germ_mem_span_freeSection_germs (X := X) (I := I) x hxU t

/-- Helper for Lemma 17.4.2: the range of the stalk map of the canonical free-to-sheaf morphism
is exactly the span of the germs of the chosen sections. -/
lemma freeHomEquiv_symm_stalk_range_eq_span
    (s : I → ℱ.sections) (x : X) :
    (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom.range =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) := by
  -- Proof comment: rewrite the range as the image of the whole free stalk, replace that whole
  -- stalk by the span of the free basis germs, and then compute the image of that span.
  calc
    (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom.range =
        Submodule.map (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom
          (⊤ : Submodule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat (SheafOfModules.free.{u} I) x)) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z, Submodule.mem_top, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, rfl⟩
    _ = Submodule.map (RingedSpace.moduleStalkHom x (ℱ.freeHomEquiv.symm s)).hom
        (Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm (SheafOfModules.free.{u} I).val.presheaf x
            ((SheafOfModules.freeSection (R := RingedSpace.ringCatSheaf X) i).1 (op ⊤)))) := by
      rw [(free_stalk_span_eq_top (X := X) (I := I) x).symm]
    _ = Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) :=
      freeHomEquiv_symm_stalk_map_span_eq_stalkwise_span (ℱ := ℱ) s x

-- Proof sketch: let `π : free I ⟶ ℱ` be the morphism corresponding to the family `s`. The family
-- generates `ℱ` exactly when `π` is an epimorphism. By the stalkwise criterion for epimorphisms of
-- sheaves, this is equivalent to surjectivity of every stalk map `π_x`. For module homomorphisms,
-- surjectivity of `π_x` is equivalent to the germs of the sections spanning the stalk.
/-- Lemma 17.4.2: a family of global sections of an `\mathcal O_X`-module sheaf on a ringed space
generates the sheaf if and only if, for every point `x`, the germs of those sections span the
stalk `\mathcal F_x` as an `\mathcal O_{X, x}`-module. -/
@[stacks 01AN]
theorem generating_sections_iff_stalkwise_span_eq_top (s : I → ℱ.sections) :
    Epi (ℱ.freeHomEquiv.symm s) ↔
      ∀ x : X,
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) = ⊤ := by
  let π := ℱ.freeHomEquiv.symm s
  have hspan_le :
      ∀ x : X,
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) ≤
            (RingedSpace.moduleStalkHom x π).hom.range :=
    fun x ↦ stalkwise_span_le_freeHomEquiv_symm_range (ℱ := ℱ) s x
  constructor
  · intro hπ x
    letI : Epi π := hπ
    -- Route correction: keep the source-faithful `π := freeHomEquiv.symm s` skeleton and read the
    -- target span off from the stalk range of `π`.
    calc
      Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) =
        (RingedSpace.moduleStalkHom x π).hom.range := by
          symm
          simpa [π] using freeHomEquiv_symm_stalk_range_eq_span (ℱ := ℱ) s x
      _ = ⊤ := module_stalk_range_eq_top_of_epi (X := X) (φ := π) x
  · intro hspan
    refine module_map_epi_of_stalk_range_eq_top (X := X) (φ := π) ?_
    intro x
    -- Proof comment: the span of the germs already sits inside the stalk range, so if that span
    -- is all of the stalk, then the stalk range is all of the stalk as well.
    apply top_unique
    rw [← hspan x]
    exact hspan_le x

namespace SheafOfModules.GeneratingSections

/-- A generating family of global sections spans every stalk. -/
theorem stalkwise_span_eq_top (σ : ℱ.GeneratingSections) :
    ∀ x : X,
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((σ.s i).1 (op ⊤))) = ⊤ :=
  (generating_sections_iff_stalkwise_span_eq_top σ.s).1 σ.epi

end SheafOfModules.GeneratingSections

end AlgebraicGeometry
