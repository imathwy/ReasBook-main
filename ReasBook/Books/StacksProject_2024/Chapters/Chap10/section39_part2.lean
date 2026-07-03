import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_39_6 (from Chap10) -/
open CategoryTheory Limits MonoidalCategory
open PresheafOfModules
open CategoryTheory.IsFiltered renaming max → max'
open scoped ChangeOfRings

universe u

noncomputable section

section

variable {C : Type u} [SmallCategory C] [IsCofiltered C]

local instance : InitiallySmall.{u} C := initiallySmall_of_essentiallySmall C

section FilteredColimitFlatness

variable {R : Type u} [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- Helper for Lemma 10.39.6: tensoring a diagram morphism on the right commutes with tensoring
the codomain modules by a fixed linear map. -/
private theorem lTensor_naturality
    {M M' N N' : ModuleCat.{u} R}
    (α : M ⟶ M') (f : N ⟶ N') :
    (α ▷ N) ≫ ModuleCat.ofHom (f.hom.lTensor M') =
      ModuleCat.ofHom (f.hom.lTensor M) ≫ (α ▷ N') := by
  -- Both sides are the canonical tensor-product map `TensorProduct.map α f`.
  apply ModuleCat.hom_ext
  change (f.hom.lTensor M').comp ((α ▷ N).hom) = ((α ▷ N').hom).comp (f.hom.lTensor M)
  rw [ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerRight]
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

/-- Helper for Lemma 10.39.6: tensoring the objects of a filtered diagram on the right by a fixed
linear map yields a natural transformation between the tensorized diagrams. -/
private def lTensor_natTrans
    (F : J ⥤ ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    F ⋙ tensorRight N ⟶ F ⋙ tensorRight N' where
  app j := ModuleCat.ofHom (f.hom.lTensor (F.obj j))
  naturality _ _ g := lTensor_naturality (F.map g) f

section

omit [IsFiltered J]

/-- Helper for Lemma 10.39.6: the tensorized cocone maps commute with tensoring by the chosen
linear map. -/
private theorem lTensor_natTrans_colimit_compat
    (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)
    {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') :
    ∀ j,
      ((tensorRight (ModuleCat.of R N)).mapCocone c).ι.app j ≫ ModuleCat.ofHom (f.lTensor c.pt) =
        (lTensor_natTrans (R := R) F (ModuleCat.ofHom f)).app j ≫
          ((tensorRight (ModuleCat.of R N')).mapCocone c).ι.app j := by
  intro j
  -- This is exactly the naturality square for right tensoring by `f`.
  simpa [lTensor_natTrans] using
    lTensor_naturality (c.ι.app j) (ModuleCat.ofHom f)

end

/-- Helper for Lemma 10.39.6: a filtered colimit cocone of flat `R`-modules has flat cocone point.
This is the only ingredient from Lemma 10.39.3 needed in this file, reproduced locally because
the generated dependency file currently fails before producing an `.olean`. -/
private theorem flat_of_isColimit_filtered_system_local
    (F : J ⥤ ModuleCat.{u} R) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R c.pt := by
  -- Use the injectivity criterion for flatness, so it suffices to preserve injective maps after
  -- tensoring with the cocone point.
  refine (Module.Flat.iff_lTensor_preserves_injective_linearMap' (R := R) (M := c.pt)).2 ?_
  intro N N' _ _ _ _ f hf
  let φ :
      F ⋙ tensorRight (ModuleCat.of R N) ⟶
        F ⋙ tensorRight (ModuleCat.of R N') :=
    lTensor_natTrans F (ModuleCat.ofHom f)
  let cN : Cocone (F ⋙ tensorRight (ModuleCat.of R N)) := (tensorRight (ModuleCat.of R N)).mapCocone c
  let cN' : Cocone (F ⋙ tensorRight (ModuleCat.of R N')) :=
    (tensorRight (ModuleCat.of R N')).mapCocone c
  have hcN : IsColimit cN := by
    -- Tensoring by a fixed module preserves the filtered colimit cocone.
    simpa [cN] using
      (Limits.isColimitOfPreserves (tensorRight (ModuleCat.of R N)) hc)
  have hcN' : IsColimit cN' := by
    -- The same colimit preservation holds for the codomain tensor factor.
    simpa [cN'] using
      (Limits.isColimitOfPreserves (tensorRight (ModuleCat.of R N')) hc)
  have hφ_app : ∀ j, Mono (φ.app j) := by
    intro j
    rw [ModuleCat.mono_iff_injective]
    -- At each stage this is exactly the tensor of `f`, so stagewise flatness gives injectivity.
    simpa [φ] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := F.obj j) f hf
  have hcompat :
      ∀ j, cN.ι.app j ≫ ModuleCat.ofHom (f.lTensor c.pt) = φ.app j ≫ cN'.ι.app j := by
    intro j
    -- The tensorized cocone maps satisfy the same naturality square stagewise.
    simpa [cN, cN', φ] using lTensor_natTrans_colimit_compat (R := R) F c f j
  have hmono_tensor : Mono (ModuleCat.ofHom (f.lTensor c.pt)) := by
    -- Filtered colimits in `ModuleCat` preserve monomorphisms, so the induced map on cocone
    -- points remains mono.
    letI : ∀ j, Mono (φ.app j) := hφ_app
    letI : Mono φ := NatTrans.mono_of_mono_app φ
    exact Limits.colim.map_mono' φ hcN hcN' (ModuleCat.ofHom (f.lTensor c.pt)) hcompat
  -- Convert the categorical mono statement back to injectivity of the underlying linear map.
  exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom (f.lTensor c.pt))).1 hmono_tensor

end FilteredColimitFlatness

/- Domain-style sampling for Lemma 10.39.6:
- primary domain: flatness for cofiltered colimits of module diagrams over a cofiltered diagram of
  commutative rings;
- sampled owner declarations:
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `PresheafOfModules.colimitFunctor`,
  `preservesColimitIso (forget₂ CommRingCat RingCat)`;
- best owner abstraction: the source-faithful finite-ideal criterion for flatness on the colimit
  ring together with the canonical colimit module `PresheafOfModules.colimitFunctor`;
- primitive data: the ring diagram `R`, either a single module over `colimit R` or a presheaf of
  modules `M` over the underlying ring diagram, and the stagewise flatness hypotheses;
- derived API: clause `(1)` is the constant-system specialization of clause `(2)`, while clause
  `(2)` follows by descending finitely generated ideals to one stage and using injectivity on the
  stage tensor maps;
- source/core/bridge triage:
  `source-facing`: the two flatness statements of Lemma 10.39.6 over `colimit R`;
  `core/canonical`: `Module.Flat.iff_lift_lsmul_comp_subtype_injective` and
    `PresheafOfModules.colimitFunctor`;
  `bridge/view`: the restriction-of-scalars passage from the ring-valued colimit
    `colimit (R ⋙ forget₂ CommRingCat RingCat)` to the source-facing ring `colimit R`. -/

/-- Helper for Lemma 10.39.6: forgetting commutativity and then transporting back along
`preservesColimitIso` recovers the original stage map into `colimit R`. -/
private theorem colimit_forget_comp_ι
    (R : Cᵒᵖ ⥤ CommRingCat) (U : Cᵒᵖ) :
    (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom.comp
        ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom =
      ((colimit.cocone R).ι.app U).hom := by
  -- This is exactly the inverse cocone-leg identity for `preservesColimitIso`.
  simpa using congrArg RingCat.Hom.hom
    (ι_preservesColimitIso_inv (G := forget₂ CommRingCat RingCat) (F := R) U)

/-- Helper for Lemma 10.39.6: restricting an `R`-module directly to a stage agrees with first
transporting it to the forgotten ring colimit and then restricting along the forgotten stage map. -/
private noncomputable abbrev restrictScalars_const_stage_iso
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : ModuleCat.{u} (colimit R : CommRingCat))
    (U : Cᵒᵖ) :
    ((ModuleCat.restrictScalars ((colimit.cocone R).ι.app U).hom).obj M) ≅
      ((ModuleCat.restrictScalars
          ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom).obj
        ((ModuleCat.restrictScalars
            (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom).obj M)) :=
  ModuleCat.restrictScalarsComp'App
    ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom
    (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom
    ((colimit.cocone R).ι.app U).hom
    (colimit_forget_comp_ι (R := R) U).symm
    M

/-- Helper for Lemma 10.39.6: any finite family of elements in the colimit ring already lifts to
one common stage. -/
private theorem filtered_colimit_exists_stage_family
    (R : Cᵒᵖ ⥤ CommRingCat) :
    ∀ n : ℕ, ∀ a : Fin n → (colimit R : CommRingCat),
      ∃ U, ∃ b : Fin n → R.obj U, ∀ m,
        (colimit.cocone R).ι.app U (b m) = a m
  | 0, a => by
      let U : Cᵒᵖ := IsFiltered.nonempty.some
      refine ⟨U, fun m => Fin.elim0 m, ?_⟩
      intro m
      exact Fin.elim0 m
  | n + 1, a => by
      let c := colimit.cocone R
      let t : Cocone (R ⋙ forget CommRingCat) := (forget CommRingCat).mapCocone c
      have ht : IsColimit t := Limits.isColimitOfPreserves (forget CommRingCat) (colimit.isColimit R)
      -- Descend the tail first, then enlarge to one stage that also contains the head element.
      obtain ⟨U, b, hb⟩ :=
        filtered_colimit_exists_stage_family R n (fun m : Fin n ↦ a m.succ)
      obtain ⟨V, x, hx⟩ := Types.jointly_surjective_of_isColimit ht (a 0)
      refine ⟨max' V U,
        Fin.cons (R.map (IsFiltered.leftToMax V U) x)
          (fun m ↦ R.map (IsFiltered.rightToMax V U) (b m)),
        ?_⟩
      intro m
      refine Fin.cases ?_ ?_ m
      · -- The head element is pushed from its original stage to the common upper stage.
        have hhead :
            c.ι.app (max' V U) (R.map (IsFiltered.leftToMax V U) x) = c.ι.app V x :=
          ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax V U)) x
        exact hhead.trans (by simpa [t] using hx)
      · intro m
        -- The tail elements are pushed from the previously chosen common stage.
        have htail :
            c.ι.app (max' V U) (R.map (IsFiltered.rightToMax V U) (b m)) = c.ι.app U (b m) :=
          ConcreteCategory.congr_hom (c.w (IsFiltered.rightToMax V U)) (b m)
        exact htail.trans (hb m)

/-- Helper for Lemma 10.39.6: a finitely generated ideal of the colimit ring is the extension of
one finitely generated ideal from a single stage. -/
private theorem exists_fg_stage_ideal_of_colimit_ideal
    (R : Cᵒᵖ ⥤ CommRingCat)
    (a : Ideal (colimit R : CommRingCat))
    (ha : a.FG) :
    ∃ U, ∃ J : Ideal (R.obj U), J.FG ∧
      Ideal.map ((colimit.cocone R).ι.app U).hom J = a := by
  -- Choose finitely many generators of `a`, lift them to one stage, and rebuild the stage ideal.
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp ha
  obtain ⟨U, t, ht⟩ := filtered_colimit_exists_stage_family R n s
  let J : Ideal (R.obj U) := Ideal.span (Set.range t)
  refine ⟨U, J, ?_, ?_⟩
  · -- The rebuilt stage ideal is finitely generated by construction.
    simpa [J] using (Submodule.fg_span (Set.finite_range t))
  · -- Mapping the rebuilt generators into the colimit recovers the original ideal.
    change Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range t)) = a
    have hs' : Ideal.span (Set.range s) = a := by
      simpa using hs
    rw [Ideal.map_span]
    have hset :
        ((colimit.cocone R).ι.app U).hom '' Set.range t = Set.range s := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨m, rfl⟩
        exact ⟨m, (ht m).symm⟩
      · rintro ⟨m, rfl⟩
        exact ⟨t m, ⟨m, rfl⟩, ht m⟩
    rw [hset]
    exact hs'

/-- Helper for Lemma 10.39.6: once a finitely generated ideal is pushed to a later stage, the
canonical tensor map into that stage module is injective by the flatness criterion. -/
private theorem stage_extension_tensor_map_injective
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [∀ U, Module.Flat (R.obj U) (M.obj U)]
    {U V : Cᵒᵖ} (f : U ⟶ V) (J : Ideal (R.obj U)) (hJ : J.FG) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)) := by
  -- Apply the finitely generated ideal criterion at the later stage.
  exact
    (Module.Flat.iff_lift_lsmul_comp_subtype_injective
      (R := R.obj V) (M := M.obj V)).1 inferInstance (Ideal.FG.map hJ (R.map f).hom)

/-- Helper for Lemma 10.39.6: the stage flatness-test map sends a pure tensor to the expected
scalar multiple in the stage module. -/
private theorem stage_extension_tensor_map_tmul
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (f : U ⟶ V) (J : Ideal (R.obj U))
    (x : Ideal.map (R.map f).hom J) (m : M.obj V) :
    TensorProduct.lift
        ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
        (x ⊗ₜ[R.obj V] m) =
      (x : R.obj V) • m := by
  -- This is the defining formula for `TensorProduct.lift` on pure tensors.
  simp

/-- Helper for Lemma 10.39.6: the stage flatness-test map is a monomorphism in `ModuleCat`. -/
private theorem stage_extension_tensor_map_mono
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [∀ U, Module.Flat (R.obj U) (M.obj U)]
    {U V : Cᵒᵖ} (f : U ⟶ V) (J : Ideal (R.obj U)) (hJ : J.FG) :
    Mono <| ModuleCat.ofHom <|
      TensorProduct.lift
        ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype) := by
  -- Package the stagewise injectivity criterion in the categorical form needed by colimit exactness.
  rw [ModuleCat.mono_iff_injective]
  simpa using stage_extension_tensor_map_injective (R := R) (M := M) f J hJ

/-- Helper for Lemma 10.39.6: the colimit cocone relation on the ring diagram becomes an equality
of ring-hom compositions. -/
private theorem colimit_cocone_comp
    (R : Cᵒᵖ ⥤ CommRingCat)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((colimit.cocone R).ι.app V).hom.comp (R.map f).hom =
      ((colimit.cocone R).ι.app U).hom := by
  -- This is exactly the cocone identity `ι_V ≫ R.map f = ι_U`, rewritten on elements.
  ext r
  exact ConcreteCategory.congr_hom ((colimit.cocone R).w f) r

/-- Helper for Lemma 10.39.6: the colimit of the constant presheaf of modules is the original
module over the forgotten colimit ring. -/
private noncomputable def colimitFunctor_constFunctor_iso
    (R : Cᵒᵖ ⥤ CommRingCat)
    (N : ModuleCat.{u} (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt) :
    ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj
      ((PresheafOfModules.constFunctor.{u}
          (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat))).obj N)) ≅
      N := by
  let F :=
    ((PresheafOfModules.constFunctor.{u}
        (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat))).obj N)
  let ε :
      ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj F) ⟶ N :=
    ((PresheafOfModules.ModuleColimit.homEquiv
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit F.presheaf)).symm (𝟙 F))
  -- The identity natural transformation sends each stage generator to itself, so `ε` is
  -- surjective.
  have hε_surj : Function.Surjective ε.hom := by
    intro n
    let U : Cᵒᵖ := IsFiltered.nonempty.some
    refine ⟨PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit F.presheaf) (U := U) n, ?_⟩
    simpa [ε, F] using
      (PresheafOfModules.ModuleColimit.homEquiv_symm_apply
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit F.presheaf)
        (β := 𝟙 F) (X := U) (x := n))
  -- Joint surjectivity on a common stage lets us read equality in the colimit back at that stage.
  have hε_inj : Function.Injective ε.hom := by
    intro x y hxy
    obtain ⟨U, xU, yU, rfl, rfl⟩ :=
      PresheafOfModules.ModuleColimit.ιM_jointly_surjective₂
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit F.presheaf)
        (hcM' := colimit.isColimit F.presheaf)
        x y
    have hx :
        ε (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit F.presheaf) xU) = xU := by
      simpa [ε, F] using
        (PresheafOfModules.ModuleColimit.homEquiv_symm_apply
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit F.presheaf)
          (β := 𝟙 F) (X := U) (x := xU))
    have hy :
        ε (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit F.presheaf) yU) = yU := by
      simpa [ε, F] using
        (PresheafOfModules.ModuleColimit.homEquiv_symm_apply
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit F.presheaf)
          (β := 𝟙 F) (X := U) (x := yU))
    have hstage : xU = yU := by
      have hxy' :
          ε (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit F.presheaf) xU) =
            ε (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit F.presheaf) yU) := hxy
      exact hx.symm.trans (hxy'.trans hy)
    simpa [hstage]
  -- The descended map is bijective, so it upgrades to the desired module isomorphism.
  exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective ε.hom ⟨hε_inj, hε_surj⟩)

/-- Helper for Lemma 10.39.6: shrinking the forgotten-colimit module changes only the universe,
not the underlying module up to canonical isomorphism. -/
private noncomputable abbrev shrink_forget_colimit_module
    {A : RingCat}
    (N : ModuleCat.{u} A) :
    ModuleCat.{u} A :=
  let _ : Module A (Shrink.{u} N) := inferInstance
  ModuleCat.of A (Shrink.{u} N)

/-- Helper for Lemma 10.39.6: shrinking the forgotten-colimit module changes only the universe,
not the underlying module up to canonical isomorphism. -/
private noncomputable abbrev shrink_forget_colimit_module_iso
    {A : RingCat}
    (N : ModuleCat.{u} A) :
    shrink_forget_colimit_module N ≅ N :=
  LinearEquiv.toModuleIso (Shrink.linearEquiv A N)

/-- Helper for Lemma 10.39.6: after shrinking the forgotten-colimit module, restricting scalars
to any stage still agrees with the original stage restriction of `M`. -/
private noncomputable abbrev restrictScalars_shrink_stage_iso
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : ModuleCat.{u} (colimit R : CommRingCat))
    (U : Cᵒᵖ) :
    ((ModuleCat.restrictScalars
        ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom).obj
      (shrink_forget_colimit_module
        (((ModuleCat.restrictScalars
            (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom).obj M)))) ≅
      ((ModuleCat.restrictScalars ((colimit.cocone R).ι.app U).hom).obj M) := by
  let N :
      ModuleCat.{u} (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt :=
    ((ModuleCat.restrictScalars
        (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom).obj M)
  exact
    ((ModuleCat.restrictScalars
      ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom).mapIso
      (shrink_forget_colimit_module_iso N)) ≪≫
      (restrictScalars_const_stage_iso R M U).symm

/-- Helper for Lemma 10.39.6: the preserved-colimit comparison and its inverse compose to the
identity ring map on `colimit R`. -/
private theorem preservesColimitIso_inv_comp_hom_id
    (R : Cᵒᵖ ⥤ CommRingCat) :
    RingHom.id (colimit R : CommRingCat) =
      (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom.comp
        (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom := by
  -- This is the ring-hom version of the categorical identity `hom ≫ inv = 𝟙`.
  ext x
  simp

/-- Helper for Lemma 10.39.6: the forward preserved-colimit comparison identifies the stage map
into `colimit R` with the forgotten stage map into the ring-valued colimit. -/
private theorem colimit_hom_comp_ι
    (R : Cᵒᵖ ⥤ CommRingCat) (U : Cᵒᵖ) :
    (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom.comp
        ((colimit.cocone R).ι.app U).hom =
      ((colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).ι.app U).hom := by
  -- This is the forward cocone-leg identity for `preservesColimitIso`.
  ext r
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom (G := forget₂ CommRingCat RingCat) (F := R) U) r

/-- Helper for Lemma 10.39.6: the colimit module of `M` viewed over `colimit R`. This is the
module appearing in the statement of clause `(2)`. -/
private noncomputable abbrev colimit_target_module
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ModuleCat.{u} (colimit R : CommRingCat) :=
  ((ModuleCat.restrictScalars
      (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
    ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M))

/-- Helper for Lemma 10.39.6: after descending `a` to `J` at stage `U`, the extension of `J` to
any later stage `V` still maps onto `a` in the colimit ring. -/
private theorem source_stage_ideal_image_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V) :
    Ideal.map ((colimit.cocone R).ι.app V).hom (Ideal.map (R.map f).hom J) = a := by
  -- Rewrite the two successive ideal extensions as one map along the composed ring hom.
  rw [Ideal.map_map]
  exact (congrArg (fun φ => Ideal.map φ J) (colimit_cocone_comp (R := R) (f := f))).trans hJmap

/-- Helper for Lemma 10.39.6: every element of the descended stage ideal maps into the target
ideal `a` in the colimit ring. -/
private theorem source_stage_ideal_mem
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J) :
    ((colimit.cocone R).ι.app V).hom x ∈ a := by
  -- Membership is immediate from the mapped-ideal description of `a` at stage `V`.
  rw [← source_stage_ideal_image_eq (R := R) (a := a) (J := J) hJmap f]
  exact Ideal.mem_map_of_mem _ x.2

/-- Helper for Lemma 10.39.6: the canonical later-stage ideal element viewed inside
`a ⊆ colimit R`. -/
private noncomputable def source_stage_ideal_to_colimit
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V) :
    Ideal.map (R.map f).hom J → a :=
  fun x ↦ ⟨((colimit.cocone R).ι.app V).hom x,
    source_stage_ideal_mem (R := R) (a := a) (J := J) hJmap f x⟩

/-- Helper for Lemma 10.39.6: forgetting the codomain restriction of
`source_stage_ideal_to_colimit` recovers the colimit leg on the underlying ideal element. -/
@[simp]
private theorem source_stage_ideal_to_colimit_apply
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J) :
    ((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x : a) :
        (colimit R : CommRingCat)) =
      ((colimit.cocone R).ι.app V).hom x := by
  -- The helper is defined by packaging the colimit-ring element with the membership proof.
  rfl

/-- Helper for Lemma 10.39.6: mapping the ideal spanned by a finite family from stage `U` into
the colimit ring is the ideal spanned by the colimit images of that family. -/
private theorem map_stage_span_generators_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    {U : Cᵒᵖ}
    {n : ℕ}
    (s : Fin n → R.obj U) :
    Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range s)) =
      Ideal.span (Set.range fun i : Fin n ↦ ((colimit.cocone R).ι.app U).hom (s i)) := by
  have himage :
      ((colimit.cocone R).ι.app U).hom '' Set.range s =
        Set.range fun i : Fin n ↦ ((colimit.cocone R).ι.app U).hom (s i) := by
    ext z
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨s i, ⟨i, rfl⟩, rfl⟩
  -- This is the finite-family specialization of `Ideal.map_span`.
  rw [Ideal.map_span, himage]

/-- Helper for Lemma 10.39.6: a colimit-ring linear combination of finitely many generators from
one stage already comes from a single later-stage extension of their span ideal. -/
private theorem span_member_lifts_to_common_stage
    (R : Cᵒᵖ ⥤ CommRingCat)
    {U : Cᵒᵖ}
    {n : ℕ}
    (s : Fin n → R.obj U)
    {y : (colimit R : CommRingCat)}
    (hy : y ∈ Ideal.span (Set.range fun i : Fin n ↦ ((colimit.cocone R).ι.app U).hom (s i))) :
    ∃ V, ∃ f : U ⟶ V, ∃ x : Ideal.map (R.map f).hom (Ideal.span (Set.range s)),
      ((colimit.cocone R).ι.app V).hom x = y := by
  -- Extract the finite coefficient family witnessing the span membership in the colimit ring.
  rcases (Ideal.mem_span_range_iff_exists_fun).1 hy with ⟨c, hc⟩
  obtain ⟨V, b, hb⟩ := filtered_colimit_exists_stage_family R n c
  let W : Cᵒᵖ := max' V U
  let g : V ⟶ W := IsFiltered.leftToMax V U
  let f : U ⟶ W := IsFiltered.rightToMax V U
  have hmem :
      ∑ i, (R.map g).hom (b i) * (R.map f).hom (s i) ∈
        Ideal.map (R.map f).hom (Ideal.span (Set.range s)) := by
    -- Each summand is a later-stage coefficient times a mapped stage generator.
    refine Ideal.sum_mem _ ?_
    intro i hi
    exact Ideal.mul_mem_left _ _ <|
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨W, f, ⟨∑ i, (R.map g).hom (b i) * (R.map f).hom (s i), hmem⟩, ?_⟩
  -- Compare the constructed later-stage linear combination with the original colimit element
  -- coefficient-by-coefficient.
  change ((colimit.cocone R).ι.app W).hom
      (∑ i, (R.map g).hom (b i) * (R.map f).hom (s i)) = y
  rw [map_sum]
  calc
    ∑ i, ((colimit.cocone R).ι.app W).hom ((R.map g).hom (b i) * (R.map f).hom (s i))
        = ∑ i,
            ((show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app V).hom (b i)) *
              (show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app U).hom (s i))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [map_mul]
          have hleft :
              ((colimit.cocone R).ι.app W).hom ((R.map g).hom (b i)) =
                ((colimit.cocone R).ι.app V).hom (b i) := by
            exact ConcreteCategory.congr_hom ((colimit.cocone R).w g) (b i)
          have hright :
              ((colimit.cocone R).ι.app W).hom ((R.map f).hom (s i)) =
                ((colimit.cocone R).ι.app U).hom (s i) := by
            exact ConcreteCategory.congr_hom ((colimit.cocone R).w f) (s i)
          rw [hleft, hright]
          rfl
    _ = ∑ i, c i * (show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app U).hom (s i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hb i]
    _ = y := hc

/-- Helper for Lemma 10.39.6: every element of the descended ideal `a` already comes from some
later-stage extension of the finitely generated stage ideal `J`. -/
private theorem source_stage_ideal_element_lifts
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJfg : J.FG)
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (y : a) :
    ∃ V, ∃ f : U ⟶ V, ∃ x : Ideal.map (R.map f).hom J,
      source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x = y := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hs' : Ideal.span (Set.range s) = J := by
    simpa using hs
  have hJmap_span :
      Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range s)) = a := by
    -- Rewrite the chosen stage ideal by its finite generating family.
    rw [hs']
    exact hJmap
  have hy_span :
      ((y : a) : (colimit R : CommRingCat)) ∈
        Ideal.span (Set.range fun i : Fin n ↦ ((colimit.cocone R).ι.app U).hom (s i)) := by
    -- Membership in `a` becomes span membership after identifying `a` with the mapped stage span.
    have hy_map :
        ((y : a) : (colimit R : CommRingCat)) ∈
          Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range s)) := by
      rw [hJmap_span]
      exact y.2
    rw [map_stage_span_generators_eq (R := R) (U := U) s] at hy_map
    exact hy_map
  obtain ⟨V, f, x, hx⟩ := span_member_lifts_to_common_stage (R := R) s hy_span
  have hxJ :
      (x : R.obj V) ∈ Ideal.map (R.map f).hom J := by
    -- The later-stage element still lies in the extension of the original ideal `J`.
    simpa [hs'] using x.2
  let xJ : Ideal.map (R.map f).hom J := ⟨x, hxJ⟩
  refine ⟨V, f, xJ, ?_⟩
  -- Equality in the subtype `a` reduces to the underlying colimit-ring element equality.
  apply Subtype.ext
  simpa [xJ, source_stage_ideal_to_colimit_apply] using hx

/-- Helper for Lemma 10.39.6: pushing a descended stage-ideal element one step farther along the
diagram lands in the correspondingly farther extended ideal. -/
private noncomputable def source_stage_ideal_transition
    (R : Cᵒᵖ ⥤ CommRingCat)
    {U V W : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (f : U ⟶ V) (g : V ⟶ W) :
    Ideal.map (R.map f).hom J → Ideal.map (R.map (f ≫ g)).hom J :=
  fun x ↦ ⟨(R.map g).hom x, by
    -- Membership is preserved by mapping once more and identifying the two-step image ideal.
    simpa [Ideal.map_map] using Ideal.mem_map_of_mem (R.map g).hom x.2⟩

/-- Helper for Lemma 10.39.6: forgetting the codomain restriction of
`source_stage_ideal_transition` recovers the obvious later-stage ring element. -/
@[simp]
private theorem source_stage_ideal_transition_apply
    (R : Cᵒᵖ ⥤ CommRingCat)
    {U V W : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (f : U ⟶ V) (g : V ⟶ W)
    (x : Ideal.map (R.map f).hom J) :
    ((source_stage_ideal_transition (R := R) J f g x :
        Ideal.map (R.map (f ≫ g)).hom J) : R.obj W) =
      (R.map g).hom x := by
  -- The transition helper is defined by applying the ring map to the underlying element.
  rfl

/-- Helper for Lemma 10.39.6: the colimit representative of a descended ideal element is
unchanged after pushing that element to a later stage. -/
private theorem source_stage_ideal_to_colimit_transition
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V W : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V) (g : V ⟶ W)
    (x : Ideal.map (R.map f).hom J) :
    source_stage_ideal_to_colimit (R := R) (a := a) J hJmap (f ≫ g)
        (source_stage_ideal_transition (R := R) J f g x) =
      source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x := by
  -- Both sides are the same colimit-ring element by the cocone relation on the ring diagram.
  apply Subtype.ext
  change ((colimit.cocone R).ι.app W).hom ((R.map g).hom x) =
      ((colimit.cocone R).ι.app V).hom x
  exact ConcreteCategory.congr_hom ((colimit.cocone R).w g) x

/-- Helper for Lemma 10.39.6: later-stage transition maps do not change the represented element in
the module colimit. -/
private theorem module_colimit_map_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {V W : Cᵒᵖ} (g : V ⟶ W) (m : M.obj V) :
    (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := W) (M.map g m) :
          colimit_target_module R M) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) m := by
  -- This is exactly the cocone relation for the module colimit.
  exact ConcreteCategory.congr_hom ((colimit.cocone M.presheaf).w g) m

/-- Helper for Lemma 10.39.6: on pure tensors, transporting a stage tensor forward and then
placing it in `a ⊗[colimit R] colimit_target_module R M` agrees with placing it there directly. -/
private theorem stage_tensor_to_flat_test_transition_tmul
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V W : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V) (g : V ⟶ W)
    (x : Ideal.map (R.map f).hom J) (m : M.obj V) :
    (show TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M) from
      ((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap (f ≫ g)
            (source_stage_ideal_transition (R := R) J f g x)) :
          a) ⊗ₜ[(colimit R : CommRingCat)] (PresheafOfModules.ModuleColimit.ιM
            (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
            (hcM := colimit.isColimit M.presheaf) (U := W) (M.map g m) :
              colimit_target_module R M)) =
      (show TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M) from
        ((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x :
            a) ⊗ₜ[(colimit R : CommRingCat)] (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit M.presheaf) (U := V) m :
                colimit_target_module R M))) := by
  -- Compare the ideal and module factors separately after passing to the later stage.
  rw [source_stage_ideal_to_colimit_transition (R := R) (a := a) J hJmap f g x,
    module_colimit_map_eq (R := R) (M := M) g m]

/-- Helper for Lemma 10.39.6: the global pure tensor determined by a stage ideal element and a
stage module element. -/
private noncomputable def stage_global_tensor
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J)
    (m : M.obj V) :
    TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M) :=
  ((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x : a) ⊗ₜ[(colimit R : CommRingCat)]
    (PresheafOfModules.ModuleColimit.ιM
      (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
      (hcM := colimit.isColimit M.presheaf) (U := V) m :
        colimit_target_module R M))

/-- Helper for Lemma 10.39.6: the scalar coming from a stage ring element becomes the native
stage scalar in the forgotten ring colimit after applying the preserved-colimit comparison. -/
private theorem colimit_target_module_scalar_transport_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    {V : Cᵒᵖ}
    (r : R.obj V) :
    (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom
        (((colimit.cocone R).ι.app V).hom r) =
      PresheafOfModules.ModuleColimit.ιR
        (cR := colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)) r := by
  -- Evaluate the cocone-point comparison on the chosen stage element.
  simpa [PresheafOfModules.ModuleColimit.ιR] using
    congrArg (fun φ => φ r) (colimit_hom_comp_ι (R := R) V)

/-- Helper for Lemma 10.39.6: scalar multiplication on `colimit_target_module R M` by a stage
scalar is the native `ModuleColimit` stage action after one restrict-scalars rewrite. -/
private theorem colimit_target_module_restrict_stage_smul_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {V : Cᵒᵖ}
    (r : R.obj V) (m : M.obj V) :
    (LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)
        (((colimit.cocone R).ι.app V).hom r)
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) m :
          colimit_target_module R M)) =
    (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) (r • m) :
          colimit_target_module R M) := by
  -- The colimit target module is the forgotten module colimit with scalars restricted along the
  -- preserved-colimit ring isomorphism, so restriction-of-scalars rewrites the stage scalar to
  -- `ModuleColimit.ιR`, after which `ModuleColimit.smul_eq` closes the computation.
  rw [LinearMap.lsmul_apply]
  have hsmul :=
    ModuleCat.restrictScalars.smul_def
      (f := (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom)
      (M := ((colimitFunctor.{u}
        (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M))
      (((colimit.cocone R).ι.app V).hom r)
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) m :
          ((ModuleCat.restrictScalars
              (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
            ((colimitFunctor.{u}
              (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M)))
  rw [hsmul]
  rw [colimit_target_module_scalar_transport_eq (R := R) (V := V) (r := r)]
  simpa using
    (PresheafOfModules.ModuleColimit.smul_eq
      (cR := colimit.cocone (R ⋙ forget₂ CommRingCat RingCat))
      (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
      (hcM := colimit.isColimit M.presheaf)
      (U := V) r m)

/-- Helper for Lemma 10.39.6: the descended ideal element in `colimit R` becomes the expected
stage scalar in the forgotten colimit ring. -/
private theorem source_stage_ideal_to_forget_colimit_scalar_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J) :
    (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom
        (((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x : a) :
          (colimit R : CommRingCat))) =
      PresheafOfModules.ModuleColimit.ιR
        (cR := colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)) (x : R.obj V) := by
  -- Rewrite the descended ideal element to its stage representative and then apply the scalar
  -- transport lemma at that stage.
  rw [source_stage_ideal_to_colimit_apply]
  simpa using
    colimit_target_module_scalar_transport_eq (R := R) (V := V) (r := (x : R.obj V))

/-- Helper for Lemma 10.39.6: scalar multiplication on `colimit_target_module R M` by a descended
stage-ideal element is the stage scalar action seen through `ModuleColimit.smul_eq`. -/
private theorem colimit_target_module_stage_smul_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J) (m : M.obj V) :
    (LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)
        (((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x : a) :
          (colimit R : CommRingCat)))
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) m :
          colimit_target_module R M)) =
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) ((x : R.obj V) • m) :
          colimit_target_module R M) := by
  -- Specialize the generic stage-scalar identity after rewriting the descended ideal element.
  rw [source_stage_ideal_to_colimit_apply]
  simpa using
    colimit_target_module_restrict_stage_smul_eq (R := R) (M := M) (V := V) (r := (x : R.obj V))
      (m := m)

/-- Helper for Lemma 10.39.6: on pure tensors, the global flatness-test map is exactly the
colimit class of the corresponding stage multiplication element. -/
private theorem flat_test_map_stage_tensor_tmul_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    (x : Ideal.map (R.map f).hom J) (m : M.obj V) :
    TensorProduct.lift
        ((LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)).comp a.subtype)
        (show TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M) from
          ((source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f x :
              a) ⊗ₜ[(colimit R : CommRingCat)] (PresheafOfModules.ModuleColimit.ιM
                (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
                (hcM := colimit.isColimit M.presheaf) (U := V) m :
                  colimit_target_module R M))) =
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V)
            ((TensorProduct.lift
            ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
            (x ⊗ₜ[R.obj V] m)) :
          M.obj V) :
            colimit_target_module R M) := by
  -- Route correction: after isolating the scalar-action transport, the pure-tensor image is just
  -- `TensorProduct.lift_tmul` followed by the stage multiplication formula.
  rw [TensorProduct.lift.tmul]
  rw [stage_extension_tensor_map_tmul (R := R) (M := M) (f := f) (J := J) (x := x) (m := m)]
  simpa [LinearMap.comp_apply] using
    (colimit_target_module_stage_smul_eq (R := R) (M := M) (a := a) J hJmap f x m)

/-- Helper for Lemma 10.39.6: two elements from the same stage of the module diagram become equal
in the colimit exactly when they agree after passing to a later stage. -/
private theorem module_colimit_eq_iff_exists_stage_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U : Cᵒᵖ} (m m' : M.obj U) :
    (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) m :
          colimit_target_module R M) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) m' ↔
      ∃ V, ∃ f : U ⟶ V, M.map f m = M.map f m' := by
  let cM := colimit.cocone M.presheaf
  let G : Cᵒᵖ ⥤ Type u := M.presheaf ⋙ forget AddCommGrpCat
  let cG : Cocone G := (forget AddCommGrpCat).mapCocone cM
  have hcG : IsColimit cG := by
    simpa [G, cG, cM] using
      (Limits.isColimitOfPreserves (forget AddCommGrpCat) (colimit.isColimit M.presheaf))
  -- Both sides are the same filtered-colimit equality, seen once in modules and once in types.
  change ((cM.ι.app U).hom m : cM.pt) = (cM.ι.app U).hom m' ↔
      ∃ V, ∃ f : U ⟶ V, M.map f m = M.map f m'
  constructor
  · intro hm
    -- Read equality in the colimit back at a later stage via the filtered-colimit criterion.
    have hm' : cG.ι.app U m = cG.ι.app U m' := by
      simpa [cG, cM] using hm
    obtain ⟨V, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (F := G) hcG m m').1 hm'
    refine ⟨V, f, ?_⟩
    simpa [G] using hf
  · rintro ⟨V, f, hf⟩
    have hm' :
        cG.ι.app U m = cG.ι.app U m' :=
      (Types.FilteredColimit.isColimit_eq_iff' (F := G) hcG m m').2
        ⟨V, f, by simpa [G] using hf⟩
    simpa [cG, cM] using hm'

/-- Helper for Lemma 10.39.6: an element coming from one stage of the module diagram vanishes in
the colimit exactly when it becomes zero at a later stage. -/
private theorem module_colimit_zero_iff_exists_stage_zero
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U : Cᵒᵖ} (m : M.obj U) :
    (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) m :
          colimit_target_module R M) = 0 ↔
      ∃ V, ∃ f : U ⟶ V, M.map f m = 0 := by
  -- Specialize the previous equality criterion to compare with the zero element.
  constructor
  · intro hm
    have hm' :
        (PresheafOfModules.ModuleColimit.ιM
            (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
            (hcM := colimit.isColimit M.presheaf) m :
              colimit_target_module R M) =
          PresheafOfModules.ModuleColimit.ιM
            (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
            (hcM := colimit.isColimit M.presheaf) (0 : M.obj U) := by
      simpa using hm
    rcases (module_colimit_eq_iff_exists_stage_eq R M m (0 : M.obj U)).1 hm' with ⟨V, f, hf⟩
    have hf0 : (M.map f).hom m = (M.map f).hom (0 : M.obj U) := by
      simpa using hf
    have hf' : (M.map f).hom m = 0 := by
      rw [hf0, (M.map f).hom.map_zero]
    exact ⟨V, f, hf'⟩
  · rintro ⟨V, f, hf⟩
    have hf0 : (M.map f).hom (0 : M.obj U) = 0 := by
      simpa using (M.map f).hom.map_zero
    have hf' : (M.map f).hom m = (M.map f).hom (0 : M.obj U) := by
      rw [hf, hf0]
    have hm' :=
      (module_colimit_eq_iff_exists_stage_eq R M m (0 : M.obj U)).2
        ⟨V, f, hf'⟩
    simpa using hm'

/-- Helper for Lemma 10.39.6: any finite family of elements in the colimit module already lifts
to one common stage. -/
private theorem filtered_colimit_exists_stage_module_family
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ∀ n : ℕ, ∀ m : Fin n → colimit_target_module R M,
      ∃ U, ∃ x : Fin n → M.obj U, ∀ i,
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit M.presheaf) (x i) :
            colimit_target_module R M) = m i
  | 0, m => by
      let U : Cᵒᵖ := IsFiltered.nonempty.some
      refine ⟨U, fun i => Fin.elim0 i, ?_⟩
      intro i
      exact Fin.elim0 i
  | n + 1, m => by
      let cM := colimit.cocone M.presheaf
      let G : Cᵒᵖ ⥤ Type u := M.presheaf ⋙ forget AddCommGrpCat
      let cG : Cocone G := (forget AddCommGrpCat).mapCocone cM
      have hcG : IsColimit cG := by
        -- The underlying additive-group cocone of `M` remains colimiting after forgetting.
        simpa [G, cM, cG] using
          (Limits.isColimitOfPreserves (forget AddCommGrpCat) (colimit.isColimit M.presheaf))
      -- First descend the tail, then enlarge once more to capture the head element too.
      obtain ⟨U, x, hx⟩ :=
        filtered_colimit_exists_stage_module_family R M n (fun i : Fin n ↦ m i.succ)
      obtain ⟨V, y, hy⟩ :=
        Types.jointly_surjective_of_isColimit hcG (m 0)
      refine ⟨max' V U,
        Fin.cons (M.map (IsFiltered.leftToMax V U) y)
          (fun i ↦ M.map (IsFiltered.rightToMax V U) (x i)),
        ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · -- Push the head element from `V` to the common upper stage.
        let y' : M.obj (max' V U) := M.map (IsFiltered.leftToMax V U) y
        have hhead :
            (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit M.presheaf)
              y' :
                colimit_target_module R M) =
              (PresheafOfModules.ModuleColimit.ιM
                (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
                (hcM := colimit.isColimit M.presheaf) y :
                  colimit_target_module R M) := by
          exact ConcreteCategory.congr_hom
            ((colimit.cocone M.presheaf).w (IsFiltered.leftToMax V U)) y
        exact hhead.trans hy
      · intro i
        -- Push the tail elements from the inductively chosen common stage.
        let x' : M.obj (max' V U) := M.map (IsFiltered.rightToMax V U) (x i)
        have htail :
            (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit M.presheaf)
              x' :
                colimit_target_module R M) =
              (PresheafOfModules.ModuleColimit.ιM
                (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
                (hcM := colimit.isColimit M.presheaf) (x i) :
                  colimit_target_module R M) := by
          exact ConcreteCategory.congr_hom
            ((colimit.cocone M.presheaf).w (IsFiltered.rightToMax V U)) (x i)
        exact htail.trans (hx i)

/-- Helper for Lemma 10.39.6: any finite matrix of elements in the colimit ring already lifts to
one common stage. -/
private theorem filtered_colimit_exists_stage_ring_matrix_family
    (R : Cᵒᵖ ⥤ CommRingCat) :
    ∀ n r : ℕ, ∀ c : Fin n → Fin r → (colimit R : CommRingCat),
      ∃ U, ∃ b : Fin n → Fin r → R.obj U, ∀ i j,
        (colimit.cocone R).ι.app U (b i j) = c i j
  | 0, r, c => by
      let U : Cᵒᵖ := IsFiltered.nonempty.some
      refine ⟨U, fun i => Fin.elim0 i, ?_⟩
      intro i
      exact Fin.elim0 i
  | n + 1, r, c => by
      -- First descend the tail rows, then enlarge once more to capture the head row.
      obtain ⟨U, b, hb⟩ :=
        filtered_colimit_exists_stage_ring_matrix_family R n r (fun i : Fin n ↦ c i.succ)
      obtain ⟨V, d, hd⟩ := filtered_colimit_exists_stage_family R r (c 0)
      refine ⟨max' V U,
        Fin.cons
          (fun j ↦ R.map (IsFiltered.leftToMax V U) (d j))
          (fun i j ↦ R.map (IsFiltered.rightToMax V U) (b i j)),
        ?_⟩
      intro i j
      refine Fin.cases ?_ ?_ i
      · -- Push the head row from `V` to the common upper stage.
        have hhead :
            (colimit.cocone R).ι.app (max' V U)
                (R.map (IsFiltered.leftToMax V U) (d j)) =
              (colimit.cocone R).ι.app V (d j) := by
          exact ConcreteCategory.congr_hom
            ((colimit.cocone R).w (IsFiltered.leftToMax V U)) (d j)
        exact hhead.trans (hd j)
      · intro i
        -- Push the tail rows from the inductively chosen common stage.
        have htail :
            (colimit.cocone R).ι.app (max' V U)
                (R.map (IsFiltered.rightToMax V U) (b i j)) =
              (colimit.cocone R).ι.app U (b i j) := by
          exact ConcreteCategory.congr_hom
            ((colimit.cocone R).w (IsFiltered.rightToMax V U)) (b i j)
        exact htail.trans (hb i j)

/-- Helper for Lemma 10.39.6: finitely many elements of the descended ideal `a` already come from
one common later-stage extension of `J`. -/
private theorem filtered_colimit_exists_stage_ideal_family
    (R : Cᵒᵖ ⥤ CommRingCat)
    {a : Ideal (colimit R : CommRingCat)} {U : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJfg : J.FG)
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    {n : ℕ} (y : Fin n → a) :
    ∃ V, ∃ f : U ⟶ V, ∃ x : Fin n → Ideal.map (R.map f).hom J, ∀ i,
      source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f (x i) = y i := by
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hs' : Ideal.span (Set.range s) = J := by
    simpa using hs
  have hJmap_span :
      Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range s)) = a := by
    -- Rewrite the descended ideal by a finite generating family.
    rw [hs']
    exact hJmap
  have hy_span :
      ∀ i, (((y i : a) : (colimit R : CommRingCat)) ∈
        Ideal.span (Set.range fun j : Fin r ↦ ((colimit.cocone R).ι.app U).hom (s j))) := by
    intro i
    have hy_map :
        ((y i : a) : (colimit R : CommRingCat)) ∈
          Ideal.map ((colimit.cocone R).ι.app U).hom (Ideal.span (Set.range s)) := by
      rw [hJmap_span]
      exact (y i).2
    rwa [map_stage_span_generators_eq (R := R) (U := U) s] at hy_map
  choose c hc using fun i ↦ (Ideal.mem_span_range_iff_exists_fun).1 (hy_span i)
  obtain ⟨V, b, hb⟩ :=
    filtered_colimit_exists_stage_ring_matrix_family R n r c
  let W : Cᵒᵖ := max' V U
  let g : V ⟶ W := IsFiltered.leftToMax V U
  let f : U ⟶ W := IsFiltered.rightToMax V U
  have hmem :
      ∀ i,
        ∑ j, (R.map g).hom (b i j) * (R.map f).hom (s j) ∈
          Ideal.map (R.map f).hom J := by
    intro i
    -- Each summand is a later-stage coefficient times a mapped generator of `J`.
    refine Ideal.sum_mem _ ?_
    intro j hj
    have hs_mem : s j ∈ J := by
      simpa [hs'] using (Ideal.subset_span (s := Set.range s) ⟨j, rfl⟩)
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hs_mem)
  refine ⟨W, f, fun i ↦ ⟨∑ j, (R.map g).hom (b i j) * (R.map f).hom (s j), hmem i⟩, ?_⟩
  intro i
  -- Compare the constructed later-stage linear combination with the prescribed colimit ideal
  -- element coefficient-by-coefficient.
  apply Subtype.ext
  change ((colimit.cocone R).ι.app W).hom
      (∑ j, (R.map g).hom (b i j) * (R.map f).hom (s j)) =
    ((y i : a) : (colimit R : CommRingCat))
  rw [map_sum]
  calc
    ∑ j, ((colimit.cocone R).ι.app W).hom ((R.map g).hom (b i j) * (R.map f).hom (s j))
        = ∑ j,
            ((show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app V).hom (b i j)) *
              (show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app U).hom (s j))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [map_mul]
          have hleft :
              ((colimit.cocone R).ι.app W).hom ((R.map g).hom (b i j)) =
                ((colimit.cocone R).ι.app V).hom (b i j) := by
            exact ConcreteCategory.congr_hom ((colimit.cocone R).w g) (b i j)
          have hright :
              ((colimit.cocone R).ι.app W).hom ((R.map f).hom (s j)) =
                ((colimit.cocone R).ι.app U).hom (s j) := by
            exact ConcreteCategory.congr_hom ((colimit.cocone R).w f) (s j)
          rw [hleft, hright]
          rfl
    _ = ∑ j, c i j * (show (colimit R : CommRingCat) from ((colimit.cocone R).ι.app U).hom (s j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hb i j]
    _ = ((y i : a) : (colimit R : CommRingCat)) := hc i

/-- Helper for Lemma 10.39.6: every tensor is a finite sum of pure tensors. -/
private theorem tensor_product_exists_fin_representation
    {S : Type u} [CommRing S]
    {A B : Type u} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (z : TensorProduct S A B) :
    ∃ n, ∃ x : Fin n → A, ∃ y : Fin n → B, z = ∑ i, x i ⊗ₜ[S] y i := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp
  · intro x y
    refine ⟨1, fun _ ↦ x, fun _ ↦ y, ?_⟩
    simp
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨n₁, x₁, y₁, rfl⟩
    rcases hz₂ with ⟨n₂, x₂, y₂, rfl⟩
    refine ⟨n₁ + n₂, Fin.append x₁ x₂, Fin.append y₁ y₂, ?_⟩
    simp [Fin.sum_univ_add]

/-- Helper for Lemma 10.39.6: every tensor in `a ⊗[colimit R] colimit_target_module R M` is a
finite sum of pure tensors coming from one common stage. -/
private theorem tensor_lifts_to_common_stage
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJfg : J.FG)
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (z : TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M)) :
    ∃ n, ∃ V, ∃ f : U ⟶ V,
      ∃ x : Fin n → Ideal.map (R.map f).hom J,
        ∃ m : Fin n → M.obj V,
          z = ∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i) := by
  obtain ⟨n, y, m, rfl⟩ := tensor_product_exists_fin_representation z
  obtain ⟨V₁, f, x, hx⟩ :=
    filtered_colimit_exists_stage_ideal_family (R := R) (a := a) J hJfg hJmap y
  obtain ⟨V₂, m', hm⟩ := filtered_colimit_exists_stage_module_family R M n m
  let W : Cᵒᵖ := max' V₁ V₂
  let g₁ : V₁ ⟶ W := IsFiltered.leftToMax V₁ V₂
  let g₂ : V₂ ⟶ W := IsFiltered.rightToMax V₁ V₂
  refine ⟨n, W, f ≫ g₁, fun i ↦ source_stage_ideal_transition (R := R) J f g₁ (x i),
    fun i ↦ M.map g₂ (m' i), ?_⟩
  -- Push the ideal-side and module-side representatives to one common stage.
  calc
    ∑ i, y i ⊗ₜ[(colimit R : CommRingCat)] m i
        = ∑ i,
            stage_global_tensor (R := R) (M := M) (a := a) J hJmap (f ≫ g₁)
              (source_stage_ideal_transition (R := R) J f g₁ (x i)) (M.map g₂ (m' i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hmodule :
              (PresheafOfModules.ModuleColimit.ιM
                (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
                (hcM := colimit.isColimit M.presheaf) (U := W) (M.map g₂ (m' i)) :
                  colimit_target_module R M) = m i := by
            rw [module_colimit_map_eq (R := R) (M := M) g₂ (m' i), hm i]
          rw [stage_global_tensor, source_stage_ideal_to_colimit_transition (R := R) (a := a) J
            hJmap f g₁ (x i), hx i, hmodule]

/-- Helper for Lemma 10.39.6: the global flatness-test map on a staged finite sum is the colimit
class of the corresponding finite sum of stage multiplication elements. -/
private theorem flat_test_map_lifted_stage_sum_eq
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    {n : ℕ}
    (x : Fin n → Ideal.map (R.map f).hom J)
    (m : Fin n → M.obj V) :
    TensorProduct.lift
        ((LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)).comp a.subtype)
        (∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i)) =
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V)
          (∑ i, TensorProduct.lift
            ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
            (x i ⊗ₜ[R.obj V] m i)) :
              colimit_target_module R M) := by
  -- Rewrite the global tensor map termwise and then fold the result back into one stage sum.
  rw [map_sum]
  calc
    ∑ i,
        TensorProduct.lift
          ((LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)).comp a.subtype)
          (stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i))
        = ∑ i,
            (PresheafOfModules.ModuleColimit.ιM
              (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
              (hcM := colimit.isColimit M.presheaf) (U := V)
                (TensorProduct.lift
                  ((LinearMap.lsmul (R.obj V) (M.obj V)).comp
                    (Ideal.map (R.map f).hom J).subtype)
                  (x i ⊗ₜ[R.obj V] m i)) :
                    colimit_target_module R M) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using flat_test_map_stage_tensor_tmul_eq (R := R) (M := M) (a := a) J hJmap f
            (x i) (m i)
    _ = (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit M.presheaf) (U := V)
            (∑ i, TensorProduct.lift
              ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
              (x i ⊗ₜ[R.obj V] m i)) :
                colimit_target_module R M) := by
          symm
          simpa using (((colimit.cocone M.presheaf).ι.app V).hom.map_sum
            (fun i ↦ TensorProduct.lift
              ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
              (x i ⊗ₜ[R.obj V] m i))
            Finset.univ)

/-- Helper for Lemma 10.39.6: if the colimit class of a staged sum is zero, then after passing to
a later stage the corresponding stage sum is already zero. -/
private theorem lifted_stage_sum_zero_later
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (f : U ⟶ V)
    {n : ℕ}
    (x : Fin n → Ideal.map (R.map f).hom J)
    (m : Fin n → M.obj V)
    (hzero : (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V)
          (∑ i, TensorProduct.lift
            ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
            (x i ⊗ₜ[R.obj V] m i)) :
              colimit_target_module R M) = 0) :
    ∃ W, ∃ g : V ⟶ W,
      ∑ i, TensorProduct.lift
        ((LinearMap.lsmul (R.obj W) (M.obj W)).comp (Ideal.map (R.map (f ≫ g)).hom J).subtype)
        (source_stage_ideal_transition (R := R) J f g (x i) ⊗ₜ[R.obj W] M.map g (m i)) = 0 := by
  let s : M.obj V :=
    ∑ i, TensorProduct.lift
      ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
      (x i ⊗ₜ[R.obj V] m i)
  have hs_zero :
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
        (hcM := colimit.isColimit M.presheaf) (U := V) s :
          colimit_target_module R M) = 0 := by
    simpa [s] using hzero
  obtain ⟨W, g, hg⟩ := (module_colimit_zero_iff_exists_stage_zero R M s).1 hs_zero
  refine ⟨W, g, ?_⟩
  let mW : Fin n → M.obj W := fun i ↦ M.map g (m i)
  have hmap :
      M.map g s =
        ∑ i, TensorProduct.lift
          ((LinearMap.lsmul (R.obj W) (M.obj W)).comp
            (Ideal.map (R.map (f ≫ g)).hom J).subtype)
          (source_stage_ideal_transition (R := R) J f g (x i) ⊗ₜ[R.obj W] mW i) := by
    -- Map the stage sum forward termwise and rewrite each summand via semilinearity.
    dsimp [s]
    calc
      M.map g (∑ i, (x i : R.obj V) • m i)
          = ∑ i, M.map g ((x i : R.obj V) • m i) := by
              simpa using (map_sum (M.map g).hom (fun i ↦ (x i : R.obj V) • m i) Finset.univ)
      _ = ∑ i, ((source_stage_ideal_transition (R := R) J f g (x i) : Ideal.map (R.map (f ≫ g)).hom J) :
            R.obj W) • mW i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              show (M.map g) ((x i : R.obj V) • m i) =
                (((source_stage_ideal_transition (R := R) J f g (x i) : Ideal.map (R.map (f ≫ g)).hom J) :
                  R.obj W) • mW i)
              simpa [mW, source_stage_ideal_transition_apply] using
                (PresheafOfModules.map_smul (M := M) g (x i : R.obj V) (m i))
      _ = ∑ i, TensorProduct.lift
            ((LinearMap.lsmul (R.obj W) (M.obj W)).comp
              (Ideal.map (R.map (f ≫ g)).hom J).subtype)
            (source_stage_ideal_transition (R := R) J f g (x i) ⊗ₜ[R.obj W] mW i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              symm
              exact stage_extension_tensor_map_tmul (R := R) (M := M) (f := f ≫ g) (J := J)
                (x := source_stage_ideal_transition (R := R) J f g (x i)) (m := mW i)
  rw [hmap] at hg
  exact hg

/-- Helper for Lemma 10.39.6: a zero relation among stage tensors remains zero after sending the
pure tensors to the global tensor product. -/
private theorem stage_tensor_sum_zero_to_colimit_zero
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {a : Ideal (colimit R : CommRingCat)} {U V : Cᵒᵖ}
    (J : Ideal (R.obj U))
    (hJmap : Ideal.map ((colimit.cocone R).ι.app U).hom J = a)
    (f : U ⟶ V)
    {n : ℕ}
    (x : Fin n → Ideal.map (R.map f).hom J)
    (m : Fin n → M.obj V)
    (hzero : ∑ i, x i ⊗ₜ[R.obj V] m i = 0) :
    ∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i) = 0 := by
  letI : Module (((Functor.const Cᵒᵖ).obj (colimit.cocone R).pt).obj V) a := by
    change Module (colimit R : CommRingCat) a
    infer_instance
  letI :
      Module (((Functor.const Cᵒᵖ).obj (colimit.cocone R).pt).obj V) (colimit_target_module R M) := by
    change Module (colimit R : CommRingCat) (colimit_target_module R M)
    infer_instance
  let hleft :
      Ideal.map (R.map f).hom J →ₛₗ[((colimit.cocone R).ι.app V).hom] a := by
    -- The descended ideal element map is semilinear over the stage-to-colimit ring map.
    refine
      { toFun := source_stage_ideal_to_colimit (R := R) (a := a) J hJmap f
        map_add' := by
          intro x y
          apply Subtype.ext
          simpa using map_add ((colimit.cocone R).ι.app V).hom (x : R.obj V) (y : R.obj V)
        map_smul' := by
          intro r x
          apply Subtype.ext
          simpa [smul_eq_mul] using map_mul ((colimit.cocone R).ι.app V).hom r (x : R.obj V) }
  let hright :
      M.obj V →ₛₗ[((colimit.cocone R).ι.app V).hom] colimit_target_module R M := by
    -- The colimit inclusion is semilinear over the stage ring.
    refine
      { toFun := fun m ↦ (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit M.presheaf) (U := V) m :
            colimit_target_module R M)
        map_add' := by
          intro m₁ m₂
          exact (PresheafOfModules.ModuleColimit.ιM
            (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
            (hcM := colimit.isColimit M.presheaf) (U := V)).map_add m₁ m₂
        map_smul' := by
          intro r m
          simpa [LinearMap.lsmul_apply] using
            colimit_target_module_restrict_stage_smul_eq (R := R) (M := M) (V := V) (r := r)
              (m := m).symm }
  have hmap :
      TensorProduct.map hleft hright (∑ i, x i ⊗ₜ[R.obj V] m i) =
        ∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa [hleft, hright, stage_global_tensor] using
      TensorProduct.map_tmul hleft hright (x i) (m i)
  have hzero' :=
    congrArg (TensorProduct.map hleft hright) hzero
  rw [hmap] at hzero'
  simpa using hzero'

-- Proof sketch: use the finitely generated ideal criterion for flatness. Descend a finitely
-- generated ideal of the colimit ring to one stage, view the target tensor map as the filtered
-- colimit of the corresponding stage tensor maps, and use stagewise injectivity together with
-- exactness of filtered colimits.
/-- Lemma 10.39.6 (2): if `R` is a cofiltered system of commutative rings and `M` is a compatible
system of flat modules over `R`, then the canonical colimit module over `colimit R` is flat. This
is the categorical reformulation of the directed-system statement `M = \mathop{\mathrm{colim}}_i
M_i`. -/
theorem flat_colimitFunctor_of_stagewise_flat
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [∀ U, Module.Flat (R.obj U) (M.obj U)] :
    Module.Flat (colimit R : CommRingCat)
      ((ModuleCat.restrictScalars
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
        ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M)) := by
  -- Route correction: the stalled fixed-base `extendScalars` diagram obscured the source proof
  -- and depended on transport-heavy functoriality. Return to the textbook finitely-generated-ideal
  -- criterion and descend the chosen ideal to one stage.
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro a ha
  obtain ⟨U, J, hJfg, hJmap⟩ := exists_fg_stage_ideal_of_colimit_ideal R a ha
  have hstage_mono :
      ∀ {V : Cᵒᵖ} (f : U ⟶ V),
        Mono <| ModuleCat.ofHom <|
          TensorProduct.lift
            ((LinearMap.lsmul (R.obj V) (M.obj V)).comp
              (Ideal.map (R.map f).hom J).subtype) := by
    intro V f
    -- Each later-stage test map is injective by the flatness hypothesis at that stage.
    simpa using stage_extension_tensor_map_mono (R := R) (M := M) f J hJfg
  rw [Function.Injective]
  intro z₁ z₂ hEq
  have hkernel : z₁ - z₂ = 0 := by
    let z : TensorProduct (colimit R : CommRingCat) a (colimit_target_module R M) := z₁ - z₂
    have hz :
        TensorProduct.lift
            ((LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)).comp a.subtype)
            z = 0 := by
      dsimp [z]
      simpa [map_sub, hEq]
    obtain ⟨n, V, f, x, m, hz_repr⟩ :=
      tensor_lifts_to_common_stage (R := R) (M := M) (a := a) J hJfg hJmap z
    have hflat_test :
        TensorProduct.lift
            ((LinearMap.lsmul (colimit R : CommRingCat) (colimit_target_module R M)).comp a.subtype)
            (∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i)) =
          (PresheafOfModules.ModuleColimit.ιM
            (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
            (hcM := colimit.isColimit M.presheaf) (U := V)
              (∑ i, TensorProduct.lift
                ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
                (x i ⊗ₜ[R.obj V] m i)) :
                  colimit_target_module R M) :=
      flat_test_map_lifted_stage_sum_eq (R := R) (M := M) (a := a) J hJmap f x m
    have hcolim_zero :
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))
          (hcM := colimit.isColimit M.presheaf) (U := V)
            (∑ i, TensorProduct.lift
              ((LinearMap.lsmul (R.obj V) (M.obj V)).comp (Ideal.map (R.map f).hom J).subtype)
              (x i ⊗ₜ[R.obj V] m i)) :
                colimit_target_module R M) = 0 := by
      rw [← hflat_test]
      simpa [z, hz_repr] using hz
    obtain ⟨W, g, hg⟩ := lifted_stage_sum_zero_later (R := R) (M := M) J f x m hcolim_zero
    have hstage_injective :
        Function.Injective
          (TensorProduct.lift
            ((LinearMap.lsmul (R.obj W) (M.obj W)).comp
              (Ideal.map (R.map (f ≫ g)).hom J).subtype)) := by
      exact
        (ModuleCat.mono_iff_injective <| ModuleCat.ofHom <|
          TensorProduct.lift
            ((LinearMap.lsmul (R.obj W) (M.obj W)).comp
              (Ideal.map (R.map (f ≫ g)).hom J).subtype)).1
          (hstage_mono (f ≫ g))
    have hstage_tensor_zero :
        ∑ i, source_stage_ideal_transition (R := R) J f g (x i) ⊗ₜ[R.obj W]
          (show M.obj W from M.map g (m i)) = 0 := by
      apply hstage_injective
      simpa using hg
    have hglobal_zero :
        ∑ i,
            stage_global_tensor (R := R) (M := M) (a := a) J hJmap (f ≫ g)
              (source_stage_ideal_transition (R := R) J f g (x i))
              (show M.obj W from M.map g (m i)) = 0 :=
      stage_tensor_sum_zero_to_colimit_zero (R := R) (M := M) (a := a) J hJmap (f ≫ g)
        (fun i ↦ source_stage_ideal_transition (R := R) J f g (x i))
        (fun i ↦ (show M.obj W from M.map g (m i))) hstage_tensor_zero
    have htransition :
        ∑ i,
            stage_global_tensor (R := R) (M := M) (a := a) J hJmap (f ≫ g)
              (source_stage_ideal_transition (R := R) J f g (x i))
              (show M.obj W from M.map g (m i)) =
          ∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i) := by
      -- Passing to a later stage does not change the represented global tensor.
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [stage_global_tensor] using
        stage_tensor_to_flat_test_transition_tmul (R := R) (M := M) (a := a) J hJmap f g
          (x i) (m i)
    calc
      z = ∑ i, stage_global_tensor (R := R) (M := M) (a := a) J hJmap f (x i) (m i) := hz_repr
      _ = ∑ i,
            stage_global_tensor (R := R) (M := M) (a := a) J hJmap (f ≫ g)
              (source_stage_ideal_transition (R := R) J f g (x i))
              (show M.obj W from M.map g (m i)) := by
            symm
            exact htransition
      _ = 0 := hglobal_zero
  exact sub_eq_zero.mp hkernel

-- Proof sketch: consider the constant presheaf of modules over `R` attached to the
-- `colimit R`-module `M`. Each stage is the restriction of scalars of `M` to `R.obj U`, so the
-- stagewise flatness hypothesis lets us apply the compatible-system clause above. The colimit of
-- this constant presheaf identifies with `M` because `Cᵒᵖ` is filtered, hence connected.
/-- Lemma 10.39.6 (1): if `R` is a cofiltered system of commutative rings, `A = colimit R`, and
an `A`-module is flat after restriction of scalars to every stage ring `R.obj U`, then it is flat
over `A`. -/
theorem flat_of_stagewise_restrictScalars_flat
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : ModuleCat.{u} (colimit R : CommRingCat))
    [∀ U, Module.Flat (R.obj U)
      ((ModuleCat.restrictScalars ((colimit.cocone R).ι.app U).hom).obj M)] :
    Module.Flat (colimit R : CommRingCat) M := by
  let N₀ :
      ModuleCat.{u} (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt :=
    ((ModuleCat.restrictScalars
        (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom).obj M)
  let N :
      ModuleCat.{u} (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt :=
    shrink_forget_colimit_module N₀
  let F :
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
    ((PresheafOfModules.constFunctor.{u}
        (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat))).obj N)
  letI : ∀ U, Module.Flat (R.obj U) (F.obj U) := fun U ↦ by
    -- Each stage of the constant system is the original restricted module up to the canonical
    -- shrink/transport isomorphism, so the given stagewise flatness hypothesis applies.
    exact Module.Flat.of_linearEquiv (restrictScalars_shrink_stage_iso R M U).toLinearEquiv
  have hflatF :
      Module.Flat (colimit R : CommRingCat)
        ((ModuleCat.restrictScalars
            (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
          ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj F)) :=
    flat_colimitFunctor_of_stagewise_flat R F
  let eConst :
      ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj F) ≅ N :=
    colimitFunctor_constFunctor_iso R N
  let eRestrict :
      ((ModuleCat.restrictScalars
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
        ((colimitFunctor.{u} (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj F)) ≅
        M :=
    ((ModuleCat.restrictScalars
        (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).mapIso eConst) ≪≫
      ((ModuleCat.restrictScalars
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).mapIso
        (shrink_forget_colimit_module_iso N₀)) ≪≫
      (ModuleCat.restrictScalarsComp'App
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).inv.hom
          (RingHom.id (colimit R : CommRingCat))
          (preservesColimitIso_inv_comp_hom_id R)
          M).symm ≪≫
        (ModuleCat.restrictScalarsId'App
          (RingHom.id (colimit R : CommRingCat))
          rfl
          M)
  -- Transport the flatness produced by clause `(2)` back along the canonical colimit
  -- identification for the constant system.
  exact (Module.Flat.equiv_iff eRestrict.toLinearEquiv).1 hflatF

end
