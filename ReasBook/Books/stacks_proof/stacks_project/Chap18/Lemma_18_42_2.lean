import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksProject_2024.Chap18.Lemma_18_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
open Finsupp

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/- Domain-style sampling:
- primary domain: constant sheaves of `Λ`-modules on a site, together with the comparison between
  tensoring before sheafification and tensoring sectionwise by a finitely presented module;
- sampled owner declarations:
  `constantSheaf`,
  `toSheafify`,
  `sheafifyLift`,
  `tensorRight`,
  `constantSheafToLocallyConstantSheaf_isIso`;
- best owner abstraction: the public owner is the canonical sheaf morphism
  `constantModuleTensorComparison`, built from `constantSheaf`, `toSheafify`, and
  `sheafifyLift` after applying `tensorRight Q`; the objectwise section map is derived API;
- primitive data: the constant presheaf with value `M`, the tensor functor `tensorRight Q`, and
  the finite-presentation hypothesis on `Q` needed to show the tensor-sections presheaf is a
  sheaf;
- derived API: the sheaf-level comparison morphism and its `IsIso` theorem, with the objectwise
  `app` statement as a thin companion.

Source/core/bridge triage:
- `source-facing`: `constantModuleTensorComparison`, `constantModuleTensorComparison_isIso`, and
  the companion `constantModuleTensorComparison_app_isIso`;
- `core/canonical`: `constantSheaf`, `toSheafify`, `sheafifyLift`, and `tensorRight`;
- `bridge/view`: the underlying constant-presheaf tensor comparison used internally to construct
  the sheaf morphism. -/

/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` obtained by tensoring the underlying
presheaf of the constant sheaf of `M` with the fixed module `Q`. -/
private abbrev constantModuleTensorSectionsPresheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    Cᵒᵖ ⥤ ModuleCat.{u} Λ :=
  ((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight Q

private abbrev constantModuleTensorComparisonNatTrans
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    ((Functor.const Cᵒᵖ).obj (M ⊗ Q)) ⟶
      constantModuleTensorSectionsPresheaf J M Q :=
  (Functor.constComp Cᵒᵖ M (tensorRight Q)).inv ≫
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (tensorRight Q)

/-- Helper for Lemma 18.42.2: a finitely presented module admits an exact presentation by finite
free modules. -/
private lemma finitely_presented_module_exists_free_presentation
    (Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    ∃ (m n : ℕ) (f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ))
      (g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q),
      Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin Λ Q
  obtain ⟨t, ht⟩ := hK
  let generators : t → (Fin n → Λ) := fun i ↦ i.1
  let ψ :
      (Fin t.card → Λ) ≃ₗ[Λ] t →₀ Λ :=
    (linearEquivFunOnFinite Λ Λ (Fin t.card)).symm ≪≫ₗ
      Finsupp.domLCongr t.equivFin.symm
  let φ :
      (Fin t.card → Λ) →ₗ[Λ] (Fin n → Λ) :=
    Finsupp.linearCombination Λ generators ∘ₗ ψ.toLinearMap
  have hφ_range :
      LinearMap.range (Finsupp.linearCombination Λ generators ∘ₗ ψ.toLinearMap) = K := by
    have hgenerators :
        LinearMap.range (Finsupp.linearCombination Λ generators) = K := by
      rw [range_linearCombination]
      simpa [generators, Subtype.range_coe_subtype] using ht
    rw [LinearMap.range_comp_of_range_eq_top _ ψ.range]
    exact hgenerators
  let gLinear : (Fin n → Λ) →ₗ[Λ] Q :=
    e.symm.toLinearMap.comp K.mkQ
  have hf_range : LinearMap.range φ = K := by
    -- The image of `φ` is exactly the chosen relation submodule `K`.
    exact hφ_range
  have hg_ker : LinearMap.ker gLinear = K := by
    -- The quotient map has kernel `K`, and the final equivalence does not change kernels.
    have heker : LinearMap.ker e.symm.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr e.symm.injective
    change LinearMap.ker (e.symm.toLinearMap.comp K.mkQ) = K
    rw [LinearMap.ker_comp, heker, Submodule.comap_bot, Submodule.ker_mkQ]
  have h_exact : Function.Exact φ gLinear := by
    rw [LinearMap.exact_iff, hf_range, hg_ker]
  have hg_surj : Function.Surjective gLinear := by
    exact e.symm.surjective.comp (Submodule.mkQ_surjective K)
  exact ⟨t.card, n, ModuleCat.ofHom φ, ModuleCat.ofHom gLinear, h_exact, hg_surj⟩

/-- Helper for Lemma 18.42.2: tensoring the finite free presentation by `M` preserves the right
exactness required by the textbook argument. -/
private lemma tensor_free_presentation_exact
    {Q : ModuleCat.{u} Λ} (M : ModuleCat.{u} Λ)
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Function.Exact (f.hom.lTensor M) (g.hom.lTensor M) ∧
      Function.Surjective (g.hom.lTensor M) := by
  constructor
  · -- This is the right exactness of tensor product on the left.
    exact lTensor_exact M hfg hg
  · -- Surjectivity is preserved objectwise after tensoring.
    exact LinearMap.lTensor_surjective M hg

/-- Helper for Lemma 18.42.2: an exact pair `A ⟶ B ⟶ Q` induces a surjection from `A` onto the
kernel of the second map by restricting the codomain to `ker g`. -/
private lemma cod_restrict_surjective_of_exact
    {A B Q : Type u}
    [AddCommGroup A] [Module Λ A]
    [AddCommGroup B] [Module Λ B]
    [AddCommGroup Q] [Module Λ Q]
    (f : A →ₗ[Λ] B) (g : B →ₗ[Λ] Q)
    (hfg : Function.Exact f g) :
    Function.Surjective
      (LinearMap.codRestrict (LinearMap.ker g) f <| by
        intro x
        simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero x) := by
  intro z
  have hz_range : (z : B) ∈ LinearMap.range f := by
    rw [← hfg.linearMap_ker_eq]
    exact z.2
  rcases hz_range with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- Helper for Lemma 18.42.2: evaluating the naturality square of
`constantCommuteCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)` identifies the underlying
abelian-group map of a module-valued constant-sheaf section map with the corresponding section map
after forgetting modules. -/
private lemma constant_module_forget_sections_naturality
    (J : GrothendieckTopology C) {A B : ModuleCat.{u} Λ} (u : A ⟶ B) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (x : (((constantSheaf J (ModuleCat.{u} Λ)).obj A).obj.obj (op U))) :
    let E := constantCommuteCompose J (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
    let eA := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app A)).app (op U)
    let eB := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app B)).app (op U)
    eB.hom ((((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) x) =
      (((constantSheaf J AddCommGrpCat.{u}).map
          ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).map u)).hom.app (op U))
        (eA.hom x) := by
  let E := constantCommuteCompose J (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
  let eA := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app B)).app (op U)
  -- Proof comment: evaluate the naturality square of `constantCommuteCompose` on the section
  -- over `U` and then read the result in `AddCommGrpCat`.
  have hnat :
      ((((constantSheaf J (ModuleCat.{u} Λ) ⋙
          sheafCompose J (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map u) ≫
          (E.hom.app B)).hom.app (op U)) =
        (((E.hom.app A) ≫
          (constantSheaf J AddCommGrpCat.{u}).map
            ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).map u)).hom.app (op U)) := by
    exact
      congrArg
        (fun α :
          ((constantSheaf J (ModuleCat.{u} Λ) ⋙
              sheafCompose J (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj A) ⟶
            ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u} ⋙
                constantSheaf J AddCommGrpCat.{u}).obj B) =>
          α.hom.app (op U))
        (E.hom.naturality u)
  simpa [E, eA, eB] using ConcreteCategory.congr_hom hnat x

/-- Helper for Lemma 18.42.2: a surjective module homomorphism induces a surjective map on
sections of the associated constant module sheaves. -/
private lemma constant_module_sheaf_app_surjective
    (J : GrothendieckTopology C) {A B : ModuleCat.{u} Λ} (u : A ⟶ B)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (hu : Function.Surjective u.hom) (U : C) :
    Function.Surjective (((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) := by
  classical
  let F := forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}
  let E := constantCommuteCompose J F
  let eA := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app B)).app (op U)
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk (0 : F.obj A ⟶ F.obj A) (F.map u) (by simp)
  let s : F.obj B → F.obj A := fun b ↦ Classical.choose (hu b)
  have hs : Function.RightInverse s u.hom := by
    intro b
    exact Classical.choose_spec (hu b)
  have hAddSurj :
      Function.Surjective
        ((((S.map (constantSheaf J AddCommGrpCat.{u})).map
            (sheafToPresheaf J AddCommGrpCat.{u})).map
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).g).hom := by
    -- Proof comment: the forgotten additive map is sectionwise surjective because a set-theoretic
    -- right inverse of `u` survives under the constant abelian-sheaf construction.
    simpa [S, F] using constant_abelian_sheaf_app_surjective (J := J) S s hs U
  intro y
  let y' := eB.hom y
  rcases hAddSurj y' with ⟨x', hx'⟩
  refine ⟨eA.inv x', ?_⟩
  have heB : Function.LeftInverse eB.inv eB.hom := by
    intro z
    exact ConcreteCategory.congr_hom eB.hom_inv_id z
  apply heB.injective
  -- Proof comment: the naturality square from `constantCommuteCompose` identifies the module map
  -- with the forgotten additive map, so the additive preimage lifts back through `eA.inv`.
  have himage :
      eB.hom ((((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) (eA.inv x')) = y' := by
    have hxA : eA.hom (eA.inv x') = x' := by
      exact ConcreteCategory.congr_hom eA.inv_hom_id x'
    have hstep1 :
        eB.hom ((((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) (eA.inv x')) =
          ((((S.map (constantSheaf J AddCommGrpCat.{u})).map
              (sheafToPresheaf J AddCommGrpCat.{u})).map
              ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).g).hom
            (eA.hom (eA.inv x')) := by
      simpa [S, F, E, eA, eB] using
        constant_module_forget_sections_naturality (J := J) u U (eA.inv x')
    have hstep2 :
        ((((S.map (constantSheaf J AddCommGrpCat.{u})).map
            (sheafToPresheaf J AddCommGrpCat.{u})).map
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).g).hom
          (eA.hom (eA.inv x')) =
          ((((S.map (constantSheaf J AddCommGrpCat.{u})).map
            (sheafToPresheaf J AddCommGrpCat.{u})).map
            ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).g).hom
          x' := by
      exact
        congrArg
          ((((S.map (constantSheaf J AddCommGrpCat.{u})).map
              (sheafToPresheaf J AddCommGrpCat.{u})).map
              ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).g).hom
          hxA
    exact hstep1.trans (hstep2.trans hx')
  simpa [y'] using himage

/-- Helper for Lemma 18.42.2: sectionwise exactness for a short exact sequence of constant module
sheaves is obtained by transporting the corresponding exact sequence of forgotten constant abelian
sheaves across the section isomorphisms from `constantCommuteCompose`. -/
private lemma constant_module_sheaf_app_exact_of_shortExact
    (J : GrothendieckTopology C) (S : ShortComplex (ModuleCat.{u} Λ)) (hS : S.ShortExact)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (U : C) :
    Function.Exact
      (((constantSheaf J (ModuleCat.{u} Λ)).map S.f).hom.app (op U))
      (((constantSheaf J (ModuleCat.{u} Λ)).map S.g).hom.app (op U)) := by
  let F := forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}
  let E := constantCommuteCompose J F
  let e₁Iso := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app S.X₁)).app (op U)
  let e₂Iso := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app S.X₂)).app (op U)
  let e₃Iso := ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (E.app S.X₃)).app (op U)
  let e₁ := CategoryTheory.Iso.addCommGroupIsoToAddEquiv e₁Iso
  let e₂ := CategoryTheory.Iso.addCommGroupIsoToAddEquiv e₂Iso
  let e₃ := CategoryTheory.Iso.addCommGroupIsoToAddEquiv e₃Iso
  let T : ShortComplex AddCommGrpCat.{u} :=
    (((S.map F).map (constantSheaf J AddCommGrpCat.{u})).map
      (sheafToPresheaf J AddCommGrpCat.{u})).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))
  have hForget : (S.map F).ShortExact := by
    -- Proof comment: the forgetful functor from modules to abelian groups preserves the short
    -- exact sequence carried by `S`.
    simpa [F] using hS.map_of_exact F
  have hExactAdd : Function.Exact T.f.hom T.g.hom := by
    -- Proof comment: after forgetting to abelian groups, the sectionwise constant-sheaf sequence
    -- is short exact by Lemma 18.42.1.
    exact
      (ShortComplex.ab_exact_iff_function_exact (S := T)).1
        (shortExact_constantAbelianSheaf_app (J := J) (S.map F) hForget U).exact
  have h₁₂ :
      AddMonoidHom.comp T.f.hom e₁.toAddMonoidHom =
        AddMonoidHom.comp e₂.toAddMonoidHom
          ((((constantSheaf J (ModuleCat.{u} Λ)).map S.f).hom.app (op U)).hom.toAddMonoidHom) := by
    ext x
    simpa [T, F, E, e₁, e₂, e₁Iso, e₂Iso] using
      (constant_module_forget_sections_naturality (J := J) S.f U x).symm
  have h₂₃ :
      AddMonoidHom.comp T.g.hom e₂.toAddMonoidHom =
        AddMonoidHom.comp e₃.toAddMonoidHom
          ((((constantSheaf J (ModuleCat.{u} Λ)).map S.g).hom.app (op U)).hom.toAddMonoidHom) := by
    ext x
    simpa [T, F, E, e₂, e₃, e₂Iso, e₃Iso] using
      (constant_module_forget_sections_naturality (J := J) S.g U x).symm
  -- Proof comment: transport exactness back across the section isomorphisms from
  -- `constantCommuteCompose`.
  simpa [e₁, e₂, e₃] using
    (Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
      (f₁₂ := (((constantSheaf J (ModuleCat.{u} Λ)).map S.f).hom.app (op U)).hom.toAddMonoidHom)
      (f₂₃ := (((constantSheaf J (ModuleCat.{u} Λ)).map S.g).hom.app (op U)).hom.toAddMonoidHom)
      (g₁₂ := T.f.hom) (g₂₃ := T.g.hom)
      (comm₁₂ := h₁₂) (comm₂₃ := h₂₃) hExactAdd)

/-- Helper for Lemma 18.42.2: after tensoring a finite free presentation by `M`, evaluating the
constant-sheaf sequence on `U` is still exact and surjective on the right. This is the source
proof's objectwise bridge from the tensor presentation to sections. -/
private lemma constant_module_tensor_app_exact_surjective
    (J : GrothendieckTopology C) (M : ModuleCat.{u} Λ)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {Q : ModuleCat.{u} Λ}
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) (U : C) :
    Function.Exact
      (((constantSheaf J (ModuleCat.{u} Λ)).map
          (ModuleCat.ofHom (f.hom.lTensor M))).hom.app (op U))
      (((constantSheaf J (ModuleCat.{u} Λ)).map
          (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U)) ∧
      Function.Surjective
        (((constantSheaf J (ModuleCat.{u} Λ)).map
            (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U)) := by
  let hTensor := tensor_free_presentation_exact (M := M) hfg hg
  let K : Submodule Λ (M ⊗[Λ] ModuleCat.of Λ (Fin n → Λ)) := LinearMap.ker (g.hom.lTensor M)
  let κ :
      M ⊗[Λ] ModuleCat.of Λ (Fin m → Λ) →ₗ[Λ] K :=
    LinearMap.codRestrict K (f.hom.lTensor M) <| by
      intro x
      simpa [K] using LinearMap.congr_fun hTensor.1.linearMap_comp_eq_zero x
  let Sker : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom (g.hom.lTensor M)) (by
      ext x
      exact x.2)
  let κApp :=
    (((constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom κ)).hom.app (op U)).hom
  let ιApp :=
    (((constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom K.subtype)).hom.app (op U)).hom
  let fApp :=
    (((constantSheaf J (ModuleCat.{u} Λ)).map
        (ModuleCat.ofHom (f.hom.lTensor M))).hom.app (op U)).hom
  let gApp :=
    (((constantSheaf J (ModuleCat.{u} Λ)).map
        (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U)).hom
  have hκSurj : Function.Surjective κ := by
    -- Proof comment: exactness of the tensored presentation identifies `range (f ⊗ M)` with
    -- `ker (g ⊗ M)`, so the cod-restricted map onto the kernel is surjective.
    exact cod_restrict_surjective_of_exact (f.hom.lTensor M) (g.hom.lTensor M) hTensor.1
  have hSker : Sker.ShortExact := by
    have hExactK : Function.Exact Sker.f Sker.g := by
      simpa [Sker, K] using (LinearMap.exact_subtype_ker_map (g.hom.lTensor M))
    -- Proof comment: `ker (g ⊗ M) ↪ M ⊗ Λ^n → M ⊗ Q` is the genuine short exact sequence
    -- behind the right-exact tensor presentation.
    exact ModuleCat.shortComplex_shortExact Sker hExactK (Submodule.injective_subtype K) hTensor.2
  have hExactInclusion : Function.Exact ιApp gApp := by
    simpa [ιApp, gApp, Sker] using
      constant_module_sheaf_app_exact_of_shortExact (J := J) Sker hSker U
  have hκAppSurj : Function.Surjective κApp := by
    simpa [κApp] using
      constant_module_sheaf_app_surjective (J := J) (ModuleCat.ofHom κ) hκSurj U
  have hgAppSurj : Function.Surjective gApp := by
    simpa [gApp] using
      constant_module_sheaf_app_surjective (J := J) (ModuleCat.ofHom (g.hom.lTensor M)) hTensor.2 U
  have hκ_comp :
      ModuleCat.ofHom κ ≫ ModuleCat.ofHom K.subtype =
        ModuleCat.ofHom (f.hom.lTensor M) := by
    refine ModuleCat.hom_ext ?_
    rfl
  have hfactor :
      ιApp.comp κApp = fApp := by
    have hmapComp :
        (constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom κ) ≫
            (constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom K.subtype) =
          (constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom (f.hom.lTensor M)) := by
      rw [← Functor.map_comp, hκ_comp]
    simpa [κApp, ιApp, fApp, LinearMap.comp_apply] using
      congrArg
        (fun α =>
          (α.hom.app (op U)).hom)
        hmapComp
  have hExactTensor : Function.Exact (ιApp.comp κApp) gApp := by
    -- Proof comment: surjectivity of `κApp` reduces exactness for `fApp` to exactness for the
    -- kernel inclusion map on sections.
    exact
      ((Function.Surjective.comp_exact_iff_exact
        (f := ιApp) (g := gApp) (p := κApp) hκAppSurj)).2 hExactInclusion
  exact ⟨by simpa [hfactor] using hExactTensor, by simpa [gApp] using hgAppSurj⟩

/-- Helper for Lemma 18.42.2: in `ModuleCat`, an exact and surjective presentation already
exhibits the right map as a cokernel. -/
private lemma moduleCat_cokernel_of_exact_surjective
    {A B Q : ModuleCat.{u} Λ} {f : A ⟶ B} {g : B ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Nonempty
      (IsColimit
        (CokernelCofork.ofπ g
          (by
            refine ModuleCat.hom_ext ?_
            exact hfg.linearMap_comp_eq_zero))) := by
  let K : Submodule Λ B := LinearMap.ker g.hom
  let S : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) g (by
      ext x
      exact x.2)
  -- Replace the original presentation by the canonical short exact sequence
  -- `ker g → B → Q`, whose cokernel owner is already built into `ShortComplex`.
  have hExactK : Function.Exact K.subtype g.hom := by
    simpa [K] using (LinearMap.exact_subtype_ker_map g.hom)
  have hS : S.ShortExact := by
    exact ModuleCat.shortComplex_shortExact S hExactK (Submodule.injective_subtype K) hg
  haveI : Epi g := (ModuleCat.epi_iff_surjective g).2 hg
  refine ⟨CokernelCofork.IsColimit.ofπ' g
    (by
      refine ModuleCat.hom_ext ?_
      exact hfg.linearMap_comp_eq_zero)
    (fun k hk ↦ ?_)⟩
  have hkK : ModuleCat.ofHom K.subtype ≫ k = 0 := by
    ext x
    obtain ⟨y, hy⟩ := (show (x : B) ∈ LinearMap.range f.hom by
      rw [← hfg.linearMap_ker_eq]
      exact x.2)
    have hkLinear : k.hom.comp f.hom = 0 := by
      simpa using ModuleCat.hom_ext_iff.mp hk
    simpa [hy] using
      LinearMap.congr_fun hkLinear y
  let hCoker : IsColimit (CokernelCofork.ofπ g S.zero) :=
    ShortComplex.ShortExact.gIsCokernel hS
  exact ⟨hCoker.desc (CokernelCofork.ofπ k hkK), hCoker.fac (CokernelCofork.ofπ k hkK)
    WalkingParallelPair.one⟩

/-- Helper for Chap18 Lemma 18 42 2: tensoring a finite free presentation with `M` already gives
the cokernel presentation of `M ⊗ Q` in `ModuleCat`. -/
private lemma tensor_free_presentation_comp_zero
    {Q : ModuleCat.{u} Λ} (M : ModuleCat.{u} Λ)
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    ModuleCat.ofHom (f.hom.lTensor M) ≫ ModuleCat.ofHom (g.hom.lTensor M) = 0 := by
  refine ModuleCat.hom_ext ?_
  exact (tensor_free_presentation_exact (M := M) hfg hg).1.linearMap_comp_eq_zero

/-- Helper for Chap18 Lemma 18 42 2: evaluating the tensor presentation on `U` kills the left map
against the right map. -/
private lemma constant_module_tensor_app_comp_zero
    (J : GrothendieckTopology C) (M : ModuleCat.{u} Λ)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {Q : ModuleCat.{u} Λ}
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom (f.hom.lTensor M))).hom.app (op U)) ≫
        (((constantSheaf J (ModuleCat.{u} Λ)).map (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U)) =
      0 := by
  refine ModuleCat.hom_ext ?_
  exact
    (constant_module_tensor_app_exact_surjective (J := J) (M := M) hfg hg U).1.linearMap_comp_eq_zero

/-- Helper for Chap18 Lemma 18 42 2: tensoring a finite free presentation with `M` already gives
the cokernel presentation of `M ⊗ Q` in `ModuleCat`. -/
private lemma tensor_free_presentation_isColimit
    {Q : ModuleCat.{u} Λ} (M : ModuleCat.{u} Λ)
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Nonempty
      (IsColimit
        (CokernelCofork.ofπ
          (ModuleCat.ofHom (g.hom.lTensor M))
          (tensor_free_presentation_comp_zero (M := M) hfg hg))) := by
  let hTensor := tensor_free_presentation_exact (M := M) hfg hg
  -- Proof comment: once the tensor presentation is exact and surjective in `ModuleCat`, the
  -- standard cokernel criterion upgrades it to the required colimit presentation.
  simpa using
    (moduleCat_cokernel_of_exact_surjective
      (f := ModuleCat.ofHom (f.hom.lTensor M))
      (g := ModuleCat.ofHom (g.hom.lTensor M))
      hTensor.1 hTensor.2)

/-- Helper for Chap18 Lemma 18 42 2: after evaluating on `U`, the tensor presentation still gives
the cokernel presentation of `\underline M(U) ⊗_\Lambda Q`. -/
private lemma constant_module_tensor_app_isColimit
    (J : GrothendieckTopology C) (M : ModuleCat.{u} Λ)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {Q : ModuleCat.{u} Λ}
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) (U : C) :
    Nonempty
      (IsColimit
        (CokernelCofork.ofπ
          (((constantSheaf J (ModuleCat.{u} Λ)).map
              (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U))
          (constant_module_tensor_app_comp_zero (J := J) (M := M) hfg hg U))) := by
  let hApp := constant_module_tensor_app_exact_surjective (J := J) (M := M) hfg hg U
  -- Proof comment: the evaluated tensor presentation is a short exact right-exact pair in
  -- `ModuleCat`, so the same cokernel criterion applies objectwise on sections.
  simpa using
    (moduleCat_cokernel_of_exact_surjective
      (f := ((constantSheaf J (ModuleCat.{u} Λ)).map
        (ModuleCat.ofHom (f.hom.lTensor M))).hom.app (op U))
      (g := ((constantSheaf J (ModuleCat.{u} Λ)).map
        (ModuleCat.ofHom (g.hom.lTensor M))).hom.app (op U))
      hApp.1 hApp.2)

-- Proof sketch: choose a finite presentation of `Q`, tensor the resulting right exact sequence
-- with the constant sheaf of `M`, and use exactness of the constant abelian-sheaf functor together
-- with preservation of finite direct sums by evaluation on `U` to identify the resulting cokernel
-- presheaf with `U ↦ \underline{M}(U) \otimes_\Lambda Q`.
/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` is a sheaf when `Q` is finitely
presented. -/
theorem constantModuleTensorSectionsPresheaf_isSheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    Presheaf.IsSheaf J (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight Q) := by
  -- Route correction: the presheaf-side cokernel is now available directly from the finite free
  -- presentation objectwise. The remaining work is to assemble these objectwise cokernels into a
  -- presheaf cokernel and then compare that presheaf with `((constantSheaf J _).obj (M ⊗ Q)).obj`
  -- via the finite-free rewrite on the constant-sheaf side.
  -- TODO: package the objectwise cokernel witnesses from
  -- `moduleCat_cokernel_of_exact_surjective` into a presheaf-level cokernel, then identify the
  -- constant-sheaf side with the same cokernel.
  sorry

/-- The canonical comparison morphism from the constant sheaf of `M ⊗_\Lambda Q` to the sheaf
`U ↦ \underline{M}(U) \otimes_\Lambda Q`. -/
def constantModuleTensorComparison
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    (constantSheaf J (ModuleCat.{u} Λ)).obj (M ⊗ Q) ⟶
      ⟨((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight Q,
        constantModuleTensorSectionsPresheaf_isSheaf J M Q⟩ :=
  ObjectProperty.homMk <|
    sheafifyLift J
      (constantModuleTensorComparisonNatTrans J M Q)
      (constantModuleTensorSectionsPresheaf_isSheaf J M Q)

-- Proof sketch: the previous theorem makes `U ↦ \underline{M}(U) \otimes_\Lambda Q` into a sheaf,
-- so the canonical map from the constant presheaf with value `M ⊗ Q` factors uniquely through its
-- sheafification `\underline{M \otimes_\Lambda Q}`. The finite-presentation argument shows that
-- this canonical comparison is already an isomorphism of sheaves, so evaluating at `U` gives the
-- textbook sectionwise statement.
/-- Lemma 18.42.2 companion: if `Q` is a finitely presented `\Lambda`-module, then the canonical
comparison morphism
`\underline{M \otimes_\Lambda Q} \to (U ↦ \underline{M}(U) \otimes_\Lambda Q)` is an
isomorphism of sheaves. -/
@[stacks 093K]
theorem constantModuleTensorComparison_isIso
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    IsIso (constantModuleTensorComparison J M Q) := by
  -- TODO: Once the presheaf-level cokernel comparison is constructed, identify this morphism with
  -- that comparison via `toSheafify_sheafifyLift` and conclude by `NatIso.isIso_of_isIso_app`.
  sorry

/-- Lemma 18.42.2: if `Q` is a finitely presented `\Lambda`-module, then for every `U : C` the
induced map on sections of the canonical comparison
`\underline{M \otimes_\Lambda Q}(U) \to \underline{M}(U) \otimes_\Lambda Q` is an isomorphism. -/
@[stacks 093K]
theorem constantModuleTensorComparison_app_isIso
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q]
    (U : C) :
    IsIso ((constantModuleTensorComparison J M Q).hom.app (op U)) := by
  letI := constantModuleTensorComparison_isIso J M Q
  letI :
      IsIso
        ((sheafToPresheaf J (ModuleCat.{u} Λ)).map
          (constantModuleTensorComparison J M Q)) :=
    Functor.map_isIso _ (constantModuleTensorComparison J M Q)
  simpa using
    (show IsIso
      ((((sheafToPresheaf J (ModuleCat.{u} Λ)).map
          (constantModuleTensorComparison J M Q)).app (op U))) by
      infer_instance)

end CategoryTheory
