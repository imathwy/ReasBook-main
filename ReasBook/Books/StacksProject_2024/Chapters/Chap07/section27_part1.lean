import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_27_1 (from Chap07) -/
open CategoryTheory Opposite

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [J.Subcanonical] (U : C)
variable (G : Sheaf (J.over U) (Type (max u v)))

/- Domain-style sampling for Lemma 7.27.1:
- primary domain: localization lower shriek on sheaves and its presheaf-level left-Kan-extension
  formula;
- sampled owner API:
  `(Over.forget U).sheafPullback`,
  `localization_lowerShriek_associatedSheafIso`,
  `localization_leftKanExtension_objIsoSigma`,
  `sheafificationIso`;
- source-facing layer: the Stacks Project identification of `j_{U!}(G)` with the presheaf
  `V ↦ ∐_{φ : V ⟶ U} G(V \xrightarrow{φ} U)`;
- core/canonical owner: the sheaf functor `(Over.forget U).sheafPullback (Type (max u v))
  (J.over U) J` and the presheaf functor `(Over.forget U).op.lan`;
- bridge/view: `localization_lowerShriek_associatedSheafIso` identifies `j_{U!}` with the
  sheafification of the left Kan extension, and subcanonicality upgrades that sheafification to the
  presheaf itself.

Primitive data are the site `J`, the localization object `U`, the sheaf `G`, and the standard
sheafification/Kan-extension hypotheses. The sheafified left Kan extension is derived API of the
canonical owners, so no separate wrapper sheaf is kept in the public surface.
-/

namespace LocalizationLeftKanExtension

/-- Helper for Lemma 7.27.1: the discrete inclusion of the terminal objects in the indexing
category for the objectwise left-Kan-extension formula. -/
private abbrev indexFunctor
    (U V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- Helper for Lemma 7.27.1: the over-object attached to a costructured arrow over `op V`. -/
private abbrev overObj
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- Helper for Lemma 7.27.1: the leg `V ⟶ A` in the triangle underlying a costructured arrow. -/
private abbrev leg
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (overObj X).left :=
  X.hom.unop

/-- Helper for Lemma 7.27.1: the composite `V ⟶ U` represented by a costructured arrow. -/
private abbrev composite
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  leg X ≫ (overObj X).hom

/-- Helper for Lemma 7.27.1: the discrete index attached to a costructured arrow. -/
private abbrev index
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (composite X)

/-- Helper for Lemma 7.27.1: the canonical map from any indexing object to the terminal object of
its fibre. -/
private abbrev terminalHom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (indexFunctor U V).obj (index X) :=
  CostructuredArrow.homMk
    ((show Over.mk (composite X) ⟶ overObj X from Over.homMk (leg X)).op)
    (by
      simp [indexFunctor, index, leg])

/-- Helper for Lemma 7.27.1: any morphism into `indexFunctor U V` preserves the composite
`V ⟶ U`. -/
private lemma composite_eq_of_map
    (U V : C) {X Y : CostructuredArrow (Over.forget U).op (op V)} (hom : X ⟶ Y) :
    composite X = composite Y := by
  let triangle : overObj Y ⟶ overObj X := hom.left.unop
  have hleg : leg Y ≫ triangle.left = leg X := by
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
    simpa [triangle] using h
  have hw : triangle.left ≫ (overObj X).hom = (overObj Y).hom := Over.w triangle
  dsimp [composite]
  calc
    leg X ≫ (overObj X).hom = (leg Y ≫ triangle.left) ≫ (overObj X).hom := by
      rw [hleg]
    _ = leg Y ≫ (triangle.left ≫ (overObj X).hom) := by rw [Category.assoc]
    _ = leg Y ≫ (overObj Y).hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ leg Y ≫ k) hw

/-- Helper for Lemma 7.27.1: any morphism into the chosen terminal object is indexed by the
composite of the source triangle. -/
private lemma composite_eq_of_hom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U} (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    composite X = φ := by
  simpa [indexFunctor, composite, leg, overObj] using composite_eq_of_map U V hom

/-- Helper for Lemma 7.27.1: the canonical morphism into the indexing object selected by a fixed
composite `φ`. -/
private def homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ) :
    X ⟶ (indexFunctor U V).obj (Discrete.mk φ) := by
  cases hφ
  exact terminalHom U V

/-- Helper for Lemma 7.27.1: maps into the terminal object of a fibre are unique. -/
private lemma hom_eq_terminalHom
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (hom : X ⟶ (indexFunctor U V).obj (index X)) :
    hom = terminalHom U V := by
  ext
  exact by
    apply Quiver.Hom.unop_inj
    apply CommaMorphism.ext
    · have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
      simpa [indexFunctor] using h
    · simp [Over.homMk]

/-- Helper for Lemma 7.27.1: the canonical map into a chosen index is unique. -/
private lemma hom_eq_homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ)
    (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    hom = homToIndex U V X φ hφ := by
  cases hφ
  simpa [homToIndex] using hom_eq_terminalHom U V X hom

/-- Helper for Lemma 7.27.1: forget a costructured arrow down to its composite map `V ⟶ U`. -/
private abbrev compositeFunctor
    (U V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (composite X)
  map hom := Discrete.eqToHom (composite_eq_of_map U V hom)

/-- Helper for Lemma 7.27.1: the discrete inclusion is right adjoint to the composite functor. -/
private def compositeIndexAdjunction (U V : C) :
    compositeFunctor U V ⊣ indexFunctor U V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := by
        intro X φ
        cases φ with
        | mk ψ =>
            refine
              { toFun := fun hom ↦ homToIndex U V X ψ (Discrete.eq_of_hom hom)
                invFun := fun hom ↦ Discrete.eqToHom (composite_eq_of_hom U V hom)
                left_inv := ?_
                right_inv := ?_ }
            · intro hom
              apply Subsingleton.elim
            · intro hom
              simpa using
                (hom_eq_homToIndex U V X ψ (composite_eq_of_hom U V hom) hom).symm
      homEquiv_naturality_left_symm := by
        intro X' X φ hom k
        apply Subsingleton.elim
      homEquiv_naturality_right := by
        intro X Y Y' hom g
        cases Y with
        | mk ψ =>
            cases Y' with
            | mk ψ' =>
                have h :=
                  (hom_eq_homToIndex U V X ψ'
                    (by simpa using Discrete.eq_of_hom (hom ≫ g))
                    (homToIndex U V X ψ (Discrete.eq_of_hom hom) ≫
                      (indexFunctor U V).map g)).symm
                simpa [homToIndex] using congrArg CommaMorphism.left h }

/-- Helper for Lemma 7.27.1: the discrete family of chosen terminal objects is final. -/
private theorem indexFunctor_final (U V : C) : Functor.Final (indexFunctor U V) := by
  let _ : (indexFunctor U V).IsRightAdjoint :=
    ⟨⟨compositeFunctor U V, ⟨compositeIndexAdjunction U V⟩⟩⟩
  infer_instance

/-- Helper for Lemma 7.27.1: the restricted indexing diagram is literally
`φ ↦ G(V \xrightarrow{φ} U)`. -/
private abbrev indexFunctorProjIso
    (U : C) (F : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    indexFunctor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ F ≅
      Discrete.functor (fun φ : V ⟶ U ↦ F.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

end LocalizationLeftKanExtension

/-- Helper for Lemma 7.27.1: the sigma-model for the left Kan extension sends the canonical
generator from `leftKanExtensionUnit` to the corresponding summand. -/
private theorem localization_leftKanExtension_objIsoSigma_hom_unit_app
    {V : C} (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma U G.obj V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s) =
      ⟨a, s⟩ := by
  -- Expand the sigma comparison into the standard colimit presentation and evaluate each stage on
  -- the generator coming from `leftKanExtensionUnit`.
  let F₁ := LocalizationLeftKanExtension.indexFunctor U V
  let F₂ :=
    CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G.obj
  let F₃ :=
    Discrete.functor (fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ)))
  letI : Functor.Final F₁ := LocalizationLeftKanExtension.indexFunctor_final U V
  have h₀ :=
    congrFun
      (Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
        (L := (Over.forget U).op) (F := G.obj) (X := op (Over.mk a)))
      s
  have h₁ :=
    congrFun
      (Functor.Final.ι_colimitIso_inv
        (F := F₁) (G := F₂) (X := Discrete.mk a))
      s
  have h₂ :=
    congrFun
      (CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom
        (w := LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)
        (j := Discrete.mk a))
      s
  have h₃ :=
    congrFun
      (CategoryTheory.Limits.Types.coproductIso_ι_comp_hom
        (F := fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))) a)
      s
  calc
    (localization_leftKanExtension_objIsoSigma U G.obj V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s)
        =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (((Over.forget U).op.leftKanExtensionObjIsoColimit G.obj (op V)).hom
                  ((((Over.forget U).op.leftKanExtensionUnit G.obj).app
                    (op (Over.mk a))) s)))) := by
      rfl
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (CategoryTheory.Limits.colimit.ι F₂ (F₁.obj (Discrete.mk a)) s))) := by
      simpa [F₁, LocalizationLeftKanExtension.indexFunctor] using congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom ∘
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom ∘
            (Functor.Final.colimitIso F₁ F₂).inv) h₀
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              (CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s)) := by
      have h₁' :
          ((Functor.Final.colimitIso F₁ F₂).inv
              (CategoryTheory.Limits.colimit.ι F₂ (F₁.obj (Discrete.mk a)) s)) =
            CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s := by
        simpa [F₁, F₂, LocalizationLeftKanExtension.indexFunctor] using h₁
      exact congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom ∘
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom) h₁'
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            (CategoryTheory.Limits.colimit.ι F₃ (Discrete.mk a) s) := by
      have h₂' :
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
              (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              (CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s) =
            CategoryTheory.Limits.colimit.ι F₃ (Discrete.mk a) s := by
        simpa [F₁, F₂, F₃, LocalizationLeftKanExtension.indexFunctorProjIso] using h₂
      exact congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom) h₂'
    _ = ⟨a, s⟩ := by
      simpa [F₃] using h₃

/-- Helper for Lemma 7.27.1: the inverse sigma comparison sends a chosen summand back to the
canonical generator of the left Kan extension. -/
private theorem localization_leftKanExtension_objIsoSigma_inv_mk
    {V : C} (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s := by
  -- Apply the sigma chart and cancel it against the generator formula proved just above.
  apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
  simp [localization_leftKanExtension_objIsoSigma_hom_unit_app]

/-- Helper for Lemma 7.27.1: in sigma coordinates, restriction along `f : Y ⟶ V` sends the
summand indexed by `a : V ⟶ U` to the summand indexed by `f ≫ a`. -/
private theorem localization_leftKanExtension_objIsoSigma_hom_map
    {V Y : C} (f : Y ⟶ V)
    (x : (((Over.forget U).op.lan.obj G.obj).obj (op V))) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
        (((Over.forget U).op.lan.obj G.obj).map f.op x) =
      ⟨f ≫ ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).1,
        G.obj.map
          (show Over.mk (f ≫ ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).1) ⟶
              Over.mk ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).1 from
            Over.homMk f).op
          ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).2⟩ := by
  -- Write `x` as the inverse image of its sigma coordinates, then use naturality of
  -- `leftKanExtensionUnit` along the canonical map `Over.mk (f ≫ a) ⟶ Over.mk a`.
  rcases hV : (localization_leftKanExtension_objIsoSigma U G.obj V).hom x with ⟨a, s⟩
  rw [← hV]
  have hx :
      x = (localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨a, s⟩ := by
    apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
    simp [hV]
  rw [hx]
  rw [localization_leftKanExtension_objIsoSigma_inv_mk (J := J) (U := U) (G := G) a s]
  let g : Over.mk (f ≫ a) ⟶ Over.mk a := Over.homMk f
  have hnat :=
    congrFun (((Over.forget U).op.leftKanExtensionUnit G.obj).naturality g.op) s
  dsimp at hnat
  have hnat' :
      (((Over.forget U).op.lan.obj G.obj).map f.op
          ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s)) =
        (((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk (f ≫ a))))
          (G.obj.map g.op s) := by
    simpa [g] using hnat.symm
  rw [hnat']
  rw [localization_leftKanExtension_objIsoSigma_hom_unit_app (J := J) (U := U) (G := G) a s]
  simpa using
    localization_leftKanExtension_objIsoSigma_hom_unit_app (J := J) (U := U) (G := G) (f ≫ a)
      (G.obj.map g.op s)

/-- Helper for Lemma 7.27.1: the raw representable presheaf `h_U`, raised to the ambient `Type`
universe used by the sigma model. -/
private abbrev representable_presheaf : Cᵒᵖ ⥤ Type (max u v) :=
  ((CategoryTheory.uliftYoneda.{max u v}.obj U) : Cᵒᵖ ⥤ Type (max u v))

/-- Helper for Lemma 7.27.1: after gluing the first coordinates to `φ`, the local sigma first
coordinate over an arrow in the induced over-sieve equals the structural map of the source
over-object. -/
private theorem localization_leftKanExtension_first_component_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1 = Y.hom := by
  -- Compare the glued first coordinate with the defining triangle of `f`.
  exact (hφ f.left ((Sieve.overEquiv_symm_iff S f).1 hf)).symm.trans (Over.w f)

/-- Helper for Lemma 7.27.1: the sigma fibre indexed by the first coordinate is the given over
object. -/
private theorem localization_leftKanExtension_overObj_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    Over.mk
        (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1) = Y := by
  -- The first-coordinate gluing identifies the sigma summand with the source over-object.
  cases Y with
  | mk leftY rightY homY =>
      cases rightY
      simpa using congrArg Over.mk
        (localization_leftKanExtension_first_component_eq
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))

/-- Helper for Lemma 7.27.1: transport along an equality of arrows `V ⟶ U` identifies the
corresponding sigma fibres in `G`. -/
private theorem localization_leftKanExtension_sigma_type_eq
    {V : C} {a b : V ⟶ U} (h : a = b) :
    G.obj.obj (op (Over.mk a)) = G.obj.obj (op (Over.mk b)) := by
  cases h
  rfl

/-- Helper for Lemma 7.27.1: the transported sigma second coordinate can be viewed as a section of
`G` on the source over-object. -/
private theorem localization_leftKanExtension_second_coordinate_type_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    G.obj.obj
        (op
          (Over.mk
            (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1))) =
      G.obj.obj (op Y) := by
  cases Y with
  | mk leftY rightY homY =>
      cases rightY
      simpa using localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G)
        (localization_leftKanExtension_first_component_eq
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))

/-- Helper for Lemma 7.27.1: after gluing the first coordinates to `φ`, each local section yields
the corresponding second coordinate in `G` on the induced over-sieve. -/
private def localization_leftKanExtension_second_coordinate
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    G.obj.obj (op Y) :=
  cast
    (localization_leftKanExtension_second_coordinate_type_eq
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
    (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
      (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2)

/-- Helper for Lemma 7.27.1: the canonical map `Over.mk (f ≫ φ) ⟶ Over.mk φ` in the localized
site. -/
private abbrev localization_leftKanExtension_over_homMk
    {V Y : C} {φ : V ⟶ U} (f : Y ⟶ V) :
    Over.mk (f ≫ φ) ⟶ Over.mk φ :=
  Over.homMk f

/-- Helper for Lemma 7.27.1: the direct second-coordinate assignment, packaged as a family on the
induced over-sieve. -/
private def localization_leftKanExtension_second_coordinate_family
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1) :
    ((Sieve.overEquiv (Over.mk φ)).symm S).arrows.FamilyOfElements G.obj :=
  fun _ f hf ↦
    localization_leftKanExtension_second_coordinate
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)

/-- Helper for Lemma 7.27.1: the canonical over-arrow attached to `f : Y ⟶ V` lies in the induced
over-sieve. -/
private theorem localization_leftKanExtension_over_homMk_mem
    {V : C} {S : Sieve V} {φ : V ⟶ U}
    {Y : C} (f : Y ⟶ V) (hf : S f) :
    ((Sieve.overEquiv (Over.mk φ)).symm S)
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f) := by
  simpa [localization_leftKanExtension_over_homMk] using
    (Sieve.overEquiv_symm_iff S
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).2 hf

/-- Helper for Lemma 7.27.1: in sigma coordinates, the local section `x f hf` is described by the
glued first coordinate `f ≫ φ` and the direct second coordinate on the canonical over-arrow. -/
private theorem localization_leftKanExtension_hom_eq_homMk
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : C} (f : Y ⟶ V) (hf : S f) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) =
      ⟨f ≫ φ,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (φ := φ) f hf)⟩ := by
  -- Compare the sigma pair by first isolating the proof-irrelevant membership argument on the
  -- canonical over-arrow.
  let hf' : ((Sieve.overEquiv (Over.mk φ)).symm S).arrows
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f) :=
    localization_leftKanExtension_over_homMk_mem (U := U) (φ := φ) f hf
  have hpf :
      (Sieve.overEquiv_symm_iff S
          (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf' = hf := by
    apply Subsingleton.elim
  -- Then rewrite the local section into explicit sigma coordinates and compare second components by
  -- `Sigma.mk.inj_iff`, finishing with the canonical cast/HEq bridge.
  rcases hsig : (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) with ⟨a, s⟩
  have ha : a = f ≫ φ := by
    simpa [hsig] using (hφ f hf).symm
  apply (Sigma.mk.inj_iff).2
  refine ⟨ha, ?_⟩
  cases ha
  have hsig' :
      (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
          (x (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).left
            ((Sieve.overEquiv_symm_iff S
              (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf')) =
        ⟨f ≫ φ, s⟩ := by
    simpa [localization_leftKanExtension_over_homMk, hpf] using hsig
  dsimp [localization_leftKanExtension_second_coordinate]
  let p := localization_leftKanExtension_second_coordinate_type_eq
    (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
    (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
    (hf := hf')
  let z := ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom
    (x (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).left
      ((Sieve.overEquiv_symm_iff S
        (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf'))).2
  have hsnd : s ≍ z := ((Sigma.mk.inj_iff).1 hsig').2.symm
  exact HEq.trans hsnd (HEq.symm (cast_heq p z))

/-- Helper for Lemma 7.27.1: every over-arrow is equal to the canonical `homMk` built from its
underlying map. -/
private theorem localization_leftKanExtension_over_homMk_eq
    {Y Z : Over U} (g : Z ⟶ Y) (w : g.left ≫ Y.hom = Z.hom) :
    Over.homMk g.left w = g := by
  -- Morphisms in `Over U` are determined by their underlying maps, so the proof field is
  -- irrelevant here.
  apply CommaMorphism.ext
  · rfl
  · rfl

/-- Helper for Lemma 7.27.1: every object of `Over U` is definitionally the canonical object built
from its structure map. -/
private theorem localization_leftKanExtension_over_mk_hom_eq
    (Y : Over U) : Over.mk Y.hom = Y := by
  cases Y
  rfl

/-- Helper for Lemma 7.27.1: the canonical `homMk` restriction factors through the source-object
equality coming from `Over.w`. -/
private theorem localization_leftKanExtension_over_homMk_eqToHom_comp
    {Y Z : Over U} (g : Z ⟶ Y) :
    localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left =
      eqToHom ((congrArg Over.mk (Over.w g)).trans
        (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)) ≫ g := by
  -- Morphisms in `Over U` are determined by their underlying arrows, so the factorization is
  -- proved by identifying the right-hand side with the canonical `homMk` for its underlying map.
  simpa [localization_leftKanExtension_over_homMk] using
    (localization_leftKanExtension_over_homMk_eq (U := U)
      (g := eqToHom ((congrArg Over.mk (Over.w g)).trans
        (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)) ≫ g)
      (w := by simp))

/-- Helper for Lemma 7.27.1: mapping an `eqToHom` in `Over U` through the `Type`-valued sheaf is
the same as transporting along the induced equality of fibres. -/
private theorem localization_leftKanExtension_map_eqToHom_op_cast
    {A B : Over U} (h : A = B) (x : G.obj.obj (op B)) :
    cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) h)
      (G.obj.map (eqToHom h).op x) = x := by
  -- After reducing to the reflexive equality, the map is the identity and the cast disappears.
  cases h
  simp

/-- Helper for Lemma 7.27.1: the sigma coordinates of a local section over an arbitrary arrow in
the induced over-sieve are given by the structural map of the source over-object and the direct
second coordinate. -/
private theorem localization_leftKanExtension_hom_eq_over
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) =
      ⟨Y.hom,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)⟩ := by
  -- Compare the sigma pair by matching first coordinates, then identify the second coordinate by
  -- the transport already built into `localization_leftKanExtension_second_coordinate`.
  rcases hsig :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) with ⟨a, s⟩
  have ha : a = Y.hom := by
    simpa [hsig] using
      localization_leftKanExtension_first_component_eq
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
  cases ha
  apply (Sigma.mk.inj_iff).2
  refine ⟨rfl, ?_⟩
  have hsig' :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) = ⟨Y.hom, s⟩ := by
    simpa using hsig
  dsimp [localization_leftKanExtension_second_coordinate]
  let z := ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
    (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2
  have hsnd : z ≍ s := ((Sigma.mk.inj_iff).1 hsig').2
  exact HEq.trans (HEq.symm hsnd) (HEq.symm <|
    cast_heq
      (localization_leftKanExtension_second_coordinate_type_eq
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
      z)

/-- Helper for Lemma 7.27.1: transporting the sigma-second-coordinate restriction along `Over.w`
identifies the canonical `homMk` restriction with the actual restriction map in `Over U`. -/
private theorem localization_leftKanExtension_second_coordinate_transport_over_w
    {Y Z : Over U} (g : Z ⟶ Y) (s : G.obj.obj (op Y)) :
    cast
      (by
        simpa [localization_leftKanExtension_over_mk_hom_eq] using
          localization_leftKanExtension_sigma_type_eq
            (J := J) (U := U) (G := G) (Over.w g))
      (G.obj.map
        (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op s) =
      G.obj.map g.op s := by
  -- Route correction: factor the canonical `homMk` through the source-object equality, then
  -- collapse the induced `eqToHom` action on the `Type`-valued presheaf to an ordinary cast.
  let hZ : Over.mk (g.left ≫ Y.hom) = Z :=
    (congrArg Over.mk (Over.w g)).trans
      (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)
  change cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
      (G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op s) =
    G.obj.map g.op s
  rw [localization_leftKanExtension_over_homMk_eqToHom_comp (U := U) g]
  calc
    cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
        (G.obj.map (eqToHom hZ ≫ g).op s) =
      cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
        (G.obj.map (eqToHom hZ).op (G.obj.map g.op s)) := by
          -- Rewrite the `Type`-valued functor on the opposite composite into successive maps.
          congr 1
          exact FunctorToTypes.map_comp_apply G.obj g.op (eqToHom hZ).op s
    _ = G.obj.map g.op s := by
      -- The `eqToHom` factor on the source object is exactly the transport cast on the fibre.
      have hcast :
          cast (congrArg (fun T : Over U ↦ G.obj.obj (op T))
              ((congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)))
            (G.obj.map
              (eqToHom
                ((congrArg Over.mk (Over.w g)).trans
                  (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))).op
              (G.obj.map g.op s)) =
            G.obj.map g.op s := by
        exact
          (show cast (congrArg (fun T : Over U ↦ G.obj.obj (op T))
              ((congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)))
              (G.obj.map
                (eqToHom ((congrArg Over.mk (Over.w g)).trans
                  (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))).op
                (G.obj.map g.op s)) =
              G.obj.map g.op s from
            localization_leftKanExtension_map_eqToHom_op_cast
              (J := J) (U := U) (G := G)
              (h := (congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))
              (x := G.obj.map g.op s))
      simpa [hZ] using hcast

/-- Helper for Lemma 7.27.1: the direct second-coordinate family is compatible on the induced
over-sieve. -/
private theorem localization_leftKanExtension_second_coordinate_map
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    (hx : x.Compatible) {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y Z : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) (g : Z ⟶ Y) :
    G.obj.map g.op
        (localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)) =
      localization_leftKanExtension_second_coordinate
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
        (f := g ≫ f)
        (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) := by
  -- Compare the compatible family in sigma coordinates and then transport the second coordinate
  -- across the equality `Over.w g : g.left ≫ Y.hom = Z.hom`.
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  have hpair :=
    congrArg
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
      (hx f.left g.left ((Sieve.overEquiv_symm_iff S f).1 hf))
  have hleft :
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (x (g ≫ f).left
            ((Sieve.overEquiv_symm_iff S (g ≫ f)).1
              (((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g))) =
        ⟨Z.hom,
          localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
            (f := g ≫ f)
            (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g)⟩ := by
    -- The restricted section on `g ≫ f` is already in the normalized sigma form.
    simpa using
      localization_leftKanExtension_hom_eq_over
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
        (f := g ≫ f)
        (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g)
  have hright :
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (((Over.forget U).op.lan.obj G.obj).map g.left.op
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))) =
        ⟨g.left ≫ Y.hom,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))⟩ := by
    -- Rewrite the source sigma coordinates first, then use the restriction formula for the chart.
    calc
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (((Over.forget U).op.lan.obj G.obj).map g.left.op
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))) =
        ⟨g.left ≫
            ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1,
          G.obj.map
            (localization_leftKanExtension_over_homMk
              (U := U)
              (φ := ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
                (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1)
              g.left).op
            ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2⟩ := by
        simpa [localization_leftKanExtension_over_homMk] using
          localization_leftKanExtension_objIsoSigma_hom_map
            (J := J) (U := U) (G := G) g.left
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
      _ = ⟨g.left ≫ Y.hom,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))⟩ := by
        let restrictSigma :
            (Σ a : Y.left ⟶ U, G.obj.obj (op (Over.mk a))) →
              Σ b : Z.left ⟶ U, G.obj.obj (op (Over.mk b)) :=
          fun p ↦
            ⟨g.left ≫ p.1,
              G.obj.map
                (localization_leftKanExtension_over_homMk (U := U) (φ := p.1) g.left).op p.2⟩
        have hsource :=
          localization_leftKanExtension_hom_eq_over
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
        simpa [restrictSigma] using congrArg restrictSigma hsource
  have hcompare := hleft.symm.trans (hpair.trans hright)
  let p :
      G.obj.obj (op (Over.mk (g.left ≫ Y.hom))) = G.obj.obj (op Z) := by
    simpa [localization_leftKanExtension_over_mk_hom_eq] using
      localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G) (Over.w g)
  have hsnd :
      localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := g ≫ f)
          (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) =
        cast p
          (G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))) := by
    -- `Sigma.mk.inj_iff` gives an `HEq`; casting puts both sides into the fibre over `Z`.
    exact eq_of_heq <|
      HEq.trans ((Sigma.mk.inj_iff).1 hcompare).2 (HEq.symm (cast_heq p _))
  have hsnd' :
      localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := g ≫ f)
          (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) =
        G.obj.map g.op
          (localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)) := by
    simpa [p] using hsnd.trans <|
      localization_leftKanExtension_second_coordinate_transport_over_w
        (J := J) (U := U) (G := G) g
        (localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
  exact hsnd'.symm

/-- Helper for Lemma 7.27.1: the direct second-coordinate family on the induced over-sieve is
compatible. -/
private theorem localization_leftKanExtension_second_coordinate_compatible
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    (hx : x.Compatible) {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1) :
    (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).Compatible := by
  -- Compatibility is exactly the restriction formula proved for the direct second coordinates.
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  simpa using (localization_leftKanExtension_second_coordinate_map
    (J := J) (U := U) (G := G) (x := x) hx (hφ := hφ) (f := f) (hf := hf) g).symm

/-- Helper for Lemma 7.27.1: a glued second coordinate on the induced over-sieve yields an
amalgamation of the original family in the left Kan extension. -/
private theorem localization_leftKanExtension_glued_pair_is_amalgamation
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {s : G.obj.obj (op (Over.mk φ))}
    (hs : (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).IsAmalgamation s) :
    x.IsAmalgamation
      ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) := by
  -- Apply the sigma chart after restricting the glued pair. The first coordinate is visibly
  -- `f ≫ φ`, and the second coordinate is the glued section prescribed by `hs`.
  intro Y f hf
  apply (localization_leftKanExtension_objIsoSigma U G.obj Y).toEquiv.injective
  have hmap :
      (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
          (((Over.forget U).op.lan.obj G.obj).map f.op
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)) =
        ⟨f ≫ φ,
          G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s⟩ := by
    have hmap₀ :=
      localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f
        ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)
    have hsigma :
        (localization_leftKanExtension_objIsoSigma U G.obj V).hom
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) = ⟨φ, s⟩ := by
      simp
    rw [hsigma] at hmap₀
    simpa [localization_leftKanExtension_over_homMk] using hmap₀
  have hs' :
      G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s =
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (S := S) (φ := φ) f hf) := by
    exact hs
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
      (localization_leftKanExtension_over_homMk_mem (U := U) (S := S) (φ := φ) f hf)
  calc
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
        (((Over.forget U).op.lan.obj G.obj).map f.op
          ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)) =
      ⟨f ≫ φ,
        G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s⟩ := hmap
    _ =
      ⟨f ≫ φ,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (S := S) (φ := φ) f hf)⟩ := by
      rw [hs']
    _ = (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) := by
      symm
      exact localization_leftKanExtension_hom_eq_homMk
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) f hf

/-- Helper for Lemma 7.27.1: if a local section of the left Kan extension already amalgamates the
original family and its sigma first coordinate is `φ`, then its sigma second coordinate
amalgamates the induced family on the over-sieve of `φ`. -/
private theorem localization_leftKanExtension_second_component_is_amalgamation
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {t : ((Over.forget U).op.lan.obj G.obj).obj (op V)}
    {u : G.obj.obj (op (Over.mk φ))}
    (ht : x.IsAmalgamation t)
    (hsig : (localization_leftKanExtension_objIsoSigma U G.obj V).hom t = ⟨φ, u⟩) :
    (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).IsAmalgamation u := by
  -- Apply the sigma chart to the amalgamation equation for `t`, then normalize the `Over.w f`
  -- transport exactly as in the compatibility proof above.
  intro Y f hf
  have hpair :=
    congrArg
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
      (ht f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
  have hleft :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (((Over.forget U).op.lan.obj G.obj).map f.left.op t) =
        ⟨f.left ≫ φ,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f.left).op u⟩ := by
    -- The sigma chart on the restriction of `t` is computed by `objIsoSigma_hom_map`.
    have hmap :=
      localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f.left t
    let restrictSigma :
        (Σ a : V ⟶ U, G.obj.obj (op (Over.mk a))) →
          Σ b : Y.left ⟶ U, G.obj.obj (op (Over.mk b)) :=
      fun p ↦
        ⟨f.left ≫ p.1,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := p.1) f.left).op p.2⟩
    simpa [restrictSigma] using congrArg restrictSigma hsig |> fun h => hmap.trans h
  have hright :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) =
        ⟨Y.hom,
          localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)⟩ := by
    -- The local family already has the normalized sigma description over the induced over-sieve.
    simpa using
      localization_leftKanExtension_hom_eq_over
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
  have hcompare := hleft.symm.trans (hpair.trans hright)
  let p :
      G.obj.obj (op (Over.mk (f.left ≫ φ))) = G.obj.obj (op Y) := by
    simpa [localization_leftKanExtension_over_mk_hom_eq] using
      localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G) (Over.w f)
  have hsnd :
      cast p
          (G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f.left).op u) =
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf) := by
    -- Extract the second coordinates after transporting to the fibre over `Y`.
    exact eq_of_heq <|
      HEq.trans (cast_heq p _) ((Sigma.mk.inj_iff).1 hcompare).2
  simpa [p] using
    localization_leftKanExtension_second_coordinate_transport_over_w
      (J := J) (U := U) (G := G) f u |>.symm.trans hsnd

/-- Helper for Lemma 7.27.1: the left Kan extension presheaf is already a sheaf, so no additional
sheafification is required. -/
private theorem localization_leftKanExtension_isSheaf :
    Presheaf.IsSheaf J ((Over.forget U).op.lan.obj G.obj) := by
  -- Route correction: glue the first coordinate in the representable sheaf `h_U`, then glue the
  -- transported second coordinates directly in `G` on the induced over-sieve.
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS
  intro x hx
  let x₁ : S.arrows.FamilyOfElements (representable_presheaf (U := U)) :=
    fun _ f hf ↦
      ULift.up ((localization_leftKanExtension_objIsoSigma U G.obj _).hom (x f hf)).1
  have hx₁ : x₁.Compatible := by
    -- The first coordinates are compatible because restriction in sigma coordinates is by
    -- postcomposition with the base map.
    rw [Presieve.compatible_iff_sieveCompatible]
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    intro Y Z f g hf
    have hpair :
        (localization_leftKanExtension_objIsoSigma U G.obj Z).hom
            (x (g ≫ f) (S.downward_closed hf g)) =
          (localization_leftKanExtension_objIsoSigma U G.obj Z).hom
            (((Over.forget U).op.lan.obj G.obj).map g.op (x f hf)) := by
      exact congrArg (localization_leftKanExtension_objIsoSigma U G.obj Z).hom (hx f g hf)
    apply ULift.ext
    simpa [x₁, localization_leftKanExtension_objIsoSigma_hom_map] using congrArg Sigma.fst hpair
  let hRep : Presieve.IsSheaf J (representable_presheaf (U := U)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := J) (representable_presheaf (U := U))
  let hRepS := hRep S hS
  let φu := hRepS.amalgamate x₁ hx₁
  let φ : V ⟶ U := φu.down
  have hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1 := by
    intro Y f hf
    have hglue : (representable_presheaf (U := U)).map f.op φu = x₁ f hf :=
      hRepS.valid_glue hx₁ f hf
    simpa [x₁, φ] using hglue
  let T : Sieve (Over.mk φ) := (Sieve.overEquiv (Over.mk φ)).symm S
  have hT : T ∈ (J.over U) (Over.mk φ) :=
    J.overEquiv_symm_mem_over (Over.mk φ) S hS
  let x₂ : T.arrows.FamilyOfElements G.obj :=
    localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
  have hx₂ : x₂.Compatible :=
    localization_leftKanExtension_second_coordinate_compatible
      (J := J) (U := U) (G := G) (x := x) hx (hφ := hφ)
  have hG : Presieve.IsSheaf (J.over U) G.obj :=
    (isSheaf_iff_isSheaf_of_type (J.over U) G.obj).1 G.property
  let hGS := hG T hT
  let s := hGS.amalgamate x₂ hx₂
  refine
    ⟨(localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩, ?_, ?_⟩
  · intro Y f hf
    -- The glued pair is an amalgamation because its first coordinate is `φ` and its second
    -- coordinate is the amalgamation of the direct family in `G`.
    exact localization_leftKanExtension_glued_pair_is_amalgamation
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
      (hs := hGS.isAmalgamation (x := x₂) hx₂) f hf
  · intro t ht
    -- First compare first coordinates to force the same arrow `φ : V ⟶ U`. Then compare the
    -- resulting second coordinates by separatedness of `G` on the induced over-sieve.
    rcases hsig : (localization_leftKanExtension_objIsoSigma U G.obj V).hom t with ⟨ψ, u⟩
    have ht₁ :
        x₁.IsAmalgamation
          (ULift.up ψ) := by
      intro Y f hf
      have hpair :
          (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
              (((Over.forget U).op.lan.obj G.obj).map f.op t) =
            (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) := by
        simpa [ht f hf]
      have hmap := localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f t
      have hfst :
          f ≫ ψ =
            ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1 := by
        simpa [hsig] using (congrArg Sigma.fst hmap).symm.trans (congrArg Sigma.fst hpair)
      let e : (Y ⟶ U) → (representable_presheaf (U := U)).obj (op Y) := fun k ↦ ULift.up k
      simpa [representable_presheaf, x₁, e] using congrArg e hfst
    have hfirst_eq_u :
        ULift.up ψ = φu :=
      hRepS.isSeparatedFor x₁
        (ULift.up ψ)
        φu ht₁ (hRepS.isAmalgamation (x := x₁) hx₁)
    have hfirst :
        ψ = φ := by
      simpa [φ] using congrArg ULift.down hfirst_eq_u
    -- Rewrite the sigma first coordinate to `φ`, then compare second coordinates using
    -- separatedness of `G` on the induced over-sieve.
    cases hfirst
    have hu :
        x₂.IsAmalgamation u := by
      exact localization_leftKanExtension_second_component_is_amalgamation
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) ht hsig
    have hu_eq :
        u = s :=
      hGS.isSeparatedFor x₂ u s hu (hGS.isAmalgamation (x := x₂) hx₂)
    apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
    calc
      (localization_leftKanExtension_objIsoSigma U G.obj V).hom t = ⟨φ, u⟩ := hsig
      _ = ⟨φ, s⟩ := by rw [hu_eq]
      _ = (localization_leftKanExtension_objIsoSigma U G.obj V).hom
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) := by
          simp

/-- Lemma 7.27.1: if `J` is subcanonical and `G` is a sheaf on `C/U`, then the underlying
presheaf of `j_{U!}(G)` is canonically isomorphic to the left Kan extension of `G` along
`(Over.forget U).op`. -/
noncomputable def localization_lowerShriek_iso_leftKanExtension :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj ≅
      (Over.forget U).op.lan.obj G.obj :=
  letI : HasWeakSheafify J (Type (max u v)) := inferInstance
  (sheafToPresheaf J (Type (max u v))).mapIso <|
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).mapIso
        (sheafificationIso G)) ≪≫
      localization_lowerShriek_associatedSheafIso J U G.obj ≪≫
        (sheafificationIso
          ⟨(Over.forget U).op.lan.obj G.obj, localization_leftKanExtension_isSheaf J U G⟩).symm

/-- Objectwise `Type`-valued form of Lemma 7.27.1. -/
noncomputable def localization_lowerShriek_objIsoSigma (V : C) :
    ((((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj.obj (op V)) ≅
      Σ φ : V ⟶ U, G.obj.obj (op (Over.mk φ)) :=
  (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
    localization_leftKanExtension_objIsoSigma U G.obj V

-- Proof sketch: unfold `localization_lowerShriek_objIsoSigma`; it is defined by evaluating the main
-- isomorphism of Lemma 7.27.1 at `V` and composing with the standard sigma-description of the left
-- Kan extension.
/-- The objectwise sigma-description is obtained by evaluating the canonical isomorphism of
Lemma 7.27.1 and then applying the standard left-Kan-extension formula. -/
theorem localization_lowerShriek_objIsoSigma_def (V : C) :
    localization_lowerShriek_objIsoSigma J U G V =
      (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
        localization_leftKanExtension_objIsoSigma U G.obj V := by
  -- This is the defining equation of `localization_lowerShriek_objIsoSigma`.
  rfl

end

/-! ### Lemma_7_27_2 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasBinaryProducts C]

/- Domain-style sampling for Lemma 7.27.2:
- primary domain: localization of a site and the direct image on sheaves;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `Over.forgetAdjStar`,
  `GrothendieckTopology.over`;
- source/core/bridge triage:
  `source-facing`: the textbook formula computing `j_{U*}` on sections by evaluation on the
  slice object `U ⨯ X ⟶ U`;
  `core/canonical`: the localization direct image owner
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*`;
  `bridge/view`: the right adjoint `Over.star U`, supplied by `Over.forgetAdjStar U`, identifies
  the section over `X` with evaluation on the slice object above `U`.

Primitive data are just the site `J` and the object `U`. The localization morphism of topoi and
its pushforward are already owned upstream, while `Over.star U` is derived from the standard
adjunction `Over.forget U ⊣ Over.star U`. The public refinement should therefore keep the main
statement on the canonical owner `j_{U*}` and use the existing right-adjoint comparison with
`Over.star U` only as a bridge to the objectwise slice formula.
-/

variable (U : C)

/- Lemma 7.27.2, owner recall: the localization direct image `j_{U*}` is the pushforward of the
canonical localization morphism attached to `Over.forget U`. -/
#check
  ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*) :
    Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf J (Type (max u v)))

/- Companion recall: localization at `U` is governed by the standard adjunction
`Over.forget U ⊣ Over.star U`, and `Over.star U` sends `X` to the slice object `U ⨯ X ⟶ U`. -/
#check Over.forgetAdjStar U

variable [HasSheafify J (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasPointwiseRightKanExtension P]

/-- The localization direct image `j_{U*}` is computed on `X` by evaluating `ℱ` on the slice
object `U ⨯ X ⟶ U`, i.e. on `(Over.star U).obj X`. -/
noncomputable def localization_directImage_objIso_sections_over_star
    (ℱ : Sheaf (J.over U) (Type (max u v))) (X : C) :
    (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj ℱ).obj.obj
        (op X)) ≅
      ℱ.obj.obj (op ((Over.star U).obj X)) :=
  let pushforwardIso :
      (((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*) ≅
        (Over.star U).sheafPushforwardContinuous (Type (max u v)) J (J.over U) :=
    (eqToIso
      (Functor.morphismOfTopoiInOfCocontinuous_pushforward
        (Over.forget U) (J.over U) J)) ≪≫
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.forget U) (Over.star U) (Type (max u v)) (Over.forgetAdjStar U)).symm
  let e :
      ((((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj ℱ).obj)) ≅
        (Over.star U).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
          pushforwardIso
          (sheafToPresheaf J (Type (max u v)))).app ℱ) ≪≫
      ((Over.star U).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u v)) J (J.over U)).app ℱ
  e.app (op X)

end

/-! ### Lemma_7_27_3 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {U V : C} (f : U ⟶ V)
variable [HasPullbacksAlong f]

/-
Domain-style sampling for Lemma 7.27.3:
- primary domain: relocalization between slice sites and the induced direct image on sheaves;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `Over.mapPullbackAdj`,
  `Adjunction.isContinuous_of_isCocontinuous`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardContinuous`;
- source-facing layer: the textbook direct image `j_*` for relocalization along `f : U ⟶ V`;
- core/canonical owner: the relocalization morphism of topoi
  `(Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)` and its direct image
  `j_*`;
- bridge/view: the right adjoint `Over.pullback f` and the continuous-versus-cocontinuous
  pushforward comparison, used only internally to compute sections of `j_*`.

Primitive data are the morphism `f` and pullbacks along `f`. Continuity of `Over.pullback f` is
derived from the owner adjunction and cocontinuity of `Over.map f`. The canonical relocalization
morphism of topoi already owns the public direct image `j_*`, while the section formula is a
derived computation obtained by comparing that owner with the continuous pushforward of
`Over.pullback f` and then evaluating the standard continuous-pushforward section formula.
-/
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasPointwiseRightKanExtension P]

/- Lemma 7.27.3, owner recall: the relocalization direct image `j_*` along `f` is the pushforward
of the canonical relocalization morphism of topoi attached to `Over.map f`. -/
#check
  ((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*) :
    Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf (J.over V) (Type (max u v)))

variable (ℱ : Sheaf (J.over U) (Type (max u v))) (X : Over V)

-- Proof sketch: whisker the functor comparison above by `sheafToPresheaf` to compare the
-- underlying presheaves, then compose with the canonical owner computation
-- `Functor.sheafPushforwardContinuousCompSheafToPresheafIso` for `Over.pullback f`. Evaluating at
-- `X/V` yields the section formula.
/-- The direct image `j_*` along relocalization is computed on `X/V` by evaluating the sheaf on
the slice pullback object `(Over.pullback f).obj X`, i.e. the textbook object
`(X ×_V U)/U`. -/
noncomputable def relocalization_directImage_objIso_sections_over_pullback :
    (((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*).obj ℱ).obj.obj
        (op X)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj X)) :=
  letI : Functor.IsContinuous (Over.pullback f) (J.over V) (J.over U) :=
    (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous (J.over U) (J.over V)
  let pushforwardIso :
      (((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*) ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (max u v)) (J.over V) (J.over U) :=
    (eqToIso
      (Functor.morphismOfTopoiInOfCocontinuous_pushforward
        (Over.map f) (J.over U) (J.over V))) ≪≫
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.map f) (Over.pullback f) (Type (max u v)) (Over.mapPullbackAdj f)).symm
  let e :
    ((((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*).obj ℱ).obj)) ≅
        (Over.pullback f).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
          pushforwardIso
          (sheafToPresheaf (J.over V) (Type (max u v)))).app ℱ) ≪≫
      ((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u v)) (J.over V) (J.over U)).app ℱ
  e.app (op X)

end

end CategoryTheory

/-! ### Lemma_7_27_4 (from Chap07) -/
open CategoryTheory

universe w v u

noncomputable section

/- Domain-style sampling for Lemma 7.27.4:
- primary domain: localization of sites and the induced adjunctions on sheaves over slice sites;
- sampled owner API:
  `Over.forget`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- source-facing layer: the two canonical maps
  `ℱ ⟶ j_U⁻¹ j_{U!} ℱ` and `j_U⁻¹ j_{U*} ℱ ⟶ ℱ`;
- core/canonical owner: the adjunction owners
  `(Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J` and
  `(Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J`;
- bridge/view: this file specializes the fully faithful site-functor results of Lemma 7.21.7 to
  the localization functor `Over.forget U`.

Primitive data are the site `J`, the object `U`, and the hypothesis that each hom-set `X ⟶ U` is
subsingleton. The `Full` structure on `Over.forget U` is the only extra primitive API needed in
this specialization; the `IsIso` statements for the unit and counit are derived from the canonical
adjunction owners.
-/

/-- Helper for Lemma 7.27.4: if every object of `C` admits at most one morphism to `U`, then the
localization functor `Over.forget U : Over U ⥤ C` is full. This is the bridge from the source
subsingleton-hom hypothesis to the canonical fully faithful adjunction owners for localization. -/
theorem overForget_full_of_subsingletonHom
    {C : Type u} [Category.{v} C] (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U)) :
    (Over.forget U).Full where
  map_surjective {X Y} f := by
    -- Any base morphism into `Y.left` automatically respects the maps to `U`.
    have h_comm : f ≫ Y.hom = X.hom := by
      exact @Subsingleton.elim _ (hU X.left) _ _
    -- The induced over-morphism maps back to the original base morphism under `Over.forget`.
    refine ⟨Over.homMk f ?_, rfl⟩
    exact h_comm

-- Proof sketch: the hypothesis makes `Over.forget U` fully faithful, so Lemma `7.21.7` applies to
-- the continuous localization functor `Over.forget U : (C/U, J.over U) ⥤ (C, J)`.
/-- Lemma 7.27.4 (1): if every object of the site `C` has at most one morphism to `U`, then for
every sheaf `ℱ` on the localized site `C/U` the canonical map
`ℱ ⟶ j_U⁻¹ j_{U!} ℱ` is an isomorphism. -/
theorem localization_lowerShriek_unit_app_isIso_of_subsingletonHom
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [HasWeakSheafify J (Type w)]
    [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseLeftKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
    (ℱ : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).unit.app ℱ) := by
  -- Install fullness of the localization functor so Lemma 7.21.7 applies directly.
  have hfull : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  letI : (Over.forget U).Full := hfull
  exact unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ

-- Proof sketch: the same full-faithfulness bridge lets Lemma `7.21.7` identify the counit of the
-- cocontinuous localization adjunction as an isomorphism.
/-- Lemma 7.27.4 (2): if every object of the site `C` has at most one morphism to `U`, then for
every sheaf `ℱ` on the localized site `C/U` the canonical map
`j_U⁻¹ j_{U*} ℱ ⟶ ℱ` is an isomorphism. -/
theorem localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (hU : ∀ X : C, Subsingleton (X ⟶ U))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
    (ℱ : Sheaf (J.over U) (Type w)) :
    IsIso (((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J).counit.app ℱ) := by
  -- The same fullness bridge identifies the cocontinuous adjunction counit as an isomorphism.
  have hfull : (Over.forget U).Full := overForget_full_of_subsingletonHom U hU
  letI : (Over.forget U).Full := hfull
  exact counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful (J.over U) J (Over.forget U) ℱ
