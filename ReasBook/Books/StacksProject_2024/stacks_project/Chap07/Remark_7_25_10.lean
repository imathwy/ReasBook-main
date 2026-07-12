import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 7.25.10:
- primary domain: category-theoretic localization of presheaves via restriction and Kan extension
  along `Over.forget U`;
- sampled owner API:
  `Functor.whiskeringLeft`,
  `Functor.lanAdjunction`,
  `Functor.ranAdjunction`,
  `Functor.leftKanExtensionObjIsoColimit`;
- source-facing layer: the remark identifies the inverse-image functor on presheaves and its two
  canonical adjoints for localization at `U`;
- core/canonical owner: restriction by precomposition with `(Over.forget U).op` and the Kan
  extension adjunctions owned upstream by mathlib;
- bridge/view: the objectwise sigma-type formula for the left Kan extension and its finite
  connected limit preservation consequences.

Primitive data are the category `C`, the localization object `U`, and a presheaf on `Over U`.
The inverse-image functor and both adjunctions are derived API owned by
`Functor.whiskeringLeft`, `Functor.lanAdjunction`, and `Functor.ranAdjunction`, so this file
should recall those owners directly and keep only the genuinely local bridge results.
-/

namespace LocalizationLeftKanExtension

-- Proof sketch: evaluate `j_{U!} = (Over.forget U).op.lan` at `V`, use the sigma-type formula
-- for its values to identify it with the coproduct of the fibers `G(V ⟶ U)`, and then apply the
-- standard fact that coproducts of sets commute with finite connected limits.
private theorem preservesFiniteConnectedLimits
    (U : C) (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := by
  sorry

/-- The discrete family of terminal objects in the indexing category for the objectwise
left-Kan-extension formula along `(Over.forget U).op`. -/
private abbrev indexFunctor
    (U V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- The composite `V ⟶ U` attached to a costructured arrow over `(Over.forget U).op`. -/
private abbrev overObj
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- The leg `V ⟶ A` of the underlying triangle `V ⟶ A ⟶ U`. -/
private abbrev leg
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (overObj X).left :=
  X.hom.unop

/-- The composite `V ⟶ U` attached to a costructured arrow over `(Over.forget U).op`. -/
private abbrev composite
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  leg X ≫ (overObj X).hom

/-- The discrete index determined by the commutative triangle underlying `X`. -/
private abbrev index
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (composite X)

/-- The distinguished morphism from an indexing object to the terminal object in its fiber. -/
private abbrev terminalHom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (indexFunctor U V).obj (index X) :=
  CostructuredArrow.homMk
    ((show Over.mk (composite X) ⟶ overObj X from Over.homMk (leg X)).op)
    (by
      simp [indexFunctor, index, leg])

/-- Any morphism into `indexFunctor U V` is indexed by the composite `V ⟶ U` of the underlying
commutative triangle. -/
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

/-- Any morphism into `indexFunctor U V` is indexed by the composite `V ⟶ U` of the underlying
commutative triangle. -/
private lemma composite_eq_of_hom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U} (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    composite X = φ := by
  simpa [indexFunctor, composite, leg, overObj] using composite_eq_of_map U V hom

/-- The distinguished morphism into an indexing object is obtained by reindexing the composite
attached to `X`. -/
private def homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ) :
    X ⟶ (indexFunctor U V).obj (Discrete.mk φ) := by
  cases hφ
  exact terminalHom U V

/-- A morphism into the chosen terminal object is determined uniquely by its commutative triangle. -/
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

private lemma hom_eq_homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ)
    (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    hom = homToIndex U V X φ hφ := by
  cases hφ
  simpa [homToIndex] using hom_eq_terminalHom U V X hom

/-- The indexing category of triangles over `V ⟶ U` remembers only the composite map
`V ⟶ U`. -/
private abbrev compositeFunctor
    (U V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (composite X)
  map hom := Discrete.eqToHom (composite_eq_of_map U V hom)

/-- The discrete inclusion of indices is right adjoint to the functor remembering the composite
`V ⟶ U`. -/
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

/-- The discrete inclusion of the chosen terminal objects is final. -/
private theorem indexFunctor_final (U V : C) : Functor.Final (indexFunctor U V) := by
  let _ : (indexFunctor U V).IsRightAdjoint :=
    ⟨⟨compositeFunctor U V, ⟨compositeIndexAdjunction U V⟩⟩⟩
  infer_instance

/-- The restricted indexing diagram is literally the discrete family
`φ ↦ G(V \xrightarrow{φ} U)`. -/
private abbrev indexFunctorProjIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    indexFunctor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

end LocalizationLeftKanExtension

/-- The canonical left Kan extension along `(Over.forget U).op` is objectwise the coproduct of
the fibers `G(V \xrightarrow{} U)` over all morphisms `V ⟶ U`. -/
noncomputable def localization_leftKanExtension_objIsoSigma
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    (((Over.forget U).op.lan.obj G).obj (op V)) ≅ Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  letI : Functor.Final (LocalizationLeftKanExtension.indexFunctor U V) :=
    LocalizationLeftKanExtension.indexFunctor_final U V
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (LocalizationLeftKanExtension.indexFunctor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (LocalizationLeftKanExtension.indexFunctorProjIso U G V) ≪≫
    Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

variable (U : C)

/- Remark 7.25.10 (1): the inverse-image functor on presheaves for localization at `U` is
restriction along `Over.forget U : Over U ⥤ C`, i.e. precomposition with `(Over.forget U).op`. -/
#check (whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type (max u v))).obj (Over.forget U).op
/- Remark 7.25.10 (2): the localization inverse-image functor on presheaves has the canonical left
adjoint `j_{U!}`, namely left Kan extension along `(Over.forget U).op`. -/
#check (Over.forget U).op.lanAdjunction (Type (max u v))

/- Remark 7.25.10 (3): the same inverse-image functor on presheaves has the canonical right adjoint
`j_{U*}`, namely right Kan extension along `(Over.forget U).op`. -/
#check (Over.forget U).op.ranAdjunction (Type (max u v))

/-- Remark 7.25.10 (1): the presheaf-level localization lower shriek `j_{U!}`, realized as left Kan
extension along `(Over.forget U).op`, commutes with fibre products. -/
theorem localization_leftKanExtension_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) :=
  LocalizationLeftKanExtension.preservesFiniteConnectedLimits U WalkingCospan

/-- Remark 7.25.10 (2): the presheaf-level localization lower shriek `j_{U!}`, realized as left Kan
extension along `(Over.forget U).op`, commutes with equalizers. -/
theorem localization_leftKanExtension_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) :=
  LocalizationLeftKanExtension.preservesFiniteConnectedLimits U WalkingParallelPair

end
