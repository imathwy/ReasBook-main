import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Limits

section

variable (R : Type u) [CommRing R]

private abbrev algForget : AlgCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

private abbrev commAlgForget : CommAlgCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  forget₂ (CommAlgCat.{max u v} R) (AlgCat.{max u v} R) ⋙
    forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

namespace TensorAlgebra

/-- The category-theoretic tensor algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (TensorAlgebra R M)
  map {_ N} f :=
    AlgCat.ofHom <| TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f.hom)
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

private noncomputable def homEquiv (M : ModuleCat.{max u v} R) (A : AlgCat.{max u v} R) :
    ((functor R).obj M ⟶ A) ≃ (M ⟶ (algForget R).obj A) where
  toFun f := ModuleCat.ofHom <| f.hom.toLinearMap ∘ₗ (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M)
  invFun f := AlgCat.ofHom <| TensorAlgebra.lift R (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact TensorAlgebra.lift_comp_ι f.hom
  right_inv f := by
    apply ModuleCat.hom_ext
    exact TensorAlgebra.ι_comp_lift (show M →ₗ[R] A from f.hom)

noncomputable instance : (functor R).IsLeftAdjoint :=
  (Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply AlgCat.hom_ext
        apply TensorAlgebra.hom_ext
        ext x
        dsimp
        calc
          (TensorAlgebra.lift R ((show X →ₗ[R] Y from g.hom).comp f.hom)) (TensorAlgebra.ι R x) =
              g.hom (f.hom x) := by
                rw [TensorAlgebra.lift_ι_apply]
                rfl
          _ =
              ((TensorAlgebra.lift R (show X →ₗ[R] Y from g.hom)).comp
                (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f.hom))) (TensorAlgebra.ι R x) := by
              rw [AlgHom.comp_apply, TensorAlgebra.lift_ι_apply]
              change g.hom (f.hom x) = (TensorAlgebra.lift R (show X →ₗ[R] Y from g.hom))
                (TensorAlgebra.ι R (f.hom x))
              rw [TensorAlgebra.lift_ι_apply]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        apply ModuleCat.hom_ext
        ext x
        rfl }).isLeftAdjoint

end TensorAlgebra

namespace SymmetricAlgebra

/-- The category-theoretic symmetric algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ CommAlgCat.{max u v} R where
  obj M := CommAlgCat.of R (SymmetricAlgebra R M)
  map {_ N} f :=
    CommAlgCat.ofHom <|
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R N).comp f.hom)
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

private noncomputable def homEquiv (M : ModuleCat.{max u v} R) (A : CommAlgCat.{max u v} R) :
    ((functor R).obj M ⟶ A) ≃ (M ⟶ (commAlgForget R).obj A) where
  toFun f := ModuleCat.ofHom <| f.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M
  invFun f := CommAlgCat.ofHom <| SymmetricAlgebra.lift (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    change
      SymmetricAlgebra.lift
          (f.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M)
          ((SymmetricAlgebra.ι R M) x) =
        f.hom ((SymmetricAlgebra.ι R M) x)
    exact SymmetricAlgebra.lift_ι_apply _ x
  right_inv f := by
    apply ModuleCat.hom_ext
    exact SymmetricAlgebra.lift_comp_ι (show M →ₗ[R] A from f.hom)

private theorem homEquiv_naturality_left_aux
    {X' X : ModuleCat.{max u v} R} {Y : CommAlgCat.{max u v} R}
    (f : X' ⟶ X) (g : (functor R).obj X ⟶ Y) :
    homEquiv R X' Y ((functor R).map f ≫ g) = f ≫ homEquiv R X Y g := by
  apply ModuleCat.hom_ext
  ext x
  change
    g.hom (((functor R).map f).hom ((SymmetricAlgebra.ι R X') x)) =
      g.hom ((SymmetricAlgebra.ι R X) (f.hom x))
  rw [show ((functor R).map f).hom =
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι R X).comp f.hom) by rfl]
  exact congrArg g.hom (SymmetricAlgebra.lift_ι_apply ((SymmetricAlgebra.ι R X).comp f.hom) x)

private theorem homEquiv_naturality_right_aux
    {X : ModuleCat.{max u v} R} {Y Y' : CommAlgCat.{max u v} R}
    (g : (functor R).obj X ⟶ Y) (h : Y ⟶ Y') :
    homEquiv R X Y' (g ≫ h) =
      homEquiv R X Y g ≫ (commAlgForget R).map h := by
  apply ModuleCat.hom_ext
  ext x
  rfl

noncomputable instance : (functor R).IsLeftAdjoint :=
  (Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [Equiv.symm_apply_eq]
        calc
          f ≫ g = f ≫ (homEquiv R X Y) ((homEquiv R X Y).symm g) := by
            exact congrArg (fun k ↦ f ≫ k) ((homEquiv R X Y).apply_symm_apply g).symm
          _ = (homEquiv R X' Y) ((functor R).map f ≫ (homEquiv R X Y).symm g) := by
            symm
            exact homEquiv_naturality_left_aux R f ((homEquiv R X Y).symm g)
      homEquiv_naturality_right := by
        intro X Y Y' g h
        exact homEquiv_naturality_right_aux R g h }).isLeftAdjoint

end SymmetricAlgebra

namespace ExteriorAlgebra

/-- The category-theoretic exterior algebra functor on `R`-modules. -/
@[simps]
def functor : ModuleCat.{max u v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (ExteriorAlgebra R M)
  map {_ _} f := AlgCat.ofHom <| ExteriorAlgebra.map f.hom
  map_id M := by
    ext m
    simp
  map_comp f g := by
    ext m
    simp

end ExteriorAlgebra

variable {I : Type v} [Preorder I] [IsDirectedOrder I]

/-- Lemma 10.13.5 (1): the tensor algebra construction commutes with colimits of directed systems
of `R`-modules. -/
@[stacks 00DQ]
instance tensor_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (TensorAlgebra.functor R) :=
  inferInstance

/-- Lemma 10.13.5 (2): the symmetric algebra construction commutes with colimits of directed
systems of `R`-modules. -/
@[stacks 00DQ]
instance symmetric_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (SymmetricAlgebra.functor R) :=
  inferInstance

-- Proof sketch: the exterior algebra is the quotient of the tensor algebra by the alternating
-- square-zero relations, so the same reduction to Lemma `10.12.9` applies.
/-- Helper for Lemma 10.13.5: the colimit module used to build the exterior-algebra colimit
cocone. -/
private noncomputable abbrev exterior_algebra_module_colimit
    (F : I ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    ModuleCat.{max u v} R :=
  CategoryTheory.Limits.colimit F

/-- Helper for Lemma 10.13.5: the mapped colimit cocone for the exterior algebra functor. -/
private noncomputable abbrev exterior_algebra_colimit_cocone
    (F : I ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    Cocone (F ⋙ ExteriorAlgebra.functor R) :=
  (ExteriorAlgebra.functor R).mapCocone (colimit.cocone F)

/-- Helper for Lemma 10.13.5: the colimit of an empty module diagram is a subsingleton module. -/
private theorem exterior_algebra_module_colimit_subsingleton_of_isEmpty
    [IsEmpty I] {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F] :
    Subsingleton (exterior_algebra_module_colimit (R := R) F) := by
  -- Identify the empty-shape colimit with the zero module.
  have hinitial : IsInitial (colimit F : ModuleCat.{max u v} R) :=
    (isColimitEquivIsInitialOfIsEmpty (ModuleCat.{max u v} R) (colimit.cocone F))
      (colimit.isColimit F)
  have hzeroModule : IsZero (ModuleCat.of R PUnit) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)
  let e : (colimit F : ModuleCat.{max u v} R) ≅ ModuleCat.of R PUnit :=
    hinitial.coconePointUniqueUpToIso hzeroModule.isInitial
  have hzero : IsZero (colimit F : ModuleCat.{max u v} R) :=
    IsZero.of_iso hzeroModule e
  exact ModuleCat.subsingleton_of_isZero hzero

/-- Helper for Lemma 10.13.5: the stagewise generator maps into a cocone over exterior algebras
form a cocone of modules. -/
private theorem exterior_algebra_generator_cocone_naturality
    {F : I ⥤ ModuleCat.{max u v} R}
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) {i j : I} (f : i ⟶ j) :
    F.map f ≫ ModuleCat.ofHom (((s.ι.app j).hom.toLinearMap).comp (ExteriorAlgebra.ι R)) =
      ModuleCat.ofHom (((s.ι.app i).hom.toLinearMap).comp (ExteriorAlgebra.ι R)) := by
  -- Evaluate cocone naturality on exterior generators.
  apply ModuleCat.hom_ext
  ext x
  have hf := congr_fun ((forget (AlgCat R)).congr_map (s.w f)) (ExteriorAlgebra.ι R x)
  calc
    (s.ι.app j).hom (ExteriorAlgebra.ι R ((F.map f).hom x)) =
        (s.ι.app j).hom (ExteriorAlgebra.map (F.map f).hom (ExteriorAlgebra.ι R x)) := by
          rw [ExteriorAlgebra.map_apply_ι]
    _ = (s.ι.app i).hom (ExteriorAlgebra.ι R x) := hf

/-- Helper for Lemma 10.13.5: a cocone over the module diagram induced by the generator maps into
an exterior-algebra cocone. -/
private noncomputable def exterior_algebra_generator_cocone
    {F : I ⥤ ModuleCat.{max u v} R}
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) :
    Cocone F where
  pt := (algForget R).obj s.pt
  ι :=
    { app := fun i ↦
        ModuleCat.ofHom (((s.ι.app i).hom.toLinearMap).comp (ExteriorAlgebra.ι R))
      naturality := fun _ _ f ↦
        exterior_algebra_generator_cocone_naturality (R := R) s f }

/-- Helper for Lemma 10.13.5: the module-colimit universal property descends the generator maps to
a linear map on the colimit module. -/
private noncomputable def exterior_algebra_colimit_linear_desc
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) :
    (exterior_algebra_module_colimit (R := R) F →ₗ[R] s.pt) :=
  (colimit.desc F (exterior_algebra_generator_cocone (R := R) s)).hom

/-- Helper for Lemma 10.13.5: the descended linear map agrees with the original cocone on each
stage generator. -/
private theorem exterior_algebra_colimit_linear_desc_ι_apply
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) (i : I) (x : F.obj i) :
    exterior_algebra_colimit_linear_desc (R := R) (F := F) s
        ((colimit.ι F i).hom x) =
      (s.ι.app i).hom (ExteriorAlgebra.ι R x) := by
  -- Evaluate the colimit factorization on the chosen stage element.
  change ((colimit.ι F i ≫ colimit.desc F (exterior_algebra_generator_cocone (R := R) s)).hom x) =
    (s.ι.app i).hom (ExteriorAlgebra.ι R x)
  rw [colimit.ι_desc]
  rfl

/-- Helper for Lemma 10.13.5: the descended linear map sends every colimit element to a
square-zero element. -/
private theorem exterior_algebra_colimit_linear_desc_sq_zero
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) :
    ∀ x : exterior_algebra_module_colimit (R := R) F,
      exterior_algebra_colimit_linear_desc (R := R) (F := F) s x *
        exterior_algebra_colimit_linear_desc (R := R) (F := F) s x = 0 := by
  intro x
  -- Route correction: use representatives only in the nonempty filtered branch; in the empty
  -- branch the module colimit is forced to be trivial.
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    letI : IsFiltered I := inferInstance
    let t : ColimitCocone F :=
      { cocone := ModuleCat.FilteredColimits.colimitCocone F
        isColimit := by
          simpa using (ModuleCat.FilteredColimits.colimitCoconeIsColimit F) }
    let e : colimit F ≅ ModuleCat.FilteredColimits.colimit F :=
      colimit.isoColimitCocone t
    -- Write the colimit element using the explicit filtered-colimit model.
    obtain ⟨i, y, hy⟩ := ModuleCat.FilteredColimits.M.mk_surjective F (e.hom x)
    have hx : (colimit.ι F i).hom y = x := by
      have hy' : e.hom ((colimit.ι F i).hom y) = e.hom x := by
        have hι :
            e.hom ((colimit.ι F i).hom y) =
              (ModuleCat.FilteredColimits.colimitCocone F).ι.app i y := by
          have hι' :
              ModuleCat.Hom.hom (colimit.ι F i ≫ e.hom) =
                ModuleCat.Hom.hom ((ModuleCat.FilteredColimits.colimitCocone F).ι.app i) :=
            congrArg ModuleCat.Hom.hom (colimit.isoColimitCocone_ι_hom t i)
          exact LinearMap.congr_fun hι' y
        exact hι.trans hy
      simpa using congrArg (fun z ↦ e.inv z) hy'
    rw [← hx]
    -- The cocone leg already lands in an exterior algebra, so its generators square to zero.
    rw [exterior_algebra_colimit_linear_desc_ι_apply (R := R) (F := F) s i y]
    exact ExteriorAlgebra.comp_ι_sq_zero (s.ι.app i).hom y
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    -- The empty colimit module has only the zero element, so the square-zero check is immediate.
    have hx : x = 0 := by
      let hsub :
          Subsingleton (exterior_algebra_module_colimit (R := R) F) :=
        exterior_algebra_module_colimit_subsingleton_of_isEmpty (R := R) (F := F)
      exact @Subsingleton.elim _ hsub x 0
    rw [hx]
    simp

/-- Helper for Lemma 10.13.5: the descended linear map upgrades to the universal algebra map out
of the exterior algebra on the colimit module. -/
private noncomputable def exterior_algebra_colimit_desc
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) :
    AlgCat.of R (ExteriorAlgebra R (exterior_algebra_module_colimit (R := R) F)) ⟶ s.pt :=
  AlgCat.ofHom <|
    ExteriorAlgebra.lift R
      ⟨exterior_algebra_colimit_linear_desc (R := R) (F := F) s,
        exterior_algebra_colimit_linear_desc_sq_zero (R := R) (F := F) s⟩

/-- Helper for Lemma 10.13.5: the algebra map built from the module-colimit descent factors the
given cocone through the mapped colimit cocone. -/
private theorem exterior_algebra_colimit_desc_fac
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    (s : Cocone (F ⋙ ExteriorAlgebra.functor R)) (i : I) :
    (exterior_algebra_colimit_cocone (R := R) F).ι.app i ≫
        exterior_algebra_colimit_desc (R := R) (F := F) s =
      s.ι.app i := by
  -- Compare the two algebra morphisms on the exterior generators.
  apply AlgCat.hom_ext
  apply ExteriorAlgebra.hom_ext
  ext x
  unfold exterior_algebra_colimit_desc
  change ExteriorAlgebra.lift R
      ⟨exterior_algebra_colimit_linear_desc (R := R) (F := F) s,
        exterior_algebra_colimit_linear_desc_sq_zero (R := R) (F := F) s⟩
      (ExteriorAlgebra.map ((colimit.ι F i).hom) (ExteriorAlgebra.ι R x)) =
    (s.ι.app i).hom (ExteriorAlgebra.ι R x)
  rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.lift_ι_apply]
  exact exterior_algebra_colimit_linear_desc_ι_apply (R := R) (F := F) s i x

/-- Helper for Lemma 10.13.5: morphisms out of the exterior algebra on the colimit are determined
by their restrictions to the stage generators. -/
private theorem exterior_algebra_hom_ext_of_module_hom_eq
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    {s : Cocone (F ⋙ ExteriorAlgebra.functor R)}
    {f g : AlgCat.of R (ExteriorAlgebra R (exterior_algebra_module_colimit (R := R) F)) ⟶ s.pt}
    (h : ModuleCat.ofHom (f.hom.toLinearMap.comp (ExteriorAlgebra.ι R)) =
      ModuleCat.ofHom (g.hom.toLinearMap.comp (ExteriorAlgebra.ι R))) :
    f = g := by
  -- Strip the bundled `ModuleCat` wrapper and reduce to generator equality.
  apply AlgCat.hom_ext
  apply ExteriorAlgebra.hom_ext
  exact congrArg ModuleCat.Hom.hom h

/-- Helper for Lemma 10.13.5: morphisms out of the exterior algebra on the colimit are determined
by their restrictions to the stage generators. -/
private theorem exterior_algebra_colimit_hom_ext
    {F : I ⥤ ModuleCat.{max u v} R} [HasColimit F]
    {s : Cocone (F ⋙ ExteriorAlgebra.functor R)}
    {f g : AlgCat.of R (ExteriorAlgebra R (exterior_algebra_module_colimit (R := R) F)) ⟶ s.pt}
    (h : ∀ i, (exterior_algebra_colimit_cocone (R := R) F).ι.app i ≫ f =
      (exterior_algebra_colimit_cocone (R := R) F).ι.app i ≫ g) :
    f = g := by
  -- Route correction: first compare the induced module maps out of `colimit F`, then invoke
  -- `ExteriorAlgebra.hom_ext` only after the bundled coercions have been stripped away.
  apply exterior_algebra_hom_ext_of_module_hom_eq (R := R) (F := F) (s := s)
  -- The colimit module morphisms agree once they agree after precomposing with each stage map.
  apply colimit.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  -- Evaluate the assumed cocone-leg equality on the exterior generator `ι x`.
  have hi :=
    congrArg (fun k ↦ k (ExteriorAlgebra.ι R x)) (congrArg AlgCat.Hom.hom (h i))
  change
    f.hom (ExteriorAlgebra.map (colimit.ι F i).hom (ExteriorAlgebra.ι R x)) =
      g.hom (ExteriorAlgebra.map (colimit.ι F i).hom (ExteriorAlgebra.ι R x)) at hi
  rw [ExteriorAlgebra.map_apply_ι] at hi
  simpa [exterior_algebra_colimit_cocone] using hi

/-- Helper for Lemma 10.13.5: the obvious cocone on `ExteriorAlgebra R (colimit F)` is a colimit
cocone. -/
private noncomputable def exterior_algebra_colimit_cocone_isColimit
    (F : I ⥤ ModuleCat.{max u v} R) [HasColimit F] :
    IsColimit (exterior_algebra_colimit_cocone (R := R) F) where
  desc s := exterior_algebra_colimit_desc (R := R) (F := F) s
  fac s i := exterior_algebra_colimit_desc_fac (R := R) (F := F) s i
  uniq s m hm := by
    -- The explicit descended algebra map is uniquely determined on every stage generator.
    apply exterior_algebra_colimit_hom_ext (R := R) (F := F) (s := s)
    intro i
    exact (hm i).trans (exterior_algebra_colimit_desc_fac (R := R) (F := F) s i).symm

/-- Lemma 10.13.5 (3): the exterior algebra construction commutes with colimits of directed
systems of `R`-modules. -/
@[stacks 00DQ]
noncomputable instance exterior_algebra_preserves_directed_colimits :
    PreservesColimitsOfShape I (ExteriorAlgebra.functor.{u, v} R) where
  preservesColimit := fun {K} ↦ by
    -- Route correction: package the chosen-cocone proof directly, instead of transporting it
    -- across an arbitrary colimiting cocone comparison.
    by_cases hK : HasColimit K
    · letI : HasColimit K := hK
      -- When the module colimit exists, reuse the explicit chosen-cocone proof above.
      have hmapped :
          IsColimit ((ExteriorAlgebra.functor.{u, v} R).mapCocone (colimit.cocone K)) := by
        simpa [exterior_algebra_colimit_cocone] using
          (exterior_algebra_colimit_cocone_isColimit (R := R) K)
      exact preservesColimit_of_preserves_colimit_cocone
        (K := K)
        (F := ExteriorAlgebra.functor.{u, v} R)
        (colimit.isColimit K)
        hmapped
    · refine ⟨?_⟩
      intro c hc
      -- If `F` had no colimit, then any claimed colimiting cocone would be impossible.
      exact False.elim <| hK (HasColimit.mk ⟨c, hc⟩)

end
