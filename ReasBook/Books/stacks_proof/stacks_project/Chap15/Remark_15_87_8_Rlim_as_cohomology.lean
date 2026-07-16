import stacks_proof.stacks_project.Chap15.«15_87_1_1»
import stacks_proof.stacks_project.Chap19.Proposition_19_6_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Sheaf

noncomputable section

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)
private abbrev rightDerivedLimitOnSequentialAbelianGroups (p : ℕ) :
    AbSeq ⥤ AddCommGrpCat :=
  ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)

local notation:max "R^" p:max " lim(" A ")" =>
  Functor.obj (rightDerivedLimitOnSequentialAbelianGroups p) A

/- Domain-style sampling for Remark 15.87.8:
- primary domain: inverse limit on sequential inverse systems of abelian groups, compared with
  sheaf cohomology on the chaotic site of `ℕ`;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `CategoryTheory.Limits.lim`,
  `sheafBotEquivalence`,
  `Sheaf.ΓNatIsoLim`,
  `Sheaf.Γ`,
  `Sheaf.cohomologyFunctor`,
  `Functor.rightDerived`;
- best owner abstraction: the source-facing sheaf-side owner is
  `Sheaf.cohomologyFunctor NatSite p`; the inverse-limit side owner is
  `lim : AbSeq ⥤ AddCommGrpCat`; the passage from inverse systems to sheaves is the bridge
  `(sheafBotEquivalence AddCommGrpCat).inverse`, while `Sheaf.ΓNatIsoLim` is the canonical
  underived comparison identifying global sections with inverse limit on the chaotic site;
- primitive data: the inverse-limit functor, the global-sections functor on the chaotic site, the
  bottom-topology sheaf equivalence, and the sheaf-cohomology owner `Sheaf.cohomologyFunctor`;
- derived API: `Functor.rightDerived`, plus the bridge from right derived global sections to
  `Sheaf.cohomologyFunctor`.

Source/core/bridge triage:
- `source-facing`: the comparison between `R lim` and the sheaf cohomology functors
  `Sheaf.cohomologyFunctor NatSite p` on the chaotic site;
- `core/canonical`: `lim : AbSeq ⥤ AddCommGrpCat` and `Sheaf.cohomologyFunctor NatSite p`;
- `bridge/view`: `(sheafBotEquivalence AddCommGrpCat).inverse`, `Sheaf.ΓNatIsoLim NatSite
  AddCommGrpCat`, and the comparison from right derived global sections to sheaf cohomology. -/

/-- The bottom-topology equivalence identifies global sections of the corresponding sheaf on
`NatSite` with inverse limit on sequential inverse systems of abelian groups. -/
noncomputable def naturalNumbersSiteInverseΓIsoLim :
    (sheafBotEquivalence AddCommGrpCat).inverse ⋙ Sheaf.Γ NatSite AddCommGrpCat ≅
      (lim : AbSeq ⥤ AddCommGrpCat) :=
  Functor.isoWhiskerLeft
      ((sheafBotEquivalence AddCommGrpCat).inverse)
      (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafBotEquivalence AddCommGrpCat).counitIso _ ≪≫
    Functor.leftUnitor _

local instance sheafBotEquivalenceInverse_additive :
    ((sheafBotEquivalence AddCommGrpCat).inverse :
      AbSeq ⥤ Sheaf NatSite AddCommGrpCat).Additive where
  map_add := by
    intro A B f g
    rfl

local instance gammaNatSite_additive :
    (Sheaf.Γ NatSite AddCommGrpCat).Additive :=
  Functor.additive_of_iso (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat).symm

/- The Ext-based sheaf-cohomology owner on `NatSite` is `Sheaf.cohomologyFunctor NatSite`. -/
recall Sheaf.cohomologyFunctor
/- The constant-sheaf/global-sections bridge used below is the adjunction
`constantSheafΓAdj NatSite AddCommGrpCat`. -/
recall constantSheafΓAdj
/- The degree-zero `Ext = Hom` bridge used below is `Abelian.Ext.homEquiv₀`. -/
recall CategoryTheory.Abelian.Ext.homEquiv₀

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the constant sheaf appearing in
`Sheaf.cohomologyFunctor NatSite` is the constant `ULift ℤ` sheaf. -/
private abbrev constantIntegerSheafOnNatSite : Sheaf NatSite AddCommGrpCat :=
  (constantSheaf NatSite AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on `NatSite`, the cohomology owner is
literally the Ext functor from the constant `ULift ℤ` sheaf. -/
theorem cohomologyFunctor_eq_extFunctorObj_constantIntegerSheaf
    (p : ℕ) :
    Sheaf.cohomologyFunctor NatSite p =
      Abelian.extFunctorObj constantIntegerSheafOnNatSite p := by
  -- `Sheaf.cohomologyFunctor` is defined as this Ext functor.
  rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): by the constant-sheaf/global-sections
adjunction, maps from the constant `ULift ℤ` sheaf correspond to maps from `ULift ℤ` into the
global sections object. -/
noncomputable abbrev globalSectionsEquivConstantIntegerSheafHom
    (F : Sheaf NatSite AddCommGrpCat) :
    ((Sheaf.Γ NatSite AddCommGrpCat).obj F) ≃
      (constantIntegerSheafOnNatSite ⟶ F) :=
  ((AddCommGrpCat.coyonedaObjIsoForget.app ((Sheaf.Γ NatSite AddCommGrpCat).obj F)).toEquiv).symm.trans
    ((constantSheafΓAdj NatSite AddCommGrpCat).homEquiv _ F).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): degree-zero sheaf cohomology classes are
ordinary morphisms from the constant `ULift ℤ` sheaf. -/
noncomputable abbrev cohomologyZeroEquivConstantIntegerSheafHom
    (F : Sheaf NatSite AddCommGrpCat) :
    ((Sheaf.cohomologyFunctor NatSite 0).obj F) ≃
      (constantIntegerSheafOnNatSite ⟶ F) := by
  -- Reduce `H^0` to `Ext^0`, then apply the canonical identification `Ext^0 = Hom`.
  simpa [cohomologyFunctor_eq_extFunctorObj_constantIntegerSheaf] using
    (Abelian.Ext.homEquiv₀ :
      Abelian.Ext constantIntegerSheafOnNatSite F 0 ≃
        (constantIntegerSheafOnNatSite ⟶ F))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on the chaotic site of `ℕ`, the source-level
degree-zero comparison `Γ(F) = H^0(F)` is already available as a canonical equivalence of the
underlying carrier types. -/
noncomputable abbrev globalSectionsEquivCohomologyZero
    (F : Sheaf NatSite AddCommGrpCat) :
    ((Sheaf.Γ NatSite AddCommGrpCat).obj F) ≃
      ((Sheaf.cohomologyFunctor NatSite 0).obj F) :=
  (globalSectionsEquivConstantIntegerSheafHom F).trans
    (cohomologyZeroEquivConstantIntegerSheafHom F).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the carrier-level comparison
`Γ(F) ≃ Hom(constantIntegerSheafOnNatSite, F)` is natural in `F`. -/
private theorem globalSectionsEquivConstantIntegerSheafHom_naturality
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (x : (Sheaf.Γ NatSite AddCommGrpCat).obj F) :
    globalSectionsEquivConstantIntegerSheafHom G
        ((Sheaf.Γ NatSite AddCommGrpCat).map f x) =
      globalSectionsEquivConstantIntegerSheafHom F x ≫ f := by
  let eF :=
    (AddCommGrpCat.coyonedaObjIsoForget.app
      ((Sheaf.Γ NatSite AddCommGrpCat).obj F)).toEquiv
  let eG :=
    (AddCommGrpCat.coyonedaObjIsoForget.app
      ((Sheaf.Γ NatSite AddCommGrpCat).obj G)).toEquiv
  have hcorep :
      eG.symm ((Sheaf.Γ NatSite AddCommGrpCat).map f x) =
        eF.symm x ≫ (Sheaf.Γ NatSite AddCommGrpCat).map f := by
    -- First move the section along `Γ.map f` through the corepresentability equivalence.
    have hx :
        AddCommGrpCat.coyonedaObjIsoForget.hom.app
            ((Sheaf.Γ NatSite AddCommGrpCat).obj F) (eF.symm x) = x := by
      exact eF.apply_symm_apply x
    apply eG.injective
    rw [Equiv.apply_symm_apply]
    calc
      (ConcreteCategory.hom ((Sheaf.Γ NatSite AddCommGrpCat).map f)) x =
          (ConcreteCategory.hom ((Sheaf.Γ NatSite AddCommGrpCat).map f))
            (AddCommGrpCat.coyonedaObjIsoForget.hom.app
              ((Sheaf.Γ NatSite AddCommGrpCat).obj F) (eF.symm x)) := by
            rw [hx]
      _ =
          AddCommGrpCat.coyonedaObjIsoForget.hom.app
            ((Sheaf.Γ NatSite AddCommGrpCat).obj G)
            (eF.symm x ≫ (Sheaf.Γ NatSite AddCommGrpCat).map f) := by
            exact
              (congrFun
                (AddCommGrpCat.coyonedaObjIsoForget.hom.naturality
                  ((Sheaf.Γ NatSite AddCommGrpCat).map f))
                (eF.symm x)).symm
  -- Then apply the right naturality of the constant-sheaf/global-sections adjunction.
  change
    ((constantSheafΓAdj NatSite AddCommGrpCat).homEquiv _ G).symm
        (eG.symm ((Sheaf.Γ NatSite AddCommGrpCat).map f x)) =
      ((constantSheafΓAdj NatSite AddCommGrpCat).homEquiv _ F).symm (eF.symm x) ≫ f
  rw [hcorep]
  simpa using
    (constantSheafΓAdj NatSite AddCommGrpCat).homEquiv_naturality_right_symm
      (eF.symm x) f

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the additive hom determined by an element
`x` sends `n` to `n • x`. -/
private theorem ulift_integer_add_hom_map_add
    {A : Type} [AddCommGroup A] (x : A) (m n : ULift ℤ) :
    (m + n).down • x = m.down • x + n.down • x := by
  -- This is the pointwise additivity needed to package `n ↦ n • x` as a morphism.
  simp [add_zsmul]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the explicit `n ↦ n • x` morphism gives the
additive corepresentability of the forgetful functor by `ULift ℤ`. -/
private noncomputable def addCommGrpForgetCorepresentableByULiftInt_additive
    (A : AddCommGrpCat) :
    A ≃+ (AddCommGrpCat.of (ULift ℤ) ⟶ A) where
  toFun x :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun n : ULift ℤ ↦ n.down • x)
        (ulift_integer_add_hom_map_add x)
  invFun f := f (ULift.up 1)
  left_inv x := by
    -- Evaluating the explicit additive hom at `1` recovers the chosen element.
    simp
  right_inv f := by
    -- A morphism out of `ULift ℤ` is determined by the image of `1`.
    ext n
    simpa using (map_zsmul (ConcreteCategory.hom f) n.down (1 : ULift ℤ)).symm
  map_add' := by
    intro x y
    -- Pointwise, `n • (x + y)` is the sum of `n • x` and `n • y`.
    ext z
    simp

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the constant-sheaf functor on `NatSite` is
additive, so the constant-sheaf/global-sections adjunction upgrades to an additive hom
equivalence. -/
local instance constantPresheafNatSite_additive :
    (Functor.const ℕᵒᵖ : AddCommGrpCat ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat)).Additive where
  -- The constant-presheaf functor sends a sum of morphisms to the pointwise sum constant
  -- natural transformation.
  map_add := by
    intro X Y f g
    ext n
    rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the constant-sheaf functor on `NatSite` is
additive, so the constant-sheaf/global-sections adjunction upgrades to an additive hom
equivalence. -/
local instance constantSheafNatSite_additive :
    (constantSheaf NatSite AddCommGrpCat).Additive := by
  -- `constantSheaf` is `Functor.const ⋙ presheafToSheaf`, and both factors are additive.
  dsimp [constantSheaf]
  letI : (presheafToSheaf NatSite AddCommGrpCat).Additive := inferInstance
  infer_instance

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the explicit `ULift ℤ` corepresentability is
natural in the target abelian group. -/
private theorem addCommGrpForgetCorepresentableByULiftInt_additive_naturality
    {A B : AddCommGrpCat} (f : A ⟶ B) (x : A) :
    addCommGrpForgetCorepresentableByULiftInt_additive B (f x) =
      addCommGrpForgetCorepresentableByULiftInt_additive A x ≫ f := by
  -- Both explicit additive homs send `n : ULift ℤ` to `n • f x`.
  ext n
  -- After unfolding the two explicit homs, this is exactly the `zsmul` compatibility of `f`.
  change n.down • f x = f (n.down • x)
  simpa using (map_zsmul (ConcreteCategory.hom f) n.down x).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): global sections on `NatSite` identify
additively with morphisms from the constant `ULift ℤ` sheaf. -/
noncomputable def globalSectionsAddEquivConstantIntegerSheafHom
    (F : Sheaf NatSite AddCommGrpCat) :
    ((Sheaf.Γ NatSite AddCommGrpCat).obj F) ≃+
      (constantIntegerSheafOnNatSite ⟶ F) :=
  -- Compose the explicit `ULift ℤ` corepresentability with the additive adjunction isomorphism.
  (addCommGrpForgetCorepresentableByULiftInt_additive _).trans
    ((constantSheafΓAdj NatSite AddCommGrpCat).homAddEquiv _ F).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the additive `Γ ≅ Hom(constantInteger,-)`
comparison is natural in the sheaf variable. -/
private theorem globalSectionsAddEquivConstantIntegerSheafHom_naturality
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (x : (Sheaf.Γ NatSite AddCommGrpCat).obj F) :
    globalSectionsAddEquivConstantIntegerSheafHom G
        ((Sheaf.Γ NatSite AddCommGrpCat).map f x) =
      globalSectionsAddEquivConstantIntegerSheafHom F x ≫ f := by
  -- Unfold the additive bridge to the explicit `ULift ℤ`-indexed morphism in global sections.
  simp only [globalSectionsAddEquivConstantIntegerSheafHom, AddEquiv.trans_apply]
  rw [addCommGrpForgetCorepresentableByULiftInt_additive_naturality
    ((Sheaf.Γ NatSite AddCommGrpCat).map f) x]
  -- Then move postcomposition along `f` through the inverse adjunction map.
  simpa using
    (constantSheafΓAdj NatSite AddCommGrpCat).homEquiv_naturality_right_symm
      (addCommGrpForgetCorepresentableByULiftInt_additive
        ((Sheaf.Γ NatSite AddCommGrpCat).obj F) x) f

/-- Helper for Remark 15.87.8 (Rlim as cohomology): global sections identify additively with the
degree-zero Ext functor from the constant `ULift ℤ` sheaf. -/
noncomputable def globalSectionsAddEquivExtZeroConstantInteger
    (F : Sheaf NatSite AddCommGrpCat) :
    ((Sheaf.Γ NatSite AddCommGrpCat).obj F) ≃+
      ((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).obj F) :=
  (globalSectionsAddEquivConstantIntegerSheafHom F).trans Abelian.Ext.addEquiv₀.symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on degree-zero Ext, postcomposition by a
sheaf morphism becomes ordinary composition after applying `Ext.addEquiv₀`. -/
private theorem extFunctorObj_zero_map_eq_postcomp
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G) :
    (Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).map f =
      AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero 0)) :=
  rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on degree-zero Ext, postcomposition by a
sheaf morphism becomes ordinary composition after applying `Ext.addEquiv₀`. -/
private theorem ext_zero_addEquiv₀_map
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (e : Abelian.Ext constantIntegerSheafOnNatSite F 0) :
    Abelian.Ext.addEquiv₀
        (((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero 0)) e) =
      Abelian.Ext.addEquiv₀ e ≫ f := by
  obtain ⟨g, hg⟩ := Abelian.Ext.homEquiv₀.symm.surjective e
  -- Replace the degree-zero class by an actual morphism and compute the Yoneda product.
  rw [← hg, Abelian.Ext.homEquiv₀_symm_apply]
  change
    Abelian.Ext.addEquiv₀
        ((Abelian.Ext.mk₀ g).comp (Abelian.Ext.mk₀ f) (add_zero 0)) =
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ f
  rw [Abelian.Ext.mk₀_comp_mk₀]
  -- Finally, `Ext.addEquiv₀` identifies `mk₀ (g ≫ f)` with the composite itself.
  have hg₀ : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  apply Abelian.Ext.homEquiv₀.symm.injective
  simp [Abelian.Ext.homEquiv₀_symm_apply, hg₀]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the additive `Γ ≅ Ext^0(constantInteger,-)`
comparison is natural in the sheaf variable. -/
private theorem globalSectionsAddEquivExtZeroConstantInteger_naturality
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (x : (Sheaf.Γ NatSite AddCommGrpCat).obj F) :
    globalSectionsAddEquivExtZeroConstantInteger G
        ((Sheaf.Γ NatSite AddCommGrpCat).map f x) =
      ((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).map f)
        (globalSectionsAddEquivExtZeroConstantInteger F x) := by
  -- Apply the degree-zero `Ext = Hom` bridge so the target map becomes postcomposition.
  apply Abelian.Ext.addEquiv₀.injective
  -- Compute the left-hand side by cancelling `Ext.addEquiv₀.symm`, then rewrite the right-hand
  -- side by the owner degree-zero postcomposition formula.
  calc
    Abelian.Ext.addEquiv₀
        (globalSectionsAddEquivExtZeroConstantInteger G
          ((Sheaf.Γ NatSite AddCommGrpCat).map f x)) =
      globalSectionsAddEquivConstantIntegerSheafHom G
        ((Sheaf.Γ NatSite AddCommGrpCat).map f x) := by
        simpa [globalSectionsAddEquivExtZeroConstantInteger] using
          (AddEquiv.apply_symm_apply
            (Abelian.Ext.addEquiv₀ :
              Abelian.Ext constantIntegerSheafOnNatSite G 0 ≃+
                (constantIntegerSheafOnNatSite ⟶ G))
            (globalSectionsAddEquivConstantIntegerSheafHom G
              ((Sheaf.Γ NatSite AddCommGrpCat).map f x)))
    _ = globalSectionsAddEquivConstantIntegerSheafHom F x ≫ f := by
        exact globalSectionsAddEquivConstantIntegerSheafHom_naturality f x
    _ = Abelian.Ext.addEquiv₀
          (((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero 0))
            (Abelian.Ext.addEquiv₀.symm
              (globalSectionsAddEquivConstantIntegerSheafHom F x))) := by
        symm
        calc
          Abelian.Ext.addEquiv₀
              (((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero 0))
                (Abelian.Ext.addEquiv₀.symm
                  (globalSectionsAddEquivConstantIntegerSheafHom F x))) =
            Abelian.Ext.addEquiv₀
              (Abelian.Ext.addEquiv₀.symm
                (globalSectionsAddEquivConstantIntegerSheafHom F x)) ≫ f := by
                  exact ext_zero_addEquiv₀_map f
                    (Abelian.Ext.addEquiv₀.symm
                      (globalSectionsAddEquivConstantIntegerSheafHom F x))
          _ = globalSectionsAddEquivConstantIntegerSheafHom F x ≫ f := by
                congr 1
                apply Abelian.Ext.homEquiv₀.symm.injective
                simp [Abelian.Ext.homEquiv₀_symm_apply]
    _ = Abelian.Ext.addEquiv₀
          (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).map f)
            (globalSectionsAddEquivExtZeroConstantInteger F x)) := by
        -- Normalize the degree-zero `Ext` element to `mk₀`, then compute postcomposition by
        -- ordinary composition.
        have hpost :
            ((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero 0))
                (globalSectionsAddEquivExtZeroConstantInteger F x) =
              Abelian.Ext.mk₀
                (globalSectionsAddEquivConstantIntegerSheafHom F x ≫ f) := by
          change
            (((globalSectionsAddEquivConstantIntegerSheafHom F).trans Abelian.Ext.addEquiv₀.symm) x).comp
                (Abelian.Ext.mk₀ f) (add_zero 0) =
              Abelian.Ext.mk₀
                (globalSectionsAddEquivConstantIntegerSheafHom F x ≫ f)
          simpa [globalSectionsAddEquivExtZeroConstantInteger,
            Abelian.Ext.homEquiv₀_symm_apply] using
            (Abelian.Ext.mk₀_comp_mk₀
              (globalSectionsAddEquivConstantIntegerSheafHom F x) f).symm
        simpa [globalSectionsAddEquivExtZeroConstantInteger] using
          congrArg Abelian.Ext.addEquiv₀ hpost.symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): package the source-faithful identity
`Γ ≅ Ext^0(constantIntegerSheafOnNatSite,-)` as a natural isomorphism of additive functors. -/
noncomputable def global_sections_nat_iso_ext_zero_constant_integer :
    Sheaf.Γ NatSite AddCommGrpCat ≅
      Abelian.extFunctorObj constantIntegerSheafOnNatSite 0 :=
  NatIso.ofComponents
    (fun F ↦ (globalSectionsAddEquivExtZeroConstantInteger F).toAddCommGrpIso)
    (fun f ↦ by
      -- Naturality is checked elementwise on global sections using the additive comparison above.
      ext x
      exact globalSectionsAddEquivExtZeroConstantInteger_naturality f x)

/-- Helper for Remark 15.87.8 (Rlim as cohomology): deriving the underived comparison
`Γ ≅ Ext^0(constantIntegerSheafOnNatSite,-)` gives the first half of the cohomology comparison. -/
noncomputable def rightDerivedGlobalSectionsNatSiteIsoRightDerivedExtZeroConstantInteger
    (p : ℕ) :
    ((Sheaf.Γ NatSite AddCommGrpCat).rightDerived p) ≅
      ((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).rightDerived p) := by
  refine
    { hom := NatTrans.rightDerived global_sections_nat_iso_ext_zero_constant_integer.hom p
      inv := NatTrans.rightDerived global_sections_nat_iso_ext_zero_constant_integer.inv p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa using
      (NatTrans.rightDerived_comp
        global_sections_nat_iso_ext_zero_constant_integer.hom
        global_sections_nat_iso_ext_zero_constant_integer.inv
        p).symm
  · simpa using
      (NatTrans.rightDerived_comp
        global_sections_nat_iso_ext_zero_constant_integer.inv
        global_sections_nat_iso_ext_zero_constant_integer.hom
        p).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): transporting a degree-zero cochain complex
across the bottom-topology equivalence inverse is exactly the generic `single₀` transport
isomorphism for `mapHomologicalComplex`. -/
noncomputable def sheafBotEquivalence_inverse_map_single₀_iso
    (A : AbSeq) :
    ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ AbSeq).obj A)) ≅
      (CochainComplex.single₀ (Sheaf NatSite AddCommGrpCat)).obj
        (((sheafBotEquivalence AddCommGrpCat).inverse).obj A) := by
  -- The owner `singleMapHomologicalComplex` already expresses the source proof's controlled
  -- transport of the augmentation object, so we expose its component at `A`.
  exact
    (HomologicalComplex.singleMapHomologicalComplex
      ((sheafBotEquivalence AddCommGrpCat).inverse :
        AbSeq ⥤ Sheaf NatSite AddCommGrpCat)
      (ComplexShape.up ℕ) 0).app A

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the cocomplex obtained by transporting an
injective resolution across the bottom-topology equivalence inverse has the expected terms. -/
private theorem sheafBotEquivalence_inverse_map_cocomplex_X
    {A : AbSeq} (I : InjectiveResolution A) (n : ℕ) :
    ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).X n =
      ((sheafBotEquivalence AddCommGrpCat).inverse.obj (I.cocomplex.X n)) := by
  -- The mapped cocomplex is computed degreewise on objects.
  simp [CategoryTheory.Functor.mapHomologicalComplex_obj_X]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the differentials of the transported
injective-resolution cocomplex are the images of the original differentials. -/
private theorem sheafBotEquivalence_inverse_map_cocomplex_d
    {A : AbSeq} (I : InjectiveResolution A) (i j : ℕ) :
    ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).d i j =
      (sheafBotEquivalence AddCommGrpCat).inverse.map (I.cocomplex.d i j) := by
  -- The mapped cocomplex is computed degreewise on differentials.
  simp [CategoryTheory.Functor.mapHomologicalComplex_obj_d]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): transporting an injective resolution across
the inverse equivalence preserves injectivity termwise. -/
private theorem sheafBotEquivalence_inverse_map_cocomplex_injective
    {A : AbSeq} (I : InjectiveResolution A) (n : ℕ) :
    Injective
      (((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).X n) := by
  -- After rewriting the mapped term, injectivity follows because equivalences preserve
  -- injective objects.
  rw [sheafBotEquivalence_inverse_map_cocomplex_X I n]
  infer_instance

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the transported injective-resolution
cocomplex already carries homology in every degree. -/
private theorem sheafBotEquivalence_inverse_map_cocomplex_hasHomology
    {A : AbSeq} (I : InjectiveResolution A) (n : ℕ) :
    HomologicalComplex.HasHomology
      ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) n := by
  -- The sheaf category is abelian, so homology is available on every cochain complex.
  infer_instance

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the inverse bottom-topology equivalence
preserves homology, so quasi-isomorphisms can be mapped across it. -/
private instance sheafBotEquivalence_inverse_preservesHomology :
    (((sheafBotEquivalence AddCommGrpCat).inverse :
        AbSeq ⥤ Sheaf NatSite AddCommGrpCat).PreservesHomology) := by
  let F :=
    ((sheafBotEquivalence AddCommGrpCat).inverse :
      AbSeq ⥤ Sheaf NatSite AddCommGrpCat)
  -- Exact equivalences preserve finite limits and colimits, so the generic exact-functor owner
  -- provides the needed homology-preservation instance.
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesFiniteColimits F := inferInstance
  exact CategoryTheory.Functor.preservesHomologyOfExact F

/-- Helper for Remark 15.87.8 (Rlim as cohomology): mapping the augmentation of an injective
resolution across the inverse bottom-topology equivalence preserves its quasi-isomorphism. -/
private theorem sheafBotEquivalence_inverse_map_augmentation_quasiIso
    {A : AbSeq} (I : InjectiveResolution A) :
    QuasiIso
      ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
          (ComplexShape.up ℕ)).map I.ι) := by
  let F :=
    ((sheafBotEquivalence AddCommGrpCat).inverse :
      AbSeq ⥤ Sheaf NatSite AddCommGrpCat)
  -- With homology preservation installed once, the owner theorem sends the original
  -- quasi-isomorphism `I.ι` to a quasi-isomorphism of mapped sheaf complexes.
  simpa [F] using
    (HomologicalComplex.quasiIso_map_of_preservesHomology I.ι F)

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after transporting the degree-zero object
across `single₀`, the mapped augmentation is still a quasi-isomorphism. -/
private theorem sheafBotEquivalence_inverse_transported_augmentation_quasiIso
    {A : AbSeq} (I : InjectiveResolution A) :
    QuasiIso
      (((sheafBotEquivalence_inverse_map_single₀_iso A).inv) ≫
        ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
            (ComplexShape.up ℕ)).map I.ι)) := by
  -- The source proof first transports the augmentation object by the `single₀` isomorphism.
  letI : ∀ n,
      HomologicalComplex.HasHomology
        ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) n :=
    sheafBotEquivalence_inverse_map_cocomplex_hasHomology I
  -- The mapped augmentation is already a quasi-isomorphism, and quasi-isomorphisms compose.
  letI :
      QuasiIso
        ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
            (ComplexShape.up ℕ)).map I.ι) :=
    sheafBotEquivalence_inverse_map_augmentation_quasiIso I
  letI : QuasiIso ((sheafBotEquivalence_inverse_map_single₀_iso A).inv) := inferInstance
  exact quasiIso_comp _ _

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the transported sheaf-side cocomplex and
augmentation package into the injective resolution used by the first derived comparison. -/
noncomputable def sheafBotEquivalence_inverse_transported_injectiveResolution
    {A : AbSeq} (I : InjectiveResolution A) :
    InjectiveResolution (((sheafBotEquivalence AddCommGrpCat).inverse).obj A) :=
  { cocomplex :=
      (((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex
    injective := sheafBotEquivalence_inverse_map_cocomplex_injective I
    hasHomology := sheafBotEquivalence_inverse_map_cocomplex_hasHomology I
    ι :=
      ((sheafBotEquivalence_inverse_map_single₀_iso A).inv) ≫
        ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
            (ComplexShape.up ℕ)).map I.ι)
    quasiIso := sheafBotEquivalence_inverse_transported_augmentation_quasiIso I }

/-- Helper for Remark 15.87.8 (Rlim as cohomology): evaluating the right derived functor of
global sections after transporting a sequential inverse system across the bottom-topology
equivalence inverse gives the same degree-`p` homology object as first transporting the chosen
injective resolution and then deriving global sections. -/
noncomputable def sheafBotEquivalence_inverse_rightDerivedGlobalSections_app_iso
    (p : ℕ) (A : AbSeq) :
    ((((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ NatSite AddCommGrpCat).rightDerived p).obj A) ≅
      (((Sheaf.Γ NatSite AddCommGrpCat).rightDerived p).obj
        (((sheafBotEquivalence AddCommGrpCat).inverse).obj A)) := by
  let I : InjectiveResolution A := injectiveResolution A
  let J : InjectiveResolution (((sheafBotEquivalence AddCommGrpCat).inverse).obj A) :=
    sheafBotEquivalence_inverse_transported_injectiveResolution I
  -- Compare both right-derived values to homology of the same transported cocomplex.
  simpa [J, sheafBotEquivalence_inverse_transported_injectiveResolution] using
    (I.isoRightDerivedObj
        ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat)
        p) ≪≫
      (J.isoRightDerivedObj (Sheaf.Γ NatSite AddCommGrpCat) p).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the `desc` morphism between chosen injective
resolutions remains compatible with the transported augmentations after applying the inverse
bottom-topology equivalence. -/
private theorem sheafBotEquivalence_inverse_transported_desc_comm
    {A B : AbSeq} (f : A ⟶ B) :
    let I_A : InjectiveResolution A := injectiveResolution A
    let I_B : InjectiveResolution B := injectiveResolution B
    let J_A : InjectiveResolution (((sheafBotEquivalence AddCommGrpCat).inverse).obj A) :=
      sheafBotEquivalence_inverse_transported_injectiveResolution I_A
    let J_B : InjectiveResolution (((sheafBotEquivalence AddCommGrpCat).inverse).obj B) :=
      sheafBotEquivalence_inverse_transported_injectiveResolution I_B
    let φ :=
      ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (InjectiveResolution.desc f I_B I_A))
    J_A.ι ≫ φ =
      ((CochainComplex.single₀ (Sheaf NatSite AddCommGrpCat)).map
        (((sheafBotEquivalence AddCommGrpCat).inverse).map f)) ≫
        J_B.ι := by
  let E : AbSeq ⥤ Sheaf NatSite AddCommGrpCat :=
    (sheafBotEquivalence AddCommGrpCat).inverse
  let I_A : InjectiveResolution A := injectiveResolution A
  let I_B : InjectiveResolution B := injectiveResolution B
  have hsingle :
      (sheafBotEquivalence_inverse_map_single₀_iso A).inv ≫
          ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((CochainComplex.single₀ AbSeq).map f)) =
        ((CochainComplex.single₀ (Sheaf NatSite AddCommGrpCat)).map (E.map f)) ≫
          (sheafBotEquivalence_inverse_map_single₀_iso B).inv := by
    -- This is the degree-zero transport naturality built into `singleMapHomologicalComplex`.
    simpa [E, sheafBotEquivalence_inverse_map_single₀_iso] using
      ((HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℕ) 0).inv.naturality f).symm
  -- Expand the transported augmentations and move the mapped `desc` across them.
  dsimp [sheafBotEquivalence_inverse_transported_injectiveResolution]
  rw [Category.assoc, ← Functor.map_comp]
  rw [InjectiveResolution.desc_commutes]
  rw [Functor.map_comp]
  simpa using
    congrArg
      (fun η ↦ η ≫ (E.mapHomologicalComplex (ComplexShape.up ℕ)).map I_B.ι)
      hsingle

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after passing to homology, mapping a `desc`
through the composite functor `((sheafBotEquivalence AddCommGrpCat).inverse ⋙ Γ)` is literally
the same as first mapping it through the inverse equivalence and then through `Γ`. -/
private theorem sheafBotEquivalence_inverse_desc_homologyFunctor_map_eq
    {A B : AbSeq} (f : A ⟶ B) (p : ℕ) :
    let I_A : InjectiveResolution A := injectiveResolution A
    let I_B : InjectiveResolution B := injectiveResolution B
    let φ := InjectiveResolution.desc f I_B I_A
    (((((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).comp
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p)).map φ) =
      (((((Sheaf.Γ NatSite AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).comp
          (HomologicalComplex.homologyFunctor AddCommGrpCat
            (ComplexShape.up ℕ) p)).map
          ((((sheafBotEquivalence AddCommGrpCat).inverse).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ))) := by
  -- This is the functorial normalization needed to keep both naturality formulas in the same
  -- codomain when packaging the objectwise comparison into a natural isomorphism.
  rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after rewriting both sides of the naturality
square by `Functor.rightDerived_map_eq`, the remaining comparison is exactly the common homology
map attached to the descended morphism of chosen injective resolutions. -/
private theorem sheafBotEquivalence_inverse_rightDerivedGlobalSections_naturality_assoc
    {A B : AbSeq} (f : A ⟶ B) (p : ℕ) :
    ((((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ NatSite AddCommGrpCat).rightDerived p).map f) ≫
        (sheafBotEquivalence_inverse_rightDerivedGlobalSections_app_iso p B).hom =
      (sheafBotEquivalence_inverse_rightDerivedGlobalSections_app_iso p A).hom ≫
        (((Sheaf.Γ NatSite AddCommGrpCat).rightDerived p).map
          (((sheafBotEquivalence AddCommGrpCat).inverse).map f)) := by
  let E : AbSeq ⥤ Sheaf NatSite AddCommGrpCat :=
    (sheafBotEquivalence AddCommGrpCat).inverse
  let φ :
      (sheafBotEquivalence_inverse_transported_injectiveResolution
        (injectiveResolution A)).cocomplex ⟶
        (sheafBotEquivalence_inverse_transported_injectiveResolution
          (injectiveResolution B)).cocomplex :=
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))
  -- First compute the left-derived map using the descended morphism on the original resolutions.
  rw [Functor.rightDerived_map_eq
    (F := E ⋙ Sheaf.Γ NatSite AddCommGrpCat) (n := p) (f := f)
    (P := injectiveResolution A) (Q := injectiveResolution B)
    (g := InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))
    (w := InjectiveResolution.desc_commutes f
      (injectiveResolution B) (injectiveResolution A))]
  -- Then compute the sheaf-side derived map using the transported descended morphism.
  dsimp [sheafBotEquivalence_inverse_rightDerivedGlobalSections_app_iso, φ, E]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- The middle morphisms coincide because both descriptions are the same composite functor map.
  trans
    ((injectiveResolution A).isoRightDerivedObj
        (((sheafBotEquivalence AddCommGrpCat).inverse) ⋙
          Sheaf.Γ NatSite AddCommGrpCat) p).hom ≫
      ((((Sheaf.Γ NatSite AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).comp
          (HomologicalComplex.homologyFunctor AddCommGrpCat
            (ComplexShape.up ℕ) p)).map φ) ≫
        ((sheafBotEquivalence_inverse_transported_injectiveResolution
            (injectiveResolution B)).isoRightDerivedObj
          (Sheaf.Γ NatSite AddCommGrpCat) p).inv
  · have hmap :=
      sheafBotEquivalence_inverse_desc_homologyFunctor_map_eq (f := f) (p := p)
    have hmap' :
        HomologicalComplex.homologyMap
            ((((sheafBotEquivalence AddCommGrpCat).inverse ⋙
                  Sheaf.Γ NatSite AddCommGrpCat).mapHomologicalComplex
                (ComplexShape.up ℕ)).map
              (InjectiveResolution.desc f (injectiveResolution B)
                (injectiveResolution A))) p =
          HomologicalComplex.homologyMap
            (((Sheaf.Γ NatSite AddCommGrpCat).mapHomologicalComplex
                (ComplexShape.up ℕ)).map φ) p := by
      simpa [Functor.comp_map] using hmap
    rw [hmap']
    rfl
  · simpa [Category.assoc] using
      (InjectiveResolution.isoRightDerivedObj_inv_naturality
          (f := ((sheafBotEquivalence AddCommGrpCat).inverse).map f)
          (I := sheafBotEquivalence_inverse_transported_injectiveResolution
            (injectiveResolution A))
          (J := sheafBotEquivalence_inverse_transported_injectiveResolution
            (injectiveResolution B))
          (φ := φ)
          (comm := by
            simpa using
              (HomologicalComplex.congr_hom
                (sheafBotEquivalence_inverse_transported_desc_comm (f := f)) 0))
          (F := Sheaf.Γ NatSite AddCommGrpCat) (n := p)).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): precomposing global sections on `NatSite`
with the bottom-topology sheaf equivalence inverse commutes with taking fixed-degree right derived
functors. -/
theorem sheafBotEquivalenceInverse_rightDerivedGlobalSections_iso
    (p : ℕ) :
    IsIsomorphic
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        (Sheaf.Γ NatSite AddCommGrpCat).rightDerived p) := by
  -- Route correction: the transported `desc` square and the exact homology-functor transport
  -- normalization are now isolated in
  -- `sheafBotEquivalence_inverse_transported_desc_comm` and
  -- `sheafBotEquivalence_inverse_desc_homologyFunctor_map_eq`.
  refine ⟨NatIso.ofComponents
    (fun A ↦ sheafBotEquivalence_inverse_rightDerivedGlobalSections_app_iso p A)
    (fun f ↦ by
      -- The remaining square is exactly the normalized associativity statement proved above.
      exact sheafBotEquivalence_inverse_rightDerivedGlobalSections_naturality_assoc f p)⟩

/-- Helper for Remark 15.87.8 (Rlim as cohomology): isomorphisms on source and target induce an
additive equivalence on the corresponding Hom groups. -/
private theorem iso_hom_congr_add_equiv_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f g : X ⟶ Y) :
    eX.homCongr eY (f + g) = eX.homCongr eY f + eX.homCongr eY g := by
  -- Additivity is exactly bilinearity of composition inside `Iso.homCongr`.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): isomorphisms on source and target induce an
additive equivalence on the corresponding Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := eX.homCongr eY
  map_add' := iso_hom_congr_add_equiv_map_add eX eY

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on `embeddingUpNat`, the extension functor map
is definitionally the owner-level `extendMap`. -/
private theorem embeddingUpNat_extendFunctor_map_eq_extendMap
    {C D : HomologicalComplex (Sheaf NatSite AddCommGrpCat) (ComplexShape.up ℕ)} (φ : C ⟶ D) :
    ((ComplexShape.embeddingUpNat.extendFunctor (Sheaf NatSite AddCommGrpCat)).map φ) =
      HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat :=
  rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the descended map of injective resolutions
acts on the extended `ℤ`-indexed cochain complexes by the transported degreewise map. -/
private theorem injective_resolution_desc_cochainComplex_map_f
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G) (n : ℕ) :
    (((ComplexShape.embeddingUpNat.extendFunctor (Sheaf NatSite AddCommGrpCat)).map
        (InjectiveResolution.desc f I_G I_F)).f (n : ℤ)) =
      (I_F.cochainComplexXIso (n : ℤ) n rfl).hom ≫
        (InjectiveResolution.desc f I_G I_F).f n ≫
        (I_G.cochainComplexXIso (n : ℤ) n rfl).inv := by
  -- Rewrite the extended descended map to the owner `extendMap`, whose degree-`n` component is
  -- exactly the original cocomplex map conjugated by the canonical transport isomorphisms.
  rw [embeddingUpNat_extendFunctor_map_eq_extendMap]
  simpa using
    (HomologicalComplex.extendMap_f
      (InjectiveResolution.desc f I_G I_F) ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ))
      (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ)))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposing a single-supported cochain by
the extended descended map stays single-supported and only changes the degree-`n` component by
the descended map in that degree. -/
private theorem fromSingleMk_postcomp_desc_cochainComplex
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I_F.cochainComplex.X (n : ℤ)) :
    CochainComplex.HomComplex.Cochain.fromSingleMk
        (g ≫
          (((ComplexShape.embeddingUpNat.extendFunctor
              (Sheaf NatSite AddCommGrpCat)).map
            (InjectiveResolution.desc f I_G I_F)).f (n : ℤ)))
        (by simp : (0 : ℤ) + (n : ℤ) = (n : ℤ)) =
      (CochainComplex.HomComplex.Cochain.fromSingleMk
          g (by simp : (0 : ℤ) + (n : ℤ) = (n : ℤ))).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          ((ComplexShape.embeddingUpNat.extendFunctor
              (Sheaf NatSite AddCommGrpCat)).map
            (InjectiveResolution.desc f I_G I_F)))
        (add_zero (n : ℤ)) := by
  -- This is the owner `fromSingleMk_postcomp` applied to the extended descended cochain map.
  simpa using
    (CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp
      (f := g)
      (h := (by simp : (0 : ℤ) + (n : ℤ) = (n : ℤ)))
      (((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf NatSite AddCommGrpCat)).map
        (InjectiveResolution.desc f I_G I_F))))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposition by a cochain map preserves
the zero cochain in each Hom-complex degree. -/
private theorem full_hom_complex_postcomp_map_zero
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    (0 : CochainComplex.HomComplex.Cochain K L n).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) =
      0 := by
  -- The Hom-complex postcomposition is pointwise composition, so it preserves `0`.
  ext p q hpq
  simp

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposition by a cochain map is additive
on each Hom-complex degree. -/
private theorem full_hom_complex_postcomp_map_add
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain K L n) :
    (z + z').comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) +
        z'.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) := by
  -- Additivity is checked degreewise because Hom-complex cochains are pointwise additive.
  ext p q hpq
  simp

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposition by a cochain map induces the
additive endomorphism on each Hom-complex degree used in the descended naturality square. -/
private def full_hom_complex_postcompAddMonoidHom
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n →+
      CochainComplex.HomComplex.Cochain K M n :=
  { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n)
    map_zero' := full_hom_complex_postcomp_map_zero σ n
    map_add' := full_hom_complex_postcomp_map_add σ n }

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposition by a cochain map commutes
with the Hom-complex differential. -/
private theorem full_hom_complex_postcomp_comm
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (full_hom_complex_postcompAddMonoidHom σ i) ≫
        (CochainComplex.HomComplex K M).d i j =
      (CochainComplex.HomComplex K L).d i j ≫
        AddCommGrpCat.ofHom (full_hom_complex_postcompAddMonoidHom σ j) := by
  -- The owner differential formula `δ_comp_ofHom` gives the cochain-level commutative square.
  ext z
  change
    CochainComplex.HomComplex.δ i j
        (z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero i)) =
      (CochainComplex.HomComplex.δ i j z).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero j)
  simpa only using
    (CochainComplex.HomComplex.δ_comp_ofHom (n := i) z σ j)

/-- Helper for Remark 15.87.8 (Rlim as cohomology): postcomposition by the extended descended map
induces the full `ℤ`-indexed Hom-complex morphism governing the middle square. -/
private def full_hom_complex_postcomp
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K M :=
  { f := fun n ↦ AddCommGrpCat.ofHom (full_hom_complex_postcompAddMonoidHom σ n)
    comm' := full_hom_complex_postcomp_comm σ }

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after whiskering the restricted map induced
by full Hom-complex postcomposition with the canonical `restrictionXIso`, the degree-`n`
component is ordinary postcomposition on the full `ℤ`-indexed Hom complex. -/
private theorem restrictionMap_full_hom_postcomp_component_formula
    {K L M : CochainComplex (Sheaf NatSite AddCommGrpCat) ℤ}
    (σ : L ⟶ M) (n : ℕ) :
    ((HomologicalComplex.restrictionMap (full_hom_complex_postcomp (K := K) σ)
        ComplexShape.embeddingUpNat).f n) ≫
      ((CochainComplex.HomComplex K M).restrictionXIso ComplexShape.embeddingUpNat rfl).hom =
    ((CochainComplex.HomComplex K L).restrictionXIso ComplexShape.embeddingUpNat rfl).hom ≫
      AddCommGrpCat.ofHom (full_hom_complex_postcompAddMonoidHom σ (n : ℤ)) := by
  -- Expand the owner `restrictionMap` component once; after whiskering by `restrictionXIso`, the
  -- remaining map is exactly the full Hom-complex postcomposition map in degree `n`.
  simpa [full_hom_complex_postcomp, Category.assoc] using
    (HomologicalComplex.restrictionMap_f'
      (φ := full_hom_complex_postcomp (K := K) σ)
      (e := ComplexShape.embeddingUpNat)
      (i := n) (i' := (n : ℤ))
      (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ)))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): for a chosen injective resolution, the
degree-`n` term of the mapped degree-zero Ext cocomplex already identifies with the corresponding
degree of the restricted Hom complex. -/
private noncomputable def mapped_ext_zero_cocomplex_X_iso_restricted_hom_X
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ) :
    ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).X n) ≅
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).X n := by
  let hext :
      ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).X n) ≅
        AddCommGrpCat.of (constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) := by
    -- The mapped cocomplex term is definitionally the degree-zero `Ext` object at `I^n`.
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (Abelian.Ext.addEquiv₀
        (X := constantIntegerSheafOnNatSite) (Y := I.cocomplex.X n)).toAddCommGrpIso
  let htransport :
      AddCommGrpCat.of (constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) ≅
        AddCommGrpCat.of (constantIntegerSheafOnNatSite ⟶ I.cochainComplex.X (n : ℤ)) := by
    -- The resolution term in degree `n` is the same object viewed inside the extended
    -- `ℤ`-indexed cochain complex.
    simpa using
      (iso_hom_congr_add_equiv (Iso.refl constantIntegerSheafOnNatSite)
        (I.cochainComplexXIso (n : ℤ) n rfl).symm).toAddCommGrpIso
  let hcochain :
      AddCommGrpCat.of (constantIntegerSheafOnNatSite ⟶ I.cochainComplex.X (n : ℤ)) ≅
        (CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).X (ComplexShape.embeddingUpNat.f n) := by
    -- Degree-`n` cochains from the single complex are literally maps into `I^n`.
    simpa using
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
          (K := I.cochainComplex)
          (X := constantIntegerSheafOnNatSite)
          (p := 0) (q := (n : ℤ)) (n := (n : ℤ))
          (by simp)).symm.toAddCommGrpIso)
  -- Compose the four source-faithful bridges: `Ext^0 = Hom`, transport along the chosen
  -- extension to a `ℤ`-indexed complex, identify degree-`n` cochains, then restrict back.
  exact
    hext ≪≫ htransport ≪≫ hcochain ≪≫
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after forgetting the final restriction
transport, the degreewise `Ext^0 = Hom` comparison sends the generator `Ext.mk₀ g` to the
single-supported cochain determined by `g`. -/
private theorem mapped_ext_zero_component_to_full_hom_apply_mk₀
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) :
    (((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
              constantIntegerSheafOnNatSite)
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp) := by
  let e :
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).X (ComplexShape.embeddingUpNat.f n)) ≃+
        (constantIntegerSheafOnNatSite ⟶ I.cochainComplex.X (n : ℤ)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := constantIntegerSheafOnNatSite)
      (p := 0) (q := (n : ℤ)) (n := (n : ℤ))
      (by simp)
  -- Apply the single-supported cochain equivalence so each factor of the composite can be
  -- simplified independently.
  apply e.injective
  -- `Ext.addEquiv₀` sends `Ext.mk₀ g` back to the morphism `g`.
  have hmk :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    apply Abelian.Ext.homEquiv₀.symm.injective
    simpa using (Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ g))
  -- The source composite is exactly `Ext.addEquiv₀`, transport along `I.cochainComplexXIso`,
  -- and then the inverse of `fromSingleEquiv`.
  calc
    e
        (((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I n).hom ≫
            ((CochainComplex.HomComplex
                ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
                  constantIntegerSheafOnNatSite)
                I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (Abelian.Ext.mk₀ g)) =
      (iso_hom_congr_add_equiv (Iso.refl constantIntegerSheafOnNatSite)
          ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
        (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g)) := by
          simpa [Function.comp, e, mapped_ext_zero_cocomplex_X_iso_restricted_hom_X,
            iso_hom_congr_add_equiv, HomologicalComplex.restrictionXIso] using
            (AddEquiv.apply_symm_apply e
              ((iso_hom_congr_add_equiv (Iso.refl constantIntegerSheafOnNatSite)
                ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
                (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g))))
    _ = g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv := by
          rw [hmk]
          simp [iso_hom_congr_add_equiv]
    _ = e
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp)) := by
          symm
          simpa [e] using
            (AddEquiv.apply_symm_apply e
              (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): on the mapped degree-zero Ext cocomplex,
the successor differential sends the generator `Ext.mk₀ g` to the generator coming from
postcomposition by the cocomplex differential. -/
private theorem mapped_ext_zero_cocomplex_d_apply_mk₀
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) :
    (((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
      (Abelian.Ext.mk₀ g)) =
        Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1)) := by
  have hmk₀_apply {Y : Sheaf NatSite AddCommGrpCat}
      (h : constantIntegerSheafOnNatSite ⟶ Y) :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ h) = h := by
    -- `Ext.addEquiv₀` is inverse to the degree-zero constructor `Ext.mk₀`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  -- Reduce the mapped cocomplex differential to the owner map
  -- `(Abelian.extFunctorObj ... 0).map (I.cocomplex.d n (n + 1))`.
  apply Abelian.Ext.addEquiv₀.injective
  calc
    Abelian.Ext.addEquiv₀
        (((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
          (Abelian.Ext.mk₀ g)) =
      Abelian.Ext.addEquiv₀
        (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).map
            (I.cocomplex.d n (n + 1)))
          (Abelian.Ext.mk₀ g)) := by
          rfl
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ I.cocomplex.d n (n + 1) := by
          exact ext_zero_addEquiv₀_map (f := I.cocomplex.d n (n + 1)) (e := Abelian.Ext.mk₀ g)
    _ = g ≫ I.cocomplex.d n (n + 1) := by rw [hmk₀_apply g]
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1))) := by
          rw [hmk₀_apply (g ≫ I.cocomplex.d n (n + 1))]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after transporting the degree-zero Ext
generator into the full Hom complex, the full differential is computed by the usual
single-supported cochain formula. -/
private theorem mapped_ext_zero_full_hom_d_apply_mk₀
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).d (n : ℤ) ((n + 1 : ℕ) : ℤ))
        ((((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I n).hom ≫
            ((CochainComplex.HomComplex
                ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
                  constantIntegerSheafOnNatSite)
                I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (Abelian.Ext.mk₀ g))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
            I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
        (by simp) := by
  -- First normalize the transported Ext class to the corresponding single-supported cochain.
  rw [mapped_ext_zero_component_to_full_hom_apply_mk₀]
  -- Then the full Hom-complex differential is exactly `δ_fromSingleMk`.
  simpa [Category.assoc] using
    (CochainComplex.HomComplex.Cochain.δ_fromSingleMk
      (K := I.cochainComplex)
      (X := constantIntegerSheafOnNatSite)
      (p := 0)
      (f := g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv)
      (n := (n : ℤ))
      (h := by simp)
      (((n + 1 : ℕ) : ℤ))
      (((n + 1 : ℕ) : ℤ))
      (by simp))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after whiskering the desired differential
square with the successor `restrictionXIso`, the comparison can be checked on the generator
`Ext.mk₀ g`. -/
private theorem mapped_ext_zero_component_d_comm_apply_mk₀
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I.cocomplex.X n) :
    (((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
              constantIntegerSheafOnNatSite)
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1) ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
              constantIntegerSheafOnNatSite)
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) =
      (((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1) ≫
          (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I (n + 1)).hom ≫
          ((CochainComplex.HomComplex
              ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
                constantIntegerSheafOnNatSite)
              I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  -- Expand the restricted differential once so both sides live in the same full Hom complex.
  rw [HomologicalComplex.restriction_d_eq
    (K := K) (e := ComplexShape.embeddingUpNat) (i' := (n : ℤ))
    (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
  simp
  -- The left side is now the full Hom differential of the transported generator.
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
          I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
      (by simp)
  · simpa [K] using mapped_ext_zero_full_hom_d_apply_mk₀ F I n g
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      ((g ≫ I.cocomplex.d n (n + 1)) ≫
        (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
      (by simp)
  · rw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
    simp [Category.assoc]
  trans
    ((((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1)) ≫
        (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I (n + 1)).hom ≫
        (K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
      (Abelian.Ext.mk₀ g))
  · change
      CochainComplex.HomComplex.Cochain.fromSingleMk
          ((g ≫ I.cocomplex.d n (n + 1)) ≫
            (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
          (show (0 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by simp) =
        (((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I (n + 1)).hom ≫
            (K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
            (Abelian.Ext.mk₀ g)))
    rw [mapped_ext_zero_cocomplex_d_apply_mk₀]
    simpa [K, Category.assoc] using
      (mapped_ext_zero_component_to_full_hom_apply_mk₀ F I (n + 1)
        (g ≫ I.cocomplex.d n (n + 1))).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degreewise `Ext^0 = Hom` comparison
intertwines the successor differential of the mapped Ext cocomplex with the successor
differential of the restricted Hom complex. -/
private theorem mapped_ext_zero_cocomplex_component_d_comm
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ) :
    (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
              constantIntegerSheafOnNatSite)
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1) =
      (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1) ≫
        (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I (n + 1)).hom := by
  -- Route correction: the Ext-side generator normalization is now isolated in
  -- `mapped_ext_zero_cocomplex_d_apply_mk₀`, so it remains to cancel the final restriction
  -- isomorphism and check the resulting square on `Ext.mk₀ g`.
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  apply (cancel_mono (K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom).1
  ext e
  obtain ⟨g, hg⟩ := (Abelian.Ext.homEquiv₀.symm.surjective e)
  have hg' : Abelian.Ext.mk₀ g = e := by
    simpa [Abelian.Ext.homEquiv₀_symm_apply] using hg
  rw [← hg']
  simpa [K] using mapped_ext_zero_component_d_comm_apply_mk₀ F I n g



/-- Helper for Remark 15.87.8 (Rlim as cohomology): for a chosen injective resolution, the
mapped degree-zero Ext cocomplex is the restriction of the usual Hom complex from the
degree-zero single complex on `constantIntegerSheafOnNatSite`. -/
private noncomputable def mapped_ext_zero_cocomplex_iso_restricted_hom_complex
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat := by
  -- The source route first upgrades the degreewise `Ext^0 = Hom` identification to a cochain
  -- complex isomorphism. The differential square is isolated in the previous helper.
  refine HomologicalComplex.Hom.isoOfComponents
    (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I) ?_
  intro i j hij
  obtain rfl : j = i + 1 := (ComplexShape.up ℕ).next_eq hij rfl
  exact mapped_ext_zero_cocomplex_component_d_comm F I i

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degreewise map on the mapped degree-zero
Ext cocomplex sends `Ext.mk₀ g` to the class represented by postcomposition with the descended
component. -/
private theorem mapped_ext_zero_cocomplex_map_apply_mk₀
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G) (n : ℕ)
    (g : constantIntegerSheafOnNatSite ⟶ I_F.cocomplex.X n) :
    (((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f I_G I_F)).f n)
      (Abelian.Ext.mk₀ g)) =
        Abelian.Ext.mk₀
          (g ≫ (InjectiveResolution.desc f I_G I_F).f n) := by
  have hmk :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    -- The canonical degree-zero `Ext = Hom` bridge sends `Ext.mk₀ g` back to `g`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    simpa using (Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ g))
  -- The degree-`n` component of the mapped cocomplex map is definitionally `Ext^0` postcompose
  -- by the descended component `(InjectiveResolution.desc f I_G I_F).f n`.
  apply Abelian.Ext.addEquiv₀.injective
  calc
    Abelian.Ext.addEquiv₀
        ((((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc f I_G I_F)).f n)
          (Abelian.Ext.mk₀ g))) =
      Abelian.Ext.addEquiv₀
        (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).map
            ((InjectiveResolution.desc f I_G I_F).f n))
          (Abelian.Ext.mk₀ g)) := by
          rfl
    _ =
        Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫
          (InjectiveResolution.desc f I_G I_F).f n := by
            exact
              ext_zero_addEquiv₀_map
                (f := (InjectiveResolution.desc f I_G I_F).f n)
                (e := Abelian.Ext.mk₀ g)
    _ = g ≫ (InjectiveResolution.desc f I_G I_F).f n := by
          rw [hmk]
    _ =
        Abelian.Ext.addEquiv₀
          (Abelian.Ext.mk₀
            (g ≫ (InjectiveResolution.desc f I_G I_F).f n)) := by
          apply Abelian.Ext.homEquiv₀.symm.injective
          simp [Abelian.Ext.homEquiv₀_symm_apply]

/-- Helper for Remark 15.87.8 (Rlim as cohomology): for a descended morphism of injective
resolutions, the degreewise `Ext^0 = Hom` comparison is already natural at the cochain-complex
level before passing to homology. -/
private theorem mapped_ext_zero_cocomplex_iso_restricted_hom_complex_naturality_of_desc
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G) :
    let φ := InjectiveResolution.desc f I_G I_F
    let σ :=
      ((ComplexShape.embeddingUpNat.extendFunctor (Sheaf NatSite AddCommGrpCat)).map φ)
    let ψr :=
      HomologicalComplex.restrictionMap
        (full_hom_complex_postcomp
          (K := ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite))
          σ)
        ComplexShape.embeddingUpNat
    (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) ≫
        (mapped_ext_zero_cocomplex_iso_restricted_hom_complex G I_G).hom =
      (mapped_ext_zero_cocomplex_iso_restricted_hom_complex F I_F).hom ≫ ψr := by
  let K :=
    ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
      constantIntegerSheafOnNatSite)
  let C_F := CochainComplex.HomComplex K I_F.cochainComplex
  let C_G := CochainComplex.HomComplex K I_G.cochainComplex
  -- Compare both complex morphisms degreewise after whiskering with the target restriction
  -- transport, and only then evaluate on the chosen element.
  ext n
  ext e
  have hwhiskered :
      ((((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f I_G I_F)).f n) ≫
          (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X G I_G n).hom) ≫
          (C_G.restrictionXIso ComplexShape.embeddingUpNat rfl).hom) =
        ((((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I_F n).hom ≫
            (HomologicalComplex.restrictionMap
              (full_hom_complex_postcomp
                (K := K)
                (((ComplexShape.embeddingUpNat.extendFunctor
                    (Sheaf NatSite AddCommGrpCat)).map
                  (InjectiveResolution.desc f I_G I_F))))
              ComplexShape.embeddingUpNat).f n) ≫
            (C_G.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)) := by
    ext x
    obtain ⟨g, hg⟩ := (Abelian.Ext.homEquiv₀.symm.surjective x)
    have hg' : Abelian.Ext.mk₀ g = x := by
      simpa [Abelian.Ext.homEquiv₀_symm_apply] using hg
    rw [← hg']
    -- Normalize both routes to the same single-supported cochain in the full Hom complex.
    calc
      ((((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f I_G I_F)).f n) ≫
          (mapped_ext_zero_cocomplex_X_iso_restricted_hom_X G I_G n).hom ≫
          (C_G.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) =
        CochainComplex.HomComplex.Cochain.fromSingleMk
          (((g ≫ (InjectiveResolution.desc f I_G I_F).f n) ≫
            (I_G.cochainComplexXIso (n : ℤ) n rfl).inv))
          (by simp) := by
            rw [mapped_ext_zero_cocomplex_map_apply_mk₀]
            rw [mapped_ext_zero_component_to_full_hom_apply_mk₀]
      _ =
        CochainComplex.HomComplex.Cochain.fromSingleMk
          (((g ≫ (I_F.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
            (((ComplexShape.embeddingUpNat.extendFunctor
                (Sheaf NatSite AddCommGrpCat)).map
              (InjectiveResolution.desc f I_G I_F)).f (n : ℤ))))
          (by simp) := by
            rw [injective_resolution_desc_cochainComplex_map_f]
            simp [Category.assoc]
      _ =
        (full_hom_complex_postcompAddMonoidHom
            (((ComplexShape.embeddingUpNat.extendFunctor
                (Sheaf NatSite AddCommGrpCat)).map
              (InjectiveResolution.desc f I_G I_F)))
            (n : ℤ))
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (g ≫ (I_F.cochainComplexXIso (n : ℤ) n rfl).inv)
            (by simp)) := by
            simpa [full_hom_complex_postcompAddMonoidHom] using
              (fromSingleMk_postcomp_desc_cochainComplex (f := f) I_F I_G n
                (g := g ≫ (I_F.cochainComplexXIso (n : ℤ) n rfl).inv)).symm
      _ =
        ((((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I_F n).hom ≫
            (C_F.restrictionXIso ComplexShape.embeddingUpNat rfl).hom) ≫
            AddCommGrpCat.ofHom
              (full_hom_complex_postcompAddMonoidHom
                (((ComplexShape.embeddingUpNat.extendFunctor
                    (Sheaf NatSite AddCommGrpCat)).map
                  (InjectiveResolution.desc f I_G I_F)))
                (n : ℤ)))
          (Abelian.Ext.mk₀ g)) := by
            rw [mapped_ext_zero_component_to_full_hom_apply_mk₀]
      _ =
        ((((mapped_ext_zero_cocomplex_X_iso_restricted_hom_X F I_F n).hom ≫
            (HomologicalComplex.restrictionMap
              (full_hom_complex_postcomp
                (K := K)
                (((ComplexShape.embeddingUpNat.extendFunctor
                    (Sheaf NatSite AddCommGrpCat)).map
                  (InjectiveResolution.desc f I_G I_F))))
              ComplexShape.embeddingUpNat).f n) ≫
              (C_G.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (Abelian.Ext.mk₀ g)) := by
            rw [Category.assoc]
            rw [restrictionMap_full_hom_postcomp_component_formula
              (K := K)
              (((ComplexShape.embeddingUpNat.extendFunctor
                  (Sheaf NatSite AddCommGrpCat)).map
                (InjectiveResolution.desc f I_G I_F)))
              n]
            rfl
  exact congrArg (fun t ↦ t e) hwhiskered

/-- Helper for Remark 15.87.8 (Rlim as cohomology): for a chosen injective resolution, the
homology of the mapped degree-zero Ext cocomplex identifies with the homology of the restricted
Hom complex. -/
private noncomputable def mapped_ext_zero_homology_add_equiv_restricted_hom
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).obj
      (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)) ≃+
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology n :=
  -- This is the homology-level form of the already constructed cochain-complex isomorphism.
  (HomologicalComplex.homologyMapIso
    (mapped_ext_zero_cocomplex_iso_restricted_hom_complex F I) n).addCommGroupIsoToAddEquiv

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the cochain-level naturality of the
`Ext^0 = Hom` comparison descends formally to the corresponding homology-level square. -/
private theorem mapped_ext_zero_homology_add_equiv_restricted_hom_naturality_of_desc
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G) (p : ℕ) :
    let φ := InjectiveResolution.desc f I_G I_F
    let σ :=
      ((ComplexShape.embeddingUpNat.extendFunctor (Sheaf NatSite AddCommGrpCat)).map φ)
    let ψr :=
      HomologicalComplex.restrictionMap
        (full_hom_complex_postcomp
          (K := ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite))
          σ)
        ComplexShape.embeddingUpNat
    ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).comp
      (HomologicalComplex.homologyFunctor AddCommGrpCat
        (ComplexShape.up ℕ) p)).map φ) ≫
        (mapped_ext_zero_homology_add_equiv_restricted_hom G I_G p).toAddCommGrpIso.hom =
      (mapped_ext_zero_homology_add_equiv_restricted_hom F I_F p).toAddCommGrpIso.hom ≫
        ((HomologicalComplex.homologyFunctor AddCommGrpCat
          (ComplexShape.up ℕ) p).map ψr) := by
  -- TODO: apply `HomologicalComplex.homologyFunctor` to
  -- `mapped_ext_zero_cocomplex_iso_restricted_hom_complex_naturality_of_desc`, rewrite the image
  -- of each composition via `Functor.map_comp` / `HomologicalComplex.homologyMap_comp`, and then
  -- identify the homology-level isomorphism components with
  -- `mapped_ext_zero_homology_add_equiv_restricted_hom`.
  sorry


/-- Helper for Remark 15.87.8 (Rlim as cohomology): in positive degrees, restricting the full
Hom complex along `embeddingUpNat` does not change homology. -/
private noncomputable def restricted_hom_complex_homology_iso_nat_succ
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (n : ℕ) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology (n + 1) ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).homology (((n + 1 : ℕ) : ℤ)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  -- In successor degree, the predecessor and successor both lie in the image of
  -- `embeddingUpNat`, so the standard restriction homology comparison applies directly.
  simpa [K] using
    (HomologicalComplex.restrictionHomologyIso
      K ComplexShape.embeddingUpNat n (n + 1) (n + 2)
      (by simp) (by simp)
      (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ))
      (by simp : ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ))
      (by norm_num : ComplexShape.embeddingUpNat.f (n + 2) = ((n + 2 : ℕ) : ℤ))
      (by simp)
      (by
        calc
          (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) := by
            simpa using (CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ)))
          _ = ((n + 2 : ℕ) : ℤ) := by omega))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degree-`0` source map of the restricted
Hom short complex is zero. -/
private theorem restricted_hom_complex_sc_zero_f_eq_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    (((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1).f = 0 := by
  let K :=
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex).restriction ComplexShape.embeddingUpNat
  -- At degree `0`, the restricted predecessor is still `0`, so the source map is `d 0 0 = 0`.
  change K.d 0 0 = 0
  simpa [K, CochainComplex.prev] using
    (K.shape 0 0 (by simp : ¬ (ComplexShape.up ℕ).Rel 0 0))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degree-`0` boundary map into cycles for
the restricted Hom short complex vanishes. -/
private theorem restricted_hom_complex_sc_zero_toCycles_eq_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    (((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1).toCycles = 0 := by
  let S :=
    (((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).sc' 0 0 1)
  -- Cancel the mono inclusion of cycles and reduce to the already normalized source map.
  apply (cancel_mono S.iCycles).1
  rw [ShortComplex.toCycles_i, restricted_hom_complex_sc_zero_f_eq_zero]
  symm
  exact
    (CategoryTheory.Limits.zero_comp :
      (0 : S.X₁ ⟶ S.cycles) ≫ S.iCycles = (0 : S.X₁ ⟶ S.X₂))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degree `-1` term of the full Hom complex
vanishes because the injective-resolution cochain complex is zero in negative degrees. -/
private theorem full_hom_complex_neg_one_isZero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    IsZero
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
            constantIntegerSheafOnNatSite)
          I.cochainComplex).X (-1)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  let e :
      K.X (-1) ≃+ (constantIntegerSheafOnNatSite ⟶ I.cochainComplex.X (-1)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := constantIntegerSheafOnNatSite)
      (p := 0) (q := (-1 : ℤ)) (n := (-1 : ℤ))
      (by simp)
  let hneg : IsZero (I.cochainComplex.X (-1)) :=
    CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by omega)
  have hsub_hom : Subsingleton (constantIntegerSheafOnNatSite ⟶ I.cochainComplex.X (-1)) := by
    refine ⟨fun f g ↦ ?_⟩
    exact hneg.eq_of_tgt f g
  have hsub : Subsingleton (K.X (-1)) := by
    refine ⟨fun x y ↦ e.injective ?_⟩
    exact Subsingleton.elim _ _
  -- A subsingleton abelian group object is zero.
  letI : Subsingleton (K.X (-1)) := hsub
  exact AddCommGrpCat.isZero_of_subsingleton (K.X (-1))

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degree-`0` boundary map into cycles for
the full `ℤ`-indexed Hom short complex vanishes because its source object is zero. -/
private theorem full_hom_complex_sc_zero_f_eq_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).sc' (-1) 0 1).f = 0 := by
  let S :=
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).sc' (-1) 0 1)
  let hzero := full_hom_complex_neg_one_isZero F I
  -- The left term is zero, so every map out of it vanishes.
  exact hzero.eq_of_src S.f 0

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the degree-`0` boundary map into cycles for
the full `ℤ`-indexed Hom short complex vanishes because its source object is zero. -/
private theorem full_hom_complex_sc_zero_toCycles_eq_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).sc' (-1) 0 1).toCycles = 0 := by
  let S :=
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).sc' (-1) 0 1)
  let hzero := full_hom_complex_neg_one_isZero F I
  -- Any morphism out of the zero source object is zero, so the boundary map into cycles vanishes.
  exact hzero.eq_of_src S.toCycles 0

/-- Helper for Remark 15.87.8 (Rlim as cohomology): after identifying both degree-`0` cycle
objects with kernels of the same outgoing differential, restricting the full Hom complex to
nonnegative degrees does not change the degree-`0` cycles. -/
private noncomputable def restricted_hom_complex_cycles_iso_nat_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).cycles 0 ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).cycles (0 : ℤ) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let Sr : ShortComplex AddCommGrpCat := Kr.sc' 0 0 1
  let Sf : ShortComplex AddCommGrpCat := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp [CochainComplex.prev]
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Expand the restricted differential once so both cycle objects become kernels of the same
    -- full Hom differential.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpNat) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Compare both degree-`0` cycle objects through the kernel of the common outgoing
  -- differential `K.d 0 1`.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): in the full `ℤ`-indexed Hom complex, the
degree-`0` homology is already represented by degree-`0` cycles because the predecessor
differential vanishes. -/
private noncomputable def full_hom_complex_cycles_to_homology_iso_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex).cycles (0 : ℤ) ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).homology (0 : ℤ) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  let S : ShortComplex AddCommGrpCat := K.sc' (-1) 0 1
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  let inv : S.homology ⟶ S.cycles :=
    S.descHomology (𝟙 S.cycles) (by
      -- The predecessor differential is zero, so the identity on cycles descends to homology.
      simpa [S] using full_hom_complex_sc_zero_toCycles_eq_zero F I)
  have hπinv : S.homologyπ ≫ inv = 𝟙 S.cycles := by
    -- This is the defining computation rule for `descHomology`.
    exact
      ShortComplex.π_descHomology (S := S) (k := 𝟙 S.cycles)
        (hk := by simpa [S] using full_hom_complex_sc_zero_toCycles_eq_zero F I)
  let eShort : S.cycles ≅ S.homology :=
    { hom := S.homologyπ
      inv := inv
      hom_inv_id := hπinv
      inv_hom_id := by
        -- Since `homologyπ` is epi, the defining left inverse is also a right inverse.
        apply (cancel_epi S.homologyπ).1
        calc
          S.homologyπ ≫ (inv ≫ S.homologyπ) = (S.homologyπ ≫ inv) ≫ S.homologyπ := by
            simp [Category.assoc]
          _ = 𝟙 S.cycles ≫ S.homologyπ := by rw [hπinv]
          _ = S.homologyπ := by simp
          _ = S.homologyπ ≫ 𝟙 S.homology := by simp }
  -- Move from the ambient degree-`0` cycles and homology to the owner short complex once, then
  -- use the explicit short-complex isomorphism above.
  exact
    (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK) ≪≫
      eShort ≪≫
      (K.homologyIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): in degree `0`, the restricted Hom complex and
the full `ℤ`-indexed Hom complex have the same homology. -/
private noncomputable def restricted_hom_complex_homology_iso_nat_zero
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology 0 ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
          constantIntegerSheafOnNatSite)
        I.cochainComplex).homology (0 : ℤ) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
        constantIntegerSheafOnNatSite)
      I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let hCycles := restricted_hom_complex_cycles_iso_nat_zero F I
  let eπr : Kr.homology 0 ≅ Kr.cycles 0 := (CochainComplex.isoHomologyπ₀ Kr).symm
  have hzero_prev : K.d (-1) 0 = 0 := by
    -- The full predecessor differential vanishes because the degree `-1` term is zero.
    exact (full_hom_complex_neg_one_isZero F I).eq_of_src _ _
  let eπf : K.cycles (0 : ℤ) ≅ K.homology (0 : ℤ) :=
    K.isoHomologyπ (-1) 0 (by simp) hzero_prev
  -- Route correction: use the canonical `isoHomologyπ` owner on both sides so the remaining
  -- naturality proof can reuse `homologyπ`-based transport instead of the custom descent model.
  exact eπr ≪≫ hCycles ≪≫ eπf

/-- Helper for Remark 15.87.8 (Rlim as cohomology): for a chosen injective resolution, the
homology of the mapped degree-zero Ext cocomplex identifies with the Ext group in degree `p`. -/
private noncomputable def homology_mapped_ext_zero_constant_integer_equiv
    (F : Sheaf NatSite AddCommGrpCat) (I : InjectiveResolution F) (p : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
      (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)) ≃+
      Abelian.Ext constantIntegerSheafOnNatSite F p := by
  -- Route correction: compute mapped `Ext^0` homology by comparing it degreewise with the full
  -- `ℤ`-indexed Hom complex used by `InjectiveResolution.extAddEquivCohomologyClass`.
  cases p with
  | zero =>
      -- In degree `0`, compare mapped `Ext^0` homology to restricted Hom homology, then use the
      -- dedicated degree-`0` restricted/full Hom bridge before applying the canonical Ext owner.
      exact
        (mapped_ext_zero_homology_add_equiv_restricted_hom F I 0).trans <|
          (restricted_hom_complex_homology_iso_nat_zero F I).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
                  constantIntegerSheafOnNatSite)
                I.cochainComplex 0).symm).symm
  | succ n =>
      -- In successor degree, the standard restriction-homology comparison applies directly.
      exact
        (mapped_ext_zero_homology_add_equiv_restricted_hom F I (n + 1)).trans <|
          (restricted_hom_complex_homology_iso_nat_succ F I n).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((CochainComplex.singleFunctor (Sheaf NatSite AddCommGrpCat) 0).obj
                  constantIntegerSheafOnNatSite)
                I.cochainComplex (n + 1)).symm).symm

/-- Helper for Remark 15.87.8 (Rlim as cohomology): objectwise, the `p`-th right derived functor
of `Ext^0(constantIntegerSheafOnNatSite,-)` agrees with `Ext^p(constantIntegerSheafOnNatSite,-)`.
-/
private noncomputable def rightDerived_ext_zero_constant_integer_app_iso
    (F : Sheaf NatSite AddCommGrpCat) (p : ℕ) :
    ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).rightDerived p).obj F) ≅
      ((Abelian.extFunctorObj constantIntegerSheafOnNatSite p).obj F)) := by
  let I : InjectiveResolution F := injectiveResolution F
  -- Compute the derived value on the chosen injective resolution, then apply the objectwise
  -- Ext-computation equivalence.
  exact
    (I.isoRightDerivedObj (Abelian.extFunctorObj constantIntegerSheafOnNatSite 0) p) ≪≫
      (homology_mapped_ext_zero_constant_integer_equiv F I p).toAddCommGrpIso

/-- Helper for Remark 15.87.8 (Rlim as cohomology): in every degree, the map of the Ext owner
functor is the canonical postcomposition map on Ext classes. -/
private theorem extFunctorObj_map_eq_postcomp
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G) (p : ℕ) :
    (Abelian.extFunctorObj constantIntegerSheafOnNatSite p).map f =
      AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero p)) := by
  -- The Ext-functor owner is defined by the degree-`p` postcomposition map.
  rfl

/-- Helper for Remark 15.87.8 (Rlim as cohomology): once the derived map is rewritten using a
chosen descended morphism of injective resolutions, the outer wrapper closes from the middle
homology square alone. -/
private theorem rightDerived_ext_zero_constant_integer_app_iso_naturality_of_middle
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G) (p : ℕ)
    (I_F : InjectiveResolution F) (I_G : InjectiveResolution G)
    (φ : I_F.cocomplex ⟶ I_G.cocomplex)
    (hφ :
      I_F.ι ≫ φ =
        ((CochainComplex.single₀ (Sheaf NatSite AddCommGrpCat)).map f) ≫ I_G.ι)
    (hmid :
      ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).comp
        (HomologicalComplex.homologyFunctor AddCommGrpCat
          (ComplexShape.up ℕ) p)).map φ) ≫
          (homology_mapped_ext_zero_constant_integer_equiv G I_G p).toAddCommGrpIso.hom =
        (homology_mapped_ext_zero_constant_integer_equiv F I_F p).toAddCommGrpIso.hom ≫
          AddCommGrpCat.ofHom
            ((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero p))) :
    (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).rightDerived p).map f) ≫
        (((I_G.isoRightDerivedObj
            (Abelian.extFunctorObj constantIntegerSheafOnNatSite 0) p)) ≪≫
          (homology_mapped_ext_zero_constant_integer_equiv G I_G p).toAddCommGrpIso).hom =
      (((I_F.isoRightDerivedObj
          (Abelian.extFunctorObj constantIntegerSheafOnNatSite 0) p)) ≪≫
        (homology_mapped_ext_zero_constant_integer_equiv F I_F p).toAddCommGrpIso).hom ≫
        ((Abelian.extFunctorObj constantIntegerSheafOnNatSite p).map f) := by
  -- First rewrite the derived map through the chosen descended morphism `φ`.
  rw [Functor.rightDerived_map_eq
    (F := Abelian.extFunctorObj constantIntegerSheafOnNatSite 0) (n := p) (f := f)
    (P := I_F) (Q := I_G) (g := φ) (w := hφ)]
  -- Then the common `isoRightDerivedObj` factor cancels, leaving exactly the middle square.
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- Precompose the middle square by the common left factor.
  simpa [Category.assoc, extFunctorObj_map_eq_postcomp] using
    congrArg
      (fun k ↦ (I_F.isoRightDerivedObj
        (Abelian.extFunctorObj constantIntegerSheafOnNatSite 0) p).hom ≫ k)
      hmid

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the objectwise comparison between
`R^p(Ext^0(constantIntegerSheafOnNatSite,-))` and `Ext^p(constantIntegerSheafOnNatSite,-)` is
natural in the sheaf variable. -/
private theorem rightDerived_ext_zero_constant_integer_app_iso_naturality
    {F G : Sheaf NatSite AddCommGrpCat} (f : F ⟶ G) (p : ℕ) :
    (((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).rightDerived p).map f) ≫
        (rightDerived_ext_zero_constant_integer_app_iso G p).hom =
      (rightDerived_ext_zero_constant_integer_app_iso F p).hom ≫
        ((Abelian.extFunctorObj constantIntegerSheafOnNatSite p).map f) := by
  let I_F : InjectiveResolution F := injectiveResolution F
  let I_G : InjectiveResolution G := injectiveResolution G
  let φ := InjectiveResolution.desc f I_G I_F
  -- Route correction: the outer `rightDerived_map_eq` wrapper is now isolated in
  -- `rightDerived_ext_zero_constant_integer_app_iso_naturality_of_middle`, so the only
  -- remaining blocker is the normalized middle homology square for the descended morphism `φ`.
  have hmid :
      ((((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).comp
        (HomologicalComplex.homologyFunctor AddCommGrpCat
          (ComplexShape.up ℕ) p)).map φ) ≫
          (homology_mapped_ext_zero_constant_integer_equiv G I_G p).toAddCommGrpIso.hom =
        (homology_mapped_ext_zero_constant_integer_equiv F I_F p).toAddCommGrpIso.hom ≫
          AddCommGrpCat.ofHom
            ((Abelian.Ext.mk₀ f).postcomp constantIntegerSheafOnNatSite (add_zero p)) := by
    -- Split the comparison into the boundary degree `0` and the successor degrees, because only
    -- degree `0` needs the special restricted/full Hom bridge.
    cases p with
    | zero =>
        -- TODO: use the new `restrictionMap_full_hom_postcomp_component_formula` to normalize
        -- the first leg, then prove the degree-`0` cycles/homology square and the
        -- `extAddEquivCohomologyClass` tail for `φ := InjectiveResolution.desc f I_G I_F`.
        sorry
    | succ n =>
        -- TODO: combine the first-leg normalization above with the standard
        -- `restricted_hom_complex_homology_iso_nat_succ` comparison and the common
        -- `extAddEquivCohomologyClass` tail in degree `n + 1`.
        sorry
  -- With the normalized middle square in hand, the outer right-derived naturality is formal.
  simpa [rightDerived_ext_zero_constant_integer_app_iso, I_F, I_G, φ] using
    rightDerived_ext_zero_constant_integer_app_iso_naturality_of_middle
      (f := f) (p := p) I_F I_G φ
      (InjectiveResolution.desc_commutes f I_G I_F) hmid

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the right derived functors of
`Ext^0(constantIntegerSheafOnNatSite,-)` identify with the higher Ext functors from the same
constant sheaf. -/
private theorem rightDerivedExtZeroConstantInteger_iso_extFunctorObj
    (p : ℕ) :
    IsIsomorphic
      ((Abelian.extFunctorObj constantIntegerSheafOnNatSite 0).rightDerived p)
      (Abelian.extFunctorObj constantIntegerSheafOnNatSite p) := by
  refine ⟨NatIso.ofComponents
    (fun F ↦ rightDerived_ext_zero_constant_integer_app_iso F p)
    (fun f ↦ by
      -- Naturality is exactly the normalized owner-level square proved above.
      exact rightDerived_ext_zero_constant_integer_app_iso_naturality f p)⟩

/-- Helper for Remark 15.87.8 (Rlim as cohomology): the right derived functors of global sections
on `NatSite` agree with the Ext-defined sheaf-cohomology functors. -/
theorem rightDerivedGlobalSectionsNatSite_iso_cohomologyFunctor
    (p : ℕ) :
    IsIsomorphic
      ((Sheaf.Γ NatSite AddCommGrpCat).rightDerived p)
      (Sheaf.cohomologyFunctor NatSite p) := by
  -- Route correction: `Sheaf.cohomologyFunctor` is definitionally
  -- `Abelian.extFunctorObj ((constantSheaf NatSite AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) p`,
  -- so the missing owner-level step is to compare the right derived functor of `Γ` with the
  -- represented `Ext` functor from the constant `ULift ℤ` sheaf. The concrete source-faithful
  -- route is now narrowed to upgrading the proved set-level bridges
  -- `globalSectionsEquivConstantIntegerSheafHom`,
  -- `cohomologyZeroEquivConstantIntegerSheafHom`, and
  -- `globalSectionsEquivCohomologyZero`
  -- to additive, degreewise natural isomorphisms on an injective resolution, then combine that
  -- with `InjectiveResolution.extEquivCohomologyClass` on the same complex.
  -- The underived half is now packaged by
  -- `global_sections_nat_iso_ext_zero_constant_integer`, so only the owner-level comparison
  -- `R^p(Ext^0(constantIntegerSheafOnNatSite,-)) ≅ Ext^p(constantIntegerSheafOnNatSite,-)`
  -- remains.
  let eΓ := rightDerivedGlobalSectionsNatSiteIsoRightDerivedExtZeroConstantInteger p
  rcases rightDerivedExtZeroConstantInteger_iso_extFunctorObj p with ⟨eExt⟩
  -- Compose the derived `Γ`/`Ext^0` comparison with the higher-Ext identification and the
  -- definitional rewrite of sheaf cohomology.
  exact ⟨eΓ ≪≫ eExt ≪≫ eqToIso
    (by rw [cohomologyFunctor_eq_extFunctorObj_constantIntegerSheaf])⟩

/-- Bridge/view companion for Remark 15.87.8: the `p`-th right derived functor of inverse limit is
canonically isomorphic to the `p`-th right derived functor of global sections of the corresponding
sheaf on the chaotic site of `ℕ`. -/
noncomputable def rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite
    (p : ℕ) :
    ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p) ≅
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ NatSite AddCommGrpCat).rightDerived p) := by
  refine
    { hom := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.symm.hom p
      inv := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.hom p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        naturalNumbersSiteInverseΓIsoLim.hom
        p).symm
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.hom
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        p).symm

/-- Bridge/view companion for Remark 15.87.8: after identifying a sequential inverse system of
abelian groups with its sheaf on the chaotic site of `ℕ`, the right derived functors of global
sections agree with the canonical sheaf-cohomology owner `Sheaf.cohomologyFunctor NatSite`. -/
theorem rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology
    (p : ℕ) :
    IsIsomorphic
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  rcases sheafBotEquivalenceInverse_rightDerivedGlobalSections_iso p with ⟨eΓ⟩
  rcases rightDerivedGlobalSectionsNatSite_iso_cohomologyFunctor p with ⟨eH⟩
  -- First move the right derived functor past the bottom-topology equivalence inverse.
  -- Then whisker the sheaf-side comparison with that inverse to reach the target functor.
  exact ⟨eΓ ≪≫ Functor.isoWhiskerLeft (sheafBotEquivalence AddCommGrpCat).inverse eH⟩

/-- Remark 15.87.8, functor form: the `p`-th right derived functor of inverse limit on sequential
inverse systems of abelian groups is canonically isomorphic to the `p`-th sheaf cohomology functor
of the associated sheaf on the chaotic site of `ℕ`. -/
@[stacks 091A]
theorem rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology
    (p : ℕ) :
    IsIsomorphic
      ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  rcases rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology p with ⟨e⟩
  exact ⟨rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite p ≪≫ e⟩

/-- Remark 15.87.8, source-facing object form: for a sequential inverse system `A` of abelian
groups, the object `R^p lim(A)` is canonically isomorphic to the sheaf cohomology
`H^p(\mathbf N, \mathcal F_A)` of the corresponding sheaf on the chaotic site of `ℕ`. -/
@[stacks 091A]
theorem rightDerivedLimitObj_isIsomorphic_toNaturalNumbersSiteCohomology
    (A : AbSeq) (p : ℕ) :
    IsIsomorphic
      (R^p lim(A))
      ((Sheaf.cohomologyFunctor NatSite p).obj
        ((sheafBotEquivalence AddCommGrpCat).inverse.obj A)) := by
  rcases rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology p with ⟨e⟩
  exact ⟨e.app A⟩
