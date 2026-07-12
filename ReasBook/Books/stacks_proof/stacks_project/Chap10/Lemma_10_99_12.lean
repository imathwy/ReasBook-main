import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_2
import StacksProject_2024.Chap10.Lemma_10_75_5
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Lemma_10_82_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

section

variable {R R' R'' S : Type u}
variable [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
variable [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
variable [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " S ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R S))

/-- Helper for Lemma 10.99.12: in an abelian category with projective resolutions, the chosen
projective-resolution functor is additive because the lift of `f + g` is homotopic to the sum of
the chosen lifts of `f` and `g`. -/
private lemma projective_resolutions_additive (C : Type u) [Category C] [Abelian C]
    [HasProjectiveResolutions C] :
    Functor.Additive (projectiveResolutions C) := by
  constructor
  intro X Y f g
  -- Compare the chosen lift of `f + g` with the sum of the chosen lifts in the homotopy category.
  change
    (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y)) =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y)) +
        (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y))
  rw [← Functor.map_add]
  -- Two lifts of the same morphism are homotopic, so they coincide in the homotopy category.
  exact
    HomotopyCategory.eq_of_homotopy _ _
      (ProjectiveResolution.liftHomotopy (f + g)
        (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y))
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
          ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y))
        (by simp)
        (by simp [Preadditive.comp_add, Preadditive.add_comp]))

/-- Helper for Lemma 10.99.12: left-derived functors of additive functors remain additive, since
their projective-resolution presentation and the homology functor are both additive. -/
private lemma left_derived_additive {C : Type u} [Category C] [Abelian C]
    [HasProjectiveResolutions C] (F : C ⥤ C) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := by
  -- Unfold the left-derived functor into the additive projective-resolution stage followed by
  -- additive homology on the homotopy category.
  let _ : Functor.Additive (projectiveResolutions C) := projective_resolutions_additive C
  dsimp [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

/-- Helper for Lemma 10.99.12: the right-variable `Tor₁` functor for a fixed left argument is
additive, so its map on endomorphisms respects zero and addition. -/
private lemma tor_right_functor_additive :
    Functor.Additive (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))) := by
  -- `Tor₁` is the first left-derived functor of tensoring on the left by `M`, so the additive
  -- structure comes from the additive resolution/homology presentation above.
  simpa [Tor] using
    (left_derived_additive
      ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)) 1)

/-- Helper for Lemma 10.99.12: the coefficient ring acts on `Tor₁^R(M, S)` through the
right-variable `Tor` functor applied to multiplication endomorphisms of `S`. -/
private noncomputable def torOneActionEnd :
    S →+* Module.End R (Tor₁[R](M, S)) := by
  let F := ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))
  let eS : End (ModuleCat.of R S) ≃+* Module.End R (ModuleCat.of R S) :=
    (ModuleCat.of R S).endRingEquiv
  let eT : End (Tor₁[R](M, S)) ≃+* Module.End R (Tor₁[R](M, S)) :=
    (Tor₁[R](M, S)).endRingEquiv
  refine
    { toFun := fun s ↦ eT <| F.map (eS.symm (Module.toModuleEnd R S s)),
      map_one' := by
        -- The scalar `1` acts through the identity endomorphism, and `Tor` preserves identities.
        have hone : eS.symm (Module.toModuleEnd R S (1 : S)) = 1 := by
          simpa using congrArg eS.symm (RingHom.map_one (Module.toModuleEnd R S))
        have hmapone :
            F.map (𝟙 (ModuleCat.of R S)) = 𝟙 (F.obj (ModuleCat.of R S)) := by
          simp using ((CategoryTheory.Functor.mapEnd (f := F) (X := ModuleCat.of R S)).map_one)
        rw [hone]
        change eT (F.map (𝟙 (ModuleCat.of R S))) = 1
        rw [hmapone]
        change eT (1 : End (F.obj (ModuleCat.of R S))) = 1
        rw [eT.map_one]
      map_mul' := by
        intro x y
        -- Multiplication of scalars matches composition of multiplication endomorphisms.
        have hmul :
            eS.symm (Module.toModuleEnd R S (x * y)) =
              eS.symm (Module.toModuleEnd R S x) * eS.symm (Module.toModuleEnd R S y) := by
          simpa using congrArg eS.symm ((Module.toModuleEnd R S).map_mul x y)
        let fx : End (F.obj (ModuleCat.of R S)) :=
          F.map (eS.symm (Module.toModuleEnd R S x))
        let fy : End (F.obj (ModuleCat.of R S)) :=
          F.map (eS.symm (Module.toModuleEnd R S y))
        have hmapmul :
            (F.map (eS.symm (Module.toModuleEnd R S (x * y))) :
                End (F.obj (ModuleCat.of R S))) =
              fx * fy := by
          rw [hmul]
          simp [fx, fy] using
            ((CategoryTheory.Functor.mapEnd (f := F) (X := ModuleCat.of R S)).map_mul
              (eS.symm (Module.toModuleEnd R S x))
              (eS.symm (Module.toModuleEnd R S y)))
        exact congrArg eT hmapmul
      map_zero' := by
        letI : F.Additive := tor_right_functor_additive (R := R) (M := M)
        -- Additivity gives the zero morphism comparison after transporting through `endRingEquiv`.
        have hzero : eS.symm (Module.toModuleEnd R S (0 : S)) = 0 := by
          simpa using congrArg eS.symm (RingHom.map_zero (Module.toModuleEnd R S))
        have hmapzero : F.map (eS.symm (Module.toModuleEnd R S (0 : S))) = 0 := by
          rw [hzero]
          exact Functor.map_zero F (ModuleCat.of R S) (ModuleCat.of R S)
        rw [hmapzero]
        change eT (0 : End (F.obj (ModuleCat.of R S))) = 0
        rw [eT.map_zero]
      map_add' := by
        intro x y
        letI : F.Additive := tor_right_functor_additive (R := R) (M := M)
        -- The scalar-addition law is inherited from additivity of the right-variable `Tor` functor.
        have hadd :
            eS.symm (Module.toModuleEnd R S (x + y)) =
              eS.symm (Module.toModuleEnd R S x) + eS.symm (Module.toModuleEnd R S y) := by
          simpa using congrArg eS.symm ((Module.toModuleEnd R S).map_add x y)
        have hmapadd :
            F.map (eS.symm (Module.toModuleEnd R S x) + eS.symm (Module.toModuleEnd R S y)) =
              F.map (eS.symm (Module.toModuleEnd R S x)) +
                F.map (eS.symm (Module.toModuleEnd R S y)) := by
          exact
            (Functor.map_add (F := F)
              (f := eS.symm (Module.toModuleEnd R S x))
              (g := eS.symm (Module.toModuleEnd R S y)))
        rw [hadd, hmapadd]
        exact eT.map_add _ _ }

/-- Helper for Lemma 10.99.12: the theorem statement views `Tor₁^R(M, S)` as an `S`-module, so
we temporarily package that action via `torOneActionEnd`. -/
private noncomputable instance torOneModule :
    Module S (Tor₁[R](M, S)) := by
  let _ : Module (Module.End R (Tor₁[R](M, S))) (Tor₁[R](M, S)) := inferInstance
  let f : S →+* Module.End R (Tor₁[R](M, S)) := torOneActionEnd
  simpa using (Module.compHom (Tor₁[R](M, S)) f : Module S (Tor₁[R](M, S)))

/-- Helper for Chap10 Lemma 10 99 12: `Module.toModuleEnd` acts on an element by literal scalar
multiplication. -/
private theorem moduleToModuleEnd_apply
    {A : Type u} [CommRing A] {X : Type u} [AddCommGroup X] [Module A X]
    (a : A) (x : X) :
    Module.toModuleEnd A X a x = a • x :=
  rfl

/-- Helper for Chap10 Lemma 10 99 12: the temporary `T`-module structure on `Tor₁^R(M,T)` acts
through the public Tor map induced by multiplication on the coefficient ring. -/
private theorem torOne_smul_eq_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T) (x : Tor₁[R](M, T)) :
    t • x =
      ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          ((ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t))).hom x) := by
  -- Proof comment: this is exactly how the temporary `T`-action on the public Tor module was
  -- defined, so the scalar action is evaluation of the mapped endomorphism.
  change (torOneActionEnd (R := R) (M := M) (S := T) t) x = _
  rfl

local notation "Tor₁Obj[" R "](" M ", " S ")" =>
  (ModuleCat.of S (Tor₁[R](M, S)))
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R' R'')
local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R' R'')

private noncomputable instance torOneBaseChangeTargetModule :
    Module R' (Tor₁[R](M, R'')) :=
  Module.compHom (Tor₁[R](M, R'')) (algebraMap R' R'')

private noncomputable instance torOneBaseChangeSourceModule :
    Module R' ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  Module.compHom _ (algebraMap R' R'')

/-- Helper for Lemma 10.99.12: a projective object of `ModuleCat` yields the usual module-theoretic
projectivity on its underlying module. -/
private lemma module_projective_of_categorical_projective
    {A : Type u} [CommRing A] {X : Type u} [AddCommGroup X] [Module A X]
    (hX : Projective (ModuleCat.of A X)) :
    Module.Projective A X := by
  -- Translate the categorical lifting property against epimorphisms into the ordinary module
  -- lifting property against surjective linear maps.
  letI : Small.{u} A := small_self A
  refine Module.Projective.of_lifting_property ?_
  intro M N _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of A X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.99.12: the scalar-extension functor along `R → R'`. -/
private noncomputable abbrev scalar_extension_functor : ModuleCat R ⥤ ModuleCat R' :=
  ModuleCat.extendScalars (algebraMap R R')

/-- Helper for Lemma 10.99.12: the fixed source projective resolution of `M` before scalar
extension. -/
private noncomputable abbrev scalar_extended_source_resolution :
    CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
  CategoryTheory.projectiveResolution (ModuleCat.of R M)

/-- Helper for Lemma 10.99.12: the degree-`n` term of the scalar-extended fixed source
resolution. -/
private noncomputable abbrev scalar_extended_resolution_X (n : ℕ) : ModuleCat R' :=
  (scalar_extension_functor (R := R) (R' := R')).obj
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)

/-- Helper for Lemma 10.99.12: the scalar-extended differential `F₁' ⟶ F₀'`. -/
private noncomputable abbrev scalar_extended_d_one :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 ⟶
      scalar_extended_resolution_X (R := R) (R' := R') (M := M) 0 :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0)

/-- Helper for Lemma 10.99.12: the scalar-extended differential `F₂' ⟶ F₁'`. -/
private noncomputable abbrev scalar_extended_d_two :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 2 ⟶
      scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1)

/-- Helper for Lemma 10.99.12: the scalar-extended augmentation `F₀' ⟶ M ⊗[R] R'`. -/
private noncomputable abbrev scalar_extended_pi_zero :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 0 ⟶
      (scalar_extension_functor (R := R) (R' := R')).obj (ModuleCat.of R M) :=
  (scalar_extension_functor (R := R) (R' := R')).map
    ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0)

/-- Helper for Lemma 10.99.12: the scalar-extended lower differential still composes to zero with
the scalar-extended augmentation. -/
private theorem scalar_extended_d_one_comp_pi_zero :
    scalar_extended_d_one (R := R) (R' := R') (M := M) ≫
        scalar_extended_pi_zero (R := R) (R' := R') (M := M) =
      0 := by
  -- Map the original augmentation relation through scalar extension.
  have hzero :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0) ≫
          ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0) =
        0 :=
    CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero
      (P := scalar_extended_source_resolution (R := R) (M := M))
  have hmap_zero :
      (scalar_extension_functor (R := R) (R' := R')).map
          (0 :
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1) ⟶
              ModuleCat.of R M) =
        0 := by
    simpa using
      (Functor.map_zero (F := scalar_extension_functor (R := R) (R' := R'))
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)
        (ModuleCat.of R M))
  rw [scalar_extended_d_one, scalar_extended_pi_zero, ← Functor.map_comp]
  exact
    (congrArg ((scalar_extension_functor (R := R) (R' := R')).map) hzero).trans
      hmap_zero

/-- Helper for Lemma 10.99.12: the scalar-extended degree-two and degree-one differentials still
compose to zero. -/
private theorem scalar_extended_d_two_comp_d_one :
    scalar_extended_d_two (R := R) (R' := R') (M := M) ≫
        scalar_extended_d_one (R := R) (R' := R') (M := M) =
      0 := by
  -- Map the original `d₂ ≫ d₁ = 0` relation through scalar extension.
  have hzero :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1) ≫
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0) =
        0 :=
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d_comp_d 2 1 0)
  have hmap_zero :
      (scalar_extension_functor (R := R) (R' := R')).map
          (0 :
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2) ⟶
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)) =
        0 := by
    simpa using
      (Functor.map_zero (F := scalar_extension_functor (R := R) (R' := R'))
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0))
  rw [scalar_extended_d_two, scalar_extended_d_one, ← Functor.map_comp]
  exact
    (congrArg ((scalar_extension_functor (R := R) (R' := R')).map) hzero).trans
      hmap_zero

/-- Helper for Chap10 Lemma 10 99 12: the scalar-extended degree-one source window
`F₂' ⟶ F₁' ⟶ F₀'` whose homology computes the source-proof model of `Tor₁`. -/
private noncomputable abbrev scalarExtendedDegreeOneWindow :
    ShortComplex (ModuleCat R') :=
  -- This packages the already mapped relation `d₂' ≫ d₁' = 0` so later comparison lemmas can
  -- state homology maps without repeating the three-term complex.
  ShortComplex.mk
    (scalar_extended_d_two (R := R) (R' := R') (M := M))
    (scalar_extended_d_one (R := R) (R' := R') (M := M))
    (scalar_extended_d_two_comp_d_one (R := R) (R' := R') (M := M))

/-- Helper for Chap10 Lemma 10 99 12: extending a fixed source-resolution term from `R` to `R'`
and then to `R''` is canonically the same as extending it directly from `R` to `R''`. -/
private noncomputable abbrev scalarExtendedResolutionBaseChangeIso (n : ℕ) :
    (extScalars).obj (scalar_extended_resolution_X (R := R) (R' := R') (M := M) n) ≅
      scalar_extended_resolution_X (R := R) (R' := R'') (M := M) n :=
  -- This is the term-level scalar-extension composition bridge; later window/homology maps should
  -- rewrite through this instead of unfolding tensor-product carriers repeatedly.
  ((ModuleCat.extendScalarsComp (algebraMap R R') (algebraMap R' R'')).app
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)).symm ≪≫
    (eqToIso
      (congrArg (fun f : R →+* R'' ↦ ModuleCat.extendScalars f)
        (IsScalarTower.algebraMap_eq R R' R'').symm)).app
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)

/-- Helper for Chap10 Lemma 10 99 12: the termwise scalar-extension base-change isomorphisms
are natural in maps between terms of the fixed source resolution. -/
private theorem scalarExtendedResolutionBaseChangeIso_hom_naturality {n m : ℕ}
    (d :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ⟶
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m)) :
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) n).hom ≫
        (scalar_extension_functor (R := R) (R' := R'')).map d =
      (extScalars).map ((scalar_extension_functor (R := R) (R' := R')).map d) ≫
        (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) m).hom := by
  let compIso := ModuleCat.extendScalarsComp (algebraMap R R') (algebraMap R' R'')
  let hFunctor :
      ModuleCat.extendScalars ((algebraMap R' R'').comp (algebraMap R R')) =
        ModuleCat.extendScalars (algebraMap R R'') :=
    congrArg (fun f : R →+* R'' ↦ ModuleCat.extendScalars f)
      (IsScalarTower.algebraMap_eq R R' R'').symm
  let directIso : ModuleCat.extendScalars ((algebraMap R' R'').comp (algebraMap R R')) ≅
      ModuleCat.extendScalars (algebraMap R R'') :=
    eqToIso hFunctor
  -- First move across the equality of scalar-extension functors, then across the composition
  -- isomorphism. This keeps both transports at the functor level where naturality applies.
  simpa [scalarExtendedResolutionBaseChangeIso, directIso, compIso, hFunctor,
    scalar_extension_functor, Category.assoc] using
    (calc
      compIso.inv.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ≫
          directIso.hom.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ≫
            (ModuleCat.extendScalars (algebraMap R R'')).map d =
        compIso.inv.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ≫
          ((ModuleCat.extendScalars ((algebraMap R' R'').comp (algebraMap R R'))).map d ≫
            directIso.hom.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m)) := by
          rw [directIso.hom.naturality]
      _ =
        (compIso.inv.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ≫
            (ModuleCat.extendScalars ((algebraMap R' R'').comp (algebraMap R R'))).map d) ≫
          directIso.hom.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m) := by
          rw [Category.assoc]
      _ =
        ((extScalars).map ((scalar_extension_functor (R := R) (R' := R')).map d) ≫
            compIso.inv.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m)) ≫
          directIso.hom.app ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m) := by
          rw [← compIso.inv.naturality]
          rfl)

/-- Helper for Chap10 Lemma 10 99 12: the termwise scalar-extension bridge is compatible with
the two differentials in the degree-one source window. -/
private theorem scalarExtendedDegreeOneWindowBaseChangeIso_nonempty :
    Nonempty
      ((scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).map extScalars ≅
        scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)) := by
  -- Package the three termwise scalar-extension isomorphisms and pay the differential
  -- naturality/coherence transport once at the short-complex boundary.
  refine ⟨ShortComplex.isoMk
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 2)
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1)
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 0)
    ?_ ?_⟩
  · -- The first square is the scalar-extension composition naturality square for `d₂`.
    simpa [scalarExtendedDegreeOneWindow, scalar_extended_d_two,
      scalar_extended_resolution_X, scalar_extension_functor, scalar_extended_source_resolution]
      using
        (scalarExtendedResolutionBaseChangeIso_hom_naturality
          (R := R) (R' := R') (R'' := R'') (M := M)
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1))
  · -- The second square is the same scalar-extension composition naturality square for `d₁`.
    simpa [scalarExtendedDegreeOneWindow, scalar_extended_d_one,
      scalar_extended_resolution_X, scalar_extension_functor, scalar_extended_source_resolution]
      using
        (scalarExtendedResolutionBaseChangeIso_hom_naturality
          (R := R) (R' := R') (R'' := R'') (M := M)
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0))

/-- Helper for Chap10 Lemma 10 99 12: the scalar-extended degree-one source window over `R'`,
after base change to `R''`, is canonically isomorphic to the degree-one source window over `R''`. -/
private noncomputable abbrev scalarExtendedDegreeOneWindowBaseChangeIso :
    (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).map extScalars ≅
      scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M) :=
  Classical.choice
    (scalarExtendedDegreeOneWindowBaseChangeIso_nonempty
      (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Lemma 10.99.12: after extending scalars on the fixed projective resolution of `M`,
the lower window `F₁' ⟶ F₀' ⟶ M ⊗[R] R'` is still exact and surjective at the augmentation. -/
private theorem scalar_extended_augmentation_exact :
    (ShortComplex.mk
        (scalar_extended_d_one (R := R) (R' := R') (M := M))
        (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
        (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))).Exact ∧
      Epi (scalar_extended_pi_zero (R := R) (R' := R') (M := M)) := by
  let P := scalar_extended_source_resolution (R := R) (M := M)
  let F := scalar_extension_functor (R := R) (R' := R')
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
          (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))) := by
    -- Map the original cokernel presentation through scalar extension; as a left adjoint it
    -- preserves the cokernel witnessing exactness at degree `0`.
    simpa [scalar_extended_pi_zero, scalar_extended_d_one_comp_pi_zero, scalar_extended_d_one,
      scalar_extension_functor, scalar_extended_source_resolution] using
      CokernelCofork.mapIsColimit (c := P.cokernelCofork) P.isColimitCokernelCofork F
  refine ⟨?_, ?_⟩
  · -- Exactness of the scalar-extended lower window is exactly the mapped cokernel statement.
    exact ShortComplex.exact_of_g_is_cokernel _ hColim
  · -- The same mapped cokernel exhibits the scalar-extended augmentation as an epimorphism.
    exact epi_of_isColimit_cofork hColim

/-- Helper for Chap10 Lemma 10 99 12: every scalar-extended term of the fixed projective
resolution of `M` is flat over the extended scalar ring. -/
private theorem scalarExtendedResolutionTermFlat (n : ℕ) :
    Module.Flat R' (scalar_extended_resolution_X (R := R) (R' := R') (M := M) n) := by
  -- Scalar extension is a left adjoint whose right adjoint preserves epimorphisms, hence it sends
  -- the projective terms of the chosen resolution to projective `R'`-modules.
  have hProjCat :
      Projective (scalar_extended_resolution_X (R := R) (R' := R') (M := M) n) := by
    simpa [scalar_extended_resolution_X, scalar_extension_functor,
      scalar_extended_source_resolution] using
      (Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R R'))).projective_obj
        ((scalar_extended_source_resolution (R := R) (M := M)).projective n)
  have hProjMod :
      Module.Projective R'
        (scalar_extended_resolution_X (R := R) (R' := R') (M := M) n) :=
    module_projective_of_categorical_projective hProjCat
  -- Projective modules are flat, so this supplies the middle flat term in the kernel row.
  letI : Module.Projective R'
      (scalar_extended_resolution_X (R := R) (R' := R') (M := M) n) := hProjMod
  exact Module.Flat.of_projective

section

variable [Module.Flat R' (TensorProduct R R' M)]

/-- Helper for Chap10 Lemma 10 99 12: the scalar-extension wrapper of `M` is flat over `R'`
whenever the textbook tensor product `R' ⊗[R] M` is flat. -/
private theorem scalarExtendedBaseModuleFlat :
    Module.Flat R' ((scalar_extension_functor (R := R) (R' := R')).obj (ModuleCat.of R M)) := by
  -- The first tensor factor in `ModuleCat.extendScalars` is the restriction-of-scalars wrapper of
  -- `R'`; we record the scalar tower needed by the heterobasic tensor congruence.
  have hTower :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) := by
    constructor
    intro r s x
    calc
      (r • s) • x = ((algebraMap R R') r * s) • x := by
        simp [Algebra.smul_def]
      _ = (algebraMap R R' r) • (s • x) := by
        rw [smul_smul]
      _ = r • (s • x) := by
        change (algebraMap R R' r) • (s • x) = (algebraMap R R' r) • (s • x)
        rfl
  letI :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) := hTower
  let eFirst :
      ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
    LinearEquiv.refl R' R'
  let eSecond : ↑(ModuleCat.of R M) ≃ₗ[R] M := LinearEquiv.refl R M
  let eTensor :
      (↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ⊗[R]
          ↑(ModuleCat.of R M)) ≃ₗ[R'] TensorProduct R R' M :=
    TensorProduct.AlgebraTensorModule.congr (R := R) (A := R') eFirst eSecond
  -- Transport flatness across the canonical equivalence from the implementation wrapper to the
  -- textbook tensor product appearing in the hypothesis.
  exact Module.Flat.of_linearEquiv (R := R') (M := TensorProduct R R' M) <| by
    simpa [scalar_extension_functor, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      eTensor

/-- Helper for Chap10 Lemma 10 99 12: the lower kernel row
`0 ⟶ ker(π₀') ⟶ F₀' ⟶ M ⊗[R] R' ⟶ 0` is universally exact over `R'`. -/
private theorem scalarExtendedAugmentationKernelUniversallyExact :
    (LinearMap.shortComplexKer
      (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).UniversallyExact := by
  -- Start from the already mapped augmentation row, whose epimorphism gives the kernel short
  -- exact sequence used in the source proof.
  have hSurj :
      Function.Surjective (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom := by
    exact (ModuleCat.epi_iff_surjective _).mp
      (scalar_extended_augmentation_exact (R := R) (R' := R') (M := M)).2
  have hShort :
      (LinearMap.shortComplexKer
        (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).ShortExact :=
    LinearMap.shortExact_shortComplexKer hSurj
  have hRight :
      Module.Flat R'
        (LinearMap.shortComplexKer
          (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).X₃ := by
    -- The right term is the scalar-extension wrapper of `M`, flat by the textbook hypothesis.
    simpa [LinearMap.shortComplexKer, scalar_extended_pi_zero] using
      (scalarExtendedBaseModuleFlat (R := R) (R' := R') (M := M))
  letI :
      Module.Flat R'
        (LinearMap.shortComplexKer
          (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).X₃ := hRight
  -- A short exact row with flat right term is universally exact.
  exact ShortComplex.ShortExact.universallyExact_of_flat_X₃ hShort

/-- Helper for Chap10 Lemma 10 99 12: after tensoring by `R''`, the inclusion
`ker(π₀') ⟶ F₀'` remains injective. -/
private theorem tensorizedLowerKernelSubtype_injective :
    Function.Injective
      ((((LinearMap.ker
        (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).subtype).rTensor R'')) := by
  -- Universal exactness is precisely the stable injectivity of the first map under right tensor.
  simpa [LinearMap.shortComplexKer] using
    (rTensor_f_injective_of_universallyExact
      (S :=
        LinearMap.shortComplexKer
          (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom)
      (scalarExtendedAugmentationKernelUniversallyExact
        (R := R) (R' := R') (M := M))
      R'')

/-- Helper for Lemma 10.99.12: the lower kernel `B' = ker(F₀' ⟶ M ⊗[R] R')` is flat over `R'`.
This is the exact place where the source hypothesis on `M ⊗[R] R'` enters the proof. -/
private theorem source_window_lower_kernel_flat :
    Module.Flat R' (LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom) := by
  let K := LinearMap.shortComplexKer
    (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom
  have hSurj :
      Function.Surjective (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom := by
    -- The scalar-extended augmentation is an epimorphism, hence surjective as a module map.
    exact (ModuleCat.epi_iff_surjective _).mp
      (scalar_extended_augmentation_exact (R := R) (R' := R') (M := M)).2
  have hShort : K.ShortExact := LinearMap.shortExact_shortComplexKer hSurj
  have hMiddle : Module.Flat R' K.X₂ := by
    -- The middle term is the degree-zero scalar-extended projective resolution term.
    simpa [K, LinearMap.shortComplexKer] using
      (scalarExtendedResolutionTermFlat (R := R) (R' := R') (M := M) 0)
  have hRight : Module.Flat R' K.X₃ := by
    -- The right term is the scalar-extension wrapper of `M`, already transported from the
    -- textbook flatness hypothesis.
    simpa [K, LinearMap.shortComplexKer, scalar_extended_pi_zero] using
      (scalarExtendedBaseModuleFlat (R := R) (R' := R') (M := M))
  letI : Module.Flat R' K.X₂ := hMiddle
  letI : Module.Flat R' K.X₃ := hRight
  have hU : K.UniversallyExact :=
    ShortComplex.ShortExact.universallyExact_of_flat_X₃ hShort
  have hKernel : Module.Flat R' K.X₁ := UniversallyExact.flat_X₁ hU
  -- The first object of the kernel short complex is exactly the kernel of the augmentation.
  simpa [K, LinearMap.shortComplexKer] using hKernel

/-- Helper for Lemma 10.99.12: the image of the scalar-extended differential `d₁'` lands in the
lower kernel `B' = ker(F₀' ⟶ M ⊗[R] R')`. -/
private theorem scalar_extended_d_one_mem_lower_kernel :
    ∀ x : scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1,
      (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom x ∈
        LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom := by
  intro x
  -- Evaluate the already-proved composition identity on the chosen element.
  change
    (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom
        ((scalar_extended_d_one (R := R) (R' := R') (M := M)).hom x) = 0
  simpa using
    DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))) x

/-- Helper for Lemma 10.99.12: the scalar-extended lower window
`F₁' ⟶ F₀' ⟶ M ⊗[R] R'` viewed as a short complex. -/
private noncomputable abbrev source_window_lower_shortComplex :
    ShortComplex (ModuleCat R') :=
  ShortComplex.mk
    (scalar_extended_d_one (R := R) (R' := R') (M := M))
    (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
    (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: the source-proof cod-restricted map `F₁' ⟶ B'`, where
`B' = ker(F₀' ⟶ M ⊗[R] R')`. -/
private noncomputable abbrev source_window_upper_to_lower_kernel :
    scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1 ⟶
      (source_window_lower_shortComplex (R := R) (R' := R') (M := M)).moduleCatLeftHomologyData.K :=
  (source_window_lower_shortComplex (R := R) (R' := R') (M := M)).moduleCatLeftHomologyData.liftK
    (scalar_extended_d_one (R := R) (R' := R') (M := M))
    (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: replacing `d₁'` by its cod-restriction to `B'` does not change the
kernel, so the source cycles object is still `K' = ker(d₁')`. -/
private theorem source_window_upper_to_lower_kernel_ker_eq :
    LinearMap.ker (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom =
      LinearMap.ker (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom := by
  -- The upper map is just `d₁'` cod-restricted into the lower kernel, so its kernel is unchanged.
  simpa [source_window_upper_to_lower_kernel, source_window_lower_shortComplex] using
    LinearMap.ker_codRestrict
      (LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom)
      (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom
      (scalar_extended_d_one_mem_lower_kernel (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: the cod-restricted upper map `F₁' ⟶ B'` is surjective because
exactness at `F₀'` identifies `B'` with the image of `d₁'`. -/
private theorem source_window_upper_to_lower_kernel_surjective :
    Function.Surjective
      (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom := by
  have hExact :
      (source_window_lower_shortComplex (R := R) (R' := R') (M := M)).Exact :=
    (scalar_extended_augmentation_exact (R := R) (R' := R') (M := M)).1
  have hRange :
      LinearMap.range (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom =
        LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom := by
    -- Exactness of the lower source window identifies `B'` with the image of `d₁'`.
    simpa [source_window_lower_shortComplex] using hExact.moduleCat_range_eq_ker
  intro y
  have hy :
      y.1 ∈ LinearMap.range (scalar_extended_d_one (R := R) (R' := R') (M := M)).hom := by
    rw [hRange]
    exact y.2
  rcases LinearMap.mem_range.mp hy with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- The canonical `liftK` map is just the cod-restriction of `d₁'` into the kernel subtype.
  show (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom x = y
  apply Subtype.ext
  dsimp [source_window_upper_to_lower_kernel, source_window_lower_shortComplex]
  exact hx

/-- Helper for Lemma 10.99.12: the source-proof upper row
`0 → K' → F₁' → B' → 0` is short exact after scalar extension to `R'`. -/
private theorem source_window_upper_shortExact :
    (LinearMap.shortComplexKer
      (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).ShortExact := by
  -- The cod-restricted upper map is surjective, so its kernel short complex is short exact.
  exact
    LinearMap.shortExact_shortComplexKer
      (source_window_upper_to_lower_kernel_surjective (R := R) (R' := R') (M := M))

/-- Helper for Lemma 10.99.12: tensoring the source-proof upper row on the right by `R''` keeps
the pair `K' ⊗[R'] R'' → F₁' ⊗[R'] R'' → B' ⊗[R'] R''` exact. This is the quotient-level part of
the textbook argument that does not yet use the comparison `B' ⊗[R'] R'' ≅ ker(π₀'')`. -/
private theorem tensorized_source_window_upper_exact :
    Function.Exact
      (((LinearMap.ker
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype).rTensor
        R'')
      (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'') := by
  have hExact :
      Function.Exact
        (LinearMap.ker
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype
        (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom := by
    -- Rewrite the already-constructed short exact row into the `LinearMap.Exact` API.
    simpa [LinearMap.shortComplexKer] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (LinearMap.shortComplexKer
          (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom)).mp
        (source_window_upper_shortExact (R := R) (R' := R') (M := M)).exact
  have hSurj :
      Function.Surjective
        (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom :=
    source_window_upper_to_lower_kernel_surjective (R := R) (R' := R') (M := M)
  -- Right exactness of tensor product carries the upper short exact row to the tensorized row.
  exact rTensor_exact R'' hExact hSurj

/-- Helper for Lemma 10.99.12: after tensoring the source-proof upper row with `R''`, the image of
`K' ⊗[R'] R'' → F₁' ⊗[R'] R''` is exactly the kernel of
`F₁' ⊗[R'] R'' → B' ⊗[R'] R''`. -/
private theorem tensorized_source_window_upper_range_eq_ker :
    LinearMap.range
        ((((LinearMap.ker
            (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype).rTensor
          R'')) =
      LinearMap.ker
        (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'') := by
  -- This is the range-kernel form of the exactness statement recorded above.
  exact
    (LinearMap.exact_iff.mp
      (tensorized_source_window_upper_exact (R := R) (R' := R') (R'' := R'') (M := M))).symm

/-- Helper for Chap10 Lemma 10 99 12: the scalar-extended inclusion of source cycles maps to
cycles in the target scalar-extended degree-one window. -/
private theorem sourceWindowTensorCyclesMap_zero :
    (extScalars).map
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).iCycles ≫
        (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1).hom ≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).g =
      0 := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e₁ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1
  let e₀ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 0
  have hnat :
      e₁.hom ≫ W₂.g = (extScalars).map W₁.g ≫ e₀.hom := by
    -- The target differential is the direct scalar extension of the source differential, so the
    -- termwise base-change square for `d₁` is the required comparison.
    simpa [W₁, W₂, e₁, e₀, scalarExtendedDegreeOneWindow, scalar_extended_d_one,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (scalarExtendedResolutionBaseChangeIso_hom_naturality
        (R := R) (R' := R') (R'' := R'') (M := M)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0))
  calc
    (extScalars).map W₁.iCycles ≫ e₁.hom ≫ W₂.g =
        (extScalars).map W₁.iCycles ≫ ((extScalars).map W₁.g ≫ e₀.hom) := by
          rw [hnat]
    _ = ((extScalars).map (W₁.iCycles ≫ W₁.g)) ≫ e₀.hom := by
          rw [← Category.assoc, ← Functor.map_comp]
    _ = 0 := by
          -- Source cycles compose trivially with the source lower differential.
          rw [W₁.iCycles_g, Functor.map_zero, zero_comp]

/-- Helper for Chap10 Lemma 10 99 12: the canonical map
`(K' ⊗[R'] R'') ⟶ K''` on abstract cycles of the scalar-extended source windows. -/
private noncomputable abbrev sourceWindowTensorCyclesMap :
    (extScalars).obj
        (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).cycles ⟶
      (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).cycles :=
  (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).liftCycles
    ((extScalars).map
        (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).iCycles ≫
      (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1).hom)
    (sourceWindowTensorCyclesMap_zero (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Chap10 Lemma 10 99 12: after forgetting from target cycles, the abstract cycle map
is the termwise scalar-extension base-change morphism in degree one. -/
private theorem sourceWindowTensorCyclesMap_iCycles :
    sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).iCycles =
      (extScalars).map
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).iCycles ≫
        (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1).hom := by
  -- This is the computation rule for `ShortComplex.liftCycles`.
  simp [sourceWindowTensorCyclesMap]

/-- Helper for Chap10 Lemma 10 99 12: the tensorized cycle map carries source boundaries to
target boundaries. -/
private theorem sourceWindowTensorCyclesMap_comp_boundaries :
    (extScalars).map
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).toCycles ≫
        sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) =
      (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).toCycles := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e₂ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 2
  let e₁ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1
  have hnat :
      e₂.hom ≫ W₂.f = (extScalars).map W₁.f ≫ e₁.hom := by
    -- This is the termwise base-change square for the upper differential `d₂`.
    simpa [W₁, W₂, e₂, e₁, scalarExtendedDegreeOneWindow, scalar_extended_d_two,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (scalarExtendedResolutionBaseChangeIso_hom_naturality
        (R := R) (R' := R') (R'' := R'') (M := M)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1))
  apply W₂.cycles_ext
  calc
    ((extScalars).map W₁.toCycles ≫
          sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)) ≫
        W₂.iCycles =
        (extScalars).map W₁.toCycles ≫
          (sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫
            W₂.iCycles) := by
          rw [Category.assoc]
    _ = (extScalars).map W₁.toCycles ≫ ((extScalars).map W₁.iCycles ≫ e₁.hom) := by
          rw [sourceWindowTensorCyclesMap_iCycles]
    _ = ((extScalars).map (W₁.toCycles ≫ W₁.iCycles)) ≫ e₁.hom := by
          rw [← Category.assoc, ← Functor.map_comp]
    _ = (extScalars).map W₁.f ≫ e₁.hom := by
          rw [W₁.toCycles_i]
    _ = e₂.hom ≫ W₂.f := hnat.symm
    _ = (e₂.hom ≫ W₂.toCycles) ≫ W₂.iCycles := by
          rw [Category.assoc, W₂.toCycles_i]

/-- Helper for Chap10 Lemma 10 99 12: a surjective tensorized map on source-window cycles
descends to a surjective map on the corresponding scalar-extended homology quotient. -/
private theorem sourceWindowBaseChangeHomologyComparison_surjective_of_cycles
    (hcycles :
      Function.Surjective
        (sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)).hom) :
    ∃ comparison :
        (extScalars).obj
          (ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) ⟶
          ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)),
      Function.Surjective comparison.hom := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let k := sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)
  let sourceCofork := CokernelCofork.ofπ W₁.homologyπ W₁.toCycles_comp_homologyπ
  have hColim : IsColimit (sourceCofork.map extScalars) := by
    -- Scalar extension is a left adjoint, so it preserves the cokernel presenting source homology.
    exact CokernelCofork.mapIsColimit (c := sourceCofork) W₁.homologyIsCokernel extScalars
  have hkill : (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) = 0 := by
    -- Boundary compatibility says tensorized boundaries become target boundaries, which vanish in
    -- the target homology cokernel.
    calc
      (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) =
          ((extScalars).map W₁.toCycles ≫ k) ≫ W₂.homologyπ := by
            rw [Category.assoc]
      _ = ((scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫ W₂.toCycles) ≫
            W₂.homologyπ := by
            rw [sourceWindowTensorCyclesMap_comp_boundaries]
      _ = (scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫
            (W₂.toCycles ≫ W₂.homologyπ) := by
            rw [Category.assoc]
      _ = 0 := by
            rw [W₂.toCycles_comp_homologyπ, comp_zero]
  let comparison :
      (extScalars).obj W₁.homology ⟶ W₂.homology :=
    hColim.desc (CokernelCofork.ofπ (k ≫ W₂.homologyπ) hkill)
  refine ⟨comparison, ?_⟩
  -- Lift a target homology class to a target cycle, lift that cycle through the cycle map, and
  -- then project the lifted source cycle to the mapped source homology quotient.
  have hπ₂ : Function.Surjective W₂.homologyπ.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  intro y
  obtain ⟨z, hz⟩ := hπ₂ y
  obtain ⟨x, hx⟩ := hcycles z
  refine ⟨((extScalars).map W₁.homologyπ).hom x, ?_⟩
  have hfac :
      (extScalars).map W₁.homologyπ ≫ comparison = k ≫ W₂.homologyπ := by
    simpa [comparison, sourceCofork] using
      hColim.fac (CokernelCofork.ofπ (k ≫ W₂.homologyπ) hkill) WalkingParallelPair.one
  calc
    comparison.hom (((extScalars).map W₁.homologyπ).hom x) =
        ((k ≫ W₂.homologyπ).hom x) := by
          change ((extScalars).map W₁.homologyπ ≫ comparison).hom x =
            (k ≫ W₂.homologyπ).hom x
          exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hfac) x
    _ = y := by
          change W₂.homologyπ.hom (k.hom x) = y
          rw [hx, hz]

/-- Helper for Lemma 10.99.12: the `2 → 1 → 0` window of the coefficient-tensored projective
resolution of `X` over `R`. This isolates the exact textbook complex used to compute `Tor₁`. -/
private noncomputable abbrev tensorRight_degree_one_window
    (A X : ModuleCat R) : ShortComplex (ModuleCat R) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).obj
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution X)))

/-- Helper for Lemma 10.99.12: degree-one homology of the coefficient-tensored projective
resolution is canonically the homology of its `2 → 1 → 0` window. -/
private noncomputable def tensorRight_degree_one_window_homology_iso
    (A X : ModuleCat R) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
      (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryTheory.ProjectiveResolution.complex
          (CategoryTheory.projectiveResolution X))) ≅
      ShortComplex.homology (tensorRight_degree_one_window (R := R) A X) :=
  -- The standard `homologyFunctorIso'` API turns the full degree-one homology computation into
  -- the explicit three-term window used in the source proof.
  (HomologicalComplex.homologyFunctorIso' (C := ModuleCat R) (c := ComplexShape.down ℕ)
      (i := 2) (j := 1) (k := 0) (by simp) (by simp)).app
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution X)))

/-- Helper for Chap10 Lemma 10 99 12: the fixed-left source owner
`X ↦ Tor'ₙ(M, X)` is the `n`th left-derived functor of `tensorRight X` evaluated at `M`. -/
private theorem source_tor_owner_eq_leftDerived_obj
    (A : ModuleCat R) (n : ℕ) :
    (((Tor' (ModuleCat R) n).obj (ModuleCat.of R M)).obj A) =
      ((tensorRight A).leftDerived n).obj (ModuleCat.of R M) := by
  -- This is the definitional expansion of `Tor'` in the non-flipped source-owner orientation.
  rfl

/-- Helper for Chap10 Lemma 10 99 12: the non-flipped source owner `Tor'₁(M, A)` is computed by
tensoring the fixed projective resolution of `M` with `A` and taking degree-one homology. -/
private noncomputable def sourceOwnerDegreeOneProjectiveResolutionIso
    (A : ModuleCat R) :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj A) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) :=
  eqToIso (source_tor_owner_eq_leftDerived_obj (R := R) (M := M) A 1) ≪≫
    (CategoryTheory.projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj
      (tensorRight A) 1

/-- Helper for Chap10 Lemma 10 99 12: degree `0` of the fixed-left source owner is the literal
left tensor product with `M`. -/
private noncomputable def sourceOwnerDegreeZeroTensorIso
    (A : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj A) ≅
      ((tensorLeft (ModuleCat.of R M)).obj A) := by
  -- Proof comment: `Tor'₀` is just the underlying tensor functor.
  erw [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) A 0]
  exact (tensorRight A).leftDerivedZeroIsoSelf.app (ModuleCat.of R M)

/-- Helper for Chap10 Lemma 10 99 12: degree `0` of the fixed-left source owner is computed by
tensoring the chosen projective resolution of `M` with the coefficient object. -/
private noncomputable def sourceOwnerDegreeZeroProjectiveResolutionIso
    (A : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj A) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).obj
        (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) := by
  -- Proof comment: the same fixed projective resolution computes the degree-zero source owner.
  erw [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) A 0]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj
      (tensorRight A) 0

/-- Helper for Chap10 Lemma 10 99 12: the projective-resolution model of
`fromLeftDerivedZero'` is natural in the functor variable. -/
private theorem projectiveResolutionFromLeftDerivedZero'_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Cancel the universal opcycles projection and reduce to naturality of `α` on the augmentation.
  rw [← cancel_epi (HomologicalComplex.pOpcycles _ _)]
  have hPrefixF :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
        P.fromLeftDerivedZero' F =
      F.map (P.π.f 0) := by
    simpa using
      CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := F)
  have h₁ :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' F ≫ α.app X =
        F.map (P.π.f 0) ≫ α.app X := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ α.app X) hPrefixF
  have h₂ :
      F.map (P.π.f 0) ≫ α.app X =
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) := by
    simpa using α.naturality (P.π.f 0)
  have h₃ :
      α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
    have hPrefixG :
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' G =
        G.map (P.π.f 0) := by
      simpa using
        CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := G)
    have hOpcycles :
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 =
          α.app (P.complex.X 0) ≫
            ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 := by
      simpa using
        HomologicalComplex.p_opcyclesMap
          (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)
          (i := 0)
    have h₃a :
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
          α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) := by
      simpa [Category.assoc] using congrArg (fun k ↦ α.app (P.complex.X 0) ≫ k) hPrefixG.symm
    have h₃b :
        α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) =
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
            P.fromLeftDerivedZero' G := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ P.fromLeftDerivedZero' G) hOpcycles.symm
    exact h₃a.trans h₃b
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Chap10 Lemma 10 99 12: the canonical degree-zero comparison
`leftDerived 0 ≅ tensor` is natural for natural transformations between additive right exact
endofunctors of `ModuleCat R`. -/
private theorem leftDerivedZeroIsoSelf_hom_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.leftDerivedZeroIsoSelf.hom =
      F.leftDerivedZeroIsoSelf.hom ≫ α := by
  apply NatTrans.ext
  funext X
  have hComp :
      (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
        F.fromLeftDerivedZero.app X ≫ α.app X := by
    let P : CategoryTheory.ProjectiveResolution X :=
      CategoryTheory.projectiveResolution X
    rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq α P 0,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P G,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hIsoHomology :
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
            (ChainComplex.isoHomologyι₀
              (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom =
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 := by
      -- Replace the degree-zero homology map by the corresponding opcycles map.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (ChainComplex.isoHomologyι₀
              (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                k ≫
                  (ChainComplex.isoHomologyι₀
                    (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom)
          (ChainComplex.isoHomologyι₀_inv_naturality
            (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex))
    calc
      (P.isoLeftDerivedObj F 0).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
          (ChainComplex.isoHomologyι₀
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' G =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ (P.isoLeftDerivedObj F 0).hom ≫ k ≫ P.fromLeftDerivedZero' G)
                  hIsoHomology
      _ =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' F ≫ α.app X := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    (P.isoLeftDerivedObj F 0).hom ≫
                      (ChainComplex.isoHomologyι₀
                        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                      k)
                  (projectiveResolutionFromLeftDerivedZero'_nattrans (R := R) (α := α) P).symm
  simpa [Functor.leftDerivedZeroIsoSelf] using hComp

/-- Helper for Chap10 Lemma 10 99 12: the degree-zero source-owner comparison transports a
coefficient morphism to the literal left-tensor map. -/
private theorem sourceOwnerDegreeZeroTensorMapTransport
    {A B : ModuleCat R} (f : A ⟶ B) :
    (tensorLeft (ModuleCat.of R M)).map f =
      (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) A).inv ≫
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫
        (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) B).hom := by
  let eLeft :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj A) ≅
        ((tensorLeft (ModuleCat.of R M)).obj A) :=
    sourceOwnerDegreeZeroTensorIso (R := R) (M := M) A
  let eRight :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj B) ≅
        ((tensorLeft (ModuleCat.of R M)).obj B) :=
    sourceOwnerDegreeZeroTensorIso (R := R) (M := M) B
  have hNat :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom =
        eLeft.hom ≫ (tensorLeft (ModuleCat.of R M)).map f := by
    -- Proof comment: naturality of the degree-zero tensor comparison identifies the mapped Tor
    -- morphism with the literal tensor map.
    simpa [eLeft, eRight, Tor', Category.assoc] using
      congrArg
        (fun k ↦ k.app (ModuleCat.of R M))
        (leftDerivedZeroIsoSelf_hom_nattrans (R := R)
          (((tensoringRight (ModuleCat R)).map f)))
  calc
    (tensorLeft (ModuleCat.of R M)).map f =
      eLeft.inv ≫ eLeft.hom ≫ (tensorLeft (ModuleCat.of R M)).map f := by
        simp
    _ = eLeft.inv ≫ ((((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom) := by
        rw [hNat]
    _ = eLeft.inv ≫ (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom := by
        simp

/-- Helper for Chap10 Lemma 10 99 12: tensoring a short exact row on the left by a projective
module preserves short exactness. -/
private theorem tensorLeft_map_shortExact_of_projective
    (P : ModuleCat R) [Projective P] {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (S.map (tensorLeft P)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Projective modules are flat, so exactness survives after tensoring on the left by `P`.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    let _ : Module.Projective R P :=
      module_projective_of_categorical_projective (R := R) P inferInstance
    let _ : Module.Flat R P := Module.Flat.of_projective
    have hExactBase : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_exact P hExactBase)
  · -- Left tensoring by a flat module preserves injectivity.
    exact (ModuleCat.mono_iff_injective _).2 <| by
      let _ : Module.Projective R P :=
        module_projective_of_categorical_projective (R := R) P inferInstance
      let _ : Module.Flat R P := Module.Flat.of_projective
      have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
      simpa [ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_preserves_injective_linearMap (M := P) S.f.hom hf)
  · -- Surjectivity of the quotient map is preserved by left tensoring.
    exact (ModuleCat.epi_iff_surjective _).2 <| by
      have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
      simpa [ModuleCat.hom_whiskerLeft] using
        (LinearMap.lTensor_surjective P hg)

/-- Helper for Chap10 Lemma 10 99 12: a short exact row
`0 → X₁ → X₂ → X₃ → 0` yields the fixed-left source-owner five-term exact row
`Tor'₁(M, X₁) → Tor'₁(M, X₂) → Tor'₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂`. -/
private theorem sourceOwnerTorOneTensorExactOfShortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
          ((tensorLeft (ModuleCat.of R M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δ
        (((tensorLeft (ModuleCat.of R M)).map S.f))
        (((tensorLeft (ModuleCat.of R M)).map S.g))).Exact := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of R M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- Proof comment: tensoring preserves the relation `S.f ≫ S.g = 0` degreewise.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[R] S.X₃)) x =
      (0 : P.complex.X k ⊗[R] S.X₁ →ₗ[R] P.complex.X k ⊗[R] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Proof comment: each projective term of the chosen resolution is flat, so left tensoring by
    -- that term preserves the short exact coefficient row degreewise.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (R := R) (P := P.complex.X k) (S := S) hS
  let eSource₁X₁ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₁) ≅ T.X₁.homology 1 :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) S.X₁
  let eSource₁X₂ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₂) ≅ T.X₂.homology 1 :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) S.X₂
  let eSource₁X₃ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ≅ T.X₃.homology 1 :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) S.X₃
  let eTensorX₁ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₁) ≅ T.X₁.homology 0 :=
    (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) S.X₁).symm ≪≫
      sourceOwnerDegreeZeroProjectiveResolutionIso (R := R) (M := M) S.X₁
  let eTensorX₂ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₂) ≅ T.X₂.homology 0 :=
    (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) S.X₂).symm ≪≫
      sourceOwnerDegreeZeroProjectiveResolutionIso (R := R) (M := M) S.X₂
  let eTensorX₃ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₃) ≅ T.X₃.homology 0 :=
    (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) S.X₃).symm ≪≫
      sourceOwnerDegreeZeroProjectiveResolutionIso (R := R) (M := M) S.X₃
  have hSource₁MapF :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f) ≫ eSource₁X₂.hom =
        eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Proof comment: the degree-one source-owner maps are the homology maps of the tensorized
    -- chain maps.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f) =
          eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eSource₁X₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₁MapG :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g) ≫ eSource₁X₃.hom =
        eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- Proof comment: the same identification holds for the second source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g) =
          eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 ≫ eSource₁X₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapF :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) ≫
          (sourceOwnerDegreeZeroProjectiveResolutionIso
            (R := R) (M := M) S.X₂).hom =
        (sourceOwnerDegreeZeroProjectiveResolutionIso
          (R := R) (M := M) S.X₁).hom ≫
          HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: degree zero is computed on the same tensorized projective resolution.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) =
          (sourceOwnerDegreeZeroProjectiveResolutionIso
            (R := R) (M := M) S.X₁).hom ≫
            HomologicalComplex.homologyMap T.f 0 ≫
            (sourceOwnerDegreeZeroProjectiveResolutionIso
              (R := R) (M := M) S.X₂).inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapG :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) ≫
          (sourceOwnerDegreeZeroProjectiveResolutionIso
            (R := R) (M := M) S.X₃).hom =
        (sourceOwnerDegreeZeroProjectiveResolutionIso
          (R := R) (M := M) S.X₂).hom ≫
          HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: and likewise for the final degree-zero source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) =
          (sourceOwnerDegreeZeroProjectiveResolutionIso
            (R := R) (M := M) S.X₂).hom ≫
            HomologicalComplex.homologyMap T.g 0 ≫
            (sourceOwnerDegreeZeroProjectiveResolutionIso
              (R := R) (M := M) S.X₃).inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hTensorMapF :
      ((tensorLeft (ModuleCat.of R M)).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: transport the degree-zero source-owner map to the literal tensor map.
    have hTransport :
        (tensorLeft (ModuleCat.of R M)).map S.f ≫ eTensorX₂.hom =
          (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) S.X₁).inv ≫
            (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) ≫
            (sourceOwnerDegreeZeroProjectiveResolutionIso
              (R := R) (M := M) S.X₂).hom := by
      rw [sourceOwnerDegreeZeroTensorMapTransport (R := R) (M := M) S.f]
      simp [eTensorX₂, Category.assoc]
    rw [hTransport, hSource₀MapF]
    simp [eTensorX₁, Category.assoc]
  have hTensorMapG :
      ((tensorLeft (ModuleCat.of R M)).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: the same transport identifies the final tensor arrow.
    have hTransport :
        (tensorLeft (ModuleCat.of R M)).map S.g ≫ eTensorX₃.hom =
          (sourceOwnerDegreeZeroTensorIso (R := R) (M := M) S.X₂).inv ≫
            (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) ≫
            (sourceOwnerDegreeZeroProjectiveResolutionIso
              (R := R) (M := M) S.X₃).hom := by
      rw [sourceOwnerDegreeZeroTensorMapTransport (R := R) (M := M) S.g]
      simp [eTensorX₃, Category.assoc]
    rw [hTransport, hSource₀MapG]
    simp [eTensorX₂, Category.assoc]
  let δSource :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
        ((tensorLeft (ModuleCat.of R M)).obj S.X₁) :=
    eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) ≫ eTensorX₁.inv
  have hSourceδ :
      δSource ≫ eTensorX₁.hom =
        eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) := by
    -- Proof comment: the connecting morphism is the raw homology boundary conjugated by the
    -- endpoint identifications.
    simp [δSource, Category.assoc]
  let eSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)) ≅
        HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp) :=
    ComposableArrows.isoMk₅
      eSource₁X₁
      eSource₁X₂
      eSource₁X₃
      eTensorX₁
      eTensorX₂
      eTensorX₃
      hSource₁MapF
      hSource₁MapG
      hSourceδ
      hTensorMapF
      hTensorMapG
  have hSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)).Exact := by
    -- Proof comment: after identifying the source-owner row with the raw homology row, exactness
    -- is inherited from the long exact homology sequence.
    have hRaw :
        (HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp)).Exact := by
      simpa using HomologicalComplex.HomologySequence.composableArrows₅_exact hT 1 0 (by simp)
    exact (ComposableArrows.exact_iff_of_iso eSource).2 hRaw
  refine ⟨δSource, ?_⟩
  -- Proof comment: this is the exact `(1,0)` source-owner row read from the homology long exact
  -- sequence of the tensorized projective-resolution short exact row.
  exact hSource

/-- Helper for Chap10 Lemma 10 99 12: when the coefficient object is the first public Tor
variable, `tor_flip_iso` identifies it with the fixed-left source owner computed from the
projective resolution of `M`. -/
private noncomputable def publicTorFirstVariableSourceOwnerIso
    (A : ModuleCat R) (n : ℕ) :
    (((Tor (ModuleCat R) n).obj A).obj (ModuleCat.of R M)) ≅
      (((Tor' (ModuleCat R) n).obj (ModuleCat.of R M)).obj A) := by
  -- This is the objectwise component of `tor_flip_iso`; recording it once keeps the later
  -- window computation in the source-owner normal form.
  simpa using (((tor_flip_iso (ModuleCat R) n).app A).app (ModuleCat.of R M))

/-- Helper for Chap10 Lemma 10 99 12: the available `tor_flip_iso` computes the flipped public
owner `Tor₁(A, M)` from the fixed projective resolution of `M`.  This records the exact endpoint
provided by mathlib and separates it from the missing same-order public-to-source comparison for
`Tor₁(M, A)`. -/
private noncomputable def publicTorFlippedWindowIso (A : ModuleCat R) :
    (((Tor (ModuleCat R) 1).obj A).obj (ModuleCat.of R M)) ≅
      ShortComplex.homology
        (tensorRight_degree_one_window (R := R) A (ModuleCat.of R M)) := by
  let eSource :
      (((Tor (ModuleCat R) 1).obj A).obj (ModuleCat.of R M)) ≅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj A) :=
    publicTorFirstVariableSourceOwnerIso (R := R) (M := M) A 1
  let eDerived :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj A) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
          (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.ProjectiveResolution.complex
              (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) A
  -- Compose the public-to-source owner comparison, the fixed-resolution computation, and the
  -- conversion from full degree-one homology to the explicit three-term source window.
  exact
    eSource ≪≫ eDerived ≪≫
      tensorRight_degree_one_window_homology_iso (R := R) A (ModuleCat.of R M)

/-- Helper for Chap10 Lemma 10 99 12: if the right input is projective, the public
right-variable owner `Tor₁(M, -)` vanishes on it. -/
private theorem publicTorOneProjectiveRight_isZero (P : ModuleCat R) [Projective P] :
    IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj P)) := by
  -- Positive left-derived functors vanish on projective objects in the resolved variable.
  simpa [Tor] using
    (Functor.isZero_leftDerived_obj_projective_succ
      ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)) 0 P)

/-- Helper for Chap10 Lemma 10 99 12: if the coefficient object is projective, the fixed-left
source owner `Tor'₁(M, P)` vanishes because tensoring the fixed projective resolution of `M` by
the flat module `P` preserves exactness at degree one. -/
private theorem sourceOwnerTorOneProjectiveRight_isZero (P : ModuleCat R) [Projective P] :
    IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj P)) := by
  have hProjMod : Module.Projective R P :=
    module_projective_of_categorical_projective (A := R) (X := P) inferInstance
  letI : Module.Projective R P := hProjMod
  letI : Module.Flat R P := Module.Flat.of_projective
  let Q := CategoryTheory.projectiveResolution (ModuleCat.of R M)
  have hExactQ : (Q.complex.sc 1).Exact := by
    -- The chosen projective resolution of `M` is exact in every positive degree.
    exact Q.complex_exactAt_succ 0
  have hTensorExact :
      ((Q.complex.sc 1).map (tensorRight P)).Exact := by
    -- Flatness of the projective coefficient preserves exactness after tensoring on the right.
    exact Module.Flat.rTensor_shortComplex_exact P (Q.complex.sc 1) hExactQ
  have hMappedExact :
      (((tensorRight P).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).ExactAt 1 := by
    -- Rewrite the mapped short complex into the `ExactAt` statement for the mapped resolution.
    simpa [HomologicalComplex.exactAt_iff, HomologicalComplex.sc,
      CategoryTheory.Functor.mapHomologicalComplex_obj_d] using hTensorExact
  have hMappedZero :
      IsZero
        ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
          (((tensorRight P).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)) := by
    -- Exactness at degree one is equivalent to vanishing of degree-one homology.
    simpa [HomologicalComplex.homology] using hMappedExact.isZero_homology
  -- Transport the homology vanishing across the source-owner computation by the fixed resolution.
  exact hMappedZero.of_iso (sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) P)

/-- Helper for Chap10 Lemma 10 99 12: the local source-owner five-term exact row gives
exactness of the first two `Tor'₁(M, -)` maps for any short exact row of coefficients. -/
private theorem sourceOwnerTorOneShortExactFirstPairExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Function.Exact ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f).hom)
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g).hom) := by
  obtain ⟨δ, hFive⟩ :=
    sourceOwnerTorOneTensorExactOfShortExact (R := R) (M := M) (S := S) hS
  have hsc :
      ((ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δ
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)).sc hFive.toIsComplex 0).Exact := hFive.exact 0
  -- Proof comment: the local five-term source-owner row already contains the exact first pair
  -- `(Tor'₁(M,S.X₁) → Tor'₁(M,S.X₂) → Tor'₁(M,S.X₃))`.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δ
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)).sc hFive.toIsComplex 0)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: the public six-term `Tor₁` row supplies a connecting map
from `Tor₁(M, S.X₃)` to `M ⊗ S.X₁` whose adjacent pairs are exact. -/
private theorem publicTorOneTensorKernelExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ : ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
        (ModuleCat.of R M ⊗ S.X₁)),
      Function.Exact ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g).hom) δ.hom ∧
        Function.Exact δ.hom (((tensorLeft (ModuleCat.of R M)).map S.f).hom) := by
  let T := ModuleCat.torTensorSixTermSequence (R := R) (ModuleCat.of R M) hS
  let δ : ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
      (ModuleCat.of R M ⊗ S.X₁)) := T.map' 2 3
  refine ⟨δ, ?_, ?_⟩
  · -- The short complex at positions `1,2,3` is the `(Tor₁(M,S.X₂), Tor₁(M,S.X₃), δ)` pair.
    have hExact : T.Exact :=
      ModuleCat.torTensorSixTermSequence_exact (R := R) (ModuleCat.of R M) hS
    have hsc : (T.sc hExact.toIsComplex 1).Exact := hExact.exact 1
    simpa [T, δ, ModuleCat.torTensorSixTermSequence, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := T.sc hExact.toIsComplex 1)).1 hsc
  · -- The next short complex is the `(δ, M ⊗ S.f)` exact pair needed for the kernel model.
    have hExact : T.Exact :=
      ModuleCat.torTensorSixTermSequence_exact (R := R) (ModuleCat.of R M) hS
    have hsc : (T.sc hExact.toIsComplex 2).Exact := hExact.exact 2
    simpa [T, δ, ModuleCat.torTensorSixTermSequence, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := T.sc hExact.toIsComplex 2)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: exactness after a zero left term makes the middle map
injective. -/
private theorem linearMap_injective_of_exact_isZero_left
    {A B K : ModuleCat R} {α : A ⟶ B} {δ : B ⟶ K}
    (hαδ : Function.Exact α.hom δ.hom) (hA : IsZero A) :
    Function.Injective δ.hom := by
  -- First convert the zero source object into the statement that `range α` is the zero submodule.
  have hSub : Subsingleton A := ModuleCat.isZero_iff_subsingleton.mp hA
  have hRangeα : α.hom.range = ⊥ := by
    ext b
    constructor
    · intro hb
      rcases LinearMap.mem_range.mp hb with ⟨a, ha⟩
      have ha0 : a = 0 := Subsingleton.elim a 0
      rw [← ha, ha0, map_zero]
      exact Submodule.zero_mem _
    · intro hb
      rw [Submodule.mem_bot] at hb
      rw [hb]
      exact ⟨0, by simp⟩
  -- Exactness identifies `ker δ` with that zero range, so `δ` is injective.
  have hkerδ : δ.hom.ker = ⊥ := by
    rw [LinearMap.exact_iff.mp hαδ, hRangeα]
  exact LinearMap.ker_eq_bot.mp hkerδ

/-- Helper for Chap10 Lemma 10 99 12: the map in an exact pair surjects onto the kernel of the
next map after codomain restriction. -/
private theorem linearMap_surjective_to_kernel_of_exact
    {B K P : ModuleCat R} {δ : B ⟶ K} {β : K ⟶ P}
    (hδβ : Function.Exact δ.hom β.hom) :
    Function.Surjective
      (δ.hom.codRestrict β.hom.ker (fun b ↦ by
        have hker_range : β.hom.ker = δ.hom.range := LinearMap.exact_iff.mp hδβ
        rw [hker_range]
        exact LinearMap.mem_range_self δ.hom b)) := by
  -- Exactness rewrites the target kernel as the range of `δ`, so every kernel element has a lift.
  intro z
  have hz : z.1 ∈ δ.hom.range := by
    have hker_range : β.hom.ker = δ.hom.range := LinearMap.exact_iff.mp hδβ
    rw [← hker_range]
    exact z.2
  rcases LinearMap.mem_range.mp hz with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact hb

/-- Helper for Chap10 Lemma 10 99 12: an exact pair with zero left source identifies the middle
module bijectively with the kernel of the next map. -/
private theorem linearMap_bijective_to_kernel_of_exact_isZero_left
    {A B K P : ModuleCat R} {α : A ⟶ B} {δ : B ⟶ K} {β : K ⟶ P}
    (hαδ : Function.Exact α.hom δ.hom) (hδβ : Function.Exact δ.hom β.hom)
    (hA : IsZero A) :
    Function.Bijective
      (δ.hom.codRestrict β.hom.ker (fun b ↦ by
        have hker_range : β.hom.ker = δ.hom.range := LinearMap.exact_iff.mp hδβ
        rw [hker_range]
        exact LinearMap.mem_range_self δ.hom b)) := by
  -- Combine injectivity from the zero left term with surjectivity onto the kernel from exactness.
  constructor
  · intro b₁ b₂ hb
    exact linearMap_injective_of_exact_isZero_left hαδ hA (congrArg Subtype.val hb)
  · exact linearMap_surjective_to_kernel_of_exact hδβ

/-- Helper for Chap10 Lemma 10 99 12: an exact pair with zero left source gives a concrete
module isomorphism from the middle object to the kernel of the following map. -/
private theorem kernelIsoOfExactPairAndIsZeroLeft_nonempty
    {A B K P : ModuleCat R} {α : A ⟶ B} {δ : B ⟶ K} {β : K ⟶ P}
    (hαδ : Function.Exact α.hom δ.hom) (hδβ : Function.Exact δ.hom β.hom)
    (hA : IsZero A) :
    Nonempty (B ≅ ModuleCat.of R (LinearMap.ker β.hom)) := by
  let φ : B →ₗ[R] LinearMap.ker β.hom :=
    δ.hom.codRestrict β.hom.ker (fun b ↦ by
      have hker_range : β.hom.ker = δ.hom.range := LinearMap.exact_iff.mp hδβ
      rw [hker_range]
      exact LinearMap.mem_range_self δ.hom b)
  have hbij : Function.Bijective φ := by
    -- The preceding helper gives bijectivity for exactly this codomain-restricted map.
    simpa [φ] using
      (linearMap_bijective_to_kernel_of_exact_isZero_left
        (R := R) (α := α) (δ := δ) (β := β) hαδ hδβ hA)
  -- Upgrade the bijective linear map to a `ModuleCat` isomorphism.
  exact ⟨(LinearEquiv.ofBijective φ hbij).toModuleIso⟩

/-- Helper for Chap10 Lemma 10 99 12: the exact-pair kernel identification built from the
explicit codomain restriction map `δ : B ⟶ ker β`. -/
private noncomputable def kernelIsoOfExactPairAndIsZeroLeft
    {A B K P : ModuleCat R} {α : A ⟶ B} {δ : B ⟶ K} {β : K ⟶ P}
    (hαδ : Function.Exact α.hom δ.hom) (hδβ : Function.Exact δ.hom β.hom)
    (hA : IsZero A) :
    B ≅ ModuleCat.of R (LinearMap.ker β.hom) := by
  let φ : B →ₗ[R] LinearMap.ker β.hom :=
    δ.hom.codRestrict β.hom.ker (fun b ↦ by
      have hker_range : β.hom.ker = δ.hom.range := LinearMap.exact_iff.mp hδβ
      rw [hker_range]
      exact LinearMap.mem_range_self δ.hom b)
  have hbij : Function.Bijective φ := by
    -- Reuse the exact-pair kernel bijectivity on the concrete codomain-restriction map.
    simpa [φ] using
      (linearMap_bijective_to_kernel_of_exact_isZero_left
        (R := R) (α := α) (δ := δ) (β := β) hαδ hδβ hA)
  exact (LinearEquiv.ofBijective φ hbij).toModuleIso

/-- Helper for Chap10 Lemma 10 99 12: the forward map of
`kernelIsoOfExactPairAndIsZeroLeft` is the codomain-restricted middle map of the exact pair. -/
private theorem kernelIsoOfExactPairAndIsZeroLeft_hom_apply
    {A B K P : ModuleCat R} {α : A ⟶ B} {δ : B ⟶ K} {β : K ⟶ P}
    (hαδ : Function.Exact α.hom δ.hom) (hδβ : Function.Exact δ.hom β.hom)
    (hA : IsZero A) (b : B) :
    ((kernelIsoOfExactPairAndIsZeroLeft
        (R := R) (α := α) (δ := δ) (β := β) hαδ hδβ hA).hom.hom b).1 =
      δ.hom b := by
  -- Proof comment: the isomorphism was built from the codomain-restricted map `b ↦ δ b`, so its
  -- first projection is definitionally the original middle arrow.
  rfl

/-- Helper for Chap10 Lemma 10 99 12: the chosen projective resolution of the coefficient module
`T` yields a canonical short exact row `K' → P₀ → T`. -/
private noncomputable abbrev ringCoeffTorOneKernelRow
    {T : Type u} [CommRing T] [Algebra R T] :
    ShortComplex (ModuleCat R) :=
  LinearMap.shortComplexKer ((CategoryTheory.projectiveResolution (ModuleCat.of R T)).π.f 0).hom

/-- Helper for Chap10 Lemma 10 99 12: the kernel row attached to the chosen projective
presentation of `T` is short exact. -/
private theorem ringCoeffTorOneKernelRow_shortExact
    {T : Type u} [CommRing T] [Algebra R T] :
    (ringCoeffTorOneKernelRow (R := R) (T := T)).ShortExact := by
  have hSurj :
      Function.Surjective
        ((CategoryTheory.projectiveResolution (ModuleCat.of R T)).π.f 0).hom := by
    -- The degree-zero augmentation of a projective resolution is an epimorphism, hence
    -- surjective after passing to modules.
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  -- The kernel short complex of a surjective map is the standard short exact row.
  simpa [ringCoeffTorOneKernelRow] using LinearMap.shortExact_shortComplexKer hSurj

/-- Helper for Chap10 Lemma 10 99 12: both endpoint Tor computations are compared through the same
kernel of `M ⊗ K₂ → M ⊗ K₃` coming from the chosen projective presentation row of `T`. -/
private noncomputable abbrev ringCoeffTorOneKernelTarget
    {T : Type u} [CommRing T] [Algebra R T] : ModuleCat R :=
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  ModuleCat.of R (LinearMap.ker (((tensorLeft (ModuleCat.of R M)).map K.f).hom))

/-- Helper for Chap10 Lemma 10 99 12: the public coefficient-side connecting morphism for the
chosen projective-presentation row of `T`, taken from the canonical six-term Tor sequence. -/
private noncomputable abbrev ringCoeffTorOnePublicKernelMap
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ⟶
      (ModuleCat.of R M ⊗ (ringCoeffTorOneKernelRow (R := R) (T := T)).X₁) :=
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  (ModuleCat.torTensorSixTermSequence
      (R := R) (ModuleCat.of R M) (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))).map' 2 3

/-- Helper for Chap10 Lemma 10 99 12: the canonical public connecting morphism is exact on the
left with the Tor map induced by `K.g`. -/
private theorem ringCoeffTorOnePublicKernelMap_exact_left
    {T : Type u} [CommRing T] [Algebra R T] :
    Function.Exact
      ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          (ringCoeffTorOneKernelRow (R := R) (T := T)).g).hom)
      (ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T)).hom := by
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  let T6 := ModuleCat.torTensorSixTermSequence
    (R := R) (ModuleCat.of R M) (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))
  have hExact : T6.Exact :=
    ModuleCat.torTensorSixTermSequence_exact
      (R := R) (ModuleCat.of R M) (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))
  have hsc : (T6.sc hExact.toIsComplex 1).Exact := hExact.exact 1
  -- The public kernel map is the middle arrow in the canonical six-term row.
  simpa [ringCoeffTorOnePublicKernelMap, T6, K, ModuleCat.torTensorSixTermSequence,
    ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := T6.sc hExact.toIsComplex 1)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: the canonical public connecting morphism is exact on the
right with the tensor map induced by `K.f`. -/
private theorem ringCoeffTorOnePublicKernelMap_exact_right
    {T : Type u} [CommRing T] [Algebra R T] :
    Function.Exact
      (ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T)).hom
      (((tensorLeft (ModuleCat.of R M)).map
          (ringCoeffTorOneKernelRow (R := R) (T := T)).f).hom) := by
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  let T6 := ModuleCat.torTensorSixTermSequence
    (R := R) (ModuleCat.of R M) (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))
  have hExact : T6.Exact :=
    ModuleCat.torTensorSixTermSequence_exact
      (R := R) (ModuleCat.of R M) (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))
  have hsc : (T6.sc hExact.toIsComplex 2).Exact := hExact.exact 2
  -- The next short complex in the same six-term row gives the exact pair `(δPub, M ⊗ K.f)`.
  simpa [ringCoeffTorOnePublicKernelMap, T6, K, ModuleCat.torTensorSixTermSequence,
    ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := T6.sc hExact.toIsComplex 2)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: the public owner `Tor₁^R(M,T)` identifies concretely with
the kernel of the tensor map in the chosen projective-presentation row of `T`. -/
private noncomputable def ringCoeffTorOnePublicKernelIso
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
      ringCoeffTorOneKernelTarget (R := R) (M := M) (T := T) := by
  let P := CategoryTheory.projectiveResolution (ModuleCat.of R T)
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  let δPub := ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T)
  have hPubLeft :
      Function.Exact ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g).hom) δPub.hom :=
    ringCoeffTorOnePublicKernelMap_exact_left (R := R) (M := M) (T := T)
  have hPubRight :
      Function.Exact δPub.hom (((tensorLeft (ModuleCat.of R M)).map K.f).hom) :=
    ringCoeffTorOnePublicKernelMap_exact_right (R := R) (M := M) (T := T)
  have hProjK₂ : Projective K.X₂ := by
    -- The middle term of the kernel row is the degree-zero projective term of the chosen
    -- resolution of `T`.
    simpa [K, ringCoeffTorOneKernelRow, LinearMap.shortComplexKer] using (P.projective 0)
  have hPubZero :
      IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj K.X₂)) := by
    -- The public right-variable owner vanishes on projective coefficients.
    letI : Projective K.X₂ := hProjK₂
    exact publicTorOneProjectiveRight_isZero (R := R) (M := M) K.X₂
  let β := ((tensorLeft (ModuleCat.of R M)).map K.f)
  -- Apply the generic exact-pair kernel computation to the public exact row.
  simpa [ringCoeffTorOneKernelTarget, K] using
    (kernelIsoOfExactPairAndIsZeroLeft
      (R := R)
      (α := (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g))
      (δ := δPub) (β := β) hPubLeft hPubRight hPubZero)

/-- Helper for Chap10 Lemma 10 99 12: the fixed-left source owner `Tor'₁(M,T)` identifies
concretely with the same projective-presentation kernel of `T`. -/
private noncomputable def ringCoeffTorOneSourceKernelMap
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ⟶
      (ModuleCat.of R M ⊗ (ringCoeffTorOneKernelRow (R := R) (T := T)).X₁) :=
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  -- Proof comment: expose the explicit source-owner connecting morphism coming from the homology
  -- sequence of the tensorized fixed projective resolution, so later transport arguments can use
  -- a theorem-local construction rather than the opaque witness bundled in `Lemma_10_75_2`.
  Classical.choose
    (sourceOwnerTorOneTensorExactOfShortExact
      (R := R) (M := M) (S := K)
      (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T)))

/-- Helper for Chap10 Lemma 10 99 12: the named source connecting morphism is exact on the left
with the Tor map induced by `K.g`. -/
private theorem ringCoeffTorOneSourceKernelMap_exact_left
    {T : Type u} [CommRing T] [Algebra R T] :
    Function.Exact
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          (ringCoeffTorOneKernelRow (R := R) (T := T)).g).hom)
      (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T)).hom := by
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  have hFive :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).Exact := by
    -- Proof comment: read the exact source-owner five-term row from the explicit homology
    -- construction specialized to the coefficient kernel presentation.
    simpa [ringCoeffTorOneSourceKernelMap, K] using
      Classical.choose_spec
        (sourceOwnerTorOneTensorExactOfShortExact
          (R := R) (M := M) (S := K)
          (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T)))
  have hsc : ((ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).sc hFive.toIsComplex 1).Exact := hFive.exact 1
  -- Proof comment: this is the exact pair `(Tor'₁(M, K.X₂) → Tor'₁(M, K.X₃) → δSrc)`.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).sc hFive.toIsComplex 1)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: the named source connecting morphism is exact on the right
with the tensor map induced by `K.f`. -/
private theorem ringCoeffTorOneSourceKernelMap_exact_right
    {T : Type u} [CommRing T] [Algebra R T] :
    Function.Exact
      (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T)).hom
      (((tensorLeft (ModuleCat.of R M)).map
          (ringCoeffTorOneKernelRow (R := R) (T := T)).f).hom) := by
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  have hFive :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).Exact := by
    -- Proof comment: reuse the same explicit source-owner five-term row as in the left exactness
    -- computation.
    simpa [ringCoeffTorOneSourceKernelMap, K] using
      Classical.choose_spec
        (sourceOwnerTorOneTensorExactOfShortExact
          (R := R) (M := M) (S := K)
          (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T)))
  have hsc : ((ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).sc hFive.toIsComplex 2).Exact := hFive.exact 2
  -- Proof comment: this is the exact pair `(δSrc, M ⊗ K.f)` adjacent to the same source
  -- connecting morphism.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
        ((tensorLeft (ModuleCat.of R M)).map K.f)
        ((tensorLeft (ModuleCat.of R M)).map K.g)).sc hFive.toIsComplex 2)).1 hsc

/-- Helper for Chap10 Lemma 10 99 12: the fixed-left source owner `Tor'₁(M,T)` identifies
concretely with the same projective-presentation kernel of `T`. -/
private noncomputable def ringCoeffTorOneSourceKernelIso
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
      ringCoeffTorOneKernelTarget (R := R) (M := M) (T := T) := by
  let P := CategoryTheory.projectiveResolution (ModuleCat.of R T)
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  have hSrcLeft :
      Function.Exact
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g).hom)
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T)).hom :=
    ringCoeffTorOneSourceKernelMap_exact_left (R := R) (M := M) (T := T)
  have hSrcRight :
      Function.Exact
        (ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T)).hom
        (((tensorLeft (ModuleCat.of R M)).map K.f).hom) :=
    ringCoeffTorOneSourceKernelMap_exact_right (R := R) (M := M) (T := T)
  have hProjK₂ : Projective K.X₂ := by
    -- The source-owner computation uses the same degree-zero projective term.
    simpa [K, ringCoeffTorOneKernelRow, LinearMap.shortComplexKer] using (P.projective 0)
  have hSrcZero :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj K.X₂)) := by
    -- The fixed-left source owner also vanishes on projective coefficients.
    letI : Projective K.X₂ := hProjK₂
    exact sourceOwnerTorOneProjectiveRight_isZero (R := R) (M := M) K.X₂
  let β := ((tensorLeft (ModuleCat.of R M)).map K.f)
  -- Apply the same kernel computation to the fixed-left source-owner exact row.
  simpa [ringCoeffTorOneKernelTarget, K] using
    (kernelIsoOfExactPairAndIsZeroLeft
      (R := R)
      (α := (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g))
      (δ := ringCoeffTorOneSourceKernelMap (R := R) (M := M) (T := T))
      (β := β) hSrcLeft hSrcRight hSrcZero)

/-- Helper for Chap10 Lemma 10 99 12: the chosen ring-coefficient comparison from public
`Tor₁^R(M,T)` to the fixed-left source owner `Tor'₁(M,T)`. -/
private noncomputable def ringCoeffTorOneOwnerKernelComparison
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) :=
  -- Route correction: use the explicit public/source kernel identifications rather than hiding
  -- the comparison behind a `Classical.choice`, so later scalar-compatibility goals can unfold to
  -- concrete exact-pair data.
  ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T) ≪≫
    (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).symm

/-- Helper for Chap10 Lemma 10 99 12: after postcomposing the public-to-source owner comparison
with the source kernel identification, one recovers the public kernel identification exactly. -/
private theorem ringCoeffTorOneOwnerKernelComparison_hom_comp_sourceKernelIso
    {T : Type u} [CommRing T] [Algebra R T] :
    (ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom ≫
      (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom =
        (ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom := by
  -- Proof comment: the comparison was defined by composing the public kernel isomorphism with the
  -- inverse of the source kernel isomorphism, so the postcomposition cancels immediately.
  simp [ringCoeffTorOneOwnerKernelComparison]

/-- Helper for Chap10 Lemma 10 99 12: on elements, the public-to-source owner comparison becomes
the public kernel comparison after applying the source kernel identification. -/
private theorem ringCoeffTorOneOwnerKernelComparison_hom_apply_sourceKernelIso
    {T : Type u} [CommRing T] [Algebra R T]
    (x : (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x) =
      (ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom x := by
  -- Proof comment: this is the pointwise form of the preceding cancellation lemma.
  simpa using
    DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (ringCoeffTorOneOwnerKernelComparison_hom_comp_sourceKernelIso
          (R := R) (M := M) (T := T)))
      x

/-- Helper for Lemma 10.99.12: conjugating a surjective module morphism by source and target
isomorphisms preserves surjectivity of the underlying function. -/
private theorem surjective_of_iso_conjugation
    {A B X Y : ModuleCat R'} (eSource : A ≅ X) (eTarget : B ≅ Y) (f : X ⟶ Y)
    (hf : Function.Surjective f) :
    Function.Surjective (eSource.hom ≫ f ≫ eTarget.inv) := by
  -- Move the target element across the chosen target isomorphism, then pull the preimage back
  -- across the chosen source isomorphism.
  intro y
  rcases hf (eTarget.hom y) with ⟨x, hx⟩
  refine ⟨eSource.inv x, ?_⟩
  change eTarget.inv (f (eSource.hom (eSource.inv x))) = y
  simp [hx]

/-- Helper for Chap10 Lemma 10 99 12: scalar extension is implemented as the left tensor
`R'' ⊗[R'] N`, but the source proof uses the right tensor `N ⊗[R'] R''`; the tensor commutor
provides the explicit linear equivalence between these two spellings. -/
private noncomputable def scalarExtensionTensorLinearEquiv (N : ModuleCat R') :
    TensorProduct R' ↑((resScalars).obj (ModuleCat.of R'' R'')) N ≃ₗ[R']
      TensorProduct R' N R'' := by
  let eR'' : R'' ≃ₗ[R'] ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        have h_source : r • x = (algebraMap R' R'') r * x := Algebra.smul_def r x
        have h_target :
            r • (show ↑((resScalars).obj (ModuleCat.of R'' R'')) from x) =
              (algebraMap R' R'') r * x := by
          simpa [Algebra.smul_def] using
            (@ModuleCat.restrictScalars.smul_def' _ _ _ _ (algebraMap R' R'')
              (ModuleCat.of R'' R'') r x)
        exact h_source.trans h_target.symm }
  -- Commute the tensor factors, then remove the restriction-of-scalars wrapper on `R''`.
  exact
    (TensorProduct.comm R' N ((resScalars).obj (ModuleCat.of R'' R''))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R' N) eR''.symm)

/-- Helper for Chap10 Lemma 10 99 12: scalar extension is implemented as the left tensor
`R'' ⊗[R'] N`, but the source proof uses the right tensor `N ⊗[R'] R''`; the tensor commutor
provides the explicit equivalence between these two spellings. -/
private noncomputable def scalarExtensionCommEquiv (N : ModuleCat R') :
    ↑((extScalars).obj N) ≃ TensorProduct R' N R'' := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (scalarExtensionTensorLinearEquiv (R' := R') (R'' := R'') N).toEquiv

/-- Helper for Chap10 Lemma 10 99 12: the scalar-extension commutor sends a pure tensor in the
left-tensor model `R'' ⊗[R'] N` to the corresponding pure tensor in the right-tensor model
`N ⊗[R'] R''`. -/
private theorem scalarExtensionCommEquiv_tmul
    (N : ModuleCat R') (c : ↑((resScalars).obj (ModuleCat.of R'' R''))) (x : N) :
    scalarExtensionCommEquiv N (show ↑((extScalars).obj N) from c ⊗ₜ[R'] x) =
      x ⊗ₜ[R'] (show R'' from c) := by
  -- Proof comment: unfold the left-tensor/right-tensor bridge once; on a pure tensor it is just
  -- the tensor commutor followed by the identity identification of the coefficient factor.
  simpa [scalarExtensionCommEquiv, scalarExtensionTensorLinearEquiv]
    using
      (show
          (scalarExtensionTensorLinearEquiv (R' := R') (R'' := R'') N).toEquiv
              (show TensorProduct R' ↑((resScalars).obj (ModuleCat.of R'' R'')) N
                from c ⊗ₜ[R'] x) =
            x ⊗ₜ[R'] (show R'' from c) from by
          simp [scalarExtensionTensorLinearEquiv])

/-- Helper for Chap10 Lemma 10 99 12: after rewriting scalar extension through the tensor
commutor, the functorial map on `extScalars` becomes the right-tensor map `f.rTensor R''`. -/
private theorem scalarExtensionCommEquiv_naturality
    {N₁ N₂ : ModuleCat R'} (f : N₁ ⟶ N₂) (z : ↑((extScalars).obj N₁)) :
    scalarExtensionCommEquiv N₂ (((extScalars).map f).hom z) =
      ((ModuleCat.Hom.hom f).rTensor R'')
        (scalarExtensionCommEquiv N₁ z) := by
  -- Proof comment: both sides are additive in the tensor variable, so tensor induction reduces
  -- the comparison to the pure-tensor case where the source proof is `f x ⊗ₜ c` on both sides.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro c x
    simp [scalarExtensionCommEquiv_tmul, ModuleCat.extendScalars, ModuleCat.ExtendScalars.map']
  · intro x y hx hy
    have hcomm₂ :
        scalarExtensionCommEquiv N₂ (((extScalars).map f).hom x + ((extScalars).map f).hom y) =
          scalarExtensionCommEquiv N₂ (((extScalars).map f).hom x) +
            scalarExtensionCommEquiv N₂ (((extScalars).map f).hom y) := by
      -- Proof comment: the commutor bridge comes from a linear equivalence, so it preserves
      -- addition on the target tensor product.
      simpa [scalarExtensionCommEquiv] using
        (scalarExtensionTensorLinearEquiv (R' := R') (R'' := R'') N₂).map_add
          (((extScalars).map f).hom x) (((extScalars).map f).hom y)
    have hcomm₁ :
        scalarExtensionCommEquiv N₁ (x + y) =
          scalarExtensionCommEquiv N₁ x + scalarExtensionCommEquiv N₁ y := by
      -- Proof comment: the same linearity holds on the source tensor object.
      simpa [scalarExtensionCommEquiv] using
        (scalarExtensionTensorLinearEquiv (R' := R') (R'' := R'') N₁).map_add x y
    calc
      scalarExtensionCommEquiv N₂ (((extScalars).map f).hom (x + y)) =
          scalarExtensionCommEquiv N₂ (((extScalars).map f).hom x + ((extScalars).map f).hom y) := by
            rw [LinearMap.map_add]
      _ =
          scalarExtensionCommEquiv N₂ (((extScalars).map f).hom x) +
            scalarExtensionCommEquiv N₂ (((extScalars).map f).hom y) := hcomm₂
      _ =
          ((ModuleCat.Hom.hom f).rTensor R'') (scalarExtensionCommEquiv N₁ x) +
            ((ModuleCat.Hom.hom f).rTensor R'') (scalarExtensionCommEquiv N₁ y) := by
            rw [hx, hy]
      _ =
          ((ModuleCat.Hom.hom f).rTensor R'')
            (scalarExtensionCommEquiv N₁ x + scalarExtensionCommEquiv N₁ y) := by
            rw [LinearMap.map_add]
      _ =
          ((ModuleCat.Hom.hom f).rTensor R'') (scalarExtensionCommEquiv N₁ (x + y)) := by
            rw [← hcomm₁]

/-- Helper for Chap10 Lemma 10 99 12: pulling a target cycle back along the degree-one
base-change isomorphism, then commuting the tensor factors, lands in the kernel of the
tensorized cod-restricted upper source differential. -/
private theorem sourceWindowTensorCyclesMap_rightTensorKernelTransport
    (z : (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).cycles) :
    (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'')
        (scalarExtensionCommEquiv
          (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1)
          ((scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 1).inv.hom
            ((scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).iCycles.hom z))) =
      0 := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e₁ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1
  let e₀ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 0
  let y := e₁.inv.hom (W₂.iCycles.hom z)
  have hz : W₂.g.hom (W₂.iCycles.hom z) = 0 := by
    -- Proof comment: target cycles are exactly the degree-one elements killed by the lower
    -- differential.
    simpa using DFunLike.congr_fun (congrArg ModuleCat.Hom.hom W₂.iCycles_g) z
  have hnat :
      e₁.hom ≫ W₂.g = (extScalars).map W₁.g ≫ e₀.hom := by
    -- Proof comment: the termwise base-change isomorphism is natural for `d₁`.
    simpa [W₁, W₂, e₁, e₀, scalarExtendedDegreeOneWindow, scalar_extended_d_one,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (scalarExtendedResolutionBaseChangeIso_hom_naturality
        (R := R) (R' := R') (R'' := R'') (M := M)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0))
  have hy0 : ((extScalars).map W₁.g).hom y = 0 := by
    -- Proof comment: after transporting the cycle equation across the naturality square, the
    -- pulled-back degree-one element is still killed by the source lower differential.
    have hyImage :
        e₀.hom.hom (((extScalars).map W₁.g).hom y) = 0 := by
      simpa [y, hz] using
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hnat) y).symm
    apply e₀.hom.hom.injective
    simpa using hyImage
  have hcomm :
      ((ModuleCat.Hom.hom W₁.g).rTensor R'')
          (scalarExtensionCommEquiv
            (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1) y) =
        0 := by
    -- Proof comment: commute the left-tensor pullback to the right-tensor model, where the
    -- differential is the ordinary right-tensor map.
    rw [← scalarExtensionCommEquiv_naturality
      (R' := R') (R'' := R'') (f := W₁.g) (z := y)]
    simpa [W₁, scalarExtendedDegreeOneWindow] using
      congrArg
        (scalarExtensionCommEquiv
          (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 0))
        hy0
  have hcomp :
      ((((LinearMap.ker
          (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom).subtype).rTensor R'').comp
          (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor
            R'')) =
        ((ModuleCat.Hom.hom W₁.g).rTensor R'') := by
    -- Proof comment: the cod-restricted upper differential followed by the lower-kernel subtype
    -- is just the raw lower differential, and right tensor preserves that composition.
    rw [← LinearMap.rTensor_comp]
    ext x
    simp [W₁, source_window_upper_to_lower_kernel, source_window_lower_shortComplex,
      scalarExtendedDegreeOneWindow, scalar_extended_d_one]
  apply (tensorizedLowerKernelSubtype_injective (R := R) (R' := R') (R'' := R'') (M := M))
  -- Proof comment: compare the cod-restricted tensor map with the raw lower differential after
  -- postcomposing by the injective lower-kernel subtype.
  simpa [hcomp, y] using hcomm

/-- Helper for Chap10 Lemma 10 99 12: the canonical map `K' ⊗[R'] R'' ⟶ K''` on abstract cycles
is surjective. -/
private theorem sourceWindowTensorCyclesMap_surjective :
    Function.Surjective
      (sourceWindowTensorCyclesMap
        (R := R) (R' := R') (R'' := R'') (M := M)).hom := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e₁ := scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1
  intro z
  let u :
      TensorProduct R'
        (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1) R'' :=
    scalarExtensionCommEquiv
      (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1)
      (e₁.inv.hom (W₂.iCycles.hom z))
  have huKer :
      u ∈ LinearMap.ker
        (((source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).rTensor R'') := by
    -- Proof comment: the previous transport lemma places the commuted pullback exactly in the
    -- kernel needed for the tensorized upper exact row.
    exact sourceWindowTensorCyclesMap_rightTensorKernelTransport
      (R := R) (R' := R') (R'' := R'') (M := M) z
  have huRange :
      u ∈ LinearMap.range
        ((((LinearMap.ker
            (source_window_upper_to_lower_kernel (R := R) (R' := R') (M := M)).hom).subtype).rTensor
          R'')) := by
    -- Proof comment: exactness of the tensorized upper row identifies this kernel with the image
    -- of the tensorized source-cycle inclusion.
    rw [tensorized_source_window_upper_range_eq_ker
      (R := R) (R' := R') (R'' := R'') (M := M)]
    exact huKer
  have huRange' :
      u ∈ LinearMap.range ((((LinearMap.ker W₁.g.hom).subtype).rTensor R'')) := by
    simpa [W₁, scalarExtendedDegreeOneWindow, source_window_upper_to_lower_kernel_ker_eq
      (R := R) (R' := R') (M := M)] using huRange
  rcases LinearMap.mem_range.mp huRange' with ⟨w, hw⟩
  let xTensor : TensorProduct R' W₁.cycles R'' :=
    (((W₁.moduleCatCyclesIso.inv).hom).rTensor R'') w
  let x : ↑((extScalars).obj W₁.cycles) :=
    (scalarExtensionCommEquiv W₁.cycles).symm xTensor
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective W₂.iCycles).1 inferInstance
  rw [sourceWindowTensorCyclesMap_iCycles]
  have hiCyclesComp :
      (((W₁.iCycles.hom).rTensor R'').comp (((W₁.moduleCatCyclesIso.inv).hom).rTensor R'')) =
        (((LinearMap.ker W₁.g.hom).subtype).rTensor R'') := by
    -- Proof comment: after identifying abstract cycles with the concrete kernel of `W₁.g`, the
    -- forgetful map to degree one is literally the kernel subtype.
    rw [← LinearMap.rTensor_comp]
    simpa [W₁] using congrArg ModuleCat.Hom.hom W₁.moduleCatCyclesIso_inv_iCycles
  have hxTensor :
      ((W₁.iCycles.hom).rTensor R'') xTensor = u := by
    -- Proof comment: the concrete witness from `range = ker` becomes a witness on abstract cycles
    -- after transporting it back through `moduleCatCyclesIso`.
    calc
      ((W₁.iCycles.hom).rTensor R'') xTensor =
          (((LinearMap.ker W₁.g.hom).subtype).rTensor R'') w := by
            simpa [xTensor] using LinearMap.congr_fun hiCyclesComp w
      _ = u := by
            simpa [W₁, scalarExtendedDegreeOneWindow, u] using hw
  have hxLeft :
      ((extScalars).map W₁.iCycles).hom x = e₁.inv.hom (W₂.iCycles.hom z) := by
    -- Proof comment: commuting the source cycle witness back to the left-tensor model recovers
    -- the pulled-back target cycle in degree one.
    apply (scalarExtensionCommEquiv
      (scalar_extended_resolution_X (R := R) (R' := R') (M := M) 1)).injective
    rw [scalarExtensionCommEquiv_naturality
      (R' := R') (R'' := R'') (f := W₁.iCycles) (z := x)]
    simpa [x, xTensor, u, W₁] using hxTensor
  -- Proof comment: after applying the base-change isomorphism in degree one, this is exactly the
  -- defining target cycle.
  simpa [hxLeft, e₁] using
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e₁.inv_hom_id) (W₂.iCycles.hom z)

/-- Helper for Lemma 10.99.12: the textbook tensor source is not just a linear map but a linear
equivalence, coming from tensor symmetry after identifying `extendScalars` with a tensor product. -/
private noncomputable def torOneTextbookTensorSourceEquiv :
    TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) := by
  let eR'' : R'' ≃ₗ[R'] ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        have h_source : r • x = (algebraMap R' R'') r * x := Algebra.smul_def r x
        have h_target :
            r • (show ↑((resScalars).obj (ModuleCat.of R'' R'')) from x) =
              (algebraMap R' R'') r * x := by
          simpa [Algebra.smul_def] using
            (@ModuleCat.restrictScalars.smul_def' _ _ _ _ (algebraMap R' R'')
              (ModuleCat.of R'' R'') r x)
        exact h_source.trans h_target.symm }
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    TensorProduct.congr (LinearEquiv.refl R' _) eR''
  let c :
      TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) := by
      simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.comm R' (Tor₁[R](M, R')) ((resScalars).obj (ModuleCat.of R'' R'')))
  exact e.trans c

/-- Helper for Lemma 10.99.12: the textbook tensor source map is surjective because it comes from
the preceding linear equivalence. -/
private theorem torOneTextbookTensorSource_surjective :
    Function.Surjective
      ((torOneTextbookTensorSourceEquiv :
          TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
            ↑((extScalars).obj (Tor₁Obj[R](M, R')))).toLinearMap) :=
  (torOneTextbookTensorSourceEquiv :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R')))).surjective

/-- Helper for Lemma 10.99.12: an internal `R'`-tensor identification with scalar extension,
used to compare the source-window construction with the public `Tor₁` owner. -/
noncomputable def torOneTextbookTensorSource :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
    torOneTextbookTensorSourceEquiv
  e.toLinearMap

/-- Helper for Chap10 Lemma 10 99 12: after forgetting from the coefficient ring `T` down to
`R`, a scalar-extended fixed-resolution term is the ordinary tensor-left term `T ⊗[R] X`. -/
private noncomputable def restrictScalarExtendedResolutionIso
    {T : Type u} [CommRing T] [Algebra R T] (n : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap R T)).obj
      (scalar_extended_resolution_X (R := R) (R' := T) (M := M) n)) ≅
      (ModuleCat.of R T ⊗
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)) := by
  let eCoeff :
      ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[R] T :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by simpa [Algebra.smul_def] }
  simpa [scalar_extended_resolution_X, scalar_extension_functor, scalar_extended_source_resolution,
    ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.congr eCoeff (LinearEquiv.refl R _)).toModuleIso

/-- Helper for Chap10 Lemma 10 99 12: after restricting scalars from `T` to `R`, the termwise
scalar-extension comparison is natural in maps of the fixed source resolution. -/
private theorem restrictScalarExtendedResolutionIso_hom_naturality
    {T : Type u} [CommRing T] [Algebra R T] {n m : ℕ}
    (d :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n) ⟶
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X m)) :
    (ModuleCat.restrictScalars (algebraMap R T)).map
        ((scalar_extension_functor (R := R) (R' := T)).map d) ≫
      (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) m).hom =
    (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom ≫
      ((tensorLeft (ModuleCat.of R T)).map d) := by
  -- Unfold the tensor-product identification once; after that both sides are the same map on
  -- `T ⊗[R] -`, namely tensoring the resolution map `d` on the right.
  let lhs :=
    (ModuleCat.restrictScalars (algebraMap R T)).map
        ((scalar_extension_functor (R := R) (R' := T)).map d) ≫
      (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) m).hom
  let rhs :=
    (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom ≫
      ((tensorLeft (ModuleCat.of R T)).map d)
  ext z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · change lhs.hom 0 = rhs.hom 0
    rw [LinearMap.map_zero, LinearMap.map_zero]
    rfl
  · intro t x
    rfl
  · intro x y hx hy
    change lhs.hom (x + y) = rhs.hom (x + y)
    calc
      lhs.hom (x + y) = lhs.hom x + lhs.hom y := lhs.hom.map_add x y
      _ = rhs.hom x + rhs.hom y := by
        simpa [rhs] using congrArg₂ (· + ·) hx hy
      _ = rhs.hom (x + y) := (rhs.hom.map_add x y).symm

/-- Helper for Chap10 Lemma 10 99 12: braiding converts left tensoring by a map into right
tensoring by the same map. This is the stable categorical ingredient in the restricted-window
comparison. -/
private theorem tensorLeft_braiding_naturality
    {T : Type u} [CommRing T] [Algebra R T] {X Y : ModuleCat R} (d : X ⟶ Y) :
    ((tensorLeft (ModuleCat.of R T)).map d) ≫ (β_ (ModuleCat.of R T) Y).hom =
      (β_ (ModuleCat.of R T) X).hom ≫ ((tensorRight (ModuleCat.of R T)).map d) := by
  -- This is exactly the symmetric-monoidal naturality square specialized to `ModuleCat R`.
  simpa using
    (SemimoduleCat.MonoidalCategory.braiding_naturality_right (ModuleCat.of R T) d)

/-- Helper for Chap10 Lemma 10 99 12: after restricting scalars from `T` to `R`, the explicit
scalar-extension identification is still `T`-linear on each term of the fixed source resolution. -/
private theorem restrictScalarExtendedResolutionIso_hom_smul
    {T : Type u} [CommRing T] [Algebra R T] (t : T) (n : ℕ) :
    (t • 𝟙 ((ModuleCat.restrictScalars (algebraMap R T)).obj
      (scalar_extended_resolution_X (R := R) (R' := T) (M := M) n))) ≫
      (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom =
    (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom ≫
      (t • 𝟙 (ModuleCat.of R T ⊗
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n))) := by
  -- Proof comment: the comparison is the identity-on-pure-tensors scalar-extension model, so it
  -- commutes with multiplication by `t` on the left tensor factor.
  apply ModuleCat.hom_ext
  ext z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · change
      (ModuleCat.Hom.hom
          ((t • 𝟙 ((ModuleCat.restrictScalars (algebraMap R T)).obj
              (scalar_extended_resolution_X (R := R) (R' := T) (M := M) n))) ≫
            (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom)) 0 =
        (ModuleCat.Hom.hom
          ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom ≫
            t • 𝟙
              (ModuleCat.of R T ⊗
                ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)))) 0
    simp
  · intro a x
    rfl
  · intro x y hx hy
    change
      (ModuleCat.Hom.hom
          ((t • 𝟙 ((ModuleCat.restrictScalars (algebraMap R T)).obj
              (scalar_extended_resolution_X (R := R) (R' := T) (M := M) n))) ≫
            (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom)) (x + y) =
        (ModuleCat.Hom.hom
          ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) n).hom ≫
            t • 𝟙
              (ModuleCat.of R T ⊗
                ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)))) (x + y)
    simpa [hx, hy] using congrArg₂ (· + ·) hx hy

/-- Helper for Chap10 Lemma 10 99 12: braiding transports multiplication by `t` on the
coefficient factor to the tensor-right action induced by `Module.toModuleEnd`. -/
private theorem tensorLeft_braiding_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T) (X : ModuleCat R) :
    (t • 𝟙 (ModuleCat.of R T ⊗ X)) ≫ (β_ (ModuleCat.of R T) X).hom =
      (β_ (ModuleCat.of R T) X).hom ≫
        ((tensorRight (ModuleCat.of R T)).map
          ((ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t))) := by
  -- Proof comment: on a pure tensor `a ⊗ x`, both sides evaluate to `x ⊗ (t * a)`.
  apply ModuleCat.hom_ext
  ext z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · change
      (ModuleCat.Hom.hom
          ((t • 𝟙 (ModuleCat.of R T ⊗ X)) ≫ (β_ (ModuleCat.of R T) X).hom)) 0 =
        (ModuleCat.Hom.hom
          ((β_ (ModuleCat.of R T) X).hom ≫
            (tensorRight (ModuleCat.of R T)).map
              ((ModuleCat.of R T).endRingEquiv.symm
                (Module.toModuleEnd R T t)))) 0
    simp
  · intro a x
    simp [moduleToModuleEnd_apply, Algebra.smul_def]
  · intro x y hx hy
    change
      (ModuleCat.Hom.hom
          ((t • 𝟙 (ModuleCat.of R T ⊗ X)) ≫ (β_ (ModuleCat.of R T) X).hom)) (x + y) =
        (ModuleCat.Hom.hom
          ((β_ (ModuleCat.of R T) X).hom ≫
            (tensorRight (ModuleCat.of R T)).map
              ((ModuleCat.of R T).endRingEquiv.symm
                (Module.toModuleEnd R T t)))) (x + y)
    simpa [hx, hy] using congrArg₂ (· + ·) hx hy

/-- Helper for Chap10 Lemma 10 99 12: after forgetting from the coefficient ring `T` down to
`R`, the scalar-extended degree-one source window is literally the tensor-right degree-one
window on the fixed projective resolution of `M`. -/
private noncomputable def tensorRightDegreeOneWindowRestrictIso
    {T : Type u} [CommRing T] [Algebra R T] :
    ((scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).map
      (ModuleCat.restrictScalars (algebraMap R T))) ≅
      tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) := by
  let d₂ := ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1)
  let d₁ := ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0)
  -- Route correction: pay the restrict-scalars/tensor-right transport once at the short-complex
  -- level, instead of expanding the same tensor-coercion square in each downstream proof.
  refine ShortComplex.isoMk
    ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2) ≪≫
      (β_ (ModuleCat.of R T)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)))
    ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1) ≪≫
      (β_ (ModuleCat.of R T)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)))
    ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 0) ≪≫
      (β_ (ModuleCat.of R T)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)))
    ?_ ?_
  · -- First compare the restricted `d₂` square with tensor-left naturality, then braid to the
    -- tensor-right spelling used by the source-owner window.
    calc
      ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2).hom ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)).hom) ≫
          ((tensorRight (ModuleCat.of R T)).map d₂) =
        (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2).hom ≫
          ((β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)).hom ≫
            ((tensorRight (ModuleCat.of R T)).map d₂)) := by
          rw [Category.assoc]
      _ =
        (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2).hom ≫
          (((tensorLeft (ModuleCat.of R T)).map d₂) ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom) := by
          exact congrArg
            (fun k ↦
              (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2).hom ≫ k)
            (tensorLeft_braiding_naturality (R := R) (T := T) d₂).symm
      _ =
        ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 2).hom ≫
            (tensorLeft (ModuleCat.of R T)).map d₂) ≫
          (β_ (ModuleCat.of R T)
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom := by
          rw [Category.assoc]
      _ =
        (((ModuleCat.restrictScalars (algebraMap R T)).map
              ((scalar_extension_functor (R := R) (R' := T)).map d₂) ≫
            (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom)) ≫
          (β_ (ModuleCat.of R T)
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom := by
          exact congrArg
            (fun k ↦
              k ≫
                (β_ (ModuleCat.of R T)
                  ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom)
            (restrictScalarExtendedResolutionIso_hom_naturality
              (R := R) (M := M) (T := T) d₂).symm
      _ =
        (ModuleCat.restrictScalars (algebraMap R T)).map
            ((scalar_extension_functor (R := R) (R' := T)).map d₂) ≫
          ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom) := by
          simp [Category.assoc]
  · -- The same argument identifies the restricted `d₁` square with the tensor-right source
    -- window.
    calc
      ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom) ≫
          ((tensorRight (ModuleCat.of R T)).map d₁) =
        (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫
          ((β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom ≫
            ((tensorRight (ModuleCat.of R T)).map d₁)) := by
          rw [Category.assoc]
      _ =
        (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫
          (((tensorLeft (ModuleCat.of R T)).map d₁) ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom) := by
          exact congrArg
            (fun k ↦
              (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫ k)
            (tensorLeft_braiding_naturality (R := R) (T := T) d₁).symm
      _ =
        ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 1).hom ≫
            (tensorLeft (ModuleCat.of R T)).map d₁) ≫
          (β_ (ModuleCat.of R T)
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom := by
          rw [Category.assoc]
      _ =
        (((ModuleCat.restrictScalars (algebraMap R T)).map
              ((scalar_extension_functor (R := R) (R' := T)).map d₁) ≫
            (restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 0).hom)) ≫
          (β_ (ModuleCat.of R T)
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom := by
          exact congrArg
            (fun k ↦
              k ≫
                (β_ (ModuleCat.of R T)
                  ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom)
            (restrictScalarExtendedResolutionIso_hom_naturality
              (R := R) (M := M) (T := T) d₁).symm
      _ =
        (ModuleCat.restrictScalars (algebraMap R T)).map
            ((scalar_extension_functor (R := R) (R' := T)).map d₁) ≫
          ((restrictScalarExtendedResolutionIso (R := R) (M := M) (T := T) 0).hom ≫
            (β_ (ModuleCat.of R T)
              ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom) := by
          simp [Category.assoc]

/-- Helper for Chap10 Lemma 10 99 12: after transporting the tensor-right degree-one window
through the restricted scalar-extension comparison, multiplication by `t` on the coefficient
factor becomes literal scalar multiplication on the restricted scalar-extended window. -/
private theorem tensorRightDegreeOneWindowRestrictIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    let φ_t :
        tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) ⟶
          tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) :=
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).map
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app
            (CategoryTheory.ProjectiveResolution.complex
              (CategoryTheory.projectiveResolution (ModuleCat.of R M))))
    (t • 𝟙 (((scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).map
        (ModuleCat.restrictScalars (algebraMap R T))))) ≫
      (tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)).hom =
    (tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)).hom ≫ φ_t := by
  -- Proof comment: each component of the short-complex comparison is `restrictIso ≫ β`, so the
  -- statement reduces componentwise to `restrictIso`-linearity and the braiding action formula.
  intro μ_t φ_t
  ext <;>
    simp [tensorRightDegreeOneWindowRestrictIso, restrictScalarExtendedResolutionIso_hom_smul,
      tensorLeft_braiding_map_actionEnd, Category.assoc]

/-- Helper for Chap10 Lemma 10 99 12: the public object `Tor₁^R(M,T)` and the degree-one
homology of the scalar-extended fixed source window are already canonically isomorphic after
forgetting from `T`-modules to `R`-modules. -/
private noncomputable def sourceOwnerWindowRestrictIso
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
      ((ModuleCat.restrictScalars (algebraMap R T)).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) := by
  -- First compute source-owner `Tor₁` by the degree-one tensor-right window of the fixed
  -- projective resolution of `M`.
  let eWindow :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
        ShortComplex.homology
          (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) (ModuleCat.of R T) ≪≫
      tensorRight_degree_one_window_homology_iso
        (R := R) (ModuleCat.of R T) (ModuleCat.of R M)
  -- Then transport that source window to the restricted scalar-extended window and identify
  -- its homology with the restricted homology of the `T`-linear source window.
  let eRestrictWindow :
      ShortComplex.homology
          (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) ≅
        ((ModuleCat.restrictScalars (algebraMap R T)).obj
          (ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) :=
    ShortComplex.homologyMapIso
        (tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)).symm ≪≫
      (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap R T))
  exact eWindow ≪≫ eRestrictWindow

/-- Helper for Chap10 Lemma 10 99 12: the fixed-resolution source-owner computation carries the
coefficient action of `μ_t` to the induced homology map on the explicit degree-one tensor-right
window. -/
private theorem sourceOwnerDegreeOneWindowHomologyIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (x : (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    let φ_t :
        tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) ⟶
          tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) :=
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).map
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app
            (CategoryTheory.ProjectiveResolution.complex
              (CategoryTheory.projectiveResolution (ModuleCat.of R M))))
    let eWindow :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
          ShortComplex.homology
            (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) :=
      sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) (ModuleCat.of R T) ≪≫
        tensorRight_degree_one_window_homology_iso
          (R := R) (ModuleCat.of R T) (ModuleCat.of R M)
    eWindow.hom.hom ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) =
      (ShortComplex.homologyMap φ_t).hom (eWindow.hom.hom x) := by
  intro μ_t φ_t eWindow
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of R M)
  have hSourceMap :
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t)) =
        (sourceOwnerDegreeOneProjectiveResolutionIso
            (R := R) (M := M) (ModuleCat.of R T)).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).map
            ((NatTrans.mapHomologicalComplex
              ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app
                P.complex) ≫
          (sourceOwnerDegreeOneProjectiveResolutionIso
            (R := R) (M := M) (ModuleCat.of R T)).inv := by
    -- Proof comment: compute the source-owner action on the fixed projective resolution of `M`.
    simpa [P, source_tor_owner_eq_leftDerived_obj, sourceOwnerDegreeOneProjectiveResolutionIso,
      Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} R)).map μ_t) P 1)
  have hWindowNat :
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).map
          ((NatTrans.mapHomologicalComplex
            ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app P.complex) ≫
        (tensorRight_degree_one_window_homology_iso
          (R := R) (ModuleCat.of R T) (ModuleCat.of R M)).hom =
      (tensorRight_degree_one_window_homology_iso
          (R := R) (ModuleCat.of R T) (ModuleCat.of R M)).hom ≫
        ShortComplex.homologyMap φ_t := by
    -- Proof comment: naturality of `homologyFunctorIso'` is exactly the passage from full
    -- degree-one homology to the explicit `2 → 1 → 0` window.
    simpa [P, φ_t, tensorRight_degree_one_window_homology_iso, Functor.comp_map,
      Category.assoc] using
      ((HomologicalComplex.homologyFunctorIso'
          (C := ModuleCat R) (c := ComplexShape.down ℕ)
          (i := 2) (j := 1) (k := 0) (by simp) (by simp)).hom.naturality
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app P.complex))
  have hComm :
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t)) ≫ eWindow.hom =
        eWindow.hom ≫ ShortComplex.homologyMap φ_t := by
    -- Proof comment: compose the fixed-resolution computation with the window naturality square.
    dsimp [eWindow]
    rw [hSourceMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hWindowNat]
    simp [Category.assoc]
  exact
    DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom hComm)
      x

/-- Helper for Chap10 Lemma 10 99 12: the comparison from the tensor-right window homology to the
restricted scalar-extended window homology carries the induced homology action to literal scalar
multiplication by `t`. -/
private theorem tensorRightDegreeOneWindowRestrictHomologyIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (z : ShortComplex.homology
      (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    let φ_t :
        tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) ⟶
          tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) :=
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).map
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app
            (CategoryTheory.ProjectiveResolution.complex
              (CategoryTheory.projectiveResolution (ModuleCat.of R M))))
    let eRestrictWindow :
        ShortComplex.homology
            (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) ≅
          ((ModuleCat.restrictScalars (algebraMap R T)).obj
            (ShortComplex.homology
              (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) :=
      ShortComplex.homologyMapIso
          (tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)).symm ≪≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).mapHomologyIso
          (ModuleCat.restrictScalars (algebraMap R T))
    eRestrictWindow.hom.hom ((ShortComplex.homologyMap φ_t).hom z) =
      t • eRestrictWindow.hom.hom z := by
  intro μ_t φ_t eRestrictWindow
  let S :=
    (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).map
      (ModuleCat.restrictScalars (algebraMap R T))
  let eIso := tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)
  have hIsoInv :
      φ_t ≫ eIso.inv = eIso.inv ≫ (t • 𝟙 S) := by
    -- Proof comment: invert the already-proved short-complex comparison square so the transport
    -- runs from the tensor-right window back to the restricted scalar-extended window.
    apply (cancel_mono eIso.hom).1
    simpa [S, eIso, Category.assoc] using
      (tensorRightDegreeOneWindowRestrictIso_hom_map_actionEnd
        (R := R) (M := M) (T := T) t)
  have hRestrictWindow :
      (ShortComplex.homologyMap φ_t) ≫
          (ShortComplex.homologyMapIso eIso.symm).hom =
        (ShortComplex.homologyMapIso eIso.symm).hom ≫
          ShortComplex.homologyMap (t • 𝟙 S) := by
    -- Proof comment: passing to homology preserves the inverted short-complex action square.
    simpa [ShortComplex.homologyMap_comp, Category.assoc] using
      congrArg ShortComplex.homologyMap hIsoInv
  have hMapHomology :
      ShortComplex.homologyMap (t • 𝟙 S) ≫
          ((scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).mapHomologyIso
            (ModuleCat.restrictScalars (algebraMap R T))).hom =
        ((scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).mapHomologyIso
          (ModuleCat.restrictScalars (algebraMap R T))).hom ≫
            (ModuleCat.restrictScalars (algebraMap R T)).map
              (ShortComplex.homologyMap
                (t • 𝟙 (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) := by
    -- Proof comment: this is the standard naturality of `mapHomologyIso` for the restrict-scalars
    -- functor applied to the scalar multiplication endomorphism of the `T`-linear window.
    simpa [S] using
      (ShortComplex.mapHomologyIso_hom_naturality
        (F := ModuleCat.restrictScalars (algebraMap R T))
        (φ := t • 𝟙 (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M))))
  have hComm :
      (ShortComplex.homologyMap φ_t) ≫ eRestrictWindow.hom =
        eRestrictWindow.hom ≫
          (t • 𝟙 ((ModuleCat.restrictScalars (algebraMap R T)).obj
            (ShortComplex.homology
              (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M))))) := by
    -- Proof comment: first move across the explicit window isomorphism, then convert the mapped
    -- homology endomorphism of the `T`-linear window into literal scalar multiplication.
    dsimp [eRestrictWindow]
    rw [Category.assoc, hRestrictWindow]
    simp only [Category.assoc]
    rw [hMapHomology]
    simp only [Category.assoc]
    rw [ShortComplex.homologyMap_smul]
    simp [moduleToModuleEnd_apply]
  have hPoint :=
    DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom hComm)
      z
  simpa using hPoint

/-- Helper for Chap10 Lemma 10 99 12: the public-to-source owner comparison commutes with the
action-end map induced by multiplication by `t` on the coefficient ring. -/
private noncomputable def ringCoeffTorOneKernelTargetActionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T) :
    ringCoeffTorOneKernelTarget (R := R) (M := M) (T := T) ⟶
      ringCoeffTorOneKernelTarget (R := R) (M := M) (T := T) := by
  let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
    (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
  -- Proof comment: package the target-kernel action by conjugating the explicit source-owner
  -- action through the already constructed source kernel identification.
  exact
    (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).inv ≫
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t)) ≫
      (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom

/-- Helper for Chap10 Lemma 10 99 12: by construction, the source kernel identification carries
the coefficient action of `μ_t` to the conjugated endomorphism of the common kernel target. -/
private theorem ringCoeffTorOneSourceKernelIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (y : (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom y) =
      (ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom
        ((ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom y) := by
  intro μ_t
  -- Proof comment: unfold the conjugated target action once; after that both sides are the same
  -- composite `sourceKernelIso.hom ≫ map μ_t`.
  simpa [ringCoeffTorOneKernelTargetActionEnd, Category.assoc]

/-- Helper for Chap10 Lemma 10 99 12: expose the private five-term exact-row witness from
Lemma 10.75.2 that underlies the public connector for the coefficient kernel row. -/
private noncomputable abbrev ringCoeffTorOnePublicFiveTermWitness
    {T : Type u} [CommRing T] [Algebra R T] :=
  _private.stacks_project.Chap10.Lemma_10_75_2.0.ModuleCat.tor_one_tensor_five_term_exact_of_shortExact
    (R := R) (M := ModuleCat.of R M)
    (S := ringCoeffTorOneKernelRow (R := R) (T := T))
    (ringCoeffTorOneKernelRow_shortExact (R := R) (T := T))

/-- Helper for Chap10 Lemma 10 99 12: the public connector `ringCoeffTorOnePublicKernelMap`
really is the connecting morphism chosen from the five-term exact row of the coefficient kernel
presentation. -/
private theorem ringCoeffTorOnePublicKernelMap_eq_choose
    {T : Type u} [CommRing T] [Algebra R T] :
    ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T) =
      Classical.choose (ringCoeffTorOnePublicFiveTermWitness (R := R) (M := M) (T := T)) := by
  -- Proof comment: `torTensorSixTermSequence.map' 2 3` is definitionally the chosen five-term
  -- connector from Lemma 10.75.2 specialized to the coefficient kernel row.
  rfl

/-- Helper for Chap10 Lemma 10 99 12: the exposed five-term witness already packages the exact
public row adjacent to `ringCoeffTorOnePublicKernelMap`. -/
private theorem ringCoeffTorOnePublicKernelMap_exact_row
    {T : Type u} [CommRing T] [Algebra R T] :
    (ComposableArrows.mk₅
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
        (ringCoeffTorOneKernelRow (R := R) (T := T)).f)
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
        (ringCoeffTorOneKernelRow (R := R) (T := T)).g)
      (ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T))
      ((tensorLeft (ModuleCat.of R M)).map
        (ringCoeffTorOneKernelRow (R := R) (T := T)).f)
      ((tensorLeft (ModuleCat.of R M)).map
        (ringCoeffTorOneKernelRow (R := R) (T := T)).g)).Exact := by
  -- Proof comment: after exposing the underlying witness, the exactness is exactly the
  -- `Classical.choose_spec` payload from Lemma 10.75.2.
  simpa [ringCoeffTorOnePublicKernelMap_eq_choose]
    using Classical.choose_spec
      (ringCoeffTorOnePublicFiveTermWitness (R := R) (M := M) (T := T))

/-- Helper for Chap10 Lemma 10 99 12: the public kernel identification should carry the
coefficient action of `μ_t` to the same conjugated endomorphism of the common kernel target. -/
private theorem ringCoeffTorOnePublicKernelIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (x : (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    (ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) =
      (ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom
        ((ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom x) := by
  intro μ_t
  let K := ringCoeffTorOneKernelRow (R := R) (T := T)
  let δPub := ringCoeffTorOnePublicKernelMap (R := R) (M := M) (T := T)
  let β := ((tensorLeft (ModuleCat.of R M)).map K.f)
  have hPubLeft :
      Function.Exact ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g).hom) δPub.hom :=
    ringCoeffTorOnePublicKernelMap_exact_left (R := R) (M := M) (T := T)
  have hPubRight :
      Function.Exact δPub.hom β.hom :=
    ringCoeffTorOnePublicKernelMap_exact_right (R := R) (M := M) (T := T)
  have hProjK₂ : Projective K.X₂ := by
    simpa [K, ringCoeffTorOneKernelRow, LinearMap.shortComplexKer] using
      ((CategoryTheory.projectiveResolution (ModuleCat.of R T)).projective 0)
  have hPubZero :
      IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj K.X₂)) := by
    letI : Projective K.X₂ := hProjK₂
    exact publicTorOneProjectiveRight_isZero (R := R) (M := M) K.X₂
  apply Subtype.ext
  change
    (((kernelIsoOfExactPairAndIsZeroLeft
        (R := R)
        (α := (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g))
        (δ := δPub) (β := β) hPubLeft hPubRight hPubZero).hom.hom
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x))).1
      =
    (((ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom
        ((ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom x))).1
  rw [kernelIsoOfExactPairAndIsZeroLeft_hom_apply
    (R := R)
    (α := (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map K.g))
    (δ := δPub) (β := β) hPubLeft hPubRight hPubZero]
  simp [ringCoeffTorOneKernelTargetActionEnd, K, δPub, β, Category.assoc]

/-- Helper for Chap10 Lemma 10 99 12: the public-to-source owner comparison commutes with the
action-end map induced by multiplication by `t` on the coefficient ring. -/
private theorem ringCoeffTorOneOwnerKernelComparison_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (x : (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    (ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) =
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom)
        ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x) := by
  -- Route correction: the planned five-term-row proof wants the canonical connecting morphisms
  -- from `Lemma_10_75_2`, but those constructors are private there and are not callable from this
  -- item file. The remaining proof therefore needs an explicit local naturality API for the
  -- chosen public/source kernel maps before the common-kernel comparison can be closed here.
  intro μ_t
  -- Proof comment: pass to the common kernel target via the source kernel isomorphism, rewrite
  -- both sides to the same conjugated kernel action, and then cancel the source kernel map.
  apply (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom.injective
  calc
    (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom
          ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x)) =
      (ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) := by
          exact ringCoeffTorOneOwnerKernelComparison_hom_apply_sourceKernelIso
            (R := R) (M := M) (T := T)
            ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x)
    _ =
      (ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom
        ((ringCoeffTorOnePublicKernelIso (R := R) (M := M) (T := T)).hom.hom x) := by
          exact ringCoeffTorOnePublicKernelIso_hom_map_actionEnd
            (R := R) (M := M) (T := T) t x
    _ =
      (ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom
        ((ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom
          ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x)) := by
          exact congrArg
            ((ringCoeffTorOneKernelTargetActionEnd (R := R) (M := M) (T := T) t).hom)
            (ringCoeffTorOneOwnerKernelComparison_hom_apply_sourceKernelIso
              (R := R) (M := M) (T := T) x).symm
    _ =
      (ringCoeffTorOneSourceKernelIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom
          ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x)) := by
          symm
          exact ringCoeffTorOneSourceKernelIso_hom_map_actionEnd
            (R := R) (M := M) (T := T) t
            ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x)

/-- Helper for Chap10 Lemma 10 99 12: after moving to the fixed-resolution source window, the
source-owner action-end map induced by multiplication by `t` becomes literal scalar
multiplication on the scalar-extended degree-one homology. -/
private theorem sourceOwnerWindowRestrictIso_hom_map_actionEnd
    {T : Type u} [CommRing T] [Algebra R T] (t : T)
    (x : (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T))) :
    let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
      (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
    (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) =
      t • (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom x := by
  intro μ_t
  let φ_t :
      tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) ⟶
        tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M) :=
    (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).map
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} R)).map μ_t) (ComplexShape.down ℕ)).app
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M))))
  let eWindow :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
        ShortComplex.homology
          (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) :=
    sourceOwnerDegreeOneProjectiveResolutionIso (R := R) (M := M) (ModuleCat.of R T) ≪≫
      tensorRight_degree_one_window_homology_iso
        (R := R) (ModuleCat.of R T) (ModuleCat.of R M)
  let eRestrictWindow :
      ShortComplex.homology
          (tensorRight_degree_one_window (R := R) (ModuleCat.of R T) (ModuleCat.of R M)) ≅
        ((ModuleCat.restrictScalars (algebraMap R T)).obj
          (ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) :=
    ShortComplex.homologyMapIso
        (tensorRightDegreeOneWindowRestrictIso (R := R) (M := M) (T := T)).symm ≪≫
      (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap R T))
  -- Route correction: keep the two transport boundaries separate, first from source-owner Tor to
  -- the tensor-right window, then from that window to the restricted scalar-extended homology.
  calc
    (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x) =
      eRestrictWindow.hom.hom
        (eWindow.hom.hom
          ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x)) := by
            rfl
    _ =
      eRestrictWindow.hom.hom
        ((ShortComplex.homologyMap φ_t).hom (eWindow.hom.hom x)) := by
            rw [sourceOwnerDegreeOneWindowHomologyIso_hom_map_actionEnd
              (R := R) (M := M) (T := T) t x]
    _ = t • eRestrictWindow.hom.hom (eWindow.hom.hom x) := by
            exact tensorRightDegreeOneWindowRestrictHomologyIso_hom_map_actionEnd
              (R := R) (M := M) (T := T) t (eWindow.hom.hom x)
    _ =
      t • (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom x := by
            rfl

/-- Helper for Chap10 Lemma 10 99 12: the public object `Tor₁^R(M,T)` and the degree-one
homology of the scalar-extended fixed source window are already canonically isomorphic after
forgetting from `T`-modules to `R`-modules. -/
private noncomputable def ringCoeffTorOneWindowRestrictIso
    {T : Type u} [CommRing T] [Algebra R T] :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
      ((ModuleCat.restrictScalars (algebraMap R T)).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)))) := by
  -- First move from the public coefficient owner to the fixed-left source owner.
  let eOwner :
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) ≅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R T)) :=
    ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)
  -- Then pass through the fixed source-window comparison already isolated above.
  exact eOwner ≪≫ sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)

/-- Helper for Chap10 Lemma 10 99 12: the restricted endpoint comparison already respects the
`T`-scalar action on underlying elements. This is the only remaining bridge needed to package the
endpoint comparison inside `ModuleCat T`. -/
private theorem ringCoeffTorOneWindowRestrictIso_hom_smul
    {T : Type u} [CommRing T] [Algebra R T] (t : T) (x : Tor₁[R](M, T)) :
    (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom (t • x) =
      t • (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom x := by
  let μ_t : ModuleCat.of R T ⟶ ModuleCat.of R T :=
    (ModuleCat.of R T).endRingEquiv.symm (Module.toModuleEnd R T t)
  -- Proof comment: first rewrite the public Tor scalar action as the mapped coefficient
  -- endomorphism, then separate the remaining work into the owner-comparison square and the
  -- source-window scalar action.
  rw [torOne_smul_eq_map_actionEnd (R := R) (M := M) (T := T) t x]
  calc
    (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x)
      =
        (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
          ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom
            ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom x)) := by
          rfl
    _ =
        (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
          ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map μ_t).hom
            ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x)) := by
          rw [ringCoeffTorOneOwnerKernelComparison_hom_map_actionEnd
            (R := R) (M := M) (T := T) t x]
    _ =
        t • (sourceOwnerWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
          ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x) := by
          exact sourceOwnerWindowRestrictIso_hom_map_actionEnd
            (R := R) (M := M) (T := T) t
            ((ringCoeffTorOneOwnerKernelComparison (R := R) (M := M) (T := T)).hom.hom x)
    _ =
        t • (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom x := by
          rfl

/-- Helper for Chap10 Lemma 10 99 12: the restricted endpoint comparison repackaged as a genuine
`T`-linear morphism. -/
private noncomputable def ringCoeffTorOneWindowLinearMap
    {T : Type u} [CommRing T] [Algebra R T] :
    ModuleCat.of T (Tor₁[R](M, T)) ⟶
      ShortComplex.homology (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)) :=
  ModuleCat.ofHom
    { toFun := (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom
      map_add' := (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).hom.hom.map_add
      map_smul' := fun t x ↦
        ringCoeffTorOneWindowRestrictIso_hom_smul (R := R) (M := M) (T := T) t x }

/-- Helper for Chap10 Lemma 10 99 12: the packaged `T`-linear endpoint map is bijective because
its underlying function is the same as the already invertible restricted comparison. -/
private theorem ringCoeffTorOneWindowLinearMap_bijective
    {T : Type u} [CommRing T] [Algebra R T] :
    Function.Bijective (ringCoeffTorOneWindowLinearMap (R := R) (M := M) (T := T)).hom := by
  -- The repackaged map has the same underlying function as the previously constructed
  -- restricted-scalars isomorphism.
  simpa [ringCoeffTorOneWindowLinearMap] using
    (ringCoeffTorOneWindowRestrictIso (R := R) (M := M) (T := T)).toLinearEquiv.bijective

/-- Helper for Chap10 Lemma 10 99 12: the endpoint comparison upgraded to an isomorphism in the
coefficient category `ModuleCat T`. -/
private noncomputable def ringCoeffTorOneWindowIso
    {T : Type u} [CommRing T] [Algebra R T] :
    ModuleCat.of T (Tor₁[R](M, T)) ≅
      ShortComplex.homology (scalarExtendedDegreeOneWindow (R := R) (R' := T) (M := M)) :=
  (LinearEquiv.ofBijective
    (ringCoeffTorOneWindowLinearMap (R := R) (M := M) (T := T)).hom
    (ringCoeffTorOneWindowLinearMap_bijective (R := R) (M := M) (T := T))).toModuleIso

/-- Helper for Chap10 Lemma 10 99 12: after extending scalars from `R'` to `R''`, the public
degree-one `Tor` object over `R'` identifies with the scalar-extended homology of the fixed
source window at `R'`. -/
private noncomputable def torOneBaseChangeSourceWindowIso :
    (extScalars).obj (Tor₁Obj[R](M, R')) ≅
      (extScalars).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) :=
  (extScalars).mapIso (ringCoeffTorOneWindowIso (R := R) (M := M) (T := R'))

/-- Helper for Chap10 Lemma 10 99 12: the target public `Tor₁^R(M, R'')` is already the degree-one
homology of the scalar-extended fixed source window at `R''`. -/
private noncomputable def torOneBaseChangeTargetWindowIso :
    Tor₁Obj[R](M, R'') ≅
      ShortComplex.homology
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)) :=
  ringCoeffTorOneWindowIso (R := R) (M := M) (T := R'')

/-- Helper for Chap10 Lemma 10 99 12: the public base-change comparison obtained by conjugating
the window-level comparison through the endpoint identifications. -/
  private noncomputable def torOneBaseChangeComparisonOfWindow
    (windowComparison :
      (extScalars).obj
          (ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) ⟶
        ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M))) :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  (torOneBaseChangeSourceWindowIso (R := R) (R' := R') (R'' := R'') (M := M)).hom ≫
    windowComparison ≫
    (torOneBaseChangeTargetWindowIso (R := R) (R'' := R'') (M := M)).inv

/-- Helper for Chap10 Lemma 10 99 12: conjugating the surjective window comparison by the
endpoint identifications yields the surjective public base-change comparison. -/
private theorem torOneBaseChangeComparison_surjective_of_window
    {windowComparison :
      (extScalars).obj
          (ShortComplex.homology
            (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) ⟶
        ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M))}
    (hwindowComparison : Function.Surjective windowComparison.hom) :
    Function.Surjective
      (torOneBaseChangeComparisonOfWindow
        (R := R) (R' := R') (R'' := R'') (M := M) windowComparison).hom := by
  let eSource := torOneBaseChangeSourceWindowIso (R := R) (R' := R') (R'' := R'') (M := M)
  let eTarget := torOneBaseChangeTargetWindowIso (R := R) (R'' := R'') (M := M)
  -- Reuse the generic conjugation lemma to keep the owner/window transport separate
  -- from the surjectivity argument itself.
  simpa [torOneBaseChangeComparisonOfWindow] using
    surjective_of_iso_conjugation eSource eTarget windowComparison hwindowComparison

/-- Helper for Chap10 Lemma 10 99 12: choose the source-window homology comparison coming from the
surjective tensorized cycle map. -/
private noncomputable def torOneBaseChangeWindowComparison :
    (extScalars).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) ⟶
      ShortComplex.homology
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)) :=
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let k := sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)
  let sourceCofork := CokernelCofork.ofπ W₁.homologyπ W₁.toCycles_comp_homologyπ
  let hColim : IsColimit (sourceCofork.map extScalars) := by
    -- Proof comment: scalar extension preserves the cokernel presenting source homology.
    exact CokernelCofork.mapIsColimit (c := sourceCofork) W₁.homologyIsCokernel extScalars
  let hkill : (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) = 0 := by
    -- Proof comment: the tensorized cycle map sends source boundaries to target boundaries, so
    -- the target homology quotient kills the composite.
    calc
      (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) =
          ((extScalars).map W₁.toCycles ≫ k) ≫ W₂.homologyπ := by
            rw [Category.assoc]
      _ = ((scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫ W₂.toCycles) ≫
            W₂.homologyπ := by
            rw [sourceWindowTensorCyclesMap_comp_boundaries]
      _ = (scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫
            (W₂.toCycles ≫ W₂.homologyπ) := by
            rw [Category.assoc]
      _ = 0 := by
            rw [W₂.toCycles_comp_homologyπ, comp_zero]
  hColim.desc (CokernelCofork.ofπ (k ≫ W₂.homologyπ) hkill)

/-- Helper for Chap10 Lemma 10 99 12: the canonical source-window comparison is defined by the
same `homologyπ` factorization as the textbook cycle map. -/
private theorem torOneBaseChangeWindowComparison_homologyPi_fac :
    (extScalars).map
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).homologyπ ≫
        torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M) =
      sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).homologyπ := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let k := sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)
  let sourceCofork := CokernelCofork.ofπ W₁.homologyπ W₁.toCycles_comp_homologyπ
  let hColim : IsColimit (sourceCofork.map extScalars) := by
    -- Proof comment: reuse the mapped cokernel presenting source homology.
    exact CokernelCofork.mapIsColimit (c := sourceCofork) W₁.homologyIsCokernel extScalars
  let hkill : (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) = 0 := by
    -- Proof comment: the same boundary computation used in the definition identifies the
    -- descended homology map with the cycle-level base-change map.
    calc
      (extScalars).map W₁.toCycles ≫ (k ≫ W₂.homologyπ) =
          ((extScalars).map W₁.toCycles ≫ k) ≫ W₂.homologyπ := by
            rw [Category.assoc]
      _ = ((scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫ W₂.toCycles) ≫
            W₂.homologyπ := by
            rw [sourceWindowTensorCyclesMap_comp_boundaries]
      _ = (scalarExtendedResolutionBaseChangeIso
              (R := R) (R' := R') (R'' := R'') (M := M) 2).hom ≫
            (W₂.toCycles ≫ W₂.homologyπ) := by
            rw [Category.assoc]
      _ = 0 := by
            rw [W₂.toCycles_comp_homologyπ, comp_zero]
  -- Proof comment: `hColim.fac` is exactly the defining factorization of the descended map.
  simpa [torOneBaseChangeWindowComparison, W₁, W₂, k, sourceCofork, hColim, hkill] using
    hColim.fac (CokernelCofork.ofπ (k ≫ W₂.homologyπ) hkill) WalkingParallelPair.one

/-- Helper for Chap10 Lemma 10 99 12: the base-changed degree-one source window is explicitly
identified with the target degree-one source window by the termwise scalar-extension comparison
isomorphisms. -/
private noncomputable def scalarExtendedDegreeOneWindowBaseChangeIsoExplicit :
    (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).map extScalars ≅
      scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M) := by
  -- Proof comment: package the termwise scalar-extension comparison isomorphisms once at the
  -- short-complex level so the later homology comparison can compute on the middle term directly.
  refine ShortComplex.isoMk
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 2)
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 1)
    (scalarExtendedResolutionBaseChangeIso (R := R) (R' := R') (R'' := R'') (M := M) 0)
    ?_ ?_
  · -- Proof comment: the first square is the termwise base-change naturality square for `d₂`.
    simpa [scalarExtendedDegreeOneWindow, scalar_extended_d_two, scalar_extended_resolution_X,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (scalarExtendedResolutionBaseChangeIso_hom_naturality
        (R := R) (R' := R') (R'' := R'') (M := M)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1))
  · -- Proof comment: the second square is the corresponding naturality square for `d₁`.
    simpa [scalarExtendedDegreeOneWindow, scalar_extended_d_one, scalar_extended_resolution_X,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (scalarExtendedResolutionBaseChangeIso_hom_naturality
        (R := R) (R' := R') (R'' := R'') (M := M)
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0))

/-- Helper for Chap10 Lemma 10 99 12: the canonical window comparison obtained by transporting the
source homology across the explicit degree-one source-window base-change isomorphism. -/
private noncomputable def scalarExtendedDegreeOneWindowBaseChangeComparison :
    (extScalars).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M))) ⟶
      ShortComplex.homology
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)) :=
  ((scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).mapHomologyIso extScalars).inv ≫
    ShortComplex.homologyMap
      (scalarExtendedDegreeOneWindowBaseChangeIsoExplicit
        (R := R) (R' := R') (R'' := R'') (M := M)).hom

/-- Helper for Chap10 Lemma 10 99 12: after transporting source cycles through
`mapCyclesIso`, the explicit short-complex base-change isomorphism induces exactly the textbook
cycle map `K' ⊗[R'] R'' ⟶ K''`. -/
private theorem scalarExtendedDegreeOneWindowBaseChangeComparison_cyclesMap :
    ((scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).mapCyclesIso extScalars).inv ≫
        ShortComplex.cyclesMap
          (scalarExtendedDegreeOneWindowBaseChangeIsoExplicit
            (R := R) (R' := R') (R'' := R'') (M := M)).hom =
      sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e :=
    scalarExtendedDegreeOneWindowBaseChangeIsoExplicit
      (R := R) (R' := R') (R'' := R'') (M := M)
  -- Proof comment: both cycle maps become the same degree-one scalar-extension morphism after
  -- forgetting the target cycles object back to degree one.
  apply W₂.cycles_ext
  calc
    (((W₁.mapCyclesIso extScalars).inv ≫ ShortComplex.cyclesMap e.hom) ≫ W₂.iCycles) =
        ((W₁.mapCyclesIso extScalars).inv ≫ (W₁.map extScalars).iCycles) ≫ e.hom.τ₂ := by
          simp [Category.assoc]
    _ = (extScalars).map W₁.iCycles ≫ e.hom.τ₂ := by
          simp [Category.assoc]
    _ = (extScalars).map W₁.iCycles ≫
          (scalarExtendedResolutionBaseChangeIso
            (R := R) (R' := R') (R'' := R'') (M := M) 1).hom := by
          rfl
    _ = sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫ W₂.iCycles := by
          symm
          exact sourceWindowTensorCyclesMap_iCycles
            (R := R) (R' := R') (R'' := R'') (M := M)

/-- Helper for Chap10 Lemma 10 99 12: the explicit short-complex base-change comparison satisfies
the same `homologyπ` factorization as the descended textbook cycle map. -/
private theorem scalarExtendedDegreeOneWindowBaseChangeComparison_homologyPi_fac :
    (extScalars).map
          (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)).homologyπ ≫
        scalarExtendedDegreeOneWindowBaseChangeComparison
          (R := R) (R' := R') (R'' := R'') (M := M) =
      sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫
        (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)).homologyπ := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let e :=
    scalarExtendedDegreeOneWindowBaseChangeIsoExplicit
      (R := R) (R' := R') (R'' := R'') (M := M)
  -- Proof comment: move the source homology quotient to the homology of the mapped short complex,
  -- apply homology naturality for the explicit base-change isomorphism, and rewrite the cycle map
  -- by the previous comparison lemma.
  calc
    (extScalars).map W₁.homologyπ ≫
        scalarExtendedDegreeOneWindowBaseChangeComparison
          (R := R) (R' := R') (R'' := R'') (M := M) =
      ((W₁.mapCyclesIso extScalars).inv ≫ (W₁.map extScalars).homologyπ) ≫
        ShortComplex.homologyMap e.hom := by
          simp [scalarExtendedDegreeOneWindowBaseChangeComparison, Category.assoc]
    _ =
        (W₁.mapCyclesIso extScalars).inv ≫
          ((W₁.map extScalars).homologyπ ≫ ShortComplex.homologyMap e.hom) := by
            simp [Category.assoc]
    _ =
        (W₁.mapCyclesIso extScalars).inv ≫
          (ShortComplex.cyclesMap e.hom ≫ W₂.homologyπ) := by
            rw [ShortComplex.homologyπ_naturality]
    _ =
        ((W₁.mapCyclesIso extScalars).inv ≫ ShortComplex.cyclesMap e.hom) ≫ W₂.homologyπ := by
            simp [Category.assoc]
    _ =
        sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M) ≫
          W₂.homologyπ := by
            rw [scalarExtendedDegreeOneWindowBaseChangeComparison_cyclesMap
              (R := R) (R' := R') (R'' := R'') (M := M)]

/-- Helper for Chap10 Lemma 10 99 12: the descended window comparison already agrees with the
canonical homology map induced by the explicit short-complex base-change isomorphism. -/
private theorem scalarExtendedDegreeOneWindowBaseChangeComparison_eq_torOneBaseChangeWindowComparison :
    scalarExtendedDegreeOneWindowBaseChangeComparison
        (R := R) (R' := R') (R'' := R'') (M := M) =
      torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M) := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let sourceCofork := CokernelCofork.ofπ W₁.homologyπ W₁.toCycles_comp_homologyπ
  let hColim : IsColimit (sourceCofork.map extScalars) := by
    -- Proof comment: source homology is presented by a cokernel, and scalar extension preserves
    -- that cokernel presentation.
    exact CokernelCofork.mapIsColimit (c := sourceCofork) W₁.homologyIsCokernel extScalars
  -- Proof comment: both candidate maps are morphisms out of the same mapped cokernel, so it
  -- suffices to compare their composites with the cokernel projection.
  apply Cofork.IsColimit.hom_ext hColim
  simpa [sourceCofork] using
    (scalarExtendedDegreeOneWindowBaseChangeComparison_homologyPi_fac
      (R := R) (R' := R') (R'' := R'') (M := M)).trans
      (torOneBaseChangeWindowComparison_homologyPi_fac
        (R := R) (R' := R') (R'' := R'') (M := M)).symm

/-- Helper for Chap10 Lemma 10 99 12: the chosen source-window comparison is surjective because it
comes from the surjective tensorized cycle map. -/
private theorem torOneBaseChangeWindowComparison_surjective :
    Function.Surjective
      (torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M)).hom := by
  let W₁ := scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)
  let W₂ := scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M)
  let k := sourceWindowTensorCyclesMap (R := R) (R' := R') (R'' := R'') (M := M)
  have hk : Function.Surjective k.hom :=
    sourceWindowTensorCyclesMap_surjective (R := R) (R' := R') (R'' := R'') (M := M)
  have hπ₂ : Function.Surjective W₂.homologyπ.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  intro y
  obtain ⟨z, hz⟩ := hπ₂ y
  obtain ⟨x, hx⟩ := hk z
  refine ⟨((extScalars).map W₁.homologyπ).hom x, ?_⟩
  -- Proof comment: project the lifted source cycle through the descended cokernel map and use
  -- the defining `homologyπ` factorization.
  calc
    (torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M)).hom
        (((extScalars).map W₁.homologyπ).hom x) =
      ((k ≫ W₂.homologyπ).hom x) := by
        change
          (((extScalars).map W₁.homologyπ ≫
              torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M)).hom x) =
            ((k ≫ W₂.homologyπ).hom x)
        exact DFunLike.congr_fun
          (ModuleCat.hom_ext_iff.mp
            (torOneBaseChangeWindowComparison_homologyPi_fac
              (R := R) (R' := R') (R'' := R'') (M := M)))
          x
    _ = y := by
      change W₂.homologyπ.hom (k.hom x) = y
      rw [hx, hz]

/-- The base-change comparison for Lemma 10.99.12, now intended to be defined by conjugating the
window-level homology map from the textbook proof. -/
private theorem exists_surjective_torOneBaseChangeComparison :
    ∃ comparison : (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R''),
      Function.Surjective
        (comparison.hom :
          ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) := by
  -- The explicit comparison is assembled from the chosen surjective source-window homology map and
  -- then conjugated through the endpoint identifications.
  refine
    ⟨torOneBaseChangeComparisonOfWindow
        (R := R) (R' := R') (R'' := R'') (M := M)
        (torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M)),
      ?_⟩
  exact
    torOneBaseChangeComparison_surjective_of_window
      (R := R) (R' := R') (R'' := R'') (M := M)
      (windowComparison :=
        torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M))
      (torOneBaseChangeWindowComparison_surjective
        (R := R) (R' := R') (R'' := R'') (M := M))

/-- The base-change comparison for Lemma 10.99.12, chosen from the explicit surjective
window-level construction. -/
noncomputable def torOneBaseChangeComparison :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  torOneBaseChangeComparisonOfWindow
    (R := R) (R' := R') (R'' := R'') (M := M)
    (torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Lemma 10.99.12: once `torOneBaseChangeComparison` is rebuilt from the explicit
window comparison, its surjectivity is exactly the source proof's statement on degree-one
homology. -/
private theorem tor_one_baseChangeComparison_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeComparison.hom :
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) := by
  -- The chosen comparison is the conjugate of the surjective window-level comparison.
  exact
    torOneBaseChangeComparison_surjective_of_window
      (R := R) (R' := R') (R'' := R'') (M := M)
      (windowComparison :=
        torOneBaseChangeWindowComparison (R := R) (R' := R') (R'' := R'') (M := M))
      (torOneBaseChangeWindowComparison_surjective
        (R := R) (R' := R') (R'' := R'') (M := M))

end

/-- Helper for Chap10 Lemma 10 99 12: the coefficient-ring map `R' → R''` viewed as an
`R`-linear morphism in `ModuleCat R`. -/
private noncomputable def torOneCoefficientBaseChangeHom :
    ModuleCat.of R R' ⟶ ModuleCat.of R R'' :=
  ModuleCat.ofHom (IsScalarTower.toAlgHom R R' R'').toLinearMap

/-- Helper for Chap10 Lemma 10 99 12: functoriality of `Tor₁^R(M,-)` in the coefficient
variable is `R'`-linear with respect to the scalar tower `R → R' → R''`. -/
private theorem torOneCoefficientBaseChange_hom_smul
    (t : R') (x : Tor₁[R](M, R')) :
    ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
        (torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R''))).hom) (t • x) =
      (algebraMap R' R'' t) •
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          (torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R''))).hom x) := by
  let F := ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))
  let g :
      Tor₁Obj[R](M, R') ⟶ Tor₁Obj[R](M, R'') :=
    F.map (torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R''))
  let μSource : ModuleCat.of R R' ⟶ ModuleCat.of R R' :=
    (ModuleCat.of R R').endRingEquiv.symm (Module.toModuleEnd R R' t)
  let μTarget : ModuleCat.of R R'' ⟶ ModuleCat.of R R'' :=
    (ModuleCat.of R R'').endRingEquiv.symm
      (Module.toModuleEnd R R'' (algebraMap R' R'' t))
  have hCoeff :
      μSource ≫ torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R'') =
        torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R'') ≫ μTarget := by
    ext y
    change algebraMap R' R'' ((Module.toModuleEnd R R' t) y) =
      (Module.toModuleEnd R R'' (algebraMap R' R'' t)) (algebraMap R' R'' y)
    simp [moduleToModuleEnd_apply, map_mul]
  have hTor :
      F.map μSource ≫ g = g ≫ F.map μTarget := by
    simpa [g] using congrArg F.map hCoeff
  have hPoint := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hTor) x
  simpa [g, μSource, μTarget, torOne_smul_eq_map_actionEnd] using hPoint

/-- Helper for Chap10 Lemma 10 99 12: the natural coefficient-variable map
`Tor₁^R(M, R') → Tor₁^R(M, R'')`, regarded as an `R'`-linear map into the restricted-scalar
target. -/
private noncomputable def torOneNaturalBaseChangeRestrictHom :
    Tor₁Obj[R](M, R') ⟶
      (ModuleCat.restrictScalars (algebraMap R' R'')).obj (Tor₁Obj[R](M, R'')) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (algebraMap R' R'')).obj (Tor₁Obj[R](M, R'')))
    { toFun := ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          (torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R''))).hom)
      map_add' := ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
          (torOneCoefficientBaseChangeHom (R := R) (R' := R') (R'' := R''))).hom.map_add)
      map_smul' := fun t x ↦
        torOneCoefficientBaseChange_hom_smul
          (R := R) (R' := R') (R'' := R'') (M := M) t x }

/-- Helper for Chap10 Lemma 10 99 12: the source-window comparison transposed back to the
restricted `R'`-linear world. -/
private noncomputable def scalarExtendedDegreeOneWindowBaseChangeRestrictHom :
    ShortComplex.homology
        (scalarExtendedDegreeOneWindow (R := R) (R' := R') (M := M)) ⟶
      (ModuleCat.restrictScalars (algebraMap R' R'')).obj
        (ShortComplex.homology
          (scalarExtendedDegreeOneWindow (R := R) (R' := R'') (M := M))) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')).homEquiv _ _)
    (scalarExtendedDegreeOneWindowBaseChangeComparison
      (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Chap10 Lemma 10 99 12: the named restricted coefficient-variable map is the
adjoint transpose of the public base-change comparison. -/
private noncomputable def torOneNaturalBaseChangeComparison :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')).homEquiv _ _).symm
    (torOneNaturalBaseChangeRestrictHom (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Chap10 Lemma 10 99 12: after transposing both maps to the restricted `R'`-linear
world, the coefficient-variable map matches the explicit source-window base-change comparison. -/
private theorem torOneNaturalBaseChangeRestrictHom_targetWindow_naturality :
    torOneNaturalBaseChangeRestrictHom (R := R) (R' := R') (R'' := R'') (M := M) ≫
        (ModuleCat.restrictScalars (algebraMap R' R'')).map
          (torOneBaseChangeTargetWindowIso (R := R) (R'' := R'') (M := M)).hom =
      (ringCoeffTorOneWindowIso (R := R) (M := M) (T := R')).hom ≫
        scalarExtendedDegreeOneWindowBaseChangeRestrictHom
          (R := R) (R' := R') (R'' := R'') (M := M) := by
  -- Route correction: prove the explicit restricted-scalars square first, then recover the
  -- public comparison by one adjunction transport step.
  ext x
  -- Proof comment: after expanding the named restricted comparison maps, both sides are the same
  -- underlying function on degree-one `Tor`.
  simp [torOneNaturalBaseChangeRestrictHom,
    scalarExtendedDegreeOneWindowBaseChangeRestrictHom, torOneBaseChangeTargetWindowIso,
    scalarExtendedDegreeOneWindowBaseChangeComparison, ringCoeffTorOneWindowIso,
    ringCoeffTorOneWindowLinearMap, Category.assoc]

/-- Helper for Chap10 Lemma 10 99 12: the functorial coefficient-variable comparison on public
`Tor₁` agrees with the canonical comparison descended from the source-window cycle map. -/
private theorem torOneNaturalBaseChangeComparison_targetWindow_naturality :
    torOneNaturalBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M) ≫
        (torOneBaseChangeTargetWindowIso (R := R) (R'' := R'') (M := M)).hom =
      (torOneBaseChangeSourceWindowIso (R := R) (R' := R') (R'' := R'') (M := M)).hom ≫
        scalarExtendedDegreeOneWindowBaseChangeComparison
          (R := R) (R' := R') (R'' := R'') (M := M) := by
  -- Route correction: the window-side comparison is now normalized to the explicit short-complex
  -- base-change homology map, so the only remaining work is the public-side naturality square.
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')
  -- Proof comment: transpose the target equality across the scalar-extension/restriction
  -- adjunction so that both sides live in the restricted `R'`-linear world.
  refine (adj.homEquiv _ _).injective ?_
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  -- Proof comment: after transposing, the goal is exactly the restricted-scalars square proved
  -- above, together with the source endpoint map rewritten via `mapIso`.
  simpa [adj, torOneNaturalBaseChangeComparison, torOneBaseChangeSourceWindowIso,
    torOneNaturalBaseChangeRestrictHom, scalarExtendedDegreeOneWindowBaseChangeRestrictHom] using
    torOneNaturalBaseChangeRestrictHom_targetWindow_naturality
      (R := R) (R' := R') (R'' := R'') (M := M)

/-- Helper for Chap10 Lemma 10 99 12: the functorial coefficient-variable comparison on public
`Tor₁` agrees with the canonical comparison descended from the source-window cycle map. -/
private theorem torOneNaturalBaseChangeComparison_eq_torOneBaseChangeComparison :
    torOneNaturalBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M) =
      torOneBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M) := by
  let eTarget := torOneBaseChangeTargetWindowIso (R := R) (R'' := R'') (M := M)
  let eSource := torOneBaseChangeSourceWindowIso (R := R) (R' := R') (R'' := R'') (M := M)
  -- Proof comment: compare both public maps after transporting to the common target window model,
  -- where the preceding window-side identification reduces the statement to the remaining
  -- functoriality square.
  apply (cancel_mono eTarget.hom).1
  calc
    torOneNaturalBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M) ≫ eTarget.hom =
        eSource.hom ≫
          scalarExtendedDegreeOneWindowBaseChangeComparison
            (R := R) (R' := R') (R'' := R'') (M := M) := by
            exact torOneNaturalBaseChangeComparison_targetWindow_naturality
              (R := R) (R' := R') (R'' := R'') (M := M)
    _ =
        eSource.hom ≫ torOneBaseChangeWindowComparison
          (R := R) (R' := R') (R'' := R'') (M := M) := by
            rw [scalarExtendedDegreeOneWindowBaseChangeComparison_eq_torOneBaseChangeWindowComparison
              (R := R) (R' := R') (R'' := R'') (M := M)]
    _ =
        torOneBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M) ≫ eTarget.hom := by
            simp [eSource, eTarget, torOneBaseChangeComparison, torOneBaseChangeComparisonOfWindow,
              Category.assoc]

/-- The source-facing tensor-product map for Lemma 10.99.12. Its source is the textbook tensor
product `Tor₁^R(M, R') ⊗[R'] R''`, and it is induced by coefficient-variable functoriality for
`Tor₁^R(M, -)` along `R' → R''`. -/
noncomputable def torOneBaseChangeMap :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R'] Tor₁[R](M, R'') :=
  (torOneNaturalBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M)).hom.comp
    (torOneTextbookTensorSource (R := R) (R' := R') (R'' := R'') (M := M))

/-- Helper for Chap10 Lemma 10 99 12: after identifying the public functorial comparison with the
canonical source-window comparison, the textbook tensor-source map is exactly their composite. -/
private theorem torOneBaseChangeMap_eq_chosenComparison_comp_tensorSource :
    (torOneBaseChangeMap (R := R) (R' := R') (R'' := R'') (M := M)) =
      (torOneBaseChangeComparison (R := R) (R' := R') (R'' := R'') (M := M)).hom.comp
        (torOneTextbookTensorSource (R := R) (R' := R') (R'' := R'') (M := M)) := by
  -- Proof comment: the public tensor-product map is defined using the functorial comparison, so
  -- the comparison identification immediately rewrites the composite.
  rw [torOneBaseChangeMap, torOneNaturalBaseChangeComparison_eq_torOneBaseChangeComparison]

-- Proof sketch: choose a free resolution of `M` over `R`, tensor the `2 → 1 → 0` window with
-- `R'`, and write `K'` for the cycles. Flatness of `M ⊗[R] R'` over `R'` keeps the lower exact
-- sequence exact after tensoring with `R''`, so `K' ⊗[R'] R'' → K''` is surjective. Passing to
-- the degree-one homology quotients and conjugating by the window identifications gives the
-- desired surjection on `Tor₁`.
/-- Chap10 Lemma 10 99 12. Textbook tensor-product form: if `M ⊗[R] R'` is flat over `R'`, then
the natural base-change map `Tor₁^R(M, R') ⊗[R'] R'' → Tor₁^R(M, R'')` is surjective. -/
@[stacks 00MM]
theorem torOne_baseChangeMap_surjective_of_flat_baseChange
    (hflat_baseChange : Module.Flat R' (M ⊗[R] R')) :
    Function.Surjective
      (torOneBaseChangeMap : TensorProduct R' (Tor₁[R](M, R')) R'' → Tor₁[R](M, R'')) := by
  let eTensor :
      TensorProduct R R' M ≃ₗ[R']
        TensorProduct R M R' := by
    simpa [scalar_extension_functor, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (scalarExtensionTensorLinearEquiv (R' := R) (R'' := R') (ModuleCat.of R M))
  letI : Module.Flat R' (TensorProduct R R' M) :=
    letI : Module.Flat R' (TensorProduct R M R') := hflat_baseChange
    Module.Flat.of_linearEquiv eTensor
  -- Proof comment: once the public map is rewritten as the canonical comparison after the
  -- textbook tensor-source identification, surjectivity is a composition of two known
  -- surjections.
  rw [torOneBaseChangeMap_eq_chosenComparison_comp_tensorSource
    (R := R) (R' := R') (R'' := R'') (M := M)]
  exact Function.Surjective.comp
    (tor_one_baseChangeComparison_surjective_of_flat_baseChange
      (R := R) (R' := R') (R'' := R'') (M := M))
    (torOneTextbookTensorSource_surjective (R := R) (R' := R') (R'' := R'') (M := M))

end
