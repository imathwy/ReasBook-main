import Mathlib
import stacks_project.Chap10.Lemma_10_75_5
import stacks_project.Chap10.Lemma_10_39_12
import stacks_project.Chap10.Lemma_10_82_7

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
    { toFun := fun s ↦ eT <| F.map (eS.symm (Module.toModuleEnd R S s))
      map_one' := by
        -- The scalar `1` acts through the identity endomorphism, and `Tor` preserves identities.
        have hone : eS.symm (Module.toModuleEnd R S (1 : S)) = 1 := by
          simpa using congrArg eS.symm (RingHom.map_one (Module.toModuleEnd R S))
        have hmapone :
            F.map (𝟙 (ModuleCat.of R S)) = 𝟙 (F.obj (ModuleCat.of R S)) := by
          simpa using ((CategoryTheory.Functor.mapEnd (f := F) (X := ModuleCat.of R S)).map_one)
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
          simpa [fx, fy] using
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

local notation "Tor₁Obj[" R "](" M ", " S ")" =>
  (ModuleCat.of S (Tor₁[R](M, S)))
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R' R'')
local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R' R'')

variable [Module.Flat R' (TensorProduct R R' M)]

private noncomputable instance torOneBaseChangeTargetModule :
    Module R' (Tor₁[R](M, R'')) :=
  Module.compHom (Tor₁[R](M, R'')) (algebraMap R' R'')

private noncomputable instance torOneBaseChangeSourceModule :
    Module R' ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  Module.compHom _ (algebraMap R' R'')

/-- Helper for Lemma 10.99.12: a projective object of `ModuleCat` yields the usual module-theoretic
projectivity on its underlying module. -/
private lemma module_projective_of_categorical_projective
    {A : Type u} [CommRing A] (P : ModuleCat A) (hP : Projective P) :
    Module.Projective A P := by
  -- TODO: restore the `ModuleCat` projective-to-module-projective bridge with the right
  -- smallness universe so the scalar-extended resolution terms inherit module projectivity.
  sorry

/-- Helper for Lemma 10.99.12: the scalar-extension functor along `R → R'`. -/
private noncomputable abbrev scalar_extension_functor : ModuleCat R ⥤ ModuleCat R' :=
  ModuleCat.extendScalars (algebraMap R R')

/-- Helper for Lemma 10.99.12: scalar extension preserves projective objects because restriction of
scalars preserves epimorphisms. -/
private noncomputable instance scalar_extension_functor_preservesProjectiveObjects :
    (scalar_extension_functor (R := R) (R' := R')).PreservesProjectiveObjects :=
  by
    -- TODO: restore the universe-aligned adjunction proof for scalar extension preserving projectives.
    sorry

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

/-- Helper for Lemma 10.99.12: after extending scalars on the fixed projective resolution of `M`,
the lower window `F₁' ⟶ F₀' ⟶ M ⊗[R] R'` is still exact and surjective at the augmentation. -/
private theorem scalar_extended_augmentation_exact :
    (ShortComplex.mk
        (scalar_extended_d_one (R := R) (R' := R') (M := M))
        (scalar_extended_pi_zero (R := R) (R' := R') (M := M))
        (scalar_extended_d_one_comp_pi_zero (R := R) (R' := R') (M := M))).Exact ∧
      Epi (scalar_extended_pi_zero (R := R) (R' := R') (M := M)) := by
  -- TODO: rebuild this scalar-extended cokernel argument with the current `CokernelCofork` API.
  sorry

/-- Helper for Lemma 10.99.12: in a short exact sequence, flatness of the middle and right terms
forces flatness of the kernel. This is the local copy needed for the `B'` step of the source
proof, avoiding a new chapter import. -/
private theorem shortExact_flat_X₁
    {A : Type u} [CommRing A] {S : ShortComplex (ModuleCat A)}
    (hS : S.ShortExact) [Module.Flat A S.X₂] [Module.Flat A S.X₃] :
    Module.Flat A S.X₁ := by
  -- TODO: prove this directly from the flatness criterion without the now-missing
  -- `ShortComplex.UniversallyExact` helper API.
  sorry

/-- Helper for Lemma 10.99.12: the lower kernel `B' = ker(F₀' ⟶ M ⊗[R] R')` is flat over `R'`.
This is the exact place where the source hypothesis on `M ⊗[R] R'` enters the proof. -/
private theorem source_window_lower_kernel_flat :
    Module.Flat R' (LinearMap.ker (scalar_extended_pi_zero (R := R) (R' := R') (M := M)).hom) := by
  -- TODO: after the scalar-extended lower row is reconstructed as a short exact sequence again,
  -- this is the flatness-of-kernel step from the textbook proof.
  sorry

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
  -- TODO: after exactness of the lower row is repaired, this is the image-equals-kernel argument.
  sorry

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

/-- Helper for Lemma 10.99.12: after flipping the public `Tor₁^R(M, A)` owner, the fixed
projective resolution of `M` computes the target via the left-derived `tensorRight A`
presentation. -/
private noncomputable def tor_flip_target_to_tensorRight_leftDerived_iso
    (A : ModuleCat R) :
    (((Functor.flip (Tor' (ModuleCat R) 1)).obj (ModuleCat.of R M)).obj A) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) := sorry

/-- Helper for Lemma 10.99.12: `Tor₁^R(M, A)` is computed by the `2 → 1 → 0` window obtained by
tensoring the fixed projective resolution of `M` with `A`. -/
private noncomputable def tor_one_flip_window_iso (A : ModuleCat R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj A) ≅
      ShortComplex.homology
        (tensorRight_degree_one_window (R := R) A (ModuleCat.of R M)) :=
  -- Route correction: first flip the public owner to the right-variable presentation, then
  -- resolve `M`, and finally reduce the full degree-one homology computation to the window.
  (((tor_flip_iso (ModuleCat R) 1).app (ModuleCat.of R M)).app A) ≪≫
    tor_flip_target_to_tensorRight_leftDerived_iso (R := R) (M := M) A ≪≫
      tensorRight_degree_one_window_homology_iso (R := R) A (ModuleCat.of R M)

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

/-- The source-facing tensor-product identification used in Lemma 10.99.12. -/
noncomputable def torOneTextbookTensorSource :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
    torOneTextbookTensorSourceEquiv
  e.toLinearMap

/-- The base-change comparison for Lemma 10.99.12, now intended to be defined by conjugating the
window-level homology map from the textbook proof. -/
noncomputable def torOneBaseChangeComparison :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  -- TODO: the next source-faithful step is to tensor the now-closed upper short exact sequence
  -- `0 → K' → F₁' → B' → 0` from `source_window_upper_shortExact`, use the flatness of `B'` from
  -- `source_window_lower_kernel_flat` to obtain a surjection on tensorized cycles, descend that
  -- surjection to degree-one homology, and only then transport it through `tor_one_flip_window_iso`.
  sorry

/-- Helper for Lemma 10.99.12: once `torOneBaseChangeComparison` is rebuilt from the explicit
window comparison, its surjectivity is exactly the source proof's statement on degree-one
homology. -/
private theorem tor_one_baseChangeComparison_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeComparison.hom :
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) := by
  -- Route correction: the remaining work is no longer an owner-level `map_smul'` problem.
  -- TODO: define `torOneBaseChangeComparison` by descending the tensorized-cycles surjection from
  -- `source_window_upper_shortExact` and `source_window_lower_kernel_flat` to the quotient
  -- description of `ShortComplex.homology`, then conjugate the resulting homology map through
  -- `tor_one_flip_window_iso` on the source and target sides.
  sorry

/-- The source-facing tensor-product map for Lemma 10.99.12. Its source is the textbook tensor
view, while its middle comparison is the categorical base-change map. -/
noncomputable def torOneBaseChangeMap :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R'] Tor₁[R](M, R'') :=
  let comparisonLinear :
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) →ₗ[R'] Tor₁[R](M, R'') :=
    { toFun := torOneBaseChangeComparison.hom
      map_add' := torOneBaseChangeComparison.hom.map_add
      map_smul' := fun c x ↦ by
        change torOneBaseChangeComparison.hom ((algebraMap R' R'' c) • x) =
          (algebraMap R' R'' c) • torOneBaseChangeComparison.hom x
        simpa using torOneBaseChangeComparison.hom.map_smul (algebraMap R' R'' c) x }
  comparisonLinear.comp torOneTextbookTensorSource

-- Proof sketch: choose a free resolution of `M` over `R`, tensor the `2 → 1 → 0` window with
-- `R'`, and write `K'` for the cycles. Flatness of `M ⊗[R] R'` over `R'` keeps the lower exact
-- sequence exact after tensoring with `R''`, so `K' ⊗[R'] R'' → K''` is surjective. Passing to
-- the degree-one homology quotients and conjugating by the window identifications gives the
-- desired surjection on `Tor₁`.
/-- Lemma 10.99.12, textbook tensor-product form: if `M ⊗[R] R'` is flat over `R'`, then the
natural base-change map `Tor₁^R(M, R') ⊗[R'] R'' → Tor₁^R(M, R'')` is surjective. -/
theorem torOne_baseChangeMap_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeMap : TensorProduct R' (Tor₁[R](M, R')) R'' → Tor₁[R](M, R'')) := by
  -- The only remaining input is surjectivity of the window-level comparison packaged above.
  have hcomparison :
      Function.Surjective
        (torOneBaseChangeComparison.hom :
          ↑((extScalars).obj (Tor₁Obj[R](M, R'))) → Tor₁[R](M, R'')) :=
    tor_one_baseChangeComparison_surjective_of_flat_baseChange
  have hsource :
      Function.Surjective
        (torOneTextbookTensorSource :
          TensorProduct R' (Tor₁[R](M, R')) R'' →
            ↑((extScalars).obj (Tor₁Obj[R](M, R')))) :=
    torOneTextbookTensorSource_surjective
  intro y
  rcases hcomparison y with ⟨x, hx⟩
  rcases hsource x with
      ⟨z, rfl⟩
  exact ⟨z, hx⟩

end
