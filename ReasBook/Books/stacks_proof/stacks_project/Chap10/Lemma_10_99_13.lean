import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_5
import StacksProject_2024.Chap10.Lemma_10_99_13.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ModuleCat MonoidalCategory
open scoped ModuleCat

noncomputable section

universe u

section

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: change-of-rings / base-change comparison on `Tor₁` for quotient modules;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `CategoryTheory.tor_flip_iso`,
  `torBaseChangeHom`,
  `torOneBaseChangeMap`;
- best owner abstraction: the canonical bifunctor owner `CategoryTheory.Tor`, with
  `tor_flip_iso`, `torBaseChangeHom`, and `torOneBaseChangeMap` providing the existing
  `bridge/view` change-of-rings machinery in the chapter;
- primitive data: the ring map `R → S`, the ideal `I`, and the `R`-module `M`;
- derived API: the source-facing existence and surjectivity statement for the natural comparison
  morphism `Tor₁^R(S / IS, M) → Tor₁^S(S / IS, S ⊗[R] M)`.

Layering:
- `source-facing`: the surjective comparison morphism of Lemma 10.99.13;
- `core/canonical`: the owner bifunctor `Tor'`;
- `bridge/view`: `tor_flip_iso`, `torBaseChangeHom`, and any quotient-tensor identifications used
  to build the map belong in the proof, not as a parallel public owner.
-/

private abbrev extendedIdeal (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

private abbrev quotientModule (I : Ideal R) : ModuleCat S :=
  ModuleCat.of S (S ⧸ extendedIdeal I)

private abbrev baseChangedModule : ModuleCat S :=
  (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)

private abbrev torOneQuotientSource (I : Ideal R) : ModuleCat R :=
  (((Tor (ModuleCat R) 1).obj
      (ModuleCat.of R (S ⧸ extendedIdeal I))).obj
    (ModuleCat.of R M))

private abbrev torOneQuotientTarget (I : Ideal R) : ModuleCat S :=
  (((Tor (ModuleCat S) 1).obj (quotientModule I)).obj
    (@baseChangedModule R S M _ _ _ _ _))

private abbrev torOneQuotientTargetRestrict (I : Ideal R) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((@torOneQuotientTarget R S M _ _ _ _ _ I) : ModuleCat S)

/-- Helper for Lemma 10.99.13: the `2 → 1 → 0` window of the coefficient-tensored complex
attached to an arbitrary chosen projective resolution. -/
private noncomputable abbrev tensorRight_degree_one_window_of_resolution
    (A : ModuleCat R) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    ShortComplex (ModuleCat R) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 2 1 0).obj
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      P.complex)

/-- Helper for Lemma 10.99.13: degree-one homology of the coefficient-tensored chosen resolution
is canonically the homology of its `2 → 1 → 0` window. -/
private noncomputable def tensorRight_degree_one_window_homology_iso_of_resolution
    (A : ModuleCat R) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
      (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≅
      ShortComplex.homology
        (tensorRight_degree_one_window_of_resolution (R := R) A P) :=
  -- The general `homologyFunctorIso'` API depends only on the chosen down-complex itself.
  (HomologicalComplex.homologyFunctorIso' (C := ModuleCat R) (c := ComplexShape.down ℕ)
      (i := 2) (j := 1) (k := 0) (by simp) (by simp)).app
    (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)

/-- Helper for Lemma 10.99.13: the `2 → 1 → 0` window of the quotient-tensored projective
resolution of `X` over `R`. This isolates the degree bookkeeping used in the source proof. -/
private noncomputable abbrev tensorRight_degree_one_window
    (A X : ModuleCat R) : ShortComplex (ModuleCat R) :=
  tensorRight_degree_one_window_of_resolution (R := R) A
    (CategoryTheory.projectiveResolution X)

/-- Helper for Lemma 10.99.13: degree-one homology of the quotient-tensored projective resolution
is canonically the homology of its `2 → 1 → 0` short-complex window. -/
private noncomputable def tensorRight_degree_one_window_homology_iso
    (A X : ModuleCat R) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
      (((tensorRight A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryTheory.ProjectiveResolution.complex
          (CategoryTheory.projectiveResolution X))) ≅
      ShortComplex.homology (tensorRight_degree_one_window (R := R) A X) :=
  -- This is the fixed-resolution specialization of the general window-homology comparison above.
  tensorRight_degree_one_window_homology_iso_of_resolution (R := R) A
    (CategoryTheory.projectiveResolution X)

/-- Helper for Lemma 10.99.13: the source `Tor₁` owner is computed by the `2 → 1 → 0` window of
the quotient-tensored projective resolution of `M`. This closes the source side of the textbook
comparison and leaves only the corrected target presentation to package. -/
private noncomputable def source_owner_to_source_window_h1_iso (I : Ideal R) :
    ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ≅
      ShortComplex.homology
        (tensorRight_degree_one_window (R := R)
          (ModuleCat.of R (S ⧸ extendedIdeal I)) (ModuleCat.of R M)) := by
  let coeffR : ModuleCat R := ModuleCat.of R (S ⧸ extendedIdeal I)
  let eFlip :
      ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ≅
        (((Functor.flip (Tor' (ModuleCat R) 1)).obj coeffR).obj (ModuleCat.of R M)) :=
    (((tor_flip_iso (ModuleCat R) 1).app coeffR).app (ModuleCat.of R M))
  -- The source proof resolves `M` and tensors termwise with `S / IS`; after flipping `Tor`, the
  -- chosen projective resolution computes the owner via `tensorRight coeffR`.
  let eDerived :
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj coeffR).obj (ModuleCat.of R M)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
          (((tensorRight coeffR).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.ProjectiveResolution.complex
              (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) :=
    (CategoryTheory.projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj
      (tensorRight coeffR) 1
  -- Convert the full down-complex homology computation to the explicit `2 → 1 → 0` window.
  exact
    eFlip ≪≫
      eDerived ≪≫
        tensorRight_degree_one_window_homology_iso (R := R) coeffR (ModuleCat.of R M)

/-- Helper for Lemma 10.99.13: the fixed projective resolution of `M` used on the source side of
the textbook proof. -/
private noncomputable abbrev scalar_extended_source_resolution :
    CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
  CategoryTheory.projectiveResolution (ModuleCat.of R M)

/-- Helper for Lemma 10.99.13: the scalar-extension functor along `R → S`. -/
private noncomputable abbrev scalar_extension_functor : ModuleCat R ⥤ ModuleCat S :=
  ModuleCat.extendScalars (algebraMap R S)

/-- Helper for Lemma 10.99.13: the degree-`n` term obtained by scalar-extending the fixed source
resolution of `M`. -/
private noncomputable abbrev scalar_extended_resolution_X (n : ℕ) : ModuleCat S :=
  (scalar_extension_functor (R := R) (S := S)).obj
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.X n)

/-- Helper for Lemma 10.99.13: the scalar-extended differential `X₁' ⟶ X₀'`. -/
private noncomputable abbrev scalar_extended_d_one :
    scalar_extended_resolution_X (R := R) (S := S) (M := M) 1 ⟶
      scalar_extended_resolution_X (R := R) (S := S) (M := M) 0 :=
  (scalar_extension_functor (R := R) (S := S)).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0)

/-- Helper for Lemma 10.99.13: the scalar-extended differential `X₂' ⟶ X₁'`. -/
private noncomputable abbrev scalar_extended_d_two :
    scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⟶
      scalar_extended_resolution_X (R := R) (S := S) (M := M) 1 :=
  (scalar_extension_functor (R := R) (S := S)).map
    ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1)

/-- Helper for Lemma 10.99.13: the scalar-extended augmentation `X₀' ⟶ M'`. -/
private noncomputable abbrev scalar_extended_pi_zero :
    scalar_extended_resolution_X (R := R) (S := S) (M := M) 0 ⟶
      @baseChangedModule R S M _ _ _ _ _ :=
  (scalar_extension_functor (R := R) (S := S)).map
    ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0)

/-- Helper for Lemma 10.99.13: the scalar-extended lower differential still composes to zero with
the scalar-extended augmentation. -/
private theorem scalar_extended_d_one_comp_pi_zero :
    scalar_extended_d_one (R := R) (S := S) (M := M) ≫
        scalar_extended_pi_zero (R := R) (S := S) (M := M) =
      0 := by
  -- Map the original augmentation relation through scalar extension.
  have hzero :
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0) ≫
          ((scalar_extended_source_resolution (R := R) (M := M)).π.f 0) =
        0 :=
    CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero
      (P := scalar_extended_source_resolution (R := R) (M := M))
  have hmap_zero :
      (scalar_extension_functor (R := R) (S := S)).map
          (0 :
            ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1) ⟶
              ModuleCat.of R M) =
        0 := by
    simpa using
      (Functor.map_zero (F := scalar_extension_functor (R := R) (S := S))
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)
        (ModuleCat.of R M))
  rw [scalar_extended_d_one, scalar_extended_pi_zero, ← Functor.map_comp]
  exact
    (congrArg ((scalar_extension_functor (R := R) (S := S)).map) hzero).trans
      hmap_zero

/-- Helper for Lemma 10.99.13: the scalar-extended differential still squares to zero at the
`2 → 1 → 0` stage. -/
private theorem scalar_extended_d_two_comp_d_one :
    scalar_extended_d_two (R := R) (S := S) (M := M) ≫
        scalar_extended_d_one (R := R) (S := S) (M := M) =
      0 := by
  -- Map the original `d² = 0` relation through scalar extension.
  rw [scalar_extended_d_two, scalar_extended_d_one, ← Functor.map_comp]
  rw [HomologicalComplex.d_comp_d, Functor.map_zero]

/-- Helper for Lemma 10.99.13: the projective resolution of `ker d₁'` supplying the extra
degree-two summand in the corrected target window. -/
private noncomputable abbrev kernel_cover_resolution :
    CategoryTheory.ProjectiveResolution
      (kernel (scalar_extended_d_one (R := R) (S := S) (M := M))) :=
  CategoryTheory.projectiveResolution
    (kernel (scalar_extended_d_one (R := R) (S := S) (M := M)))

/-- Helper for Lemma 10.99.13: the degree-zero projective cover of `ker d₁'`. -/
private noncomputable abbrev kernel_cover_object : ModuleCat S :=
  (kernel_cover_resolution (R := R) (S := S) (M := M)).complex.X 0

/-- Helper for Lemma 10.99.13: the augmentation from the chosen projective cover onto `ker d₁'`. -/
private noncomputable abbrev kernel_cover_map :
    kernel_cover_object (R := R) (S := S) (M := M) ⟶
      kernel (scalar_extended_d_one (R := R) (S := S) (M := M)) :=
  (kernel_cover_resolution (R := R) (S := S) (M := M)).π.f 0

/-- Helper for Lemma 10.99.13: the extra degree-two summand map into `X₁'`, obtained by composing
the projective cover with the kernel inclusion of `d₁'`. -/
private noncomputable abbrev corrected_window_extra_map :
    kernel_cover_object (R := R) (S := S) (M := M) ⟶
      scalar_extended_resolution_X (R := R) (S := S) (M := M) 1 :=
  kernel_cover_map (R := R) (S := S) (M := M) ≫
    kernel.ι (scalar_extended_d_one (R := R) (S := S) (M := M))

/-- Helper for Lemma 10.99.13: the corrected degree-two differential lands in the kernel of
`d₁'`. -/
private theorem corrected_window_zero :
    biprod.desc (scalar_extended_d_two (R := R) (S := S) (M := M))
        (corrected_window_extra_map (R := R) (S := S) (M := M)) ≫
      scalar_extended_d_one (R := R) (S := S) (M := M) =
    0 := by
  -- Each summand separately lands in the kernel of `d₁'`.
  apply biprod.hom_ext'
  · simp [scalar_extended_d_two_comp_d_one]
  · simp [corrected_window_extra_map]

/-- Helper for Lemma 10.99.13: after extending scalars on the chosen projective resolution of
`M`, the lower window `X₁' ⟶ X₀' ⟶ M'` stays exact because `extendScalars` preserves cokernels. -/
private theorem scalar_extended_augmentation_exact :
    (ShortComplex.mk
        (scalar_extended_d_one (R := R) (S := S) (M := M))
        (scalar_extended_pi_zero (R := R) (S := S) (M := M))
        (scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M))).Exact ∧
      Epi (scalar_extended_pi_zero (R := R) (S := S) (M := M)) := by
  let P := scalar_extended_source_resolution (R := R) (M := M)
  let F := scalar_extension_functor (R := R) (S := S)
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (scalar_extended_pi_zero (R := R) (S := S) (M := M))
          (scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M))) := by
    -- Map the original cokernel presentation through `extendScalars`; as a left adjoint it
    -- preserves the cokernel witnessing exactness at degree `0`.
    simpa [scalar_extended_pi_zero, scalar_extended_d_one_comp_pi_zero, scalar_extended_d_one,
      scalar_extension_functor, scalar_extended_source_resolution] using
      CokernelCofork.mapIsColimit (c := P.cokernelCofork) P.isColimitCokernelCofork F
  refine ⟨?_, ?_⟩
  · -- Exactness of the scalar-extended lower window is exactly the mapped cokernel statement.
    exact ShortComplex.exact_of_g_is_cokernel _ hColim
  · -- The same mapped cokernel exhibits the scalar-extended augmentation as an epimorphism.
    exact epi_of_isColimit_cofork hColim

/-- Helper for Lemma 10.99.13: adjoining a projective cover of `ker d₁'` produces the corrected
source-faithful `2 → 1 → 0` target window. The extra summand alone surjects onto the kernel, and
the original degree-two term is kept only to match the textbook comparison map. -/
private theorem kernel_cover_corrected_window_exact :
    (ShortComplex.mk
        (biprod.desc
          (scalar_extended_d_two (R := R) (S := S) (M := M))
          (corrected_window_extra_map (R := R) (S := S) (M := M)))
        (scalar_extended_d_one (R := R) (S := S) (M := M))
        (corrected_window_zero (R := R) (S := S) (M := M))).Exact ∧
  Projective (kernel_cover_object (R := R) (S := S) (M := M)) := by
  let q := kernel_cover_map (R := R) (S := S) (M := M)
  let e₂ := corrected_window_extra_map (R := R) (S := S) (M := M)
  have hExactKernelCover :
      (ShortComplex.mk e₂
          (scalar_extended_d_one (R := R) (S := S) (M := M))
          (by simp [e₂, corrected_window_extra_map])).Exact := by
    letI : Epi q := by
      change Epi ((kernel_cover_resolution (R := R) (S := S) (M := M)).π.f 0)
      infer_instance
    let α :
        ShortComplex.mk e₂
            (scalar_extended_d_one (R := R) (S := S) (M := M))
            (by simp [e₂, corrected_window_extra_map]) ⟶
          ShortComplex.mk
            (kernel.ι (scalar_extended_d_one (R := R) (S := S) (M := M)))
            (scalar_extended_d_one (R := R) (S := S) (M := M))
            (kernel.condition _) :=
      { τ₁ := q
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          -- The projective cover lands in the kernel by construction.
          simp [q, e₂, corrected_window_extra_map, kernel_cover_map]
        comm₂₃ := by
          simp }
    -- Compare with the actual kernel short complex; the projective cover is epi onto that kernel.
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hExactCorrected :
      (ShortComplex.mk
          (biprod.desc
            (scalar_extended_d_two (R := R) (S := S) (M := M))
          (corrected_window_extra_map (R := R) (S := S) (M := M)))
          (scalar_extended_d_one (R := R) (S := S) (M := M))
          (corrected_window_zero (R := R) (S := S) (M := M))).Exact := by
    -- The corrected differential is exact because the added kernel-cover summand already hits
    -- every cycle of `d₁'`; the original scalar-extended degree-two term is retained only so that
    -- the comparison from the uncorrected window is the textbook inclusion.
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    rcases (ShortComplex.moduleCat_exact_iff
        (ShortComplex.mk e₂
          (scalar_extended_d_one (R := R) (S := S) (M := M))
          (by simp [e₂, corrected_window_extra_map]))).1 hExactKernelCover x hx with
      ⟨y, hy⟩
    refine ⟨(biprod.inr : kernel_cover_object (R := R) (S := S) (M := M) ⟶
        scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⊞
          kernel_cover_object (R := R) (S := S) (M := M)) y, ?_⟩
    have hy' :
        (biprod.desc
            (scalar_extended_d_two (R := R) (S := S) (M := M))
            e₂)
          ((biprod.inr : kernel_cover_object (R := R) (S := S) (M := M) ⟶
              scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⊞
                kernel_cover_object (R := R) (S := S) (M := M)) y) =
          x := by
      change (((biprod.inr :
            kernel_cover_object (R := R) (S := S) (M := M) ⟶
              scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⊞
                kernel_cover_object (R := R) (S := S) (M := M)) ≫
          biprod.desc
            (scalar_extended_d_two (R := R) (S := S) (M := M))
            e₂) y) = x
      simpa using hy
    exact hy'
  refine ⟨hExactCorrected, ?_⟩
  -- The added cover term comes from a projective resolution of the kernel.
  simpa [kernel_cover_object, kernel_cover_resolution] using
    (kernel_cover_resolution (R := R) (S := S) (M := M)).projective 0

/-- Helper for Lemma 10.99.13: every `Projective.d` differential composes to zero with the map it
was built from. This is the uniform tail relation used to continue the corrected target
resolution after the textbook `2 → 1 → 0` window. -/
private theorem projective_d_comp_zero
    {X Y : ModuleCat S} (f : X ⟶ Y) :
    Projective.d f ≫ f = 0 := by
  -- `Projective.d f` factors through `kernel f`, so its composite with `f` is the kernel relation.
  simp [Projective.d]

/-- Helper for Lemma 10.99.13: the corrected degree-two object on the target side is the original
scalar-extended degree-two term together with the extra projective summand covering cycles of
`d₁'`. -/
private noncomputable abbrev corrected_target_degree_two_object : ModuleCat S :=
  scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⊞
    kernel_cover_object (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.99.13: the corrected target differential in degree `2 → 1` is the
textbook map obtained by adjoining the extra summand into the kernel of `d₁'`. -/
private noncomputable abbrev corrected_target_degree_two_map :
    corrected_target_degree_two_object (R := R) (S := S) (M := M) ⟶
      scalar_extended_resolution_X (R := R) (S := S) (M := M) 1 :=
  biprod.desc
    (scalar_extended_d_two (R := R) (S := S) (M := M))
    (corrected_window_extra_map (R := R) (S := S) (M := M))

/-- Helper for Lemma 10.99.13: the corrected target chain complex keeps the scalar-extended
`0`-th and `1`-st terms, uses the textbook corrected degree-two object, and then continues by the
canonical `Projective.d` tail. -/
private noncomputable abbrev corrected_target_resolution_complex :
    ChainComplex (ModuleCat S) ℕ :=
  ChainComplex.mk
    (scalar_extended_resolution_X (R := R) (S := S) (M := M) 0)
    (scalar_extended_resolution_X (R := R) (S := S) (M := M) 1)
    (corrected_target_degree_two_object (R := R) (S := S) (M := M))
    (scalar_extended_d_one (R := R) (S := S) (M := M))
    (corrected_target_degree_two_map (R := R) (S := S) (M := M))
    (corrected_window_zero (R := R) (S := S) (M := M))
    (fun T ↦ ⟨Projective.syzygies T.f, Projective.d T.f, projective_d_comp_zero T.f⟩)

/-- Helper for Lemma 10.99.13: the lower exactness of the corrected target resolution is exactly
the scalar-extended augmentation exactness established earlier. -/
private theorem corrected_target_resolution_complex_exact_zero :
    (ShortComplex.mk
        ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).d 1 0)
        (scalar_extended_pi_zero (R := R) (S := S) (M := M))
        (scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M))).Exact ∧
      Epi (scalar_extended_pi_zero (R := R) (S := S) (M := M)) := by
  -- The corrected resolution leaves the `1 → 0 → M'` window untouched.
  simpa [corrected_target_resolution_complex] using
    scalar_extended_augmentation_exact (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.99.13: exactness at the first nontrivial homology spot of the corrected
target resolution is precisely the corrected-window exactness proved from the extra degree-two
summand. -/
private theorem corrected_target_resolution_complex_exact_one :
    (corrected_target_resolution_complex (R := R) (S := S) (M := M)).ExactAt 1 := by
  -- The `2 → 1 → 0` window is the explicit corrected short complex.
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  simpa [corrected_target_resolution_complex, corrected_target_degree_two_map] using
    (kernel_cover_corrected_window_exact (R := R) (S := S) (M := M)).1

/-- Helper for Lemma 10.99.13: the first tail exactness statement, at degree `2`, already has the
standard `Projective.d` form once the corrected `2 → 1` map is fixed. -/
private theorem corrected_target_resolution_complex_exact_two :
    (corrected_target_resolution_complex (R := R) (S := S) (M := M)).ExactAt 2 := by
  -- The first tail window is exactly the corrected degree-two map followed by its canonical
  -- projective syzygy differential.
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)]
  dsimp [corrected_target_resolution_complex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', ChainComplex.mk]
  exact
    CategoryTheory.exact_d_f
      (corrected_target_degree_two_map (R := R) (S := S) (M := M))

/-- Helper for Lemma 10.99.13: every positive-degree tail window of the corrected target
resolution is the canonical `Projective.d` short complex, up to the bookkeeping isomorphism on the
left term coming from `ChainComplex.mk`. -/
private noncomputable def corrected_target_tail_shortComplex_iso (n : ℕ) :
    ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).sc'
        (n + 4) (n + 3) (n + 2)) ≅
      ShortComplex.mk
        (Projective.d
          ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).d (n + 3) (n + 2)))
        ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).d (n + 3) (n + 2))
        (projective_d_comp_zero
          ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).d (n + 3) (n + 2))) :=
  ShortComplex.isoMk
    (ChainComplex.mkXIso
      (X₀ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 0)
      (X₁ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 1)
      (X₂ := corrected_target_degree_two_object (R := R) (S := S) (M := M))
      (d₀ := scalar_extended_d_one (R := R) (S := S) (M := M))
      (d₁ := corrected_target_degree_two_map (R := R) (S := S) (M := M))
      (s := corrected_window_zero (R := R) (S := S) (M := M))
      (succ := fun T ↦ ⟨Projective.syzygies T.f, Projective.d T.f, projective_d_comp_zero T.f⟩)
      (n + 1))
    (Iso.refl _)
    (Iso.refl _)
    (by
      -- `ChainComplex.mk_d` identifies the left differential of the tail window with the
      -- canonical `Projective.d` differential after transporting the left term by `mkXIso`.
      have hmk :=
        (ChainComplex.mk_d
          (X₀ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 0)
          (X₁ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 1)
          (X₂ := corrected_target_degree_two_object (R := R) (S := S) (M := M))
          (d₀ := scalar_extended_d_one (R := R) (S := S) (M := M))
          (d₁ := corrected_target_degree_two_map (R := R) (S := S) (M := M))
          (s := corrected_window_zero (R := R) (S := S) (M := M))
          (succ := fun T ↦ ⟨Projective.syzygies T.f, Projective.d T.f, projective_d_comp_zero T.f⟩)
          (n + 1))
      simpa [corrected_target_resolution_complex] using hmk.symm)
    (by
      -- The middle-to-right differential is unchanged; only the left term is transported.
      simp)

/-- Helper for Lemma 10.99.13: after the corrected degree-two term, the tail of the chosen target
resolution is generated by successive `Projective.d`, so every later exactness statement is the
canonical `exact_d_f`. -/
private theorem corrected_target_resolution_complex_exact_succ (n : ℕ) :
    (corrected_target_resolution_complex (R := R) (S := S) (M := M)).ExactAt (n + 2) := by
  cases n with
  | zero =>
      -- The first positive spot is the already established degree-`2` exactness statement.
      simpa using corrected_target_resolution_complex_exact_two (R := R) (S := S) (M := M)
  | succ n =>
      -- After freezing the positive tail window by an explicit isomorphism, exactness is the
      -- canonical `Projective.d` exactness of the chosen recursive tail.
      rw [HomologicalComplex.exactAt_iff' _ (n + 4) (n + 3) (n + 2) (by simp) (by simp)]
      exact ShortComplex.exact_of_iso
        (corrected_target_tail_shortComplex_iso (R := R) (S := S) (M := M) n).symm
        (CategoryTheory.exact_d_f
          ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).d (n + 3) (n + 2)))

/-- Helper for Lemma 10.99.13: every term of the corrected target chain complex is projective. -/
private theorem corrected_target_resolution_complex_projective (n : ℕ) :
    Projective ((corrected_target_resolution_complex (R := R) (S := S) (M := M)).X n) := by
  -- The first three terms are visibly projective, and the tail is built from `Projective.syzygies`.
  obtain rfl | rfl | rfl | n := n
  · simpa [corrected_target_resolution_complex, scalar_extended_resolution_X,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))).projective_obj
        ((scalar_extended_source_resolution (R := R) (M := M)).projective 0)
  · simpa [corrected_target_resolution_complex, scalar_extended_resolution_X,
      scalar_extension_functor, scalar_extended_source_resolution] using
      (Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))).projective_obj
        ((scalar_extended_source_resolution (R := R) (M := M)).projective 1)
  · have hleft :
        Projective
          (scalar_extended_resolution_X (R := R) (S := S) (M := M) 2) := by
        simpa [scalar_extended_resolution_X, scalar_extension_functor,
          scalar_extended_source_resolution] using
          (Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
            (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))).projective_obj
            ((scalar_extended_source_resolution (R := R) (M := M)).projective 2)
    have hright :
        Projective (kernel_cover_object (R := R) (S := S) (M := M)) := by
      simpa [kernel_cover_object, kernel_cover_resolution] using
        (kernel_cover_resolution (R := R) (S := S) (M := M)).projective 0
    simpa [corrected_target_resolution_complex, corrected_target_degree_two_object] using
      (show Projective
          (scalar_extended_resolution_X (R := R) (S := S) (M := M) 2 ⊞
            kernel_cover_object (R := R) (S := S) (M := M)) from inferInstance)
  ·
    let e :=
      ChainComplex.mkXIso
        (X₀ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 0)
        (X₁ := scalar_extended_resolution_X (R := R) (S := S) (M := M) 1)
        (X₂ := corrected_target_degree_two_object (R := R) (S := S) (M := M))
        (d₀ := scalar_extended_d_one (R := R) (S := S) (M := M))
        (d₁ := corrected_target_degree_two_map (R := R) (S := S) (M := M))
        (s := corrected_window_zero (R := R) (S := S) (M := M))
        (succ := fun T ↦ ⟨Projective.syzygies T.f, Projective.d T.f, projective_d_comp_zero T.f⟩)
        n
    exact Projective.of_iso e.symm inferInstance

/-- Helper for Lemma 10.99.13: existence of the corrected target projective resolution whose front
window is the textbook corrected scalar-extended presentation. -/
private theorem corrected_target_resolution_exists :
    Nonempty (CategoryTheory.ProjectiveResolution (@baseChangedModule R S M _ _ _ _ _)) := by
  refine ⟨?_⟩
  refine
    { complex := corrected_target_resolution_complex (R := R) (S := S) (M := M)
      projective := corrected_target_resolution_complex_projective (R := R) (S := S) (M := M)
      π := (ChainComplex.toSingle₀Equiv _ _).symm
        ⟨scalar_extended_pi_zero (R := R) (S := S) (M := M),
          scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M)⟩
      quasiIso := ?_ }
  -- Quasi-isomorphism at degree `0` comes from the unchanged lower window; higher exactness uses
  -- the corrected `2 → 1 → 0` window and the canonical `Projective.d` tail.
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simpa [corrected_target_resolution_complex] using
          corrected_target_resolution_complex_exact_zero (R := R) (S := S) (M := M)
      all_goals rfl
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · cases n with
        | zero =>
            exact corrected_target_resolution_complex_exact_one (R := R) (S := S) (M := M)
        | succ n =>
            simpa [Nat.add_assoc] using
              corrected_target_resolution_complex_exact_succ
                (R := R) (S := S) (M := M) n
      · apply ChainComplex.exactAt_succ_single_obj

/-- Helper for Lemma 10.99.13: the explicit corrected target chain map to `M'` is a
quasi-isomorphism, using the unchanged lower window and the canonical exact tail. -/
private theorem corrected_target_resolution_quasiIso :
    QuasiIso
      (((ChainComplex.toSingle₀Equiv
          (corrected_target_resolution_complex (R := R) (S := S) (M := M))
          (@baseChangedModule R S M _ _ _ _ _)).symm
        ⟨scalar_extended_pi_zero (R := R) (S := S) (M := M),
          scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M)⟩) :
        corrected_target_resolution_complex (R := R) (S := S) (M := M) ⟶
          (ChainComplex.single₀ (ModuleCat S)).obj (@baseChangedModule R S M _ _ _ _ _)) := by
  -- The quasi-isomorphism proof follows the source proof: exactness at degree `0` is unchanged,
  -- degree `1` is corrected by the added cover summand, and all higher degrees use the
  -- canonical `Projective.d` tail.
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simpa [corrected_target_resolution_complex] using
          corrected_target_resolution_complex_exact_zero (R := R) (S := S) (M := M)
      all_goals rfl
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · cases n with
        | zero =>
            exact corrected_target_resolution_complex_exact_one (R := R) (S := S) (M := M)
        | succ n =>
            simpa [Nat.add_assoc] using
              corrected_target_resolution_complex_exact_succ
                (R := R) (S := S) (M := M) n
      · apply ChainComplex.exactAt_succ_single_obj

/-- Helper for Lemma 10.99.13: choose the corrected target projective resolution built above. -/
private noncomputable def corrected_target_resolution :
    CategoryTheory.ProjectiveResolution (@baseChangedModule R S M _ _ _ _ _) :=
  { complex := corrected_target_resolution_complex (R := R) (S := S) (M := M)
    projective := corrected_target_resolution_complex_projective (R := R) (S := S) (M := M)
    π := (ChainComplex.toSingle₀Equiv
        (corrected_target_resolution_complex (R := R) (S := S) (M := M))
        (@baseChangedModule R S M _ _ _ _ _)).symm
      ⟨scalar_extended_pi_zero (R := R) (S := S) (M := M),
        scalar_extended_d_one_comp_pi_zero (R := R) (S := S) (M := M)⟩
    quasiIso := corrected_target_resolution_quasiIso (R := R) (S := S) (M := M) }

/-- Helper for Lemma 10.99.13: existence of the owner-level identification computing the target
`Tor₁` module from the corrected target resolution tensored with `S / IS`. -/
private theorem target_owner_to_corrected_window_h1_iso_exists (I : Ideal R) :
    Nonempty
      (((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R) ≅
        (ModuleCat.restrictScalars (algebraMap R S)).obj
          (ShortComplex.homology
            (tensorRight_degree_one_window_of_resolution (R := S)
              (quotientModule (R := R) (S := S) I)
              (corrected_target_resolution (R := R) (S := S) (M := M))))) := by
  refine ⟨?_⟩
  let eFlip :
      ((@torOneQuotientTarget R S M _ _ _ _ _ I) : ModuleCat S) ≅
        (((Functor.flip (Tor' (ModuleCat S) 1)).obj
            (quotientModule (R := R) (S := S) I)).obj
          (@baseChangedModule R S M _ _ _ _ _)) :=
    (((tor_flip_iso (ModuleCat S) 1).app
        (quotientModule (R := R) (S := S) I)).app
      (@baseChangedModule R S M _ _ _ _ _))
  let eDerived :
      (((Functor.flip (Tor' (ModuleCat S) 1)).obj
          (quotientModule (R := R) (S := S) I)).obj
        (@baseChangedModule R S M _ _ _ _ _)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) 1).obj
          (((tensorRight (quotientModule (R := R) (S := S) I)).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
            (corrected_target_resolution (R := R) (S := S) (M := M)).complex) :=
    (corrected_target_resolution (R := R) (S := S) (M := M)).isoLeftDerivedObj
      (tensorRight (quotientModule (R := R) (S := S) I)) 1
  let eWindow :
      (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) 1).obj
        (((tensorRight (quotientModule (R := R) (S := S) I)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (corrected_target_resolution (R := R) (S := S) (M := M)).complex) ≅
        ShortComplex.homology
          (tensorRight_degree_one_window_of_resolution (R := S)
            (quotientModule (R := R) (S := S) I)
            (corrected_target_resolution (R := R) (S := S) (M := M))) :=
    tensorRight_degree_one_window_homology_iso_of_resolution (R := S)
      (quotientModule (R := R) (S := S) I)
      (corrected_target_resolution (R := R) (S := S) (M := M))
  -- Restricting scalars simply views the same owner-level comparison over `R`.
  exact
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (eFlip ≪≫ eDerived ≪≫ eWindow)

/-- Helper for Lemma 10.99.13: choose the owner-level target identification built from the
corrected target resolution. -/
private noncomputable abbrev target_owner_to_corrected_window_h1_iso (I : Ideal R) :
    ((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ShortComplex.homology
          (tensorRight_degree_one_window_of_resolution (R := S)
            (quotientModule (R := R) (S := S) I)
            (corrected_target_resolution (R := R) (S := S) (M := M)))) :=
  Classical.choice
    (target_owner_to_corrected_window_h1_iso_exists (R := R) (S := S) (M := M) I)

/-- Helper for Lemma 10.99.13: tensoring the scalar-extended `2 → 1 → 0` window with `S / IS`
still gives a short complex because the scalar-extended differential squares to zero. -/
private theorem quotient_tensor_scalar_extended_d_two_comp_d_one (I : Ideal R) :
    (tensorRight (quotientModule (R := R) (S := S) I)).map
        (scalar_extended_d_two (R := R) (S := S) (M := M)) ≫
      (tensorRight (quotientModule (R := R) (S := S) I)).map
        (scalar_extended_d_one (R := R) (S := S) (M := M)) =
    0 := by
  -- The quotient-tensor functor preserves composition and zero morphisms.
  rw [← Functor.map_comp, scalar_extended_d_two_comp_d_one, Functor.map_zero]

/-- Helper for Lemma 10.99.13: the uncorrected scalar-extended target window tensored with
`S / IS`. -/
private noncomputable abbrev uncorrected_target_window (I : Ideal R) :
    ShortComplex (ModuleCat S) :=
  ShortComplex.mk
    ((tensorRight (quotientModule (R := R) (S := S) I)).map
      (scalar_extended_d_two (R := R) (S := S) (M := M)))
    ((tensorRight (quotientModule (R := R) (S := S) I)).map
      (scalar_extended_d_one (R := R) (S := S) (M := M)))
    (quotient_tensor_scalar_extended_d_two_comp_d_one (R := R) (S := S) (M := M) I)

/-- Helper for Lemma 10.99.13: the source tensor object already has the raw tensor-product
carrier used by the explicit comparison map. -/
private theorem quotient_tensor_scalar_extension_source_eq
    (I : Ideal R) (X : ModuleCat R) :
    ((tensorRight (ModuleCat.of R (S ⧸ extendedIdeal I))).obj X) =
      ModuleCat.of R (TensorProduct R X (S ⧸ extendedIdeal I)) :=
  rfl

/-- Helper for Lemma 10.99.13: the source tensor object is canonically the raw tensor-product
carrier used by the explicit comparison map. -/
private noncomputable abbrev quotient_tensor_scalar_extension_source_iso
    (I : Ideal R) (X : ModuleCat R) :
    ((tensorRight (ModuleCat.of R (S ⧸ extendedIdeal I))).obj X) ≅
      ModuleCat.of R (TensorProduct R X (S ⧸ extendedIdeal I)) :=
  eqToIso (quotient_tensor_scalar_extension_source_eq (R := R) (S := S) I X)

/-- Helper for Chap10 Lemma 10 99 13: the original `R`-action on
`S ⧸ extendedIdeal I` agrees with the action obtained by restricting scalars from `S`. -/
private theorem quotientModule_restrictScalars_smul
    (I : Ideal R) (r : R) (q : S ⧸ extendedIdeal I) :
    (algebraMap R S r) • q = r • q := by
  -- Reduce the quotient statement to representatives, where both actions are multiplication by
  -- `algebraMap R S r`.
  refine Submodule.Quotient.induction_on _ q ?_
  intro s
  simp [Algebra.smul_def]

/-- Helper for Chap10 Lemma 10 99 13: the additive identity map from the quotient to its
restricted-scalar presentation. -/
private def quotientModule_toRestrictScalars_addHom (I : Ideal R) :
    (S ⧸ extendedIdeal I) →+
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (quotientModule (R := R) (S := S) I)) where
  toFun q := q
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Helper for Chap10 Lemma 10 99 13: the additive identity map from the restricted-scalar
presentation of the quotient back to the original `R`-module presentation. -/
private def quotientModule_fromRestrictScalars_addHom (I : Ideal R) :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (quotientModule (R := R) (S := S) I)) →+
      (S ⧸ extendedIdeal I) where
  toFun q := q
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Helper for Chap10 Lemma 10 99 13: the identity map from the original quotient presentation
to the restricted-scalar presentation is `R`-linear. -/
private theorem quotientModule_toRestrictScalars_map_smul
    (I : Ideal R) (r : R) (q : S ⧸ extendedIdeal I) :
    (quotientModule_toRestrictScalars_addHom (R := R) (S := S) I) (r • q) =
      r • (quotientModule_toRestrictScalars_addHom (R := R) (S := S) I) q := by
  -- This is the scalar-action comparison, read in the target restricted-scalar module.
  exact (quotientModule_restrictScalars_smul (R := R) (S := S) I r q).symm

/-- Helper for Chap10 Lemma 10 99 13: the identity map from the restricted-scalar quotient
presentation back to the original presentation is `R`-linear. -/
private theorem quotientModule_fromRestrictScalars_map_smul
    (I : Ideal R) (r : R)
    (q :
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (quotientModule (R := R) (S := S) I))) :
    (quotientModule_fromRestrictScalars_addHom (R := R) (S := S) I) (r • q) =
      r • (quotientModule_fromRestrictScalars_addHom (R := R) (S := S) I) q := by
  -- This is the same scalar-action comparison, read back in the original quotient module.
  exact quotientModule_restrictScalars_smul (R := R) (S := S) I r q

/-- Helper for Chap10 Lemma 10 99 13: the quotient coefficient is `R`-linearly identical to its
restricted-scalar presentation. -/
private noncomputable def quotientModule_restrictScalars_linearEquiv (I : Ideal R) :
    (S ⧸ extendedIdeal I) ≃ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (quotientModule (R := R) (S := S) I)) :=
  -- Package the identity maps directly, avoiding expensive definitional comparison between the
  -- two bundled module structures.
  { toFun := fun q ↦ q
    invFun := fun q ↦ q
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := quotientModule_toRestrictScalars_map_smul (R := R) (S := S) I }

/-- Helper for Chap10 Lemma 10 99 13: cancelling the intermediate base change identifies
`Q ⊗[S] (S ⊗[R] X)` after restriction of scalars with `Q ⊗[R] X`. -/
private noncomputable def quotient_tensor_scalar_extension_cancelBaseChange_iso
    (I : Ideal R) (X : ModuleCat R) :
    ((ModuleCat.extendScalars (algebraMap R S)) ⋙
        (curriedTensor (ModuleCat S)).obj (quotientModule (R := R) (S := S) I) ⋙
        (ModuleCat.restrictScalars (algebraMap R S))).obj X ≅
      ((curriedTensor (ModuleCat R)).obj
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          (quotientModule (R := R) (S := S) I))).obj X :=
  -- Use mathlib's `cancelBaseChange` comparison under the scalar-restriction instances used by
  -- `ModuleCat.extendScalars`.
  let f : R →+* S := algebraMap R S
  letI : Algebra R S := f.toAlgebra
  letI : Module R (quotientModule (R := R) (S := S) I) :=
    Module.compHom (quotientModule (R := R) (S := S) I) f
  letI : IsScalarTower R S (quotientModule (R := R) (S := S) I) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (ModuleCat.restrictScalars f).mapIso
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S
      (S ⧸ extendedIdeal I) X).toModuleIso)

/-- Helper for Lemma 10.99.13: for any source module term `X`, tensoring with `S / IS` over `R`
matches restricting scalars on the scalar-extended term tensored with `S / IS` over `S`. -/
private noncomputable def quotient_tensor_scalar_extension_term_iso (I : Ideal R) (X : ModuleCat R) :
    ((tensorRight (ModuleCat.of R (S ⧸ extendedIdeal I))).obj X) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((tensorRight (quotientModule (R := R) (S := S) I)).obj
          ((scalar_extension_functor (R := R) (S := S)).obj X)) :=
  -- Move `X ⊗ Q` to the restricted quotient coefficient, cancel the intermediate base change,
  -- and finally braid the two `S`-tensor factors into the target order.
  quotient_tensor_scalar_extension_source_iso (R := R) (S := S) I X ≪≫
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R X)
      (quotientModule_restrictScalars_linearEquiv (R := R) (S := S) I)).toModuleIso ≪≫
    (β_ X
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (quotientModule (R := R) (S := S) I))) ≪≫
    (quotient_tensor_scalar_extension_cancelBaseChange_iso
      (R := R) (S := S) I X).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (β_ (quotientModule (R := R) (S := S) I)
        ((scalar_extension_functor (R := R) (S := S)).obj X))

/-- Helper for Lemma 10.99.13: the tensor/base-change term isomorphism sends a pure tensor
`x ⊗ q` to `((1 ⊗ x) ⊗ q)`. -/
private theorem quotient_tensor_scalar_extension_term_iso_pure_tensor
    (I : Ideal R) (X : ModuleCat R) (x : X) (q : S ⧸ extendedIdeal I) :
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I X).hom (x ⊗ₜ[R] q) =
      ((((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] q :
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          ((tensorRight (quotientModule (R := R) (S := S) I)).obj
            ((scalar_extension_functor (R := R) (S := S)).obj X))))) := by
  -- Unfold the component iso to the four canonical steps; on pure tensors each step is
  -- definitionally the displayed swap/cancel/swap.
  simp only [quotient_tensor_scalar_extension_term_iso,
    quotient_tensor_scalar_extension_source_iso,
    quotient_tensor_scalar_extension_cancelBaseChange_iso, Iso.trans_hom, ModuleCat.hom_comp]
  rfl

/-- Helper for Lemma 10.99.13: the termwise tensor/base-change identification is natural in the
source module morphism. -/
private theorem quotient_tensor_scalar_extension_term_iso_naturality
    (I : Ideal R) {X Y : ModuleCat R} (f : X ⟶ Y) :
    (tensorRight (ModuleCat.of R (S ⧸ extendedIdeal I))).map f ≫
        (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I Y).hom =
      (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I X).hom ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          ((tensorRight (quotientModule (R := R) (S := S) I)).map
            ((scalar_extension_functor (R := R) (S := S)).map f)) := by
  -- It is enough to compare the two `R`-linear maps on pure tensors; the pure-tensor formula
  -- turns both sides into `((1 : S) ⊗ f x) ⊗ q`.
  ext z
  let leftMap :=
    Hom.hom
      ((tensorRight (ModuleCat.of R (S ⧸ extendedIdeal I))).map f ≫
        (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I Y).hom)
  let rightMap :=
    Hom.hom
      ((quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I X).hom ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          ((tensorRight (quotientModule (R := R) (S := S) I)).map
            ((scalar_extension_functor (R := R) (S := S)).map f)))
  change leftMap z = rightMap z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul x q =>
      change
        (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I Y).hom
            (f x ⊗ₜ[R] q) =
          ((ModuleCat.restrictScalars (algebraMap R S)).map
            ((tensorRight (quotientModule (R := R) (S := S) I)).map
              ((scalar_extension_functor (R := R) (S := S)).map f)))
            ((quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I X).hom
              (x ⊗ₜ[R] q))
      rw [quotient_tensor_scalar_extension_term_iso_pure_tensor]
      rw [quotient_tensor_scalar_extension_term_iso_pure_tensor]
      rfl
  | add z w hz hw =>
      exact
        (map_add leftMap z w).trans
          ((congrArg₂ (fun a b ↦ a + b) hz hw).trans
            (map_add rightMap z w).symm)

/-- Helper for Lemma 10.99.13: the source `R`-window tensored with `S / IS` is identified with
the restriction of scalars of the uncorrected scalar-extended `S`-window. -/
private theorem quotient_tensor_scalar_extension_window_comm_two_one (I : Ideal R) :
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2)).hom ≫
        ((uncorrected_target_window (R := R) (S := S) (M := M) I).map
          (ModuleCat.restrictScalars (algebraMap R S))).f =
      (tensorRight_degree_one_window (R := R)
          (ModuleCat.of R (S ⧸ extendedIdeal I)) (ModuleCat.of R M)).f ≫
        (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom := by
  -- This is the source differential instance of the general naturality statement.
  simpa [tensorRight_degree_one_window, tensorRight_degree_one_window_of_resolution,
    uncorrected_target_window, scalar_extended_d_two, scalar_extension_functor,
    scalar_extended_source_resolution] using
    (quotient_tensor_scalar_extension_term_iso_naturality
      (R := R) (S := S) I
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 2 1)).symm

/-- Helper for Lemma 10.99.13: the source/target tensor-base-change comparison is also natural on
the lower differential of the chosen source resolution. -/
private theorem quotient_tensor_scalar_extension_window_comm_one_zero (I : Ideal R) :
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
        ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1)).hom ≫
        ((uncorrected_target_window (R := R) (S := S) (M := M) I).map
          (ModuleCat.restrictScalars (algebraMap R S))).g =
      (tensorRight_degree_one_window (R := R)
          (ModuleCat.of R (S ⧸ extendedIdeal I)) (ModuleCat.of R M)).g ≫
        (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
          ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0)).hom := by
  -- This is the lower differential instance of the same naturality statement.
  simpa [tensorRight_degree_one_window, tensorRight_degree_one_window_of_resolution,
    uncorrected_target_window, scalar_extended_d_one, scalar_extension_functor,
    scalar_extended_source_resolution] using
    (quotient_tensor_scalar_extension_term_iso_naturality
      (R := R) (S := S) I
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.d 1 0)).symm

/-- Helper for Lemma 10.99.13: the source `R`-window tensored with `S / IS` is identified with
the restriction of scalars of the uncorrected scalar-extended `S`-window. -/
private noncomputable def restrictScalars_quotient_tensor_scalar_extension_window_iso
    (I : Ideal R) :
    tensorRight_degree_one_window (R := R)
      (ModuleCat.of R (S ⧸ extendedIdeal I)) (ModuleCat.of R M) ≅
      (uncorrected_target_window (R := R) (S := S) (M := M) I).map
        (ModuleCat.restrictScalars (algebraMap R S)) :=
  ShortComplex.isoMk
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 2))
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 1))
    (quotient_tensor_scalar_extension_term_iso (R := R) (S := S) I
      ((scalar_extended_source_resolution (R := R) (M := M)).complex.X 0))
    (quotient_tensor_scalar_extension_window_comm_two_one
      (R := R) (S := S) (M := M) I)
    (quotient_tensor_scalar_extension_window_comm_one_zero
      (R := R) (S := S) (M := M) I)

/-- Helper for Lemma 10.99.13: the source `Tor₁` owner is identified with the restricted
homology of the uncorrected scalar-extended target window. -/
-- TODO: compose the already-proved source owner/window iso with the short-complex homology iso
-- induced by `restrictScalars_quotient_tensor_scalar_extension_window_iso` and then with
-- `(uncorrected_target_window I).mapHomologyIso (ModuleCat.restrictScalars _)`.
private noncomputable def source_owner_to_uncorrected_target_window_h1_iso (I : Ideal R) :
    ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ShortComplex.homology
          (uncorrected_target_window (R := R) (S := S) (M := M) I)) :=
  -- First compute the source owner from the source `2 → 1 → 0` window, then transport that
  -- window across the tensor/base-change isomorphism, and finally identify homology after
  -- restricting scalars.
  source_owner_to_source_window_h1_iso (R := R) (S := S) (M := M) I ≪≫
    ShortComplex.homologyMapIso
      (restrictScalars_quotient_tensor_scalar_extension_window_iso
        (R := R) (S := S) (M := M) I) ≪≫
    (uncorrected_target_window (R := R) (S := S) (M := M) I).mapHomologyIso
      (ModuleCat.restrictScalars (algebraMap R S))

/-- Helper for Lemma 10.99.13: the uncorrected target window maps to the actual front window of
the corrected target resolution by the degree-two inclusion and identities below. -/
private noncomputable def corrected_target_front_window_comparison (I : Ideal R) :
    uncorrected_target_window (R := R) (S := S) (M := M) I ⟶
      tensorRight_degree_one_window_of_resolution (R := S)
        (quotientModule (R := R) (S := S) I)
        (corrected_target_resolution (R := R) (S := S) (M := M)) where
  τ₁ := (tensorRight (quotientModule (R := R) (S := S) I)).map biprod.inl
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    -- The corrected degree-two differential restricts to the uncorrected one on the left
    -- summand, matching the source proof's inclusion of complexes.
    change
      (tensorRight (quotientModule (R := R) (S := S) I)).map biprod.inl ≫
          (tensorRight (quotientModule (R := R) (S := S) I)).map
            (corrected_target_degree_two_map (R := R) (S := S) (M := M)) =
        (tensorRight (quotientModule (R := R) (S := S) I)).map
          (scalar_extended_d_two (R := R) (S := S) (M := M))
    rw [← Functor.map_comp]
    simp [corrected_target_degree_two_map]
  comm₂₃ := by
    -- Degrees one and zero are unchanged in the corrected resolution.
    simp [uncorrected_target_window, tensorRight_degree_one_window_of_resolution,
      corrected_target_resolution, corrected_target_resolution_complex]

/-- Helper for Lemma 10.99.13: the front-window comparison induces a surjective map on
degree-one homology, and restricting scalars preserves that surjectivity. -/
private theorem corrected_target_front_window_homologyMap_surjective (I : Ideal R) :
    Function.Surjective
      ((ModuleCat.restrictScalars (algebraMap R S)).map
        (ShortComplex.homologyMap
          (corrected_target_front_window_comparison (R := R) (S := S) (M := M) I))) := by
  -- The middle and right components are identities, so the induced degree-one homology map is
  -- surjective before and after restricting scalars.
  let comparison :=
    corrected_target_front_window_comparison (R := R) (S := S) (M := M) I
  haveI : IsIso comparison.τ₂ := by
    change IsIso (𝟙 _)
    infer_instance
  haveI : IsIso comparison.τ₃ := by
    change IsIso (𝟙 _)
    infer_instance
  have hsurj :
      Function.Surjective
        (ShortComplex.homologyMap comparison) :=
    surjective_shortComplex_homologyMap_of_isIso_τ₂_τ₃ comparison
  exact surjective_restrictScalars_map _ hsurj


-- Proof sketch: resolve `M` by a free `R`-resolution, tensor termwise with `S / IS`, and compare
-- the resulting complex with an `S`-free resolution of `S ⊗[R] M` extending the scalar-extended
-- resolution. The induced map on degree-one homology is the textbook comparison map, and the extra
-- free summand in degree two makes that map surjective.
/-- Chap10 Lemma 10 99 13: with `I' = IS` and `M' = S ⊗[R] M`, there exists a natural comparison map
`Tor₁^R(S / I', M) → Tor₁^S(S / I', M')`, written in Lean using the canonical owner
`CategoryTheory.Tor`; the target is viewed over `R` using the canonical
`ModuleCat.restrictScalars` functor. This comparison is surjective. The chapter already contains
the owner-level `Tor`/base-change machinery, but this particular quotient-coefficient comparison is
recorded here only at the source-facing existence/surjectivity layer to avoid introducing a
noncanonical chosen witness as public API. -/
@[stacks 00MN]
theorem exists_surjective_torOne_quotient_baseChangeComparison (I : Ideal R) :
    ∃ comparison :
      ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ⟶
        ((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R),
      Function.Surjective comparison := by
  -- Route correction: the source owner is now already identified with the restricted uncorrected
  -- target window, so the remaining work is the source-side tensor/base-change transport together
  -- with the target-side front-window comparison into the actual corrected resolution.
  let comparison :
      ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ⟶
        ((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R) :=
    (source_owner_to_uncorrected_target_window_h1_iso (R := R) (S := S) (M := M) I).hom ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        (ShortComplex.homologyMap
          (corrected_target_front_window_comparison (R := R) (S := S) (M := M) I)) ≫
      (target_owner_to_corrected_window_h1_iso (R := R) (S := S) (M := M) I).inv
  refine ⟨comparison, ?_⟩
  -- Conjugate the surjective front-window homology map by the owner/window identifications.
  have hmiddle :
      Function.Surjective
        ((ModuleCat.restrictScalars (algebraMap R S)).map
          (ShortComplex.homologyMap
            (corrected_target_front_window_comparison (R := R) (S := S) (M := M) I))) :=
    corrected_target_front_window_homologyMap_surjective
      (R := R) (S := S) (M := M) I
  simpa [comparison] using
    surjective_of_iso_conjugation
      (source_owner_to_uncorrected_target_window_h1_iso (R := R) (S := S) (M := M) I)
      (target_owner_to_corrected_window_h1_iso (R := R) (S := S) (M := M) I)
      _ hmiddle

end
