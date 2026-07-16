import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_3
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_4
import StacksProject_2024.stacks_project.Chap13.Definition_13_15_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex₂
open CochainComplex
open DerivedCategory.TStructure
open scoped CategoryTheory HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

/- Domain-style sampling:
- primary domain: Cartan-Eilenberg double complexes, their two canonical filtered totals, and the
  associated cohomological spectral sequences together with the bounded-below right-derived
  abutment;
- sampled owner declarations:
  `Functor.mapHomologicalComplex`,
  `firstDoubleComplexFilteredComplex`,
  `secondDoubleComplexFilteredComplex`,
  `Functor.totalRightDerived`;
- best owner abstraction: the functorial image of a double complex is the iterated canonical owner
  `((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj I`, while the two spectral
  sequences are owned by the canonical filtered complexes attached to that double complex, and the
  abutment is owned by the bounded-below right derived functor of
  `mapBoundedBelowHomotopyCategoryToDerivedBelow F`;
- primitive data here: the bounded-below source complex `K`, a Cartan-Eilenberg resolution `CE`
  of `K`, and the resulting mapped double complex;
- derived API here: the two associated spectral sequences, their page identifications,
  boundedness, the two finite abutment-filtration owners, the two convergence packages, together
  with the canonical comparison from `H^*(Tot(F(I^{•,•})))` to the right-derived cohomology of
  `K^•`;
- source/core/bridge triage:
  `source-facing`: the existence statement for the two Cartan-Eilenberg spectral sequences;
  `core/canonical`: the mapped double complex owner from `Functor.mapHomologicalComplex`, the two
    filtered-complex owners, `Functor.totalRightDerived`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the page-one and page-two identifications with the right-derived functors and
    the abutment isomorphism to the bounded-below derived value.

The one-off name for the mapped double complex is therefore a duplicate wheel: the theorem should
use the canonical owner directly, derive the two filtered-complex views from it, and expose the
abutment through the canonical bounded-below right-derived owner rather than an existential
`HasTotal` witness.
-/

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
variable [Category.{v₁} 𝒜] [Category.{v₂} 𝒝] [Abelian 𝒜] [Abelian 𝒝]
variable [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒝]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable [LocallySmall 𝒝] [WellPowered 𝒝] [HasWidePullbacks 𝒝] [HasCoproducts 𝒝]
variable [InitialMonoClass 𝒝]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒝)))

section

variable (F : 𝒜 ⥤ 𝒝) [F.Additive] [PreservesFiniteLimits F] [HasInjectiveResolutions 𝒜]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (K : CochainComplex.Plus 𝒜) (CE : CartanEilenbergResolution K)

local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜

/-- Helper for Lemma 13.21.3: the underlying Cartan-Eilenberg double complex has only finitely
many nonzero terms on each antidiagonal. -/
private theorem cartan_eilenberg_has_finite_antidiagonal_support :
    doubleComplexHasFiniteAntidiagonalSupport CE.doubleComplex.obj := by
  obtain ⟨a, ha⟩ :=
    (CochainComplex.plus_iff (C := CochainComplex 𝒜 ℤ) CE.doubleComplex.obj).mp
      CE.doubleComplex.property
  intro n
  -- Proof comment: any nonzero summand on the antidiagonal `p + q = n` must satisfy the
  -- horizontal lower bound `a ≤ p` and the vertical lower bound `0 ≤ q = n - p`.
  refine (Set.finite_Icc a n).subset ?_
  intro p hp
  constructor
  · by_contra hpa
    have hp_lt : p < a := lt_of_not_ge hpa
    have hzeroColumn : IsZero (CE.doubleComplex.obj.X p) := by
      let _ : CE.doubleComplex.obj.IsStrictlyGE a := ha
      exact CE.doubleComplex.obj.isZero_of_isGE a p hp_lt
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) :=
      (HomologicalComplex.eval 𝒜 (up ℤ) (n - p)).map_isZero hzeroColumn
    exact hp hzeroSource
  · by_contra hpn
    have hn_lt : n < p := lt_of_not_ge hpn
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) := by
      let _ : CochainComplex.IsStrictlyGE (CE.doubleComplex.obj.X p) 0 :=
        CE.vertical_isStrictlyGE p
      exact (CE.doubleComplex.obj.X p).isZero_of_isGE 0 (n - p) (by omega)
    exact hp hzeroSource

/-- Helper for Lemma 13.21.3: the mapped Cartan-Eilenberg double complex has only finitely many
nonzero terms on each antidiagonal. -/
private theorem mapped_cartan_eilenberg_has_finite_antidiagonal_support :
    let I :=
      ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    doubleComplexHasFiniteAntidiagonalSupport I := by
  let I :=
    ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
  obtain ⟨a, ha⟩ :=
    (CochainComplex.plus_iff (C := CochainComplex 𝒜 ℤ) CE.doubleComplex.obj).mp
      CE.doubleComplex.property
  intro n
  -- Proof comment: a nonzero term on the antidiagonal `p + q = n` must lie inside the finite
  -- interval forced by the horizontal lower bound `p ≥ a` and the vertical lower bound `q ≥ 0`.
  refine (Set.finite_Icc a n).subset ?_
  intro p hp
  constructor
  · by_contra hpa
    have hp_lt : p < a := lt_of_not_ge hpa
    have hzeroColumn : IsZero (CE.doubleComplex.obj.X p) := by
      let _ : CE.doubleComplex.obj.IsStrictlyGE a := ha
      exact CE.doubleComplex.obj.isZero_of_isGE a p hp_lt
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) :=
      (HomologicalComplex.eval 𝒜 (up ℤ) (n - p)).map_isZero hzeroColumn
    have hzeroTarget : IsZero ((I.X p).X (n - p)) := by
      simpa [I, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using F.map_isZero hzeroSource
    exact hp hzeroTarget
  · by_contra hpn
    have hn_lt : n < p := lt_of_not_ge hpn
    have hzeroSource : IsZero ((CE.doubleComplex.obj.X p).X (n - p)) := by
      let _ : CochainComplex.IsStrictlyGE (CE.doubleComplex.obj.X p) 0 :=
        CE.vertical_isStrictlyGE p
      exact (CE.doubleComplex.obj.X p).isZero_of_isGE 0 (n - p) (by omega)
    have hzeroTarget : IsZero ((I.X p).X (n - p)) := by
      simpa [I, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using F.map_isZero hzeroSource
    exact hp hzeroTarget

/-- Helper for Lemma 13.21.3: on the first filtered total of a double complex, the `E₁`-page is
the vertical homology of the corresponding column. -/
private noncomputable def first_filtered_page_one_iso_to_column_homology
    (I : HomologicalComplex₂ 𝒝 (up ℤ) (up ℤ)) [I.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒝 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex I) E]
    (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (I.X p).homology q := by
  -- Proof comment: the owner `FilteredComplex.pageOneIso` computes the first page in terms of
  -- the graded pieces of the first filtration, and Lemma `12.25.1` identifies those graded
  -- pieces with the vertical homology of the columns.
  simpa [firstDoubleComplexPageOne_def] using
    (FilteredComplex.pageOneIso (firstDoubleComplexFilteredComplex I) E p q)

/-- Helper for Lemma 13.21.3: on the second filtered total of a double complex, the `E₁`-page is
the horizontal homology of the corresponding row. -/
private noncomputable theorem second_filtered_page_one_iso_to_row_homology
    (I : HomologicalComplex₂ 𝒝 (up ℤ) (up ℤ)) [I.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒝 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex I) E]
    (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (I.flip.X p).homology q := by
  -- Proof comment: this is the rowwise analogue of the first-page column computation, obtained
  -- by feeding the second filtered total into the owner `FilteredComplex.pageOneIso`.
  simpa [secondDoubleComplexPageOne_def] using
    (FilteredComplex.pageOneIso (secondDoubleComplexFilteredComplex I) E p q)

/-- Helper for Lemma 13.21.3: applying `F` to the chosen column comparison `CE.columnIso p`
identifies the homology of the mapped chosen resolution with the homology of the mapped `p`-th
column. -/
private noncomputable theorem mapped_column_homology_iso_to_resolution
    (p q : ℤ) :
    (((F.mapHomologicalComplex (up ℤ)).obj ((CE.columnResolution p).cochainComplex)).homology q) ≅
      (((F.mapHomologicalComplex (up ℤ)).obj (CE.doubleComplex.obj.X p)).homology q) := by
  -- Proof comment: the source proof first replaces the actual column by the chosen injective
  -- resolution of `K^p`; here that transport is just `F.mapHomologicalComplex` applied to
  -- `CE.columnIso p`, followed by homology in degree `q`.
  exact
    (HomologicalComplex.homologyFunctor 𝒝 (up ℤ) q).mapIso
      (((F.mapHomologicalComplex (up ℤ)).mapIso (CE.columnIso p)))

/-- Helper for Lemma 13.21.3: the first spectral-sequence `E₁`-term identifies with the homology
of `F` applied to the chosen injective resolution of `K^p`. -/
private noncomputable theorem first_page_one_iso_to_mapped_column_resolution
    (E : CohomologicalSpectralSequence 𝒝 0)
    (hAssoc :
      IsAssociatedToFilteredComplex
        (firstDoubleComplexFilteredComplex
          (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
            CE.doubleComplex.obj))
        E)
    (p : ℤ) (q : ℕ) :
    (E.page 1).X (p, Int.ofNat q) ≅
      (((F.mapHomologicalComplex (up ℤ)).obj ((CE.columnResolution p).cochainComplex)).homology
        (Int.ofNat q)) := by
  let I :=
    ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
  letI : IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex I) E := hAssoc
  let hpage :
      (E.page 1).X (p, Int.ofNat q) ≅
        (I.X p).homology (Int.ofNat q) :=
    first_filtered_page_one_iso_to_column_homology
      (I := I) (E := E) p (Int.ofNat q)
  let hpage' :
      (E.page 1).X (p, Int.ofNat q) ≅
        (((F.mapHomologicalComplex (up ℤ)).obj (CE.doubleComplex.obj.X p)).homology
          (Int.ofNat q)) := by
    -- Proof comment: unfold the mapped double-complex owner once so the `p`-th column is
    -- visibly `F` applied to the original Cartan-Eilenberg column.
    simpa [I, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using hpage
  -- Proof comment: the chosen column comparison `CE.columnIso p` replaces the actual column by
  -- the chosen injective resolution of `K^p`.
  exact
    hpage' ≪≫
      (mapped_column_homology_iso_to_resolution
        (F := F) (K := K) (CE := CE) p (Int.ofNat q)).symm

/-- Helper for Lemma 13.21.3: restricting the `ℤ`-indexed cochain complex attached to an
injective resolution along `embeddingUpNat` recovers the original `ℕ`-indexed cocomplex. -/
private noncomputable theorem injective_resolution_restriction_iso_cocomplex
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) :
    I.cochainComplex.restriction ComplexShape.embeddingUpNat ≅ I.cocomplex := by
  -- Proof comment: the restriction only sees the nonnegative degrees of the extended cochain
  -- complex, so each component is the canonical `cochainComplexXIso`, and the differentials agree
  -- by the defining formula for `InjectiveResolution.cochainComplex_d`.
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro n
    exact
      I.cochainComplex.restrictionXIso ComplexShape.embeddingUpNat
        (i := n) (i' := Int.ofNat n) (by simp) ≪≫
        I.cochainComplexXIso (Int.ofNat n) n rfl
  · rintro n _ rfl
    dsimp only
    rw [HomologicalComplex.restriction_d_eq (e := ComplexShape.embeddingUpNat)
      (K := I.cochainComplex) (i' := Int.ofNat n) (j' := Int.ofNat (n + 1))
      (by simp) (by simp)]
    rw [I.cochainComplex_d (Int.ofNat n) (Int.ofNat (n + 1)) n (n + 1) rfl rfl]
    simp

/-- Helper for Lemma 13.21.3: after applying `F`, restricting the `ℤ`-indexed mapped cochain
complex of an injective resolution along `embeddingUpNat` gives the mapped `ℕ`-indexed
cocomplex. -/
private noncomputable theorem mapped_injective_resolution_restriction_iso_cocomplex
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).restriction
      ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (up ℕ)).obj I.cocomplex) := by
  -- Proof comment: once the restriction comparison is established for the injective resolution
  -- itself, the mapped comparison is its image under `F.mapHomologicalComplex`.
  simpa using
    (F.mapHomologicalComplex (up ℕ)).mapIso
      (injective_resolution_restriction_iso_cocomplex (I := I))

/-- Helper for Lemma 13.21.3: in positive degrees, the `ℤ`-indexed mapped cochain complex of an
injective resolution computes the right derived functors after restricting to the native
`ℕ`-indexed cocomplex. -/
private noncomputable theorem mapped_injective_resolution_positive_cochain_homology_iso_right_derived_obj
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) (q : ℕ) :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology (Int.ofNat (q + 1))) ≅
      (F.rightDerived (q + 1)).obj X := by
  have hi'' : (up ℤ).prev (Int.ofNat (q + 1)) = Int.ofNat q := by
    simp
  have hk'' : (up ℤ).next (Int.ofNat (q + 1)) = Int.ofNat (q + 2) := by
    omega
  have hrestriction :
      (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology (Int.ofNat (q + 1))) ≅
        ((((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).restriction
          ComplexShape.embeddingUpNat).homology (q + 1)) := by
    -- Proof comment: positive degrees lie entirely inside the image of `embeddingUpNat`, so
    -- `restrictionHomologyIso` compares the `ℤ`-indexed homology with the restricted
    -- `ℕ`-indexed homology without any boundary correction.
    exact
      ((((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).restrictionHomologyIso
        ComplexShape.embeddingUpNat q (q + 1) (q + 2) (by simp) (by simp)
        (i' := Int.ofNat q) (j' := Int.ofNat (q + 1)) (k' := Int.ofNat (q + 2))
        (by simp) (by simp) (by simp) hi'' hk'').symm)
  -- Proof comment: after restricting, the mapped complex is the native mapped cocomplex of the
  -- injective resolution, so `I.isoRightDerivedObj` computes the right-derived value directly.
  exact
    hrestriction ≪≫
      HomologicalComplex.homologyMapIso
        (mapped_injective_resolution_restriction_iso_cocomplex (F := F) (I := I))
        (q + 1) ≪≫
      (I.isoRightDerivedObj F (q + 1)).symm

/-- Helper for Lemma 13.21.3: in degree `0`, the restricted mapped injective-resolution complex
and the full `ℤ`-indexed mapped cochain complex have the same cycles. -/
private noncomputable theorem mapped_injective_resolution_cycles_iso_nat_zero
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) :
    ((((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).restriction
        ComplexShape.embeddingUpNat).cycles 0) ≅
      (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).cycles (0 : ℤ)) := by
  let K := ((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex)
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let Sr : ShortComplex 𝒝 := Kr.sc' 0 0 1
  let Sf : ShortComplex 𝒝 := K.sc' (-1) 0 1
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
    -- Proof comment: expanding the restricted differential shows that both cycle objects are
    -- kernels of the same outgoing differential in the full mapped complex.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpNat) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Proof comment: identify both cycle objects with the kernel of the common degree-`0`
  -- differential of the full mapped cochain complex.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 13.21.3: the degree-`0` homology of the `ℤ`-indexed mapped cochain complex
of an injective resolution computes `R^0F`. -/
private noncomputable theorem mapped_injective_resolution_zero_cochain_homology_iso_right_derived_zero
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology (0 : ℤ)) ≅
      (F.rightDerived 0).obj X := by
  let K := ((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex)
  let Kr := K.restriction ComplexShape.embeddingUpNat
  have hzeroSource : IsZero (I.cochainComplex.X (-1 : ℤ)) := by
    let _ : CochainComplex.IsStrictlyGE I.cochainComplex 0 := inferInstance
    exact I.cochainComplex.isZero_of_isGE 0 (-1) (by omega)
  have hzeroTarget : IsZero (K.X (-1 : ℤ)) := by
    simpa [K, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using F.map_isZero hzeroSource
  have hzero_prev : K.d (-1) 0 = 0 := hzeroTarget.eq_of_src _ _
  -- Proof comment: degree `0` is the boundary case for restriction, so first replace homology by
  -- cycles in the full complex, compare those cycles with the restricted cocomplex, and only
  -- then apply the native injective-resolution computation of `R^0F`.
  exact
    (K.isoHomologyπ (-1) 0 (by simp) hzero_prev).symm ≪≫
      (mapped_injective_resolution_cycles_iso_nat_zero (F := F) (I := I)).symm ≪≫
      (CochainComplex.isoHomologyπ₀ Kr) ≪≫
      HomologicalComplex.homologyMapIso
        (mapped_injective_resolution_restriction_iso_cocomplex (F := F) (I := I))
        0 ≪≫
      (I.isoRightDerivedObj F 0).symm

/-- Helper for Lemma 13.21.3: the mapped chosen column resolution computes the object
`R^qF(K^p)`. -/
private noncomputable theorem mapped_column_resolution_homology_iso_to_rightDerived
    (p : ℤ) (q : ℕ) :
    (((F.mapHomologicalComplex (up ℤ)).obj ((CE.columnResolution p).cochainComplex)).homology
      (Int.ofNat q)) ≅
      (F.rightDerived q).obj (K.obj.X p) := by
  -- Route correction: the source proof computes `R^qF(K^p)` from the chosen injective resolution
  -- of `K^p`; the positive-degree transport is now reduced to the native `ℕ`-indexed
  -- `InjectiveResolution.isoRightDerivedObj`, leaving only the boundary degree `q = 0`.
  cases q with
  | zero =>
      -- Proof comment: the remaining boundary case is degree `0`, where the comparison must use
      -- the vanishing of degree `-1` in the extended cochain complex instead of the positive
      -- `restrictionHomologyIso` route.
      exact
        mapped_injective_resolution_zero_cochain_homology_iso_right_derived_zero
          (F := F) (I := CE.columnResolution p)
  | succ q =>
      exact
        mapped_injective_resolution_positive_cochain_homology_iso_right_derived_obj
          (F := F) (I := CE.columnResolution p) q

/-- Helper for Lemma 13.21.3: the bottom-row augmentation of a column already lands in the
cycles of that column. -/
private theorem cartan_eilenberg_column_augmentation_cycles
    (p : ℤ) :
    CE.ε.f p ≫ (CE.doubleComplex.obj.X p).d 0 1 = 0 := by
  have hcomm :
      (CE.columnIso p).hom.f 0 ≫ (CE.doubleComplex.obj.X p).d 0 1 =
        (CE.columnResolution p).cochainComplex.d 0 1 ≫ (CE.columnIso p).hom.f 1 := by
    simpa using ((CE.columnIso p).hom.comm (0 : ℤ) 1)
  have hcomp :
      ((CE.columnResolution p).ι' ≫ (CE.columnIso p).hom).f 0 ≫
          (CE.doubleComplex.obj.X p).d 0 1 = 0 := by
    -- Proof comment: transport the degree-zero augmentation along the column isomorphism and use
    -- the fact that the injective-resolution augmentation is a chain map from a single complex.
    calc
      ((CE.columnResolution p).ι' ≫ (CE.columnIso p).hom).f 0 ≫
          (CE.doubleComplex.obj.X p).d 0 1
        = (CE.columnResolution p).ι'.f 0 ≫
            ((CE.columnIso p).hom.f 0 ≫ (CE.doubleComplex.obj.X p).d 0 1) := by
              simp [Category.assoc]
      _ = (CE.columnResolution p).ι'.f 0 ≫
            ((CE.columnResolution p).cochainComplex.d 0 1 ≫
              (CE.columnIso p).hom.f 1) := by
              rw [hcomm]
      _ = ((CE.columnResolution p).ι'.f 0 ≫
            (CE.columnResolution p).cochainComplex.d 0 1) ≫
            (CE.columnIso p).hom.f 1 := by
              simp [Category.assoc]
      _ = 0 := by
              simp [(CE.columnResolution p).ι_f_zero_comp_complex_d, Category.assoc]
  -- Proof comment: the chosen column augmentation agrees with `CE.ε` in degree `0`.
  simpa [CE.columnAugmentation_f_zero p] using hcomp

/-- Helper for Lemma 13.21.3: every Cartan-Eilenberg column vanishes in negative vertical
degrees. -/
private theorem cartan_eilenberg_column_vanish_below_zero
    (p q : ℤ) (hq : q < 0) :
    IsZero ((CE.doubleComplex.obj.X p).X q) := by
  -- Proof comment: each column is identified with an injective resolution, hence is strictly
  -- nonnegative in the vertical direction.
  let _ : CochainComplex.IsStrictlyGE (CE.doubleComplex.obj.X p) 0 :=
    CE.vertical_isStrictlyGE p
  exact (CE.doubleComplex.obj.X p).isZero_of_isGE 0 q hq

/-- Helper for Lemma 13.21.3: every Cartan-Eilenberg column is exact in positive vertical
degrees. -/
private theorem cartan_eilenberg_column_exactAt_succ
    (p : ℤ) (q : ℕ) :
    (CE.doubleComplex.obj.X p).ExactAt (Int.ofNat (q + 1)) := by
  have hExactResolution :
      (CE.columnResolution p).cochainComplex.ExactAt (Int.ofNat (q + 1)) := by
    -- Proof comment: the extended `ℤ`-indexed injective resolution is quasi-isomorphic to the
    -- degree-zero single complex, so its positive-degree exactness is inherited from that single
    -- complex.
    rw [← quasiIsoAt_iff_exactAt
      (CE.columnResolution p).ι'
      (Int.ofNat (q + 1))
      (CochainComplex.exactAt_succ_single_obj (K.obj.X p) q)]
    infer_instance
  -- Proof comment: transport exactness across the chosen comparison between the resolution and
  -- the actual Cartan-Eilenberg column.
  exact hExactResolution.of_iso (CE.columnIso p).symm

/-- Helper for Lemma 13.21.3: evaluating the chosen image resolution at horizontal degree `p`
recovers the image of the fixed row differential landing in degree `q`. -/
private noncomputable theorem image_resolution_component_iso_to_row_image
    (p q : ℤ) :
    (((CE.imageResolution (q - 1)).cochainComplex).X p) ≅
      image (((CE.doubleComplex.obj.flip.X p).d (q - 1) q)) := by
  -- Proof comment: the chosen image resolution already identifies with the horizontal image
  -- complex `image (d₁^{q-1,q})`; evaluating that complex at degree `p` gives the image of the
  -- fixed-row differential by definition.
  simpa using
    (HomologicalComplex.eval 𝒜 (up ℤ) p).mapIso
      (CE.imageIso (q - 1))

/-- Helper for Lemma 13.21.3: evaluating the chosen cycles resolution at horizontal degree `p`
recovers the cycles of the fixed row in degree `q`. -/
private noncomputable theorem cycles_resolution_component_iso_to_row_cycles
    (p q : ℤ) :
    (((CE.cyclesResolution q).cochainComplex).X p) ≅
      ((CE.doubleComplex.obj.flip.X p).cycles q) := by
  -- Proof comment: `CE.cyclesIso q` identifies the whole cycles resolution with the horizontal
  -- cycles complex, and evaluation at `p` extracts the corresponding row cycles object.
  simpa using
    (HomologicalComplex.eval 𝒜 (up ℤ) p).mapIso
      (CE.cyclesIso q)

/-- Helper for Lemma 13.21.3: evaluating the chosen horizontal-homology resolution at horizontal
degree `p` recovers the homology of the fixed row in degree `q`. -/
private noncomputable theorem homology_resolution_component_iso_to_row_homology
    (p q : ℤ) :
    (((CE.homologyResolution q).cochainComplex).X p) ≅
      ((CE.doubleComplex.obj.flip.X p).homology q) := by
  -- Proof comment: `CE.homologyIso q` is already the canonical comparison with the horizontal
  -- homology complex, so evaluation immediately gives the rowwise homology object.
  simpa using
    (HomologicalComplex.eval 𝒜 (up ℤ) p).mapIso
      (CE.homologyIso q)

/-- Helper for Lemma 13.21.3: the second `E₁`-page object at `(p,q)` is `F` applied to the
`p`-th term of the horizontal-homology resolution `H_I^q(I^{\bullet,\bullet})`. -/
private noncomputable theorem mapped_row_homology_iso_to_homology_resolution_component
    (p q : ℤ) :
    ((((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
        CE.doubleComplex.obj).flip.X p).homology q ≅
      (((F.mapHomologicalComplex (up ℤ)).obj ((CE.homologyResolution q).cochainComplex)).X p) := by
  -- Proof comment: the source-faithful route is to compute the fixed-row homology using the
  -- split short exact sequences coming from the rows of the Cartan-Eilenberg resolution after
  -- applying `F`, and then transport along `CE.homologyIso q`.
  -- TODO: the objectwise transports from `CE.imageIso`, `CE.cyclesIso`, and `CE.homologyIso`
  -- are now packaged by
  -- `image_resolution_component_iso_to_row_image`,
  -- `cycles_resolution_component_iso_to_row_cycles`, and
  -- `homology_resolution_component_iso_to_row_homology`.
  -- It remains to identify the mapped row short complex with the mapped homology-resolution
  -- component using those transports and
  -- `ShortComplex.ShortExact.splittingOfInjective`.
  sorry

/-- Helper for Lemma 13.21.3: the fixed-`q` second `E₁` complex is the mapped horizontal-homology
resolution of `H^q(K^\bullet)`. -/
private noncomputable theorem second_page_one_complex_iso_to_mapped_homology_resolution
    (q : ℤ) :
    secondDoubleComplexPageOneComplex
        (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
          CE.doubleComplex.obj)
        q ≅
      ((F.mapHomologicalComplex (up ℤ)).obj ((CE.homologyResolution q).cochainComplex)) := by
  -- Proof comment: package the componentwise row-homology computation into an isomorphism of
  -- cochain complexes, then compare the differentials using
  -- `secondDoubleComplexPageOneDifferential_def`.
  -- TODO: turn the componentwise isomorphisms from
  -- `mapped_row_homology_iso_to_homology_resolution_component` into a chain isomorphism and check
  -- the signed differential compatibility.
  sorry

/-- Helper for Lemma 13.21.3: the second spectral sequence has `E₂`-page
`R^pF(H^q(K^\bullet))`. -/
private noncomputable theorem second_cartan_eilenberg_page_two_iso
    (E : CohomologicalSpectralSequence 𝒝 0)
    (hAssoc :
      IsAssociatedToFilteredComplex
        (secondDoubleComplexFilteredComplex
          (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
            CE.doubleComplex.obj))
        E)
    (p : ℕ) (q : ℤ) :
    (E.page 2).X (Int.ofNat p, q) ≅
      (F.rightDerived p).obj (K.obj.homology q) := by
  -- Proof comment: first rewrite the whole fixed-`q` `E''_1` complex into the mapped
  -- injective-resolution owner, then compute its homology in degree `p`.
  -- TODO: combine `E.iso 1 2 (Int.ofNat p, q)` with
  -- `second_page_one_complex_iso_to_mapped_homology_resolution q`, then use the already proved
  -- degree-zero and positive-degree injective-resolution computations on
  -- `CE.homologyResolution q`.
  let _ : IsAssociatedToFilteredComplex
      (secondDoubleComplexFilteredComplex
        (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
          CE.doubleComplex.obj))
      E := hAssoc
  sorry

/-- Helper for Lemma 13.21.3: the total Cartan-Eilenberg complex is quasi-isomorphic to the
original complex `K^\bullet`. -/
private theorem cartan_eilenberg_total_quasiIso :
    QuasiIso
      (doubleComplexZeroRowToTotal
        CE.ε
        (cartan_eilenberg_column_augmentation_cycles (K := K) (CE := CE))) := by
  refine zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
      (K := K.obj) (A := CE.doubleComplex.obj)
      (cartan_eilenberg_has_finite_antidiagonal_support (K := K) (CE := CE))
      ?_ ?_ CE.ε
      (cartan_eilenberg_column_augmentation_cycles (K := K) (CE := CE))
      ?_
  · intro p q hq
    exact cartan_eilenberg_column_vanish_below_zero (K := K) (CE := CE) p q hq
  · intro p q hq
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q by omega)
    cases n with
    | zero =>
        omega
    | succ n =>
        exact cartan_eilenberg_column_exactAt_succ (K := K) (CE := CE) p n
  · intro p
    -- Proof comment: the remaining source-facing step is to identify the degree-zero cycles of
    -- each column with `K^p` via the chosen column resolution and `CE.columnAugmentation_f_zero`.
    -- TODO: compare `doubleComplexZeroRowCyclesMap` with the kernel equivalence coming from
    -- `(CE.columnResolution p).isLimitKernelFork`, transported through `CE.columnIso p`.
    sorry

/-- Helper for Lemma 13.21.3: the common abutment `H^n(Tot(F(I^{\bullet,\bullet})))` agrees with
the bounded-below total right-derived value of `K^\bullet`. -/
private noncomputable theorem cartan_eilenberg_total_abutment_iso
    (n : ℤ) :
    (firstDoubleComplexFilteredComplex
        (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
          CE.doubleComplex.obj)).underlying.homology n ≅
      ((plusι ⋙ DerivedCategory.homologyFunctor 𝒝 n).obj
        ((Functor.totalRightDerived
            (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
            Qplus
            (boundedBelowHomotopyQuasiIso 𝒜)).obj
          ((Qhplus ⋙ Qplus).obj K))) := by
  -- Proof comment: once `K.obj ⟶ Tot(CE.doubleComplex.obj)` is recognized as a quasi-isomorphism,
  -- the abutment comparison should be reduced to the canonical bounded-below injective owner for
  -- `RF(K^\bullet)`.
  -- TODO: rewrite the filtered-total owner with `firstDoubleComplexFilteredComplex_underlying`,
  -- use `cartan_eilenberg_total_quasiIso` to replace `K.obj` by `Tot(CE.doubleComplex.obj)`, and
  -- then invoke `boundedBelowInjectiveComplex_computesRightDerivedFunctorAt` together with
  -- `Functor.computesRightDerivedAt_iff`.
  let _ := cartan_eilenberg_total_quasiIso (F := F) (K := K) (CE := CE)
  sorry

-- Proof sketch: let `I` be the canonical functorial image of the Cartan-Eilenberg double complex
-- under `((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ))`. Use the column
-- resolutions and horizontal-homology resolutions in `CE` to identify the first `E₁`-page with
-- the objectwise right derived functors `R^qF(K^p)` and the second `E₂`-page with
-- `R^pF(H^q(K^•))`. Apply the two spectral-sequence constructions for `I`; this directly
-- produces the two associated spectral sequences together with the page identifications,
-- boundedness, the finite filtrations on the abutment cohomology owned by the two canonical
-- filtered complexes, convergence to the cohomology of the total complex, and the canonical
-- comparison of that abutment with `H^*(RF(K^•))`.
/-- Lemma 13.21.3: let `F : 𝒜 ⥤ 𝒝` be a left exact functor of abelian categories, let `K^•` be
a bounded-below cochain complex of `𝒜`, and let `CE` be a Cartan-Eilenberg resolution of `K^•`.
Then the two spectral sequences associated to the double complex `F(I^{•,•})` can be packaged so
that `{}'E_1^{p,q} = R^qF(K^p)` and `{}''E_2^{p,q} = R^pF(H^q(K^•))`; both are bounded and both
converge to the cohomology of `Tot(F(I^{•,•}))`, together with canonical abutment isomorphisms
`H^n(Tot(F(I^{•,•}))) ≅ H^n(RF(K^•))`. The induced filtrations on the abutment cohomology are
finite, recorded separately by the canonical owner
`FilteredComplex.cohomologyFiltrationIsFinite`, while convergence itself is recorded by
`FilteredComplex.convergesToCohomology`. -/
theorem exists_cartanEilenberg_rightDerived_spectralSequences
    :
    let I :=
      ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₁ := firstDoubleComplexFilteredComplex I
    let FI₂ := secondDoubleComplexFilteredComplex I
    ∃ (firstSpectralSequence secondSpectralSequence : CohomologicalSpectralSequence 𝒝 0)
      (_ : IsAssociatedToFilteredComplex FI₁ firstSpectralSequence)
      (_ : IsAssociatedToFilteredComplex FI₂ secondSpectralSequence)
      (firstPageOneIso :
        ∀ (p : ℤ) (q : ℕ),
          (firstSpectralSequence.page 1).X (p, Int.ofNat q) ≅
            (F.rightDerived q).obj (K.obj.X p))
      (secondPageTwoIso :
        ∀ (p : ℕ) (q : ℤ),
          (secondSpectralSequence.page 2).X (Int.ofNat p, q) ≅
            (F.rightDerived p).obj (K.obj.homology q))
      (targetIso :
        ∀ n : ℤ,
          FI₁.underlying.homology n ≅
            ((plusι ⋙ DerivedCategory.homologyFunctor 𝒝 n).obj
              ((Functor.totalRightDerived
                  (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
                  Qplus
                  (boundedBelowHomotopyQuasiIso 𝒜)).obj
                ((Qhplus ⋙ Qplus).obj K)))),
      CohomologicalSpectralSequence.IsBounded firstSpectralSequence ∧
        FI₁.cohomologyFiltrationIsFinite ∧
        FI₁.convergesToCohomology firstSpectralSequence ∧
        CohomologicalSpectralSequence.IsBounded secondSpectralSequence ∧
        FI₂.cohomologyFiltrationIsFinite ∧
        FI₂.convergesToCohomology secondSpectralSequence := by
  let I :=
    ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
  let FI₁ := firstDoubleComplexFilteredComplex I
  let FI₂ := secondDoubleComplexFilteredComplex I
  have hmain :
      ∃ (firstSpectralSequence secondSpectralSequence : CohomologicalSpectralSequence 𝒝 0)
        (_ : IsAssociatedToFilteredComplex FI₁ firstSpectralSequence)
        (_ : IsAssociatedToFilteredComplex FI₂ secondSpectralSequence)
        (firstPageOneIso :
          ∀ (p : ℤ) (q : ℕ),
            (firstSpectralSequence.page 1).X (p, Int.ofNat q) ≅
              (F.rightDerived q).obj (K.obj.X p))
        (secondPageTwoIso :
          ∀ (p : ℕ) (q : ℤ),
            (secondSpectralSequence.page 2).X (Int.ofNat p, q) ≅
              (F.rightDerived p).obj (K.obj.homology q))
        (targetIso :
          ∀ n : ℤ,
            FI₁.underlying.homology n ≅
              ((plusι ⋙ DerivedCategory.homologyFunctor 𝒝 n).obj
                ((Functor.totalRightDerived
                    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
                    Qplus
                    (boundedBelowHomotopyQuasiIso 𝒜)).obj
                  ((Qhplus ⋙ Qplus).obj K)))),
        CohomologicalSpectralSequence.IsBounded firstSpectralSequence ∧
          FI₁.cohomologyFiltrationIsFinite ∧
          FI₁.convergesToCohomology firstSpectralSequence ∧
          CohomologicalSpectralSequence.IsBounded secondSpectralSequence ∧
          FI₂.cohomologyFiltrationIsFinite ∧
          FI₂.convergesToCohomology secondSpectralSequence := by
    obtain ⟨firstSpectralSequence, hFirstAssoc⟩ :=
      exists_filteredComplexAssociatedSpectralSequence FI₁
    obtain ⟨secondSpectralSequence, hSecondAssoc⟩ :=
      exists_filteredComplexAssociatedSpectralSequence FI₂
    letI : IsAssociatedToFilteredComplex FI₁ firstSpectralSequence := hFirstAssoc
    letI : IsAssociatedToFilteredComplex FI₂ secondSpectralSequence := hSecondAssoc
    have hfin : doubleComplexHasFiniteAntidiagonalSupport I :=
      mapped_cartan_eilenberg_has_finite_antidiagonal_support
        (F := F) (K := K) (CE := CE)
    refine ⟨firstSpectralSequence, secondSpectralSequence, hFirstAssoc, hSecondAssoc, ?_, ?_, ?_,
      ?_⟩
    · intro p q
      -- Proof comment: the first-page route is now split into the verified page-one-to-resolution
      -- prefix and the remaining injective-resolution computation bridge.
      exact
        (first_page_one_iso_to_mapped_column_resolution
          (F := F) (K := K) (CE := CE) firstSpectralSequence
          (by simpa [FI₁, I] using hFirstAssoc) p q) ≪≫
          (mapped_column_resolution_homology_iso_to_rightDerived
            (F := F) (K := K) (CE := CE) p q)
    · intro p q
      -- Proof comment: the rowwise `E''₂` computation is packaged separately so the main theorem
      -- only invokes the canonical fixed-`q` comparison once.
      exact
        second_cartan_eilenberg_page_two_iso
          (F := F) (K := K) (CE := CE) secondSpectralSequence
          (by simpa [FI₂, I] using hSecondAssoc) p q
    · intro n
      -- Proof comment: the abutment comparison is factored through the standalone total-complex
      -- bridge from `K^\bullet` to the bounded-below derived owner.
      exact cartan_eilenberg_total_abutment_iso (F := F) (K := K) (CE := CE) n
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [FI₁, I] using
          firstDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
            I firstSpectralSequence hfin
      · simpa [FI₁, I] using
          firstDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport I hfin
      · simpa [FI₁, I] using
          firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
            I firstSpectralSequence hfin
      · simpa [FI₂, I] using
          secondDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
            I secondSpectralSequence hfin
      · simpa [FI₂, I] using
          secondDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport I hfin
      · simpa [FI₂, I] using
          secondDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
            I secondSpectralSequence hfin
  simpa [I, FI₁, FI₂] using hmain

end

end
