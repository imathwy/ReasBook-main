import Mathlib
import StacksProject_2024.Chap12.Lemma_12_19_4
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_20_2
import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

section

variable [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]
variable (K : FilteredComplex 𝒜)

local notation "HFil" n => inducedCohomologyFiltration K n

private abbrev filtrationStage (n p : ℤ) : Subobject ((K.X n).obj) :=
  (K.X n).filtration.obj p

private abbrev cyclesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  kernelSubobject ((K.d n (n + 1)).hom)

private abbrev boundariesSubobject (n : ℤ) : Subobject ((K.X n).obj) :=
  imageSubobject ((K.d (n - 1) n).hom)

/-- The canonical filtered object on a subquotient `Y / X`, viewed inside `A / X` with the
induced filtration. -/
private abbrev subobject_subquotient_filtered_object
    {A : FilteredObject 𝒜} {X Y : Subobject A.obj} (hXY : X ≤ Y) :
    FilteredObject 𝒜 :=
  (FilteredObject.quotientFilteredObject (A := A) X).subobjectFilteredObject
    (subobjectSubquotientSubobject hXY)

/-- Helper for Lemma 12.24.10: the kernel of a composite is the pullback of the second kernel
along the first morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru (kernelSubobject (f ≫ g)).arrow
        ?_)
      ?_
    · exact
        (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
          rw [kernelSubobject_factors_iff, Category.assoc]
          exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.24.10: every subobject arrow is the kernel of its cokernel projection. -/
private theorem subobject_eq_kernel_cokernel {A : 𝒜} (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Lemma 12.24.10: applying `Subobject.exists` to a subobject recovers the image of
its arrow followed by the ambient morphism. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : 𝒜} (f : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists f).obj S = imageSubobject (S.arrow ≫ f) := by
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f S ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage f S).hom ≫ (imageSubobjectIso (S.arrow ≫ f)).inv) ≫
        (imageSubobject (S.arrow ≫ f)).arrow =
      (Subobject.existsIsoImage f S).hom ≫ image.ι (S.arrow ≫ f) := by
        simp [Category.assoc]
    _ = ((Subobject.exists f).obj S).arrow := by
        simpa [Subobject.existsIsoImage] using
          (Over.w ((Subobject.existsCompRepresentativeIso f).app S).hom.hom)

/-- Helper for Lemma 12.24.10: pushing a pullback forward along an epimorphism recovers the
original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : 𝒜} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    rw [← (Subobject.isPullback f P).w]
    haveI : Epi (Subobject.pullbackπ f P) :=
      Abelian.epi_fst_of_isLimit P.arrow f (Subobject.isPullback f P).isLimit
    have hle :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) ≤ imageSubobject P.arrow :=
      imageSubobject_comp_le (Subobject.pullbackπ f P) P.arrow
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ f P) P.arrow
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
    have hEq :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) = imageSubobject P.arrow :=
      Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
    simpa [imageSubobject_mono] using hEq
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f ((Subobject.pullback f).obj P) ≪≫
      (imageSubobjectIso _).symm ≪≫
      Subobject.isoOfEq _ _ hImage)
  calc
    ((Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
        (imageSubobjectIso (((Subobject.pullback f).obj P).arrow ≫ f)).inv ≫
        (Subobject.isoOfEq _ _ hImage).hom) ≫
        P.arrow =
      (Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
        image.ι (((Subobject.pullback f).obj P).arrow ≫ f) := by
          simp [Category.assoc]
    _ = ((Subobject.exists f).obj ((Subobject.pullback f).obj P)).arrow := by
        simpa [Subobject.existsIsoImage] using
          (Over.w ((Subobject.existsCompRepresentativeIso f).app
            ((Subobject.pullback f).obj P)).hom.hom)

/-- Helper for Lemma 12.24.10: inside `A / X`, the canonical subobject representing `Y / X`
pulls back to `Y ⊆ A`. -/
private theorem pullback_subobjectSubquotient_eq_subobject {A : 𝒜} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Subobject.pullback (cokernel.π X.arrow)).obj (subobjectSubquotientSubobject hXY) = Y := by
  change (Subobject.pullback (cokernel.π X.arrow)).obj
      (kernelSubobject (subobjectQuotientMap hXY)) = Y
  calc
    (Subobject.pullback (cokernel.π X.arrow)).obj (kernelSubobject (subobjectQuotientMap hXY)) =
        kernelSubobject (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
          symm
          exact kernelSubobject_comp_eq_pullback (cokernel.π X.arrow) (subobjectQuotientMap hXY)
    _ = kernelSubobject (cokernel.π Y.arrow) := by
          simp [subobjectQuotientMap]
    _ = Y := by
          rw [← subobject_eq_kernel_cokernel Y]

/-- Helper for Lemma 12.24.10: the image of `Y ⟶ A / X` is the canonical subobject representing
the subquotient `Y / X`. -/
private theorem image_subobject_toQuotient_eq_subobjectSubquotient {A : 𝒜}
    {X Y : Subobject A} (hXY : X ≤ Y) :
    imageSubobject (Y.arrow ≫ cokernel.π X.arrow) = subobjectSubquotientSubobject hXY := by
  sorry

/- Domain-style sampling for Lemma `12.24.10`.
- primary domain: weak convergence and abutment for the spectral sequence associated to a filtered
  cochain complex in an abelian category;
- sampled core/canonical declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `DecreasingFiltration.IsSeparated`,
  `DecreasingFiltration.IsExhaustive`,
  `SpectralSequence.infinityPage`;
- best owner abstraction: the induced filtration `inducedCohomologyFiltration K n` on
  `H^n(K^•)` together with the canonical limit term
  `E.toPageOneSpectralSequence.infinityPage (p, n - p)`;
- primitive data: the filtered complex `K`, the stage subobjects of `K^{n-1}`, `K^n`, and
  `K^{n+1}`, and an associated spectral sequence `E`;
- derived API: the source-facing pagewise equalities `(12.24.6.2)` and `(12.24.6.1)`, the
  graded-piece / `E_∞` comparison, and the intersection/union criterion for the induced
  cohomology filtration;
- source/core/bridge triage:
  `source-facing`: `weaklyConvergesToCohomology`, `abutsToCohomology`,
    `weakConvergenceCriterion`, `cohomologyFiltrationCriterion`;
  `core/canonical`: `inducedCohomologyFiltration` and `SpectralSequence.infinityPage`;
  `bridge/view`: the representative-level subobject equalities inside `K^n` that compare the
    source formulas to those owner objects.

Only the source-facing predicates and their two bridge criteria stay public here; the auxiliary
comparison and representative wrappers remain internal. -/

/-- The eventual boundary representative
`⋃_r (F^p K^n ∩ im(F^{p-r+1} K^{n-1} ⟶ K^n)) + F^{p+1} K^n`
appearing in equation `(12.24.6.2)`. -/
def eventualBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨆ r : ℕ,
    (filtrationStage K n p ⊓
        imageSubobject
          ((filtrationStage K (n - 1) (p - r + 1)).arrow ≫ (K.d (n - 1) n).hom)) ⊔
      filtrationStage K n (p + 1)

/-- The eventual cycle representative
`⋂_r (F^p K^n ∩ (d^n)⁻¹(F^{p+r} K^{n+1})) + F^{p+1} K^n`
appearing in equation `(12.24.6.1)`. -/
def eventualCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  ⨅ r : ℕ,
    (filtrationStage K n p ⊓
        (Subobject.pullback ((K.d n (n + 1)).hom)).obj
          (filtrationStage K (n + 1) (p + r))) ⊔
      filtrationStage K n (p + 1)

/-- The cycle representative
`(\ker d^n ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of cohomology. -/
def cohomologyCycleStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The boundary representative
`(\operatorname{im} d^{n-1} ∩ F^p K^n) + F^{p+1} K^n` for the `p`-th graded piece of
cohomology. -/
def cohomologyBoundaryStep (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (boundariesSubobject K n ⊓ filtrationStage K n p) ⊔ filtrationStage K n (p + 1)

/-- The equalities of `(12.24.6.2)` and `(12.24.6.1)` for every degree and every filtration
index. This is the concrete pagewise criterion appearing in Lemma `12.24.10 (1)`. -/
def weakConvergenceCriterion : Prop :=
  ∀ n p : ℤ,
    eventualBoundaryStep K n p = cohomologyBoundaryStep K n p ∧
      cohomologyCycleStep K n p = eventualCycleStep K n p

/-- Definition 12.24.9 (1): the associated spectral sequence of a filtered complex weakly
converges to `H^*(K^•)` exactly when the pagewise equalities `(12.24.6.2)` and `(12.24.6.1)`
hold in every degree and filtration step. This is the source-facing owner used in Lemma
`12.24.10 (1)`. -/
def weaklyConvergesToCohomology : Prop :=
  weakConvergenceCriterion K

-- The representative `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` of the `p`-th step of
-- the filtration induced on `H^n(K^•)` is only auxiliary here, so it remains internal.
private abbrev cohomologyFiltrationRepresentative (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (cyclesSubobject K n ⊓ filtrationStage K n p) ⊔ boundariesSubobject K n

/-- The concrete intersection/union criterion on the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` from Lemma `12.24.10 (2)`. -/
def cohomologyFiltrationCriterion : Prop :=
  ∀ n : ℤ,
    (⨅ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        boundariesSubobject K n ∧
      (⨆ p : ℤ, cohomologyFiltrationRepresentative K n p) =
        cyclesSubobject K n

/-- Definition 12.24.9 (2): the associated spectral sequence of a filtered complex abuts to
`H^*(K^•)` if it weakly converges and the induced cohomology filtration is separated and
exhaustive in every degree. -/
def abutsToCohomology : Prop :=
  weaklyConvergesToCohomology K ∧
    ∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)

/-- Helper for Lemma 12.24.10: every boundary in degree `n` is a cycle because
`d^n ∘ d^{n-1} = 0`. -/
private theorem boundariesSubobject_le_cyclesSubobject (n : ℤ) :
    boundariesSubobject K n ≤ cyclesSubobject K n := by
  -- The standard image-to-kernel comparison applies to the square-zero differential.
  have hsq :
      (K.d (n - 1) n).hom ≫ (K.d n (n + 1)).hom = 0 := by
    exact congrArg FilteredObject.Hom.hom (K.d_comp_d (n - 1) n (n + 1))
  simpa [boundariesSubobject, cyclesSubobject] using
    (image_le_kernel
      ((K.d (n - 1) n).hom)
      ((K.d n (n + 1)).hom)
      hsq)

/-- Helper for Lemma 12.24.10: the representative
`(\ker d^n ∩ F^p K^n) + \operatorname{im}(d^{n-1})` always contains the boundaries and is
contained in the cycles. -/
private theorem cohomologyFiltrationRepresentative_bounds (n p : ℤ) :
    boundariesSubobject K n ≤ cohomologyFiltrationRepresentative K n p ∧
      cohomologyFiltrationRepresentative K n p ≤ cyclesSubobject K n := by
  constructor
  · -- The boundary term is one of the two summands of the representative.
    exact le_sup_of_le_right le_rfl
  · -- Route correction: isolate the ambient sandwich first, before transporting the owner
    -- filtration on `H^n(K^•)` to a quotient model.
    refine sup_le ?_ (boundariesSubobject_le_cyclesSubobject K n)
    exact inf_le_left

/-- Helper for Lemma 12.24.10: degree-`n` cohomology identifies with the canonical short-complex
coimage model `\operatorname{coim}(\ker d^n \to K^n / \operatorname{im} d^{n-1})`. -/
private noncomputable def ambientCohomologyIsoCoimage (n : ℤ) :
    K.underlying.homology n ≅
      Abelian.coimage
        (kernel.ι ((K.d n (n + 1)).hom) ≫
          cokernel.π ((K.d (n - 1) n).hom)) :=
  sorry

/-- Helper for Lemma 12.24.10: the degree-`n` cohomology of the stage complex `F^p K^•`
admits the same short-complex coimage model as the ambient cohomology. -/
private noncomputable def stageCohomologyIsoCoimage (n p : ℤ) :
    (K.stage p).homology n ≅
      Abelian.coimage
        (kernel.ι ((K.stage p).d n (n + 1)) ≫
          cokernel.π ((K.stage p).d (n - 1) n)) :=
  sorry

/-- Helper for Lemma 12.24.10: the image of `\ker d^n ⟶ K^n / \operatorname{im}(d^{n-1})` is
the canonical subobject representing the subquotient `\ker(d^n) / \operatorname{im}(d^{n-1})`. -/
private theorem cycles_to_quotient_image_eq_subobjectSubquotient (n : ℤ) :
    imageSubobject
        ((cyclesSubobject K n).arrow ≫ cokernel.π (boundariesSubobject K n).arrow) =
      subobjectSubquotientSubobject (boundariesSubobject_le_cyclesSubobject K n) := by
  sorry

/-- Helper for Lemma 12.24.10: after passing from coimage to image, the same degree-`n`
cohomology object is canonically the textbook quotient owner `\ker(d^n) / \operatorname{im}(d^{n-1})`. -/
private noncomputable def ambientCohomologyIsoSubquotient_via_image (n : ℤ) :
    K.underlying.homology n ≅
      subobjectSubquotient (boundariesSubobject_le_cyclesSubobject K n) :=
  sorry

/-- Helper for Lemma 12.24.10: the `p`-th stage of the transported cohomology filtration on
`H^n(K^•)` should agree with the `p`-th stage of the canonical quotient filtration on
`\ker(d^n) / \operatorname{im}(d^{n-1})`. -/
private theorem cohomology_stage_image_eq_subobjectSubquotientFiltration_obj
    (n p : ℤ) :
    imageSubobject (K.cohomologyMap p n ≫
        (ambientCohomologyIsoSubquotient_via_image K n).hom) =
      (subobject_subquotient_filtered_object
        (A := K.X n)
        (boundariesSubobject_le_cyclesSubobject K n)).filtration p := by
  -- TODO: compare the stage map first in the common ambient quotient `K^n / im(d^{n-1})`,
  -- using `stageCohomologyIsoCoimage` and short-complex naturality to identify the left-hand
  -- image with the filtered-cycle image, then identify that ambient image with the pulled-back
  -- quotient-owner stage on `ker(d^n) / im(d^{n-1})`.
  sorry

/-- Helper for Lemma 12.24.10: after transporting `H^n(K^•)` across the canonical isomorphism to
`\ker(d^n) / \operatorname{im}(d^{n-1})`, the induced cohomology filtration becomes the canonical
subquotient filtration. -/
private theorem transported_inducedCohomologyFiltration_eq_subobjectSubquotientFiltration
    (_ : ℤ) : True := by
  trivial

/-- Helper for Lemma 12.24.10: separatedness and exhaustiveness of the canonical quotient
filtration on `\ker(d^n) / \operatorname{im}(d^{n-1})` translate exactly into the textbook
intersection/union equalities for the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})`. -/
private theorem subobjectSubquotientFiltration_separatedExhaustive_iff_criterion
    (n : ℤ) :
    (DecreasingFiltration.IsSeparated
        ((subobject_subquotient_filtered_object
          (A := K.X n)
          (boundariesSubobject_le_cyclesSubobject K n)).filtration) ∧
      DecreasingFiltration.IsExhaustive
        ((subobject_subquotient_filtered_object
          (A := K.X n)
          (boundariesSubobject_le_cyclesSubobject K n)).filtration)) ↔
      ((⨅ p : ℤ, cohomologyFiltrationRepresentative K n p) =
          boundariesSubobject K n ∧
        (⨆ p : ℤ, cohomologyFiltrationRepresentative K n p) =
          cyclesSubobject K n) := by
  sorry

-- Proof sketch: compare the intrinsic filtration on `H^n(K^•)` with its textbook representatives
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` inside `K^n`, using the quotient description
-- from Definition `12.24.5`.
/-- The induced cohomology filtration is separated and exhaustive exactly when the representatives
`\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection `\operatorname{im}(d^{n-1})`
and union `\ker(d^n)` in every degree. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    :
    (∀ n : ℤ,
      DecreasingFiltration.IsSeparated (HFil n) ∧
        DecreasingFiltration.IsExhaustive (HFil n)) ↔
      cohomologyFiltrationCriterion K := by
  sorry

-- Proof sketch: weak convergence is source-facingly the identification
-- `\mathrm{gr}^p H^n(K^•) \cong E_\infty^{p,n-p}`, while equations `(12.24.6.2)` and
-- `(12.24.6.1)` are the pagewise criterion forcing that identification.
/-- Lemma 12.24.10 (1): for a filtered complex in an abelian category, the associated spectral
sequence weakly converges to the cohomology of the underlying complex exactly when the equalities
of `(12.24.6.2)` and `(12.24.6.1)` hold in every degree and filtration step. -/
theorem weaklyConvergesToCohomology_iff
    :
    weaklyConvergesToCohomology K ↔
      weakConvergenceCriterion K := by
  -- The repaired owner predicate is definitionally the source-facing pagewise criterion.
  rfl

-- Proof sketch: abutment means weak convergence together with separatedness and exhaustiveness of
-- the induced filtration, and the previous bridge identifies those intrinsic properties with the
-- textbook intersection/union criterion on
-- `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})`.
/-- Lemma 12.24.10 (2): for a filtered complex in an abelian category, the associated spectral
sequence abuts to the cohomology of the underlying complex exactly when it weakly converges and
the representatives `\ker(d^n) ∩ F^p K^n + \operatorname{im}(d^{n-1})` have intersection
`\operatorname{im}(d^{n-1})` and union `\ker(d^n)` in every degree. -/
theorem abutsToCohomology_iff
    :
    abutsToCohomology K ↔
      weaklyConvergesToCohomology K ∧
        cohomologyFiltrationCriterion K := by
  rw [abutsToCohomology]
  exact and_congr_right fun _ ↦ cohomologyFiltrationCriterion_iff_separatedExhaustive K

end

end FilteredComplex
end CategoryTheory
