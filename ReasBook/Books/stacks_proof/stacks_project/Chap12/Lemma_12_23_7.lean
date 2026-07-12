import Mathlib
import StacksProject_2024.Chap12.Definition_12_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat
open scoped CategoryTheory

noncomputable section

universe uR uM

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The pagewise equalities in equations `(12.23.5.2)` and `(12.23.5.1)` that characterize weak
convergence of the spectral sequence associated to a filtered differential module. -/
def weakConvergenceCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  ∀ p : ℤ,
    (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) =
        (LinearMap.range d ⊓ F p) ⊔ F (p + 1) ∧
      ((LinearMap.ker d ⊓ F p) ⊔ F (p + 1)) =
        ⨅ r : ℕ, (F p ⊓ Submodule.comap d (F (p + r))) ⊔ F (p + 1)

namespace Lemma12237Cohomology

/-- Helper for Lemma 12.23.7: the representative submodule
`(\ker d \cap F^p M) + \operatorname{im}(d)`. -/
abbrev representative (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (p : ℤ) :
    Submodule R M :=
  LinearMap.ker d ⊓ F p ⊔ LinearMap.range d

end Lemma12237Cohomology

/-- The intersection/union equalities of Lemma `12.23.7 (2)` for the filtration induced on
cohomology, expressed on the canonical representatives
`Lemma12237Cohomology.representative d F p` inside `M`. -/
def cohomologyFiltrationCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  (⨅ p : ℤ, Lemma12237Cohomology.representative d F p) =
      LinearMap.range d ∧
    (⨆ p : ℤ, Lemma12237Cohomology.representative d F p) =
      LinearMap.ker d

/-- Helper for Lemma 12.23.7: the subtype inclusion of a submodule defines a monomorphism in
`ModuleCat`. -/
private instance subtype_mono (S : Submodule R M) : Mono (ModuleCat.ofHom S.subtype) := by
  exact (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype S)

/-- Helper for Lemma 12.23.7: the inclusion map between submodules is a monomorphism in
`ModuleCat`. -/
private instance inclusion_mono {S T : Submodule R M} (h : S ≤ T) :
    Mono (ModuleCat.ofHom (Submodule.inclusion h)) := by
  refine (ModuleCat.mono_iff_injective _).2 ?_
  intro x y hxy
  apply Subtype.ext
  simpa using congrArg Subtype.val hxy

/-- Helper for Lemma 12.23.7: regard a submodule of `M` as the corresponding subobject of
`ModuleCat.of R M`. -/
private noncomputable abbrev toSubobject (S : Submodule R M) :
    Subobject (ModuleCat.of R M) :=
  Subobject.mk (ModuleCat.ofHom S.subtype)

/-- Helper for Lemma 12.23.7: inclusion of submodules induces inclusion of the corresponding
subobjects. -/
private theorem toSubobject_mono {S T : Submodule R M} (h : S ≤ T) :
    toSubobject S ≤ toSubobject T := by
  simpa [toSubobject, Category.assoc] using
    (Subobject.mk_le_mk_of_comm (ModuleCat.ofHom (Submodule.inclusion h)) (by
      ext x
      rfl) :
      Subobject.mk (ModuleCat.ofHom (Submodule.inclusion h) ≫ ModuleCat.ofHom T.subtype) ≤
        Subobject.mk (ModuleCat.ofHom T.subtype))

/-- Helper for Lemma 12.23.7: package a decreasing filtration of `M` as an object of
`Fil (ModuleCat R)`. -/
private def toFilteredObject (F : ℤ → Submodule R M) (hF : Antitone F) :
    Fil(ModuleCat.{uM} R) where
  obj := ModuleCat.of R M
  filtration :=
    { toFun := fun p ↦ toSubobject (F (OrderDual.ofDual p))
      monotone' := by
        intro p q hpq
        exact toSubobject_mono (R := R) (M := M) (hF hpq) }

variable [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)]

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- Helper for Lemma 12.23.7: in `ModuleCat`, the categorical image subobject of a morphism is
the linear-algebraic range of its underlying map. -/
private theorem subobjectModule_imageSubobject
    {X Y : ModuleCat.{uM} R} (f : X ⟶ Y) :
    ModuleCat.subobjectModule Y (imageSubobject f) = LinearMap.range f.hom := by
  have himage :
      imageSubobject f = Subobject.mk (ModuleCat.ofHom (LinearMap.range f.hom).subtype) := by
    exact CategoryTheory.Subobject.eq_mk_of_comm
      (ModuleCat.ofHom (LinearMap.range f.hom).subtype)
      ((imageSubobjectIso f).trans (ModuleCat.imageIsoRange f))
      (by simp [Category.assoc])
  rw [himage]
  exact (ModuleCat.subobjectModule Y).right_inv (LinearMap.range f.hom)

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- Helper for Lemma 12.23.7: the explicit subtype subobject attached to `S` recovers `S` under
`ModuleCat.subobjectModule`. -/
private theorem subobjectModule_toSubobject (S : Submodule R M) :
    ModuleCat.subobjectModule (ModuleCat.of R M) (toSubobject S) = S := by
  have hmono :
      imageSubobject (ModuleCat.ofHom S.subtype) = toSubobject S := by
    simpa [toSubobject] using (Limits.imageSubobject_mono (ModuleCat.ofHom S.subtype))
  rw [← hmono, subobjectModule_imageSubobject]
  simpa using Submodule.range_subtype S

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- Helper for Lemma 12.23.7: a differential preserving `S` factors through the corresponding
subobject of `ModuleCat.of R M`. -/
private theorem toSubobject_factors
    (d : M →ₗ[R] M) {S : Submodule R M} (hS : Submodule.map d S ≤ S) :
    (toSubobject S).Factors
      ((toSubobject S).arrow ≫ ModuleCat.ofHom d) := by
  have hmem : ∀ x : S, d x ∈ S := by
    intro x
    exact hS ⟨x, x.2, rfl⟩
  let g : S →ₗ[R] S := (d.domRestrict S).codRestrict S hmem
  let e := Subobject.underlyingIso (ModuleCat.ofHom S.subtype)
  change (Subobject.mk (ModuleCat.ofHom S.subtype)).Factors
      ((Subobject.mk (ModuleCat.ofHom S.subtype)).arrow ≫ ModuleCat.ofHom d)
  rw [Subobject.mk_factors_iff]
  refine ⟨e.hom ≫ ModuleCat.ofHom g, ?_⟩
  have hg :
      ModuleCat.ofHom g ≫ ModuleCat.ofHom S.subtype =
        ModuleCat.ofHom S.subtype ≫ ModuleCat.ofHom d := by
    ext x
    rfl
  calc
    e.hom ≫ ModuleCat.ofHom g ≫ ModuleCat.ofHom S.subtype =
        e.hom ≫ (ModuleCat.ofHom S.subtype ≫ ModuleCat.ofHom d) := by
          simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hg
    _ = (Subobject.mk (ModuleCat.ofHom S.subtype)).arrow ≫ ModuleCat.ofHom d := by
          rw [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for Lemma 12.23.7: a filtration-preserving endomorphism of `M` induces an endomorphism
of the packaged filtered object. -/
private def toFilteredEndomorphism
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) :
    toFilteredObject F hF ⟶ toFilteredObject F hF where
  hom := ModuleCat.ofHom d
  preserves := by
    intro p
    simpa [toFilteredObject] using toSubobject_factors d (hdF p)

/-- Helper for Lemma 12.23.7: package `(M, d, F)` as the corresponding one-object filtered
differential object. -/
private def toFilteredDifferentialObjectCore
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1}) where
  X := fun _ ↦ toFilteredObject F hF
  d := fun _ _ ↦ toFilteredEndomorphism d F hF hdF
  shape := by
    intro i j hij
    cases i
    cases j
    exact False.elim <| hij <| by simp
  d_comp_d' := by
    intro i j k _ _
    change toFilteredEndomorphism d F hF hdF ≫ toFilteredEndomorphism d F hF hdF = 0
    apply FilteredObject.Hom.ext
    ext x
    simpa [toFilteredEndomorphism] using LinearMap.congr_fun hd x

/-- Helper for Lemma 12.23.7: fix the instance arguments of
`toFilteredDifferentialObject` explicitly for the current section. -/
private abbrev packagedFilteredDifferentialObject
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1}) :=
  toFilteredDifferentialObjectCore d F hF hdF hd

/-- Helper for Lemma 12.23.7: a reducible name for the packaged one-object filtered differential
object. -/
private abbrev toFilteredDifferentialObjectAux
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1}) :=
  packagedFilteredDifferentialObject d F hF hdF hd

local notation "toFilteredDifferentialObject" =>
  (fun d F hF hdF hd ↦
    toFilteredDifferentialObjectAux (R := R) (M := M) d F hF hdF hd)

/-- Helper for Lemma 12.23.7: the source-facing weak-convergence criterion, generalized to an
arbitrary filtered `R`-module. -/
private def weakConvergenceCriterionFor
    {N : Type*} [AddCommGroup N] [Module R N]
    (d : N →ₗ[R] N) (F : ℤ → Submodule R N) : Prop :=
  ∀ p : ℤ,
    (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) =
        (LinearMap.range d ⊓ F p) ⊔ F (p + 1) ∧
      ((LinearMap.ker d ⊓ F p) ⊔ F (p + 1)) =
        ⨅ r : ℕ, (F p ⊓ Submodule.comap d (F (p + r))) ⊔ F (p + 1)

/-- Helper for Lemma 12.23.7: the source-facing separated/exhaustive criterion, generalized to an
arbitrary filtered `R`-module. -/
private def cohomologyFiltrationCriterionFor
    {N : Type*} [AddCommGroup N] [Module R N]
    (d : N →ₗ[R] N) (F : ℤ → Submodule R N) : Prop :=
  (⨅ p : ℤ, Lemma12237Cohomology.representative d F p) =
      LinearMap.range d ∧
    (⨆ p : ℤ, Lemma12237Cohomology.representative d F p) =
      LinearMap.ker d

/-- Helper for Lemma 12.23.7: the differential extracted from a one-object filtered differential
module in `ModuleCat R`. -/
private abbrev packagedDifferential
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) :
    (↥((K.X PUnit.unit).obj)) →ₗ[R] ↥((K.X PUnit.unit).obj) :=
  (K.d PUnit.unit PUnit.unit).hom.hom

/-- Helper for Lemma 12.23.7: the filtration extracted from the unique object of a one-object
filtered differential module in `ModuleCat R`. -/
private abbrev packagedFiltration
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) :
    ℤ → Submodule R ↥((K.X PUnit.unit).obj) :=
  fun p ↦ ModuleCat.subobjectModule _ ((K.X PUnit.unit).filtration.obj p)

/-- Helper for Lemma 12.23.7: weak convergence specialized to the packaged one-object filtered
differential module. -/
def weaklyConvergesToHomologyOwner
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) : Prop :=
  weakConvergenceCriterionFor (packagedDifferential K) (packagedFiltration K)

/-- Helper for Lemma 12.23.7: separatedness and exhaustiveness specialized to the packaged
one-object filtered differential module. -/
def inducedHomologyFiltrationSeparatedExhaustiveOwner
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) : Prop :=
  cohomologyFiltrationCriterionFor (packagedDifferential K) (packagedFiltration K)

/-- Helper for Lemma 12.23.7: abutment is weak convergence together with the concrete
cohomology-filtration criterion for the packaged one-object filtered differential module. -/
def abutsToHomologyOwner
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) : Prop :=
  weaklyConvergesToHomologyOwner K ∧ inducedHomologyFiltrationSeparatedExhaustiveOwner K

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- Helper for Lemma 12.23.7: unfold the local abutment predicate. -/
theorem abutsToHomology_iff_owner
    (K : HomologicalComplex (Fil(ModuleCat.{uM} R)) (ComplexShape.refl PUnit.{1})) :
    abutsToHomologyOwner K ↔
      weaklyConvergesToHomologyOwner K ∧ inducedHomologyFiltrationSeparatedExhaustiveOwner K :=
  Iff.rfl

local notation "weaklyConvergesToHomology" => weaklyConvergesToHomologyOwner (R := R)
local notation "inducedHomologyFiltrationSeparatedExhaustive" =>
  inducedHomologyFiltrationSeparatedExhaustiveOwner (R := R)
local notation "abutsToHomology" => abutsToHomologyOwner (R := R)

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- Helper for Lemma 12.23.7: extracting the packaged filtration recovers the original
filtration function `F`. -/
private theorem packagedFiltration_toFilteredDifferentialObject
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    packagedFiltration (toFilteredDifferentialObject d F hF hdF hd) = F := by
  funext p
  change ModuleCat.subobjectModule (ModuleCat.of R M) (toSubobject (F p)) = F p
  exact subobjectModule_toSubobject (R := R) (M := M) (F p)

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
-- Proof sketch: package `(M, d, F)` as the corresponding one-object filtered differential object
-- in `FilteredObject (ModuleCat R)`, then unfold the extracted weak-convergence predicate.
/-- Lemma 12.23.7 (1): for a filtered differential module, weak convergence of the associated
spectral sequence to cohomology is exactly the pair of pagewise equalities `(12.23.5.2)` and
`(12.23.5.1)`. The canonical owner predicate is
`HomologicalComplex.Filtered.weaklyConvergesToHomology`; the right-hand side records its module
theoretic criterion. -/
@[stacks 012J]
theorem weaklyConvergesToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weakConvergenceCriterion d F := by
  change
    weakConvergenceCriterionFor d
        (packagedFiltration (toFilteredDifferentialObject d F hF hdF hd)) ↔
      weakConvergenceCriterion d F
  rw [packagedFiltration_toFilteredDifferentialObject d F hF hdF hd]
  rfl

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
/-- The induced filtration on `H(M, d)` is separated and exhaustive exactly when the textbook
intersection/union criterion holds for the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    cohomologyFiltrationCriterion d F ↔
      inducedHomologyFiltrationSeparatedExhaustive
        (toFilteredDifferentialObject d F hF hdF hd) := by
  change
    cohomologyFiltrationCriterion d F ↔
      cohomologyFiltrationCriterionFor d
        (packagedFiltration (toFilteredDifferentialObject d F hF hdF hd))
  rw [packagedFiltration_toFilteredDifferentialObject d F hF hdF hd]
  rfl

omit [LocallySmall (ModuleCat.{uM} R)] [WellPowered (ModuleCat.{uM} R)]
  [HasWidePullbacks (ModuleCat.{uM} R)] [HasCoproducts (ModuleCat.{uM} R)]
  [InitialMonoClass (ModuleCat.{uM} R)] in
-- Proof sketch: the local abutment predicate is defined as weak convergence together with the
-- same concrete cohomology-filtration criterion recorded above.
/-- Lemma 12.23.7 (2): for a filtered differential module, the associated spectral sequence abuts
to cohomology exactly when it weakly converges and the induced cohomology filtration satisfies the
textbook intersection/union criterion on the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
@[stacks 012J]
theorem abutsToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    abutsToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ∧
        cohomologyFiltrationCriterion d F := by
  rw [abutsToHomology_iff_owner]
  exact and_congr_right fun _ ↦
    (cohomologyFiltrationCriterion_iff_separatedExhaustive d F hF hdF hd).symm

end
