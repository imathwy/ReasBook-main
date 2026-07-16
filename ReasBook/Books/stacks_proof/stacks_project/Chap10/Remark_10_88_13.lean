import Mathlib
import Mathlib.Algebra.Module.Presentation.Tautological
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import stacks_proof.stacks_project.Chap10.Definition_10_88_7
import stacks_proof.stacks_project.Chap10.Lemma_10_36_23
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.TensorDomination
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.HomMittagLeffler
import stacks_proof.stacks_project.Chap10.Proposition_10_89_3
import stacks_proof.stacks_project.Chap10.Lemma_10_94_1
import stacks_proof.stacks_project.Chap10.Example_10_91_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Pointwise TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]

local instance (M : ModuleCat.{w} (DualNumber R)) : Module R M :=
  Module.compHom M (algebraMap R (DualNumber R))

/-- Helper for Chap10 Remark 10 88 13: the presentation endomorphism
`(a, b) ↦ (0, ρ a)` on `F₁ × F₀` is square-zero. -/
private lemma presentationEndomorphism_comp_self_eq_zero
    {F₁ F₀ : Type v} [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]
    (ρ : F₁ →ₗ[R] F₀) :
    ((LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))).comp
        ((LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))) =
      (0 : F₁ × F₀ →ₗ[R] F₁ × F₀) := by
  -- The first application lands in the right summand, so the second application reads zero from
  -- the left projection.
  ext x <;> simp [LinearMap.comp_apply]

/-- Helper for Chap10 Remark 10 88 13: a square-zero endomorphism of an `R`-module satisfies the
side conditions needed by `DualNumber.lift` into `Module.End R X`. -/
private lemma squareZeroEndomorphism_liftData
    {X : Type v} [AddCommGroup X] [Module R X] (e : Module.End R X) (he : e.comp e = 0) :
    e * e = 0 ∧ ∀ r : R, Commute e ((Algebra.ofId R (Module.End R X)) r) := by
  -- Multiplication in `Module.End` is composition; scalar endomorphisms commute with every
  -- endomorphism over a commutative base ring.
  constructor
  · simpa [Module.End.mul_eq_comp] using he
  · intro r
    exact Algebra.commute_algebraMap_right r e

/-- Helper for Chap10 Remark 10 88 13: a square-zero `R`-linear endomorphism defines the
corresponding dual-number module structure. -/
@[reducible]
private def dualNumberModuleOfSquareZero
    {X : Type v} [AddCommGroup X] [Module R X] (e : Module.End R X) (he : e.comp e = 0) :
    Module (DualNumber R) X :=
  Module.compHom X (DualNumber.lift ⟨(Algebra.ofId R (Module.End R X), e),
    squareZeroEndomorphism_liftData e he⟩).toRingHom

/-- Helper for Chap10 Remark 10 88 13: in the square-zero dual-number module, `ε` acts by the
chosen endomorphism. -/
private lemma dualNumberModuleOfSquareZero_eps_smul
    {X : Type v} [AddCommGroup X] [Module R X] (e : Module.End R X) (he : e.comp e = 0)
    (x : X) :
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    (DualNumber.eps : DualNumber R) • x = e x := by
  -- Unfold the induced action only to the `Module.End` level, then use the `DualNumber.lift`
  -- computation rule for `ε`.
  change ((DualNumber.lift ⟨(Algebra.ofId R (Module.End R X), e),
    squareZeroEndomorphism_liftData e he⟩).toRingHom (DualNumber.eps) : Module.End R X) x = e x
  simp

/-- Helper for Chap10 Remark 10 88 13: in the square-zero dual-number module, base scalars act by
the original `R`-module structure. -/
private lemma dualNumberModuleOfSquareZero_inl_smul
    {X : Type v} [AddCommGroup X] [Module R X] (e : Module.End R X) (he : e.comp e = 0)
    (r : R) (x : X) :
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    (TrivSqZeroExt.inl r : DualNumber R) • x = r • x := by
  -- The same induced-action normalization reduces base scalars to the algebra map into
  -- `Module.End R X`.
  change ((DualNumber.lift ⟨(Algebra.ofId R (Module.End R X), e),
    squareZeroEndomorphism_liftData e he⟩).toRingHom (TrivSqZeroExt.inl r) :
      Module.End R X) x = r • x
  simp [Module.algebraMap_end_apply]

/-- Helper for Chap10 Remark 10 88 13: the square-zero dual-number action extends the original
`R`-module structure, so restriction of scalars along `R → DualNumber R` forms a scalar tower. -/
private lemma dualNumberModuleOfSquareZero_isScalarTower
    {X : Type v} [AddCommGroup X] [Module R X] (e : Module.End R X) (he : e.comp e = 0) :
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    IsScalarTower R (DualNumber R) X := by
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  -- The induced `DualNumber R`-action restricts to the original `R`-action on the nose.
  exact IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa using dualNumberModuleOfSquareZero_inl_smul (R := R) e he r x

/-- Helper for Chap10 Remark 10 88 13: a split summand of a Mittag-Leffler module is
Mittag-Leffler. -/
private theorem mittagLefflerOfSplit
    {P : Type v} {N : Type w} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [MittagLeffler R N] (i : P →ₗ[R] N) (p : N →ₗ[R] P) (hp : p.comp i = LinearMap.id) :
    MittagLeffler R P := by
  -- Compare the tensor-product injectivity test after tensoring the split inclusion and
  -- projection.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective (R := R) (M := P)).2 ?_
  intro (A : Type (max v w)) (Q : A → Type (max v w)) _ _
  have hN : Function.Injective (TensorProduct.piRightHom R R N Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1
      (inferInstance : MittagLeffler R N)) A Q
  have hsplit_tensor :
      (p.rTensor (∀ a, Q a)).comp (i.rTensor (∀ a, Q a)) = LinearMap.id := by
    -- Tensoring preserves the retraction identity.
    rw [← LinearMap.rTensor_comp, hp, LinearMap.rTensor_id]
  have hi_tensor : Function.Injective (i.rTensor (∀ a, Q a)) :=
    LinearMap.injective_of_comp_eq_id _ _ hsplit_tensor
  intro x y hxy
  apply hi_tensor
  apply hN
  rw [piRightHom_rTensor_apply_linear i x, piRightHom_rTensor_apply_linear i y, hxy]

/-- Helper for Chap10 Remark 10 88 13: the Mittag-Leffler property transports backward along a
linear equivalence. -/
private theorem mittagLefflerOfLinearEquiv
    {P : Type v} {N : Type w} [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [MittagLeffler R N] (e : P ≃ₗ[R] N) :
    MittagLeffler R P := by
  -- A linear equivalence exhibits the source as a split summand of the target.
  refine mittagLefflerOfSplit (R := R) e.toLinearMap e.symm.toLinearMap ?_
  ext x
  simp

/-- Helper for Chap10 Remark 10 88 13: every free module is Mittag-Leffler. -/
private theorem mittagLefflerOfFree
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Free R N] :
    MittagLeffler R N := by
  -- Reuse the projective/free bridge already proved earlier in the chapter.
  exact Module.mittagLeffler_of_free N

/-- Helper for Chap10 Remark 10 88 13: the right summand inclusion into a product is split by the
second projection. -/
private lemma snd_comp_inr_eq_id
    {F₁ : Type w} {F₂ : Type v} [AddCommGroup F₁] [Module R F₁]
    [AddCommGroup F₂] [Module R F₂] :
    (LinearMap.snd R F₁ F₂).comp (LinearMap.inr R F₁ F₂) = LinearMap.id := by
  -- Check the retraction identity componentwise on the product coordinates.
  ext x
  simp

/-- Helper for Chap10 Remark 10 88 13: a product module being Mittag-Leffler forces its second
factor to be Mittag-Leffler, because the second factor is a split summand. -/
private theorem mittagLeffler_of_prod_right
    {F : Type w} {M : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (hFM : MittagLeffler R (F × M)) :
    MittagLeffler R M := by
  -- Retract from `F × M` onto `M` using the standard inclusion/projection pair.
  letI : MittagLeffler R (F × M) := hFM
  exact mittagLefflerOfSplit (R := R) (P := M) (N := F × M)
    (LinearMap.inr R F M) (LinearMap.snd R F M) snd_comp_inr_eq_id

/-- Helper for Chap10 Remark 10 88 13: the quotient submodule `I • ⊤` attached to an ideal action
on a module. Naming it keeps later quotient statements in a stable normal form. -/
private abbrev idealSmulTopSubmodule {S : Type*} [CommSemiring S]
    {X : Type*} [AddCommMonoid X] [Module S X] (I : Ideal S) : Submodule S X :=
  I • (⊤ : Submodule S X)

/-- Helper for Chap10 Remark 10 88 13: the principal ideal `(ε)` in `DualNumber R` is the kernel
of the projection `TrivSqZeroExt.fstHom R R R : DualNumber R →ₐ[R] R`. -/
private lemma dualNumberSpanEps_eq_kerFstHom :
    Ideal.span ({DualNumber.eps} : Set (DualNumber R)) =
      RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom := by
  -- Compare both ideals by their elementwise membership conditions.
  ext x
  rw [Ideal.mem_span_singleton', RingHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    simp [TrivSqZeroExt.fstHom]
  · intro hx
    have hx' : x.fst = 0 := by
      simpa [TrivSqZeroExt.fstHom] using hx
    rcases (DualNumber.fst_eq_zero_iff_eps_dvd (x := x)).mp hx' with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [mul_comm] using ha.symm

/-- Helper for Chap10 Remark 10 88 13: the square-zero dual-number module is Mittag-Leffler over
`R` on its carrier because the underlying `R`-module remains the original free module. -/
private theorem dualNumberModuleOfSquareZero_mittagLefflerOverBase
    {X : Type w} [AddCommGroup X] [Module R X] [Module.Free R X]
    (e : Module.End R X) (he : e.comp e = 0) :
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    MittagLeffler R X := by
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  -- Route correction: work on the carrier `X` directly so the final theorem does not need a
  -- bundled/unbundled transport across `ModuleCat.of`.
  exact mittagLefflerOfFree (R := R) X

/- The quotient argument below works on the presentation map
`φ : F₁ × F₀ → F₁ × M₀`, with the `ε`-multiple submodule identified through the explicit formula
for the square-zero action. -/

/-- Helper for Chap10 Remark 10 88 13: in the square-zero presentation module, the `ε`-multiple
submodule consists exactly of pairs whose first coordinate is `0` and whose second coordinate lies
in `LinearMap.range ρ`. -/
private lemma mem_presentationIdealSmulTop_iff
    {F₁ F₀ : Type v} [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]
    (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    let X := F₁ × F₀
    let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
    let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
    x ∈ J ↔ x.1 = 0 ∧ x.2 ∈ LinearMap.range ρ := by
  let X := F₁ × F₀
  let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
  let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
  change x ∈ J ↔ x.1 = 0 ∧ x.2 ∈ LinearMap.range ρ
  constructor
  · intro hx
    -- Normalize membership in the ideal multiple to an explicit witness `y` with `ε • y = x`.
    have hx' : x ∈ I • (⊤ : Submodule (DualNumber R) X) := by
      simpa [J, idealSmulTopSubmodule] using hx
    have hx'' :
        x ∈ Ideal.span ({DualNumber.eps} : Set (DualNumber R)) •
          (⊤ : Submodule (DualNumber R) X) := by
      simpa [I] using hx'
    rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
      Submodule.map_top, LinearMap.mem_range] at hx''
    rcases hx'' with ⟨y, hy⟩
    have hyEps : (DualNumber.eps : DualNumber R) • y = (0, ρ y.1) := by
      simpa [e, LinearMap.comp_apply] using
        dualNumberModuleOfSquareZero_eps_smul (R := R) e he y
    have hxy : x = (0, ρ y.1) := hy.symm.trans hyEps
    constructor
    · simpa [hxy]
    · exact ⟨y.1, by simpa [hxy]⟩
  · rintro ⟨hx₁, hx₂⟩
    rcases hx₂ with ⟨y, hy⟩
    have hyEps : (DualNumber.eps : DualNumber R) • (y, (0 : F₀)) = (0, ρ y) := by
      simpa [e, LinearMap.comp_apply] using
        dualNumberModuleOfSquareZero_eps_smul (R := R) e he (y, (0 : F₀))
    -- Build the quotient witness from the representative `(y, 0)`.
    have hx' : x ∈ I • (⊤ : Submodule (DualNumber R) X) := by
      have hx'' :
          x ∈ Ideal.span ({DualNumber.eps} : Set (DualNumber R)) •
            (⊤ : Submodule (DualNumber R) X) := by
        rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
          Submodule.map_top, LinearMap.mem_range]
        refine ⟨(y, (0 : F₀)), ?_⟩
        exact hyEps.trans (Prod.ext hx₁.symm hy)
      simpa [I] using hx''
    simpa [J, idealSmulTopSubmodule] using hx'

/-- Helper for Chap10 Remark 10 88 13: the submodule generated by the ideal `(ε)` agrees with the
canonical `ε • ⊤` submodule used by `QuotSMulTop`. -/
private lemma squareZeroIdealSmulTop_eq_epsSmulTop
    {X : Type w} [AddCommGroup X] [Module (DualNumber R) X] :
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    idealSmulTopSubmodule (S := DualNumber R) (X := X) I =
      (DualNumber.eps : DualNumber R) • (⊤ : Submodule (DualNumber R) X) := by
  -- Normalize the ideal-generated submodule to the owner spelling used by `QuotSMulTop`.
  simp [idealSmulTopSubmodule, Submodule.ideal_span_singleton_smul]

/-- Helper for Chap10 Remark 10 88 13: the raw square-zero quotient is the canonical
`QuotSMulTop (DualNumber.eps : DualNumber R) X`. -/
private noncomputable def squareZeroQuotientEquivQuotSmulTop
    {X : Type w} [AddCommGroup X] [Module (DualNumber R) X] :
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    (X ⧸ idealSmulTopSubmodule (S := DualNumber R) (X := X) I) ≃ₗ[DualNumber R]
      QuotSMulTop (DualNumber.eps : DualNumber R) X := by
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  let hJ :
      idealSmulTopSubmodule (S := DualNumber R) (X := X) I =
        (DualNumber.eps : DualNumber R) • (⊤ : Submodule (DualNumber R) X) :=
    squareZeroIdealSmulTop_eq_epsSmulTop (R := R) (X := X)
  -- Transport quotient modules across the single stabilized submodule equality.
  exact Submodule.quotEquivOfEq _ _ hJ

/-- Helper for Chap10 Remark 10 88 13: viewing a quotient by a `DualNumber R`-submodule as an
`R`-module via `Module.compHom` agrees with quotienting by the restricted-scalar submodule. -/
private noncomputable abbrev quotientRestrictScalarsCompHomEquiv
    {X : Type w} [AddCommGroup X] [Module (DualNumber R) X]
    (P : Submodule (DualNumber R) X) :
    letI : Module R X := Module.compHom X (algebraMap R (DualNumber R))
    letI : IsScalarTower R (DualNumber R) X := IsScalarTower.of_compHom R (DualNumber R) X
    let Q := X ⧸ P.restrictScalars R
    let QDual := X ⧸ P
    letI : Module R QDual := Module.compHom QDual (algebraMap R (DualNumber R))
    Q ≃ₗ[R] QDual :=
  letI : Module R X := Module.compHom X (algebraMap R (DualNumber R))
  letI : IsScalarTower R (DualNumber R) X := IsScalarTower.of_compHom R (DualNumber R) X
  -- Use the owner quotient comparison instead of rebuilding the identity map by hand.
  Submodule.Quotient.restrictScalarsEquiv R P

/- The product quotient is governed by the tautological presentation map
`φ : F₁ × F₀ → F₁ × M₀`; its kernel is exactly the `ε`-multiple submodule. -/

/-- Helper for Chap10 Remark 10 88 13: the kernel of the tautological product map is exactly the
`ε`-multiple submodule in the square-zero presentation module. -/
private lemma presentationMap_ker_eq_presentationIdealSmulTop
    (M₀ : ModuleCat.{v} R) :
    let pres := Module.Presentation.tautological R M₀
    let F₁ := pres.R →₀ R
    let F₀ := pres.G →₀ R
    let ρ : F₁ →ₗ[R] F₀ := pres.map
    let X := F₁ × F₀
    let φ : X →ₗ[R] (F₁ × ↑M₀) :=
      (LinearMap.fst R F₁ F₀).prod (pres.π.comp (LinearMap.snd R F₁ F₀))
    let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
    let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
      (R := R) e he
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
    LinearMap.ker φ = J.restrictScalars R := by
  let pres := Module.Presentation.tautological R M₀
  let F₁ := pres.R →₀ R
  let F₀ := pres.G →₀ R
  let ρ : F₁ →ₗ[R] F₀ := pres.map
  let X := F₁ × F₀
  let φ : X →ₗ[R] (F₁ × ↑M₀) :=
    (LinearMap.fst R F₁ F₀).prod (pres.π.comp (LinearMap.snd R F₁ F₀))
  let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
  let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
    (R := R) e he
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
  -- Compare kernel membership with the explicit description of the `ε`-multiple submodule.
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hx₁ : x.1 = 0 := by
      simpa [φ, LinearMap.comp_apply] using congrArg Prod.fst hx
    have hxπ : pres.π x.2 = 0 := by
      simpa [φ, LinearMap.comp_apply] using congrArg Prod.snd hx
    have hx₂ker : x.2 ∈ LinearMap.ker pres.π := by
      rwa [LinearMap.mem_ker]
    have hx₂ : x.2 ∈ LinearMap.range ρ := by
      change x.2 ∈ LinearMap.range pres.map
      rw [pres.range_map, ← pres.ker_π]
      exact hx₂ker
    have hxJ : x ∈ J := (mem_presentationIdealSmulTop_iff (R := R) ρ x).2 ⟨hx₁, hx₂⟩
    simpa using hxJ
  · intro hx
    have hxJ : x ∈ J := by
      simpa using hx
    rcases (mem_presentationIdealSmulTop_iff (R := R) ρ x).1 hxJ with ⟨hx₁, hx₂⟩
    rw [LinearMap.mem_ker]
    refine Prod.ext ?_ ?_
    · simpa [φ, LinearMap.comp_apply] using hx₁
    · have hxπ : pres.π x.2 = 0 := by
        have hx₂' := hx₂
        change x.2 ∈ LinearMap.range pres.map at hx₂'
        have hx₂ker : x.2 ∈ LinearMap.ker pres.π := by
          rw [pres.ker_π, ← pres.range_map]
          exact hx₂'
        rwa [LinearMap.mem_ker] at hx₂ker
      simpa [φ, LinearMap.comp_apply, hxπ]

/- Source/core/bridge triage:
* source-facing: existence of a dual-number counterexample to ascent for the Mittag-Leffler
  property.
* core/canonical: the chapter owner `Module.MittagLeffler` on the underlying module carrier of a
  bundled `ModuleCat`.
* bridge/view: the induced `R`-module structure on a `DualNumber R`-module via restriction of
  scalars along `algebraMap R (DualNumber R)`.
-/

/-- Helper for Chap10 Remark 10 88 13: quotienting the square-zero presentation module by the
`ε`-multiple submodule admits an `R`-linear identification with `F₁ × M₀`. -/
private theorem presentationTensorQuotientEquivProdExists
    (M₀ : ModuleCat.{v} R) :
    let pres := Module.Presentation.tautological R M₀
    let F₁ := pres.R →₀ R
    let F₀ := pres.G →₀ R
    let ρ : F₁ →ₗ[R] F₀ := pres.map
    let X := F₁ × F₀
    let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
    let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
      (R := R) e he
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
    Nonempty ((X ⧸ J.restrictScalars R) ≃ₗ[R] (F₁ × ↑M₀)) := by
  let pres := Module.Presentation.tautological R M₀
  let F₁ := pres.R →₀ R
  let F₀ := pres.G →₀ R
  let ρ : F₁ →ₗ[R] F₀ := pres.map
  let X := F₁ × F₀
  let φ : X →ₗ[R] (F₁ × ↑M₀) :=
    (LinearMap.fst R F₁ F₀).prod (pres.π.comp (LinearMap.snd R F₁ F₀))
  let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
  let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
    (R := R) e he
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
  have hker : LinearMap.ker φ = J.restrictScalars R :=
    presentationMap_ker_eq_presentationIdealSmulTop (R := R) M₀
  have hsurj : Function.Surjective φ := by
    intro z
    rcases pres.surjective_π z.2 with ⟨y, hy⟩
    refine ⟨(z.1, y), ?_⟩
    refine Prod.ext ?_ ?_
    · rfl
    · simpa [φ, LinearMap.comp_apply] using hy
  -- First pass to the quotient by `ker φ`, then use the first isomorphism theorem.
  refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)⟩

/-- Helper for Chap10 Remark 10 88 13: quotienting the square-zero presentation module by the
`ε`-multiple submodule recovers `F₁ × M₀`. -/
private noncomputable def presentationTensorQuotientEquivProd
    (M₀ : ModuleCat.{v} R) :
    let pres := Module.Presentation.tautological R M₀
    let F₁ := pres.R →₀ R
    let F₀ := pres.G →₀ R
    let ρ : F₁ →ₗ[R] F₀ := pres.map
    let X := F₁ × F₀
    let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
    let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
    letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
    letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
      (R := R) e he
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
    (X ⧸ J.restrictScalars R) ≃ₗ[R] (F₁ × ↑M₀) :=
  Classical.choice (presentationTensorQuotientEquivProdExists (R := R) M₀)

/-- Helper for Chap10 Remark 10 88 13: the quotient ring `DualNumber R / (ε)` is canonically
identified with `R`. -/
private noncomputable def dualNumberQuotientAlgEquivBase :
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    (DualNumber R ⧸ I) ≃ₐ[R] R := by
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  have hfst_surj : Function.Surjective (TrivSqZeroExt.fstHom R R R) := by
    intro r
    refine ⟨TrivSqZeroExt.inl r, ?_⟩
    simp [TrivSqZeroExt.fstHom]
  -- Replace the principal ideal `(ε)` with the kernel of the projection, then apply the
  -- canonical quotient-by-kernel equivalence.
  exact (Ideal.quotientEquivAlgOfEq R (dualNumberSpanEps_eq_kerFstHom (R := R))).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := TrivSqZeroExt.fstHom R R R) hfst_surj)

/-- Helper for Chap10 Remark 10 88 13: the quotient ring `DualNumber R / (ε)` is finitely
presented as an `R`-module. -/
private theorem dualNumberQuotientFinitePresentationOverBase :
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    Module.FinitePresentation R (DualNumber R ⧸ I) := by
  let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
  -- Transport finite presentation from the rank-one free `R`-module along the quotient-ring
  -- equivalence.
  exact Module.FinitePresentation.of_equiv
    (dualNumberQuotientAlgEquivBase (R := R)).symm.toLinearEquiv

/-- Helper for Chap10 Remark 10 88 13: after reducing scalars modulo `(ε)`, the tensor stage
`(DualNumber R / (ε)) ⊗[DualNumber R] X` is Mittag-Leffler over the quotient ring. -/
private theorem presentationTensorMittagLefflerOverQuotient
    {X : Type w} [AddCommGroup X] [Module R X] [Module (DualNumber R) X]
    [IsScalarTower R (DualNumber R) X]
    (hX : MittagLeffler (DualNumber R) X) :
    let A := DualNumber R
    let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
    let S := A ⧸ I
    MittagLeffler S (S ⊗[A] X) := by
  let A := DualNumber R
  let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
  let S := A ⧸ I
  -- Route correction: use the chapter's base-change theorem directly on the tensor stage first;
  -- the quotient-module comparison is the next blocked step.
  exact Module.mittagLeffler_tensorProduct (R := A) (S := S) (M := X) hX

/-- Helper for Chap10 Remark 10 88 13: the quotient-ring tensor stage is canonically the quotient
module by the `(ε)`-multiple submodule. -/
private noncomputable def quotTensorEquivQuotSmulOverQuotient
    {X : Type w} [AddCommGroup X] [Module (DualNumber R) X] :
    let A := DualNumber R
    let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
    let S := A ⧸ I
    let J : Submodule A X := idealSmulTopSubmodule (S := A) (X := X) I
    (S ⊗[A] X) ≃ₗ[S] (X ⧸ J) := by
  let A := DualNumber R
  let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
  let S := A ⧸ I
  let J : Submodule A X := idealSmulTopSubmodule (S := A) (X := X) I
  -- Proof comment: upgrade the standard quotient-tensor equivalence to the quotient-ring scalar
  -- level using the surjectivity of `A → A ⧸ I`.
  exact (TensorProduct.quotTensorEquivQuotSMul X I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Remark 10 88 13: the quotient module `X ⧸ (εX)` is Mittag-Leffler over the
quotient ring `DualNumber R / (ε)` whenever `X` is Mittag-Leffler over `DualNumber R`. -/
private theorem presentationQuotientMittagLefflerOverQuotient
    {X : Type w} [AddCommGroup X] [Module R X] [Module (DualNumber R) X]
    [IsScalarTower R (DualNumber R) X]
    (hX : MittagLeffler (DualNumber R) X) :
    let A := DualNumber R
    let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
    let S := A ⧸ I
    let J : Submodule A X := idealSmulTopSubmodule (S := A) (X := X) I
    MittagLeffler S (X ⧸ J) := by
  let A := DualNumber R
  let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
  let S := A ⧸ I
  let J : Submodule A X := idealSmulTopSubmodule (S := A) (X := X) I
  have hTensorS : MittagLeffler S (S ⊗[A] X) := by
    simpa [A, I, S] using
      (presentationTensorMittagLefflerOverQuotient (R := R) (X := X) hX)
  let eQuot : (S ⊗[A] X) ≃ₗ[S] (X ⧸ J) :=
    quotTensorEquivQuotSmulOverQuotient (R := R) (X := X)
  -- Proof comment: transport the tensor-stage result across the owner-normal-form quotient
  -- equivalence.
  letI : MittagLeffler S (S ⊗[A] X) := hTensorS
  exact mittagLefflerOfLinearEquiv (R := S) eQuot.symm

/-- Helper for Chap10 Remark 10 88 13: ordinary restriction of scalars on `ModuleCat.of S M`
gives the expected bundled `R`-module object on the same carrier. -/
private noncomputable def restrictScalarsAlgEquivBaseObjIso
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  -- Proof comment: the restriction functor only forgets the `S`-linearity, so the resulting
  -- `R`-linear object is the same carrier with the same scalar action.
  (show ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

/-- Helper for Chap10 Remark 10 88 13: the eventual-factorization condition survives applying a
restriction-of-scalars functor to the entire directed system. -/
private lemma eventualFactorization_restrictScalars
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {I : Type w} [Preorder I]
    (f : A →+* B)
    (F : I ⥤ ModuleCat B)
    (hfactor :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h :
          (F ⋙ ModuleCat.restrictScalars f).obj k ⟶
            (F ⋙ ModuleCat.restrictScalars f).obj j,
        (F ⋙ ModuleCat.restrictScalars f).map (homOfLE hij) =
          (F ⋙ ModuleCat.restrictScalars f).map (homOfLE hik) ≫ h := by
  intro i
  obtain ⟨j, hij, hj⟩ := hfactor i
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨h, hh⟩ := hj k hik
  refine ⟨(ModuleCat.restrictScalars f).map h, ?_⟩
  -- Proof comment: apply the functor to the existing factorization identity.
  simpa using congrArg (fun g ↦ (ModuleCat.restrictScalars f).map g) hh

/-- Helper for Chap10 Remark 10 88 13: an eventual stage factorization of transition maps forces
every associated Hom inverse system to be Mittag-Leffler. -/
private lemma tailFactorization_implies_homMittagLeffler
    {A : Type u} [CommRing A]
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{max v w} A)
    (hfactor :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h) :
    ∀ N : ModuleCat.{max v w} A, (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
  intro (N : ModuleCat.{max v w} A)
  let G : Iᵒᵖ ⥤ Type (max v w) := colimitPresentationHomInverseSystem F N
  rw [Functor.isMittagLeffler_iff_subset_range_comp]
  intro iop
  let i : I := unop iop
  obtain ⟨j, hij, hj⟩ := hfactor i
  refine ⟨op j, (homOfLE hij).op, ?_⟩
  intro kop g
  let k : I := unop kop
  let hjk : j ≤ k := leOfHom g.unop
  let hik : i ≤ k := hij.trans hjk
  have hg_unop : g.unop = homOfLE hjk := Subsingleton.elim _ _
  have hcomp_unop :
      (g ≫ (homOfLE hij).op).unop = homOfLE hik := by
    -- Proof comment: preorder categories are thin, so this composite is the canonical arrow.
    exact Subsingleton.elim _ _
  have hjk_factor := hj k hik
  intro y hy
  have hy' :
      y ∈ Set.range (fun φ : F.obj j ⟶ (N : ModuleCat.{max v w} A) ↦ F.map (homOfLE hij) ≫ φ) := by
    simpa [G] using hy
  rcases hy' with ⟨φ, rfl⟩
  rcases hjk_factor with ⟨h, hh⟩
  have hyk :
      F.map (homOfLE hij) ≫ φ = F.map (homOfLE hik) ≫ (h ≫ φ) := by
    -- Proof comment: postcompose the stage factorization with `φ` to place the element in the
    -- stabilized range at stage `k`.
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ φ) hh
  have hyk' :
      F.map (homOfLE hij) ≫ φ ∈
        Set.range (fun ψ : F.obj k ⟶ (N : ModuleCat.{max v w} A) ↦ F.map (homOfLE hik) ≫ ψ) := by
    exact ⟨h ≫ φ, hyk.symm⟩
  simpa [G, hg_unop, hcomp_unop] using hyk'

/-- Helper for Chap10 Remark 10 88 13: a Mittag-Leffler directed system of `S`-modules stays
Mittag-Leffler after restriction of scalars along a ring equivalence `R ≃ S`. -/
private lemma isMittagLefflerDirectedSystem_restrictScalarsOfAlgEquivBase
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (e : S ≃ₐ[R] R)
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat S)
    (c : colimit F ≅ ModuleCat.of S M)
    (hML : IsMittagLefflerDirectedSystem F) :
    let G := ModuleCat.restrictScalars (algebraMap R S)
    IsMittagLefflerDirectedSystem (F ⋙ G) := by
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cR :
      colimit (F ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G F).symm ≪≫ G.mapIso c ≪≫
      restrictScalarsAlgEquivBaseObjIso (R := R) (S := S)
  rcases hML with ⟨hfpS, hallS⟩
  have hfactorS :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
    let Nprod : ModuleCat.{w} S :=
      ModuleCat.of.{w} S ((s : I) → ↥(F.obj s))
    have hprod :
        (colimitPresentationHomInverseSystem F Nprod).IsMittagLeffler := hallS Nprod
    exact product_hom_mittag_leffler_gives_stage_factorization (R := S) (F := F) hprod
  have hfactorR :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h :
            (F ⋙ G).obj k ⟶ (F ⋙ G).obj j,
          (F ⋙ G).map (homOfLE hij) = (F ⋙ G).map (homOfLE hik) ≫ h :=
    eventualFactorization_restrictScalars (algebraMap R S) F hfactorS
  have hfiniteS : Module.Finite R S := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hfpAlgS : Algebra.FinitePresentation R S := Algebra.FinitePresentation.equiv e.symm
  have hfpR : ∀ i, Module.FinitePresentation R ((F ⋙ G).obj i) := by
    intro i
    -- Proof comment: the quotient-ring equivalence makes `S` finite and finitely presented over
    -- `R`, so Lemma 10.36.23 transfers stagewise finite presentation directly.
    letI : Module.Finite R S := hfiniteS
    letI : Algebra.FinitePresentation R S := hfpAlgS
    letI : Module R (F.obj i) := Module.compHom (F.obj i) (algebraMap R S)
    letI : IsScalarTower R S (F.obj i) := IsScalarTower.restrictScalars R S (F.obj i)
    let eObj : ((F ⋙ G).obj i) ≃ₗ[R] (F.obj i) :=
      show ↑((F ⋙ G).obj i) ≃ₗ[R] (F.obj i) from
        { __ := AddEquiv.refl _
          map_smul' := fun _ _ ↦ by rfl }
    have hfpObj : Module.FinitePresentation R (F.obj i) := by
      exact (Module.FinitePresentation.iff_of_finite_finitePresentation
        (R := R) (S := S) (M := F.obj i)).2 (hfpS i)
    letI : Module.FinitePresentation R (F.obj i) := hfpObj
    exact Module.FinitePresentation.of_equiv eObj.symm
  have hallR :
      ∀ N : ModuleCat R, (colimitPresentationHomInverseSystem (F ⋙ G) N).IsMittagLeffler :=
    tailFactorization_implies_homMittagLeffler (F := F ⋙ G) hfactorR
  exact ⟨hfpR, hallR⟩

/-- Helper for Chap10 Remark 10 88 13: a module that is Mittag-Leffler over `S` remains
Mittag-Leffler after restricting scalars along an `R`-algebra equivalence `S ≃ₐ[R] R`. -/
private theorem mittagLefflerRestrictScalarsOfAlgEquivBase
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (e : S ≃ₐ[R] R) [MittagLeffler S M] :
    MittagLeffler R M := by
  classical
  let P : MittagLefflerPresentation S M :=
    Classical.choice (MittagLeffler.exists_presentation (R := S) (M := M))
  letI : Preorder P.index := P.indexPreorder
  letI : Nonempty P.index := P.indexNonempty
  letI : IsDirectedOrder P.index := P.indexDirected
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cS : colimit P.diagram ≅ ModuleCat.of S M := Classical.choice P.colimitIso
  let cR :
      colimit (P.diagram ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G P.diagram).symm ≪≫ G.mapIso cS ≪≫
      restrictScalarsAlgEquivBaseObjIso (R := R) (S := S)
  have hMLR : IsMittagLefflerDirectedSystem (P.diagram ⋙ G) :=
    isMittagLefflerDirectedSystem_restrictScalarsOfAlgEquivBase
      (R := R) (S := S) (e := e) P.diagram cS P.presentation_isMittagLeffler
  -- Proof comment: reuse the same presentation diagram after pulling every stage back along the
  -- ring equivalence.
  exact ⟨⟨{
    index := P.index
    indexPreorder := P.indexPreorder
    indexNonempty := P.indexNonempty
    indexDirected := P.indexDirected
    diagram := P.diagram ⋙ G
    presentation_isMittagLeffler := hMLR
    colimitIso := ⟨cR⟩
  }⟩⟩

/-- Helper for Chap10 Remark 10 88 13: the `R`-module structure on `X ⧸ J` obtained by
restricting the `DualNumber R`-action agrees with the `Module.compHom` spelling used by
`quotientRestrictScalarsCompHomEquiv`. -/
private noncomputable def quotientCompHomLinearEquiv
    {X : Type w} [AddCommGroup X] [Module R X] [Module (DualNumber R) X]
    [IsScalarTower R (DualNumber R) X]
    (J : Submodule (DualNumber R) X) :
    let Q := X ⧸ J
    letI : Module R Q := Module.compHom Q (algebraMap R (DualNumber R))
    (X ⧸ J) ≃ₗ[R] Q := by
  let Q := X ⧸ J
  letI : Module R Q := Module.compHom Q (algebraMap R (DualNumber R))
  -- Proof comment: both `R`-actions are induced by the same scalar map `R → DualNumber R`, so
  -- the identity map is already `R`-linear.
  exact
    { __ := AddEquiv.refl Q
      map_smul' := fun _ _ ↦ by rfl }

/-- Helper for Chap10 Remark 10 88 13: the quotient of a square-zero presentation module by its
`(ε)`-multiple submodule is Mittag-Leffler over `R` once the ambient `DualNumber R`-module is. -/
private theorem presentationQuotientMittagLefflerOverBase
    {X : Type w} [AddCommGroup X] [Module R X] [Module (DualNumber R) X]
    [IsScalarTower R (DualNumber R) X]
    (hX : MittagLeffler (DualNumber R) X) :
    let I : Ideal (DualNumber R) := Ideal.span ({DualNumber.eps} : Set (DualNumber R))
    let J : Submodule (DualNumber R) X := idealSmulTopSubmodule (S := DualNumber R) (X := X) I
    MittagLeffler R (X ⧸ J.restrictScalars R) := by
  let A := DualNumber R
  let I : Ideal A := Ideal.span ({DualNumber.eps} : Set A)
  let S := A ⧸ I
  let J : Submodule A X := idealSmulTopSubmodule (S := A) (X := X) I
  have hQuotS : MittagLeffler S (X ⧸ J) := by
    -- Proof comment: first convert the tensor-stage theorem into the quotient-owner statement over
    -- `S = DualNumber R / (ε)`.
    simpa [A, I, S, J, idealSmulTopSubmodule] using
      (presentationQuotientMittagLefflerOverQuotient (R := R) (X := X) hX)
  letI : MittagLeffler S (X ⧸ J) := hQuotS
  have hQuotR : MittagLeffler R (X ⧸ J) := by
    -- Proof comment: descend the quotient-ring statement back to `R` along the explicit algebra
    -- equivalence `DualNumber R / (ε) ≃ₐ[R] R`.
    exact mittagLefflerRestrictScalarsOfAlgEquivBase
      (R := R) (S := S) (e := dualNumberQuotientAlgEquivBase (R := R))
  let eRestrict : (X ⧸ J.restrictScalars R) ≃ₗ[R] (X ⧸ J) :=
    Submodule.Quotient.restrictScalarsEquiv R J
  letI : MittagLeffler R (X ⧸ J) := hQuotR
  -- Proof comment: the owner quotient over `DualNumber R` and the quotient by the restricted
  -- scalar submodule are canonically the same `R`-module.
  simpa [A, I, J, S] using mittagLefflerOfLinearEquiv (R := R) eRestrict

-- Proof sketch: start from a non-Mittag-Leffler `R`-module `M₀` and choose a presentation by free
-- modules `F₁ ⟶ F₀ ⟶ M₀ ⟶ 0`. Endow `F₁ ⊕ F₀` with the dual-number action coming from the square-zero
-- endomorphism given by the presentation map. As an `R`-module this object is free, hence
-- Mittag-Leffler over `R`; if it were Mittag-Leffler over `DualNumber R`, then reduction modulo
-- `ε` would also be Mittag-Leffler, forcing `F₁ ⊕ M₀` to be Mittag-Leffler over `R`, a
-- contradiction.
/-- Chap10 Remark 10 88 13: assuming there exists an `R`-module which is not Mittag-Leffler, the dual
numbers over `R` provide a counterexample to ascent of the Mittag-Leffler property: there exists a
`DualNumber R`-module which is Mittag-Leffler when viewed as an `R`-module, but which is not
Mittag-Leffler as a `DualNumber R`-module. -/
@[stacks 05CS]
theorem exists_dualNumber_module_mittagLeffler_over_base_not_over_dualNumber
    (h₀ : ∃ M₀ : ModuleCat.{v} R, ¬ MittagLeffler R M₀) :
    ∃ M : ModuleCat.{max u v} (DualNumber R),
      MittagLeffler R M ∧ ¬ MittagLeffler (DualNumber R) M := by
  classical
  rcases h₀ with ⟨M₀, hM₀⟩
  let pres := Module.Presentation.tautological R M₀
  let F₁ := pres.R →₀ R
  let F₀ := pres.G →₀ R
  let ρ : F₁ →ₗ[R] F₀ := pres.map
  let X := F₁ × F₀
  let e : Module.End R X := (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))
  let he : e.comp e = 0 := presentationEndomorphism_comp_self_eq_zero (R := R) ρ
  letI : Module.Free R X := inferInstance
  letI : Module (DualNumber R) X := dualNumberModuleOfSquareZero e he
  letI : IsScalarTower R (DualNumber R) X := dualNumberModuleOfSquareZero_isScalarTower
    (R := R) e he
  let M : ModuleCat.{max u v} (DualNumber R) := ModuleCat.of (DualNumber R) X
  refine ⟨M, ?_, ?_⟩
  · -- As an `R`-module, the square-zero construction does not change the underlying free module.
    change MittagLeffler R ((ModuleCat.restrictScalars (algebraMap R (DualNumber R))).obj M)
    let eBase :
        ((ModuleCat.restrictScalars (algebraMap R (DualNumber R))).obj M) ≃ₗ[R] X :=
      { __ := AddEquiv.refl X
        map_smul' := fun r x ↦ by
          -- The restricted-scalar action on `M` agrees with the original `R`-action on `X`.
          simpa [M] using dualNumberModuleOfSquareZero_inl_smul (R := R) e he r (x : X) }
    letI : MittagLeffler R X := dualNumberModuleOfSquareZero_mittagLefflerOverBase
      (R := R) (X := X) e he
    exact mittagLefflerOfLinearEquiv (R := R) eBase
  · intro hM
    have hXdual : MittagLeffler (DualNumber R) X := by
      -- Rephrase the bundled hypothesis on the carrier before descending modulo `ε`.
      simpa [M] using (show MittagLeffler (DualNumber R) (↑M) from hM)
    have hQuot :
        MittagLeffler R
          (X ⧸
            (idealSmulTopSubmodule
              (S := DualNumber R) (X := X)
              (Ideal.span ({DualNumber.eps} : Set (DualNumber R)))).restrictScalars R) := by
      -- Reduction modulo `ε` preserves Mittag-Leffler over the base ring.
      simpa [X, e, he] using
        (presentationQuotientMittagLefflerOverBase (R := R) (X := X) hXdual)
    have hProd : MittagLeffler R (F₁ × ↑M₀) := by
      letI :
          MittagLeffler R
            (X ⧸
              (idealSmulTopSubmodule
                (S := DualNumber R) (X := X)
                (Ideal.span ({DualNumber.eps} : Set (DualNumber R)))).restrictScalars R) := hQuot
      let eQuot :
          (X ⧸
            (idealSmulTopSubmodule
              (S := DualNumber R) (X := X)
              (Ideal.span ({DualNumber.eps} : Set (DualNumber R)))).restrictScalars R) ≃ₗ[R]
            (F₁ × ↑M₀) := by
        -- The tautological presentation quotient is exactly `F₁ × M₀`.
        simpa [pres, F₁, F₀, ρ, X, e, he] using
          (presentationTensorQuotientEquivProd (R := R) M₀)
      exact mittagLefflerOfLinearEquiv (R := R) eQuot.symm
    have hM₀' : MittagLeffler R M₀ := by
      -- The second factor of a Mittag-Leffler product is a split summand.
      simpa using
        (mittagLeffler_of_prod_right (R := R) (F := F₁) (M := ↑M₀) hProd)
    exact hM₀ hM₀'

end

end Module
