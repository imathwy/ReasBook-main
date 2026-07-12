import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf
import StacksProject_2024.Chap21.Definition_21_8_1
import StacksProject_2024.Chap21.Lemma_21_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w}
variable [Limits.HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]

/-- The degree-`p` Čech cohomology functor of the covering family `family`, restricted from
abelian presheaves to abelian sheaves. -/
abbrev cechCohomologyOnSheaves (J : GrothendieckTopology C) (family : ι → Over U) (p : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  sheafToPresheaf J AddCommGrpCat.{v} ⋙ (cechCohomologyDegree U family p).obj

/-- Evaluating `cechCohomologyOnSheaves J family p` at an abelian sheaf recovers the degree-`p`
Čech cohomology object of its underlying abelian presheaf. -/
@[simp] theorem cechCohomologyOnSheaves_obj_obj
    (family : ι → Over U) (p : ℕ) (ℐ : Sheaf J AddCommGrpCat.{v}) :
    (cechCohomologyOnSheaves J family p).obj ℐ =
      cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) p :=
  rfl

/- Domain-style sampling for Lemma 21.10.2:
- primary domain: Čech cohomology of abelian sheaves on a site, with the degree-zero term
  identified by the sheaf condition and the positive-degree terms computed by right derived
  functors;
- sampled canonical declarations:
  `cechCohomology`,
  `sheafSections`,
  `Presheaf.isSheaf_iff_multiequalizer`,
  `higherCechCohomologyFunctor_isomorphic_rightDerived`,
  `Functor.isZero_rightDerived_obj_injective_succ`;
- best owner abstraction: the source-facing owners remain the degree-zero identification and the
  positive-degree vanishing for `cechCohomology`, while the core/canonical owners are the sections
  functor `((sheafSections J AddCommGrpCat).obj (op U))`, the sheaf-condition owner
  `Presheaf.isSheaf_iff_multiequalizer`, and the right-derived functor package for higher degrees.

Source/core/bridge triage:
- `source-facing`: Čech `H^0` of a sheaf identifies with sections over `U`, and higher Čech
  cohomology of an injective sheaf vanishes;
- `core/canonical`: `sheafSections`, `Presheaf.isSheaf_iff_multiequalizer`,
  `higherCechCohomologyFunctor_isomorphic_rightDerived`, and
  `Functor.isZero_rightDerived_obj_injective_succ`;
- `bridge/view`: the degree-zero comparison is used only as internal proof data for the
  source-facing `IsIsomorphic` theorem, while `injective_underlying_abelian_presheaf` moves an
  injective abelian sheaf to the ambient abelian-presheaf category where the higher-degree
  right-derived owners live; this injective bridge uses
  `[HasSheafify J AddCommGrpCat.{v}]`, and the right-derived comparison is already exposed by
  Lemma `21.9.6`.

Primitive data versus derived API:
- primitive data: a covering family `family : ι → Over U`, a proof `hfamily` that it covers `U`
  for the degree-zero theorem, and an abelian sheaf `ℐ`, with injectivity used only for the
  positive-degree statement;
- derived API: the degree-zero comparison with sections and the positive-degree vanishing object.

The mixed `if p = 0 then ... else ...` wrapper is not kept as the public owner: the chapter owner
surface is the pair of atomic source-facing consequences, matching how the later module-valued
analogue is stated. -/

-- Proof sketch: compare degree-zero Čech cohomology for the covering family with the canonical
-- multiequalizer object, then apply the sheaf-condition identification from Lemma `21.8.2` to
-- the underlying abelian presheaf of `ℐ`.

/-- Lemma 21.10.2 (1): for a covering family of `U`, the degree-zero Čech cohomology of an
abelian sheaf is canonically isomorphic to its sections over the covered object. -/
@[stacks 03AW]
theorem cechCohomology_zero_of_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{v}) :
    IsIsomorphic
      (cechCohomology U family
        ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) 0)
      (((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj ℐ) := by
  sorry

/-- Sheaf-level companion to Lemma 21.10.2 (1): evaluating the degree-zero Čech cohomology
functor on an abelian sheaf identifies it with sections over `U`. -/
theorem cechCohomologyOnSheaves_zero_of_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{v}) :
    IsIsomorphic ((cechCohomologyOnSheaves J family 0).obj ℐ)
      (((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj ℐ) := by
  change IsIsomorphic
    (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) 0)
    (((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj ℐ)
  exact cechCohomology_zero_of_sheaf family hfamily ℐ

section

variable [HasSheafify J AddCommGrpCat.{v}]

-- Proof sketch: regard `ℐ` as injective in abelian presheaves by Lemma `21.10.1`, identify the
-- degree-`p + 1` term with the `(p + 1)`-st right derived functor of Čech `H^0` using Lemma
-- `21.9.6`, and then apply `Functor.isZero_rightDerived_obj_injective_succ`.
omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Lemma 21.10.2 (2): for an injective abelian sheaf, every positive-degree Čech cohomology
object vanishes. -/
@[stacks 03AW]
theorem cechCohomology_isZero_of_injective_succ
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ] (p : ℕ) :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) (p + 1)) :=
  sorry

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Typeclass form of Lemma 21.10.2 (2) on the source-facing owner `cechCohomology`. -/
instance instIsZeroCechCohomologyOfInjectiveSucc
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ] (p : ℕ) :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) (p + 1)) :=
  cechCohomology_isZero_of_injective_succ family ℐ p

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Sheaf-level companion to Lemma 21.10.2 (2): evaluating the positive-degree Čech cohomology
functor on an injective abelian sheaf gives the zero object. -/
theorem cechCohomologyOnSheaves_isZero_of_injective_succ
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ] (p : ℕ) :
    IsZero ((cechCohomologyOnSheaves J family (p + 1)).obj ℐ) := by
  change IsZero
    (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) (p + 1))
  exact cechCohomology_isZero_of_injective_succ family ℐ p

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Typeclass form of Lemma 21.10.2 (2) on the public sheaf-level owner
`cechCohomologyOnSheaves`. -/
instance instIsZeroCechCohomologyOnSheavesOfInjectiveSucc
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ] (p : ℕ) :
    IsZero ((cechCohomologyOnSheaves J family (p + 1)).obj ℐ) :=
  cechCohomologyOnSheaves_isZero_of_injective_succ family ℐ p

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Companion form of positive-degree Čech acyclicity: every strictly positive Čech cohomology
object of an injective abelian sheaf vanishes. -/
theorem cechCohomology_isZero_of_pos_of_injective
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ]
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa [Nat.add_comm] using cechCohomology_isZero_of_injective_succ family ℐ q

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Typeclass form of positive-degree Čech acyclicity on the source-facing owner
`cechCohomology`, using `Fact (0 < p)` for the positivity input. -/
instance instIsZeroCechCohomologyOfPosOfInjective
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ]
    (p : ℕ) [Fact (0 < p)] :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj ℐ) p) :=
  cechCohomology_isZero_of_pos_of_injective family ℐ p Fact.out

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Sheaf-level companion form of positive-degree Čech acyclicity. -/
theorem cechCohomologyOnSheaves_isZero_of_pos_of_injective
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((cechCohomologyOnSheaves J family p).obj ℐ) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa [Nat.add_comm] using
    cechCohomologyOnSheaves_isZero_of_injective_succ family ℐ q

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Typeclass form of positive-degree Čech acyclicity on the public sheaf-level owner
`cechCohomologyOnSheaves`, using `Fact (0 < p)` for the positivity input. -/
instance instIsZeroCechCohomologyOnSheavesOfPosOfInjective
    (family : ι → Over U) (ℐ : Sheaf J AddCommGrpCat.{v}) [Injective ℐ]
    (p : ℕ) [Fact (0 < p)] :
    IsZero ((cechCohomologyOnSheaves J family p).obj ℐ) :=
  cechCohomologyOnSheaves_isZero_of_pos_of_injective family ℐ p Fact.out

end

end CategoryTheory
