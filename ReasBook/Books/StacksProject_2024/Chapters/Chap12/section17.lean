import Mathlib
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Retract
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_17_1 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/- Domain-style sampling for Definition 12.17.1:
- primary domain: monoidal categories whose underlying category is additive and whose tensor
  product is additive in each variable;
- sampled owner API:
  `Preadditive`,
  `HasFiniteProducts`,
  `HasFiniteBiproducts.of_hasFiniteProducts`,
  `MonoidalPreadditive`;
- source/core/bridge triage:
  `source-facing`: the additive underlying-category condition, expressed by the earlier chapter
    owners `Preadditive C` and `HasFiniteProducts C`;
  `core/canonical`: the tensor-additivity owner `MonoidalPreadditive C`;
  `bridge/view`: finite biproducts are derived from `HasFiniteProducts C` in a preadditive
    category, so they are not primitive data here.

Primitive data are only the ambient monoidal category, the preadditive enrichment, the finite
product structure encoding additivity from Definition 12.3.8, and the tensor-additivity owner
`MonoidalPreadditive C`, whose primitive whiskering-linearity data are recorded by
`MonoidalPreadditive.whiskerLeft_zero`, `MonoidalPreadditive.zero_whiskerRight`,
`MonoidalPreadditive.whiskerLeft_add`, and `MonoidalPreadditive.add_whiskerRight`. The additive
tensor-functor API is derived from that owner, so no extra local wrapper is needed.
-/
/- Companion recall: by Definition 12.3.8, the additive part of Definition 12.17.1 is carried by
the canonical owner pair `Preadditive C` and `HasFiniteProducts C`. -/
recall Preadditive
recall HasFiniteProducts

variable [Preadditive C] [HasFiniteProducts C]

/- Definition 12.17.1: an additive monoidal category is a monoidal category whose underlying
category is additive and whose tensor product is additive in each variable. Reusing the earlier
chapter owner for additivity, the new owner-level content is `MonoidalPreadditive C`. -/
recall MonoidalPreadditive

/- Companion recall: the owner stores linearity of tensoring in each variable via the primitive
zero and addition whiskering fields. -/
recall MonoidalPreadditive.whiskerLeft_zero
recall MonoidalPreadditive.zero_whiskerRight
recall MonoidalPreadditive.whiskerLeft_add
recall MonoidalPreadditive.add_whiskerRight

/- Companion recall: the tensoring functors are additive by the canonical derived API attached to
`MonoidalPreadditive C`. -/
recall tensorLeft_additive
recall tensorRight_additive

end CategoryTheory

/-! ### Lemma_12_17_2 (from Chap12) -/
noncomputable section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [HasFiniteBiproducts C]
variable [MonoidalPreadditive C]
variable {X₁ Y₁ X₂ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]

local notation "X" => X₁ ⊞ X₂
local notation "Y" => Y₁ ⊞ Y₂

/-
Domain-style sampling for Lemma 12.17.2:
- primary domain: rigid monoidal category theory in a preadditive monoidal category with finite
  biproducts
- core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.HasLeftDual`
  - `CategoryTheory.Retract.hasLeftDual` from `Lemma_12_17_3`
  - `Limits.hasBinaryBiproducts_of_finite_biproducts` as the ambient biproduct bridge actually
    used by the construction
- best owner abstraction: `ExactPairing`
- primitive data: explicit exact pairings `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`
- derived API: the chosen-left-dual owner `HasLeftDual (Y₁ ⊞ Y₂)` when `Xᵢ = ᘁYᵢ`
- source/core/bridge triage:
  - source-facing: the direct sums of two explicit dual pairs again form an explicit dual pair
  - core/canonical: `ExactPairing`
  - bridge/view: `HasLeftDual.biprod` obtained by specializing to the chosen left duals
-/

/-- The diagonal summands `(X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₂)` embed canonically into
`X ⊗ Y` by first inserting them into the two distributed tensor factors and then undoing the
left distributor. -/
private def biprodDiagonalCoevaluationMap :
    (X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₂) ⟶ X ⊗ Y :=
  biprod.map
      ((biprod.inl : X₁ ⊗ Y₁ ⟶ (X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₁)) ≫
        ((tensorRight Y₁).mapBiprod X₁ X₂).inv)
      ((biprod.inr : X₂ ⊗ Y₂ ⟶ (X₁ ⊗ Y₂) ⊞ (X₂ ⊗ Y₂)) ≫
        ((tensorRight Y₂).mapBiprod X₁ X₂).inv) ≫
    ((tensorLeft X).mapBiprod Y₁ Y₂).inv

/-- The coevaluation for the biproduct exact-pairing datum is obtained by inserting the two given
coevaluations on the diagonal summands and transporting through the binary distributor isomorphisms
for tensoring on the left and on the right. -/
private def biprodCoevaluation : 𝟙_ C ⟶ X ⊗ Y :=
  biprod.lift (η_ X₁ Y₁) (η_ X₂ Y₂) ≫ biprodDiagonalCoevaluationMap

/-- Projecting `Y ⊗ X` to the two diagonal summands amounts to distributing the tensor product and
then keeping only the `Y₁ ⊗ X₁` and `Y₂ ⊗ X₂` pieces. -/
private def biprodDiagonalEvaluationMap :
    Y ⊗ X ⟶ (Y₁ ⊗ X₁) ⊞ (Y₂ ⊗ X₂) :=
  ((tensorLeft Y).mapBiprod X₁ X₂).hom ≫
    biprod.map
      (((tensorRight X₁).mapBiprod Y₁ Y₂).hom ≫
        (biprod.fst : (Y₁ ⊗ X₁) ⊞ (Y₂ ⊗ X₁) ⟶ Y₁ ⊗ X₁))
      (((tensorRight X₂).mapBiprod Y₁ Y₂).hom ≫
        (biprod.snd : (Y₁ ⊗ X₂) ⊞ (Y₂ ⊗ X₂) ⟶ Y₂ ⊗ X₂))

/-- The evaluation for the biproduct exact-pairing datum first distributes tensor product across
the direct sum, projects to the two diagonal summands, and then applies the given evaluations. -/
private def biprodEvaluation : Y ⊗ X ⟶ 𝟙_ C :=
  biprodDiagonalEvaluationMap ≫ biprod.desc (ε_ X₁ Y₁) (ε_ X₂ Y₂)

/-- The first triangle identity for the biproduct exact-pairing datum. -/
-- Proof sketch: expand `biprodCoevaluation` and `biprodEvaluation`, use the binary biproduct
-- relations to eliminate the off-diagonal terms, and then apply the two given triangle identities
-- on the diagonal summands together with the biproduct extensionality lemmas.
private theorem biprodCoevaluation_evaluation :
    Y ◁ biprodCoevaluation ≫
        (α_ Y X Y).inv ≫
        biprodEvaluation ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv := sorry

/-- The second triangle identity for the biproduct exact-pairing datum. -/
-- Proof sketch: distribute tensoring over the two biproducts, project to the diagonal summands,
-- observe that every off-diagonal composite vanishes by the biproduct identities, and reduce the
-- remaining diagonal pieces to the given triangle identities for `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`.
private theorem biprodEvaluation_coevaluation :
    biprodCoevaluation ▷ X ≫
        (α_ X Y X).hom ≫
        X ◁ biprodEvaluation =
      (λ_ X).hom ≫ (ρ_ X).inv := sorry

namespace ExactPairing

/-- If `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`, then their binary direct sums again form an exact pairing. -/
instance biprod : ExactPairing X Y where
  coevaluation' := biprodCoevaluation
  evaluation' := biprodEvaluation
  coevaluation_evaluation' := biprodCoevaluation_evaluation
  evaluation_coevaluation' := biprodEvaluation_coevaluation

end ExactPairing

namespace HasLeftDual

/-- If two objects have chosen left duals, then their direct sum has the direct sum of those
chosen left duals as a chosen left dual. -/
instance biprod {A B : C} [HasLeftDual A] [HasLeftDual B] : HasLeftDual (A ⊞ B) where
  leftDual := (ᘁA : C) ⊞ (ᘁB : C)
  exact := inferInstance

end HasLeftDual

end CategoryTheory

/-! ### Lemma_12_17_3 (from Chap12) -/
open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsIdempotentComplete C]
variable {X Y : C}

/-
Domain-style sampling for Lemma 12.17.3:
- primary domain: rigid monoidal category theory with retracts in an idempotent complete category
- core/canonical declarations inspected:
  - `HasLeftDual`
  - `ExactPairing`
  - `Retract`
  - `IsIdempotentComplete.idempotents_split`
- best owner abstraction: `HasLeftDual`
- primitive data: a retract `r : Retract X Y` and a chosen left dual on `Y`
- derived API: the induced `HasLeftDual X`
- source/core/bridge triage:
  - `source-facing`: retracts of left-dualizable objects are again left-dualizable
  - `core/canonical`: `HasLeftDual`
  - `bridge/view`: split the induced idempotent on `ᘁY` to obtain the chosen left dual of `X`
-/

namespace Retract

private def idempotent (r : Retract X Y) : Y ⟶ Y :=
  r.r ≫ r.i

omit [MonoidalCategory C] [IsIdempotentComplete C] in
private theorem idempotent_idem (r : Retract X Y) :
    r.idempotent ≫ r.idempotent = r.idempotent := by
  dsimp [idempotent]
  simp [Category.assoc]

private def dualIdempotent [HasLeftDual Y] (r : Retract X Y) : (ᘁY : C) ⟶ ᘁY :=
  ᘁ(r.idempotent)

omit [IsIdempotentComplete C] in
private theorem dualIdempotent_idem [HasLeftDual Y] (r : Retract X Y) :
    r.dualIdempotent ≫ r.dualIdempotent = r.dualIdempotent := by
  simpa [dualIdempotent, comp_leftAdjointMate] using
    congrArg (fun f : Y ⟶ Y ↦ leftAdjointMate f) r.idempotent_idem

section

variable [HasLeftDual Y] (r : Retract X Y)

private theorem exists_dualSplit :
    ∃ split : Σ Y' : C, Retract Y' (ᘁY : C), split.2.r ≫ split.2.i = r.dualIdempotent := by
  rcases IsIdempotentComplete.idempotents_split (ᘁY : C) r.dualIdempotent r.dualIdempotent_idem with
    ⟨Y', i, e, hi, he⟩
  exact ⟨⟨Y', ⟨i, e, hi⟩⟩, he⟩

private noncomputable def dualSplit :
    Σ Y' : C, Retract Y' (ᘁY : C) :=
  Classical.choose r.exists_dualSplit

private noncomputable def leftDual : C :=
  r.dualSplit.1

private noncomputable def leftDualRetract :
    Retract r.leftDual (ᘁY : C) :=
  r.dualSplit.2

private theorem dualSplit_comp :
    (r.leftDualRetract).r ≫ (r.leftDualRetract).i = r.dualIdempotent :=
  Classical.choose_spec r.exists_dualSplit

private noncomputable def coevaluation :
    𝟙_ C ⟶ r.leftDual ⊗ X :=
  η_ (ᘁY) Y ≫ (r.leftDualRetract).r ▷ Y ≫ r.leftDual ◁ r.r

private noncomputable def evaluation :
    X ⊗ r.leftDual ⟶ 𝟙_ C :=
  r.i ▷ r.leftDual ≫ Y ◁ (r.leftDualRetract).i ≫ ε_ (ᘁY) Y

private theorem coevaluation_evaluation :
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := sorry

private theorem evaluation_coevaluation :
    r.coevaluation ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.evaluation =
      (λ_ r.leftDual).hom ≫ (ρ_ r.leftDual).inv := sorry

@[implicit_reducible] private noncomputable instance exactPairing :
    ExactPairing r.leftDual X where
  coevaluation' := r.coevaluation
  evaluation' := r.evaluation
  coevaluation_evaluation' := r.coevaluation_evaluation
  evaluation_coevaluation' := r.evaluation_coevaluation

end

/-- Lemma 12.17.3: in an idempotent complete monoidal category, every retract, hence every
summand, of an object admitting a left dual again admits a left dual. -/
@[implicit_reducible] noncomputable def hasLeftDual [HasLeftDual Y] (r : Retract X Y) :
    HasLeftDual X where
  leftDual := r.leftDual
  exact := inferInstance

end Retract

end CategoryTheory

/-! ### Example_12_17_4 (from Chap12) -/
open CategoryTheory
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory

variable {F : Type u} [Field F]

namespace GradedObject.Monoidal

/- Source/core/bridge triage:
- `source-facing`: the Koszul-signed commutativity constraint on graded `F`-vector spaces.
- `core/canonical`: there is no exact upstream owner for the Koszul-signed braiding in
  `GradedObject ℤ (ModuleCat F)`. The canonical infrastructure this file should reuse is the graded
  tensor API `tensorObjDesc`/`ιTensorObj`, with nearby domain samples
  `GradedObject.Monoidal.braiding`, `TensorProduct.gradedComm`, and
  `CategoryTheory.CatCenter.app_neg_one_zpow`.
- `bridge/view`: the summandwise restriction theorem `koszulBraiding_hom_app`.

Primitive data are only the degreewise signed swaps; naturality, hexagon identities, and symmetry
are derived theorem-level API used to package the symmetric structure. -/

/-- The degreewise Koszul-signed swap on the `(p, q)`-summand of a tensor product of graded
`F`-vector spaces. -/
def koszulBraidingComponent (V W : GradedObject ℤ (ModuleCat F)) (p q : ℤ) :
    V p ⊗ W q ⟶ W q ⊗ V p :=
  ((p * q).negOnePow : F) • (β_ (V p) (W q)).hom

private abbrev koszulBraidingHom (V W : GradedObject ℤ (ModuleCat F)) :
    V ⊗ W ⟶ W ⊗ V :=
  fun n ↦
    tensorObjDesc
      (fun p q h ↦
        koszulBraidingComponent V W p q ≫
          ιTensorObj W V q p n (by simpa [add_comm] using h))

-- Proof sketch: compute both composites degreewise. On the summand `V^p ⊗ W^q`, the two signed
-- swaps contribute the scalar `(-1)^(pq) * (-1)^(qp) = 1`, and the remaining map is the ordinary
-- symmetry of the tensor product in `ModuleCat F`, which is involutive.
private theorem koszulBraiding_hom_inv_id (V W : GradedObject ℤ (ModuleCat F)) :
    koszulBraidingHom V W ≫ koszulBraidingHom W V = 𝟙 (V ⊗ W) := sorry

/-- The Koszul-signed braiding on graded `F`-vector spaces. -/
noncomputable def koszulBraiding (V W : GradedObject ℤ (ModuleCat F)) :
    V ⊗ W ≅ W ⊗ V where
  hom := koszulBraidingHom V W
  inv := koszulBraidingHom W V
  hom_inv_id := koszulBraiding_hom_inv_id V W
  inv_hom_id := koszulBraiding_hom_inv_id W V

private theorem koszulBraiding_naturality_left
    {V W X : GradedObject ℤ (ModuleCat F)} (f : V ⟶ W) :
    f ▷ X ≫ (koszulBraiding W X).hom =
      (koszulBraiding V X).hom ≫ X ◁ f := by
  sorry

private theorem koszulBraiding_naturality_right
    (V : GradedObject ℤ (ModuleCat F)) {W X : GradedObject ℤ (ModuleCat F)} (f : W ⟶ X) :
    V ◁ f ≫ (koszulBraiding V X).hom =
      (koszulBraiding V W).hom ≫ f ▷ V := by
  sorry

private theorem koszulBraiding_hexagon_forward
    (V W X : GradedObject ℤ (ModuleCat F)) :
    (α_ V W X).hom ≫ (koszulBraiding V (W ⊗ X)).hom ≫ (α_ W X V).hom =
      (koszulBraiding V W).hom ▷ X ≫ (α_ W V X).hom ≫
        W ◁ (koszulBraiding V X).hom := by
  sorry

private theorem koszulBraiding_hexagon_reverse
    (V W X : GradedObject ℤ (ModuleCat F)) :
    (α_ V W X).inv ≫ (koszulBraiding (V ⊗ W) X).hom ≫ (α_ X V W).inv =
      V ◁ (koszulBraiding W X).hom ≫ (α_ V X W).inv ≫
        (koszulBraiding V X).hom ▷ W := by
  sorry

/-- The symmetric-category package whose braiding is `koszulBraiding`. -/
noncomputable abbrev koszulSymmetricCategory :
    SymmetricCategory (GradedObject ℤ (ModuleCat F)) where
  toBraidedCategory :=
    { braiding := koszulBraiding
      braiding_naturality_left := by
        intro V W f X
        simpa using koszulBraiding_naturality_left f
      braiding_naturality_right := by
        intro X V W f
        simpa using koszulBraiding_naturality_right X f
      hexagon_forward := by
        intro V W X
        simpa using koszulBraiding_hexagon_forward V W X
      hexagon_reverse := by
        intro V W X
        simpa using koszulBraiding_hexagon_reverse V W X }
  symmetry V W := (koszulBraiding V W).hom_inv_id

-- Proof sketch: unfold `koszulBraiding`; its degree-`n` component is defined by
-- descending the signed swaps on the summands `V^p ⊗ W^q`, so restricting along the canonical
-- inclusion of the `(p, q)`-summand gives exactly that signed swap.
/-- The signed commutativity constraint restricts on each `(p, q)`-summand to the Koszul-signed
swap map. -/
@[reassoc]
theorem koszulBraiding_hom_app
    (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj V W p q n h ≫ (koszulBraiding V W).hom n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (Eq.trans (add_comm q p) h) := by
  simp [koszulBraiding, koszulBraidingHom, ι_tensorObjDesc]

end GradedObject.Monoidal

end CategoryTheory

/-! ### Lemma_12_17_5 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory

variable {F : Type u} [Field F]

/-
Source/core/bridge triage for Lemma 12.17.5:
- source-facing statement: a left-dualizable graded `F`-vector space has finite total dimension,
  and the evaluation map induces nondegenerate degreewise pairings
- core/canonical owner: `ExactPairing W V` for a chosen left dual `W` of `V`, together with the
  signed graded braiding `GradedObject.Monoidal.koszulBraiding` from Example 12.17.4 and the
  canonical support owner `GradedObject.finrankSupport`
- bridge/view: the degreewise bilinear pairing obtained by restricting the owner evaluation map to
  the summand of total degree `0` and transporting it to the `W^{-n} ⊗ V^n` order used by the
  textbook pairing through the Koszul-signed braiding
-/

/-- A graded `F`-vector space has finite total dimension if only finitely many graded pieces are
nonzero and each graded piece is finite dimensional. We record this using the canonical graded
support `GradedObject.finrankSupport`. -/
abbrev hasFiniteTotalDimension (V : GradedObject ℤ (ModuleCat F)) : Prop :=
  Set.Finite (GradedObject.finrankSupport V) ∧ ∀ n : ℤ, FiniteDimensional F (V n)

/-- For a finite-dimensional graded piece of a graded `F`-vector space, belonging to the
canonical finite-rank support is equivalent to being nonzero. -/
private theorem mem_finrankSupport_iff_not_isZero
    (V : GradedObject ℤ (ModuleCat F)) (n : ℤ) [FiniteDimensional F (V n)] :
    n ∈ GradedObject.finrankSupport V ↔ ¬ IsZero (V n) := by
  have hzero : Module.finrank F (V n) = 0 ↔ IsZero (V n) := by
    rw [Module.finrank_eq_zero_iff_of_free F (V n), ModuleCat.isZero_iff_subsingleton]
  rw [GradedObject.finrankSupport, Function.mem_support]
  exact not_congr hzero

private theorem finrankSupport_eq_nonzero_degrees
    (V : GradedObject ℤ (ModuleCat F)) (hfd : ∀ n : ℤ, FiniteDimensional F (V n)) :
    GradedObject.finrankSupport V = {n : ℤ | ¬ IsZero (V n)} := by
  ext n
  letI := hfd n
  simpa using mem_finrankSupport_iff_not_isZero V n

/-- Textbook reformulation of `hasFiniteTotalDimension`: only finitely many graded pieces are
nonzero, and every graded piece is finite dimensional. -/
theorem hasFiniteTotalDimension_iff
    (V : GradedObject ℤ (ModuleCat F)) :
    hasFiniteTotalDimension V ↔
      Set.Finite {n : ℤ | ¬ IsZero (V n)} ∧ ∀ n : ℤ, FiniteDimensional F (V n) := by
  constructor
  · rintro ⟨hfin, hfd⟩
    rw [finrankSupport_eq_nonzero_degrees V hfd] at hfin
    exact ⟨hfin, hfd⟩
  · rintro ⟨hfin, hfd⟩
    exact ⟨(finrankSupport_eq_nonzero_degrees V hfd).symm ▸ hfin, hfd⟩

variable {V W : GradedObject ℤ (ModuleCat F)} [ExactPairing W V]

/-- The degree-`0` component of the exact-pairing evaluation, restricted to the `(-n,n)` tensor
summand and written in textbook order via the Koszul-signed braiding from Example 12.17.4. -/
private abbrev degreewiseEvaluationHom
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) ⊗ V n ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (koszulBraiding W V).hom 0 ≫
    ε_ W V 0 ≫ tensorUnit₀.hom

/-- The degreewise bilinear pairing induced from the evaluation of a chosen left dual `W` of `V`,
written in the textbook order `W^{-n} × V^n → F`. -/
noncomputable abbrev degreewiseEvaluation
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) →ₗ[F] V n →ₗ[F] F :=
  TensorProduct.curry (degreewiseEvaluationHom V W n).hom

/-- Lemma 12.17.5: if `V` in the monoidal category of graded `F`-vector spaces has left dual
`W`, then `V` has finite total dimension and the evaluation morphism induces nondegenerate
pairings `W^{-n} × V^n → F` in every degree. -/
-- Proof sketch: write the coevaluation of the exact pairing as a finite sum of homogeneous pure
-- tensors. The triangle identities force the finitely many homogeneous vectors appearing there to
-- generate both graded objects, which gives finite dimensionality of each graded piece and leaves
-- only finitely many nonzero degrees. The same identities identify the degreewise evaluation maps
-- with dual-basis pairings, hence each resulting bilinear map is nondegenerate.
theorem leftDual_hasFiniteTotalDimension_and_nondegenerate_degreewiseEvaluation
    :
    hasFiniteTotalDimension V ∧
      ∀ n : ℤ, (degreewiseEvaluation V W n).Nondegenerate := sorry

end CategoryTheory
