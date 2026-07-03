import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_31_1 (from Chap12) -/
universe u v

open CategoryTheory
open CategoryTheory.Limits
open OrderDual (ofDual toDual)
open Opposite

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category C]

/- Domain-style sampling for Lemma 12.31.1 in the inverse-system exactness domain:
- primary domain: exactness of short complexes in the functor category `Iᵒᵈ ⥤ C`
- sampled owner declarations:
  `NatTrans.isIso_iff_isIso_app`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `inferInstance : Abelian (Iᵒᵈ ⥤ C)`.
- owner abstraction: the evaluation family
    `((evaluation Iᵒᵈ C).obj : Iᵒᵈ → (Iᵒᵈ ⥤ C) ⥤ C)` viewed through
    `JointlyReflectIsomorphisms`
- primitive data: a short complex `S` of inverse systems and the evaluation functors at each index
- derived API: the stagewise short complex `S.app i` and the exactness criterion
  `inverse_system_exact_iff_exact_app`, both indexed by textbook stages `i : I`
- source/core/bridge triage: this theorem is a `source-facing` bridge specialization of the
  core/canonical theorem `JointlyReflectIsomorphisms.exact_iff`. -/

namespace ShortComplex

variable [HasZeroMorphisms C]

/-- The short complex obtained by evaluating a short complex of inverse systems at stage `i`. -/
abbrev app (S : ShortComplex (Iᵒᵈ ⥤ C)) (i : I) : ShortComplex C :=
  S.map ((evaluation Iᵒᵈ C).obj (toDual i))

end ShortComplex

section Additive

variable [Preadditive C]

/- Background recall: for a preadditive category `C`, the category of inverse systems
`Iᵒᵈ ⥤ C` inherits the canonical preadditive structure objectwise. -/
#check (inferInstance : Preadditive (Iᵒᵈ ⥤ C))

section Biproducts

variable [HasFiniteBiproducts C]

/- Background recall: if `C` has finite biproducts, then inverse systems with values in `C`
also have finite biproducts. -/
#check (HasFiniteBiproducts.of_hasFiniteProducts :
  HasFiniteBiproducts (Iᵒᵈ ⥤ C))

end Biproducts
end Additive

section Abelian

variable [Abelian C]

/- Background recall: if `C` is abelian, then the category of inverse systems with values in `C`
is abelian. -/
#check (inferInstance : Abelian (Iᵒᵈ ⥤ C))

/-- Lemma 12.31.1: a short complex of inverse systems is exact if and only if the evaluated
short complex is exact at every index. -/
theorem inverse_system_exact_iff_exact_app
    (S : ShortComplex (Iᵒᵈ ⥤ C)) :
    S.Exact ↔ ∀ i : I, (S.app i).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation Iᵒᵈ C).obj : Iᵒᵈ → (Iᵒᵈ ⥤ C) ⥤ C) := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    simpa using (inferInstance : IsIso (((evaluation Iᵒᵈ C).obj i).map f))
  constructor
  · intro hS i
    simpa [ShortComplex.app] using (hEval.exact_iff S).1 hS (toDual i)
  · intro hS
    exact (hEval.exact_iff S).2 fun i ↦ by
      simpa [ShortComplex.app] using hS (ofDual i)

end Abelian

end CategoryTheory

/-! ### Definition_12_31_2 (from Chap12) -/
open Opposite
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

/-- High-reuse core vocabulary for a sequential inverse system in `A`, namely a functor
`ℕᵒᵖ ⥤ A`. -/
abbrev SequentialInverseSystem (A : Type u) [Category.{v} A] := ℕᵒᵖ ⥤ A

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-
Domain-style sampling for Definition 12.31.2 in the inverse-system / Mittag-Leffler domain:
- sampled mathlib owner declarations in the concrete `Type`-valued setting:
  * `CategoryTheory.Functor.IsMittagLeffler`
  * `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`
  * `CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp`
- source/core/bridge triage:
  * `source-facing`: the textbook stabilization of image subobjects for a sequential inverse system
    in an abelian category
  * `core/canonical`: mathlib's `Functor.IsMittagLeffler` for `Type`-valued cofiltered systems
  * `bridge/view`: faithful/concrete comparisons between the image-subobject formulation here and
    the range-stabilization owner in concrete categories

The present item therefore stays `source-facing`: its primitive data are only the inverse system
`F`, while the transition morphisms are derived from that owner object. The broader categorical
image-subobject formulation carries genuinely more semantics than the `Type`-valued owner, so this
file should define it directly rather than disguise it as a wrapper around the concrete mathlib
predicate.
-/

/-- Derived API: the transition morphism `F_j ⟶ F_i` attached to an inequality `i ≤ j`. -/
abbrev transitionMap (F : SequentialInverseSystem A) {i j : ℕ} (hij : i ≤ j) :
    F.obj (op j) ⟶ F.obj (op i) :=
  F.map ((homOfLE hij).op)

/-- Derived API: the successor transition morphism `F_{n + 1} ⟶ F_n` of a sequential inverse
system. -/
abbrev stepMap (F : SequentialInverseSystem A) (n : ℕ) :
    F.obj (op (n + 1)) ⟶ F.obj (op n) :=
  F.transitionMap (Nat.le_add_right n 1)

/-- The tail of a sequential inverse system obtained by shifting the index by `n`. -/
abbrev shift (F : SequentialInverseSystem A) (n : ℕ) : SequentialInverseSystem A :=
  ({ toFun := fun i ↦ n + i
     monotone' := fun _ _ hij ↦ Nat.add_le_add_left hij n } : ℕ →o ℕ).toFunctor.op ⋙ F

@[simp] theorem shift_obj (F : SequentialInverseSystem A) (n i : ℕ) :
    (F.shift n).obj (op i) = F.obj (op (n + i)) :=
  rfl

@[simp] theorem shift_transitionMap (F : SequentialInverseSystem A) (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) :
    (F.shift n).transitionMap hij = F.transitionMap (Nat.add_le_add_left hij n) :=
  rfl

/-- The sequential inverse system obtained by taking countable coproducts stagewise. -/
noncomputable def countableCoproduct [HasCountableCoproducts A] (F : SequentialInverseSystem A) :
    SequentialInverseSystem A :=
  F ⋙ ((Functor.const (Discrete ℕ)) ⋙ colim)

/-- Evaluating the stagewise countable-coproduct inverse system at `n` gives the canonical
countable coproduct of copies of `F.obj n`. -/
@[simp] theorem countableCoproduct_obj [HasCountableCoproducts A]
    (F : SequentialInverseSystem A) (n : ℕᵒᵖ) :
    F.countableCoproduct.obj n = ∐ fun _ : ℕ ↦ F.obj n :=
  rfl

/-- Definition 12.31.2: the textbook Mittag-Leffler condition for a sequential inverse system in
an abelian category only uses the image subobjects of the transition morphisms, so the owner-level
Lean predicate is stated in any category with images. -/
def IsMittagLeffler [HasImages A] (F : SequentialInverseSystem A) : Prop :=
  ∀ i : ℕ, ∃ (c : ℕ) (hic : i ≤ c),
    ∀ ⦃k : ℕ⦄ (hck : c ≤ k),
      imageSubobject (F.transitionMap (hic.trans hck)) =
        imageSubobject (F.transitionMap hic)

end SequentialInverseSystem

namespace SequentialProObjectMorphismRep

variable {A : Type u} [Category.{v} A] {X Y : SequentialInverseSystem A}

/-- Build a sequential pro-object representative from a natural transformation out of a shifted
source inverse system. -/
def ofShiftNatTrans (c : ℕ) (α : X.shift c ⟶ Y) :
    SequentialProObjectMorphismRep X Y where
  reindex :=
    { toFun := fun n ↦ c + n
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h c }
  hom := by
    simpa [SequentialInverseSystem.shift] using α

end SequentialProObjectMorphismRep

end CategoryTheory

/-! ### Lemma_12_31_3 (from Chap12) -/
open CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 12.31.3 in the inverse-limit / Mittag-Leffler domain:
- owner abstractions:
  * `SequentialInverseSystem` and `SequentialInverseSystem.IsMittagLeffler` from
    `Definition_12_31_2`
  * `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`
  * `ShortComplex.ShortExact.mk'`
  * `ShortComplex.exact_and_mono_f_iff_f_is_kernel`
- primitive data: a short exact sequence `S` of sequential inverse systems together with, for (2)
  and (3), the owner Mittag-Leffler hypothesis on one term
- derived API: the induced short complex `S.map lim` on inverse limits and its exactness,
  monomorphism, and short-exactness consequences
- source/core/bridge triage:
  * `source-facing`: the textbook statements about inverse limits and Mittag-Leffler towers
  * `core/canonical`: the owner exactness criteria for `ShortComplex` under `lim`
  * `bridge/view`: the abelian-group specialization from a short exact sequence of towers to the
    induced exactness properties on inverse limits

These lemmas should therefore live under the chapter owner `SequentialInverseSystem`; the short
complex on inverse limits is derived from `lim`, not packaged as a separate public wrapper. -/

variable (S : ShortComplex AbSeq)

-- Proof sketch: inverse limits of abelian groups are left exact. Apply the owner exact-functor
-- criterion for `lim` preserving finite limits to the given short exact sequence of sequential
-- inverse systems.
/-- Lemma 12.31.3 (1): for a short exact sequence of sequential inverse systems of abelian groups,
the induced sequence on inverse limits is left exact; equivalently, the map
`\varprojlim A_i \to \varprojlim B_i` is monic and the short complex
`\varprojlim A_i \to \varprojlim B_i \to \varprojlim C_i` is exact. -/
theorem inverseLimit_exact_and_mono_of_shortExact
    (hS : S.ShortExact)
    : (S.map lim).Exact ∧ Mono (S.map lim).f := by
  simpa using
    (S.map lim).exact_and_mono_f_iff_f_is_kernel.2
      ⟨KernelFork.mapIsLimit _ hS.fIsKernel lim⟩

-- Proof sketch: evaluate the short exact sequence at each stage, where the right map is
-- surjective. The image-stabilization condition for the middle inverse system then passes to the
-- quotient inverse system, so the right term is again Mittag-Leffler.
/-- Lemma 12.31.3 (2): if the middle term of a short exact sequence of sequential inverse systems
of abelian groups is Mittag-Leffler, then the quotient inverse system is also Mittag-Leffler. -/
theorem isMittagLeffler_right_of_shortExact
    (hS : S.ShortExact)
    (hML : S.X₂.IsMittagLeffler) :
    S.X₃.IsMittagLeffler := sorry

-- Proof sketch: this is the abelian-group specialization of the inverse-limit short-exactness
-- theorem for short exact sequences of sequential inverse systems with Mittag-Leffler left term.
/-- Lemma 12.31.3 (3): if the left term of a short exact sequence of sequential inverse systems of
abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short exact. -/
theorem inverseLimit_shortExact_of_isMittagLeffler_left
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    (S.map lim).ShortExact := sorry

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_12_31_4 (from Chap12) -/
open CategoryTheory.Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe u

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 12.31.4 in the sequential inverse-system exactness domain:
- `source-facing`: a four-term exact sequence of sequential inverse systems and the induced exact
  tail sequence on inverse limits
- `core/canonical`: the finite exact-sequence owner `ComposableArrows.Exact` together with the
  chapter theorems `inverseLimit_shortExact_of_isMittagLeffler_left` and
  `inverseLimit_exact_and_mono_of_shortExact`
- `bridge/view`: the present theorem, which passes from an exact four-term composable-arrow object
  of towers to exactness of the tail sequence after applying inverse limit

Primitive data are the exact composable-arrow object `S : ComposableArrows AbSeq 3` and the
Mittag-Leffler condition on its leftmost term `S.left`. The tail inverse-limit sequence is
derived canonically as `δ₀ (S ⋙ lim)`, so the statement should use that owner-level
construction directly rather than reintroducing separate primitive morphism binders. -/

-- Proof sketch: let `Z_i = ker(C_i ⟶ D_i)` and `I_i = im(A_i ⟶ B_i)`. The short exact sequence
-- `0 ⟶ I_i ⟶ B_i ⟶ Z_i ⟶ 0` together with Lemma 12.31.3 yields surjectivity of
-- `\varprojlim B_i ⟶ \varprojlim Z_i`, and `\varprojlim Z_i` identifies with the kernel of
-- `\varprojlim C_i ⟶ \varprojlim D_i`.
/-- Lemma 12.31.4: let `A ⟶ B ⟶ C ⟶ D` be an exact sequence of sequential inverse systems of
abelian groups. If `A` is Mittag-Leffler, then the induced sequence on inverse limits
`\varprojlim B ⟶ \varprojlim C ⟶ \varprojlim D` is exact. -/
theorem inverseLimit_exact_of_four_term_exact_of_isMittagLeffler_left
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : S.left.IsMittagLeffler) :
    (δ₀ (S ⋙ lim)).Exact := sorry

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_12_31_5 (from Chap12) -/
open Opposite
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.31.5 in the sequential inverse-system / split-limit domain:
- sampled owner-level declarations:
  * `SequentialInverseSystem` in `Definition_12_31_2`
  * `SequentialInverseSystem.transitionMap` in `Definition_12_31_2`
  * `SequentialInverseSystem.shift` in `Definition_12_31_2`
  * `HasEventuallySplitLimit` in `Lemma_12_30_1`
  * `essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit` in `Lemma_12_30_1`
  * `BinaryBiproductData` in mathlib's binary-biproduct API
- best owner abstractions:
  * primitive tail owners: `SequentialInverseSystem.shift` for the shifted tail of `F`, and
    `SequentialInverseSystem` for the complementary system
  * chapter bridge owner: `HasEventuallySplitLimit`

Primitive-vs-derived split:
- primitive source-facing data: an actual limit cone `c : LimitCone F`, a tail index `N`, the
  shifted tail owner `F.shift N`, and for each shifted stage `j` a direct-sum decomposition of
  `(F.shift N).obj (op j)` into the limit object `c.cone.pt` and the `j`-th object of a
  complementary sequential inverse system `Z`, together with the induced tail comparison maps read
  directly from `(F.shift N).transitionMap` and `Z.transitionMap`.
- derived API: the owner-level criterion `HasEventuallySplitLimit F`, and hence the canonical
  essential-constancy predicate on the cofiltered diagram `F`.

Source/core/bridge triage:
- `source-facing`: `HasLimitTailDecomposition`, which is the sequential tail decomposition stated
  in the Stacks lemma.
- `core/canonical`: `HasEventuallySplitLimit F` and `IsEssentiallyConstantCofilteredDiagram F`.
- `bridge/view`: `hasEventuallySplitLimit_iff` and
  `essentiallyConstant_iff_hasLimitTailDecomposition`, which identify the source-facing sequential
  criterion with the chapter owner abstractions. -/

private def tailDecompositionMap
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    bY.bicone.pt ⟶ bZ.bicone.pt :=
  let hZ : IsLimit bZ.bicone.toCone := bZ.isBilimit.isLimit
  hZ.lift (BinaryFan.mk bY.bicone.fst (bY.bicone.snd ≫ f))

/-- Lemma 12.31.5: a sequential inverse system admits a split limit tail when, after shifting by
some index `N`, the shifted system `F.shift N` is identified stagewise with the direct sum of the
actual inverse limit `c.cone.pt` and a complementary sequential inverse system `Z`, the transition
maps preserve the limit summand, and the complementary transition maps are eventually zero. -/
def HasLimitTailDecomposition (F : SequentialInverseSystem A) : Prop :=
  ∃ c : LimitCone F,
    ∃ N : ℕ,
      ∃ Z : SequentialInverseSystem A,
        ∃ B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)),
          ∃ e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt,
            (∀ j, c.cone.π.app (op (N + j)) = (B j).bicone.inl ≫ (e j).inv) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                (F.shift N).transitionMap hij =
                  (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫
                    (e i).inv) ∧
                ∀ i : ℕ, ∃ j : ℕ, ∃ hij : i ≤ j, Z.transitionMap hij = 0

-- Proof sketch: pass from the owner-level criterion `HasEventuallySplitLimit F` to a cofinal tail
-- of `ℕᵒᵖ`, identify an initial full subcategory with another sequential inverse system, and
-- rewrite the splitting data from Lemma 12.30.1 as explicit biproduct decompositions of the tail
-- stages. The eventual-vanishing clause is the translated form of the condition that the
-- complementary summand is killed by some earlier transition map.
/-- Bridge theorem for Lemma 12.31.5: the chapter owner `HasEventuallySplitLimit F` is equivalent
to the explicit sequential tail decomposition with actual limit object and eventually vanishing
complementary transition maps. -/
theorem hasEventuallySplitLimit_iff [IsIdempotentComplete A] (F : SequentialInverseSystem A) :
    HasEventuallySplitLimit F ↔ HasLimitTailDecomposition F := sorry

/-- A sequential inverse system is essentially constant if and only if it admits the source-facing
tail decomposition from Lemma 12.31.5. -/
theorem essentiallyConstant_iff_hasLimitTailDecomposition [IsIdempotentComplete A]
    (F : SequentialInverseSystem A) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasLimitTailDecomposition F := by
  rw [essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit, hasEventuallySplitLimit_iff]

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_12_31_6 (from Chap12) -/
open CategoryTheory

universe u v

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {S : ShortComplex (SequentialInverseSystem A)}

/- Domain-style sampling for Lemma 12.31.6 in the sequential inverse-system domain:
- owner abstractions: `ShortComplex.ShortExact`,
  `SequentialInverseSystem.IsMittagLeffler`, and `IsEssentiallyConstantCofilteredDiagram`
- sampled chapter-level declarations:
  * `SequentialInverseSystem.IsMittagLeffler` in `Definition_12_31_2`
  * `ShortComplex.ShortExact` in the ambient abelian-category owner API
  * `SequentialInverseSystem.essentiallyConstant_iff_hasLimitTailDecomposition` in
    `Lemma_12_31_5`

This item is therefore `bridge/view`: the source lemma compares the two owner predicates across a
short exact sequence whose right term is controlled by the chapter-level essential-constancy
criterion. The statement should stay at that bridge layer rather than introduce any new wrapper
around the short exact sequence data. -/

-- Proof sketch: use the structure theorem for essentially constant sequential inverse systems from
-- Lemma 12.31.5 to reduce to a quotient that is eventually zero modulo a constant summand, and
-- then compare the stabilized images in the short exact sequence stagewise. The eventually zero
-- case identifies the middle images with successive left images, while the constant case preserves
-- stabilization because the quotients of the middle images are all canonically `C`.
/-- Lemma 12.31.6: in a short exact sequence of sequential inverse systems in an abelian category,
if the quotient inverse system is essentially constant, then the left inverse system is
Mittag-Leffler if and only if the middle inverse system is Mittag-Leffler. -/
theorem isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃
    (hS : S.ShortExact) (hC : IsEssentiallyConstantCofilteredDiagram S.X₃) :
    S.X₁.IsMittagLeffler ↔ S.X₂.IsMittagLeffler := sorry

end ShortComplex.ShortExact

end CategoryTheory

/-! ### Lemma_12_31_7 (from Chap12) -/
open CategoryTheory Opposite Limits ComplexShape

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbCpxSeq" => SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local notation "ev" => HomologicalComplex.eval AddCommGrpCat (up ℤ)
local notation "H" => HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)

/- Domain-style sampling for Lemma 12.31.7 in the inverse-limit/cohomology domain:
- owner abstractions:
  * `SequentialInverseSystem.IsMittagLeffler`
  * `IsEssentiallyConstantCofilteredDiagram`
  * `HomologicalComplex.eval`, `HomologicalComplex.homologyFunctor`, and
    `ShortComplex.ShortExact.homology_exact₂`
- sampled supporting declarations:
  * `SequentialInverseSystem.inverseLimit_shortExact_of_isMittagLeffler_left` in
    `Lemma_12_31_3`
  * `ShortComplex.ShortExact.isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃` in
    `Lemma_12_31_6`
  * `ShortComplex.ShortExact.homology_exact₂` in mathlib's
    `Algebra/Homology/HomologySequence`

This item is `source-facing`: its primitive data are the inverse system `A` together with the
Mittag-Leffler hypotheses on the degree `-2` and `-1` evaluation towers and the essential
constancy hypothesis on the degree `-1` homology tower. The comparison morphism
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is derived from the
owner functor `HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)`, so the public statement
should expose that canonical morphism directly rather than introduce any parallel wrapper API. -/

-- Proof sketch: form the short exact sequences of cocycles, objects, and coboundaries in degrees
-- `-1` and `0`; Lemma `12.31.3` gives exactness after taking inverse limits once the relevant
-- Mittag-Leffler conditions are known, and Lemma `12.31.6` upgrades the essential constancy of
-- `H^{-1}` to the Mittag-Leffler property for the cocycle tower. Chasing the resulting exact
-- sequences shows that the canonical map `H^0(lim A_i) ⟶ lim H^0(A_i)` is an isomorphism.
/-- Lemma 12.31.7: for a sequential inverse system of cochain complexes of abelian groups, if the
systems in degrees `-2` and `-1` are Mittag-Leffler and the degree `-1` cohomology system is
essentially constant, then the canonical comparison morphism
`H^0(\varprojlim A_i) \to \varprojlim H^0(A_i)` given by
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is an isomorphism. -/
theorem cohomologyLimitComparison_zero_isIso_of_isMittagLeffler_negTwo_negOne_and_essentiallyConstant_homology_negOne
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsEssentiallyConstantCofilteredDiagram (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := sorry

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_12_31_8 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ

variable {α : Ordinal.{u}}

/- Domain-style sampling for Lemma 12.31.8:
- primary domain: inverse limits of ordinal-indexed systems of cochain complexes of abelian groups;
- sampled core/canonical declarations:
  `HomologicalComplex.Acyclic`,
  `PrincipalSeg.cocone`,
  `coneOfCoconeRightOp`,
  `Functor.IsWellOrderContinuous.isColimitOfIsWellOrderContinuous`;
- best owner abstraction for the predecessor comparison map at `β`:
  the canonical predecessor cocone `(Set.principalSegIio β).cocone K.rightOp` and its standard
  opposite-side bridge `coneOfCoconeRightOp`;
- primitive data: the inverse system `K` and the canonical predecessor cocones indexed by
  `Set.principalSegIio β`;
- derived API: the canonical predecessor comparison morphism
  `ordinalCochainPredecessorComparison K β`, obtained by applying `limit.lift` to
  `coneOfCoconeRightOp ((Set.principalSegIio β).cocone K.rightOp)`;
- source/core/bridge triage:
  `source-facing`: the acyclicity lemma for the inverse-limit complex;
  `core/canonical`: `HomologicalComplex.Acyclic`, `PrincipalSeg.cocone`, and
    `coneOfCoconeRightOp`;
  `bridge/view`: the canonical comparison morphism
    `K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)` obtained from
    `limit.lift` on that canonical cone, used in the surjectivity hypothesis.

The file should therefore keep the canonical predecessor cocone direct, while naming only the
resulting comparison morphism that recurs in the source-facing surjectivity hypothesis. -/

-- Proof sketch: argue by transfinite induction on `β < α`. At successor stages, lift a
-- primitive for a cocycle and correct it using acyclicity of the previous stage together with
-- surjectivity in degree `n - 1`. At limit stages, use the inductive acyclicity of the
-- predecessor inverse limit together with the assumed degreewise surjectivity of the canonical
-- comparison morphism `K_β^\bullet ⟶ \lim_{\gamma < β} K_γ^\bullet` obtained from `limit.lift`
-- and the canonical predecessor cone `coneOfCoconeRightOp ((Set.principalSegIio β).cocone
-- K.rightOp)`.
-- The recursively constructed primitives assemble into a primitive in `limit K`.
/-- The canonical comparison morphism from the stage `β` of an ordinal-indexed inverse system of
cochain complexes to the inverse limit of the predecessor subsystem indexed by `γ < β`. -/
noncomputable def ordinalCochainPredecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) :
    K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K) :=
  limit.lift _ <|
    coneOfCoconeRightOp <|
      show Cocone ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).rightOp) from
        (Set.principalSegIio β).cocone K.rightOp

/-- Lemma 12.31.8: if an ordinal-indexed inverse system of cochain complexes of abelian groups is
stagewise acyclic and each degree component of the canonical comparison morphism
`ordinalCochainPredecessorComparison K β`
is surjective in every degree, then the inverse limit complex is acyclic. Here
`β : α.ToType` ranges over the ordinals `< α`. -/
lemma ordinalCochainLimit_acyclic_of_stagewise_acyclic_of_surjective_predecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom)) :
    (limit K).Acyclic := sorry
