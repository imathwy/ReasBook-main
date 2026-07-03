import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_8_1 (from Chap12) -/
open CategoryTheory
open Opposite

universe w v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u} [Category.{w} D]
variable {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]

private theorem instPreadditiveUnop_eq (A : Type u) [Category.{v} A] [P : Preadditive A] :
    letI : Preadditive Aᵒᵖ := inferInstance
    instPreadditiveUnop A = P := by
  apply Preadditive.ext
  funext X Y
  apply AddCommGroup.ext
  ext f g
  simp only [Equiv.add_def]
  let e : (X ⟶ Y) ≃ ((opOp A).obj X ⟶ (opOp A).obj Y) :=
    (Functor.FullyFaithful.ofFullyFaithful (opOp A)).homEquiv
  have h : e f + e g = e (f + g) := by
    change f.op.op + g.op.op = (f + g).op.op
    simp
  change e.symm (e f + e g) = f + g
  rw [h, e.symm_apply_apply]

namespace Localization

/- Source/core/bridge triage for Lemma 12.8.1:
- source-facing: the main item states existence and uniqueness of a preadditive structure on a
  localization making the localization functor additive
- core/canonical owner: for left fractions, the owner is `Localization.preadditive L W` together
  with `Localization.functor_additive L W`
- bridge/view: for right fractions, pass to `L.op : Cᵒᵖ ⥤ Dᵒᵖ`, use the left-fraction owner there,
  and transport the resulting preadditive structure back along the chapter owner
  `instPreadditiveUnop` from Lemma 12.5.2. -/
/-- The preadditive structure on `D` induced from the opposite localization when `W` has a right
calculus of fractions. -/
@[reducible] noncomputable def preadditiveOfHasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    Preadditive D :=
  letI : Preadditive Dᵒᵖ := preadditive L.op W.op
  instPreadditiveUnop D

lemma functor_additive_of_hasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    letI := preadditiveOfHasRightCalculusOfFractions L W
    L.Additive := by
  letI : Preadditive Dᵒᵖ := preadditive L.op W.op
  letI : Preadditive D :=
    Preadditive.ofFullyFaithful ((opOpEquivalence D).symm.fullyFaithfulFunctor)
  letI : L.op.Additive := functor_additive L.op W.op
  letI : Functor.Additive (L.op.rightOp) := inferInstance
  letI : (unopUnop D).Additive := by
    simpa using Equivalence.additive_inverse_of_FullyFaithful ((opOpEquivalence D).symm)
  have hAdd : (L.op.rightOp ⋙ unopUnop D).Additive := inferInstance
  rw [preadditiveOfHasRightCalculusOfFractions, instPreadditiveUnop]
  convert hAdd using 1
  congr
  exact Subsingleton.elim _ _

end Localization

private lemma localization_preadditive_unique
    {A : Type*} [Category A] [Preadditive A]
    {B : Type*} [Category B] (S : MorphismProperty A) (F : A ⥤ B) [F.IsLocalization S]
    [S.HasLeftCalculusOfFractions]
    (P Q : Preadditive B)
    (hP : letI := P; F.Additive)
    (hQ : letI := Q; F.Additive) :
    P = Q := by
  letI := P
  letI : F.Additive := hP
  let B' := InducedCategory B id
  letI : Category B' := inferInstance
  letI : Preadditive B' := by
    letI := Q
    infer_instance
  let G : B ⥤ B' :=
    { obj := id
      map := fun f ↦ InducedCategory.homMk f }
  have hFG : (F ⋙ G).Additive := by
    letI := Q
    letI : F.Additive := hQ
    refine ⟨?_⟩
    intro X Y f g
    ext
    exact F.map_add
  have hG : G.Additive := (Localization.functor_additive_iff F S G).2 hFG
  apply Preadditive.ext
  funext X Y
  apply AddCommGroup.ext
  ext f g
  simpa [G] using congrArg InducedCategory.Hom.hom G.map_add

section LeftCalculusOfFractions

private lemma localization_existsUnique_preadditive_of_hasLeftCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasLeftCalculusOfFractions] :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  let P₀ : Preadditive D := Localization.preadditive L W
  have hP₀ : letI := P₀; L.Additive := by
    simpa [P₀] using (Localization.functor_additive L W)
  refine ⟨P₀, ?_, ?_⟩
  · exact hP₀
  · intro P hP
    exact localization_preadditive_unique W L P P₀ hP hP₀

end LeftCalculusOfFractions

section RightCalculusOfFractions

private lemma localization_existsUnique_preadditive_of_hasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  let P₀ : Preadditive D := Localization.preadditiveOfHasRightCalculusOfFractions L W
  refine ⟨P₀, ?_, ?_⟩
  · simpa [P₀] using Localization.functor_additive_of_hasRightCalculusOfFractions L W
  · intro P hP
    letI := P
    letI : L.Additive := hP
    let transport : Preadditive Dᵒᵖ → Preadditive D := fun R ↦
      letI : Preadditive Dᵒᵖ := R
      show Preadditive D from instPreadditiveUnop D
    have hP_op : letI := instPreadditiveOpposite D; L.op.Additive := by
      infer_instance
    have hP₀_op : instPreadditiveOpposite D = Localization.preadditive L.op W.op := by
      exact localization_preadditive_unique W.op L.op (instPreadditiveOpposite D)
        (Localization.preadditive L.op W.op) hP_op
        (Localization.functor_additive L.op W.op)
    have htransport : transport (instPreadditiveOpposite D) =
        transport (Localization.preadditive L.op W.op) := by
      exact congrArg transport hP₀_op
    have htransport_left : transport (instPreadditiveOpposite D) = P := by
      simpa [transport] using (instPreadditiveUnop_eq D)
    have htransport_right : transport (Localization.preadditive L.op W.op) = P₀ := by
      rfl
    calc
      P = transport (instPreadditiveOpposite D) := htransport_left.symm
      _ = transport (Localization.preadditive L.op W.op) := htransport
      _ = P₀ := htransport_right

end RightCalculusOfFractions

-- Proof sketch: in the left-fraction case, use the canonical construction
-- `CategoryTheory.Localization.preadditive L W` together with
-- `CategoryTheory.Localization.functor_additive L W`. In the right-fraction case, pass to the
-- opposite localization, apply the left-fraction construction there, and transfer the resulting
-- preadditive structure back across opposites.
/-- Lemma 12.8.1: if `C` is preadditive and `W` is a left or right multiplicative system, then
any localization functor `L : C ⥤ D` carries a unique preadditive structure on `D` for which `L`
is additive. -/
theorem localization_existsUnique_preadditive
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  rcases hW with hW | hW
  · letI := hW
    exact localization_existsUnique_preadditive_of_hasLeftCalculusOfFractions L W
  · letI := hW
    exact localization_existsUnique_preadditive_of_hasRightCalculusOfFractions L W

end CategoryTheory

/-! ### Lemma_12_8_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe t w v u

namespace CategoryTheory

open MorphismProperty
open Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : MorphismProperty C)

/- Domain-style sampling for Lemma 12.8.2:
- primary domain: additive localizations of preadditive categories;
- inspected owner declarations:
  `HasFiniteProducts`,
  `Functor.Additive`,
  `Localization.preadditive`,
  `Localization.functor_additive`;
- best owner abstraction: the additive-category half is expressed by
  `HasFiniteProducts S.Localization`, and the functorial half by `S.Q.Additive`;
- primitive data: the preadditive source category, the morphism property `S`, and the left/right
  calculus-of-fractions hypotheses;
- derived API: the induced preadditive structure on `S.Localization`, the additivity of `S.Q`,
  and the finite-product structure transported across an additive essentially surjective
  localization. -/

/- Source/core/bridge triage for Lemma 12.8.2:
- source-facing: the source lemma says the localization is an additive category and the
  localization functor `Q` is additive;
- core/canonical owners: `HasFiniteProducts S.Localization` and `S.Q.Additive`;
- bridge/view: the preadditive target structure comes from `Localization.preadditive` on the left
  and `Localization.preadditiveOfHasRightCalculusOfFractions` on the right, while
  `hasFiniteProducts_of_essSurj_additive` upgrades that preadditive target to the additive owner. -/

section

variable [HasFiniteProducts C]

private theorem hasFiniteProducts_of_essSurj_additive
    {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteProducts A]
    {B : Type w} [Category.{t} B] [Preadditive B] (L : A ⥤ B)
    [L.EssSurj] [L.Additive] : HasFiniteProducts B := by
  letI : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasZeroObject A := hasZeroObject_of_hasFiniteBiproducts A
  letI : PreservesFiniteProducts L := Functor.preservesFiniteProductsOfAdditive L
  letI : HasBinaryProducts B := by
    letI : HasBinaryBiproducts A := hasBinaryBiproducts_of_finite_biproducts A
    letI : HasBinaryProducts A := hasBinaryProducts_of_hasBinaryBiproducts
    have (X Y : B) : HasBinaryProduct X Y := by
      letI : HasLimit (pair (L.objPreimage X) (L.objPreimage Y)) := by infer_instance
      letI : HasLimit (pair (L.objPreimage X) (L.objPreimage Y) ⋙ L) :=
        ⟨_, isLimitOfPreserves L (limit.isLimit (pair (L.objPreimage X) (L.objPreimage Y)))⟩
      exact hasLimit_of_iso
        (show pair (L.objPreimage X) (L.objPreimage Y) ⋙ L ≅ pair X Y from
          mapPairIso (L.objObjPreimageIso X) (L.objObjPreimageIso Y))
    exact hasBinaryProducts_of_hasLimit_pair B
  letI : HasZeroObject B := Functor.hasZeroObject_of_additive L
  letI : HasTerminal B := HasZeroObject.hasTerminal
  exact hasFiniteProducts_of_has_binary_and_terminal

-- Proof sketch: in the left-fraction case, use the canonical preadditive owner on
-- `S.Localization` together with the finite-colimit construction available for left localizations,
-- and then recover the additive owner `HasFiniteProducts`. In the right-fraction case, pass to the
-- opposite localization, apply the left-fraction argument there, and transport the resulting
-- finite products back across opposites.
/-- A left-fraction localization of an additive category has finite products. -/
theorem localization_hasFiniteProducts_of_left_calculus_of_fractions
    [S.HasLeftCalculusOfFractions] : HasFiniteProducts S.Localization := by
  letI : Preadditive S.Localization := Localization.preadditive S.Q S
  letI : Additive S.Q := Localization.functor_additive S.Q S
  letI : EssSurj S.Q := Localization.essSurj S.Q S
  exact hasFiniteProducts_of_essSurj_additive S.Q

/-- A right-fraction localization of an additive category has finite products. -/
theorem localization_hasFiniteProducts_of_right_calculus_of_fractions
    [S.HasRightCalculusOfFractions] : HasFiniteProducts S.Localization := by
  letI : Preadditive S.Localizationᵒᵖ := Localization.preadditive S.Q.op S.op
  letI : Additive S.Q.op := Localization.functor_additive S.Q.op S.op
  letI : EssSurj S.Q.op := Localization.essSurj S.Q.op S.op
  letI : HasFiniteProducts S.Localizationᵒᵖ :=
    hasFiniteProducts_of_essSurj_additive S.Q.op
  exact instHasFiniteProductsUnop S.Localization

end

section

variable [S.HasLeftCalculusOfFractions]

/- Lemma 12.8.2, left-fraction additive-functor clause: once
`localization_hasFiniteProducts_of_left_calculus_of_fractions S` supplies finite products on
`S.Localization`, the additivity of the localization functor is the canonical owner theorem
`Localization.functor_additive S.Q S`. -/
#check Localization.functor_additive S.Q S

end

section

variable [S.HasRightCalculusOfFractions]

/- Lemma 12.8.2, right-fraction additive-functor clause: with the canonical preadditive structure
`Localization.preadditiveOfHasRightCalculusOfFractions S.Q S`, the additivity of the localization
functor is the chapter owner theorem
`Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S`. -/
#check Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S

end

end CategoryTheory

/-! ### Lemma_12_8_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
  (X : C)

/- Domain-style sampling for Lemma 12.8.3:
- primary domain: preadditive localizations by a morphism property and zero-object detection in the
  localized category;
- inspected owner declarations:
  `Localization.preadditive` together with the canonical instance `Preadditive S.Localization`,
  `Localization.functor_additive` together with the canonical instance `S.Q.Additive`,
  `MorphismProperty.map_eq_iff_postcomp`,
  `MorphismProperty.map_eq_iff_precomp`,
  `IsZero.iff_id_eq_zero`;
- best owner abstraction: the canonical localization functor `S.Q`, with zero-object detection
  expressed by the owner predicate `IsZero (S.Q.obj X)`;
- primitive data: the morphism property `S`, the object `X`, and the left/right
  calculus-of-fractions instances;
- derived API: the existence of zero morphisms out of or into `X` lying in `S`, recovered from the
  canonical localization equality criteria. -/

/- Source/core/bridge triage for Lemma 12.8.3:
- source-facing: the source criterion compares the vanishing of `S.Q.obj X` with the existence of
  zero morphisms into or out of `X` that lie in `S`
- core/canonical owners: `S.HasLeftCalculusOfFractions` and `S.HasRightCalculusOfFractions`,
  acting through the canonical localization functor `S.Q`
- bridge/view: `map_eq_iff_postcomp`, `map_eq_iff_precomp`, and `IsZero.iff_id_eq_zero` move
  between the source-level zero-morphism formulation and the canonical zero-object criterion in the
  localization -/
-- Proof sketch: in the additive localization, `IsZero (S.Q.obj X)` is equivalent to
-- `S.Q.map (𝟙 X) = S.Q.map 0`. The canonical localization comparison lemmas
-- `map_eq_iff_postcomp` and `map_eq_iff_precomp` translate this equality into the existence of a
-- morphism in `S` that equalizes `𝟙 X` and `0`, i.e. into a zero morphism out of or into `X`
-- belonging to `S`.
/-- Lemma 12.8.3: for an additive category localized at a multiplicative system `S`, the object
`S.Q.obj X` is zero exactly when some zero morphism out of `X` belongs to `S`, and exactly when
some zero morphism into `X` belongs to `S`. -/
theorem localization_object_isZero_tfae :
    List.TFAE [IsZero (S.Q.obj X), ∃ Y : C, S (0 : X ⟶ Y), ∃ Z : C, S (0 : Z ⟶ X)] := by
  tfae_have 1 ↔ 2 := by
    rw [IsZero.iff_id_eq_zero, ← S.Q.map_id, ← S.Q.map_zero, map_eq_iff_postcomp S.Q S (𝟙 X) 0]
    simp
  tfae_have 1 ↔ 3 := by
    rw [IsZero.iff_id_eq_zero, ← S.Q.map_id, ← S.Q.map_zero, map_eq_iff_precomp S.Q S (𝟙 X) 0]
    simp
  tfae_finish

end CategoryTheory

/-! ### Lemma_12_8_4 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

variable {A : Type u} [Category.{v} A]
variable (S : MorphismProperty A)

noncomputable section

/- Domain-style sampling for Lemma 12.8.4:
- primary domain: localization of an abelian category at a multiplicative system, with the owner
  abstractions `HasKernels`, `HasCokernels`, `Abelian`, `PreservesLimit`, `PreservesColimit`, and
  `exactFunctor`;
- inspected owner declarations:
  `Functor.IsLocalization.preservesFiniteLimits`,
  `Functor.IsLocalization.preservesFiniteColimits`,
  `Abelian.ofCoimageImageComparisonIsIso`,
  `ObjectProperty.SerreClassLocalization.hasKernels` /
  `ObjectProperty.SerreClassLocalization.hasCokernels`;
- best owner abstraction: the localized category should expose the canonical instance owners
  `HasKernels`, `HasCokernels`, and `Abelian`, while the numbered preservation statements remain
  thin source-facing bridges to `PreservesLimit` and `PreservesColimit`.

Primitive-vs-derived split:
- primitive data: the source category `A`, the morphism property `S`, zero morphisms for the
  parallel-pair preservation clauses, the left/right calculus-of-fractions hypotheses, the
  preadditive/zero-object/kernel-cokernel data needed for parts `(1)` and `(3)`, and the abelian
  structure needed for part `(5)`;
- derived API: the preadditive/additive localization data from Lemma 12.8.1, finite products from
  Lemma 12.8.2, finite-(co)limit preservation from Chapter 4, and the induced abelian/exact owner
  structure on `S.Localization`. -/

/- Source/core/bridge triage for Lemma 12.8.4:
- source-facing: the six numbered statements of the Stacks lemma;
- core/canonical: `HasCokernels`, `HasKernels`, `Abelian`, `PreservesLimit`,
  `PreservesColimit`, and `exactFunctor`;
- bridge/view: parts `(2)`, `(4)`, and `(6)` are thin source-facing bridges to the owner
  predicates, while parts `(1)`, `(3)`, and `(5)` are public instances proving the corresponding
  owner structure on `S.Localization`. -/

section LeftPreservation

variable [HasZeroMorphisms A] [S.HasLeftCalculusOfFractions]

/-- Lemma 12.8.4 (2): if `S` is a left multiplicative system in an abelian category `A`, then the
canonical localization functor `Q : A ⥤ S.Localization` commutes with cokernels. -/
theorem localizationFunctor_preservesCokernels_of_left_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) S.Q := inferInstance

end LeftPreservation

section Left

variable [Preadditive A] [HasZeroObject A] [HasCokernels A] [S.HasLeftCalculusOfFractions]

local instance : HasZeroMorphisms A := inferInstance

noncomputable local instance : Preadditive S.Localization :=
  Localization.preadditive S.Q S

local instance : S.Q.Additive :=
  Localization.functor_additive S.Q S

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

noncomputable local instance : HasZeroObject S.Localization :=
  S.Q.hasZeroObject_of_additive

/-
Lemma 12.8.4 (1): if `S` is a left multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has cokernels.
-/
set_option backward.isDefEq.respectTransparency false in
/-- Lemma 12.8.4 (1): if `S` is a left multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has cokernels. -/
noncomputable instance localization_hasCokernels_of_left_multiplicative_system
    : HasCokernels S.Localization where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow S.Q S).mem_essImage (Arrow.mk f)
    letI : PreservesColimit (parallelPair g.hom 0) S.Q := inferInstance
    letI : HasCokernel g.hom := HasCokernels.has_colimit g.hom
    have : HasColimit (parallelPair (S.Q.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ S.Q).1
        (isColimitOfPreserves S.Q (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show parallelPair f 0 ≅ parallelPair (S.Q.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm)
        (by simp) (by simp))

end Left

section RightPreservation

variable [HasZeroMorphisms A] [S.HasRightCalculusOfFractions]

/-- Lemma 12.8.4 (4): if `S` is a right multiplicative system in an abelian category `A`, then the
canonical localization functor `Q : A ⥤ S.Localization` commutes with kernels. -/
theorem localizationFunctor_preservesKernels_of_right_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) S.Q := inferInstance

end RightPreservation

section Right

variable [Preadditive A] [HasZeroObject A] [HasKernels A] [S.HasRightCalculusOfFractions]

local instance : HasZeroMorphisms A := inferInstance

noncomputable local instance : Preadditive S.Localization :=
  Localization.preadditiveOfHasRightCalculusOfFractions S.Q S

local instance : S.Q.Additive :=
  Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

noncomputable local instance : HasZeroObject S.Localization :=
  S.Q.hasZeroObject_of_additive

/-
Lemma 12.8.4 (3): if `S` is a right multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has kernels.
-/
set_option backward.isDefEq.respectTransparency false in
/-- Lemma 12.8.4 (3): if `S` is a right multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has kernels. -/
noncomputable instance localization_hasKernels_of_right_multiplicative_system
    : HasKernels S.Localization where
  has_limit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions S.Q S).mem_essImage
        (Arrow.mk f)
    letI : PreservesLimit (parallelPair g.hom 0) S.Q := inferInstance
    letI : HasLimit (parallelPair g.hom 0) := HasKernels.has_limit g.hom
    letI : HasLimit (parallelPair (S.Q.map g.hom) 0) :=
      ⟨⟨_, isLimitOfHasKernelOfPreservesLimit S.Q g.hom⟩⟩
    exact hasLimit_of_iso (show parallelPair (S.Q.map g.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
        (by simp) (by simp))

end Right

section Multiplicative

variable [Abelian A] [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

local instance : Preadditive A := ‹Abelian A›.toPreadditive
local instance : HasZeroObject A := inferInstance
local instance : HasKernels A := inferInstance
local instance : HasCokernels A := inferInstance
local instance : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
local instance : HasFiniteProducts A := Limits.hasFiniteProducts_of_hasFiniteBiproducts A

noncomputable local instance : Preadditive S.Localization :=
  Localization.preadditive S.Q S

local instance : S.Q.Additive :=
  Localization.functor_additive S.Q S

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

-- Proof sketch: a multiplicative system is both left and right, so the localization has kernels
-- and cokernels; then every arrow is isomorphic to `S.Q.map f`, and the coimage-image comparison
-- is inherited from the abelian category `A`.
set_option backward.isDefEq.respectTransparency false in
/-- Lemma 12.8.4 (5): if `S` is a multiplicative system in an abelian category `A`, then the
localized category `S.Localization` is abelian. -/
noncomputable instance localization_abelian_of_multiplicative_system
    : Abelian S.Localization := by
  letI : HasFiniteProducts S.Localization :=
    localization_hasFiniteProducts_of_left_calculus_of_fractions S
  letI : HasZeroObject S.Localization := S.Q.hasZeroObject_of_additive
  letI : HasCokernels S.Localization :=
    localization_hasCokernels_of_left_multiplicative_system S
  letI : HasKernels S.Localization :=
    by
      refine ⟨?_⟩
      intro X Y f
      obtain ⟨g, ⟨e⟩⟩ :=
        (Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions S.Q S).mem_essImage
          (Arrow.mk f)
      letI : PreservesLimit (parallelPair g.hom 0) S.Q := inferInstance
      letI : HasLimit (parallelPair g.hom 0) := HasKernels.has_limit g.hom
      letI : HasLimit (parallelPair (S.Q.map g.hom) 0) :=
        ⟨⟨_, isLimitOfHasKernelOfPreservesLimit S.Q g.hom⟩⟩
      exact hasLimit_of_iso (show parallelPair (S.Q.map g.hom) 0 ≅ parallelPair f 0 from
        parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
          (by simp) (by simp))
  letI : PreservesFiniteLimits S.Q := inferInstance
  letI : PreservesFiniteColimits S.Q := inferInstance
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasKernel f := fun {X Y} f ↦
    HasKernels.has_limit f
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasCokernel f := fun {X Y} f ↦
    HasCokernels.has_colimit f
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasKernel (cokernel.π f) := fun {X Y} f ↦
    HasKernels.has_limit (cokernel.π f)
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasCokernel (kernel.ι f) := fun {X Y} f ↦
    HasCokernels.has_colimit (kernel.ι f)
  have hcoimageImage {X Y : S.Localization} (f : X ⟶ Y)
      [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)] :
      IsIso (Abelian.coimageImageComparison f) := by
    obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow S.Q S).mem_essImage (Arrow.mk f)
    letI : HasKernel g.hom := HasKernels.has_limit g.hom
    letI : HasCokernel g.hom := HasCokernels.has_colimit g.hom
    letI : HasKernel (cokernel.π g.hom) := HasKernels.has_limit (cokernel.π g.hom)
    letI : HasCokernel (kernel.ι g.hom) := HasCokernels.has_colimit (kernel.ι g.hom)
    letI : HasKernel (S.Q.map g.hom) := HasKernels.has_limit (S.Q.map g.hom)
    letI : HasCokernel (S.Q.map g.hom) := HasCokernels.has_colimit (S.Q.map g.hom)
    letI : HasKernel (cokernel.π (S.Q.map g.hom)) :=
      HasKernels.has_limit (cokernel.π (S.Q.map g.hom))
    letI : HasCokernel (kernel.ι (S.Q.map g.hom)) :=
      HasCokernels.has_colimit (kernel.ι (S.Q.map g.hom))
    let iso :
        Arrow.mk (S.Q.map (Abelian.coimageImageComparison g.hom)) ≅
          Arrow.mk (Abelian.coimageImageComparison f) :=
      Abelian.PreservesCoimageImageComparison.iso S.Q g.hom ≪≫
        Abelian.coimageImageComparisonFunctor.mapIso e
    rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
    infer_instance
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    letI : HasKernel f := HasKernels.has_limit f
    letI : HasCokernel f := HasCokernels.has_colimit f
    letI : HasKernel (cokernel.π f) := HasKernels.has_limit (cokernel.π f)
    letI : HasCokernel (kernel.ι f) := HasCokernels.has_colimit (kernel.ι f)
    exact hcoimageImage f
  exact Abelian.ofCoimageImageComparisonIsIso

-- Proof sketch: exactness is the conjunction of preservation of finite limits and finite
-- colimits, which are precisely the localization owner theorems from 4.27.17 and 4.27.9.
omit [Abelian A] in
/-- Lemma 12.8.4 (6): if `S` is a multiplicative system in an abelian category `A`, then the
canonical localization functor `Q : A ⥤ S.Localization` is exact. -/
theorem localizationFunctor_exact_of_multiplicative_system
    : exactFunctor A S.Localization S.Q :=
  (exactFunctor_iff S.Q).2 ⟨inferInstance, inferInstance⟩

end Multiplicative

end

end CategoryTheory
