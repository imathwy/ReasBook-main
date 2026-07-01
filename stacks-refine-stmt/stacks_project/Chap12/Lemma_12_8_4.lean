import Mathlib
import stacks_project.Chap04.Lemma_4_27_17
import stacks_project.Chap12.Lemma_12_8_2

-- Declarations for this item will be appended below by the statement pipeline.

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
