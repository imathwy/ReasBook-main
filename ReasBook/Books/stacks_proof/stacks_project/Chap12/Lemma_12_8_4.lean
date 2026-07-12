import Mathlib
import StacksProject_2024.Chap04.Lemma_4_27_17
import StacksProject_2024.Chap12.Lemma_12_8_2

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
@[stacks 05QG]
theorem localizationFunctor_preservesCokernels_of_left_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) S.Q := by
  letI : PreservesFiniteColimits S.Q :=
    show PreservesFiniteColimits S.Q from localization_Q_preservesFiniteColimits (W := S)
  infer_instance

end LeftPreservation

section ArrowIso

variable [HasZeroMorphisms S.Localization] [HasZeroObject S.Localization]

/-- Helper for Lemma 12.8.4: the left branch of an arrow isomorphism gives the left naturality
equation for the induced parallel-pair isomorphism. -/
lemma parallel_pair_iso_of_arrow_iso_left
    {X Y X' Y' : S.Localization} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    (parallelPair f 0).map WalkingParallelPairHom.left ≫ (Arrow.rightFunc.mapIso e).hom =
      (Arrow.leftFunc.mapIso e).hom ≫ (parallelPair g 0).map WalkingParallelPairHom.left := by
  -- Proof comment: the left branch is exactly the commutative square encoded by the arrow
  -- isomorphism `e`.
  simpa using (Arrow.w e.hom).symm

/-- Helper for Lemma 12.8.4: the zero branch of the induced parallel-pair isomorphism is
natural. -/
lemma parallel_pair_iso_of_arrow_iso_right
    {X Y X' Y' : S.Localization} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    (parallelPair f 0).map WalkingParallelPairHom.right ≫ (Arrow.rightFunc.mapIso e).hom =
      (Arrow.leftFunc.mapIso e).hom ≫ (parallelPair g 0).map WalkingParallelPairHom.right := by
  -- Proof comment: both composites are zero because the right branch of a parallel-pair diagram
  -- is the zero morphism.
  simp

/-- Helper for Lemma 12.8.4: an isomorphism between arrows induces an isomorphism between the
parallel-pair diagrams used to define kernels and cokernels. -/
def parallel_pair_iso_of_arrow_iso {X Y X' Y' : S.Localization} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    parallelPair f 0 ≅ parallelPair g 0 := by
  -- Proof comment: `parallelPairIso` packages the domain and codomain isomorphisms together with
  -- the two branch equalities proved just above.
  refine parallelPairIso f 0 g 0 (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) ?_ ?_
  · exact parallel_pair_iso_of_arrow_iso_left (e := e)
  · exact parallel_pair_iso_of_arrow_iso_right (e := e)

/-- Helper for Lemma 12.8.4: an arrow isomorphism transports cokernel existence backward. -/
lemma hasCokernel_of_arrow_iso
    {X Y X' Y' : S.Localization} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasCokernel g] :
    HasCokernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Proof comment: transport the canonical cokernel cofork of `g` across the source and target
  -- isomorphisms coming from the arrow square `e`.
  have hcomp : f ≫ (eY.hom ≫ cokernel.π g) = 0 := by
    calc
      f ≫ (eY.hom ≫ cokernel.π g) = (f ≫ eY.hom) ≫ cokernel.π g := by
        rw [Category.assoc]
      _ = (eX.hom ≫ g) ≫ cokernel.π g := by
        exact congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
      _ = eX.hom ≫ (g ≫ cokernel.π g) := by
        rw [Category.assoc]
      _ = 0 := by simp
  let cofork : CokernelCofork f := CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) hcomp
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_cofork : eY.inv ≫ cofork.π = cokernel.π g ≫ (Iso.refl _).hom := by
    simp [cofork]
  -- Proof comment: the universal property now follows from the universal property of the cokernel
  -- of `g`.
  refine ⟨⟨cofork, ?_⟩⟩
  exact IsCokernel.ofIso g (cokernelIsCokernel g) cofork eX.symm eY.symm (Iso.refl _)
    h_arrow h_cofork

/-- Helper for Lemma 12.8.4: an arrow isomorphism transports kernel existence backward. -/
lemma hasKernel_of_arrow_iso
    {X Y X' Y' : S.Localization} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasKernel g] :
    HasKernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Proof comment: transport the canonical kernel fork of `g` across the same arrow square.
  have hcomp : (kernel.ι g ≫ eX.inv) ≫ f = 0 := by
    calc
      (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (eX.inv ≫ f) := by
        rw [Category.assoc]
      _ = kernel.ι g ≫ (g ≫ eY.inv) := by
        exact congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
      _ = 0 := by simp
  let fork : KernelFork f := KernelFork.ofι (kernel.ι g ≫ eX.inv) hcomp
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_fork : (Iso.refl _).hom ≫ fork.ι = kernel.ι g ≫ eX.inv := by
    simp [fork]
  -- Proof comment: reuse the kernel universal property of `g` after rewriting through the arrow
  -- isomorphism.
  refine ⟨⟨fork, ?_⟩⟩
  exact IsKernel.ofIso g (kernelIsKernel g) fork eX.symm eY.symm (Iso.refl _) h_arrow h_fork

end ArrowIso

section MapParallelPair

variable [HasZeroMorphisms A] [HasZeroObject A]
variable [HasZeroMorphisms S.Localization] [HasZeroObject S.Localization]
variable [S.Q.PreservesZeroMorphisms]

/-- Helper for Lemma 12.8.4: mapping the source parallel-pair diagram through `Q` yields the
parallel-pair diagram of the mapped morphism. -/
def map_parallelPair_zero_iso {X Y : A} (f : X ⟶ Y) :
    parallelPair f 0 ⋙ S.Q ≅ parallelPair (S.Q.map f) 0 := by
  -- Proof comment: both diagrams have the same objects after applying `Q`, and their two arrows
  -- are exactly `S.Q.map f` and the preserved zero morphism.
  refine NatIso.ofComponents (fun j ↦ by cases j <;> exact Iso.refl _) (by
    rintro _ _ (_ | _ | _)
    · rfl
    · simpa using (Functor.map_zero S.Q : S.Q.map (0 : X ⟶ Y) = 0)
    · simp)

end MapParallelPair

section Left

variable [Preadditive A] [HasZeroObject A] [HasCokernels A] [S.HasLeftCalculusOfFractions]

local instance : HasZeroMorphisms A := inferInstance

noncomputable local instance : Preadditive S.Localization :=
  Localization.preadditive S.Q S

local instance : S.Q.Additive :=
  Localization.functor_additive S.Q S

local instance : S.Q.EssSurj :=
  Localization.essSurj S.Q S

local instance : HasZeroObject S.Localization :=
  Functor.hasZeroObject_of_additive S.Q

local instance : HasZeroMorphisms S.Localization := inferInstance

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

/-- Helper for Lemma 12.8.4: a represented arrow `Q(f)` already has its cokernel diagram because
`Q` preserves the source cokernel of `f`. -/
lemma localization_hasColimit_parallelPair_of_q_map
    {X Y : A} (f : X ⟶ Y) :
    HasColimit (parallelPair f 0 ⋙ S.Q) := by
  -- The source cokernel diagram exists in `A`, and `Q` carries it to a colimit diagram.
  letI : HasColimit (parallelPair f 0) := HasCokernels.has_colimit f
  letI : PreservesColimit (parallelPair f 0) S.Q :=
    localizationFunctor_preservesCokernels_of_left_multiplicative_system (S := S) f
  exact ⟨_, isColimitOfPreserves S.Q (colimit.isColimit (parallelPair f 0))⟩

/-- Helper for Lemma 12.8.4: a represented localized arrow `Q(f)` has a cokernel because the
represented source parallel-pair diagram already has a colimit. -/
lemma localization_hasCokernel_of_q_map
    {X Y : A} (f : X ⟶ Y) :
    HasCokernel (S.Q.map f) := by
  -- Proof comment: transfer the represented colimit diagram to the literal parallel-pair diagram
  -- of `S.Q.map f` using `map_parallelPair_zero_iso`.
  letI : HasColimit (parallelPair f 0 ⋙ S.Q) :=
    localization_hasColimit_parallelPair_of_q_map (S := S) f
  exact hasColimit_of_iso (map_parallelPair_zero_iso (S := S) f).symm

/-- Helper for Lemma 12.8.4: every localized arrow admits a cokernel diagram once `S` has left
calculus of fractions. -/
lemma localization_hasColimit_parallelPair_of_left_multiplicative_system
    {X Y : S.Localization} (f : X ⟶ Y) :
    HasColimit (parallelPair f 0) := by
  -- Proof comment: represent `f` by a mapped arrow `S.Q.map g.hom`, inherit its cokernel from
  -- the source category, and transport that owner back along the arrow-category isomorphism.
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow S.Q S).mem_essImage (Arrow.mk f)
  letI : HasCokernel (S.Q.map g.hom) := localization_hasCokernel_of_q_map (S := S) g.hom
  letI : HasCokernel f := hasCokernel_of_arrow_iso (e := e.symm)
  infer_instance

/-
Lemma 12.8.4 (1): if `S` is a left multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has cokernels.
-/
set_option backward.isDefEq.respectTransparency false in
/-- Part (1) of Chap12 Lemma 12 8 4: if `S` is a left multiplicative system in an abelian
category `A`, then the
localized category `S.Localization` has cokernels. -/
@[stacks 05QG]
noncomputable instance localization_hasCokernels_of_left_multiplicative_system
    : HasCokernels S.Localization where
  has_colimit := fun _ ↦ localization_hasColimit_parallelPair_of_left_multiplicative_system
    (S := S) _

end Left

section RightPreservation

variable [HasZeroMorphisms A] [S.HasRightCalculusOfFractions]

/-- Lemma 12.8.4 (4): if `S` is a right multiplicative system in an abelian category `A`, then the
canonical localization functor `Q : A ⥤ S.Localization` commutes with kernels. -/
@[stacks 05QG]
theorem localizationFunctor_preservesKernels_of_right_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) S.Q := by
  letI : PreservesFiniteLimits S.Q := Functor.IsLocalization.preservesFiniteLimits S S.Q
  infer_instance

end RightPreservation

section Right

variable [Preadditive A] [HasZeroObject A] [HasKernels A] [S.HasRightCalculusOfFractions]

local instance : HasZeroMorphisms A := inferInstance

noncomputable local instance : Preadditive S.Localization :=
  Localization.preadditiveOfHasRightCalculusOfFractions S.Q S

local instance : S.Q.Additive :=
  Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S

local instance : S.Q.EssSurj :=
  Localization.essSurj S.Q S

local instance : HasZeroObject S.Localization :=
  Functor.hasZeroObject_of_additive S.Q

local instance : HasZeroMorphisms S.Localization := inferInstance

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

/-- Helper for Lemma 12.8.4: a represented arrow `Q(f)` already has its kernel diagram because
`Q` preserves the source kernel of `f`. -/
lemma localization_hasLimit_parallelPair_of_q_map
    {X Y : A} (f : X ⟶ Y) :
    HasLimit (parallelPair f 0 ⋙ S.Q) := by
  -- The source kernel diagram exists in `A`, and `Q` carries it to a limit diagram.
  letI : HasLimit (parallelPair f 0) := HasKernels.has_limit f
  letI : PreservesLimit (parallelPair f 0) S.Q :=
    localizationFunctor_preservesKernels_of_right_multiplicative_system (S := S) f
  exact ⟨_, isLimitOfPreserves S.Q (limit.isLimit (parallelPair f 0))⟩

/-- Helper for Lemma 12.8.4: a represented localized arrow `Q(f)` has a kernel because the
represented source parallel-pair diagram already has a limit. -/
lemma localization_hasKernel_of_q_map
    {X Y : A} (f : X ⟶ Y) :
    HasKernel (S.Q.map f) := by
  -- Proof comment: transfer the represented limit diagram to the literal parallel-pair diagram of
  -- `S.Q.map f` using `map_parallelPair_zero_iso`.
  letI : HasLimit (parallelPair f 0 ⋙ S.Q) :=
    localization_hasLimit_parallelPair_of_q_map (S := S) f
  exact hasLimit_of_iso (map_parallelPair_zero_iso (S := S) f)

/-- Helper for Lemma 12.8.4: every localized arrow admits a kernel diagram once `S` has right
calculus of fractions. -/
lemma localization_hasLimit_parallelPair_of_right_multiplicative_system
    {X Y : S.Localization} (f : X ⟶ Y) :
    HasLimit (parallelPair f 0) := by
  -- Route correction: use the right-calculus `mapArrow` essential-surjectivity theorem directly,
  -- then transport the represented kernel owner back along the resulting arrow isomorphism.
  letI : Functor.EssSurj ((S.Q).mapArrow) :=
    Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions S.Q S
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (L := S.Q) (W := S)).mem_essImage (Arrow.mk f)
  letI : HasKernel (S.Q.map g.hom) := localization_hasKernel_of_q_map (S := S) g.hom
  letI : HasKernel f := hasKernel_of_arrow_iso (e := e.symm)
  infer_instance

/-
Lemma 12.8.4 (3): if `S` is a right multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has kernels.
-/
set_option backward.isDefEq.respectTransparency false in
/-- Lemma 12.8.4 (3): if `S` is a right multiplicative system in an abelian category `A`, then the
localized category `S.Localization` has kernels. -/
@[stacks 05QG]
noncomputable instance localization_hasKernels_of_right_multiplicative_system
    : HasKernels S.Localization where
  has_limit := fun _ ↦ localization_hasLimit_parallelPair_of_right_multiplicative_system
    (S := S) _

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

local instance : S.Q.EssSurj :=
  Localization.essSurj S.Q S

local instance : HasZeroObject S.Localization :=
  Functor.hasZeroObject_of_additive S.Q

local instance : HasZeroMorphisms S.Localization := inferInstance

local instance : S.Q.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive S.Q

omit [S.HasLeftCalculusOfFractions] in
/-- Helper for Lemma 12.8.4: under the left-induced preadditive structure on the localization, the
represented source parallel-pair diagram still has a limit after applying `Q`. -/
lemma localization_hasLimit_parallelPair_of_q_map_in_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    HasLimit (parallelPair f 0 ⋙ S.Q) := by
  -- Proof comment: the source kernel diagram exists in `A`, and the right-calculus preservation
  -- theorem carries it to a limit diagram in the localization.
  letI : HasLimit (parallelPair f 0) := HasKernels.has_limit f
  letI : PreservesLimit (parallelPair f 0) S.Q :=
    localizationFunctor_preservesKernels_of_right_multiplicative_system (S := S) f
  exact ⟨_, isLimitOfPreserves S.Q (limit.isLimit (parallelPair f 0))⟩

/-- Helper for Lemma 12.8.4: under the left-induced preadditive structure on the localization, a
represented localized arrow `Q(f)` has a kernel. -/
lemma localization_hasKernel_of_q_map_in_multiplicative_system
    {X Y : A} (f : X ⟶ Y) :
    HasKernel (S.Q.map f) := by
  -- Proof comment: identify the mapped source diagram with the literal parallel-pair diagram of
  -- `S.Q.map f`.
  letI : HasLimit (parallelPair f 0 ⋙ S.Q) :=
    localization_hasLimit_parallelPair_of_q_map_in_multiplicative_system (S := S) f
  exact hasLimit_of_iso (map_parallelPair_zero_iso (S := S) f)

/-- Helper for Lemma 12.8.4: under the left-induced preadditive structure on the localization, the
parallel-pair diagram of any localized arrow has a limit. -/
lemma localization_hasLimit_parallelPair_in_multiplicative_system
    {X Y : S.Localization} (f : X ⟶ Y) :
    HasLimit (parallelPair f 0) := by
  -- Route correction: rerun the represented-arrow kernel argument directly with the current
  -- left-induced zero-morphism structure, instead of transporting the earlier right-section proof
  -- across a non-definitional equality of zero-morphism instances.
  letI : Functor.EssSurj ((S.Q).mapArrow) :=
    Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions S.Q S
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (L := S.Q) (W := S)).mem_essImage (Arrow.mk f)
  letI : HasKernel (S.Q.map g.hom) :=
    localization_hasKernel_of_q_map_in_multiplicative_system (S := S) g.hom
  letI : HasKernel f := hasKernel_of_arrow_iso (e := e.symm)
  infer_instance

noncomputable local instance : HasKernels S.Localization where
  has_limit := fun _ ↦ localization_hasLimit_parallelPair_in_multiplicative_system (S := S) _

noncomputable local instance : HasCokernels S.Localization :=
  localization_hasCokernels_of_left_multiplicative_system (S := S)

/-- Helper for Lemma 12.8.4: the coimage-image comparison is an isomorphism for every localized
arrow once kernels and cokernels have been transported from the abelian source category. -/
lemma localization_coimageImageComparison_isIso
    {X Y : S.Localization} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f] [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)] :
    IsIso (Abelian.coimageImageComparison f) := by
  letI : PreservesFiniteLimits S.Q := Functor.IsLocalization.preservesFiniteLimits S S.Q
  letI : PreservesFiniteColimits S.Q :=
    show PreservesFiniteColimits S.Q from localization_Q_preservesFiniteColimits (W := S)
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  -- Proof comment: represent `f` by a mapped source arrow, then transfer the coimage-image
  -- comparison through the preservation isomorphism and the arrow-category isomorphism.
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow S.Q S).mem_essImage (Arrow.mk f)
  letI : HasKernel g.hom := HasKernels.has_limit g.hom
  letI : HasCokernel g.hom := HasCokernels.has_colimit g.hom
  letI : HasCokernel (kernel.ι g.hom) := HasCokernels.has_colimit (kernel.ι g.hom)
  letI : HasKernel (cokernel.π g.hom) := HasKernels.has_limit (cokernel.π g.hom)
  letI : HasKernel (S.Q.map g.hom) :=
    localization_hasKernel_of_q_map_in_multiplicative_system (S := S) g.hom
  letI : HasCokernel (S.Q.map g.hom) := localization_hasCokernel_of_q_map (S := S) g.hom
  letI : HasCokernel (kernel.ι (S.Q.map g.hom)) :=
    localization_hasColimit_parallelPair_of_left_multiplicative_system (S := S)
      (kernel.ι (S.Q.map g.hom))
  letI : HasKernel (cokernel.π (S.Q.map g.hom)) :=
    localization_hasLimit_parallelPair_in_multiplicative_system (S := S)
      (cokernel.π (S.Q.map g.hom))
  let arrowIso : Arrow.mk (S.Q.map g.hom) ≅ Arrow.mk f := e
  let iso : Arrow.mk (S.Q.map (Abelian.coimageImageComparison g.hom)) ≅
      Arrow.mk (Abelian.coimageImageComparison f) :=
    Abelian.PreservesCoimageImageComparison.iso S.Q g.hom ≪≫
      Abelian.coimageImageComparisonFunctor.mapIso arrowIso
  rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
  infer_instance

-- Proof sketch: a multiplicative system is both left and right, so the localization has kernels
-- and cokernels; then every arrow is isomorphic to `S.Q.map f`, and the coimage-image comparison
-- is inherited from the abelian category `A`.
set_option backward.isDefEq.respectTransparency false in
/-- Chap12 Lemma 12 8 4 (5): if `S` is a multiplicative system in an abelian category `A`, then the
localized category `S.Localization` is abelian. -/
@[stacks 05QG]
noncomputable instance localization_abelian_of_multiplicative_system
    : Abelian S.Localization := by
  letI : HasFiniteProducts S.Localization :=
    localization_hasFiniteProducts_of_left_calculus_of_fractions (S := S)
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasKernel f := by
    intro X Y f
    exact localization_hasLimit_parallelPair_in_multiplicative_system (S := S) f
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasCokernel f := by
    intro X Y f
    exact localization_hasColimit_parallelPair_of_left_multiplicative_system (S := S) f
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasCokernel (kernel.ι f) := by
    intro X Y f
    exact localization_hasColimit_parallelPair_of_left_multiplicative_system (S := S) (kernel.ι f)
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y), HasKernel (cokernel.π f) := by
    intro X Y f
    exact localization_hasLimit_parallelPair_in_multiplicative_system (S := S) (cokernel.π f)
  -- Proof comment: once kernels, cokernels, and finite products are in place, the comparison-map
  -- criterion is exactly the standard abelian-category constructor.
  letI : ∀ {X Y : S.Localization} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    exact localization_coimageImageComparison_isIso (S := S) f
  exact Abelian.ofCoimageImageComparisonIsIso

-- Proof sketch: exactness is the conjunction of preservation of finite limits and finite
-- colimits, which are precisely the localization owner theorems from 4.27.17 and 4.27.9.
omit [Abelian A] in
/-- Lemma 12.8.4 (6): if `S` is a multiplicative system in an abelian category `A`, then the
canonical localization functor `Q : A ⥤ S.Localization` is exact. -/
@[stacks 05QG]
theorem localizationFunctor_exact_of_multiplicative_system
    : exactFunctor A S.Localization S.Q :=
  letI : PreservesFiniteLimits S.Q := Functor.IsLocalization.preservesFiniteLimits S S.Q
  letI : PreservesFiniteColimits S.Q :=
    show PreservesFiniteColimits S.Q from localization_Q_preservesFiniteColimits (W := S)
  (exactFunctor_iff S.Q).2 ⟨inferInstance, inferInstance⟩

end Multiplicative

end

end CategoryTheory
