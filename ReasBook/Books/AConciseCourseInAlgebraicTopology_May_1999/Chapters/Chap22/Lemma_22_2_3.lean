import Mathlib.Topology.Homotopy.HSpaces
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.HomotopyClasses

noncomputable section

open scoped HSpaces

universe u

-- Chapter 7 already owns the canonical quotient of `C(X, Z)` by `ContinuousMap.Homotopic`.
-- This file keeps the textbook Chapter 22 surface `[X,Z]` as a thin bridge to that owner and
-- equips it with the induced `HSpace` operations.

/-- The type `homotopyClasses X Z` formalizes the unbased homotopy classes `[X,Z]` using the
canonical Chapter 7 owner `continuousMapHomotopyClasses X Z`. -/
abbrev homotopyClasses (X Z : Type u) [TopologicalSpace X] [TopologicalSpace Z] :=
  continuousMapHomotopyClasses X Z

/-- Lean notation for the unbased homotopy-class object formalizing textbook `[X,Z]`. -/
scoped[HomotopyClasses] notation "Ho[" X ", " Z "]" => homotopyClasses X Z

open scoped HomotopyClasses

section HSpaceMaps

variable (Z : Type u) [TopologicalSpace Z] [HSpace Z]

/-- The left-associated pointwise `HSpace` multiplication on triples of points of `Z`. -/
def hSpaceAssocLeft : C(Z × (Z × Z), Z) :=
  ⟨fun p ↦ (p.1 ⋀ p.2.1) ⋀ p.2.2, by
    fun_prop⟩

/-- The right-associated pointwise `HSpace` multiplication on triples of points of `Z`. -/
def hSpaceAssocRight : C(Z × (Z × Z), Z) :=
  ⟨fun p ↦ p.1 ⋀ (p.2.1 ⋀ p.2.2), by
    fun_prop⟩

/-- The pointwise multiplication map with the two inputs swapped. -/
def hSpaceMulSwap : C(Z × Z, Z) :=
  ⟨fun p ↦ p.2 ⋀ p.1, by
    fun_prop⟩

/-- The pointwise left-inverse candidate attached to a map `inv : C(Z, Z)`. -/
def hSpaceLeftInverseMap (inv : C(Z, Z)) : C(Z, Z) :=
  HSpace.hmul.comp (inv.prodMk (ContinuousMap.id Z))

/-- The pointwise right-inverse candidate attached to a map `inv : C(Z, Z)`. -/
def hSpaceRightInverseMap (inv : C(Z, Z)) : C(Z, Z) :=
  HSpace.hmul.comp ((ContinuousMap.id Z).prodMk inv)

end HSpaceMaps

namespace HSpace

section

variable (Z : Type u) [TopologicalSpace Z] [HSpace Z]

/-- A homotopy-associative `HSpace` has multiplication homotopic to its right-associated form on
triples. -/
class IsHomotopyAssociative : Prop where
  homotopic_assoc : ContinuousMap.Homotopic (hSpaceAssocLeft Z) (hSpaceAssocRight Z)

/-- A homotopy-commutative `HSpace` has multiplication homotopic to its twist. -/
class IsHomotopyCommutative : Prop where
  homotopic_mul_swap : ContinuousMap.Homotopic (HSpace.hmul : C(Z × Z, Z)) (hSpaceMulSwap Z)

/-- A grouplike `HSpace` comes with a chosen homotopy inverse on both sides. -/
class Grouplike where
  inv : C(Z, Z)
  left_inv :
    ContinuousMap.Homotopic (hSpaceLeftInverseMap Z inv) (ContinuousMap.const Z HSpace.e)
  right_inv :
    ContinuousMap.Homotopic (hSpaceRightInverseMap Z inv) (ContinuousMap.const Z HSpace.e)

end

end HSpace

section HomotopyClasses

open HSpace

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z] [HSpace Z]

/-- Pointwise `HSpace` multiplication respects homotopy classes of maps `X ⟶ Z`. -/
theorem hSpaceMul_wellDefined
    {f₀ f₁ g₀ g₁ : C(X, Z)}
    (hf : ContinuousMap.Homotopic f₀ f₁) (hg : ContinuousMap.Homotopic g₀ g₁) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp (f₀.prodMk g₀))
      (HSpace.hmul.comp (f₁.prodMk g₁)) := by
  -- First descend the pair of representatives to a homotopy of product maps.
  exact ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl HSpace.hmul)
    (ContinuousMap.Homotopic.prodMk hf hg)

/-- Pointwise `HSpace` multiplication descends to unbased homotopy classes. -/
def homotopyClassesMul (a b : Ho[X, Z]) : Ho[X, Z] :=
  Quotient.map₂
    (fun f g : C(X, Z) ↦ HSpace.hmul.comp (f.prodMk g))
    (fun _ _ hf _ _ hg ↦ hSpaceMul_wellDefined hf hg)
    a b

instance : Mul Ho[X, Z] where
  mul := homotopyClassesMul

/-- The unit homotopy class in `[X,Z]`, represented by the constant map at `HSpace.e`. -/
def homotopyClassesOne : Ho[X, Z] :=
  Quotient.mk (continuousMapHomotopySetoid X Z) (ContinuousMap.const X HSpace.e)

instance : One Ho[X, Z] where
  one := homotopyClassesOne

instance [g : HSpace.Grouplike Z] : Inv Ho[X, Z] where
  inv := continuousMapHomotopyClassesPostcompose g.inv

@[simp] theorem homotopyClasses_mul_mk (f g : C(X, Z)) :
    (Quotient.mk (continuousMapHomotopySetoid X Z) f : Ho[X, Z]) *
        Quotient.mk (continuousMapHomotopySetoid X Z) g =
      Quotient.mk (continuousMapHomotopySetoid X Z) (HSpace.hmul.comp (f.prodMk g)) :=
  rfl

@[simp] theorem homotopyClasses_one_def :
    (1 : Ho[X, Z]) =
      Quotient.mk (continuousMapHomotopySetoid X Z) (ContinuousMap.const X HSpace.e) :=
  rfl

@[simp] theorem homotopyClasses_inv_mk [g : HSpace.Grouplike Z] (f : C(X, Z)) :
    ((Quotient.mk (continuousMapHomotopySetoid X Z) f : Ho[X, Z])⁻¹ : Ho[X, Z]) =
      Quotient.mk (continuousMapHomotopySetoid X Z) (g.inv.comp f) :=
  rfl

/-- Helper for Lemma 22.2.3: precomposing the homotopy-associativity of `Z` with three
representatives gives associativity up to homotopy on pointwise products of maps `X ⟶ Z`. -/
theorem pointwiseMulAssocHomotopic
    [HSpace.IsHomotopyAssociative Z]
    (f g h : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp ((HSpace.hmul.comp (f.prodMk g)).prodMk h))
      (HSpace.hmul.comp (f.prodMk (HSpace.hmul.comp (g.prodMk h)))) := by
  -- Precompose the associativity homotopy on `Z` with the triple of representatives.
  simpa [hSpaceAssocLeft, hSpaceAssocRight] using
    ContinuousMap.Homotopic.comp
      (HSpace.IsHomotopyAssociative.homotopic_assoc (Z := Z))
      (ContinuousMap.Homotopic.refl (f.prodMk (g.prodMk h)))

/-- Helper for Lemma 22.2.3: the constant representative at `HSpace.e` acts by left unit up to
homotopy on maps `X ⟶ Z`. -/
theorem pointwiseOneMulHomotopic
    (f : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp ((ContinuousMap.const X HSpace.e).prodMk f))
      f := by
  -- Precompose the left-unit homotopy on `Z` with the representative `f`.
  simpa using
    ContinuousMap.Homotopic.comp
      (show ContinuousMap.Homotopic
          (HSpace.hmul.comp
            ((ContinuousMap.const Z HSpace.e).prodMk (ContinuousMap.id Z)))
          (ContinuousMap.id Z) from
        ⟨HSpace.eHmul.toHomotopy⟩)
      (ContinuousMap.Homotopic.refl f)

/-- Helper for Lemma 22.2.3: the constant representative at `HSpace.e` acts by right unit up to
homotopy on maps `X ⟶ Z`. -/
theorem pointwiseMulOneHomotopic
    (f : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp (f.prodMk (ContinuousMap.const X HSpace.e)))
      f := by
  -- Precompose the right-unit homotopy on `Z` with the representative `f`.
  simpa using
    ContinuousMap.Homotopic.comp
      (show ContinuousMap.Homotopic
          (HSpace.hmul.comp
            ((ContinuousMap.id Z).prodMk (ContinuousMap.const Z HSpace.e)))
          (ContinuousMap.id Z) from
        ⟨HSpace.hmulE.toHomotopy⟩)
      (ContinuousMap.Homotopic.refl f)

/-- Helper for Lemma 22.2.3: precomposing the chosen left inverse on `Z` with a representative
gives the left inverse law up to homotopy on maps `X ⟶ Z`. -/
theorem pointwiseInvMulHomotopic
    [g : HSpace.Grouplike Z]
    (f : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp ((g.inv.comp f).prodMk f))
      (ContinuousMap.const X HSpace.e) := by
  -- Precompose the chosen left-inverse homotopy on `Z` with the representative `f`.
  simpa [hSpaceLeftInverseMap] using
    ContinuousMap.Homotopic.comp g.left_inv (ContinuousMap.Homotopic.refl f)

/-- Helper for Lemma 22.2.3: precomposing the chosen right inverse on `Z` with a representative
gives the right inverse law up to homotopy on maps `X ⟶ Z`. -/
theorem pointwiseMulInvHomotopic
    [g : HSpace.Grouplike Z]
    (f : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp (f.prodMk (g.inv.comp f)))
      (ContinuousMap.const X HSpace.e) := by
  -- Precompose the chosen right-inverse homotopy on `Z` with the representative `f`.
  simpa [hSpaceRightInverseMap] using
    ContinuousMap.Homotopic.comp g.right_inv (ContinuousMap.Homotopic.refl f)

/-- Helper for Lemma 22.2.3: precomposing the homotopy-commutativity of `Z` with two
representatives gives commutativity up to homotopy on pointwise products of maps `X ⟶ Z`. -/
theorem pointwiseMulCommHomotopic
    [HSpace.IsHomotopyCommutative Z]
    (f g : C(X, Z)) :
    ContinuousMap.Homotopic
      (HSpace.hmul.comp (f.prodMk g))
      (HSpace.hmul.comp (g.prodMk f)) := by
  -- Precompose the commutativity homotopy on `Z` with the pair of representatives.
  simpa [hSpaceMulSwap] using
    ContinuousMap.Homotopic.comp
      (HSpace.IsHomotopyCommutative.homotopic_mul_swap (Z := Z))
      (ContinuousMap.Homotopic.refl (f.prodMk g))

/-- Associativity of the induced multiplication on `[X,Z]`, assuming homotopy associativity of
the `HSpace` structure on `Z`. -/
theorem homotopyClasses_mul_assoc
    [HSpace.IsHomotopyAssociative Z]
    (a b c : Ho[X, Z]) :
    (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro f g h
  -- Reduce the quotient identity to associativity on representatives.
  apply Quotient.sound
  simpa [homotopyClassesMul] using pointwiseMulAssocHomotopic (X := X) (Z := Z) f g h

/-- The constant class at `HSpace.e` acts as a left unit on `[X,Z]`. -/
theorem homotopyClasses_one_mul
    (a : Ho[X, Z]) :
    1 * a = a := by
  refine Quotient.inductionOn a ?_
  intro f
  -- Reduce the quotient identity to the left-unit homotopy on representatives.
  apply Quotient.sound
  simpa [homotopyClassesOne, homotopyClassesMul] using pointwiseOneMulHomotopic (X := X) (Z := Z) f

/-- The constant class at `HSpace.e` acts as a right unit on `[X,Z]`. -/
theorem homotopyClasses_mul_one
    (a : Ho[X, Z]) :
    a * 1 = a := by
  refine Quotient.inductionOn a ?_
  intro f
  -- Reduce the quotient identity to the right-unit homotopy on representatives.
  apply Quotient.sound
  simpa [homotopyClassesOne, homotopyClassesMul] using pointwiseMulOneHomotopic (X := X) (Z := Z) f

/-- A chosen homotopy inverse induces the `inv_mul_cancel` law on `[X,Z]`. -/
theorem homotopyClasses_inv_mul_cancel
    [HSpace.Grouplike Z]
    (a : Ho[X, Z]) :
    a⁻¹ * a = 1 := by
  refine Quotient.inductionOn a ?_
  intro f
  -- Reduce the quotient identity to the left inverse homotopy on representatives.
  apply Quotient.sound
  simpa [homotopyClassesOne, homotopyClassesMul] using pointwiseInvMulHomotopic (X := X) (Z := Z) f

/-- A chosen homotopy inverse also induces the right cancellation law on `[X,Z]`. -/
theorem homotopyClasses_mul_inv_cancel
    [HSpace.Grouplike Z]
    (a : Ho[X, Z]) :
    a * a⁻¹ = 1 := by
  refine Quotient.inductionOn a ?_
  intro f
  -- Reduce the quotient identity to the right inverse homotopy on representatives.
  apply Quotient.sound
  simpa [homotopyClassesOne, homotopyClassesMul] using pointwiseMulInvHomotopic (X := X) (Z := Z) f

/-- Pointwise homotopy commutativity of `Z` induces commutativity on `[X,Z]`. -/
theorem homotopyClasses_mul_comm
    [HSpace.IsHomotopyCommutative Z]
    (a b : Ho[X, Z]) :
    a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro f g
  -- Reduce the quotient identity to commutativity on representatives.
  apply Quotient.sound
  simpa [homotopyClassesMul] using pointwiseMulCommHomotopic (X := X) (Z := Z) f g

/-- A homotopy-associative grouplike `HSpace` gives `[X,Z]` its induced group structure. -/
instance homotopyClassesGroup
    [HSpace.IsHomotopyAssociative Z] [HSpace.Grouplike Z] :
    Group Ho[X, Z] where
  mul := homotopyClassesMul
  one := homotopyClassesOne
  inv a := a⁻¹
  mul_assoc := homotopyClasses_mul_assoc
  one_mul := homotopyClasses_one_mul
  mul_one := homotopyClasses_mul_one
  inv_mul_cancel := homotopyClasses_inv_mul_cancel

/-- Lemma 22.2.3: if `Z` is a grouplike homotopy-associative and homotopy-commutative `HSpace`,
then `Ho[X, Z]`, formalizing `[X,Z]`, carries the induced canonical abelian group structure. The
grouplike hypothesis is recorded by `HSpace.Grouplike Z`, which stores a chosen two-sided
homotopy inverse. -/
instance homotopyClassesCommGroup
    [HSpace.IsHomotopyAssociative Z] [HSpace.IsHomotopyCommutative Z] [HSpace.Grouplike Z] :
    CommGroup Ho[X, Z] :=
  { (homotopyClassesGroup : Group Ho[X, Z]) with
      mul_comm := homotopyClasses_mul_comm }

end HomotopyClasses
