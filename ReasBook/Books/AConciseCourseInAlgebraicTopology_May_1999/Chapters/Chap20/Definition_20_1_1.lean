import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.LocallyConstant.Basic

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u

private abbrev puncturedPoint (X : Type u) [TopologicalSpace X] (x₀ : X) := {x : X // x ≠ x₀}

/-- The constant coefficient module `Coeff` in `ModuleCat Coeff`. -/
abbrev constantCoefficientModule (Coeff : Type u) [CommRing Coeff] :
    ModuleCat.{u} Coeff :=
  ModuleCat.of.{u} Coeff (ULift Coeff)

def puncturedPointInclusion {X : Type u} [TopologicalSpace X] (x₀ : X) :
    TopCat.of (puncturedPoint X x₀) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private abbrev constantCoefficientSingularChainFunctor (Coeff : Type u) [CommRing Coeff] :
    TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} Coeff) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} Coeff)).obj
    (constantCoefficientModule Coeff)

private abbrev nthHomologyFunctor (Coeff : Type u) [CommRing Coeff] (n : ℕ) :
    ChainComplex (ModuleCat.{u} Coeff) ℕ ⥤ ModuleCat.{u} Coeff :=
  HomologicalComplex.homologyFunctor (ModuleCat.{u} Coeff) (ComplexShape.down ℕ) n

abbrev localTopHomologyGroup (Coeff : Type u) [CommRing Coeff] (n : ℕ) (X : Type u)
    [TopologicalSpace X] (x₀ : X) : ModuleCat.{u} Coeff :=
  (nthHomologyFunctor Coeff n).obj
    (cokernel ((constantCoefficientSingularChainFunctor Coeff).map (puncturedPointInclusion x₀)))

abbrev subspaceComplement (X : Type u) [TopologicalSpace X] (Y : Set X) :=
  { y : X // y ∉ Y }

abbrev subspaceComplementInclusion (X : Type u) [TopologicalSpace X] (Y : Set X) :
    TopCat.of (subspaceComplement X Y) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

abbrev subspaceComplementMapOfSubset
    (X : Type u) [TopologicalSpace X] {Y Z : Set X} (hYZ : Y ⊆ Z) :
    TopCat.of (subspaceComplement X Z) ⟶ TopCat.of (subspaceComplement X Y) :=
  TopCat.ofHom
    ⟨fun z ↦ ⟨z.1, fun hzY ↦ (show ¬ z.1 ∈ Z from z.2) (hYZ hzY)⟩,
      continuous_subtype_val.subtype_mk fun z hzY ↦
        (show ¬ z.1 ∈ Z from z.2) (hYZ hzY)⟩

theorem subspaceComplementInclusion_eq_subspaceComplementMapOfSubset_comp
    (X : Type u) [TopologicalSpace X] {Y Z : Set X} (hYZ : Y ⊆ Z) :
    subspaceComplementInclusion X Z =
      subspaceComplementMapOfSubset X hYZ ≫ subspaceComplementInclusion X Y := by
  ext z
  rfl

private abbrev subspaceComplementToPuncturedPoint
    (X : Type u) [TopologicalSpace X] (Y : Set X) (x : X)
    (hx : x ∈ Y) : TopCat.of (subspaceComplement X Y) ⟶ TopCat.of (puncturedPoint X x) :=
  TopCat.ofHom
    ⟨fun y ↦ ⟨y.1, fun hxy : y.1 = x ↦ (show ¬ y.1 ∈ Y from y.2) (hxy.symm ▸ hx)⟩,
      Continuous.subtype_mk continuous_subtype_val
        fun y (hxy : y.1 = x) ↦ (show ¬ y.1 ∈ Y from y.2) (hxy.symm ▸ hx)⟩

private theorem subspaceComplementInclusion_eq_subspaceComplementToPuncturedPoint_comp
    (X : Type u) [TopologicalSpace X] (Y : Set X) (x : X) (hx : x ∈ Y) :
    subspaceComplementInclusion X Y =
      subspaceComplementToPuncturedPoint X Y x hx ≫ puncturedPointInclusion x := by
  ext y
  rfl

abbrev relativeTopHomologyGroup (Coeff : Type u) [CommRing Coeff] (n : ℕ) (X : Type u)
    [TopologicalSpace X] (Y : Set X) : ModuleCat.{u} Coeff :=
  let F := constantCoefficientSingularChainFunctor Coeff
  (nthHomologyFunctor Coeff n).obj
    (cokernel (F.map (subspaceComplementInclusion X Y)))

def relativeTopHomologyRestrict (Coeff : Type u) [CommRing Coeff] (n : ℕ) (X : Type u)
    [TopologicalSpace X] (Y Z : Set X) (hYZ : Y ⊆ Z) :
    relativeTopHomologyGroup Coeff n X Z ⟶ relativeTopHomologyGroup Coeff n X Y :=
  let F := constantCoefficientSingularChainFunctor Coeff
  let w :
      F.map (subspaceComplementInclusion X Z) ≫ 𝟙 _ =
        F.map (subspaceComplementMapOfSubset X hYZ) ≫
          F.map (subspaceComplementInclusion X Y) :=
    calc
      F.map (subspaceComplementInclusion X Z) ≫ 𝟙 _ =
          F.map (subspaceComplementInclusion X Z) := Category.comp_id _
      _ =
          F.map (subspaceComplementMapOfSubset X hYZ ≫ subspaceComplementInclusion X Y) :=
        congrArg F.map
          (subspaceComplementInclusion_eq_subspaceComplementMapOfSubset_comp X hYZ)
      _ =
          F.map (subspaceComplementMapOfSubset X hYZ) ≫
            F.map (subspaceComplementInclusion X Y) := F.map_comp _ _
  (nthHomologyFunctor Coeff n).map
    (cokernel.map
      (F.map (subspaceComplementInclusion X Z))
      (F.map (subspaceComplementInclusion X Y))
      (F.map (subspaceComplementMapOfSubset X hYZ))
      (𝟙 _)
      w)

def relativeToLocalTopHomologyMap (Coeff : Type u) [CommRing Coeff] (n : ℕ) (X : Type u)
    [TopologicalSpace X] (Y : Set X) {x : X} (hx : x ∈ Y) :
    relativeTopHomologyGroup Coeff n X Y ⟶ localTopHomologyGroup Coeff n X x :=
  let F := constantCoefficientSingularChainFunctor Coeff
  let w :
      F.map (subspaceComplementInclusion X Y) ≫ 𝟙 _ =
        F.map (subspaceComplementToPuncturedPoint X Y x hx) ≫
          F.map (puncturedPointInclusion x) :=
    calc
      F.map (subspaceComplementInclusion X Y) ≫ 𝟙 _ =
          F.map (subspaceComplementInclusion X Y) := Category.comp_id _
      _ =
          F.map (subspaceComplementToPuncturedPoint X Y x hx ≫ puncturedPointInclusion x) :=
        congrArg F.map
          (subspaceComplementInclusion_eq_subspaceComplementToPuncturedPoint_comp X Y x hx)
      _ =
          F.map (subspaceComplementToPuncturedPoint X Y x hx) ≫
            F.map (puncturedPointInclusion x) := F.map_comp _ _
  (nthHomologyFunctor Coeff n).map
    (cokernel.map
      (F.map (subspaceComplementInclusion X Y))
      (F.map (puncturedPointInclusion x))
      (F.map (subspaceComplementToPuncturedPoint X Y x hx))
      (𝟙 _)
      w)

def unitModuleIso (Coeff : Type u) [CommRing Coeff] (unit : Coeffˣ) :
    constantCoefficientModule Coeff ≅ constantCoefficientModule Coeff :=
  LinearEquiv.toModuleIso <|
    (ULift.moduleEquiv (R := Coeff) (M := Coeff)).trans
      ((unit.mulRightLinearEquiv Coeff).trans
        (ULift.moduleEquiv (R := Coeff) (M := Coeff)).symm)

structure LocalTopHomologyTrivialization (Coeff : Type u) [CommRing Coeff] (n : ℕ) (X : Type u)
    [TopologicalSpace X] where
  domain : Set X
  isOpen_domain : IsOpen domain
  localOrientationClass : relativeTopHomologyGroup Coeff n X domain
  identify :
    ∀ x : domain, localTopHomologyGroup Coeff n X x.1 ≅ constantCoefficientModule Coeff
  identify_localOrientationClass :
    ∀ x : domain,
      (identify x).hom
          ((relativeToLocalTopHomologyMap Coeff n X domain x.property) localOrientationClass) = 1

theorem LocalTopHomologyTrivialization.identify_localOrientationClass_apply
    {Coeff : Type u} [CommRing Coeff] {n : ℕ} {X : Type u} [TopologicalSpace X]
    (U : LocalTopHomologyTrivialization Coeff n X) (x : U.domain) :
    (U.identify x).hom
        ((relativeToLocalTopHomologyMap Coeff n X U.domain x.property) U.localOrientationClass) =
      1 :=
  U.identify_localOrientationClass x

def LocalTopHomologyTrivialization.Compatible
    {Coeff : Type u} [CommRing Coeff] {n : ℕ} {X : Type u} [TopologicalSpace X]
    (U V : LocalTopHomologyTrivialization Coeff n X) : Prop :=
  ∃ transition : LocallyConstant {x : X // x ∈ U.domain ∩ V.domain} Coeffˣ,
    ∀ ⦃x : X⦄ (hxU : x ∈ U.domain) (hxV : x ∈ V.domain),
      U.identify ⟨x, hxU⟩ =
        V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩)

/-- Two local top-homology trivializations determine the same local orientation on their overlap
when their identifications agree pointwise. Unlike `Compatible`, this excludes a nontrivial unit
transition and therefore distinguishes an orientation from its opposite. -/
def LocalTopHomologyTrivialization.OrientationCompatible
    {Coeff : Type u} [CommRing Coeff] {n : ℕ} {X : Type u} [TopologicalSpace X]
    (U V : LocalTopHomologyTrivialization Coeff n X) : Prop :=
  ∀ ⦃x : X⦄ (hxU : x ∈ U.domain) (hxV : x ∈ V.domain),
    U.identify ⟨x, hxU⟩ = V.identify ⟨x, hxV⟩

theorem LocalTopHomologyTrivialization.exists_overlap_transition
    {Coeff : Type u} [CommRing Coeff] {n : ℕ} {X : Type u} [TopologicalSpace X]
    {U V : LocalTopHomologyTrivialization Coeff n X} (hUV : U.Compatible V) :
    ∃ transition : LocallyConstant {x : X // x ∈ U.domain ∩ V.domain} Coeffˣ,
      ∀ ⦃x : X⦄ (hxU : x ∈ U.domain) (hxV : x ∈ V.domain),
        U.identify ⟨x, hxU⟩ =
          V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩) :=
  hUV

namespace LocalTopHomologyTrivialization

variable {Coeff : Type u} [CommRing Coeff] {n : ℕ} {X : Type u} [TopologicalSpace X]

/-- Helper for Definition 20.1.1: the unit-induced automorphism acts on `ULift Coeff` by right
multiplication on the underlying coefficient. -/
theorem unitModuleIso_hom_down (unit : Coeffˣ) (z : constantCoefficientModule Coeff) :
    ((unitModuleIso Coeff unit).hom z).down = z.down * unit := by
  -- Reduce the `ModuleCat` automorphism to the defining linear equivalence on `ULift Coeff`.
  cases z
  rfl

/-- Helper for Definition 20.1.1: the unit action of `1 : Coeffˣ` is the identity
automorphism. -/
theorem unitModuleIso_one :
    unitModuleIso Coeff (1 : Coeffˣ) = Iso.refl (constantCoefficientModule Coeff) := by
  -- Compare the two automorphisms on elements of the coefficient module.
  ext z
  cases z with
  | up z =>
      simp [unitModuleIso, ULift.moduleEquiv, Units.mulRightLinearEquiv_apply]

/-- Helper for Definition 20.1.1: composing two unit actions multiplies the units. -/
theorem unitModuleIso_mul (u v : Coeffˣ) :
    unitModuleIso Coeff u ≪≫ unitModuleIso Coeff v = unitModuleIso Coeff (u * v) := by
  -- The composition law is checked on coefficients in `ULift Coeff`.
  ext z
  cases z with
  | up z =>
      simp [unitModuleIso, ULift.moduleEquiv, Units.mulRightLinearEquiv_apply, mul_assoc]

/-- Helper for Definition 20.1.1: on a triple overlap, the two transition functions compose by
multiplying their unit values. -/
theorem composeOverlapTransitionAt
    {U V W : LocalTopHomologyTrivialization Coeff n X}
    {transitionUV : LocallyConstant {x : X // x ∈ U.domain ∩ V.domain} Coeffˣ}
    {transitionVW : LocallyConstant {x : X // x ∈ V.domain ∩ W.domain} Coeffˣ}
    (hUV : ∀ ⦃x : X⦄ (hxU : x ∈ U.domain) (hxV : x ∈ V.domain),
      U.identify ⟨x, hxU⟩ =
        V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (transitionUV ⟨x, ⟨hxU, hxV⟩⟩))
    (hVW : ∀ ⦃x : X⦄ (hxV : x ∈ V.domain) (hxW : x ∈ W.domain),
      V.identify ⟨x, hxV⟩ =
        W.identify ⟨x, hxW⟩ ≪≫ unitModuleIso Coeff (transitionVW ⟨x, ⟨hxV, hxW⟩⟩))
    {x : X} (hxU : x ∈ U.domain) (hxV : x ∈ V.domain) (hxW : x ∈ W.domain) :
    U.identify ⟨x, hxU⟩ =
      W.identify ⟨x, hxW⟩ ≪≫
        unitModuleIso Coeff
          (transitionVW ⟨x, ⟨hxV, hxW⟩⟩ * transitionUV ⟨x, ⟨hxU, hxV⟩⟩) := by
  -- Rewrite through the intermediate trivialization and then normalize the composed unit action.
  calc
    U.identify ⟨x, hxU⟩ =
        (W.identify ⟨x, hxW⟩ ≪≫ unitModuleIso Coeff (transitionVW ⟨x, ⟨hxV, hxW⟩⟩)) ≪≫
          unitModuleIso Coeff (transitionUV ⟨x, ⟨hxU, hxV⟩⟩) := by
      rw [hUV hxU hxV, hVW hxV hxW]
    _ = W.identify ⟨x, hxW⟩ ≪≫
          unitModuleIso Coeff
            (transitionVW ⟨x, ⟨hxV, hxW⟩⟩ * transitionUV ⟨x, ⟨hxU, hxV⟩⟩) := by
      simpa [Iso.trans_assoc] using congrArg (fun iso ↦ W.identify ⟨x, hxW⟩ ≪≫ iso)
        (unitModuleIso_mul
          (transitionVW ⟨x, ⟨hxV, hxW⟩⟩)
          (transitionUV ⟨x, ⟨hxU, hxV⟩⟩))

/-- Helper for Definition 20.1.1: a pointwise identification between two local trivializations
determines its transition unit uniquely. -/
theorem transitionUnit_unique
    {U W : LocalTopHomologyTrivialization Coeff n X}
    {x : X} {hxU : x ∈ U.domain} {hxW : x ∈ W.domain}
    {u v : Coeffˣ}
    (hu : U.identify ⟨x, hxU⟩ =
      W.identify ⟨x, hxW⟩ ≪≫ unitModuleIso Coeff u)
    (hv : U.identify ⟨x, hxU⟩ =
      W.identify ⟨x, hxW⟩ ≪≫ unitModuleIso Coeff v) :
    u = v := by
  let localClass :=
    (relativeToLocalTopHomologyMap Coeff n X W.domain hxW) W.localOrientationClass
  -- Evaluate both comparison isomorphisms on `W`'s chosen local orientation class.
  have huEval :
      (((U.identify ⟨x, hxU⟩).hom localClass).down) = u := by
    have huMap :
        (U.identify ⟨x, hxU⟩).hom localClass =
          (unitModuleIso Coeff u).hom ((W.identify ⟨x, hxW⟩).hom localClass) := by
      simpa [localClass] using congrArg (fun iso ↦ iso.hom localClass) hu
    rw [huMap, W.identify_localOrientationClass_apply]
    simpa using unitModuleIso_hom_down (Coeff := Coeff) u (1 : constantCoefficientModule Coeff)
  have hvEval :
      (((U.identify ⟨x, hxU⟩).hom localClass).down) = v := by
    have hvMap :
        (U.identify ⟨x, hxU⟩).hom localClass =
          (unitModuleIso Coeff v).hom ((W.identify ⟨x, hxW⟩).hom localClass) := by
      simpa [localClass] using congrArg (fun iso ↦ iso.hom localClass) hv
    rw [hvMap, W.identify_localOrientationClass_apply]
    simpa using unitModuleIso_hom_down (Coeff := Coeff) v (1 : constantCoefficientModule Coeff)
  have huv : (u : Coeff) = v := huEval.symm.trans hvEval
  exact Units.ext huv

/-- Reversing a local `Coeff`-orientation twists the chosen trivialization by `-1`. -/
@[reducible] def opposite (U : LocalTopHomologyTrivialization Coeff n X) :
    LocalTopHomologyTrivialization Coeff n X where
  domain := U.domain
  isOpen_domain := U.isOpen_domain
  localOrientationClass := -U.localOrientationClass
  identify := fun x ↦ U.identify x ≪≫ unitModuleIso Coeff (-1 : Coeffˣ)
  identify_localOrientationClass := by
    intro x
    -- Push the negation through the two linear maps and compute the `-1` unit action on `-1`.
    change ((unitModuleIso Coeff (-1 : Coeffˣ)).hom)
        ((U.identify x).hom
          ((relativeToLocalTopHomologyMap Coeff n X U.domain x.property)
            (-U.localOrientationClass))) = 1
    rw [map_neg, map_neg]
    rw [U.identify_localOrientationClass_apply x]
    ext
    simp [unitModuleIso, ULift.moduleEquiv, Units.mulRightLinearEquiv_apply]

@[refl] theorem Compatible.refl (U : LocalTopHomologyTrivialization Coeff n X) :
    U.Compatible U := by
  refine ⟨1, ?_⟩
  intro x hxU hxU'
  have hproof : hxU = hxU' := Subsingleton.elim _ _
  -- Proof irrelevance aligns the subtype witnesses, after which the transition is the unit `1`.
  cases hproof
  change U.identify ⟨x, hxU⟩ = U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff (1 : Coeffˣ)
  rw [unitModuleIso_one]
  simp

@[symm] theorem Compatible.symm {U V : LocalTopHomologyTrivialization Coeff n X}
    (hUV : U.Compatible V) :
    V.Compatible U := by
  rcases hUV with ⟨transition, htransition⟩
  let swapOverlap :
      C({x : X // x ∈ V.domain ∩ U.domain}, {x : X // x ∈ U.domain ∩ V.domain}) :=
    ⟨fun x ↦ ⟨x.1, And.symm x.2⟩, by continuity⟩
  let reverseTransition : LocallyConstant {x : X // x ∈ V.domain ∩ U.domain} Coeffˣ :=
    (LocallyConstant.comap swapOverlap transition)⁻¹
  refine ⟨reverseTransition, ?_⟩
  intro x hxV hxU
  have hcomp := htransition hxU hxV
  -- Compose with the inverse unit action to move the compatibility relation backwards.
  calc
    V.identify ⟨x, hxV⟩ =
        (V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩)) ≪≫
          unitModuleIso Coeff ((transition ⟨x, ⟨hxU, hxV⟩⟩)⁻¹) := by
      simp [unitModuleIso_mul, unitModuleIso_one, Iso.trans_assoc]
    _ = U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff ((transition ⟨x, ⟨hxU, hxV⟩⟩)⁻¹) := by
      rw [hcomp]
    _ = U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff (reverseTransition ⟨x, ⟨hxV, hxU⟩⟩) := by
      rfl

/-- Reversing both local orientations preserves compatibility of transition functions. -/
theorem Compatible.opposite {U V : LocalTopHomologyTrivialization Coeff n X}
    (hUV : U.Compatible V) :
    U.opposite.Compatible V.opposite := by
  rcases hUV with ⟨transition, htransition⟩
  refine ⟨transition, ?_⟩
  intro x hxU hxV
  -- Both trivializations are twisted by the same `-1` action, so the original transition remains.
  change U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ) =
    (V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ)) ≪≫
      unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩)
  calc
    U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ) =
        (V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩)) ≪≫
          unitModuleIso Coeff (-1 : Coeffˣ) := by
      rw [htransition hxU hxV]
    _ = V.identify ⟨x, hxV⟩ ≪≫
          unitModuleIso Coeff ((transition ⟨x, ⟨hxU, hxV⟩⟩) * (-1 : Coeffˣ)) := by
      simpa [Iso.trans_assoc] using congrArg (fun iso ↦ V.identify ⟨x, hxV⟩ ≪≫ iso)
        (unitModuleIso_mul (transition ⟨x, ⟨hxU, hxV⟩⟩) (-1 : Coeffˣ))
    _ = V.identify ⟨x, hxV⟩ ≪≫
          unitModuleIso Coeff ((-1 : Coeffˣ) * transition ⟨x, ⟨hxU, hxV⟩⟩) := by
      rw [mul_comm]
    _ = (V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ)) ≪≫
          unitModuleIso Coeff (transition ⟨x, ⟨hxU, hxV⟩⟩) := by
      simpa [Iso.trans_assoc] using congrArg (fun iso ↦ V.identify ⟨x, hxV⟩ ≪≫ iso)
        (unitModuleIso_mul (-1 : Coeffˣ) (transition ⟨x, ⟨hxU, hxV⟩⟩)).symm

/-- Pointwise agreement of local orientations is reflexive. -/
@[refl] theorem OrientationCompatible.refl
    (U : LocalTopHomologyTrivialization Coeff n X) :
    U.OrientationCompatible U := by
  intro x hx hx'
  cases Subsingleton.elim hx hx'
  rfl

/-- Pointwise agreement of local orientations is symmetric. -/
@[symm] theorem OrientationCompatible.symm
    {U V : LocalTopHomologyTrivialization Coeff n X}
    (hUV : U.OrientationCompatible V) :
    V.OrientationCompatible U := by
  intro x hxV hxU
  exact (hUV hxU hxV).symm

/-- Orientation-preserving compatibility implies compatibility up to a locally constant unit,
with transition unit identically equal to `1`. -/
theorem OrientationCompatible.compatible
    {U V : LocalTopHomologyTrivialization Coeff n X}
    (hUV : U.OrientationCompatible V) :
    U.Compatible V := by
  refine ⟨1, ?_⟩
  intro x hxU hxV
  rw [hUV hxU hxV]
  change V.identify ⟨x, hxV⟩ =
    V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (1 : Coeffˣ)
  rw [unitModuleIso_one]
  simp

/-- Reversing both local orientations preserves pointwise orientation agreement. -/
theorem OrientationCompatible.opposite
    {U V : LocalTopHomologyTrivialization Coeff n X}
    (hUV : U.OrientationCompatible V) :
    U.opposite.OrientationCompatible V.opposite := by
  intro x hxU hxV
  change U.identify ⟨x, hxU⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ) =
    V.identify ⟨x, hxV⟩ ≪≫ unitModuleIso Coeff (-1 : Coeffˣ)
  rw [hUV hxU hxV]

end LocalTopHomologyTrivialization

/-- Definition 20.1.1. An `R`-oriented `n`-manifold is a manifold equipped with an atlas of
local top-homology trivializations whose overlap identifications differ by locally constant units
of `R`. -/
class ROrientedManifold (R : outParam (Type _)) [CommRing R]
    {E : outParam (Type _)} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : outParam (Type _)} [TopologicalSpace H]
    (I : outParam (ModelWithCorners ℝ E H)) [I.Boundaryless]
    (n : outParam ℕ) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [Fact (Module.finrank ℝ E = n)] extends IsManifold I ⊤ M where
  atlas : Set (LocalTopHomologyTrivialization R n M)
  cover : ∀ x : M, ∃ U ∈ atlas, x ∈ U.domain
  pairwise_compatible :
    ∀ {U V : LocalTopHomologyTrivialization R n M},
      U ∈ atlas → V ∈ atlas → U.OrientationCompatible V

namespace ROrientedManifold

variable {R : Type _} [CommRing R]
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The opposite `R`-orientation obtained by negating every local orientation in the atlas. -/
@[reducible] def opposite (o : ROrientedManifold R I n M) : ROrientedManifold R I n M where
  toIsManifold := o.toIsManifold
  atlas := LocalTopHomologyTrivialization.opposite '' o.atlas
  cover := by
    intro x
    rcases o.cover x with ⟨U, hU, hxU⟩
    exact ⟨U.opposite, ⟨U, hU, rfl⟩, hxU⟩
  pairwise_compatible := by
    intro U V hU hV
    rcases hU with ⟨U', hU', rfl⟩
    rcases hV with ⟨V', hV', rfl⟩
    exact (o.pairwise_compatible hU' hV').opposite

/-- Two `R`-oriented atlases represent the same global orientation when, at every point, any chart
from the first atlas and any chart from the second atlas that both contain that point are
compatible. -/
def SameOrientation (o₁ o₂ : ROrientedManifold R I n M) : Prop :=
  ∀ x : M, ∀ ⦃U V : LocalTopHomologyTrivialization R n M⦄,
    ∀ (_hU : U ∈ o₁.atlas) (hxU : x ∈ U.domain)
      (_hV : V ∈ o₂.atlas) (hxV : x ∈ V.domain),
      U.identify ⟨x, hxU⟩ = V.identify ⟨x, hxV⟩

/-- Helper for Definition 20.1.1: an intermediate atlas chart produces a pointwise overlap unit
between charts from the first and third atlases. -/
theorem existsPointwiseTransitionUnit
    {o₁ o₂ o₃ : ROrientedManifold R I n M}
    (h₁₂ : SameOrientation o₁ o₂) (h₂₃ : SameOrientation o₂ o₃)
    {U W : LocalTopHomologyTrivialization R n M}
    (hU : U ∈ o₁.atlas) (hW : W ∈ o₃.atlas)
    {x : M} (hxU : x ∈ U.domain) (hxW : x ∈ W.domain) :
    ∃ unit : Rˣ,
      U.identify ⟨x, hxU⟩ = W.identify ⟨x, hxW⟩ ≪≫ unitModuleIso R unit := by
  rcases o₂.cover x with ⟨V, hV, hxV⟩
  refine ⟨1, ?_⟩
  rw [h₁₂ x hU hxU hV hxV, h₂₃ x hV hxV hW hxW,
    LocalTopHomologyTrivialization.unitModuleIso_one]
  simp

@[refl] theorem SameOrientation.refl (o : ROrientedManifold R I n M) :
    SameOrientation o o := by
  intro x U V hU hxU hV hxV
  exact o.pairwise_compatible hU hV hxU hxV

@[symm] theorem SameOrientation.symm {o₁ o₂ : ROrientedManifold R I n M}
    (h : SameOrientation o₁ o₂) :
    SameOrientation o₂ o₁ := by
  intro x U V hU hxU hV hxV
  exact (h x hV hxV hU hxU).symm

@[trans] theorem SameOrientation.trans {o₁ o₂ o₃ : ROrientedManifold R I n M}
    (h₁₂ : SameOrientation o₁ o₂) (h₂₃ : SameOrientation o₂ o₃) :
    SameOrientation o₁ o₃ := by
  intro x U W hU hxU hW hxW
  rcases o₂.cover x with ⟨V, hV, hxV⟩
  calc
    U.identify ⟨x, hxU⟩ = V.identify ⟨x, hxV⟩ := h₁₂ x hU hxU hV hxV
    _ = W.identify ⟨x, hxW⟩ := h₂₃ x hV hxV hW hxW

/-- Reversing both global orientations preserves the same-orientation relation. -/
theorem SameOrientation.opposite {o₁ o₂ : ROrientedManifold R I n M}
    (h : SameOrientation o₁ o₂) :
    SameOrientation o₁.opposite o₂.opposite := by
  intro x U V hU hxU hV hxV
  rcases hU with ⟨U', hU', rfl⟩
  rcases hV with ⟨V', hV', rfl⟩
  change U'.identify ⟨x, hxU⟩ ≪≫ unitModuleIso R (-1 : Rˣ) =
    V'.identify ⟨x, hxV⟩ ≪≫ unitModuleIso R (-1 : Rˣ)
  rw [h x hU' hxU hV' hxV]

instance sameOrientationSetoid : Setoid (ROrientedManifold R I n M) where
  r := SameOrientation
  iseqv := ⟨SameOrientation.refl, SameOrientation.symm, SameOrientation.trans⟩

private abbrev OrientedAtlasOwner (R : Type _) [CommRing R]
    {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (n : ℕ) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [Fact (Module.finrank ℝ E = n)] : Type _ :=
  @ROrientedManifold R _ E _ _ _ H _ I _ n M _ _ _

/-- A global `R`-orientation on `M` is an equivalence class of compatible `R`-oriented atlases. -/
abbrev GlobalOrientation (R : Type _) [CommRing R]
    {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (n : ℕ) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [Fact (Module.finrank ℝ E = n)] :=
  Quotient (sameOrientationSetoid : Setoid (OrientedAtlasOwner R I n M))

/-- An oriented atlas determines its global orientation class. -/
abbrev toGlobalOrientation (o : ROrientedManifold R I n M) :
    Quotient (sameOrientationSetoid : Setoid (ROrientedManifold R I n M)) :=
  Quotient.mk _ o

/-- The opposite global orientation induced by reversing every local orientation. -/
def GlobalOrientation.opposite :
    Quotient (sameOrientationSetoid : Setoid (ROrientedManifold R I n M)) →
      Quotient (sameOrientationSetoid : Setoid (ROrientedManifold R I n M)) :=
  Quotient.map ROrientedManifold.opposite fun _ _ h ↦ SameOrientation.opposite h

end ROrientedManifold

class NonorientableManifold
    {E : outParam (Type _)} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : outParam (Type _)} [TopologicalSpace H]
    (I : outParam (ModelWithCorners ℝ E H)) [I.Boundaryless]
    (n : outParam ℕ) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [Fact (Module.finrank ℝ E = n)] [IsManifold I ⊤ M] : Prop where
  not_nonempty_rOrientedManifold : ¬ Nonempty (ROrientedManifold ℤ I n M)
