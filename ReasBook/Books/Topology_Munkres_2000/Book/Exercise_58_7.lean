module

import Topology_Munkres_2000.Book.Definition_54_4
import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv
public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Homotopy.Affine

public section

universe u

open scoped ContinuousMap

/-- Helper for Exercise 58.7: two-sided homotopy-inverse data for a subtype inclusion
defines a homotopy equivalence with the ambient space. -/
private def subtypeInclusionHomotopyEquiv
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (hleft : (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
      (ContinuousMap.id A))
    (hright : ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f).Homotopic
      (ContinuousMap.id X)) : A ≃ₕ X :=
  -- Package the inclusion and its homotopy inverse without exposing fundamental-group details.
  { toFun := ⟨Subtype.val, continuous_subtype_val⟩
    invFun := f
    left_inv := hleft
    right_inv := hright }

/-- Helper for Exercise 58.7: a subtype inclusion with a two-sided homotopy inverse
induces a bijection on fundamental groups. -/
private lemma subtypeInclusionFundamentalGroupMapBijective
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (hleft : (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
      (ContinuousMap.id A))
    (hright : ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f).Homotopic
      (ContinuousMap.id X)) (a₀ : A) :
    Function.Bijective (FundamentalGroup.mapOfSubtype A a₀) := by
  -- Apply homotopy invariance to the equivalence whose forward map is the inclusion.
  exact (subtypeInclusionHomotopyEquiv f hleft hright).fundamentalGroupMap_bijective a₀

/-- Helper for Exercise 58.7: an ambient homotopy preserving a subspace is continuous
when regarded as a homotopy valued in that subspace. -/
private lemma invariantHomotopyLiftContinuous
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (H : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f)
      (ContinuousMap.id X))
    (hH : ∀ t a, H (t, (a : X)) ∈ A) :
    Continuous (fun p : unitInterval × A ↦
      (⟨H (p.1, (p.2 : X)), hH p.1 p.2⟩ : A)) := by
  -- Compose the ambient homotopy with the inclusion on the spatial coordinate.
  apply Continuous.subtype_mk
  exact (map_continuous H).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Helper for Exercise 58.7: the lifted invariant homotopy starts at the
restriction of the ambient endpoint map. -/
private lemma invariantHomotopyLift_zero
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (H : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f)
      (ContinuousMap.id X))
    (hH : ∀ t a, H (t, (a : X)) ∈ A) (a : A) :
    (⟨H (0, (a : X)), hH 0 a⟩ : A) =
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))) a := by
  -- Compare subtype values and use the zero endpoint of the ambient homotopy.
  apply Subtype.ext
  exact H.map_zero_left (a : X)

/-- Helper for Exercise 58.7: the lifted invariant homotopy ends at the identity
of the subspace. -/
private lemma invariantHomotopyLift_one
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (H : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f)
      (ContinuousMap.id X))
    (hH : ∀ t a, H (t, (a : X)) ∈ A) (a : A) :
    (⟨H (1, (a : X)), hH 1 a⟩ : A) = (ContinuousMap.id A) a := by
  -- Compare subtype values and use the identity endpoint of the ambient homotopy.
  apply Subtype.ext
  exact H.map_one_left (a : X)

/-- Helper for Exercise 58.7: an ambient homotopy preserving a subspace restricts
to a homotopy on that subspace. -/
private def invariantHomotopyLift
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (H : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f)
      (ContinuousMap.id X))
    (hH : ∀ t a, H (t, (a : X)) ∈ A) :
    ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
      (ContinuousMap.id A) :=
  -- Bundle the restricted map using the continuity and endpoint interface above.
  { toFun := fun p ↦ ⟨H (p.1, (p.2 : X)), hH p.1 p.2⟩
    continuous_toFun := invariantHomotopyLiftContinuous f H hH
    map_zero_left := invariantHomotopyLift_zero f H hH
    map_one_left := invariantHomotopyLift_one f H hH }

/-- Exercise 58.7 (1). If the map back to a subspace is a retraction and its ambient
composite is homotopic to the identity, then inclusion induces a bijection on fundamental groups. -/
theorem fundamentalGroup_inclusion_bijective_of_retraction
    {X : Type u} [TopologicalSpace X] {A : Set X} (r : Set.Retraction A)
    (H : ContinuousMap.Homotopy r.toAmbient (ContinuousMap.id X)) (a₀ : A) :
    Function.Bijective (FundamentalGroup.mapOfSubtype A a₀) := by
  -- The retraction law gives the left homotopy-inverse equation strictly.
  have hleft :
      (r.toContinuousMap.comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
          (ContinuousMap.id A) := by
    have hComposite :
        r.toContinuousMap.comp
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) =
            ContinuousMap.id A := by
      ext a
      exact congrArg Subtype.val (r.leftInverse a)
    rw [hComposite]
  -- The supplied ambient homotopy is the other homotopy-inverse equation.
  have hAmbient : r.toAmbient.Homotopic (ContinuousMap.id X) := ⟨H⟩
  have hright :
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp
        r.toContinuousMap).Homotopic (ContinuousMap.id X) := by
    simpa only [Set.Retraction.toAmbient] using hAmbient
  -- Invoke the common homotopy-equivalence argument for the inclusion.
  exact subtypeInclusionFundamentalGroupMapBijective r.toContinuousMap hleft hright a₀

/-- Exercise 58.7 (2). If a homotopy from `j ∘ f` to the identity preserves the
subspace throughout, then inclusion induces a bijection on fundamental groups. -/
theorem fundamentalGroup_inclusion_bijective_of_invariantHomotopy
    {X : Type u} [TopologicalSpace X] {A : Set X} (f : C(X, A))
    (H : ContinuousMap.Homotopy
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f)
      (ContinuousMap.id X))
    (hH : ∀ t a, H (t, (a : X)) ∈ A) (a₀ : A) :
    Function.Bijective (FundamentalGroup.mapOfSubtype A a₀) := by
  -- Restrict the invariant ambient homotopy to obtain the left inverse law on `A`.
  have hleft :
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
        (ContinuousMap.id A) := ⟨invariantHomotopyLift f H hH⟩
  -- The original ambient homotopy supplies the right inverse law on `X`.
  have hright :
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f).Homotopic
        (ContinuousMap.id X) := ⟨H⟩
  -- Apply the shared homotopy-equivalence argument.
  exact subtypeInclusionFundamentalGroupMapBijective f hleft hright a₀

/-- The inclusion of the unit circle into the complex plane. -/
def circleToPlane : C(Circle, ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The constant map from the complex plane to the unit circle with value `1`. -/
noncomputable def planeToCircleConstant : C(ℂ, Circle) :=
  ContinuousMap.const ℂ 1

/-- The affine homotopy from the constant ambient composite to the identity of `ℂ`. -/
noncomputable def circlePlaneHomotopy : ContinuousMap.Homotopy
    (circleToPlane.comp planeToCircleConstant) (ContinuousMap.id ℂ) :=
  ContinuousMap.Homotopy.affine _ _

/-- Exercise 58.7 (3). The inclusion `Circle ↪ ℂ` satisfies the ambient homotopy
hypothesis but does not induce a bijection on fundamental groups. -/
theorem circleInclusion_fundamentalGroupMap_not_bijective :
    ¬ Function.Bijective (FundamentalGroup.map circleToPlane (1 : Circle)) := by
  -- Injectivity into the trivial fundamental group of the contractible plane would
  -- make the circle's fundamental group a subsingleton.
  intro hBijective
  have hSubsingleton : Subsingleton (FundamentalGroup Circle (1 : Circle)) :=
    hBijective.1.subsingleton
  -- This contradicts the established infinitude, hence nontriviality, of `π₁(S¹)`.
  have hNotSubsingleton : ¬ Subsingleton (FundamentalGroup Circle (1 : Circle)) :=
    not_subsingleton_iff_nontrivial.mpr inferInstance
  exact hNotSubsingleton hSubsingleton

end
