import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_3_4.Pointed
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5

open CategoryTheory

universe u v

noncomputable section

section

variable (BO : ℕ → Type u)
variable [∀ n, TopologicalSpace (BO n)]
variable (γ : ∀ n, BO n → Type v)
variable [∀ n, TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) (γ n))]
variable [∀ n, (b : BO n) → TopologicalSpace (γ n b)]
variable [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
variable [∀ n, (b : BO n) → AddCommGroup (γ n b)]
variable [∀ n, (b : BO n) → Module ℝ (γ n b)]
variable [∀ n, RealPlaneBundleClassifyingSpace n (BO n) (γ n)]
variable [TOStagewiseNormedBundle BO γ]

/-- The universal bundle `γ m` pulled back to `BO(m) × BO(n)` along the first projection. -/
abbrev TOFstPullbackBundle (m n : ℕ) :
    RealPlaneBundle m ((BO m) × (BO n)) :=
  @RealPlaneBundle.ofFamily m ((BO m) × (BO n)) _ (ContinuousMap.fst *ᵖ (γ m))
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (continuousMapCoePullbackModules ContinuousMap.fst (γ m))
    (show VectorBundle ℝ (Fin m → ℝ) (ContinuousMap.fst *ᵖ (γ m)) from
      VectorBundle.pullback ℝ ContinuousMap.fst)

/-- The universal bundle `γ n` pulled back to `BO(m) × BO(n)` along the second projection. -/
abbrev TOSndPullbackBundle (m n : ℕ) :
    RealPlaneBundle n ((BO m) × (BO n)) :=
  @RealPlaneBundle.ofFamily n ((BO m) × (BO n)) _ (ContinuousMap.snd *ᵖ (γ n))
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (continuousMapCoePullbackModules ContinuousMap.snd (γ n))
    (show VectorBundle ℝ (Fin n → ℝ) (ContinuousMap.snd *ᵖ (γ n)) from
      VectorBundle.pullback ℝ ContinuousMap.snd)

/-- The fiber family underlying the Whitney sum of the pullbacks of the universal bundles `γ m`
and `γ n` to the product base `BO(m) × BO(n)`. -/
abbrev TOWhitneySumFiber (m n : ℕ) :
    (BO m × BO n) → Type v :=
  fun x ↦ (TOFstPullbackBundle BO γ m n).fiber x × (TOSndPullbackBundle BO γ m n).fiber x

/-- Unfolding `TOWhitneySumFiber` recovers the fiberwise product of the pulled-back universal
bundles. -/
@[simp] theorem TOWhitneySumFiber_def (m n : ℕ) :
    TOWhitneySumFiber BO γ m n =
      fun x ↦
        (TOFstPullbackBundle BO γ m n).fiber x × (TOSndPullbackBundle BO γ m n).fiber x :=
  rfl

/-- A Whitney-sum presentation of the stabilization map in Construction 25.3.4 consists of the
relevant direct-sum bundle over `BO(n) × BO(1)` together with the displayed Thom-space
stabilization map it presents. -/
structure TOWhitneySumStabilizationPresentation
    (bInf : ∀ n, BO n) (n : ℕ) where
  /-- The Whitney-sum bundle over `BO(n) × BO(1)`. -/
  bundle : RealPlaneBundle (n + 1) ((BO n) × (BO 1))
  /-- The exhibited bundle has the expected fiberwise direct-sum family. -/
  bundle_fiber : bundle.fiber = TOWhitneySumFiber BO γ n 1
  /-- The stabilization map presented by this Whitney-sum bundle. -/
  presentedMap :
    reducedSuspension
        (TOPointedCompactlyGenerated BO γ bInf n) ⟶
      TOPointedCompactlyGenerated BO γ bInf (n + 1)

/-- A Whitney-sum presentation of the multiplication map in Construction 25.3.4 consists of the
relevant direct-sum bundle over `BO(m) × BO(n)` together with the displayed Thom-space
multiplication map it presents. -/
structure TOWhitneySumMultiplicationPresentation
    (bInf : ∀ n, BO n)
    (directSumStructureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1))
    (m n : ℕ) where
  /-- The Whitney-sum bundle over `BO(m) × BO(n)`. -/
  bundle : RealPlaneBundle (m + n) ((BO m) × (BO n))
  /-- The exhibited bundle has the expected fiberwise direct-sum family. -/
  bundle_fiber : bundle.fiber = TOWhitneySumFiber BO γ m n
  /-- The multiplication map presented by this Whitney-sum bundle. -/
  presentedMap :
    smashProduct
        ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace m)
        ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ⟶
      (TO_prespectrum BO γ bInf directSumStructureMap).basedSpace (m + n)

/-- Package a chosen family of Thom-space stabilization, unit, and multiplication maps with their
coherence laws as a ring prespectrum. -/
def TO_ringPrespectrum
    (bInf : ∀ n, BO n)
    (directSumStructureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1))
    (directSumUnit :
      sphereZero ⟶ (TO_prespectrum BO γ bInf directSumStructureMap).basedSpace 0)
    (directSumMul :
      ∀ m n : ℕ,
        smashProduct
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace m)
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ⟶
          (TO_prespectrum BO γ bInf directSumStructureMap).basedSpace (m + n))
    (directSumMulAssoc :
      ∀ l m n : ℕ,
        basedHomotopyRel
          (smashProductMap (directSumMul l m)
              (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n)) ≫
            directSumMul (l + m) n)
          (smashProductAssoc
              ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace l)
              ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace m)
              ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
            smashProductMap
              (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace l))
              (directSumMul m n) ≫
            directSumMul l (m + n) ≫
              (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
                (Nat.add_assoc l m n).symm))
    (directSumOneMul :
      ∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap directSumUnit
              (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n)) ≫
            directSumMul 0 n)
          (smashProductLeftUnit
              ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
            (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
              (Nat.zero_add n).symm))
    (directSumMulOne :
      ∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap
              (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n))
              directSumUnit ≫
            directSumMul n 0)
          (smashProductRightUnit
              ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
            (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
              (Nat.add_zero n).symm)) :
    RingPrespectrum where
  toPrespectrum := TO_prespectrum BO γ bInf directSumStructureMap
  unit := directSumUnit
  mul := directSumMul
  mul_assoc := directSumMulAssoc
  one_mul := directSumOneMul
  mul_one := directSumMulOne

/-- A chosen direct-sum-induced stabilization, unit, and multiplication structure on the
stagewise Thom spaces `TO n`. Its fields are the direct-sum Thom stabilization, unit, and
multiplication maps together with the ring-prespectrum coherence laws they satisfy. -/
structure TODirectSumRingStructure
    (bInf : ∀ n, BO n) where
  /-- The stabilization maps of the Thom prespectrum. -/
  directSumStructureMap :
    ∀ n : ℕ,
      reducedSuspension
          (TOPointedCompactlyGenerated BO γ bInf n) ⟶
        TOPointedCompactlyGenerated BO γ bInf (n + 1)
  /-- The unit of the Thom ring prespectrum. -/
  directSumUnit :
    sphereZero ⟶ (TO_prespectrum BO γ bInf directSumStructureMap).basedSpace 0
  /-- The multiplication maps of the Thom ring prespectrum. -/
  directSumMul :
    ∀ m n : ℕ,
      smashProduct
          ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace m)
          ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ⟶
        (TO_prespectrum BO γ bInf directSumStructureMap).basedSpace (m + n)
  /-- Associativity of the multiplication. -/
  directSumMulAssoc :
    ∀ l m n : ℕ,
      basedHomotopyRel
        (smashProductMap (directSumMul l m)
            (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n)) ≫
          directSumMul (l + m) n)
        (smashProductAssoc
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace l)
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace m)
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
          smashProductMap
            (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace l))
            (directSumMul m n) ≫
          directSumMul l (m + n) ≫
            (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
              (Nat.add_assoc l m n).symm)
  /-- Left unitality of the multiplication. -/
  directSumOneMul :
    ∀ n : ℕ,
      basedHomotopyRel
        (smashProductMap directSumUnit
            (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n)) ≫
          directSumMul 0 n)
        (smashProductLeftUnit
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
          (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
            (Nat.zero_add n).symm)
  /-- Right unitality of the multiplication. -/
  directSumMulOne :
    ∀ n : ℕ,
      basedHomotopyRel
        (smashProductMap
            (𝟙 ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n))
            directSumUnit ≫
          directSumMul n 0)
        (smashProductRightUnit
            ((TO_prespectrum BO γ bInf directSumStructureMap).basedSpace n) ≫
          (TO_prespectrum BO γ bInf directSumStructureMap).basedSpaceCast
            (Nat.add_zero n).symm)

namespace TODirectSumRingStructure

/-- The direct-sum-induced Thom data determine the associated ring prespectrum. -/
def toRingPrespectrum
    {bInf : ∀ n, BO n} (data : TODirectSumRingStructure BO γ bInf) :
    RingPrespectrum :=
  TO_ringPrespectrum
    BO γ bInf data.directSumStructureMap data.directSumUnit data.directSumMul
    data.directSumMulAssoc data.directSumOneMul data.directSumMulOne

omit [∀ n, RealPlaneBundleClassifyingSpace n (BO n) (γ n)] in
/-- The data in `TODirectSumRingStructure` recover the stabilization, unit, and multiplication
maps of the associated Thom ring prespectrum from Construction 25.3.4. -/
theorem spec
    {bInf : ∀ n, BO n} (data : TODirectSumRingStructure BO γ bInf) :
    data.toRingPrespectrum.toPrespectrum =
        TO_prespectrum BO γ bInf data.directSumStructureMap ∧
      data.toRingPrespectrum.unit = data.directSumUnit ∧
      data.toRingPrespectrum.mul = data.directSumMul := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

omit [∀ n, TopologicalSpace (BO n)]
  [∀ n, (b : BO n) → TopologicalSpace (γ n b)]
  [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
  [∀ n, (b : BO n) → AddCommGroup (γ n b)]
  [∀ n, (b : BO n) → Module ℝ (γ n b)]
  [∀ n, RealPlaneBundleClassifyingSpace n (BO n) (γ n)] in
/-- The ring prespectrum assembled from direct-sum data has the expected underlying Thom
prespectrum. -/
@[simp] theorem toRingPrespectrum_toPrespectrum
    [TOStagewiseNormedBundle BO γ]
    {bInf : ∀ n, BO n} (data : TODirectSumRingStructure BO γ bInf) :
    data.toRingPrespectrum.toPrespectrum =
      TO_prespectrum BO γ bInf data.directSumStructureMap := rfl

end TODirectSumRingStructure

/-- A source-facing presentation of the stabilization and multiplication maps in Construction
25.3.4 by Whitney sums of the universal bundles. It records the relevant Whitney-sum bundles over
the product bases together with the displayed stabilization and multiplication maps that those
bundles present. -/
def IsTOWhitneySumRingPresentation
    (bInf : ∀ n, BO n)
    (directSumData : TODirectSumRingStructure BO γ bInf) :
    Prop :=
  (∀ n : ℕ,
      ∃ presentation : TOWhitneySumStabilizationPresentation BO γ bInf n,
        presentation.presentedMap = directSumData.directSumStructureMap n) ∧
    ∀ m n : ℕ,
      ∃ presentation :
        TOWhitneySumMultiplicationPresentation
          BO γ bInf directSumData.directSumStructureMap m n,
        presentation.presentedMap = directSumData.directSumMul m n

namespace IsTOWhitneySumRingPresentation

/-- The specification of a Whitney-sum presentation is exactly the bundle-level Whitney-sum data
and the displayed stabilization and multiplication maps attached to those bundles. -/
theorem spec
    {bInf : ∀ n, BO n}
    {directSumData : TODirectSumRingStructure BO γ bInf}
    (hPresentation :
      IsTOWhitneySumRingPresentation BO γ bInf directSumData) :
    (∀ n : ℕ,
      ∃ presentation : TOWhitneySumStabilizationPresentation BO γ bInf n,
        presentation.presentedMap = directSumData.directSumStructureMap n) ∧
    (∀ m n : ℕ,
      ∃ presentation :
        TOWhitneySumMultiplicationPresentation
          BO γ bInf directSumData.directSumStructureMap m n,
        presentation.presentedMap = directSumData.directSumMul m n) :=
  hPresentation

end IsTOWhitneySumRingPresentation

/-- Helper for Construction 25.3.4: once the direct-sum ring data and their Whitney-sum
presentation are known, the target existential statement only needs the definitional equality of
the underlying prespectrum. -/
theorem ringPrespectrumWitnessOfPresentation
    {bInf : ∀ n, BO n}
    (directSumData : TODirectSumRingStructure BO γ bInf)
    (hPresentation : IsTOWhitneySumRingPresentation BO γ bInf directSumData) :
    directSumData.toRingPrespectrum.toPrespectrum =
        TO_prespectrum BO γ bInf directSumData.directSumStructureMap ∧
      IsTOWhitneySumRingPresentation BO γ bInf directSumData := by
  constructor
  · rfl
  · exact hPresentation

/-- A ring prespectrum on the Thom spaces `TO n` is direct-sum-induced when its underlying
prespectrum is the chosen Thom prespectrum and its multiplication and stabilization data admit a
Whitney-sum presentation. -/
def IsTODirectSumRingPrespectrum
    (bInf : ∀ n, BO n)
    (structureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1))
    (T : RingPrespectrum) : Prop :=
  T.toPrespectrum = TO_prespectrum BO γ bInf structureMap ∧
  ∃ directSumData : TODirectSumRingStructure BO γ bInf,
    directSumData.directSumStructureMap = structureMap ∧
      T = directSumData.toRingPrespectrum ∧
      IsTOWhitneySumRingPresentation BO γ bInf directSumData

/-- Direct-sum-induced Thom ring-prespectrum data determine the underlying Thom prespectrum built
from their stabilization maps. -/
theorem IsTODirectSumRingPrespectrum.toPrespectrum_eq
    {bInf : ∀ n, BO n}
    {structureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated BO γ bInf n) ⟶
          TOPointedCompactlyGenerated BO γ bInf (n + 1)}
    {T : RingPrespectrum}
    (hT : IsTODirectSumRingPrespectrum BO γ bInf structureMap T) :
    T.toPrespectrum = TO_prespectrum BO γ bInf structureMap :=
  hT.1

/-- A Whitney-sum presentation of the direct-sum Thom data determines the associated
direct-sum-induced ring prespectrum on the Thom spaces `TO n`. -/
theorem IsTOWhitneySumRingPresentation.toRingPrespectrum
    {bInf : ∀ n, BO n}
    {directSumData : TODirectSumRingStructure BO γ bInf}
    (hPresentation :
      IsTOWhitneySumRingPresentation BO γ bInf directSumData) :
    IsTODirectSumRingPrespectrum
      BO γ bInf directSumData.directSumStructureMap directSumData.toRingPrespectrum := by
  refine ⟨rfl, directSumData, rfl, rfl, hPresentation⟩

/-- A ring prespectrum on the Thom spaces `TO n` is assembled by direct sums of vector bundles if
it can be realized from some pointed Thom-space models whose stabilization and multiplication data
admit Whitney-sum presentations. The auxiliary fiberwise norm data needed for the Thom-space
topology are quantified explicitly here rather than being left as hidden ambient assumptions. -/
def IsTOAssembledRingPrespectrum (T : RingPrespectrum) : Prop :=
  ∃ normed : TOStagewiseNormedBundle BO γ,
    let _ : TOStagewiseNormedBundle BO γ := normed
    ∃ bInf : ∀ n, BO n,
      ∃ structureMap :
        ∀ n : ℕ,
          reducedSuspension
              (TOPointedCompactlyGenerated BO γ bInf n) ⟶
            TOPointedCompactlyGenerated BO γ bInf (n + 1),
        IsTODirectSumRingPrespectrum BO γ bInf structureMap T

namespace IsTOAssembledRingPrespectrum

/-- Unfolding `IsTOAssembledRingPrespectrum` recovers the explicit stagewise norm owner, the
pointed Thom-space model, and the direct-sum-induced ring-prespectrum structure used to assemble
`T`. -/
theorem spec
    {T : RingPrespectrum}
    (hT : IsTOAssembledRingPrespectrum BO γ T) :
    ∃ normed : TOStagewiseNormedBundle BO γ,
      let _ : TOStagewiseNormedBundle BO γ := normed
      ∃ bInf : ∀ n, BO n,
        ∃ structureMap :
          ∀ n : ℕ,
            reducedSuspension
                (TOPointedCompactlyGenerated BO γ bInf n) ⟶
              TOPointedCompactlyGenerated BO γ bInf (n + 1),
          IsTODirectSumRingPrespectrum BO γ bInf structureMap T :=
  hT

end IsTOAssembledRingPrespectrum

end
