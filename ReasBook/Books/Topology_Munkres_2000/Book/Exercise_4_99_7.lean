module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Topology_Munkres_2000.Book.Example_16_3.OrderedSquare
public import Topology_Munkres_2000.Book.Example_31_3.Separation
public import Topology_Munkres_2000.Book.Example_41_5.Instances
public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Exercise_34_1.RealLine
public import Topology_Munkres_2000.Book.Exercise_4_99_1
public import Topology_Munkres_2000.Book.Exercise_41_2
public import Topology_Munkres_2000.Book.Example_41_3
import Topology_Munkres_2000.Book.Example_41_6
public import Topology_Munkres_2000.Book.Example_41_4.Instances
public import Topology_Munkres_2000.Book.Theorem_41_4.Paracompact
import Topology_Munkres_2000.Book.Proposition_41_1.Counterexamples
public import Topology_Munkres_2000.Book.Exercise_43_6.Subspace
public import Topology_Munkres_2000.Book.Exercise_4_99_7.Instances
public import Topology_Munkres_2000.Book.Theorem_20_2
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.UnitInterval

public section

open Set

universe u v

/-- Helper for Exercise 4.99.7: the discrete copy of a small topological space maps
surjectively onto the space itself, with independent source and target universes. -/
private def liftedDiscreteCover (Z : Type) [TopologicalSpace Z] :
    ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z :=
  ULift.map WithTopology.ofTopology

/-- Helper for Exercise 4.99.7: `liftedDiscreteCover` is continuous. -/
private lemma liftedDiscreteCover_continuous (Z : Type) [TopologicalSpace Z] :
    Continuous (liftedDiscreteCover Z :
      ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z) := by
  -- Every map from a discrete source is continuous.
  exact continuous_of_discreteTopology

/-- Helper for Exercise 4.99.7: `liftedDiscreteCover` is surjective. -/
private lemma liftedDiscreteCover_surjective (Z : Type) [TopologicalSpace Z] :
    Function.Surjective (liftedDiscreteCover Z :
      ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z) := by
  -- Lift each target point after viewing it in the discrete copy.
  intro z
  refine ⟨ULift.up (WithTopology.toTopology ⊥ z.down), ?_⟩
  cases z
  rfl

/-- Helper for Exercise 4.99.7: closure of paracompactness under countable products
would imply closure under products indexed by `Fin 2`. -/
private lemma paracompactFinTwoPiOfNatPi
    (h : ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)]
      [∀ i, ParacompactSpace (X i)], ParacompactSpace (∀ i, X i)) :
    ∀ (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)]
      [∀ i, ParacompactSpace (X i)], ParacompactSpace (∀ i, X i) := by
  -- Pad the two given coordinates by one-point spaces indexed by `ℕ`.
  intro X topologyX paracompactX
  let Y : Fin 2 ⊕ ℕ → Type u := Sum.elim X (fun _ ↦ PUnit.{u + 1})
  let topologyY (i : Fin 2 ⊕ ℕ) : TopologicalSpace (Y i) :=
    Sum.rec (fun j ↦ topologyX j)
      (fun _ ↦ (inferInstance : TopologicalSpace PUnit.{u + 1})) i
  let paracompactY (i : Fin 2 ⊕ ℕ) : ParacompactSpace (Y i) :=
    Sum.rec (fun j ↦ paracompactX j)
      (fun _ ↦ (inferInstance : ParacompactSpace PUnit.{u + 1})) i
  letI (i : Fin 2 ⊕ ℕ) : TopologicalSpace (Y i) := topologyY i
  letI (i : Fin 2 ⊕ ℕ) : ParacompactSpace (Y i) := paracompactY i
  have hNat : ParacompactSpace
      (∀ n : ℕ, Y ((finSumNatEquiv 2).symm n)) :=
    @h (fun n ↦ Y ((finSumNatEquiv 2).symm n))
      (fun n ↦ topologyY ((finSumNatEquiv 2).symm n))
      (fun n ↦ paracompactY ((finSumNatEquiv 2).symm n))
  -- Reindex, split the sum-indexed product, and discard its unique tail.
  have hSum : ParacompactSpace (∀ i, Y i) :=
    (Homeomorph.piCongrLeft (Y := Y) (finSumNatEquiv 2).symm).paracompactSpace_iff.mp hNat
  have hProd : ParacompactSpace ((∀ i, X i) × (∀ _ : ℕ, PUnit.{u + 1})) :=
    (Homeomorph.sumPiEquivProdPi (Fin 2) ℕ Y).paracompactSpace_iff.mp hSum
  exact (Homeomorph.prodUnique (∀ i, X i)
    (∀ _ : ℕ, PUnit.{u + 1})).paracompactSpace_iff.mp hProd

/- Exercise 4.99.7 (1): The open first-uncountable ordinal is not paracompact. -/
#check OpenOmegaOne.notParacompact

/- Exercise 4.99.7 (2): The closed first-uncountable ordinal is paracompact. -/
#check (inferInstance : ParacompactSpace ClosedOmegaOne)

/- Exercise 4.99.7 (3): The product of the open and closed first-uncountable
ordinals is not paracompact. -/
#check OpenOmegaOne.prodClosedOmegaOne_notParacompact

/- Exercise 4.99.7 (4): The ordered square is paracompact. -/
#check (inferInstance : ParacompactSpace OrderedSquare)

/- Exercise 4.99.7 (5): The Sorgenfrey line is paracompact. -/
#check SorgenfreyLine.instParacompactSpace

/- Exercise 4.99.7 (6): The square-metric plane is paracompact. -/
#check (inferInstance : ParacompactSpace (Fin 2 → ℝ))

/- Exercise 4.99.7 (7): The countable product of real lines is paracompact. -/
#check (inferInstance : ParacompactSpace (ℕ → ℝ))

/- Exercise 4.99.7 (8): Real sequence space with the uniform topology is
paracompact. -/
#check (inferInstance : ParacompactSpace UniformRealSequence)

/- Exercise 4.99.7 (9): The paracompactness of real sequence space with the
box topology is not settled by the results assumed in the text. -/
#check ParacompactSpace BoxRealSequence

/- Exercise 4.99.7 (10): The product of real lines indexed by the unit interval
is not paracompact. -/
#check (realPower_not_paracompact : ¬ ParacompactSpace (unitInterval → ℝ))

/-- Part (11) of Exercise 4.99.7: The real line with the `K`-topology is not
paracompact. -/
theorem kTopologyReal_not_paracompact :
    ¬ ParacompactSpace RealKLine := by
  -- A Hausdorff paracompact K-line would be regular, contradicting its defining obstruction.
  intro h
  letI : ParacompactSpace RealKLine := h
  exact RealTopology.kNotRegularSpace (inferInstance : RegularSpace RealKLine)

/-- Exercise 4.99.7 local theorem family compatibility entry: the real line with
the `K`-topology is not paracompact. -/
theorem «Exercise 4.99.7 local theorem family» :
    ¬ ParacompactSpace RealKLine := by
  -- Expose the established atomic result under the planner's declaration name.
  exact kTopologyReal_not_paracompact

/-- Exercise 4.99.7 (12): The open first-uncountable ordinal is not topologically
complete. -/
theorem openOmegaOne_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace OpenOmegaOne := by
  intro h
  exact OpenOmegaOne.notMetrizable inferInstance

/-- Exercise 4.99.7 (13): The closed first-uncountable ordinal is not
topologically complete. -/
theorem closedOmegaOne_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace ClosedOmegaOne := by
  intro h
  exact ClosedOmegaOne.notMetrizable inferInstance

/-- Exercise 4.99.7 (14): The product of the open and closed first-uncountable
ordinals is not topologically complete. -/
theorem omegaOneProduct_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace
      (OpenOmegaOne × ClosedOmegaOne) := by
  intro h
  exact OmegaOneProduct.notMetrizable inferInstance

/-- Exercise 4.99.7 (15): The ordered square is not topologically complete. -/
theorem orderedSquare_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace OrderedSquare := by
  intro h
  exact OrderedSquare.notMetrizable inferInstance

/-- Exercise 4.99.7 (16): The Sorgenfrey line is not topologically complete. -/
theorem sorgenfreyLine_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace SorgenfreyLine := by
  intro h
  exact SorgenfreyLine.notMetrizable inferInstance

/- Exercise 4.99.7 (17): The square-metric plane is topologically complete. -/
#check (inferInstance :
  TopologicalSpace.IsCompletelyMetrizableSpace (Fin 2 → ℝ))

/- Exercise 4.99.7 (18): The countable product of real lines is topologically
complete. -/
#check (inferInstance :
  TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → ℝ))

/- Exercise 4.99.7 (19): Real sequence space with the uniform topology is
topologically complete. -/
#check uniformRealSequencesCompletelyMetrizable

/-- Exercise 4.99.7 (20): Real sequence space with the box topology is not
topologically complete. -/
theorem boxRealSequences_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace BoxRealSequence := by
  -- Complete metrizability implies metrizability, which the countable box product lacks.
  intro h
  letI : TopologicalSpace.IsCompletelyMetrizableSpace BoxRealSequence := h
  exact Pi.real_box_not_metrizable ℕ inferInstance

/-- Exercise 4.99.7 (21): The product of real lines indexed by the unit interval
is not topologically complete. -/
theorem unitIntervalRealPower_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (unitInterval → ℝ) := by
  intro h
  exact UnitIntervalRealPower.notMetrizable inferInstance

/-- Exercise 4.99.7 (22): The real line with the `K`-topology is not
topologically complete. -/
theorem kTopologyReal_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace RealKLine := by
  -- Complete metrizability would supply a compatible metric on the K-line.
  intro h
  letI : TopologicalSpace.IsCompletelyMetrizableSpace RealKLine := h
  exact RealKLine.notMetrizable inferInstance

/- Exercise 4.99.7 (23): Every metrizable space is paracompact. -/
#check Metric.instParacompactSpace

/-- Exercise 4.99.7 (24): A metrizable space need not be topologically complete. -/
theorem rationals_not_completelyMetrizable :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace ℚ := by
  -- A completely metrizable space is Baire, but the rational singleton cover is meagre.
  intro h
  letI : TopologicalSpace.IsCompletelyMetrizableSpace ℚ := h
  letI : BaireSpace ℚ := BaireSpace.of_completelyPseudoMetrizable
  obtain ⟨q, hq⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun r : ℚ ↦ ({r} : Set ℚ)) (fun _ ↦ isClosed_singleton) (Set.iUnion_of_singleton ℚ)
  rw [interior_singleton] at hq
  exact Set.not_nonempty_empty hq

/- Exercise 4.99.7 (25): Every compact space, hence every compact Hausdorff
space, is paracompact. -/
#check paracompact_of_compact

/- Exercise 4.99.7 (26): The compact Hausdorff ordered square is not
topologically complete. -/
#check orderedSquare_not_completelyMetrizable

/- Exercise 4.99.7 (27): Paracompactness is not preserved by arbitrary
subspaces. -/
#check ParacompactSpace.not_hereditary

/- Exercise 4.99.7 (28): Paracompactness is preserved by closed subspaces. -/
#check Topology.IsClosedEmbedding.paracompactSpace

/-- Exercise 4.99.7 (29): Paracompactness is not preserved by open subspaces. -/
theorem paracompactness_not_preserved_by_openSubspaces :
    ¬ ∀ (X : Type u) [TopologicalSpace X] [ParacompactSpace X]
      (s : Set X), IsOpen s → ParacompactSpace s := by
  -- The lifted Sorgenfrey plane is the open canonical copy in its compactification.
  intro hpreserved
  let P := ULift.{u} (SorgenfreyLine × SorgenfreyLine)
  let s : Set (OnePoint P) := Set.range ((↑) : P → OnePoint P)
  have hRange : ParacompactSpace s :=
    hpreserved (OnePoint P) s OnePoint.isOpen_range_coe
  have hLifted : ParacompactSpace P :=
    (OnePoint.isOpenEmbedding_coe (X := P)).isEmbedding.toHomeomorph.paracompactSpace_iff.mpr
      hRange
  have hPlane : ParacompactSpace (SorgenfreyLine × SorgenfreyLine) :=
    Homeomorph.ulift.paracompactSpace_iff.mp hLifted
  letI : ParacompactSpace (SorgenfreyLine × SorgenfreyLine) := hPlane
  exact SorgenfreyPlane.notT4 T4Space.of_paracompactSpace_t2Space

/-- Exercise 4.99.7 (30): Topological completeness is not preserved by
arbitrary subspaces. -/
theorem completeMetrizability_not_preserved_by_subspaces :
    ¬ ∀ (X : Type u) [TopologicalSpace X]
      [TopologicalSpace.IsCompletelyMetrizableSpace X] (s : Set X),
      TopologicalSpace.IsCompletelyMetrizableSpace s := by
  -- Embed the rationals into the completely metrizable lifted real line.
  intro hpreserved
  let f : ℚ → ULift.{u} ℝ := fun q ↦ ULift.up (q : ℝ)
  have hf : Topology.IsEmbedding f :=
    Homeomorph.ulift.symm.isEmbedding.comp Rat.isEmbedding_coe_real
  let s : Set (ULift.{u} ℝ) := Set.range f
  have hRange : TopologicalSpace.IsCompletelyMetrizableSpace s :=
    hpreserved (ULift.{u} ℝ) s
  letI : TopologicalSpace.IsCompletelyMetrizableSpace s := hRange
  have hRat : TopologicalSpace.IsCompletelyMetrizableSpace ℚ :=
    hf.toHomeomorph.isClosedEmbedding.IsCompletelyMetrizableSpace
  exact rationals_not_completelyMetrizable hRat

/- Exercise 4.99.7 (31): Topological completeness is preserved by closed
subspaces. -/
#check IsClosed.isCompletelyMetrizableSpace

/- Exercise 4.99.7 (32): Topological completeness is preserved by open
subspaces. -/
#check IsOpen.isCompletelyMetrizableSpace

/- Exercise 4.99.7 (33): Paracompactness is not preserved by finite products. -/
#check ParacompactSpace.not_closed_under_finTwo_pi

/-- Exercise 4.99.7 (34): Paracompactness is not preserved by countable
products. -/
theorem paracompactness_not_preserved_by_countableProducts :
    ¬ ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)]
      [∀ i, ParacompactSpace (X i)], ParacompactSpace (∀ i, X i) := by
  -- Padding a binary family would turn countable closure into the known-false finite closure.
  intro h
  exact ParacompactSpace.not_closed_under_finTwo_pi (paracompactFinTwoPiOfNatPi h)

/-- Exercise 4.99.7 (35): Paracompactness is not preserved by arbitrary
products. -/
theorem paracompactness_not_preserved_by_arbitraryProducts :
    ¬ ∀ (ι : Type v) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
      [∀ i, ParacompactSpace (X i)], ParacompactSpace (∀ i, X i) := by
  -- Specializing arbitrary product closure to `ℕ` gives countable closure.
  intro h
  apply paracompactness_not_preserved_by_countableProducts
  intro X topologyX paracompactX
  have hLifted : ParacompactSpace (∀ i : ULift.{v} ℕ, X i.down) :=
    h (ULift.{v} ℕ) (fun i ↦ X i.down)
  exact (Homeomorph.piCongrLeft (Y := X) Homeomorph.ulift.toEquiv).paracompactSpace_iff.mp
    hLifted

/- Exercise 4.99.7 (36): Topological completeness is preserved by finite
products. -/
#check TopologicalSpace.IsCompletelyMetrizableSpace.prod

/- Exercise 4.99.7 (37): Topological completeness is preserved by countable
products. -/
#check TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable

/- Exercise 4.99.7 (38): The product of completely metrizable real lines
indexed by the unit interval is not topologically complete. -/
#check unitIntervalRealPower_not_completelyMetrizable

/-- Exercise 4.99.7 (39): Paracompactness is not always preserved by
continuous surjections. -/
theorem continuousImage_not_always_paracompact :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [ParacompactSpace X] (f : X → Y),
      Continuous f → Function.Surjective f → ParacompactSpace Y := by
  -- A completely metrizable discrete cover maps continuously onto the nonparacompact K-line.
  intro hpreserved
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable
    (ULift.{u} (WithDiscreteTopology RealKLine))
  have hTarget := hpreserved _ _ (liftedDiscreteCover RealKLine)
    (liftedDiscreteCover_continuous RealKLine)
    (liftedDiscreteCover_surjective RealKLine)
  letI : ParacompactSpace (ULift.{v} RealKLine) := hTarget
  exact kTopologyReal_not_paracompact
    (Homeomorph.ulift.paracompactSpace_iff.mp hTarget)

/-- Exercise 4.99.7 (40): Topological completeness is not always preserved by
continuous surjections. -/
theorem continuousImage_not_always_completelyMetrizable :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [TopologicalSpace.IsCompletelyMetrizableSpace X] (f : X → Y),
      Continuous f → Function.Surjective f →
        TopologicalSpace.IsCompletelyMetrizableSpace Y := by
  -- The discrete cover is completely metrizable but maps onto the nonmetrizable K-line.
  intro hpreserved
  have hTarget := hpreserved _ _ (liftedDiscreteCover RealKLine)
    (liftedDiscreteCover_continuous RealKLine)
    (liftedDiscreteCover_surjective RealKLine)
  letI : TopologicalSpace.IsCompletelyMetrizableSpace
      (ULift.{v} RealKLine) := hTarget
  have hBase : TopologicalSpace.IsCompletelyMetrizableSpace RealKLine :=
    Homeomorph.ulift.symm.isClosedEmbedding.IsCompletelyMetrizableSpace
  exact kTopologyReal_not_completelyMetrizable hBase

end
