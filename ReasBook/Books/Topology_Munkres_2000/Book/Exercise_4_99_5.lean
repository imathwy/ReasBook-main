module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Example_31_2.Instances
public import Topology_Munkres_2000.Book.Example_31_3.Separation
public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Topology_Munkres_2000.Book.Exercise_4_99_5.Products
public import Topology_Munkres_2000.Book.Exercise_4_99_1.LocallyMetrizable
public import Topology_Munkres_2000.Book.Theorem_21_2.Instances
public import Mathlib.Topology.UnitInterval
import Topology_Munkres_2000.Book.Example_28_3
import Topology_Munkres_2000.Book.Exercise_28_3
import Topology_Munkres_2000.Book.Exercise_4_99_4.Subspace
import Topology_Munkres_2000.Book.Exercise_29_2
import Topology_Munkres_2000.Book.Theorem_20_2
import Topology_Munkres_2000.Book.Theorem_34_3
import Topology_Munkres_2000.Book.Example_30_4
import Topology_Munkres_2000.Book.Exercise_4_99_5.CardinalSelection
import Topology_Munkres_2000.Book.Exercise_4_99_5.NovakDerivedSet
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.DerivedSet

public section

universe u v

/- Exercise 4.99.5 refers, in order, to the following list printed at the start of the
supplementary exercises: connected, path connected, locally connected, locally path
connected, compact, limit point compact, locally compact Hausdorff, Hausdorff,
regular, completely regular, normal, first-countable, second-countable, Lindelöf,
having a countable dense subset, locally metrizable, and metrizable. -/

/- Exercise 4.99.5 (1): Connectedness is preserved by arbitrary products. -/
#check instConnectedSpaceForall

/- Exercise 4.99.5 (2): Path connectedness is preserved by arbitrary products. -/
#check Pi.instPathConnectedSpace

/- Exercise 4.99.5 (3): Local connectedness is preserved by finite products. -/
#check Pi.locallyConnectedSpace_of_finite

/- Exercise 4.99.5 (4): Although `Bool` is discrete and hence locally connected, its
countable power with the product topology is not locally connected. -/
#check (inferInstance : LocallyConnectedSpace Bool)

/-- Helper for Exercise 4.99.5: a locally connected totally disconnected space is discrete. -/
lemma discreteTopologyOfLocallyConnectedTotallyDisconnected {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] [TotallyDisconnectedSpace X] :
    DiscreteTopology X := by
  -- Every connected component is both a singleton and an open set.
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  rw [← connectedComponent_eq_singleton x]
  exact isOpen_connectedComponent

/-- The countable product of copies of `Bool` is not locally connected. -/
theorem boolSequences_not_locallyConnected :
    ¬ LocallyConnectedSpace (ℕ → Bool) := by
  -- Local connectedness would make compact Cantor space discrete and hence finite.
  intro hlocal
  letI : LocallyConnectedSpace (ℕ → Bool) := hlocal
  letI : DiscreteTopology (ℕ → Bool) :=
    discreteTopologyOfLocallyConnectedTotallyDisconnected
  letI : Finite (ℕ → Bool) := finite_of_compact_of_discrete
  exact Infinite.false (α := ℕ → Bool) inferInstance

/- Exercise 4.99.5 (5): Local path connectedness is preserved by finite products. -/
#check Pi.locallyPathConnectedSpace_of_finite

/- Exercise 4.99.5 (6): Although `Bool` is discrete and hence locally path connected,
its countable power with the product topology is not locally path connected. -/
#check (inferInstance : LocallyPathConnectedSpace Bool)

/-- The countable product of copies of `Bool` is not locally path-connected. -/
theorem boolSequences_not_locallyPathConnected :
    ¬ LocallyPathConnectedSpace (ℕ → Bool) := by
  -- Local path connectedness implies the already-refuted local connectedness.
  intro hlocal
  letI : LocallyPathConnectedSpace (ℕ → Bool) := hlocal
  exact boolSequences_not_locallyConnected inferInstance

/- Exercise 4.99.5 (7): Compactness is preserved by arbitrary products. -/
#check Pi.compactSpace

/-- Helper for Exercise 4.99.5: an ambient accumulation point of the image of a
subtype set induces an accumulation point in the subtype. -/
private lemma accPt_subtype_of_accPt_image {K : Type*} [TopologicalSpace K]
    {A : Set K} {s : Set A} {x : A}
    (hx : AccPt x.1 (Filter.principal (Subtype.val '' s))) :
    AccPt x (Filter.principal s) := by
  -- Refine a subtype neighborhood to an ambient neighborhood and use the ambient point.
  rw [accPt_iff_nhds]
  intro v hv
  obtain ⟨w, hw, hwv⟩ := (mem_nhds_subtype A x v).mp hv
  obtain ⟨y, hy, hyx⟩ := accPt_iff_nhds.mp hx w hw
  obtain ⟨z, hzs, rfl⟩ := hy.2
  refine ⟨z, ⟨hwv hy.1, hzs⟩, ?_⟩
  intro hzx
  exact hyx (congrArg Subtype.val hzx)

/-- Helper for Exercise 4.99.5: a set of selected accumulation points meeting the
derived set of every countably infinite set makes its union with any set limit point compact. -/
private lemma limitPointCompactSpace_union_of_derivedSelector
    {K : Type*} [TopologicalSpace K] (D P : Set K)
    (hP : ∀ S : Set K, S.Countable → S.Infinite →
      (P ∩ derivedSet S).Nonempty) :
    LimitPointCompactSpace {x : K // x ∈ D ∪ P} := by
  -- Reduce an arbitrary infinite subtype set to a countably infinite ambient subset.
  rw [limitPointCompactSpace_iff]
  intro s hs
  have hsImage : (Subtype.val '' s : Set K).Infinite :=
    hs.image Subtype.val_injective.injOn
  obtain ⟨T, hTsub, hTcountable, hTinfinite⟩ :=
    hsImage.exists_subset_countable_infinite
  obtain ⟨p, hpP, hpAcc⟩ := hP T hTcountable hTinfinite
  let x : {x : K // x ∈ D ∪ P} := ⟨p, Set.mem_union_right D hpP⟩
  -- Monotonicity enlarges the selected countable set back to the original set.
  have hxAmbient : AccPt x.1 (Filter.principal (Subtype.val '' s)) :=
    hpAcc.mono (Filter.principal_mono.mpr hTsub)
  exact ⟨x, accPt_subtype_of_accPt_image hxAmbient⟩

/-- Helper for Exercise 4.99.5: two subspaces with disjoint remainders have a
closed discrete diagonal whenever their common discrete core is infinite. -/
private lemma diagonalSubtypes_not_limitPointCompact
    {K : Type*} [TopologicalSpace K] [T2Space K]
    (D P Q : Set K) (hDinfinite : D.Infinite)
    (hDopen : ∀ x ∈ D, IsOpen ({x} : Set K)) (hPQ : Disjoint P Q) :
    ¬ LimitPointCompactSpace
      ({x : K // x ∈ D ∪ P} × {x : K // x ∈ D ∪ Q}) := by
  classical
  let A : Set K := D ∪ P
  let B : Set K := D ∪ Q
  let toA : D → A := fun x ↦ ⟨x, Set.mem_union_left P x.property⟩
  let toB : D → B := fun x ↦ ⟨x, Set.mem_union_left Q x.property⟩
  let diagonalMap : D → A × B := fun x ↦ (toA x, toB x)
  let E : Set (A × B) := Set.range diagonalMap
  -- The diagonal map remembers its index in either coordinate.
  have hDiagonalInjective : Function.Injective diagonalMap := by
    intro x y hxy
    have hfirst := congrArg (fun z : A × B ↦ (z.1 : K)) hxy
    exact Subtype.ext hfirst
  letI : Infinite D := hDinfinite.to_subtype
  have hEinfinite : E.Infinite :=
    Set.infinite_range_of_injective hDiagonalInjective
  -- Equality of the two ambient coordinates characterizes the selected diagonal.
  have hErange :
      E = {z : A × B | (z.1 : K) = (z.2 : K)} := by
    ext z
    constructor
    · rintro ⟨d, rfl⟩
      rfl
    · intro hz
      have hzA : (z.1 : K) ∈ D ∨ (z.1 : K) ∈ P := z.1.property
      have hzB : (z.2 : K) ∈ D ∨ (z.2 : K) ∈ Q := z.2.property
      have hzD : (z.1 : K) ∈ D := by
        rcases hzA with hzD | hzP
        · exact hzD
        · rcases hzB with hzD | hzQ
          · exact hz.symm ▸ hzD
          · exact False.elim (Set.disjoint_left.mp hPQ hzP (hz.symm ▸ hzQ))
      refine ⟨⟨z.1, hzD⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hz
  -- Hausdorffness makes the ambient diagonal closed, hence `E` is closed.
  have hEclosed : IsClosed E := by
    rw [hErange]
    let ambientPair : A × B → K × K :=
      fun z ↦ ((z.1 : K), (z.2 : K))
    have hAmbientPair : Continuous ambientPair :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact isClosed_diagonal.preimage hAmbientPair
  -- An open singleton in the first coordinate isolates each point of `E`.
  have hEdiscrete : IsDiscrete E := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    obtain ⟨d, rfl⟩ := hz
    let firstValue : A × B → K := fun w ↦ w.1
    let U : Set (A × B) := firstValue ⁻¹' {d.1}
    refine ⟨U, (hDopen d d.property).preimage
      (continuous_subtype_val.comp continuous_fst), ?_⟩
    ext w
    constructor
    · rintro ⟨hwU, e, rfl⟩
      have hed : e = d := by
        apply Subtype.ext
        exact hwU
      subst e
      rfl
    · intro hw
      have hwEq : w = diagonalMap d := by
        simpa only [Set.mem_singleton_iff] using hw
      subst w
      exact ⟨rfl, d, rfl⟩
  -- A closed subspace would inherit limit point compactness, contradicting discreteness.
  intro hProduct
  letI : LimitPointCompactSpace (A × B) := hProduct
  letI : LimitPointCompactSpace E := hEclosed.limitPointCompactSpace
  letI : Infinite E := hEinfinite.to_subtype
  letI : DiscreteTopology E := isDiscrete_iff_discreteTopology.mp hEdiscrete
  obtain ⟨x, hx⟩ := LimitPointCompactSpace.exists_accPt (Set.univ : Set E) Set.infinite_univ
  rw [accPt_iff_nhds] at hx
  obtain ⟨y, hy, hyx⟩ := hx {x} (discreteTopology_iff_singleton_mem_nhds.mp inferInstance x)
  have hyEq : y = x := by
    simpa only [Set.mem_singleton_iff] using hy.1
  exact hyx hyEq

/-- Helper for Exercise 4.99.5: pure ultrafilters are isolated in the Stone–Čech
topology on `Ultrafilter ℕ`. -/
private lemma ultrafilterPure_isOpen_singleton (n : ℕ) :
    IsOpen ({pure n} : Set (Ultrafilter ℕ)) := by
  -- The basic clopen set determined by `{n}` contains only the pure ultrafilter at `n`.
  have heq : {F : Ultrafilter ℕ | {n} ∈ F} = {pure n} := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hF
      obtain ⟨m, hm, hFm⟩ :=
        F.eq_pure_of_finite_mem (Set.finite_singleton n) hF
      have hmn : m = n := by
        simpa only [Set.mem_singleton_iff] using hm
      subst m
      exact hFm
    · intro hF
      subst F
      exact Ultrafilter.mem_pure.mpr (Set.mem_singleton n)
  rw [← heq]
  exact ultrafilter_isOpen_basic ({n} : Set ℕ)

/-- Helper for Exercise 4.99.5: there are two disjoint sets of ultrafilters, each
meeting the derived set of every countably infinite subset of `Ultrafilter ℕ`. -/
private lemma existsDisjointUltrafilterAccPtSelectors :
    ∃ P Q : Set (Ultrafilter ℕ), Disjoint P Q ∧
      (∀ S : Set (Ultrafilter ℕ), S.Countable → S.Infinite →
        (P ∩ derivedSet S).Nonempty) ∧
      (∀ S : Set (Ultrafilter ℕ), S.Countable → S.Infinite →
        (Q ∩ derivedSet S).Nonempty) := by
  classical
  let I := {S : Set (Ultrafilter ℕ) // S.Countable ∧ S.Infinite}
  -- Encode every constraint, together with one Boolean selector slot, by a sequence.
  have hEnumeration (S : I) : ∃ a : ℕ → Ultrafilter ℕ, S.1 = Set.range a :=
    S.property.1.exists_eq_range S.property.2.nonempty
  let enumeration : I → ℕ → Ultrafilter ℕ := fun S ↦
    Classical.choose (hEnumeration S)
  have hEnumerationRange (S : I) : S.1 = Set.range (enumeration S) :=
    Classical.choose_spec (hEnumeration S)
  let boolCode : Bool → ℕ := fun b ↦ if b then 1 else 0
  have hBoolCode : Function.Injective boolCode := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [boolCode]
  let code : I × Bool → ℕ → Ultrafilter ℕ := fun p n ↦
    match n with
    | 0 => pure (boolCode p.2)
    | n + 1 => enumeration p.1 n
  have hCodeInjective : Function.Injective code := by
    intro p q hpq
    apply Prod.ext
    · apply Subtype.ext
      rw [hEnumerationRange p.1, hEnumerationRange q.1]
      congr 1
      funext n
      exact congrFun hpq (n + 1)
    · apply hBoolCode
      apply Ultrafilter.pure_injective
      exact congrFun hpq 0
  -- Exact ultrafilter cardinal arithmetic bounds the two-slot constraint type.
  have hIndexCard : Cardinal.mk (I × Bool) ≤ Cardinal.mk (Ultrafilter ℕ) := by
    calc
      Cardinal.mk (I × Bool) ≤ Cardinal.mk (ℕ → Ultrafilter ℕ) :=
        Cardinal.mk_le_of_injective hCodeInjective
      _ = Cardinal.mk (Ultrafilter ℕ) := by
        rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat,
          cardinalMk_ultrafilterNat, ← Cardinal.power_mul, Cardinal.lift_aleph0,
          Cardinal.continuum_mul_aleph0]
  -- Novák's theorem supplies a full-cardinality candidate set at every constraint.
  let candidates : I × Bool → Set (Ultrafilter ℕ) := fun p ↦ derivedSet p.1.1
  have hCandidateCard (p : I × Bool) :
      Cardinal.mk (Ultrafilter ℕ) ≤ Cardinal.mk (candidates p) := by
    exact (ultrafilterNat_derivedSet_cardinalMk p.1.1 p.1.property.1
      p.1.property.2).ge
  obtain ⟨f, hfInjective, hfMem⟩ :=
    existsInjective_mem_of_cardinalMk_le candidates hIndexCard hCandidateCard
  let P : Set (Ultrafilter ℕ) := Set.range (fun S : I ↦ f (S, false))
  let Q : Set (Ultrafilter ℕ) := Set.range (fun S : I ↦ f (S, true))
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.mpr (fun x hxP hxQ ↦ ?_)
    obtain ⟨S, rfl⟩ := hxP
    obtain ⟨T, hST⟩ := hxQ
    have hIndexEq := hfInjective hST
    exact Bool.false_ne_true (congrArg Prod.snd hIndexEq).symm
  · intro S hSCountable hSInfinite
    let T : I := ⟨S, hSCountable, hSInfinite⟩
    exact ⟨f (T, false), ⟨⟨T, rfl⟩, hfMem (T, false)⟩⟩
  · intro S hSCountable hSInfinite
    let T : I := ⟨S, hSCountable, hSInfinite⟩
    exact ⟨f (T, true), ⟨⟨T, rfl⟩, hfMem (T, true)⟩⟩

/-- Exercise 4.99.5 (8): Limit point compactness is not preserved by finite products. -/
theorem limitPointCompactSpace_prod_counterexample :
    ∃ (X : Type u) (Y : Type v) (_ : TopologicalSpace X) (_ : TopologicalSpace Y),
      LimitPointCompactSpace X ∧ LimitPointCompactSpace Y ∧
        ¬ LimitPointCompactSpace (X × Y) := by
  classical
  -- The selector sets give two limit-point-compact subspaces with a bad diagonal.
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := existsDisjointUltrafilterAccPtSelectors
  let D : Set (Ultrafilter ℕ) := Set.range (pure : ℕ → Ultrafilter ℕ)
  let A : Type := {x : Ultrafilter ℕ // x ∈ D ∪ P}
  let B : Type := {x : Ultrafilter ℕ // x ∈ D ∪ Q}
  have hDinfinite : D.Infinite :=
    Set.infinite_range_of_injective Ultrafilter.pure_injective
  have hDopen : ∀ x ∈ D, IsOpen ({x} : Set (Ultrafilter ℕ)) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact ultrafilterPure_isOpen_singleton n
  letI : LimitPointCompactSpace A :=
    limitPointCompactSpace_union_of_derivedSelector D P hP
  letI : LimitPointCompactSpace B :=
    limitPointCompactSpace_union_of_derivedSelector D Q hQ
  have hBaseProduct : ¬ LimitPointCompactSpace (A × B) :=
    diagonalSubtypes_not_limitPointCompact D P Q hDinfinite hDopen hPQ
  -- Lift the two factors independently to the universes required by the statement.
  letI : LimitPointCompactSpace (ULift.{u} A) :=
    Homeomorph.ulift.symm.limitPointCompactSpace
  letI : LimitPointCompactSpace (ULift.{v} B) :=
    Homeomorph.ulift.symm.limitPointCompactSpace
  refine ⟨ULift.{u} A, ULift.{v} B, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  intro hLiftedProduct
  letI : LimitPointCompactSpace (ULift.{u} A × ULift.{v} B) := hLiftedProduct
  have hTransported : LimitPointCompactSpace (A × B) :=
    (Homeomorph.ulift.prodCongr Homeomorph.ulift).limitPointCompactSpace
  exact hBaseProduct hTransported

/- Exercise 4.99.5 (9): Local compactness is preserved by finite products, while the
Hausdorff property of the same product is inferred independently. -/
#check Pi.locallyCompactSpace_of_finite

/-- Exercise 4.99.5 (10): The countable product `ℕ → ℝ` is Hausdorff but not locally
compact, so locally compact Hausdorff spaces are not preserved by countable products. -/
theorem realSequences_not_locallyCompact : ¬ LocallyCompactSpace (ℕ → ℝ) := by
  -- Local compactness would make all but finitely many real factors compact.
  intro hlocal
  letI : LocallyCompactSpace (ℕ → ℝ) := hlocal
  have hcompact : ∀ᶠ _i : ℕ in Filter.cofinite, CompactSpace ℝ :=
    Pi.eventuallyCompactSpace
  have hnoncompact : ¬ CompactSpace ℝ :=
    not_compactSpace_iff.mpr inferInstance
  rw [Filter.eventually_cofinite] at hcompact
  have hunivFinite : (Set.univ : Set ℕ).Finite := by
    simpa only [hnoncompact, not_false_eq_true, Set.setOf_true] using hcompact
  exact Set.infinite_univ hunivFinite

#check (inferInstance : T2Space (ℕ → ℝ))

/- Exercise 4.99.5 (11): The Hausdorff property is preserved by arbitrary products. -/
#check Pi.t2Space

/- Exercise 4.99.5 (12): Regularity is preserved by arbitrary products. -/
#check instT3SpaceForall

/- Exercise 4.99.5 (13): Complete regularity is preserved by arbitrary products. -/
#check instT35SpaceForall

/- Exercise 4.99.5 (14): The Sorgenfrey line is normal, but the Sorgenfrey plane is
not normal, so normality is not preserved by finite products. -/
#check SorgenfreyLine.instT4Space
#check SorgenfreyPlane.notT4

/- Exercise 4.99.5 (15): First countability is preserved by countable products. -/
#check TopologicalSpace.instFirstCountableTopologyForallOfCountable

/-- Exercise 4.99.5 (16): The product `unitInterval → ℝ` shows that first countability
is not preserved by arbitrary products. -/
theorem unitIntervalRealPower_not_firstCountable :
    ¬ FirstCountableTopology (unitInterval → ℝ) := by
  -- A first-countable real product has a countable coordinate type.
  intro hfirst
  letI : FirstCountableTopology (unitInterval → ℝ) := hfirst
  have hcountable : Countable unitInterval :=
    Pi.countable_of_firstCountable_real_pi unitInterval
  have hinterval : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp hcountable
  have hcollapsed : (1 : ℝ) ≤ 0 :=
    Cardinal.Real.Icc_countable_iff.mp hinterval
  exact (not_le_of_gt zero_lt_one) hcollapsed

/- Exercise 4.99.5 (17): Second countability is preserved by countable products. -/
#check TopologicalSpace.instSecondCountableTopologyForallOfCountable

/-- Exercise 4.99.5 (18): The product `unitInterval → ℝ` shows that second countability
is not preserved by arbitrary products. -/
theorem unitIntervalRealPower_not_secondCountable :
    ¬ SecondCountableTopology (unitInterval → ℝ) := by
  -- Second countability would supply the already-refuted first countability.
  intro hsecond
  letI : SecondCountableTopology (unitInterval → ℝ) := hsecond
  exact unitIntervalRealPower_not_firstCountable inferInstance

/- Exercise 4.99.5 (19): The Sorgenfrey line is Lindelöf, but the Sorgenfrey plane is
not Lindelöf, so the Lindelöf property is not preserved by finite products. -/
#check SorgenfreyLine.instLindelofSpace
#check (inferInstance : NonLindelofSpace (SorgenfreyLine × SorgenfreyLine))

/- Exercise 4.99.5 (20): Having a countable dense subset is preserved by countable products. -/
#check TopologicalSpace.instSeparableSpaceForallOfCountable

/- Exercise 4.99.5 (21): Although the discrete two-point space `Bool` is separable,
its product indexed by `Set ℝ` is not separable. -/
#check (inferInstance : TopologicalSpace.SeparableSpace Bool)

/-- Helper for Exercise 4.99.5: a dense set in a Boolean product separates distinct
coordinates. -/
private lemma denseBoolPi_exists_coordinateSeparator {J : Type u} {D : Set (J → Bool)}
    (hD : Dense D) {α β : J} (hαβ : α ≠ β) :
    ∃ d : D, d.1 α = true ∧ d.1 β = false := by
  classical
  -- A two-coordinate cylinder is open and contains an explicit Boolean sequence.
  let U : Set (J → Bool) :=
    (fun f ↦ f α) ⁻¹' {true} ∩ (fun f ↦ f β) ⁻¹' {false}
  have hUOpen : IsOpen U :=
    (isOpen_discrete {true}).preimage (continuous_apply α) |>.inter
      ((isOpen_discrete {false}).preimage (continuous_apply β))
  have hUNonempty : U.Nonempty := by
    let f : J → Bool := Function.update (fun _ ↦ false) α true
    refine ⟨f, ?_⟩
    simp only [U, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · simp only [f, Function.update_self]
    · simp [f, Ne.symm hαβ]
  -- Density supplies a member of `D` in the separating cylinder.
  obtain ⟨f, hfD, hfU⟩ := hD.exists_mem_open hUOpen hUNonempty
  refine ⟨⟨f, hfD⟩, ?_, ?_⟩
  · simpa only [U, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hfU.1
  · simpa only [U, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hfU.2

/-- Helper for Exercise 4.99.5: coordinatewise truth traces on a dense subset of a
Boolean product distinguish the coordinates. -/
private lemma coordinateTrueTrace_injective {J : Type u} {D : Set (J → Bool)}
    (hD : Dense D) :
    Function.Injective (fun α : J ↦ {d : D | d.1 α = true}) := by
  intro α β htrace
  -- A separator would belong to exactly one of two allegedly equal traces.
  by_contra hαβ
  obtain ⟨d, hdα, hdβ⟩ := denseBoolPi_exists_coordinateSeparator hD hαβ
  have hdTrace : d ∈ {d : D | d.1 β = true} :=
    (Set.ext_iff.mp htrace d).mp hdα
  exact Bool.false_ne_true (hdβ.symm.trans hdTrace)

/-- Helper for Exercise 4.99.5: the powerset of a countable subtype has cardinality
at most the continuum. -/
private lemma cardinalMk_set_le_continuum_of_countable {X : Type u} {D : Set X}
    (hD : D.Countable) : Cardinal.mk (Set D) ≤ Cardinal.continuum := by
  have hTwo : (2 : Cardinal) ≠ 0 := by
    norm_num
  -- Powerset cardinality is bounded by `2 ^ ℵ₀` for a countable carrier.
  rw [Cardinal.mk_set, ← Cardinal.two_power_aleph0]
  exact Cardinal.power_le_power_left hTwo hD.le_aleph0

/-- Helper for Exercise 4.99.5: separability of `J → Bool` bounds `Cardinal.mk J`
by the continuum. -/
lemma cardinalMk_le_continuum_of_boolPi_separable (J : Type u)
    [TopologicalSpace.SeparableSpace (J → Bool)] :
    Cardinal.mk J ≤ Cardinal.continuum := by
  -- Embed coordinates into the powerset of a countable dense set via truth traces.
  obtain ⟨D, hDCountable, hDDense⟩ :=
    TopologicalSpace.exists_countable_dense (α := J → Bool)
  calc
    Cardinal.mk J ≤ Cardinal.mk (Set D) :=
      Cardinal.mk_le_of_injective (coordinateTrueTrace_injective hDDense)
    _ ≤ Cardinal.continuum := cardinalMk_set_le_continuum_of_countable hDCountable

/-- The product of copies of `Bool` indexed by `Set ℝ` is not separable. -/
theorem boolSetRealPower_not_separable :
    ¬ TopologicalSpace.SeparableSpace (Set ℝ → Bool) := by
  -- Cantor's theorem contradicts the coordinate bound forced by separability.
  intro hseparable
  letI : TopologicalSpace.SeparableSpace (Set ℝ → Bool) := hseparable
  have hle : Cardinal.mk (Set ℝ) ≤ Cardinal.continuum :=
    cardinalMk_le_continuum_of_boolPi_separable (Set ℝ)
  have hlt : Cardinal.continuum < Cardinal.mk (Set ℝ) := by
    rw [Cardinal.mk_set, Cardinal.mk_real]
    exact Cardinal.cantor _
  exact (not_le_of_gt hlt) hle

/- Exercise 4.99.5 (22): Local metrizability is preserved by finite products. -/
#check Pi.locallyMetrizableSpace_of_finite

/-- Helper for Exercise 4.99.5: a locally metrizable product of nonempty T₁ spaces
has only finitely many nonmetrizable factors. -/
lemma finiteNonmetrizableFactorsOfPiLocallyMetrizable
    {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, Nonempty (X i)] [∀ i, T1Space (X i)]
    [LocallyMetrizableSpace ((i : ι) → X i)] :
    {i | ¬ TopologicalSpace.MetrizableSpace (X i)}.Finite := by
  classical
  -- Refine a metrizable neighborhood of a base point to a finite-support cylinder.
  let x : (i : ι) → X i := fun i ↦ Classical.choice (inferInstance : Nonempty (X i))
  obtain ⟨s, hs, hsMetric⟩ := LocallyMetrizableSpace.exists_metrizable_nhds x
  obtain ⟨U, hUs, hUOpen, hxU⟩ := mem_nhds_iff.mp hs
  obtain ⟨I, V, hV, hVU⟩ := isOpen_pi_iff.mp hUOpen x hxU
  refine I.finite_toSet.subset ?_
  intro i hiNonmetric
  by_contra hiI
  -- Outside the support, updating coordinate `i` stays inside the cylinder.
  have hUpdateCylinder :
      ∀ z : X i, Function.update x i z ∈ (I : Set ι).pi V := by
    intro z j hj
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hiI hj
    simpa [Function.update, hji] using (hV j hj).2
  have hUpdateS : ∀ z : X i, Function.update x i z ∈ s := by
    intro z
    exact hUs (hVU (hUpdateCylinder z))
  -- The coordinate factor embeds into the metrizable neighborhood by this update map.
  letI : TopologicalSpace.MetrizableSpace s := hsMetric
  have hEmbedding : Topology.IsEmbedding
      (Set.codRestrict (Function.update x i) s hUpdateS) :=
    (isClosedEmbedding_update x i).isEmbedding.codRestrict s hUpdateS
  exact hiNonmetric hEmbedding.metrizableSpace

/-- Exercise 4.99.5 (23): Although the open first-uncountable ordinal is locally
metrizable, its countable power with the product topology is not locally metrizable. -/
theorem openOmegaOneSequences_not_locallyMetrizable :
    ¬ LocallyMetrizableSpace (ℕ → OpenOmegaOne) := by
  -- The generic finite-support lemma would make only finitely many factors nonmetrizable.
  intro hlocal
  letI : LocallyMetrizableSpace (ℕ → OpenOmegaOne) := hlocal
  have hfinite :
      {i : ℕ | ¬ TopologicalSpace.MetrizableSpace OpenOmegaOne}.Finite :=
    finiteNonmetrizableFactorsOfPiLocallyMetrizable
  have hnonmetric : ¬ TopologicalSpace.MetrizableSpace OpenOmegaOne :=
    OpenOmegaOne.notMetrizable
  have hnonmetricSet :
      {i : ℕ | ¬ TopologicalSpace.MetrizableSpace OpenOmegaOne} = Set.univ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hnonmetric
  rw [hnonmetricSet] at hfinite
  exact Set.infinite_univ hfinite

/- Exercise 4.99.5 (24): Metrizability is preserved by countable products. -/
#check TopologicalSpace.MetrizableSpace.pi_countable

/-- Exercise 4.99.5 (25): The product `unitInterval → ℝ` shows that metrizability is
not preserved by arbitrary products. -/
theorem unitIntervalRealPower_not_metrizable :
    ¬ TopologicalSpace.MetrizableSpace (unitInterval → ℝ) := by
  -- Metrizability would supply the already-refuted first countability.
  intro hmetric
  letI : TopologicalSpace.MetrizableSpace (unitInterval → ℝ) := hmetric
  exact unitIntervalRealPower_not_firstCountable inferInstance
