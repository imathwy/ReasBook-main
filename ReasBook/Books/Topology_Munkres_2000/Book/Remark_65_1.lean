module

public import Topology_Munkres_2000.Book.Definition_65_1.WindingNumber
public import Topology_Munkres_2000.Book.Exercise_62_4
public import Topology_Munkres_2000.Book.Remark_65_1.AffineLineCrosscut
public import Topology_Munkres_2000.Book.Remark_65_1.CrossingCover
public import Topology_Munkres_2000.Book.Remark_65_1.PairComplement
public import Topology_Munkres_2000.Book.Remark_65_1.PunctureMotion
public import Topology_Munkres_2000.Book.Theorem_63_1
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_5
public import Topology_Munkres_2000.Book.Theorem_63_6
public import Topology_Munkres_2000.Book.Theorem_58_2
public import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

namespace PuncturedPlaneMap

/-- The first assertion of Remark 65.1: an injective circle map into the punctured plane is
nullhomotopic when the origin component of the complement of its simple closed image is
unbounded. -/
theorem nullhomotopic_of_originComponent_unbounded
    (h : C(Circle, EuclideanPlane.punctured)) (h_injective : Function.Injective h)
    (h_unbounded : ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range (fun x : Circle ↦ (h x : EuclideanSpace ℝ (Fin 2))))ᶜ 0)) :
    h.Nullhomotopic := by
  -- Apply the planar specialization of Lemma 61.2 to the given embedding.
  exact (nullhomotopic_iff_originComponent_unbounded h h_injective).mpr h_unbounded

/-- Helper for Remark 65.1: an injective parametrization of `Circle` has a
simple-closed-curve range in a Hausdorff space. -/
private lemma isSimpleClosedCurve_range_of_injective
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(Circle, X)) (hf : Function.Injective f) :
    Topology.IsSimpleClosedCurve (Set.range f) := by
  -- Compactness turns the injective map into a homeomorphism onto its range.
  have hEmbedding : Topology.IsEmbedding f :=
    (f.continuous.isClosedEmbedding hf).isEmbedding
  apply (Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle _).mpr
  exact ⟨hEmbedding.toHomeomorph.symm⟩

/-- Helper for Remark 65.1: a nontrivial homomorphism between groups equipped
with infinite-cyclic coordinates is injective. -/
private lemma monoidHom_injective_of_equivInt_of_ne_one
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (sourceCoordinates : G ≃* Multiplicative ℤ)
    (targetCoordinates : H ≃* Multiplicative ℤ) (hf : f ≠ 1) :
    Function.Injective f := by
  -- Conjugate `f` to an endomorphism of the infinite cyclic group.
  let coordinateMap : Multiplicative ℤ →* Multiplicative ℤ :=
    targetCoordinates.toMonoidHom.comp
      (f.comp sourceCoordinates.symm.toMonoidHom)
  have coordinateMap_ne_one : coordinateMap ≠ 1 := by
    intro hcoordinate
    apply hf
    ext x
    apply targetCoordinates.injective
    calc
      targetCoordinates (f x) = coordinateMap (sourceCoordinates x) := by
        simp only [coordinateMap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      _ = 1 := by rw [hcoordinate]; rfl
      _ = targetCoordinates 1 := targetCoordinates.map_one.symm
  let additiveCoordinateMap : ℤ →+ ℤ := coordinateMap.toAdditive
  have additiveCoordinateMap_ne_zero : additiveCoordinateMap ≠ 0 := by
    intro hadditive
    apply coordinateMap_ne_one
    apply MonoidHom.toAdditive.injective
    exact hadditive
  have generator_image_ne_zero : additiveCoordinateMap 1 ≠ 0 := by
    intro hgenerator
    apply additiveCoordinateMap_ne_zero
    apply AddMonoidHom.ext_int
    simpa using hgenerator
  have additiveCoordinateMap_injective : Function.Injective additiveCoordinateMap := by
    intro m n hmn
    have hm : additiveCoordinateMap m = m * additiveCoordinateMap 1 := by
      simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using
        additiveCoordinateMap.map_zsmul m (1 : ℤ)
    have hn : additiveCoordinateMap n = n * additiveCoordinateMap 1 := by
      simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using
        additiveCoordinateMap.map_zsmul n (1 : ℤ)
    rw [hm, hn] at hmn
    exact mul_right_cancel₀ generator_image_ne_zero hmn
  have coordinateMap_injective : Function.Injective coordinateMap := by
    intro m n hmn
    apply Multiplicative.toAdd.injective
    apply additiveCoordinateMap_injective
    exact hmn
  -- Injectivity in coordinates transports back through the two equivalences.
  intro x y hxy
  apply sourceCoordinates.injective
  apply coordinateMap_injective
  simpa only [coordinateMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using congrArg targetCoordinates hxy

/-- Helper for Remark 65.1: an induced fundamental-group map commutes with
basepoint change along a path. -/
private lemma fundamentalGroupMap_basepointChange_naturality
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} (γ : Path x₀ x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (γ.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f x₀) =
      (FundamentalGroup.map f x₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom := by
  -- Functoriality maps conjugation by `γ` to conjugation by its image path.
  ext loop
  let F := FundamentalGroupoid.map f
  let sourceIso : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦γ⟧
  let targetIso : FundamentalGroupoid.mk (f x₀) ≅ FundamentalGroupoid.mk (f x₁) :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦γ.map f.continuous⟧
  have mapIso_eq : F.mapIso sourceIso = targetIso := by
    apply CategoryTheory.Iso.ext
    rfl
  change targetIso.conj (F.map loop) = F.map (sourceIso.conj loop)
  rw [← mapIso_eq]
  simp only [CategoryTheory.Iso.conj_apply, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  rfl

/-- Helper for Remark 65.1: surjectivity of an induced fundamental-group map
passes forward along a chosen basepoint path. -/
private lemma fundamentalGroupMap_surjective_of_path
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} (γ : Path x₀ x₁) :
    Function.Surjective (FundamentalGroup.map f x₀) →
      Function.Surjective (FundamentalGroup.map f x₁) := by
  -- Move a target loop backward across the target basepoint equivalence, then lift it.
  intro hsurjective targetLoop
  let sourceChange := FundamentalGroup.fundamentalGroupMulEquivOfPath γ
  let targetChange :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map f.continuous)
  obtain ⟨oldTarget, holdTarget⟩ := targetChange.surjective targetLoop
  obtain ⟨oldSource, holdSource⟩ := hsurjective oldTarget
  refine ⟨sourceChange oldSource, ?_⟩
  have naturality := DFunLike.congr_fun
    (fundamentalGroupMap_basepointChange_naturality f γ) oldSource
  calc
    FundamentalGroup.map f x₁ (sourceChange oldSource) =
        targetChange (FundamentalGroup.map f x₀ oldSource) := naturality.symm
    _ = targetChange oldTarget := congrArg targetChange holdSource
    _ = targetLoop := holdTarget

/-- Helper for Remark 65.1: surjectivity of an induced fundamental-group map
is independent of the basepoint along a chosen path. -/
private lemma fundamentalGroupMap_surjective_iff_of_path
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} (γ : Path x₀ x₁) :
    Function.Surjective (FundamentalGroup.map f x₀) ↔
      Function.Surjective (FundamentalGroup.map f x₁) := by
  -- Apply the forward transport to `γ` and to its reverse.
  constructor
  · exact fundamentalGroupMap_surjective_of_path f γ
  · exact fundamentalGroupMap_surjective_of_path f γ.symm

/-- Helper for Remark 65.1: crossing-cover data for a curve in a twice-punctured
sphere makes its inclusion surjective on fundamental groups at every curve basepoint. -/
private lemma pairComplementInclusionMap_surjective_of_crossingCover
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (p q : (Cᶜ : Set (StandardSphere 2)))
    (hpq : (p : StandardSphere 2) ≠ q) {a b : C}
    (α : Path a b) (β : Path b a)
    (data : FundamentalGroup.CrossingCoverData
      (ContinuousMap.inclusion (curve_subset_pairComplement C p q)) α β)
    (c : C) :
    Function.Surjective
      (FundamentalGroup.mapOfSubset (curve_subset_pairComplement C p q) c) := by
  classical
  -- Integer coordinates supply the two typeclass facts required by the crossing theorem.
  let inclusion : C(C, ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ :
      Set (StandardSphere 2))) :=
    ContinuousMap.inclusion (curve_subset_pairComplement C p q)
  obtain ⟨coordinates⟩ := StandardSphere.pairComplementFundamentalGroupEquivInt
    p q hpq (inclusion a)
  letI : Infinite (FundamentalGroup
      ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ : Set (StandardSphere 2))
      (inclusion a)) := coordinates.toEquiv.infinite_iff.mpr inferInstance
  letI : IsCyclic (FundamentalGroup
      ({(p : StandardSphere 2), (q : StandardSphere 2)}ᶜ : Set (StandardSphere 2))
      (inclusion a)) := coordinates.isCyclic.mpr inferInstance
  have surjectiveAtA : Function.Surjective (FundamentalGroup.map inclusion a) := by
    exact data.mapSurjective inclusion α β
  -- A simple closed curve is path connected, so transport the certificate to `c`.
  obtain ⟨curveEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : PathConnectedSpace C :=
    curveEquiv.symm.surjective.pathConnectedSpace curveEquiv.symm.continuous
  let basepointPath : Path a c := PathConnectedSpace.somePath a c
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  exact (fundamentalGroupMap_surjective_iff_of_path inclusion basepointPath).mp
    surjectiveAtA

/-- Helper for Remark 65.1: concatenating injective paths whose ranges meet only
at their common endpoint gives an injective path. -/
private lemma Path.trans_injective_of_range_inter_eq_singleton
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (alpha : Path x y) (beta : Path y z)
    (halpha : Function.Injective alpha) (hbeta : Function.Injective beta)
    (hinter : Set.range alpha ∩ Set.range beta = {y}) :
    Function.Injective (alpha.trans beta) := by
  -- Equal parameters in the same half are handled by the corresponding path;
  -- parameters in opposite halves must both represent the joining endpoint.
  have hcross (s t : unitInterval) (hs : (s : ℝ) ≤ 1 / 2)
      (ht : ¬ (t : ℝ) ≤ 1 / 2)
      (hst : (alpha.trans beta) s = (alpha.trans beta) t) : s = t := by
    rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
    have hsMem : 2 * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [s.property.1], by linarith⟩
    have htMem : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [not_le.mp ht], by linarith [t.property.2]⟩
    let s₁ : unitInterval := ⟨2 * (s : ℝ), hsMem⟩
    let t₂ : unitInterval := ⟨2 * (t : ℝ) - 1, htMem⟩
    change alpha s₁ = beta t₂ at hst
    have hsInter : alpha s₁ ∈ Set.range alpha ∩ Set.range beta :=
      ⟨Set.mem_range_self s₁, ⟨t₂, hst.symm⟩⟩
    rw [hinter, Set.mem_singleton_iff] at hsInter
    have hsOne : s₁ = 1 := halpha (hsInter.trans alpha.target.symm)
    have htZero : t₂ = 0 :=
      hbeta (hst.symm.trans hsInter |>.trans beta.source.symm)
    apply Subtype.ext
    have hsValue := congrArg Subtype.val hsOne
    have htValue := congrArg Subtype.val htZero
    dsimp [s₁, t₂] at hsValue htValue ⊢
    linarith
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have hparameters := congrArg Subtype.val (halpha hst)
      apply Subtype.ext
      dsimp at hparameters ⊢
      linarith
    · exact hcross s t hs ht hst
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · exact (hcross t s ht hs hst.symm).symm
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_neg ht] at hst
      have hparameters := congrArg Subtype.val (hbeta hst)
      apply Subtype.ext
      dsimp at hparameters ⊢
      linarith

/-- Helper for Remark 65.1: a nondegenerate subpath of an injective path is
injective. -/
private lemma Path.subpath_injective_of_ne
    {X : Type*} [TopologicalSpace X] {x y : X}
    (gamma : Path x y) (hgamma : Function.Injective gamma)
    (s t : unitInterval) (hst : s ≠ t) :
    Function.Injective (gamma.subpath s t) := by
  -- The affine interval reparametrization is injective when its endpoints differ.
  intro u v huv
  change gamma (Set.Icc.convexComb s t u) =
    gamma (Set.Icc.convexComb s t v) at huv
  have hparameters := congrArg Subtype.val (hgamma huv)
  have hvalues : (s : ℝ) ≠ (t : ℝ) := Subtype.coe_ne_coe.mpr hst
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb] at hparameters
  rcases lt_or_gt_of_ne hvalues with hlt | hgt
  · nlinarith
  · nlinarith

/-- Helper for Remark 65.1: an embedded path from outside a closed set to a
point of that set has an embedded initial subpath meeting the set only at its
terminal point. -/
private lemma existsEmbeddedInitialSubpathToClosedSet
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}
    (gamma : Path x y) (hgamma : Topology.IsEmbedding gamma)
    (D : Set X) (hDclosed : IsClosed D) (hx : x ∉ D) (hy : y ∈ D) :
    ∃ t : unitInterval, ∃ delta : Path x (gamma t),
      Topology.IsEmbedding delta ∧ gamma t ∈ D ∧
        Set.range delta ∩ D = {gamma t} := by
  classical
  -- The compact set of hitting parameters has a least member.
  let hitSet : Set unitInterval := gamma ⁻¹' D
  have hitSetClosed : IsClosed hitSet := hDclosed.preimage gamma.continuous
  have hitSetCompact : IsCompact hitSet :=
    isCompact_univ.of_isClosed_subset hitSetClosed (Set.subset_univ _)
  have hitSetNonempty : hitSet.Nonempty := by
    refine ⟨1, ?_⟩
    change gamma 1 ∈ D
    simpa only [gamma.target] using hy
  obtain ⟨t, htHit, htLeast⟩ := hitSetCompact.exists_isLeast hitSetNonempty
  have htNonzero : t ≠ 0 := by
    intro htZero
    apply hx
    change gamma t ∈ D at htHit
    rwa [htZero, gamma.source] at htHit
  let raw : Path (gamma 0) (gamma t) := gamma.subpath 0 t
  let delta : Path x (gamma t) := raw.cast gamma.source.symm rfl
  have deltaCoe : (delta : unitInterval → X) = raw :=
    Path.cast_coe raw gamma.source.symm rfl
  have deltaInjective : Function.Injective delta := by
    rw [deltaCoe]
    exact Path.subpath_injective_of_ne gamma hgamma.injective 0 t
      (Ne.symm htNonzero)
  refine ⟨t, delta, delta.continuous.isClosedEmbedding deltaInjective |>.isEmbedding,
    htHit, ?_⟩
  -- Minimality forces every point of the trimmed range lying in `D` to be the endpoint.
  rw [deltaCoe, Path.range_subpath_of_le gamma 0 t bot_le]
  ext w
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, huD⟩
    have huHit : u ∈ hitSet := huD
    have htu : t ≤ u := htLeast huHit
    have hut : u = t := le_antisymm hu.2 htu
    rw [Set.mem_singleton_iff, hut]
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact ⟨⟨t, ⟨bot_le, le_rfl⟩, rfl⟩, htHit⟩

/-- Helper for Remark 65.1: two embedded paths with a common endpoint contain
an embedded path joining their other endpoints. -/
private lemma existsEmbeddedPathInUnion
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y z : X}
    (alpha : Path x y) (beta : Path y z)
    (halpha : Topology.IsEmbedding alpha) (hbeta : Topology.IsEmbedding beta)
    (hxz : x ≠ z) :
    ∃ gamma : Path x z, Topology.IsEmbedding gamma ∧
      Set.range gamma ⊆ Set.range alpha ∪ Set.range beta := by
  classical
  -- Choose the first parameter at which `alpha` meets the compact range of `beta`.
  let hitSet : Set unitInterval := alpha ⁻¹' Set.range beta
  have hitSetClosed : IsClosed hitSet := by
    exact (isCompact_range beta.continuous).isClosed.preimage alpha.continuous
  have hitSetCompact : IsCompact hitSet :=
    isCompact_univ.of_isClosed_subset hitSetClosed (Set.subset_univ _)
  have hitSetNonempty : hitSet.Nonempty := by
    refine ⟨1, ?_⟩
    change alpha 1 ∈ Set.range beta
    exact ⟨0, beta.source.trans alpha.target.symm⟩
  obtain ⟨t₀, ht₀Hit, ht₀Least⟩ := hitSetCompact.exists_isLeast hitSetNonempty
  change alpha t₀ ∈ Set.range beta at ht₀Hit
  obtain ⟨s₀, hs₀⟩ := ht₀Hit
  by_cases ht₀Zero : t₀ = 0
  · -- If the first hit is the source, the terminal subpath of `beta` suffices.
    have hs₀One : s₀ ≠ 1 := by
      intro hs₀One
      apply hxz
      calc
        x = alpha 0 := alpha.source.symm
        _ = alpha t₀ := congrArg alpha ht₀Zero.symm
        _ = beta s₀ := hs₀.symm
        _ = beta 1 := congrArg beta hs₀One
        _ = z := beta.target
    let raw : Path (beta s₀) (beta 1) := beta.subpath s₀ 1
    have sourceEq : x = beta s₀ := by
      calc
        x = alpha 0 := alpha.source.symm
        _ = alpha t₀ := congrArg alpha ht₀Zero.symm
        _ = beta s₀ := hs₀.symm
    let gamma : Path x z := raw.cast sourceEq beta.target.symm
    have gammaCoe : (gamma : unitInterval → X) = raw :=
      Path.cast_coe raw sourceEq beta.target.symm
    have gammaInjective : Function.Injective gamma := by
      rw [gammaCoe]
      exact Path.subpath_injective_of_ne beta hbeta.injective s₀ 1 hs₀One
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    rw [Set.range_subset_iff, gammaCoe]
    intro u
    exact Or.inr ⟨Set.Icc.convexComb s₀ 1 u, rfl⟩
  by_cases hs₀One : s₀ = 1
  · -- Dually, a hit at the target of `beta` leaves only the initial subpath.
    let raw : Path (alpha 0) (alpha t₀) := alpha.subpath 0 t₀
    have targetEq : z = alpha t₀ := by
      calc
        z = beta 1 := beta.target.symm
        _ = beta s₀ := congrArg beta hs₀One.symm
        _ = alpha t₀ := hs₀
    let gamma : Path x z := raw.cast alpha.source.symm targetEq
    have gammaCoe : (gamma : unitInterval → X) = raw :=
      Path.cast_coe raw alpha.source.symm targetEq
    have gammaInjective : Function.Injective gamma := by
      rw [gammaCoe]
      exact Path.subpath_injective_of_ne alpha halpha.injective 0 t₀
        (Ne.symm ht₀Zero)
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    rw [Set.range_subset_iff, gammaCoe]
    intro u
    exact Or.inl ⟨Set.Icc.convexComb 0 t₀ u, rfl⟩
  · -- In the nondegenerate case, trim both paths and concatenate at the first hit.
    let leftRaw : Path (alpha 0) (alpha t₀) := alpha.subpath 0 t₀
    let rightRaw : Path (beta s₀) (beta 1) := beta.subpath s₀ 1
    let left : Path x (alpha t₀) := leftRaw.cast alpha.source.symm rfl
    let right : Path (alpha t₀) z := rightRaw.cast hs₀.symm beta.target.symm
    let gamma : Path x z := left.trans right
    have leftCoe : (left : unitInterval → X) = leftRaw :=
      Path.cast_coe leftRaw alpha.source.symm rfl
    have rightCoe : (right : unitInterval → X) = rightRaw :=
      Path.cast_coe rightRaw hs₀.symm beta.target.symm
    have leftInjective : Function.Injective left := by
      rw [leftCoe]
      exact Path.subpath_injective_of_ne alpha halpha.injective 0 t₀
        (Ne.symm ht₀Zero)
    have rightInjective : Function.Injective right := by
      rw [rightCoe]
      exact Path.subpath_injective_of_ne beta hbeta.injective s₀ 1 hs₀One
    have rangeInter : Set.range left ∩ Set.range right = {alpha t₀} := by
      rw [leftCoe, rightCoe, Path.range_subpath_of_le alpha 0 t₀ bot_le,
        Path.range_subpath_of_le beta s₀ 1 le_top]
      ext w
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
        have huHit : u ∈ hitSet := by
          change alpha u ∈ Set.range beta
          exact ⟨v, huv⟩
        have ht₀u : t₀ ≤ u := ht₀Least huHit
        have hut₀ : u = t₀ := le_antisymm hu.2 ht₀u
        rw [Set.mem_singleton_iff, hut₀]
      · intro hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact ⟨⟨t₀, ⟨bot_le, le_rfl⟩, rfl⟩,
          ⟨s₀, ⟨le_rfl, le_top⟩, hs₀⟩⟩
    have gammaInjective : Function.Injective gamma :=
      Path.trans_injective_of_range_inter_eq_singleton left right
        leftInjective rightInjective rangeInter
    refine ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding, ?_⟩
    change Set.range (left.trans right) ⊆ Set.range alpha ∪ Set.range beta
    rw [Path.trans_range, leftCoe, rightCoe]
    apply Set.union_subset
    · rw [Path.range_subpath]
      exact (Set.image_subset_range alpha _).trans Set.subset_union_left
    · rw [Path.range_subpath]
      exact (Set.image_subset_range beta _).trans Set.subset_union_right

/-- Helper for Remark 65.1: distinct points of an open connected subset of a
real normed vector space are joined inside it by an embedded path. -/
private lemma existsEmbeddedPathInOpenConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUconnected : IsConnected U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ gamma : Path x y, Topology.IsEmbedding gamma ∧ Set.range gamma ⊆ U := by
  -- Use embedded path access as the locally generated symmetric relation.
  let R : E → E → Prop := fun a b ↦
    a = b ∨ ∃ gamma : Path a b, Topology.IsEmbedding gamma ∧ Set.range gamma ⊆ U
  have localAccess : ∀ a ∈ U, ∀ᶠ b in nhdsWithin a U, R a b := by
    intro a ha
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hUopen a ha
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds a hepsilon)] with b hb
    by_cases hab : a = b
    · exact Or.inl hab
    · right
      let gamma : Path a b := Path.segment a b
      have gammaInjective : Function.Injective gamma :=
        Path.segment_injective_of_ne hab
      have gammaRange : Set.range gamma ⊆ U := by
        change Set.range (Path.segment a b) ⊆ U
        rw [Path.range_segment]
        exact ((convex_ball a epsilon).segment_subset
          (Metric.mem_ball_self hepsilon) hb).trans hball
      exact ⟨gamma, gamma.continuous.isClosedEmbedding gammaInjective |>.isEmbedding,
        gammaRange⟩
  have transitiveAccess : ∀ a b d, a ∈ U → b ∈ U → d ∈ U →
      R a b → R b d → R a d := by
    intro a b d _ _ _ hab hbd
    rcases hab with rfl | ⟨alpha, halpha, halphaRange⟩
    · exact hbd
    rcases hbd with rfl | ⟨beta, hbeta, hbetaRange⟩
    · exact Or.inr ⟨alpha, halpha, halphaRange⟩
    by_cases had : a = d
    · exact Or.inl had
    · right
      obtain ⟨gamma, hgamma, hgammaRange⟩ :=
        existsEmbeddedPathInUnion alpha beta halpha hbeta had
      exact ⟨gamma, hgamma,
        hgammaRange.trans (Set.union_subset halphaRange hbetaRange)⟩
  have symmetricAccess : ∀ a b, a ∈ U → b ∈ U → R a b → R b a := by
    intro a b _ _ hab
    rcases hab with rfl | ⟨gamma, hgamma, hgammaRange⟩
    · exact Or.inl rfl
    · right
      have reverseInjective : Function.Injective gamma.symm := by
        intro s t hst
        apply unitInterval.symm_bijective.injective
        exact hgamma.injective hst
      exact ⟨gamma.symm,
        gamma.symm.continuous.isClosedEmbedding reverseInjective |>.isEmbedding,
        Path.symm_range gamma ▸ hgammaRange⟩
  have haccess : R x y := by
    exact hUconnected.isPreconnected.induction₂ R localAccess transitiveAccess
      symmetricAccess hx hy
  rcases haccess with hxy' | hpath
  · exact False.elim (hxy hxy')
  · exact hpath

/-- Helper for Remark 65.1: distinct points in the complement of a spherical
arc are joined there by an embedded path. -/
private lemma existsEmbeddedPathInComplSphereArc
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    {x y : StandardSphere 2} (hx : x ∈ Aᶜ) (hy : y ∈ Aᶜ) (hxy : x ≠ y) :
    ∃ gamma : Path x y, Topology.IsEmbedding gamma ∧ Set.range gamma ⊆ Aᶜ := by
  classical
  -- Choose a chart pole on the arc and record compactness of the arc first.
  obtain ⟨arcEquiv⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := arcEquiv.symm.compactSpace
  have hAclosed : IsClosed A :=
    (isCompact_iff_compactSpace.mpr inferInstance : IsCompact A).isClosed
  let p : A := arcEquiv.symm 0
  have hcomplSubsetPuncture : Aᶜ ⊆ ({(p : StandardSphere 2)}ᶜ :
      Set (StandardSphere 2)) := by
    intro w hwA hwp
    exact hwA (hwp ▸ p.property)
  let chart := StandardSphere.puncturedHomeomorphPlane (p : StandardSphere 2)
  let chartDomain : Set ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2)) :=
    Subtype.val ⁻¹' Aᶜ
  have chartDomainImage : ((fun w ↦ w.1) '' chartDomain) = Aᶜ := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hcomplSubsetPuncture]
  have chartDomainOpen : IsOpen chartDomain :=
    hAclosed.isOpen_compl.preimage continuous_subtype_val
  let x' : ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2)) :=
    ⟨x, hcomplSubsetPuncture hx⟩
  let y' : ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2)) :=
    ⟨y, hcomplSubsetPuncture hy⟩
  have chartDomainNonempty : chartDomain.Nonempty := ⟨x', hx⟩
  -- Arc nonseparation makes the chart domain connected; the chart preserves it.
  have hcomplPreconnected : IsPreconnected Aᶜ := by
    apply isPreconnected_iff_preconnectedSpace.mpr
    by_contra hpreconnected
    exact arc_not_separates A (Set.separates_iff.mpr hpreconnected)
  have chartDomainPreconnected : IsPreconnected chartDomain := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [chartDomainImage]
    exact hcomplPreconnected
  have chartDomainConnected : IsConnected chartDomain :=
    ⟨chartDomainNonempty, chartDomainPreconnected⟩
  have chartImageOpen : IsOpen (chart '' chartDomain) :=
    chart.isOpenMap chartDomain chartDomainOpen
  have chartImageConnected : IsConnected (chart '' chartDomain) :=
    chart.isConnected_image.mpr chartDomainConnected
  have hxImage : chart x' ∈ chart '' chartDomain := ⟨x', hx, rfl⟩
  have hyImage : chart y' ∈ chart '' chartDomain := ⟨y', hy, rfl⟩
  have hxy' : x' ≠ y' := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hchartxy : chart x' ≠ chart y' := chart.injective.ne hxy'
  obtain ⟨delta, hdelta, hdeltaRange⟩ :=
    existsEmbeddedPathInOpenConnected (chart '' chartDomain)
      chartImageOpen chartImageConnected hxImage hyImage hchartxy
  -- Map the embedded planar path back through the chart and the subtype inclusion.
  let rawLifted : Path (chart.symm (chart x')) (chart.symm (chart y')) :=
    delta.map chart.symm.continuous
  let lifted : Path x' y' := rawLifted.cast
    (chart.symm_apply_apply x').symm (chart.symm_apply_apply y').symm
  let gamma : Path x y := lifted.map continuous_subtype_val
  have rawLiftedCoe : (rawLifted : unitInterval →
      ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2))) =
      chart.symm ∘ delta := Path.map_coe delta chart.symm.continuous
  have liftedCoe : (lifted : unitInterval →
      ({(p : StandardSphere 2)}ᶜ : Set (StandardSphere 2))) = rawLifted :=
    Path.cast_coe rawLifted (chart.symm_apply_apply x').symm
      (chart.symm_apply_apply y').symm
  have gammaCoe : (gamma : unitInterval → StandardSphere 2) =
      Subtype.val ∘ lifted := Path.map_coe lifted continuous_subtype_val
  have gammaEmbedding : Topology.IsEmbedding gamma := by
    rw [gammaCoe, liftedCoe, rawLiftedCoe]
    exact Topology.IsEmbedding.subtypeVal.comp (chart.symm.isEmbedding.comp hdelta)
  refine ⟨gamma, gammaEmbedding, ?_⟩
  rw [Set.range_subset_iff]
  intro t
  rw [gammaCoe, liftedCoe, rawLiftedCoe]
  have htImage : delta t ∈ chart '' chartDomain :=
    hdeltaRange (Set.mem_range_self t)
  obtain ⟨w, hwDomain, hwt⟩ := htImage
  have hback : chart.symm (delta t) = w := by
    have := congrArg chart.symm hwt
    simpa using this.symm
  change (chart.symm (delta t) : StandardSphere 2) ∈ Aᶜ
  rw [hback]
  exact hwDomain

/-- Helper for Remark 65.1: complex coordinates identify punctured-plane
membership with nonvanishing. -/
private lemma euclideanPlane_mem_punctured_iff_complex_ne_zero
    (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ EuclideanPlane.punctured ↔
      Complex.orthonormalBasisOneI.repr.symm z ≠ 0 := by
  -- The coordinate isometry is injective and preserves the zero vector.
  rw [EuclideanPlane.mem_punctured_iff]
  constructor
  · intro hz hcomplex
    apply hz
    apply Complex.orthonormalBasisOneI.repr.symm.injective
    simpa using hcomplex
  · intro hcomplex hz
    subst z
    exact hcomplex (map_zero Complex.orthonormalBasisOneI.repr.symm)

/-- Helper for Remark 65.1: complex coordinates give a homeomorphism from the
punctured Euclidean plane to the punctured complex plane. -/
private noncomputable def puncturedPlaneHomeomorphPuncturedComplex :
    EuclideanPlane.punctured ≃ₜ {z : ℂ // z ≠ 0} :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlane_mem_punctured_iff_complex_ne_zero

/-- Helper for Remark 65.1: polar and logarithmic coordinates identify the
punctured complex plane with the infinite cylinder. -/
private noncomputable def puncturedComplexHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- Helper for Remark 65.1: every based fundamental group of the punctured
Euclidean plane has infinite-cyclic coordinates. -/
private lemma puncturedPlane_fundamentalGroupEquivInt
    (z : EuclideanPlane.punctured) :
    Nonempty (FundamentalGroup EuclideanPlane.punctured z ≃* Multiplicative ℤ) := by
  -- Transport the standard cylinder computation through the two coordinate charts.
  let e := puncturedPlaneHomeomorphPuncturedComplex.trans
    puncturedComplexHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroup_infiniteCylinder (e z)).some⟩

/-- Helper for Remark 65.1: two disjoint closed obstacles give crossing-cover
data when their common complement has exactly two components and the path
endpoints lie in opposite components. -/
private lemma crossingCover_of_disjoint_closed_obstacles
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace Y]
    (f : C(X, Y)) {a b : X}
    (alpha : Path a b) (beta : Path b a)
    (D₁ D₂ : Set Y)
    (hD₁closed : IsClosed D₁) (hD₂closed : IsClosed D₂)
    (hdisjoint : Disjoint D₁ D₂)
    (ha : f a ∈ (D₁ ∪ D₂)ᶜ) (hb : f b ∈ (D₁ ∪ D₂)ᶜ)
    (hdifferent : connectedComponentIn (D₁ ∪ D₂)ᶜ (f a) ≠
      connectedComponentIn (D₁ ∪ D₂)ᶜ (f b))
    (hcomponents :
      Cardinal.mk (ConnectedComponents (((D₁ ∪ D₂)ᶜ : Set Y))) = 2)
    (halpha : ∀ t, f (alpha t) ∈ D₁ᶜ)
    (hbeta : ∀ t, f (beta t) ∈ D₂ᶜ) :
    Nonempty (FundamentalGroup.CrossingCoverData f alpha beta) := by
  -- Disjointness makes the two obstacle complements cover the sphere.
  have hcover : D₁ᶜ ∪ D₂ᶜ = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hyD₁ : y ∈ D₁
    · exact Or.inr (fun hyD₂ ↦ Set.disjoint_left.mp hdisjoint hyD₁ hyD₂)
    · exact Or.inl hyD₁
  have hoverlapComponents :
      Cardinal.mk (ConnectedComponents ((D₁ᶜ ∩ D₂ᶜ) :
        Set Y)) = 2 := by
    -- De Morgan's law identifies the overlap with the supplied complement.
    have hoverlap : D₁ᶜ ∩ D₂ᶜ = (D₁ ∪ D₂)ᶜ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, not_or]
    rw [hoverlap]
    exact hcomponents
  -- The generic two-component constructor now supplies every cover field.
  apply FundamentalGroup.CrossingCoverData.ofTwoOverlapComponents
    f alpha beta D₁ᶜ D₂ᶜ hD₁closed.isOpen_compl hD₂closed.isOpen_compl hcover
  · simpa only [compl_union] using ha
  · simpa only [compl_union] using hb
  · simpa only [compl_union] using hdifferent
  · exact hoverlapComponents
  · exact halpha
  · exact hbeta

/-- Helper for Remark 65.1: induced maps on fundamental groups preserve
composition of continuous maps. -/
private lemma fundamentalGroupMap_comp_eq
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- Evaluate the two homomorphisms on a loop and use functoriality of path mapping.
  ext loop
  simp only [FundamentalGroup.map_apply]
  exact Path.Homotopic.Quotient.map_comp

/-- Helper for Remark 65.1: a composite of maps inducing bijections on
fundamental groups also induces a bijection. -/
private lemma fundamentalGroupMap_comp_bijective
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (hf : Function.Bijective (FundamentalGroup.map f x))
    (hg : Function.Bijective (FundamentalGroup.map g (f x))) :
    Function.Bijective (FundamentalGroup.map (g.comp f) x) := by
  -- Rewrite the induced map to the composite and combine the two bijections.
  rw [fundamentalGroupMap_comp_eq]
  exact hg.comp hf

/-- Helper for Remark 65.1: a metric ball lies in the complement of the sphere
with the same center and radius. -/
private lemma ball_subset_compl_sphere
    {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    Metric.ball x r ⊆ (Metric.sphere x r)ᶜ := by
  -- A point cannot have distance both strictly below and equal to the radius.
  intro y hyBall hySphere
  exact Metric.sphere_disjoint_ball.le_bot ⟨hySphere, hyBall⟩

/-- Helper for Remark 65.1: recentering an ambient plane homeomorphism avoids
the origin exactly when its input avoids the origin. -/
private lemma recenteredPuncturedHomeomorph_mem_iff
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ EuclideanPlane.punctured ↔
      h.trans (Homeomorph.subRight (h 0)) x ∈ EuclideanPlane.punctured := by
  -- Translation by `h 0` converts nonvanishing to injectivity of `h` at zero.
  rw [EuclideanPlane.mem_punctured_iff, EuclideanPlane.mem_punctured_iff]
  simp only [Homeomorph.trans_apply, Homeomorph.subRight_apply, sub_ne_zero]
  rw [h.injective.ne_iff]

/-- Helper for Remark 65.1: an ambient plane homeomorphism, recentered at the
image of the origin, restricts to a self-homeomorphism of the punctured plane. -/
private def recenteredPuncturedHomeomorph
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    EuclideanPlane.punctured ≃ₜ EuclideanPlane.punctured :=
  (h.trans (Homeomorph.subRight (h 0))).subtype
    (recenteredPuncturedHomeomorph_mem_iff h)

/-- Helper for Remark 65.1: the recentered punctured-plane homeomorphism has
the expected ambient value. -/
private lemma recenteredPuncturedHomeomorph_apply
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (x : EuclideanPlane.punctured) :
    ((recenteredPuncturedHomeomorph h x : EuclideanPlane.punctured) :
      EuclideanSpace ℝ (Fin 2)) = h x - h 0 := by
  -- Unfold only this coercion bridge; later proofs rewrite through this formula.
  simp [recenteredPuncturedHomeomorph]

/-- Helper for Remark 65.1: translating the unit-sphere inclusion by any
puncture in the open unit ball induces a bijection on fundamental groups. -/
private lemma translatedUnitSphereInclusionMap_bijective_of_mem_ball
    (p : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ :
      Set (EuclideanSpace ℝ (Fin 2))))
    (hp : (p : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1)
    (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    Function.Bijective
      (FundamentalGroup.map
        (translatedPunctureInclusion (Metric.sphere 0 1) p) c) := by
  let unitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hzeroComplement : (0 : EuclideanSpace ℝ (Fin 2)) ∈ unitSphereᶜ :=
    ball_subset_compl_sphere 0 1 (Metric.mem_ball_self one_pos)
  let originPuncture : (unitSphereᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    ⟨0, hzeroComplement⟩
  -- The open unit ball puts the origin and `p` in one complementary component.
  have hpComponent : (p : EuclideanSpace ℝ (Fin 2)) ∈
      connectedComponentIn unitSphereᶜ (originPuncture : EuclideanSpace ℝ (Fin 2)) := by
    exact (Metric.isConnected_ball one_pos).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self one_pos) (ball_subset_compl_sphere 0 1) hp
  have hcomponents : connectedComponentIn unitSphereᶜ originPuncture =
      connectedComponentIn unitSphereᶜ p :=
    connectedComponentIn_eq hpComponent
  have hjoined : JoinedIn unitSphereᶜ
      (originPuncture : EuclideanSpace ℝ (Fin 2)) p :=
    joinedIn_compl_of_connectedComponentIn_eq unitSphere Metric.isClosed_sphere
      originPuncture p hcomponents
  -- At the origin, the translated inclusion is the standard radial inclusion,
  -- after the identity homeomorphism between the two punctured-plane spellings.
  let puncturedEquiv : EuclideanPlane.punctured ≃ₜ PuncturedEuclideanSpace 1 :=
    (Homeomorph.refl (EuclideanSpace ℝ (Fin 2))).subtype
      EuclideanPlane.mem_punctured_iff
  have puncturedEquiv_symm_apply (y : PuncturedEuclideanSpace 1) :
      ((puncturedEquiv.symm y : EuclideanPlane.punctured) :
        EuclideanSpace ℝ (Fin 2)) = y := by
    -- The identity subtype homeomorphism preserves the ambient point.
    rfl
  have leftRoute_apply (x : StandardSphere 1) :
      (((puncturedEquiv.symm.toHomotopyEquiv.toFun.comp
          (StandardSphere.toPunctured 1)) x : EuclideanPlane.punctured) :
        EuclideanSpace ℝ (Fin 2)) = x := by
    -- Normalize the composite spelling before proving the commuting square.
    exact puncturedEquiv_symm_apply (StandardSphere.toPunctured 1 x)
  have hfactor : puncturedEquiv.symm.toHomotopyEquiv.toFun.comp
      (StandardSphere.toPunctured 1) =
        translatedPunctureInclusion unitSphere originPuncture := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rw [leftRoute_apply, translatedPunctureInclusion_apply]
    simp only [originPuncture, sub_zero]
  have horiginBijective : Function.Bijective
      (FundamentalGroup.map
        (translatedPunctureInclusion unitSphere originPuncture) c) := by
    rw [← hfactor]
    exact fundamentalGroupMap_comp_bijective (StandardSphere.toPunctured 1)
      puncturedEquiv.symm.toHomotopyEquiv.toFun c
      (fundamentalGroupMap_bijective_of_leftToRight
        (StandardSphere.toPunctured 1) c
        (StandardSphere.fundamentalGroupMap_bijective 1 c))
      (puncturedEquiv.symm.toHomotopyEquiv.fundamentalGroupMap_bijective
        (StandardSphere.toPunctured 1 c))
  have hmoving := translatedPunctureInclusion_homotopic_of_joinedIn
    unitSphere originPuncture p hjoined
  -- Homotopy invariance moves both injectivity and surjectivity to `p`.
  exact ⟨
    fundamentalGroupMap_injective_of_homotopic_canonical
      (translatedPunctureInclusion unitSphere originPuncture)
      (translatedPunctureInclusion unitSphere p) c hmoving horiginBijective.1,
    fundamentalGroupMap_surjective_of_homotopic_canonical
      (translatedPunctureInclusion unitSphere originPuncture)
      (translatedPunctureInclusion unitSphere p) c hmoving horiginBijective.2⟩

/-- Helper for Remark 65.1: the planar Jordan-curve inclusion is surjective when
the origin lies in its bounded complementary component. -/
private lemma jordanCurveInclusionMap_surjective_of_originComponent_bounded
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (hC : C ⊆ EuclideanPlane.punctured) (c : C)
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ 0)) :
    Function.Surjective (FundamentalGroup.mapOfSubset hC c) := by
  -- Route correction: ambient Schoenflies straightening replaces the blocked
  -- embedded-K₄ construction and sends the bounded side to the open unit disk.
  have hzeroNotMem : (0 : EuclideanSpace ℝ (Fin 2)) ∉ C := by
    intro hzero
    exact (EuclideanPlane.mem_punctured_iff 0).mp (hC hzero) rfl
  let originComplement : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    ⟨0, hzeroNotMem⟩
  obtain ⟨straighten, hcurve, hcomponent⟩ :=
    Topology.IsSimpleClosedCurve.existsAmbientHomeomorph_maps_boundedComponentToUnitBall
      C originComplement h_bounded
  have hzeroComponent : (0 : EuclideanSpace ℝ (Fin 2)) ∈
      connectedComponentIn Cᶜ 0 :=
    mem_connectedComponentIn originComplement.property
  have hpunctureBall : straighten 0 ∈ Metric.ball 0 1 := by
    rw [← hcomponent]
    exact Set.mem_image_of_mem straighten hzeroComponent
  let spherePuncture :
      ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ :
        Set (EuclideanSpace ℝ (Fin 2))) :=
    ⟨straighten 0, ball_subset_compl_sphere 0 1 hpunctureBall⟩
  let curveHomeomorph : C ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (Homeomorph.image straighten C).trans (Homeomorph.setCongr hcurve)
  let puncturedHomeomorph :
      EuclideanPlane.punctured ≃ₜ EuclideanPlane.punctured :=
    recenteredPuncturedHomeomorph straighten
  let inclusion : C(C, EuclideanPlane.punctured) := ContinuousMap.inclusion hC
  have curveHomeomorph_apply (x : C) :
      (curveHomeomorph x : EuclideanSpace ℝ (Fin 2)) = straighten x := by
    -- The image restriction and set-congruence maps preserve the ambient point.
    rfl
  have inclusion_apply (x : C) :
      ((inclusion x : EuclideanPlane.punctured) : EuclideanSpace ℝ (Fin 2)) = x := by
    -- The canonical inclusion preserves the ambient curve point.
    rfl
  have spherePuncture_apply :
      (spherePuncture : EuclideanSpace ℝ (Fin 2)) = straighten 0 := by
    -- The packaged puncture has the straightened origin as its ambient value.
    rfl
  have hsquare : puncturedHomeomorph.toHomotopyEquiv.toFun.comp inclusion =
      (translatedPunctureInclusion (Metric.sphere 0 1) spherePuncture).comp
        curveHomeomorph.toHomotopyEquiv.toFun := by
    -- The two routes around the square both send `x` to `straighten x - straighten 0`.
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    calc
      ((puncturedHomeomorph (inclusion x) : EuclideanPlane.punctured) :
          EuclideanSpace ℝ (Fin 2)) =
          straighten ((inclusion x : EuclideanPlane.punctured) :
            EuclideanSpace ℝ (Fin 2)) - straighten 0 := by
        exact recenteredPuncturedHomeomorph_apply straighten (inclusion x)
      _ = straighten x - straighten 0 := by rw [inclusion_apply]
      _ = (curveHomeomorph x : EuclideanSpace ℝ (Fin 2)) - spherePuncture := by
        rw [curveHomeomorph_apply, spherePuncture_apply]
      _ = ((translatedPunctureInclusion (Metric.sphere 0 1) spherePuncture
          (curveHomeomorph x) : EuclideanPlane.punctured) :
            EuclideanSpace ℝ (Fin 2)) :=
        (translatedPunctureInclusion_apply _ spherePuncture
          (curveHomeomorph x)).symm
  have hcurveMap : Function.Bijective
      (FundamentalGroup.map curveHomeomorph.toHomotopyEquiv.toFun c) :=
    curveHomeomorph.toHomotopyEquiv.fundamentalGroupMap_bijective c
  have htranslatedMap : Function.Bijective
      (FundamentalGroup.map
        (translatedPunctureInclusion (Metric.sphere 0 1) spherePuncture)
        (curveHomeomorph c)) :=
    translatedUnitSphereInclusionMap_bijective_of_mem_ball
      spherePuncture hpunctureBall (curveHomeomorph c)
  have hrightComposite : Function.Bijective
      (FundamentalGroup.map
        ((translatedPunctureInclusion (Metric.sphere 0 1) spherePuncture).comp
          curveHomeomorph.toHomotopyEquiv.toFun) c) :=
    fundamentalGroupMap_comp_bijective curveHomeomorph.toHomotopyEquiv.toFun
      (translatedPunctureInclusion (Metric.sphere 0 1) spherePuncture) c
      hcurveMap htranslatedMap
  have hleftSurjective : Function.Surjective
      (FundamentalGroup.map
        (puncturedHomeomorph.toHomotopyEquiv.toFun.comp inclusion) c) := by
    rw [hsquare]
    exact hrightComposite.2
  rw [fundamentalGroupMap_comp_eq] at hleftSurjective
  have hpuncturedInjective : Function.Injective
      (FundamentalGroup.map puncturedHomeomorph.toHomotopyEquiv.toFun (inclusion c)) :=
    (puncturedHomeomorph.toHomotopyEquiv.fundamentalGroupMap_bijective
      (inclusion c)).1
  -- Surjectivity of the composite and injectivity of the codomain equivalence
  -- cancel the latter, leaving surjectivity of the original inclusion.
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  intro targetLoop
  obtain ⟨sourceLoop, hsourceLoop⟩ := hleftSurjective
    (FundamentalGroup.map puncturedHomeomorph.toHomotopyEquiv.toFun
      (inclusion c) targetLoop)
  refine ⟨sourceLoop, hpuncturedInjective ?_⟩
  exact hsourceLoop

/-- Helper for Remark 65.1: the inclusion of a planar Jordan curve surrounding
the origin induces a bijection on fundamental groups. -/
private lemma jordanCurveInclusionMap_bijective_of_originComponent_bounded
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (hC : C ⊆ EuclideanPlane.punctured) (c : C)
    (sourceCoordinates : FundamentalGroup C c ≃* Multiplicative ℤ)
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured
      ((ContinuousMap.inclusion hC) c) ≃* Multiplicative ℤ)
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ 0)) :
    Function.Bijective (FundamentalGroup.mapOfSubset hC c) := by
  constructor
  · -- Exercise 62.4 gives nontriviality, which is injectivity in integer coordinates.
    apply monoidHom_injective_of_equivInt_of_ne_one
      (FundamentalGroup.mapOfSubset hC c) sourceCoordinates targetCoordinates
    exact fundamentalGroupMap_ne_one_of_originComponent_bounded
      C hC c h_bounded
  · -- The geometric helper transports crossing-cover surjectivity to this basepoint.
    exact jordanCurveInclusionMap_surjective_of_originComponent_bounded
      C hC c h_bounded

/-- Helper for Remark 65.1: an injective circle map surrounding the origin
induces a bijection on fundamental groups. -/
private lemma fundamentalGroupMap_bijective_of_injective_originComponent_bounded
    (h : C(Circle, EuclideanPlane.punctured)) (h_injective : Function.Injective h)
    (sourceCoordinates : Circle.FundamentalOrientation)
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ)
    (h_bounded : Bornology.IsBounded
      (connectedComponentIn (Set.range (fun x : Circle ↦
        (h x : EuclideanSpace ℝ (Fin 2))))ᶜ 0)) :
    Function.Bijective (FundamentalGroup.map h 1) := by
  -- View the parametrization in the ambient plane and identify its range with `Circle`.
  let ambient : C(Circle, EuclideanSpace ℝ (Fin 2)) :=
    ⟨fun x ↦ (h x : EuclideanSpace ℝ (Fin 2)),
      continuous_subtype_val.comp h.continuous⟩
  have ambient_injective : Function.Injective ambient := by
    intro x y hxy
    apply h_injective
    exact Subtype.ext hxy
  letI : Topology.IsSimpleClosedCurve (Set.range ambient) :=
    isSimpleClosedCurve_range_of_injective ambient ambient_injective
  have range_subset_punctured : Set.range ambient ⊆ EuclideanPlane.punctured := by
    rintro z ⟨x, rfl⟩
    exact (h x).property
  have hEmbedding : Topology.IsEmbedding ambient :=
    (ambient.continuous.isClosedEmbedding ambient_injective).isEmbedding
  let rangeParam : C(Circle, Set.range ambient) := hEmbedding.toHomeomorph
  let inclusion : C(Set.range ambient, EuclideanPlane.punctured) :=
    ContinuousMap.inclusion range_subset_punctured
  have rangeParam_bijective :
      Function.Bijective (FundamentalGroup.map rangeParam 1) := by
    -- A homeomorphism is a homotopy equivalence, so it induces an isomorphism on `π₁`.
    exact ContinuousMap.HomotopyEquiv.fundamentalGroupMap_bijective
      hEmbedding.toHomeomorph.toHomotopyEquiv 1
  let rangeCoordinates :
      FundamentalGroup (Set.range ambient) (rangeParam 1) ≃* Multiplicative ℤ :=
    (MulEquiv.ofBijective (FundamentalGroup.map rangeParam 1)
      rangeParam_bijective).symm.trans sourceCoordinates
  have factorization : inclusion.comp rangeParam = h := by
    -- Inclusion after the range parametrization recovers the original punctured-plane map.
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact Topology.IsEmbedding.toHomeomorph_apply_coe hEmbedding x
  have basepoint_eq : inclusion (rangeParam 1) = h 1 :=
    DFunLike.congr_fun factorization 1
  have inclusionCoordinates :
      FundamentalGroup EuclideanPlane.punctured (inclusion (rangeParam 1)) ≃*
        Multiplicative ℤ := by
    -- Rewrite only the basepoint, retaining the supplied target coordinates.
    rw [basepoint_eq]
    exact targetCoordinates
  have inclusion_bijective :
      Function.Bijective (FundamentalGroup.map inclusion (rangeParam 1)) := by
    -- The deep input applies to the canonical inclusion of the image curve.
    change Function.Bijective
      (FundamentalGroup.map (ContinuousMap.inclusion range_subset_punctured) (rangeParam 1))
    rw [← FundamentalGroup.mapOfSubset_eq_map_inclusion]
    exact jordanCurveInclusionMap_bijective_of_originComponent_bounded
      (Set.range ambient) range_subset_punctured (rangeParam 1)
        rangeCoordinates inclusionCoordinates h_bounded
  have composite_bijective := fundamentalGroupMap_comp_bijective rangeParam inclusion 1
    rangeParam_bijective inclusion_bijective
  rwa [factorization] at composite_bijective

/-- Helper for Remark 65.1: a bijective induced map between infinite cyclic
fundamental groups has winding number `1` or `-1`. -/
private lemma windingNumber_eq_one_or_neg_one_of_fundamentalGroupMap_bijective
    (h : C(Circle, EuclideanPlane.punctured))
    (sourceCoordinates : Circle.FundamentalOrientation)
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ)
    (h_bijective : Function.Bijective (FundamentalGroup.map h 1)) :
    windingNumber sourceCoordinates h targetCoordinates = 1 ∨
      windingNumber sourceCoordinates h targetCoordinates = -1 := by
  classical
  let inducedEquiv := MulEquiv.ofBijective (FundamentalGroup.map h 1) h_bijective
  let coordinateChange : ℤ ≃+ ℤ :=
    (sourceCoordinates.symm.trans (inducedEquiv.trans targetCoordinates)).toAdditive
  have target_value :
      targetCoordinates
          (FundamentalGroup.map h 1
            (sourceCoordinates.symm (Multiplicative.ofAdd 1))) =
        Multiplicative.ofAdd (windingNumber sourceCoordinates h targetCoordinates) := by
    -- Evaluate the defining winding-number specification in target coordinates.
    rw [windingNumber_spec, targetCoordinates.apply_symm_apply]
  have winding_coordinate :
      windingNumber sourceCoordinates h targetCoordinates = coordinateChange 1 := by
    -- Return the multiplicative coordinate identity to ordinary integers.
    have additive_value := congrArg Multiplicative.toAdd target_value
    have additive_value' :
        Multiplicative.toAdd
            (targetCoordinates
              (FundamentalGroup.map h 1
                (sourceCoordinates.symm (Multiplicative.ofAdd 1)))) =
          windingNumber sourceCoordinates h targetCoordinates := by
      exact additive_value
    have coordinateChange_apply :
        coordinateChange 1 =
          Multiplicative.toAdd
            (targetCoordinates
              (FundamentalGroup.map h 1
                (sourceCoordinates.symm (Multiplicative.ofAdd 1)))) := by
      rfl
    exact additive_value'.symm.trans coordinateChange_apply.symm
  -- Every additive automorphism of `ℤ` is either the identity or negation.
  rcases Int.addEquiv_eq_refl_or_neg coordinateChange with coordinate_eq | coordinate_eq
  · left
    have coordinate_at_one : coordinateChange 1 = 1 := by
      exact DFunLike.congr_fun coordinate_eq 1
    exact winding_coordinate.trans coordinate_at_one
  · right
    have coordinate_at_one : coordinateChange 1 = -1 := by
      exact DFunLike.congr_fun coordinate_eq 1
    exact winding_coordinate.trans coordinate_at_one

/-- Remark 65.1 (2). If the origin component of the complement of the simple closed image of an
injective circle map is bounded, then its winding number is `1` or `-1`. -/
theorem windingNumber_eq_one_or_neg_one_of_originComponent_bounded
    (h : C(Circle, EuclideanPlane.punctured)) (h_injective : Function.Injective h)
    (sourceCoordinates : Circle.FundamentalOrientation)
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ)
    (h_bounded : Bornology.IsBounded
      (connectedComponentIn (Set.range (fun x : Circle ↦ (h x : EuclideanSpace ℝ (Fin 2))))ᶜ 0)) :
    windingNumber sourceCoordinates h targetCoordinates = 1 ∨
      windingNumber sourceCoordinates h targetCoordinates = -1 := by
  -- The geometric input makes the induced map bijective; cyclic-group algebra finishes.
  apply windingNumber_eq_one_or_neg_one_of_fundamentalGroupMap_bijective
  exact fundamentalGroupMap_bijective_of_injective_originComponent_bounded
    h h_injective sourceCoordinates targetCoordinates h_bounded

end PuncturedPlaneMap
