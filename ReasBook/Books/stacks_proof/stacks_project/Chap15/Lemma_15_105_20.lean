import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_50_11
import stacks_proof.stacks_project.Chap10.Lemma_10_107_1
import stacks_proof.stacks_project.Chap15.Definition_15_105_3
import stacks_proof.stacks_project.Chap15.Lemma_15_105_20.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CommRingCat

universe u

section

variable {A : Type u} {K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [IsIntegrallyClosed A]

/-- Helper for Lemma 15.105.20: the chosen valuation subrings cut out exactly the embedded image
of `A` inside `K`. -/
private lemma mem_range_iff_mem_selected_valuationSubrings
    (W : {x : K // x ∉ (algebraMap A K).range} → ValuationSubring K)
    (hcontains : ∀ x, (algebraMap A K).range ≤ (W x).toSubring)
    (hexclude : ∀ x, (x : K) ∉ W x)
    (y : K) :
    y ∈ (algebraMap A K).range ↔ ∀ x, y ∈ W x := by
  constructor
  · intro hy x
    -- Any chosen valuation subring contains the embedded copy of `A` by construction.
    exact hcontains x hy
  · intro hy
    -- Route correction: the backward direction uses the source's contradiction on the index
    -- `x = ⟨y, hy_range⟩`, instead of drifting to a separate intersection theorem.
    by_contra hy_range
    exact (hexclude ⟨y, hy_range⟩) (hy ⟨y, hy_range⟩)

/-- Helper for Lemma 15.105.20: an element of the embedded copy of `A` in `K` lies in every
chosen valuation subring. -/
private lemma range_subtype_mem_selected_valuationSubring
    {I : Type u} (W : I → ValuationSubring K)
    (hcontains : ∀ x, (algebraMap A K).range ≤ (W x).toSubring)
    (x : I) (y : (algebraMap A K).range) :
    ((algebraMap A K).range.subtype y : K) ∈ W x := by
  -- The range element already comes with the membership proof needed by the containment hypothesis.
  exact hcontains x y.2

/-- Helper for Lemma 15.105.20: the embedded image of `A` maps to the product of the selected
valuation subrings by taking the same element in every coordinate. -/
private def selected_valuation_range_fst_hom
    {I : Type u} (W : I → ValuationSubring K)
    (hcontains : ∀ x, (algebraMap A K).range ≤ (W x).toSubring) :
    (algebraMap A K).range →+* ((x : I) → W x) :=
  Pi.ringHom fun x ↦
    RingHom.codRestrict ((algebraMap A K).range.subtype) (W x)
      (range_subtype_mem_selected_valuationSubring (A := A) (K := K) W hcontains x)

/-
Domain-style sampling:
- primary domain: commutative algebra of normal domains, valuation-theoretic presentations of
  fraction fields, and cartesian squares in `CommRingCat`;
- sampled owner declarations:
  `CategoryTheory.IsPullback`,
  `HasWeakDimensionLE`,
  `RingHom.Flat`,
  `CategoryTheory.Epi`;
- best owner abstraction: the source-facing object here is the cartesian square over the canonical
  map `A → K`, and the correct square owner is `IsPullback` itself rather than a new local
  package. The Stacks lemma is a single existence statement, so the lower-left weak-dimension
  condition and the flat/injective/epimorphism properties of the bottom map belong on the same
  witness instead of being split into parallel existential theorems.

Primitive-vs-derived split:
- primitive data: rings `V` and `L`, morphisms `i`, `j`, `k`, and the pullback witness
  `IsPullback i (ofHom (algebraMap A K)) k j` together with the properties
  `HasWeakDimensionLE V 1`, `k.hom.Flat`, `Function.Injective k.hom`, and `Epi k`;
- derived API: forgetful consequences such as the existence of the cartesian square alone are
  derived from the single source-facing witness and do not need separate public owners here.

Source/core/bridge triage:
- `source-facing`: the Stacks existence assertion for one cartesian square over `A → K` carrying
  all listed properties at once;
- `core/canonical`: `IsPullback`, `HasWeakDimensionLE`, `Function.Injective`, and `Epi`;
- `bridge/view`: no additional bridge object is needed here, because the categorical pullback
  square is already the owner abstraction used downstream.
-/

-- Proof sketch: for each `x : K` outside the image of `A`, choose a valuation subring `Vₓ ⊆ K`
-- containing `A` but not `x` by Lemma `10.50.11`. Take `V` to be the product of these valuation
-- rings and `L` the product of the ambient field `K`; the induced square with `A → K` is
-- cartesian by the intersection description of a normal domain inside its fraction field. Lemma
-- `15.105.19` gives weak dimension at most `1` for this product and identifies `V → L` as a
-- localization. Localizations are flat and epimorphisms, and here the map is also injective
-- because each component `Vₓ → K` is injective.
/-- Lemma 15.105.20: if `A` is a normal domain with fraction field `K`, then there exists a
cartesian square
\[
\require{AMScd}
\begin{CD}
A @>>> K \\
@VVV @VVV \\
V @>>> L
\end{CD}
\]
of commutative rings where `V` has weak dimension at most `1` and the bottom map `V → L` is flat,
injective, and an epimorphism. -/
@[stacks 092U]
theorem exists_cartesian_square_over_fractionField_with_weakDimensionLEOne_and_flat_injective_epi :
    ∃ (V L : CommRingCat.{u}) (i : of A ⟶ V) (k : V ⟶ L) (j : of K ⟶ L),
      IsPullback i (ofHom (algebraMap A K)) k j ∧
        HasWeakDimensionLE V 1 ∧
        k.hom.Flat ∧ Function.Injective k.hom ∧ Epi k := by
  classical
  let I : Type u := {x : K // x ∉ (algebraMap A K).range}
  choose W hcontains hexclude using
    (fun x : I ↦ exists_valuationSubring_not_mem_of_not_mem_range (A := A) (K := K) x.2)
  have hmem :
      ∀ y : K, y ∈ (algebraMap A K).range ↔ ∀ x : I, y ∈ W x :=
    mem_range_iff_mem_selected_valuationSubrings
      (A := A) (K := K) W hcontains hexclude
  let VRing : Type u := (x : I) → W x
  let LRing : Type u := I → K
  let V : CommRingCat := CommRingCat.of VRing
  let L : CommRingCat := CommRingCat.of LRing
  let k : V ⟶ L := CommRingCat.ofHom (algebraMap VRing LRing)
  let j : of K ⟶ L := CommRingCat.ofHom (algebraMap K LRing)
  let R : CommRingCat := CommRingCat.of ((algebraMap A K).range)
  let fstRange : R ⟶ V :=
    CommRingCat.ofHom (selected_valuation_range_fst_hom (A := A) (K := K) W hcontains)
  let sndRange : R ⟶ of K :=
    CommRingCat.ofHom ((algebraMap A K).range.subtype)
  have hRangeComm : fstRange ≫ k = sndRange ≫ j := by
    -- Both composites send a range element to the constant tuple given by its underlying value in `K`.
    apply CommRingCat.hom_ext
    ext y x
    rfl
  have hPullbackSndMemRange :
      ∀ z : ↥(pullback k j), ((pullback.snd k j).hom z : K) ∈ (algebraMap A K).range := by
    intro z
    have hzmem : ∀ x : I, (pullback.snd k j).hom z ∈ W x := by
      intro x
      -- Read the pullback condition on the `x`-th coordinate to recover membership in `W x`.
      have hz :=
        congrArg (fun f : pullback k j ⟶ L ↦ (f.hom z) x) (pullback.condition (f := k) (g := j))
      have hx :
          (((pullback.fst k j).hom z) x : K) = (pullback.snd k j).hom z := by
        simpa [k, j, CommRingCat.comp_apply] using hz
      exact hx.symm ▸ (((pullback.fst k j).hom z) x).2
    -- The source proof's invariant says that belonging to every selected valuation subring is
    -- exactly the same as coming from `A`.
    exact (hmem ((pullback.snd k j).hom z)).2 hzmem
  let pullbackToRange : pullback k j ⟶ R :=
    CommRingCat.ofHom <|
      RingHom.codRestrict (pullback.snd k j).hom ((algebraMap A K).range) hPullbackSndMemRange
  have hSelectedHomInvId :
      (pullback.lift fstRange sndRange hRangeComm) ≫ pullbackToRange = 𝟙 R := by
    -- On the range object, the pullback lift followed by the restricted second projection keeps
    -- the underlying fraction-field element unchanged.
    apply CommRingCat.hom_ext
    ext y
    have hy :
        ((pullback.snd k j).hom ((pullback.lift fstRange sndRange hRangeComm).hom y) : K) =
          (sndRange.hom y : K) := by
      exact congrArg (fun f : R ⟶ of K ↦ f.hom y) (pullback.lift_snd fstRange sndRange hRangeComm)
    change (pullback.snd k j).hom ((pullback.lift fstRange sndRange hRangeComm).hom y) = (y : K)
    simpa [sndRange, CommRingCat.comp_apply] using hy
  have hSelectedInvHomId :
      pullbackToRange ≫ (pullback.lift fstRange sndRange hRangeComm) = 𝟙 (pullback k j) := by
    -- Compare the two maps into the pullback through its two projections.
    apply pullback.hom_ext
    · apply CommRingCat.hom_ext
      ext z x
      change (((((pullbackToRange ≫ pullback.lift fstRange sndRange hRangeComm) ≫ pullback.fst k j).hom z) x :
          W x) : K) =
        (((((𝟙 (pullback k j) ≫ pullback.fst k j).hom z) x : W x)) : K)
      -- The first coordinate is recovered from the pullback condition in the `x`-th factor.
      have hz :
          (((pullback.fst k j).hom z) x : K) = (pullback.snd k j).hom z := by
        have hz' :=
          congrArg (fun f : pullback k j ⟶ L ↦ (f.hom z) x) (pullback.condition (f := k) (g := j))
        simpa [k, j, CommRingCat.comp_apply] using hz'
      have hfst :
          (((((pullbackToRange ≫ pullback.lift fstRange sndRange hRangeComm) ≫ pullback.fst k j).hom z) x :
              W x) : K) =
            (((fstRange.hom (pullbackToRange.hom z)) x : W x) : K) := by
        have hfst' :=
          congrArg (fun f : R ⟶ V ↦ (f.hom (pullbackToRange.hom z)) x)
            (pullback.lift_fst fstRange sndRange hRangeComm)
        exact congrArg Subtype.val <| by
          simpa [CommRingCat.comp_apply] using hfst'
      have hmid :
          (((fstRange.hom (pullbackToRange.hom z)) x : W x) : K) =
            ((((pullback.fst k j).hom z) x : W x) : K) := by
        have hmid' :
            (fstRange.hom (pullbackToRange.hom z)) x = ((pullback.fst k j).hom z) x := by
          apply Subtype.ext
          change ((pullbackToRange.hom z : R) : K) = (((pullback.fst k j).hom z) x : K)
          simpa [pullbackToRange, CommRingCat.comp_apply]
            using hz.symm
        exact congrArg Subtype.val hmid'
      have hcoord :
          (((((pullbackToRange ≫ pullback.lift fstRange sndRange hRangeComm) ≫ pullback.fst k j).hom z) x :
              W x) : K) =
            ((((pullback.fst k j).hom z) x : W x) : K) :=
        hfst.trans hmid
      simpa [CommRingCat.comp_apply] using hcoord
    · apply CommRingCat.hom_ext
      ext z
      have hz :
          ((pullback.snd k j).hom ((pullbackToRange ≫ pullback.lift fstRange sndRange hRangeComm).hom z)
              : K) =
            (sndRange.hom (pullbackToRange.hom z) : K) := by
        exact congrArg (fun f : R ⟶ of K ↦ f.hom (pullbackToRange.hom z))
          (pullback.lift_snd fstRange sndRange hRangeComm)
      simpa [pullbackToRange, sndRange, CommRingCat.comp_apply] using hz
  let selected_valuation_pullback_iso : R ≅ pullback k j :=
    { hom := pullback.lift fstRange sndRange hRangeComm
      inv := pullbackToRange
      hom_inv_id := hSelectedHomInvId
      inv_hom_id := hSelectedInvHomId }
  have hRangePullback : IsPullback fstRange sndRange k j := by
    -- The range ring is identified with the actual pullback object by the source invariant above.
    refine (IsPullback.of_hasPullback k j).of_iso' selected_valuation_pullback_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa [selected_valuation_pullback_iso] using (pullback.lift_fst fstRange sndRange hRangeComm)
    · simpa [selected_valuation_pullback_iso] using (pullback.lift_snd fstRange sndRange hRangeComm)
    · simp
    · simp
  have hRangeRestrictInjective : Function.Injective (algebraMap A K).rangeRestrict := by
    -- Injectivity is inherited from the fraction-field map `A → K`.
    intro a b hab
    exact (IsFractionRing.injective A K) (congrArg Subtype.val hab)
  have hRangeRestrictSurjective : Function.Surjective (algebraMap A K).rangeRestrict := by
    -- Every point of the image range is represented by some element of `A`.
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have hRangeRestrictBijective : Function.Bijective (algebraMap A K).rangeRestrict := by
    exact ⟨hRangeRestrictInjective, hRangeRestrictSurjective⟩
  let fractionField_range_iso : of A ≅ R :=
    (RingEquiv.ofBijective (algebraMap A K).rangeRestrict hRangeRestrictBijective).toCommRingCatIso
  let i : of A ⟶ V := fractionField_range_iso.hom ≫ fstRange
  have hTop :
      fractionField_range_iso.hom ≫ sndRange = ofHom (algebraMap A K) := by
    -- The range equivalence was built from `rangeRestrict`, so the top edge is the original
    -- fraction-field map.
    apply CommRingCat.hom_ext
    ext a
    rfl
  have hsq : IsPullback i (ofHom (algebraMap A K)) k j := by
    -- Transport the range-level pullback square back across `A ≅ range(algebraMap A K)`.
    refine hRangePullback.of_iso' fractionField_range_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simpa [i]
    · simpa using hTop
    · simp
    · simp
  have hwdV : HasWeakDimensionLE V 1 := by
    -- This is exactly the product valuation-ring weak-dimension owner restored in the local
    -- helper module.
    simpa [V, VRing] using
      (hasWeakDimensionLEOne_pi_of_valuationRing (A := fun x : I ↦ W x))
  let M : Submonoid VRing := Submonoid.pi Set.univ fun x : I ↦ nonZeroDivisors (W x)
  letI : IsLocalization M LRing := inferInstance
  have hkflat : k.hom.Flat := by
    -- The bottom map is the canonical localization map into the product of fraction fields.
    exact RingHom.flat_algebraMap_iff.mpr <| by
      simpa [M] using (IsLocalization.flat LRing M : Module.Flat VRing LRing)
  have hkinj : Function.Injective k.hom := by
    -- Coordinatewise injectivity is immediate because each factor sits inside the field `K`.
    intro a b hab
    funext x
    apply Subtype.ext
    exact congrArg (fun f : LRing ↦ f x) hab
  have hkAlgEpi : Algebra.IsEpi VRing LRing := by
    -- The localization map is an algebra epimorphism because the two tensor-factor maps agree by
    -- localization extensionality.
    refine (algebra_isEpi_iff_includeLeft_eq_includeRight (R := VRing) (S := LRing)).2 ?_
    simpa using
      (IsLocalization.algHom_ext (W := M)
        (Algebra.ext_id
          (TensorProduct VRing LRing LRing)
          (Algebra.TensorProduct.includeLeft.comp (Algebra.algHom VRing VRing LRing))
          (Algebra.TensorProduct.includeRight.comp (Algebra.algHom VRing VRing LRing))))
  have hkepi : Epi k := by
    -- The product map `V → L` is a localization, so the algebra map is an epimorphism.
    exact
      (CommRingCat.epi_iff_epi (R := VRing) (S := LRing)).2
        hkAlgEpi
  exact ⟨V, L, i, k, j, hsq, hwdV, hkflat, hkinj, hkepi⟩

end
