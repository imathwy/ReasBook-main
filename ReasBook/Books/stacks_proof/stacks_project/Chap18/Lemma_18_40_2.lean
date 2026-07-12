import Mathlib
import StacksProject_2024.Chap07.Lemma_7_38_2
import StacksProject_2024.Chap18.Lemma_18_36_4
import StacksProject_2024.Chap18.Lemma_18_40_1
import StacksProject_2024.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

namespace CategoryTheory

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 18.40.2:
- primary domain: point stalks of sheaves of commutative rings on a site, together with enough
  points and the chapter-local unit-dichotomy owner for ringed sites;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `GrothendieckTopology.HasEnoughPoints`,
  `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`;
- best owner abstraction: the source-facing local section hypothesis is the chapter owner
  `HasLocalUnitDichotomy J 𝒪`; the chapter stalk-ring owner is `sourcePointRing`, so the theorem
  surface should use that owner directly rather than repeating the full typed fiber expression;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: the stalkwise “zero or local” conclusion, with the local section dichotomy reused
  through its chapter owner instance, and the enough-points equivalence.

Source/core/bridge triage:
- `source-facing`: the forward implication and the enough-points equivalence below;
- `core/canonical`: `GrothendieckTopology.Point.sheafFiber` and
  `GrothendieckTopology.HasEnoughPoints`;
- `bridge/view`: `HasLocalUnitDichotomy`, the chapter stalk-ring bridge `sourcePointRing`, and the
  local-ring dichotomy on stalks.

The previous single conjunction-valued theorem repeated both the local-dichotomy hypothesis and the
raw stalk expression. This file should reuse the existing chapter owners and expose the two source-
facing clauses atomically.
-/

/-- Helper for Lemma 18.40.2: restricting a representative along a point-fiber lift does not
change the resulting germ. -/
lemma stalkRestriction_eq_of_coverLift
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point)
    {X Y : C} (f : Y ⟶ X) (x : p.fiber.obj X) (y : p.fiber.obj Y)
    (hxy : p.fiber.map f y = x) (s : 𝒪.obj.obj (op X)) :
    ((p.toPresheafFiber Y y 𝒪.obj).hom) ((𝒪.obj.map f.op).hom s) =
      ((p.toPresheafFiber X x 𝒪.obj).hom) s := by
  -- The point-fiber comparison map is natural in the chosen arrow.
  simpa [hxy] using congrArg (fun k ↦ k.hom s) (p.toPresheafFiber_w f y 𝒪.obj)

/-- Helper for Lemma 18.40.2: a point meets every covering family. -/
lemma GrothendieckTopology.Point.existsArrowLiftOfCover
    (p : J.Point) {U : C} (S : J.Cover U) (x : p.fiber.obj U) :
    ∃ I : S.Arrow, ∃ y : p.fiber.obj I.Y, p.fiber.map I.f y = x := by
  -- Proof comment: this is the exact point axiom specialized to the cover `S`.
  rcases p.jointly_surjective S.1 S.2 x with ⟨Y, f, hf, y, hy⟩
  exact ⟨⟨Y, f, hf⟩, y, hy⟩

/-- Helper for Lemma 18.40.2: the algebraic binary factorization map on a commutative ring. -/
private def binaryFactorizationOnRing
    {R : Type*} [CommRing R] :
    Sum (R × R) (R × R) → R × R
  | Sum.inl (f, a) => (f, a * f)
  | Sum.inr (f, b) => (f, b * (1 - f))

/-- Helper for Lemma 18.40.2: the binary factorization map on a commutative ring is surjective as
soon as the ring is either subsingleton or local. -/
lemma binaryFactorization_surjective_of_subsingleton_or_isLocalRing
    {R : Type*} [CommRing R]
    (hR : Subsingleton R ∨ IsLocalRing R) :
    Function.Surjective (binaryFactorizationOnRing (R := R)) := by
  intro z
  rcases hR with hSub | hLocal
  · -- In the zero-ring branch every pair is equal, so any tagged preimage works.
    refine ⟨Sum.inl (z.1, z.2), ?_⟩
    apply Prod.ext
    · rfl
    · exact hSub.elim _ _
  · -- In a local ring either `f` or `1 - f` is a unit, which picks the correct summand.
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self z.1 with hz | hz
    · refine ⟨Sum.inl (z.1, z.2 * ↑(hz.unit⁻¹)), ?_⟩
      apply Prod.ext
      · rfl
      · have hInv : (↑(hz.unit⁻¹) : R) * z.1 = 1 := by
          simpa [hz.unit_spec] using hz.unit.inv_mul
        calc
          (z.2 * ↑(hz.unit⁻¹)) * z.1 = z.2 * ((↑(hz.unit⁻¹) : R) * z.1) := by
            rw [mul_assoc]
          _ = z.2 * 1 := by rw [hInv]
          _ = z.2 := by simp
    · refine ⟨Sum.inr (z.1, z.2 * ↑(hz.unit⁻¹)), ?_⟩
      apply Prod.ext
      · rfl
      · have hInv : (↑(hz.unit⁻¹) : R) * (1 - z.1) = 1 := by
          simpa [hz.unit_spec] using hz.unit.inv_mul
        calc
          (z.2 * ↑(hz.unit⁻¹)) * (1 - z.1) = z.2 * ((↑(hz.unit⁻¹) : R) * (1 - z.1)) := by
            rw [mul_assoc]
          _ = z.2 * 1 := by rw [hInv]
          _ = z.2 := by simp

/-- Helper for Lemma 18.40.2: local surjectivity of the canonical binary factorization map is one
of the equivalent formulations of `HasLocalUnitDichotomy`. -/
lemma hasLocalUnitDichotomy_of_binaryFactorizationMap_isLocallySurjective
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (h : Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)) :
    HasLocalUnitDichotomy J 𝒪 := by
  -- Route correction: reuse the owner equivalence from Lemma 18.40.1 instead of reproving the
  -- binary-factorization implication abstractly.
  rw [isLocallySurjective_binaryFactorizationMap_iff] at h
  refine ⟨fun U f ↦ ?_⟩
  -- Specializing the sectionwise factorization statement at `c = 1` recovers the dichotomy.
  obtain ⟨S, hS⟩ := h U f 1
  refine ⟨S, ?_⟩
  intro I
  rcases hS I with hI | hI
  · rcases hI with ⟨a, ha⟩
    left
    have ha' : a * (𝒪.obj.map I.f.op).hom f = 1 := by
      simpa using ha.symm
    simpa using IsUnit.of_mul_eq_one_right a ha'
  · rcases hI with ⟨b, hb⟩
    right
    have hb' : b * (1 - (𝒪.obj.map I.f.op).hom f) = 1 := by
      simpa using hb.symm
    simpa using IsUnit.of_mul_eq_one_right b hb'

/-- Helper for Lemma 18.40.2: the `Type`-valued sheaf underlying the structure sheaf `𝒪`. -/
private abbrev underlyingTypeSheaf (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪

/-- Helper for Lemma 18.40.2: the point fiber of the underlying `Type`-valued sheaf identifies
with the carrier of the stalk ring. -/
private noncomputable def pointRingCarrierIso
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point) :
    p.sheafFiber.obj (underlyingTypeSheaf (J := J) 𝒪) ≅
      (forget CommRingCat.{max u v}).obj (sourcePointRing 𝒪 p) :=
  (preservesColimitIso (forget CommRingCat.{max u v})
    (((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op).obj 𝒪.obj)).symm

/-- Helper for Lemma 18.40.2: after taking the point fiber, the target of
`binaryFactorizationMap` identifies with a pair of stalk-ring elements. -/
private noncomputable def pointBinaryFactorizationTargetIso
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point) :
    p.sheafFiber.obj
        ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪)) ≅
      (sourcePointRing 𝒪 p × sourcePointRing 𝒪 p) := by
  let O := underlyingTypeSheaf (J := J) 𝒪
  let eRing := pointRingCarrierIso (J := J) 𝒪 p
  let eProd :
      p.sheafFiber.obj (O ⨯ O) ≅ p.sheafFiber.obj O ⨯ p.sheafFiber.obj O :=
    Limits.PreservesLimitPair.iso p.sheafFiber O O
  let eTypes :
      p.sheafFiber.obj O ⨯ p.sheafFiber.obj O ≅
        (p.sheafFiber.obj O × p.sheafFiber.obj O) :=
    CategoryTheory.Limits.Types.binaryProductIso _ _
  exact eProd ≪≫ eTypes ≪≫ (Equiv.prodCongr eRing.toEquiv eRing.toEquiv).toIso

/-- Helper for Lemma 18.40.2: after taking the point fiber, the source of
`binaryFactorizationMap` identifies with a tagged pair of stalk-ring elements. -/
local instance pointBinaryFactorizationHasColimit
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Limits.HasColimit
      (Limits.pair
        ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪))
        ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪))) := by
  let _ : Limits.HasColimitsOfShape (Discrete Limits.WalkingPair) (Type (max u v)) :=
    inferInstance
  let _ : Limits.HasColimitsOfShape (Discrete Limits.WalkingPair) (Sheaf J (Type (max u v))) :=
    (Sheaf.instHasColimitsOfShape :
      Limits.HasColimitsOfShape (Discrete Limits.WalkingPair) (Sheaf J (Type (max u v))))
  infer_instance

/-- Helper for Lemma 18.40.2: after taking the point fiber, the source of
`binaryFactorizationMap` identifies with a tagged pair of stalk-ring elements. -/
private noncomputable def pointBinaryFactorizationSourceIso
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point) :
    p.sheafFiber.obj
        (((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪)) ⨿
          ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪))) ≅
      Sum
        (sourcePointRing 𝒪 p × sourcePointRing 𝒪 p)
        (sourcePointRing 𝒪 p × sourcePointRing 𝒪 p) := by
  let O := underlyingTypeSheaf (J := J) 𝒪
  let eTarget := pointBinaryFactorizationTargetIso (J := J) 𝒪 p
  let eCoprod :
      p.sheafFiber.obj ((O ⨯ O) ⨿ (O ⨯ O)) ≅
        p.sheafFiber.obj (O ⨯ O) ⨿ p.sheafFiber.obj (O ⨯ O) :=
    (Limits.PreservesColimitPair.iso p.sheafFiber (O ⨯ O) (O ⨯ O)).symm
  let eTypes :
      p.sheafFiber.obj (O ⨯ O) ⨿ p.sheafFiber.obj (O ⨯ O) ≅
        Sum (p.sheafFiber.obj (O ⨯ O)) (p.sheafFiber.obj (O ⨯ O)) :=
    CategoryTheory.Limits.Types.binaryCoproductIso _ _
  exact eCoprod ≪≫ eTypes ≪≫ (Equiv.sumCongr eTarget.toEquiv eTarget.toEquiv).toIso

/-- Helper for Lemma 18.40.2: the inverse source normalization sends a left-tagged normalized pair
back through the left coproduct inclusion. -/
private lemma pointBinaryFactorizationSourceIso_inv_inl
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point)
    (z : sourcePointRing 𝒪 p × sourcePointRing 𝒪 p) :
    (pointBinaryFactorizationSourceIso (J := J) 𝒪 p).inv (Sum.inl z) =
      (p.sheafFiber.map
        (coprod.inl :
          (underlyingTypeSheaf (J := J) 𝒪 ⨯ underlyingTypeSheaf (J := J) 𝒪) ⟶
            ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪)) ⨿
              ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪))))
        ((pointBinaryFactorizationTargetIso (J := J) 𝒪 p).inv z) := by
  -- Proof comment: unwind the coproduct comparison and the `Type`-level sum comparison on the
  -- left generator before applying the point-fiber coproduct comparison.
  simp [pointBinaryFactorizationSourceIso, PreservesColimitPair.iso_hom, Category.assoc]

/-- Helper for Lemma 18.40.2: the inverse source normalization sends a right-tagged normalized pair
back through the right coproduct inclusion. -/
private lemma pointBinaryFactorizationSourceIso_inv_inr
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point)
    (z : sourcePointRing 𝒪 p × sourcePointRing 𝒪 p) :
    (pointBinaryFactorizationSourceIso (J := J) 𝒪 p).inv (Sum.inr z) =
      (p.sheafFiber.map
        (coprod.inr :
          (underlyingTypeSheaf (J := J) 𝒪 ⨯ underlyingTypeSheaf (J := J) 𝒪) ⟶
            ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪)) ⨿
              ((underlyingTypeSheaf (J := J) 𝒪) ⨯ (underlyingTypeSheaf (J := J) 𝒪))))
        ((pointBinaryFactorizationTargetIso (J := J) 𝒪 p).inv z) := by
  -- Proof comment: the right branch is the same coproduct normalization with `Sum.inr`.
  simp [pointBinaryFactorizationSourceIso, PreservesColimitPair.iso_hom, Category.assoc]

/-- Helper for Lemma 18.40.2: the point-fiber map of `binaryFactorizationMap` becomes the explicit
ring-level binary factorization map after the source and target are normalized. -/
private lemma pointBinaryFactorizationConjugation
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point)
    (z :
      Sum
        (sourcePointRing 𝒪 p × sourcePointRing 𝒪 p)
        (sourcePointRing 𝒪 p × sourcePointRing 𝒪 p)) :
    (pointBinaryFactorizationTargetIso (J := J) 𝒪 p).hom
        ((p.sheafFiber.map (binaryFactorizationMap 𝒪))
          ((pointBinaryFactorizationSourceIso (J := J) 𝒪 p).inv z)) =
      binaryFactorizationOnRing z := by
  -- TODO: the source normalization is now reduced to the two branch lemmas above. The remaining
  -- work is the target-side compatibility of `pointRingCarrierIso` with the two sectionwise
  -- formulas `binaryFactorizationLeft` and `binaryFactorizationRight`.
  sorry

/-- Helper for Lemma 18.40.2: if a point stalk ring is zero or local, then the point-fiber map of
`binaryFactorizationMap` is surjective. -/
private lemma pointBinaryFactorizationMap_surjective_of_zeroOrLocal
    (𝒪 : Sheaf J CommRingCat.{max u v}) (p : J.Point)
    (hStalk : Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p)) :
    Function.Surjective (p.sheafFiber.map (binaryFactorizationMap 𝒪)) := by
  intro z
  let z' := (pointBinaryFactorizationTargetIso (J := J) 𝒪 p).hom z
  obtain ⟨w, hw⟩ :=
    binaryFactorization_surjective_of_subsingleton_or_isLocalRing (R := sourcePointRing 𝒪 p)
      hStalk z'
  refine ⟨(pointBinaryFactorizationSourceIso (J := J) 𝒪 p).inv w, ?_⟩
  -- Proof comment: transport the stalk target to the explicit pair model and close there.
  apply (pointBinaryFactorizationTargetIso (J := J) 𝒪 p).toEquiv.injective
  simpa [z'] using (pointBinaryFactorizationConjugation (J := J) 𝒪 p w).trans hw

/-- Helper for Lemma 18.40.2: every element of a point stalk is a unit or has unit complement
whenever the structure sheaf satisfies the local unit dichotomy. -/
lemma stalk_isUnit_or_isUnit_one_sub_of_hasLocalUnitDichotomy
    (𝒪 : Sheaf J CommRingCat.{max u v}) [HasLocalUnitDichotomy J 𝒪]
    (p : J.Point) (a : sourcePointRing 𝒪 p) :
    IsUnit a ∨ IsUnit (1 - a) :=
by
  -- Route correction: the remaining blocker is not the germ-transport step but the exact point
  -- cover-lift API needed to choose one arrow of the local-dichotomy cover through the point.
  -- Once that lift is in hand, `stalkRestriction_eq_of_coverLift` transports the representative.
  let a' : ToType (p.presheafFiber.obj 𝒪.obj) := a
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := 𝒪.obj) a'
  obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) U s
  obtain ⟨I, y, hy⟩ := p.existsArrowLiftOfCover S x
  rcases hS I with hI | hI
  · left
    -- Proof comment: a unit after restriction remains a unit after mapping into the stalk ring.
    have hUnit :
        IsUnit
          (((p.toPresheafFiber I.Y y 𝒪.obj).hom) ((𝒪.obj.map I.f.op).hom s)) :=
      hI.map (p.toPresheafFiber I.Y y 𝒪.obj).hom
    rw [stalkRestriction_eq_of_coverLift 𝒪 p I.f x y hy s] at hUnit
    simpa using hUnit
  · right
    -- Proof comment: the same transport works for the complementary section `1 - s`.
    have hUnit :
        IsUnit
          (((p.toPresheafFiber I.Y y 𝒪.obj).hom) (1 - (𝒪.obj.map I.f.op).hom s)) :=
      hI.map (p.toPresheafFiber I.Y y 𝒪.obj).hom
    have hOneSub :
        ((p.toPresheafFiber I.Y y 𝒪.obj).hom) (1 - (𝒪.obj.map I.f.op).hom s) =
          1 - ((p.toPresheafFiber U x 𝒪.obj).hom) s := by
      calc
        ((p.toPresheafFiber I.Y y 𝒪.obj).hom) (1 - (𝒪.obj.map I.f.op).hom s)
            = 1 - ((p.toPresheafFiber I.Y y 𝒪.obj).hom) ((𝒪.obj.map I.f.op).hom s) := by
                simp
        _ = 1 - ((p.toPresheafFiber U x 𝒪.obj).hom) s := by
              rw [stalkRestriction_eq_of_coverLift 𝒪 p I.f x y hy s]
    rw [hOneSub] at hUnit
    simpa using hUnit

-- Proof sketch: represent a stalk element by a section, apply the local
-- invertibility/complement-invertibility cover from `HasLocalUnitDichotomy J 𝒪`, and use the point
-- axiom to refine to one member of the cover. This shows that every element of the stalk ring is
-- either a unit or has unit complement; Lemma `10.18.3` then yields that the stalk ring is either
-- trivial or local.
/-- Lemma 18.40.2, forward direction: under the chapter-local owner
`HasLocalUnitDichotomy J 𝒪`, every point stalk is either the zero ring or a local ring. -/
@[stacks 04ET]
theorem stalkwise_zero_or_local_of_hasLocalUnitDichotomy
    (𝒪 : Sheaf J CommRingCat.{max u v}) [HasLocalUnitDichotomy J 𝒪]
    (p : J.Point) :
    Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) := by
  by_cases hSub : Subsingleton (sourcePointRing 𝒪 p)
  · exact Or.inl hSub
  · right
    letI : Nontrivial (sourcePointRing 𝒪 p) := (not_subsingleton_iff_nontrivial.1 hSub)
    -- The stalkwise unit-or-complement-unit dichotomy is the standard local-ring criterion.
    exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦
      stalk_isUnit_or_isUnit_one_sub_of_hasLocalUnitDichotomy (J := J) 𝒪 p a

-- Proof sketch: use Lemma `18.40.1` to identify `HasLocalUnitDichotomy J 𝒪` with local
-- surjectivity of the canonical binary factorization map, check this map is stalkwise surjective
-- because each stalk ring is zero or local by Lemma `10.18.3`, and then reflect local
-- surjectivity from stalks using enough points.
/-- Lemma 18.40.2: if the site has enough points, then the local unit dichotomy is equivalent to
every point stalk being either the zero ring or a local ring. -/
@[stacks 04ET]
theorem hasLocalUnitDichotomy_iff_stalkwise_zero_or_local
    [GrothendieckTopology.HasEnoughPoints.{max u v} J]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    HasLocalUnitDichotomy J 𝒪 ↔
      ∀ p : J.Point,
        Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) :=
by
  constructor
  · -- The forward implication is the stalkwise criterion already established above.
    intro h p
    letI : HasLocalUnitDichotomy J 𝒪 := h
    exact stalkwise_zero_or_local_of_hasLocalUnitDichotomy (J := J) 𝒪 p
  · intro hStalk
    -- Route correction: the converse should first reflect stalkwise surjectivity of
    -- `binaryFactorizationMap 𝒪` to a global epi under enough points, then invoke Lemma 18.40.1.
    have hLoc : Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) := by
      have hEpi : Epi (binaryFactorizationMap 𝒪) := by
        -- Proof comment: enough points gives a conservative indexed family, and the stalkwise
        -- surjectivity helper above applies to each point in that family.
        obtain ⟨ι, q, hq⟩ :=
          (GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily
            (J := J)).1 inferInstance
        exact GrothendieckTopology.sheaf_epi_of_stalkwise_surjective
          (p := q) hq (binaryFactorizationMap 𝒪)
          (fun i ↦ pointBinaryFactorizationMap_surjective_of_zeroOrLocal
            (J := J) 𝒪 (q i) (hStalk (q i)))
      exact (Sheaf.isLocallySurjective_iff_epi (binaryFactorizationMap 𝒪)).2 hEpi
    exact hasLocalUnitDichotomy_of_binaryFactorizationMap_isLocallySurjective
      (J := J) 𝒪 hLoc

end

end CategoryTheory
