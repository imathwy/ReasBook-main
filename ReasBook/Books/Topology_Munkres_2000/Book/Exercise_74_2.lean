module

public import Topology_Munkres_2000.Book.Exercise_74_2.Presentation
public import Topology_Munkres_2000.Book.Theorem_74_2
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.Tactic.FinCases
import all Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Exercise_74_2.Presentation
import all Topology_Munkres_2000.Book.Theorem_74_2.Presentation

public section

namespace HeptagonFreeProduct

noncomputable section

/-- Helper for Exercise 74.2: parameter zero on an oriented pasted edge is its signed
initial vertex. -/
private lemma orientedPoint_zero {n : ℕ} {poly : CyclicPolygon n} {S : Type*}
    (q : poly.EdgePasting S) (i : Fin n) :
    q.orientedPoint i 0 = poly.vertexPoint (if q.sign i then i else finRotate n i) := by
  -- Reduce the affine parameter to the initial endpoint and then inspect the edge sign.
  apply Subtype.ext
  have hzero : ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
  rw [q.orientedPoint_apply, q.includePoint_coe, OrientedSegment.point_coe, hzero,
    AffineMap.lineMap_apply_zero, q.orientation_eq]
  cases hsign : q.sign i
  · simp only [Bool.false_eq_true, if_false, CyclicPolygon.signedOrientation,
      OrientedSegment.reverse_initial, CyclicPolygon.cyclicOrientation,
      CyclicPolygon.vertexPoint]
  · simp only [if_true, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation, CyclicPolygon.vertexPoint]

/-- Helper for Exercise 74.2: parameter one on an oriented pasted edge is its signed
final vertex. -/
private lemma orientedPoint_one {n : ℕ} {poly : CyclicPolygon n} {S : Type*}
    (q : poly.EdgePasting S) (i : Fin n) :
    q.orientedPoint i 1 = poly.vertexPoint (if q.sign i then finRotate n i else i) := by
  -- Reduce the affine parameter to the final endpoint and then inspect the edge sign.
  apply Subtype.ext
  have hone : ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
  rw [q.orientedPoint_apply, q.includePoint_coe, OrientedSegment.point_coe, hone,
    AffineMap.lineMap_apply_one, q.orientation_eq]
  cases hsign : q.sign i
  · simp only [Bool.false_eq_true, if_false, CyclicPolygon.signedOrientation,
      OrientedSegment.reverse_final, CyclicPolygon.cyclicOrientation,
      CyclicPolygon.vertexPoint]
  · simp only [if_true, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation, CyclicPolygon.vertexPoint]

/-- Helper for Exercise 74.2: equally labelled edges have equal quotient images at
their signed initial endpoints and at their signed final endpoints. -/
private lemma quotientMap_signedEndpoints_eq_of_label_eq {n : ℕ}
    {poly : CyclicPolygon n} {S : Type*} (q : poly.EdgePasting S) (i j : Fin n)
    (hlabel : q.label i = q.label j) :
    q.quotientMap (poly.vertexPoint (if q.sign i then i else finRotate n i)) =
        q.quotientMap (poly.vertexPoint (if q.sign j then j else finRotate n j)) ∧
      q.quotientMap (poly.vertexPoint (if q.sign i then finRotate n i else i)) =
        q.quotientMap (poly.vertexPoint (if q.sign j then finRotate n j else j)) := by
  -- The edge-pasting relation pairs points with the same oriented affine parameter.
  have horiented (t : Set.Icc (0 : ℝ) 1) :
      q.quotientMap (q.orientedPoint i t) = q.quotientMap (q.orientedPoint j t) := by
    apply Quotient.sound
    apply Relation.EqvGen.rel
    rw [q.related_iff]
    refine ⟨i, j, hlabel, (q.orientation i).point t, q.orientedPoint_apply i t, ?_⟩
    rw [q.positiveIdentification_point]
    exact q.orientedPoint_apply j t
  -- Specialize the common-parameter equality to the two endpoints.
  constructor
  · simpa only [orientedPoint_zero] using horiented 0
  · simpa only [orientedPoint_one] using horiented 1

/-- Helper for Exercise 74.2: every vertex of the heptagon has image `basepoint` in
the pasted quotient. -/
private lemma quotientMap_vertexPoint (i : Fin 7) :
    quotientMap (polygon.vertexPoint i) = basepoint := by
  -- Compare edge zero with the other four edges carrying the label `a`.
  have h02raw := quotientMap_signedEndpoints_eq_of_label_eq pasting 0 2 rfl
  have h03raw := quotientMap_signedEndpoints_eq_of_label_eq pasting 0 3 rfl
  have h04raw := quotientMap_signedEndpoints_eq_of_label_eq pasting 0 4 rfl
  have h06raw := quotientMap_signedEndpoints_eq_of_label_eq pasting 0 6 rfl
  have h02 : quotientMap (polygon.vertexPoint 0) =
      quotientMap (polygon.vertexPoint 2) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h02raw.1
  have h13 : quotientMap (polygon.vertexPoint 1) =
      quotientMap (polygon.vertexPoint 3) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h02raw.2
  have h03 : quotientMap (polygon.vertexPoint 0) =
      quotientMap (polygon.vertexPoint 3) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h03raw.1
  have h04 : quotientMap (polygon.vertexPoint 0) =
      quotientMap (polygon.vertexPoint 4) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h04raw.1
  have h15 : quotientMap (polygon.vertexPoint 1) =
      quotientMap (polygon.vertexPoint 5) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h04raw.2
  have h16 : quotientMap (polygon.vertexPoint 1) =
      quotientMap (polygon.vertexPoint 6) := by
    simpa [Space, quotientMap, pasting, CyclicPolygon.EdgePasting.ofSigns,
      finRotate_apply] using h06raw.2
  have h10 : quotientMap (polygon.vertexPoint 1) =
      quotientMap (polygon.vertexPoint 0) := h13.trans h03.symm
  -- Enumerate the seven vertices and follow these endpoint equalities back to vertex zero.
  fin_cases i
  · rfl
  · exact h10
  · exact h02.symm
  · exact h03.symm
  · exact h04.symm
  · exact h15.symm.trans h10
  · exact h16.symm.trans h10

/-- Helper for Exercise 74.2: the one-relator group associated to the heptagon
pasting. -/
private abbrev Presentation : Type :=
  PresentedGroup ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))

/-- Helper for Exercise 74.2: the used label represented by the first edge. -/
private def aLabel : pasting.UsedLabel :=
  ⟨pasting.label 0, Set.mem_range_self 0⟩

/-- Helper for Exercise 74.2: the used label represented by the second edge. -/
private def bLabel : pasting.UsedLabel :=
  ⟨pasting.label 1, Set.mem_range_self 1⟩

/-- Helper for Exercise 74.2: the heptagonal boundary relator is
`a * b * a³ * b⁻¹ * a⁻¹` in the free group. -/
private lemma relator_eq_conjugateCube :
    pasting.relator =
      FreeGroup.of aLabel * FreeGroup.of bLabel * FreeGroup.of aLabel ^ 3 *
        (FreeGroup.of bLabel)⁻¹ * (FreeGroup.of aLabel)⁻¹ := by
  have mk_generatorWord (a b : pasting.UsedLabel) :
      FreeGroup.mk
          [(a, true), (b, true), (a, true), (a, true), (a, true),
            (b, false), (a, false)] =
        FreeGroup.of a * FreeGroup.of b * FreeGroup.of a ^ 3 *
          (FreeGroup.of b)⁻¹ * (FreeGroup.of a)⁻¹ := by
    rw [pow_three']
    rfl
  -- Expand the seven signed edges once and collect the three consecutive `a` letters.
  simpa [CyclicPolygon.EdgePasting.relator, CyclicPolygon.EdgePasting.boundaryWord,
    pasting, CyclicPolygon.EdgePasting.ofSigns, aLabel, bLabel] using
    mk_generatorWord aLabel bLabel

/-- Helper for Exercise 74.2: the canonical `a` generator has order dividing three
in the heptagon presentation. -/
private lemma presentationGeneratorA_cube :
    (PresentedGroup.of aLabel : Presentation) ^ 3 = 1 := by
  have hrelator :
      PresentedGroup.mk ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))
          pasting.relator = 1 :=
    PresentedGroup.one_of_mem (Set.mem_singleton pasting.relator)
  have hconjugate :
      (PresentedGroup.of aLabel : Presentation) * PresentedGroup.of bLabel *
          PresentedGroup.of aLabel ^ 3 * (PresentedGroup.of bLabel)⁻¹ *
            (PresentedGroup.of aLabel)⁻¹ = 1 := by
    simpa [PresentedGroup.of, relator_eq_conjugateCube] using hrelator
  -- Cancel the outer `a` and `b` conjugations, leaving precisely the cube relation.
  have hwithoutA :
      (PresentedGroup.of aLabel : Presentation) * PresentedGroup.of bLabel *
          PresentedGroup.of aLabel ^ 3 * (PresentedGroup.of bLabel)⁻¹ =
        PresentedGroup.of aLabel := by
    calc
      (PresentedGroup.of aLabel : Presentation) * PresentedGroup.of bLabel *
            PresentedGroup.of aLabel ^ 3 * (PresentedGroup.of bLabel)⁻¹ =
          ((PresentedGroup.of aLabel : Presentation) * PresentedGroup.of bLabel *
              PresentedGroup.of aLabel ^ 3 * (PresentedGroup.of bLabel)⁻¹ *
                (PresentedGroup.of aLabel)⁻¹) * PresentedGroup.of aLabel := by
            exact (inv_mul_cancel_right _ _).symm
      _ = 1 * PresentedGroup.of aLabel := by rw [hconjugate]
      _ = PresentedGroup.of aLabel := one_mul _
  have hwithoutB :
      (PresentedGroup.of bLabel : Presentation) * PresentedGroup.of aLabel ^ 3 *
          (PresentedGroup.of bLabel)⁻¹ = 1 := by
    apply mul_left_cancel (a := (PresentedGroup.of aLabel : Presentation))
    simpa only [mul_assoc, mul_one] using hwithoutA
  have hcubeWithB :
      (PresentedGroup.of bLabel : Presentation) * PresentedGroup.of aLabel ^ 3 =
        PresentedGroup.of bLabel := by
    calc
      (PresentedGroup.of bLabel : Presentation) * PresentedGroup.of aLabel ^ 3 =
          ((PresentedGroup.of bLabel : Presentation) * PresentedGroup.of aLabel ^ 3 *
              (PresentedGroup.of bLabel)⁻¹) * PresentedGroup.of bLabel := by
            exact (inv_mul_cancel_right _ _).symm
      _ = 1 * PresentedGroup.of bLabel := by rw [hwithoutB]
      _ = PresentedGroup.of bLabel := one_mul _
  apply mul_left_cancel (a := (PresentedGroup.of bLabel : Presentation))
  simpa only [mul_one] using hcubeWithB

/-- Helper for Exercise 74.2: every used label is represented by either the `a` edge
or the `b` edge. -/
private lemma usedLabel_eq_a_or_b (x : pasting.UsedLabel) :
    x = aLabel ∨ x = bLabel := by
  -- The ambient label type is `Fin 2`, so enumerate its two possible values.
  rcases x with ⟨x, hx⟩
  fin_cases x
  · left
    apply Subtype.ext
    simp [aLabel, pasting, CyclicPolygon.EdgePasting.ofSigns]
  · right
    apply Subtype.ext
    simp [bLabel, pasting, CyclicPolygon.EdgePasting.ofSigns]

/-- Helper for Exercise 74.2: the target free product of the order-three and infinite
cyclic groups. -/
private abbrev CyclicCoprod :=
  Monoid.Coprod (Multiplicative (ZMod 3)) (Multiplicative ℤ)

/-- Helper for Exercise 74.2: send `a` to the order-three factor and `b` to the
infinite cyclic factor. -/
private def coprodGenerator (x : pasting.UsedLabel) : CyclicCoprod :=
  if x.1 = aLabel.1 then
    Monoid.Coprod.inl (Multiplicative.ofAdd 1)
  else
    Monoid.Coprod.inr (Multiplicative.ofAdd 1)

/-- Helper for Exercise 74.2: the generator assignment sends `a` to the left
coproduct generator. -/
private lemma coprodGenerator_aLabel :
    coprodGenerator aLabel = Monoid.Coprod.inl (Multiplicative.ofAdd 1) := by
  -- The defining branch recognizes the first edge label.
  rw [coprodGenerator, if_pos rfl]

/-- Helper for Exercise 74.2: the generator assignment sends `b` to the right
coproduct generator. -/
private lemma coprodGenerator_bLabel :
    coprodGenerator bLabel = Monoid.Coprod.inr (Multiplicative.ofAdd 1) := by
  -- The two concrete labels in `Fin 2` are distinct.
  simp [coprodGenerator, aLabel, bLabel, pasting, CyclicPolygon.EdgePasting.ofSigns]

/-- Helper for Exercise 74.2: the distinguished element of `Multiplicative (ZMod 3)`
has cube one. -/
private lemma multiplicativeZModThree_generator_cube :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
  -- Under the multiplicative tag, cubing adds three modulo three.
  change (1 + (1 + 1) : ZMod 3) = 0
  decide

/-- Helper for Exercise 74.2: the coproduct generator assignment kills the
heptagonal boundary relator. -/
private lemma coprodGenerator_relator_eq_one :
    FreeGroup.lift coprodGenerator pasting.relator = 1 := by
  have hleftCube :
      (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) : CyclicCoprod) ^ 3 = 1 := by
    rw [← map_pow, multiplicativeZModThree_generator_cube, map_one]
  -- Normalize the relator, map its factors, and use the order-three relation.
  rw [relator_eq_conjugateCube]
  simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of,
    coprodGenerator_aLabel, coprodGenerator_bLabel, hleftCube, mul_one,
    mul_inv_cancel_right, mul_inv_cancel]

/-- Helper for Exercise 74.2: the coproduct generator assignment respects the
singleton defining relation. -/
private lemma coprodGenerator_respectsRelator
    (r : FreeGroup pasting.UsedLabel)
    (hr : r ∈ ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))) :
    FreeGroup.lift coprodGenerator r = 1 := by
  -- Singleton membership reduces the universal-property condition to the relator calculation.
  rw [Set.mem_singleton_iff] at hr
  subst r
  exact coprodGenerator_relator_eq_one

/-- Helper for Exercise 74.2: the presentation maps canonically to the two cyclic
factors. -/
private def presentationToCoprod : Presentation →* CyclicCoprod :=
  PresentedGroup.toGroup coprodGenerator_respectsRelator

/-- Helper for Exercise 74.2: the presentation map sends its `a` generator to the
left factor generator. -/
private lemma presentationToCoprod_aLabel :
    presentationToCoprod (PresentedGroup.of aLabel) =
      Monoid.Coprod.inl (Multiplicative.ofAdd 1) := by
  -- Apply the computation rule of the presented-group universal property.
  rw [presentationToCoprod, PresentedGroup.toGroup.of]
  exact coprodGenerator_aLabel

/-- Helper for Exercise 74.2: the presentation map sends its `b` generator to the
right factor generator. -/
private lemma presentationToCoprod_bLabel :
    presentationToCoprod (PresentedGroup.of bLabel) =
      Monoid.Coprod.inr (Multiplicative.ofAdd 1) := by
  -- Apply the computation rule of the presented-group universal property.
  rw [presentationToCoprod, PresentedGroup.toGroup.of]
  exact coprodGenerator_bLabel

/-- Helper for Exercise 74.2: three integer multiples of the additive form of the
presentation's `a` generator vanish. -/
private lemma presentationGeneratorA_zmultiples_three :
    zmultiplesHom (Additive Presentation)
        (Additive.ofMul (PresentedGroup.of aLabel : Presentation)) 3 = 0 := by
  -- Transport the cube relation across the multiplicative-to-additive tag.
  have hcube := congrArg (fun g : Presentation ↦ Additive.ofMul g)
    presentationGeneratorA_cube
  have htriple :
      Additive.ofMul (PresentedGroup.of aLabel : Presentation) +
          (Additive.ofMul (PresentedGroup.of aLabel : Presentation) +
            Additive.ofMul (PresentedGroup.of aLabel : Presentation)) = 0 := by
    simpa only [ofMul_pow, ofMul_one, three_nsmul] using hcube
  rw [zmultiplesHom_apply]
  calc
    (3 : ℤ) • Additive.ofMul (PresentedGroup.of aLabel : Presentation) =
        (1 + 2 : ℤ) • Additive.ofMul (PresentedGroup.of aLabel : Presentation) := by
          rfl
    _ = (1 : ℤ) • Additive.ofMul (PresentedGroup.of aLabel : Presentation) +
        (2 : ℤ) • Additive.ofMul (PresentedGroup.of aLabel : Presentation) :=
      add_zsmul _ _ _
    _ = Additive.ofMul (PresentedGroup.of aLabel : Presentation) +
        (Additive.ofMul (PresentedGroup.of aLabel : Presentation) +
          Additive.ofMul (PresentedGroup.of aLabel : Presentation)) := by
      rw [one_zsmul, two_zsmul]
    _ = 0 := htriple

/-- Helper for Exercise 74.2: the order-three cyclic group maps to the presentation
by sending its generator to `a`. -/
private def zmodThreeToPresentationAddHom : ZMod 3 →+ Additive Presentation :=
  ZMod.lift 3
    ⟨zmultiplesHom (Additive Presentation)
      (Additive.ofMul (PresentedGroup.of aLabel : Presentation)),
      presentationGeneratorA_zmultiples_three⟩

/-- Helper for Exercise 74.2: the multiplicative order-three factor maps to the
presentation by sending its generator to `a`. -/
private def zmodThreeToPresentation : Multiplicative (ZMod 3) →* Presentation :=
  AddMonoidHom.toMultiplicativeLeft zmodThreeToPresentationAddHom

/-- Helper for Exercise 74.2: the order-three factor map has the prescribed value on
its distinguished generator. -/
private lemma zmodThreeToPresentation_generator :
    zmodThreeToPresentation (Multiplicative.ofAdd 1) = PresentedGroup.of aLabel := by
  -- Compute the `ZMod.lift` on the integer representative one.
  change (zmodThreeToPresentationAddHom (1 : ZMod 3)).toMul =
    PresentedGroup.of aLabel
  have hone : (1 : ZMod 3) = ((1 : ℤ) : ZMod 3) := rfl
  rw [hone]
  simp only [zmodThreeToPresentationAddHom, ZMod.lift_coe, zmultiplesHom_apply,
    one_zsmul, toMul_ofMul]

/-- Helper for Exercise 74.2: the order-three factor map sends an integer class to
the corresponding power of `a`. -/
private lemma zmodThreeToPresentation_intCast (n : ℤ) :
    zmodThreeToPresentation (Multiplicative.ofAdd (n : ZMod 3)) =
      (PresentedGroup.of aLabel : Presentation) ^ n := by
  -- Compute `ZMod.lift` on the chosen integer representative and remove the type tags.
  change (zmodThreeToPresentationAddHom (n : ZMod 3)).toMul =
    (PresentedGroup.of aLabel : Presentation) ^ n
  simp only [zmodThreeToPresentationAddHom, ZMod.lift_coe, zmultiplesHom_apply,
    toMul_zsmul, toMul_ofMul]

/-- Helper for Exercise 74.2: the infinite cyclic factor maps to the presentation by
sending its generator to `b`. -/
private def integerToPresentation : Multiplicative ℤ →* Presentation :=
  zpowersHom Presentation (PresentedGroup.of bLabel)

/-- Helper for Exercise 74.2: the coproduct of cyclic factors maps back to the
presentation on its two canonical generators. -/
private def coprodToPresentation : CyclicCoprod →* Presentation :=
  Monoid.Coprod.lift zmodThreeToPresentation integerToPresentation

/-- Helper for Exercise 74.2: mapping from the presentation to the cyclic coproduct
and back is the identity. -/
private lemma coprodToPresentation_comp_presentationToCoprod :
    coprodToPresentation.comp presentationToCoprod = MonoidHom.id Presentation := by
  -- Presented-group extensionality reduces the composite to the two used labels.
  apply PresentedGroup.ext
  intro x
  rcases usedLabel_eq_a_or_b x with rfl | rfl
  · simp only [MonoidHom.comp_apply, presentationToCoprod_aLabel,
      coprodToPresentation, Monoid.Coprod.lift_apply_inl,
      zmodThreeToPresentation_generator, MonoidHom.id_apply]
  · simp only [MonoidHom.comp_apply, presentationToCoprod_bLabel,
      coprodToPresentation, Monoid.Coprod.lift_apply_inr, integerToPresentation,
      zpowersHom_apply, toAdd_ofAdd, zpow_one, MonoidHom.id_apply]

/-- Helper for Exercise 74.2: mapping from the cyclic coproduct to the presentation
and back is the identity. -/
private lemma presentationToCoprod_comp_coprodToPresentation :
    presentationToCoprod.comp coprodToPresentation = MonoidHom.id CyclicCoprod := by
  -- Coproduct extensionality separates the order-three and infinite cyclic factors.
  apply Monoid.Coprod.hom_ext
  · apply DFunLike.ext
    intro z
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective z.toAdd
    have hz : z = Multiplicative.ofAdd (n : ZMod 3) := by
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_ofAdd] using hn.symm
    subst z
    simp only [MonoidHom.comp_apply, coprodToPresentation,
      Monoid.Coprod.lift_apply_inl, zmodThreeToPresentation_intCast, map_zpow,
      presentationToCoprod_aLabel, MonoidHom.id_apply]
    rw [← map_zpow]
    simp only [← ofAdd_zsmul, zsmul_one]
  · apply MonoidHom.ext_mint
    simp only [MonoidHom.comp_apply, coprodToPresentation,
      Monoid.Coprod.lift_apply_inr, integerToPresentation, zpowersHom_apply,
      toAdd_ofAdd, zpow_one, presentationToCoprod_bLabel, MonoidHom.id_apply]

/-- Helper for Exercise 74.2: the heptagon presentation is the free product of the
order-three cyclic group and the infinite cyclic group. -/
private lemma nonemptyPresentationMulEquivCoprod :
    Nonempty (Presentation ≃* CyclicCoprod) := by
  -- Package the two universal-property maps and their generatorwise inverse laws.
  exact ⟨MonoidHom.toMulEquiv presentationToCoprod coprodToPresentation
    coprodToPresentation_comp_presentationToCoprod
    presentationToCoprod_comp_coprodToPresentation⟩

/-- Exercise 74.2: The fundamental group of the heptagon quotient is the free product of the
cyclic group of order three and the infinite cyclic group. -/
theorem fundamentalGroupMulEquiv :
    Nonempty
      (FundamentalGroup Space basepoint ≃*
        Monoid.Coprod (Multiplicative (ZMod 3)) (Multiplicative ℤ)) := by
  -- Theorem 74.2 converts the vertex-identified polygon quotient into its presentation.
  obtain ⟨topologicalEquiv⟩ :=
    CyclicPolygon.EdgePasting.fundamentalGroupMulEquiv
      pasting basepoint quotientMap_vertexPoint
  -- Compose that equivalence with the algebraic decomposition of the one-relator group.
  obtain ⟨algebraicEquiv⟩ := nonemptyPresentationMulEquivCoprod
  exact ⟨topologicalEquiv.trans algebraicEquiv⟩

end

end HeptagonFreeProduct
