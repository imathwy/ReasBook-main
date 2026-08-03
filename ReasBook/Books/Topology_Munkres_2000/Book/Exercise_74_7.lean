module

public import Topology_Munkres_2000.Book.Theorem_74_4
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace NonorientableSurfacePresentation

-- The first surface generator is sent to the left involution and all remaining
-- generators are sent to the right involution.
/-- Helper for Exercise 74.7: assign the surface generators to the two distinguished
generators of `Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 2)`. -/
def zmodTwoCoprodGenerator (m : ℕ) (i : Fin m) :
    Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)) :=
  if i.val = 0 then
    Monoid.Coprod.inl (Multiplicative.ofAdd 1)
  else
    Monoid.Coprod.inr (Multiplicative.ofAdd 1)

/-- Helper for Exercise 74.7: the distinguished element of `Multiplicative (ZMod 2)`
is an involution. -/
lemma multiplicativeZModTwo_generator_sq :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
  -- Under the multiplicative tag, the square is addition by two modulo two.
  change (1 + 1 : ZMod 2) = 0
  decide

/-- Helper for Exercise 74.7: every selected coproduct generator is an involution. -/
lemma zmodTwoCoprodGenerator_sq (m : ℕ) (i : Fin m) :
    (zmodTwoCoprodGenerator m i) ^ 2 = 1 := by
  -- Each branch is the image of the same order-two element under a factor inclusion.
  unfold zmodTwoCoprodGenerator
  split_ifs
  · rw [← map_pow, multiplicativeZModTwo_generator_sq, map_one]
  · rw [← map_pow, multiplicativeZModTwo_generator_sq, map_one]

/-- Helper for Exercise 74.7: the generator assignment kills the nonorientable
surface relator. -/
lemma zmodTwoCoprodGenerator_relator_eq_one (m : ℕ) :
    FreeGroup.lift (zmodTwoCoprodGenerator m) (NonorientableSurfaceGroup.relator m) = 1 := by
  -- Map the ordered product of squares and use the involution calculation termwise.
  rw [NonorientableSurfaceGroup.relator_def, map_list_prod]
  apply List.prod_eq_one
  intro g hg
  obtain ⟨generatorSquare, hgeneratorSquare, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_ofFn'] at hgeneratorSquare
  obtain ⟨i, rfl⟩ := hgeneratorSquare
  rw [map_pow, FreeGroup.lift_apply_of, zmodTwoCoprodGenerator_sq]

/-- Helper for Exercise 74.7: every element of `ZMod 2` is zero or one. -/
lemma zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  -- The canonical representative has value strictly below two.
  have hval : a.val = 0 ∨ a.val = 1 := by
    have hlt := a.val_lt
    omega
  rcases hval with hzero | hone
  · left
    rw [← ZMod.natCast_zmod_val a, hzero]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val a, hone]
    norm_num

/-- Helper for Exercise 74.7: every element of the multiplicative cyclic group of
order two is the identity or its distinguished generator. -/
lemma multiplicativeZModTwo_eq_one_or_generator (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  -- Transport the two-element classification across the multiplicative tag.
  rcases zmodTwo_eq_zero_or_one a.toAdd with hzero | hone
  · left
    simpa using congrArg Multiplicative.ofAdd hzero
  · right
    simpa using congrArg Multiplicative.ofAdd hone

/-- Helper for Exercise 74.7: when there are at least two surface generators, their
free-group lift generates both factors of the coproduct. -/
lemma zmodTwoCoprodGenerator_lift_surjective (m : ℕ) (hm : 1 < m) :
    Function.Surjective (FreeGroup.lift (zmodTwoCoprodGenerator m)) := by
  -- Induct over coproduct words, giving explicit preimages for each factor element.
  intro y
  induction y using Monoid.Coprod.induction_on with
  | inl a =>
      rcases multiplicativeZModTwo_eq_one_or_generator a with hone | hgenerator
      · subst a
        refine ⟨1, ?_⟩
        simp
      · subst a
        refine ⟨FreeGroup.of ⟨0, Nat.zero_lt_of_lt hm⟩, ?_⟩
        simp [zmodTwoCoprodGenerator]
  | inr a =>
      rcases multiplicativeZModTwo_eq_one_or_generator a with hone | hgenerator
      · subst a
        refine ⟨1, ?_⟩
        simp
      · subst a
        refine ⟨FreeGroup.of ⟨1, hm⟩, ?_⟩
        simp [zmodTwoCoprodGenerator]
  | mul a b ha hb =>
      obtain ⟨wa, hwa⟩ := ha
      obtain ⟨wb, hwb⟩ := hb
      refine ⟨wa * wb, ?_⟩
      rw [map_mul, hwa, hwb]

/-- The homomorphism suggested in Exercise 74.7: the fundamental group of the `m`-fold
projective plane maps onto `ℤ/2 ∗ ℤ/2`. -/
theorem exists_surjective_to_zmodTwo_coprod (m : ℕ) (hm : 1 < m)
    (x : mFoldProjectivePlane m hm) :
    ∃ φ : FundamentalGroup (mFoldProjectivePlane m hm) x →*
        Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)),
      Function.Surjective φ := by
  -- The relator calculation lets the generator assignment descend to the presentation.
  have hrel : ∀ r ∈ ({NonorientableSurfaceGroup.relator m} :
      Set (FreeGroup (Fin m))), FreeGroup.lift (zmodTwoCoprodGenerator m) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    exact zmodTwoCoprodGenerator_relator_eq_one m
  let presentationHom : NonorientableSurfaceGroup.Presentation m →*
      Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)) :=
    PresentedGroup.toGroup hrel
  -- The descended map agrees with the original free-group lift on every generator.
  have hpresentation_comp :
      presentationHom.comp
          (PresentedGroup.mk ({NonorientableSurfaceGroup.relator m} :
            Set (FreeGroup (Fin m)))) =
        FreeGroup.lift (zmodTwoCoprodGenerator m) := by
    apply FreeGroup.ext_hom
    intro i
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of hrel
  -- Surjectivity before descent supplies surjectivity of the presentation map.
  have hpresentation_surjective : Function.Surjective presentationHom := by
    intro y
    obtain ⟨w, hw⟩ := zmodTwoCoprodGenerator_lift_surjective m hm y
    refine ⟨PresentedGroup.mk
      ({NonorientableSurfaceGroup.relator m} : Set (FreeGroup (Fin m))) w, ?_⟩
    have hw' := DFunLike.congr_fun hpresentation_comp w
    exact hw'.trans hw
  -- Transport the presentation map across the fundamental-group equivalence.
  obtain ⟨e⟩ := fundamentalGroupMulEquiv m hm x
  let φ := presentationHom.comp e.toMonoidHom
  have hφ : Function.Surjective φ := hpresentation_surjective.comp e.surjective
  exact ⟨φ, hφ⟩

/-- Helper for Exercise 74.7: an involution determines a homomorphism from
`Multiplicative (ZMod 2)`. -/
lemma exists_zmodTwoHom_of_sq_eq_one {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) :
    ∃ f : Multiplicative (ZMod 2) →* G, f (Multiplicative.ofAdd 1) = g := by
  -- The multiples map kills two precisely because the chosen element squares to one.
  have htwo : zmultiplesHom (Additive G) (Additive.ofMul g) 2 = 0 := by
    have hproduct : g * g = 1 := by
      simpa only [pow_two] using hg
    simpa only [zmultiplesHom_apply, two_zsmul, ofMul_mul,
      ofMul_one] using congrArg Additive.ofMul hproduct
  let additiveHom : ZMod 2 →+ Additive G :=
    ZMod.lift 2 ⟨zmultiplesHom (Additive G) (Additive.ofMul g), htwo⟩
  let f : Multiplicative (ZMod 2) →* G :=
    AddMonoidHom.toMultiplicativeLeft additiveHom
  -- The computation rule for `ZMod.lift` identifies the distinguished generator's image.
  refine ⟨f, ?_⟩
  change (additiveHom (1 : ZMod 2)).toMul = g
  have hone : (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
    norm_num
  dsimp only [additiveHom]
  rw [hone, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, one_zsmul, toMul_ofMul]

/-- Helper for Exercise 74.7: the coproduct of two cyclic groups of order two is not
commutative. -/
lemma zmodTwoCoprod_not_isMulCommutative :
    ¬ IsMulCommutative
      (Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))) := by
  -- Map the two coproduct generators to distinct reflections of a triangle.
  have hreflectionZero : (DihedralGroup.sr (0 : ZMod 3)) ^ 2 = 1 := by
    simpa only [pow_two] using DihedralGroup.sr_mul_self (0 : ZMod 3)
  have hreflectionOne : (DihedralGroup.sr (1 : ZMod 3)) ^ 2 = 1 := by
    simpa only [pow_two] using DihedralGroup.sr_mul_self (1 : ZMod 3)
  obtain ⟨leftHom, hleftHom⟩ :=
    exists_zmodTwoHom_of_sq_eq_one (DihedralGroup.sr (0 : ZMod 3)) hreflectionZero
  obtain ⟨rightHom, hrightHom⟩ :=
    exists_zmodTwoHom_of_sq_eq_one (DihedralGroup.sr (1 : ZMod 3)) hreflectionOne
  intro hcomm
  have hproducts := congrArg (Monoid.Coprod.lift leftHom rightHom)
    (hcomm.is_comm.comm
      (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)))
      (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))))
  simp only [map_mul, Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inr,
    hleftHom, hrightHom, DihedralGroup.sr_mul_sr] at hproducts
  have hrotation : (1 : ZMod 3) - 0 = 0 - 1 := DihedralGroup.r.inj hproducts
  have hone_ne_neg_one : (1 : ZMod 3) ≠ -1 := by decide
  exact hone_ne_neg_one hrotation

/-- Exercise 74.7: If `m > 1`, the fundamental group of the `m`-fold projective plane is
not abelian, for every choice of basepoint. -/
theorem fundamentalGroup_not_isMulCommutative (m : ℕ) (hm : 1 < m)
    (x : mFoldProjectivePlane m hm) :
    ¬ IsMulCommutative (FundamentalGroup (mFoldProjectivePlane m hm) x) := by
  -- Commutativity would descend along the hinted surjection to the noncommutative coproduct.
  intro hcomm
  obtain ⟨φ, hφ⟩ := exists_surjective_to_zmodTwo_coprod m hm x
  exact zmodTwoCoprod_not_isMulCommutative
    (Function.Surjective.mul_comm (f := φ) hφ hcomm)

end NonorientableSurfacePresentation
