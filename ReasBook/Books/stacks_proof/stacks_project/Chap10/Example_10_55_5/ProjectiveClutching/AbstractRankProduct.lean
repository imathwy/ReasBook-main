import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveRank
import StacksProject_2024.Chap10.Example_10_55_5.MilnorUnits

noncomputable section

universe u v w

/-- Helper for Chap10 Example 10 55 5: an additive group with an integer-valued homomorphism
split by a section is the product of the rank kernel and `ℤ`. -/
theorem addEquivProductOfRankSplit
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (s : ℤ →+ G)
    (hright : r.comp s = AddMonoidHom.id ℤ)
    (eker : A ≃+ r.ker) :
    ∃ e : G ≃+ A × ℤ,
      (AddMonoidHom.snd A ℤ).comp e.toAddMonoidHom = r := by
  let φ : G →+ A × ℤ :=
    { toFun := fun g =>
        (eker.symm ⟨g - s (r g), by
          -- The residual term has rank zero because the section has the same rank as `g`.
          have hs : r (s (r g)) = r g := by
            simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright (r g)
          simp [map_sub, hs]⟩, r g)
      map_zero' := by
        -- Both the rank and the residual component vanish at zero.
        ext <;> simp
      map_add' := by
        intro x y
        -- Residuals add because both `r` and the section `s` are additive homomorphisms.
        ext
        · apply eker.injective
          ext
          simp [map_add, sub_eq_add_neg]
          abel
        · simp [map_add] }
  have hφ_injective : Function.Injective φ := by
    intro x y hxy
    have hrank : r x = r y := congrArg Prod.snd hxy
    have hker : x - s (r x) = y - s (r y) := by
      have hfirst : (φ x).1 = (φ y).1 := congrArg Prod.fst hxy
      have hfirst' := congrArg eker hfirst
      simpa [φ] using congrArg Subtype.val hfirst'
    -- Reassemble each element from its rank-zero residual and its section part.
    calc
      x = (x - s (r x)) + s (r x) := by abel
      _ = (y - s (r y)) + s (r y) := by rw [hker, hrank]
      _ = y := by abel
  have hφ_surjective : Function.Surjective φ := by
    intro p
    rcases p with ⟨a, n⟩
    refine ⟨(eker a).1 + s n, ?_⟩
    -- The chosen kernel element supplies the first coordinate, and the section supplies the rank.
    ext
    · apply eker.injective
      ext
      have hker_zero : r (eker a).1 = 0 := (eker a).2
      have hs : r (s n) = n := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright n
      simp [φ, hker_zero, hs, map_add]
    · have hker_zero : r (eker a).1 = 0 := (eker a).2
      have hs : r (s n) = n := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright n
      simp [φ, hker_zero, hs, map_add]
  refine ⟨AddEquiv.ofBijective φ ⟨hφ_injective, hφ_surjective⟩, ?_⟩
  -- By construction, projecting to the integer coordinate is exactly `r`.
  apply AddMonoidHom.ext
  intro x
  rfl

/-- Helper for Chap10 Example 10 55 5: a product decomposition whose second coordinate is a
rank homomorphism identifies the first factor with the rank kernel. -/
theorem existsAddEquivRankKernelOfProduct
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (e : G ≃+ A × ℤ)
    (he : (AddMonoidHom.snd A ℤ).comp e.toAddMonoidHom = r) :
    Nonempty (A ≃+ r.ker) := by
  -- Send a first-coordinate element to the element whose product coordinates are `(a, 0)`.
  refine ⟨
    { toFun := fun a =>
        ⟨e.symm (a, 0), by
          have h := DFunLike.congr_fun he (e.symm (a, 0))
          simpa using h.symm⟩
      invFun := fun x => (e x.1).1
      left_inv := by
        -- Applying `e` immediately recovers the chosen first coordinate.
        intro a
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        apply e.injective
        have hsecond : (e x.1).2 = 0 := by
          exact (DFunLike.congr_fun he x.1).trans x.2
        -- The kernel condition forces the second product coordinate to be zero.
        ext <;> simp [hsecond]
      map_add' := by
        intro a b
        apply Subtype.ext
        -- Additivity follows from additivity of the inverse product equivalence.
        simpa using (e.symm.map_add (a, 0) (b, 0)) }⟩

/-- Helper for Chap10 Example 10 55 5: two-sided inverse homomorphisms between a group and a
rank product assemble the product equivalence with the prescribed rank projection. -/
theorem addEquivRankProductOfTwoSidedInverse
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (classMap : A × ℤ →+ G) (coordMap : G →+ A × ℤ)
    (hleft : coordMap.comp classMap = AddMonoidHom.id (A × ℤ))
    (hright : classMap.comp coordMap = AddMonoidHom.id G)
    (hsnd : (AddMonoidHom.snd A ℤ).comp coordMap = r) :
    ∃ e : G ≃+ A × ℤ,
      (AddMonoidHom.snd A ℤ).comp e.toAddMonoidHom = r := by
  have hcoord_injective : Function.Injective coordMap := by
    intro x y hxy
    -- The right inverse reassembles an element from its product coordinates, so equal
    -- coordinates force equality in the source group.
    calc
      x = classMap (coordMap x) := by
        simpa [AddMonoidHom.comp_apply] using (DFunLike.congr_fun hright x).symm
      _ = classMap (coordMap y) := by rw [hxy]
      _ = y := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright y
  have hcoord_surjective : Function.Surjective coordMap := by
    intro p
    -- The left inverse says every product coordinate is reached by the class map.
    refine ⟨classMap p, ?_⟩
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft p
  refine ⟨AddEquiv.ofBijective coordMap ⟨hcoord_injective, hcoord_surjective⟩, ?_⟩
  -- The equivalence is built from the coordinate homomorphism, so its second coordinate is `r`.
  simpa using hsnd

/-- Helper for Chap10 Example 10 55 5: for two-sided inverse class and coordinate maps, it is
enough to check the rank projection on the explicit class map. -/
theorem addEquivRankProductOfTwoSidedInverseWithRankOnClassMap
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (classMap : A × ℤ →+ G) (coordMap : G →+ A × ℤ)
    (hleft : coordMap.comp classMap = AddMonoidHom.id (A × ℤ))
    (hright : classMap.comp coordMap = AddMonoidHom.id G)
    (hrankClass : r.comp classMap = AddMonoidHom.snd A ℤ) :
    ∃ e : G ≃+ A × ℤ,
      (AddMonoidHom.snd A ℤ).comp e.toAddMonoidHom = r := by
  have hsnd : (AddMonoidHom.snd A ℤ).comp coordMap = r := by
    -- Transport the class-map rank formula across the right inverse identity.
    apply AddMonoidHom.ext
    intro x
    have hreassemble : classMap (coordMap x) = x := by
      simpa [AddMonoidHom.comp_apply] using (DFunLike.congr_fun hright x)
    calc
      ((AddMonoidHom.snd A ℤ).comp coordMap) x =
          (AddMonoidHom.snd A ℤ) (coordMap x) := rfl
      _ = (r.comp classMap) (coordMap x) := by
        rw [hrankClass]
      _ = r (classMap (coordMap x)) := rfl
      _ = r x := by rw [hreassemble]
  -- The existing two-sided-inverse assembly now supplies the product equivalence.
  exact addEquivRankProductOfTwoSidedInverse r classMap coordMap hleft hright hsnd

/-- Helper for Chap10 Example 10 55 5: a product equivalence with the prescribed rank projection
supplies explicit inverse class and coordinate homomorphisms. -/
theorem rankProductDataOfAddEquiv
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (e : G ≃+ A × ℤ)
    (he : (AddMonoidHom.snd A ℤ).comp e.toAddMonoidHom = r) :
    ∃ (classMap : A × ℤ →+ G) (coordMap : G →+ A × ℤ),
      coordMap.comp classMap = AddMonoidHom.id (A × ℤ) ∧
        classMap.comp coordMap = AddMonoidHom.id G ∧
        r.comp classMap = AddMonoidHom.snd A ℤ := by
  refine ⟨e.symm.toAddMonoidHom, e.toAddMonoidHom, ?_, ?_, ?_⟩
  · -- The coordinate map followed by the inverse class map is the identity on product data.
    apply AddMonoidHom.ext
    intro p
    simp
  · -- Conversely, reassembling the coordinates of an element gives that element back.
    apply AddMonoidHom.ext
    intro g
    simp
  · -- Pull the rank-projection identity through the inverse equivalence.
    apply AddMonoidHom.ext
    intro p
    simpa [AddMonoidHom.comp_apply] using (DFunLike.congr_fun he (e.symm p)).symm

/-- Helper for Chap10 Example 10 55 5: a rank-kernel equivalence and a rank section already
produce the explicit product-data homomorphisms. -/
theorem rankProductDataOfRankKernelEquiv
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (s : ℤ →+ G)
    (hright : r.comp s = AddMonoidHom.id ℤ)
    (eker : A ≃+ r.ker) :
    ∃ (classMap : A × ℤ →+ G) (coordMap : G →+ A × ℤ),
      coordMap.comp classMap = AddMonoidHom.id (A × ℤ) ∧
        classMap.comp coordMap = AddMonoidHom.id G ∧
        r.comp classMap = AddMonoidHom.snd A ℤ := by
  -- First split the group by rank and its kernel, then read off the inverse homomorphisms.
  rcases addEquivProductOfRankSplit r s hright eker with ⟨e, he⟩
  exact rankProductDataOfAddEquiv r e he

/-- Helper for Chap10 Example 10 55 5: two additive homomorphisms with two-sided inverse
identities assemble an equivalence with a rank-kernel target. -/
theorem rankKernelEquivOfInverseHoms
    {G : Type w} {A : Type v} [AddCommGroup G] [AddCommGroup A]
    (r : G →+ ℤ) (boundary : A →+ r.ker) (coord : r.ker →+ A)
    (hleft : coord.comp boundary = AddMonoidHom.id A)
    (hright : boundary.comp coord = AddMonoidHom.id r.ker) :
    Nonempty (A ≃+ r.ker) := by
  have hboundary_injective : Function.Injective boundary := by
    intro x y hxy
    have hx : coord (boundary x) = x := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft x
    have hy : coord (boundary y) = y := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft y
    -- Apply the coordinate map to an equality of boundary values, then use the left inverse.
    calc
      x = coord (boundary x) := hx.symm
      _ = coord (boundary y) := by rw [hxy]
      _ = y := hy
  have hboundary_surjective : Function.Surjective boundary := by
    intro z
    -- Every kernel element is the boundary of its coordinate by the right inverse.
    refine ⟨coord z, ?_⟩
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright z
  -- The boundary homomorphism is bijective, so mathlib turns it into an additive equivalence.
  exact ⟨AddEquiv.ofBijective boundary ⟨hboundary_injective, hboundary_surjective⟩⟩
