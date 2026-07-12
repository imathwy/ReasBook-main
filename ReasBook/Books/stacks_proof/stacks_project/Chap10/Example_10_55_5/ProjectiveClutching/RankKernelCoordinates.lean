import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.LineRankClassMap

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: determinant-coordinate data for the projective
rank kernel, inverse to residual Milnor-line classes. -/
structure EqualEndpointRankKernelCoordinateData where
  coord : (equalEndpointProjectiveRankMap.{u, u} k).ker →+ Additive kˣ
  coord_line : ∀ unitRatio : kˣ,
    coord (equalEndpointLineResidualClass k unitRatio) = Additive.ofMul unitRatio
  line_coord : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
    equalEndpointLineResidualClass k (coord z).toMul = z

/-- Helper for Chap10 Example 10 55 5: restrict a projective determinant coordinate to the
projective-rank kernel. -/
noncomputable def equalEndpointRankKernelDetCoord
    (det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ) :
    (equalEndpointProjectiveRankMap.{u, u} k).ker →+ Additive kˣ where
  toFun := fun z => det z.1
  map_zero' := det.map_zero
  map_add' := fun x y => det.map_add x.1 y.1

/-- Helper for Chap10 Example 10 55 5: a determinant coordinate that computes on residual
Milnor lines and is jointly injective with rank supplies the rank-kernel coordinate data. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_detRank
    (det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ)
    (hline : ∀ unitRatio : kˣ,
      det (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio)
    (hinj : Function.Injective
      (fun x : projectiveGrothendieckGroup.{u, u} R =>
        (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Restrict the determinant coordinate to rank-zero classes and use joint injectivity to prove
  -- that every rank-kernel class is the residual line with the same determinant coordinate.
  let coord := equalEndpointRankKernelDetCoord (k := k) det
  refine ⟨
    { coord := coord
      coord_line := ?_
      line_coord := ?_ }⟩
  · intro unitRatio
    exact hline unitRatio
  · intro z
    apply Subtype.ext
    apply hinj
    -- The determinant coordinates agree by the residual-line computation, and the rank
    -- coordinates agree because both classes lie in the rank kernel.
    have hdet :
        det (equalEndpointLineResidualClass k (coord z).toMul :
          projectiveGrothendieckGroup.{u, u} R) = det z.1 := by
      calc
        det (equalEndpointLineResidualClass k (coord z).toMul :
            projectiveGrothendieckGroup.{u, u} R) =
            Additive.ofMul (coord z).toMul := hline (coord z).toMul
        _ = coord z := by
          cases coord z
          rfl
        _ = det z.1 := rfl
    have hrank :
        equalEndpointProjectiveRankMap.{u, u} k
            (equalEndpointLineResidualClass k (coord z).toMul :
              projectiveGrothendieckGroup.{u, u} R) =
          equalEndpointProjectiveRankMap.{u, u} k z.1 := by
      calc
        equalEndpointProjectiveRankMap.{u, u} k
            (equalEndpointLineResidualClass k (coord z).toMul :
              projectiveGrothendieckGroup.{u, u} R) = 0 :=
          (equalEndpointLineResidualClass k (coord z).toMul).2
        _ = equalEndpointProjectiveRankMap.{u, u} k z.1 := z.2.symm
    exact Prod.ext hdet hrank

/-- Helper for Chap10 Example 10 55 5: an existential determinant-rank package supplies
coordinate data on the projective-rank kernel. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_detRankExists
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Unpack the determinant coordinate and pass it to the pointwise coordinate-data bridge.
  rcases hdetRank with ⟨det, hline, hinj⟩
  exact equalEndpointRankKernelCoordinateData_nonempty_of_detRank k det hline hinj

/-- Helper for Chap10 Example 10 55 5: a normalized product equivalence gives the
determinant-rank coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_rankProductEquiv
    (e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ)
    (hrank : (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
      equalEndpointProjectiveRankMap.{u, u} k)
    (hline : ∀ unitRatio : kˣ,
      e (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) =
          (Additive.ofMul unitRatio, 0)) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- The determinant is the first coordinate of the normalized product equivalence.
  let det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ :=
    (AddMonoidHom.fst (Additive kˣ) ℤ).comp e.toAddMonoidHom
  refine ⟨det, ?_, ?_⟩
  · intro unitRatio
    -- The line normalization reads off exactly the first product coordinate.
    simpa [det, AddMonoidHom.comp_apply] using congrArg Prod.fst (hline unitRatio)
  · intro x y hxy
    -- Equality of determinant and rank is equality of both coordinates of `e`.
    apply e.injective
    apply Prod.ext
    · simpa [det, AddMonoidHom.comp_apply] using congrArg Prod.fst hxy
    · have hrankxy :
          equalEndpointProjectiveRankMap.{u, u} k x =
            equalEndpointProjectiveRankMap.{u, u} k y :=
        congrArg Prod.snd hxy
      have hxrank :
          (e x).2 = equalEndpointProjectiveRankMap.{u, u} k x := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hrank x
      have hyrank :
          (e y).2 = equalEndpointProjectiveRankMap.{u, u} k y := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hrank y
      calc
        (e x).2 = equalEndpointProjectiveRankMap.{u, u} k x := hxrank
        _ = equalEndpointProjectiveRankMap.{u, u} k y := hrankxy
        _ = (e y).2 := hyrank.symm

/-- Helper for Chap10 Example 10 55 5: explicit product-coordinate maps whose class map sends
endpoint-unit generators to residual Milnor-line classes supply the determinant-rank data. -/
theorem equalEndpointProjectiveDetRankData_exists_of_productData
    (classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R)
    (coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ)
    (hleft : coordMap.comp classMap = AddMonoidHom.id (Additive kˣ × ℤ))
    (hright : classMap.comp coordMap = AddMonoidHom.id (projectiveGrothendieckGroup.{u, u} R))
    (hrankClass : (equalEndpointProjectiveRankMap.{u, u} k).comp classMap =
      AddMonoidHom.snd (Additive kˣ) ℤ)
    (hline : ∀ unitRatio : kˣ,
      classMap (Additive.ofMul unitRatio, 0) =
        (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R)) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Take the determinant coordinate to be the first coordinate of the explicit product map.
  let det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ :=
    (AddMonoidHom.fst (Additive kˣ) ℤ).comp coordMap
  have hsnd : (AddMonoidHom.snd (Additive kˣ) ℤ).comp coordMap =
      equalEndpointProjectiveRankMap.{u, u} k := by
    -- The right inverse reassembles an element from its product coordinates; applying rank and
    -- the class-map rank formula identifies the second coordinate with generic rank.
    apply AddMonoidHom.ext
    intro x
    have hreassemble : classMap (coordMap x) = x := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright x
    calc
      ((AddMonoidHom.snd (Additive kˣ) ℤ).comp coordMap) x =
          (AddMonoidHom.snd (Additive kˣ) ℤ) (coordMap x) := rfl
      _ = ((equalEndpointProjectiveRankMap.{u, u} k).comp classMap) (coordMap x) := by
        rw [hrankClass]
      _ = equalEndpointProjectiveRankMap.{u, u} k (classMap (coordMap x)) := rfl
      _ = equalEndpointProjectiveRankMap.{u, u} k x := by rw [hreassemble]
  refine ⟨det, ?_, ?_⟩
  · intro unitRatio
    -- The left inverse reads the first product coordinate of the residual-line generator.
    have hcoord := DFunLike.congr_fun hleft (Additive.ofMul unitRatio, (0 : ℤ))
    calc
      det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) =
          det (classMap (Additive.ofMul unitRatio, 0)) := by
        rw [hline]
      _ = (coordMap (classMap (Additive.ofMul unitRatio, 0))).1 := rfl
      _ = Additive.ofMul unitRatio := by
        simpa [AddMonoidHom.comp_apply] using congrArg Prod.fst hcoord
  · intro x y hxy
    -- Joint equality of determinant and rank is equality of both product coordinates.
    have hxy' : (det x, equalEndpointProjectiveRankMap.{u, u} k x) =
        (det y, equalEndpointProjectiveRankMap.{u, u} k y) := by
      simpa using hxy
    have hdetxy : det x = det y := (Prod.ext_iff.mp hxy').1
    have hrankxy : equalEndpointProjectiveRankMap.{u, u} k x =
        equalEndpointProjectiveRankMap.{u, u} k y := (Prod.ext_iff.mp hxy').2
    have hfirst : (coordMap x).1 = (coordMap y).1 := by
      simpa [det, AddMonoidHom.comp_apply] using hdetxy
    have hsecond : (coordMap x).2 = (coordMap y).2 := by
      have hxrank : (coordMap x).2 = equalEndpointProjectiveRankMap.{u, u} k x := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hsnd x
      have hyrank : (coordMap y).2 = equalEndpointProjectiveRankMap.{u, u} k y := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hsnd y
      calc
        (coordMap x).2 = equalEndpointProjectiveRankMap.{u, u} k x := hxrank
        _ = equalEndpointProjectiveRankMap.{u, u} k y := hrankxy
        _ = (coordMap y).2 := hyrank.symm
    have hcoord : coordMap x = coordMap y := Prod.ext hfirst hsecond
    calc
      x = classMap (coordMap x) := by
        simpa [AddMonoidHom.comp_apply] using (DFunLike.congr_fun hright x).symm
      _ = classMap (coordMap y) := by rw [hcoord]
      _ = y := by
        simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright y

/-- Helper for Chap10 Example 10 55 5: determinant-rank data reconstructs explicit product
coordinate maps with the residual Milnor-line normalization. -/
theorem equalEndpointProjectiveRankProductData_exists_of_detRank
    (det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ)
    (hline : ∀ unitRatio : kˣ,
      det (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio)
    (hinj : Function.Injective
      (fun x : projectiveGrothendieckGroup.{u, u} R =>
        (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    ∃ (classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R)
      (coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ),
      coordMap.comp classMap = AddMonoidHom.id (Additive kˣ × ℤ) ∧
        classMap.comp coordMap = AddMonoidHom.id (projectiveGrothendieckGroup.{u, u} R) ∧
        (equalEndpointProjectiveRankMap.{u, u} k).comp classMap =
          AddMonoidHom.snd (Additive kˣ) ℤ ∧
        ∀ unitRatio : kˣ,
          classMap (Additive.ofMul unitRatio, 0) =
            (equalEndpointLineResidualClass k unitRatio :
              projectiveGrothendieckGroup.{u, u} R) := by
  -- Build the line part from the already-proved residual product law, then subtract the
  -- determinant of the rank-section part so the first coordinate is exactly the requested unit.
  let rank := equalEndpointProjectiveRankMap.{u, u} k
  let rankSection := equalEndpointProjectiveRankSection k
  let residualKernel :=
    equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k)
  let residualToK0 : Additive kˣ →+ projectiveGrothendieckGroup.{u, u} R :=
    rank.ker.subtype.comp residualKernel
  let fstHom := AddMonoidHom.fst (Additive kˣ) ℤ
  let sndHom := AddMonoidHom.snd (Additive kˣ) ℤ
  let rankPart : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
    rankSection.comp sndHom
  let linePart : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
    residualToK0.comp fstHom
  let correction : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
    residualToK0.comp (det.comp rankPart)
  let classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
    linePart - correction + rankPart
  let coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ :=
    det.prod rank
  have hdet_line (unitRatio : Additive kˣ) :
      det (residualToK0 unitRatio) = unitRatio := by
    -- The determinant coordinate is normalized on residual Milnor lines.
    calc
      det (residualToK0 unitRatio) =
          det (equalEndpointLineResidualClass k unitRatio.toMul :
            projectiveGrothendieckGroup.{u, u} R) := by
        rfl
      _ = Additive.ofMul unitRatio.toMul := hline unitRatio.toMul
      _ = unitRatio := by
        cases unitRatio
        rfl
  have hrank_line (unitRatio : Additive kˣ) :
      rank (residualToK0 unitRatio) = 0 := by
    -- Residual Milnor-line classes were defined as elements of the projective-rank kernel.
    exact (residualKernel unitRatio).2
  have hrank_section (n : ℤ) :
      equalEndpointProjectiveRankMap.{u, u} k (rankSection n) = n := by
    -- The free-class section is right-inverse to generic rank.
    simpa [rankSection] using equalEndpointProjectiveRankSection_rank (k := k) n
  refine ⟨classMap, coordMap, ?_, ?_, ?_, ?_⟩
  · -- The determinant and rank coordinates recover the input product coordinate.
    apply AddMonoidHom.ext
    intro p
    rcases p with ⟨unitRatio, n⟩
    apply Prod.ext
    · simp [classMap, coordMap, linePart, correction, rankPart, fstHom, sndHom,
        hdet_line]
    · simpa [classMap, coordMap, linePart, correction, rankPart, fstHom, sndHom, rank,
        hrank_line] using hrank_section n
  · -- Reassembling an element from its determinant and rank coordinates is certified by joint
    -- determinant-rank injectivity.
    apply AddMonoidHom.ext
    intro x
    apply hinj
    apply Prod.ext
    · simp [classMap, coordMap, linePart, correction, rankPart, fstHom, sndHom,
        hdet_line]
    · simpa [classMap, coordMap, linePart, correction, rankPart, fstHom, sndHom, rank,
        hrank_line] using hrank_section (equalEndpointProjectiveRankMap.{u, u} k x)
  · -- The second coordinate of the class map is the generic rank.
    apply AddMonoidHom.ext
    intro p
    rcases p with ⟨unitRatio, n⟩
    simpa [classMap, linePart, correction, rankPart, fstHom, sndHom, rank, hrank_line]
      using hrank_section n
  · intro unitRatio
    -- At integer coordinate zero, the correction and rank-section terms vanish, leaving exactly
    -- the residual Milnor-line class.
    simpa [classMap, linePart, correction, rankPart, fstHom, sndHom, residualToK0,
      residualKernel] using
      equalEndpointLineResidualHom_apply (k := k)
        (hmul := equalEndpointLineResidualClass_mul k) (Additive.ofMul unitRatio)

/-- Helper for Chap10 Example 10 55 5: the determinant coordinate is injective on the
projective rank kernel. -/
theorem equalEndpointRankKernelCoordinateData_coord_injective
    (data : EqualEndpointRankKernelCoordinateData k) :
    Function.Injective data.coord := by
  intro x y hxy
  -- Reconstruct each kernel element from its coordinate and then transport across the
  -- coordinate equality.
  calc
    x = equalEndpointLineResidualClass k (data.coord x).toMul := by
      exact (data.line_coord x).symm
    _ = equalEndpointLineResidualClass k (data.coord y).toMul := by
      rw [hxy]
    _ = y := data.line_coord y

/-- Helper for Chap10 Example 10 55 5: coordinate inverse data makes residual Milnor-line
classes multiplicative. -/
theorem equalEndpointLineResidualClass_mul_of_coordinateData
    (data : EqualEndpointRankKernelCoordinateData k) (u v : kˣ) :
    equalEndpointLineResidualClass k (u * v) =
      equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v := by
  -- The determinant coordinate is injective, so it is enough to compare the two coordinates.
  apply equalEndpointRankKernelCoordinateData_coord_injective (k := k) data
  rw [data.coord_line, map_add, data.coord_line, data.coord_line]
  rfl

/-- Helper for Chap10 Example 10 55 5: coordinate inverse data makes the residual Milnor-line
homomorphism bijective. -/
theorem equalEndpointLineResidualHom_bijective_of_coordinateData
    (data : EqualEndpointRankKernelCoordinateData k) :
    Function.Bijective
      (equalEndpointLineResidualHom (k := k)
        (hmul := equalEndpointLineResidualClass_mul_of_coordinateData k data)) := by
  -- Convert bijectivity to class-level injectivity and rank-kernel normal form, both supplied by
  -- the two coordinate inverse formulas.
  apply (equalEndpointLineResidualHom_bijective_iff (k := k)
    (equalEndpointLineResidualClass_mul_of_coordinateData k data)).mpr
  constructor
  · intro u v huv
    have htag : Additive.ofMul u = Additive.ofMul v := by
      calc
        Additive.ofMul u = data.coord (equalEndpointLineResidualClass k u) := by
          exact (data.coord_line u).symm
        _ = data.coord (equalEndpointLineResidualClass k v) := by
          rw [huv]
        _ = Additive.ofMul v := data.coord_line v
    simpa using congrArg Additive.toMul htag
  · intro z
    refine ⟨(data.coord z).toMul, ?_⟩
    exact data.line_coord z

/-- Helper for Chap10 Example 10 55 5: two-sided inverse homomorphisms whose boundary map is
the residual Milnor-line class package determinant-coordinate data. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_inverseBoundary
    (boundary : Additive kˣ →+ (equalEndpointProjectiveRankMap.{u, u} k).ker)
    (coord : (equalEndpointProjectiveRankMap.{u, u} k).ker →+ Additive kˣ)
    (hboundary : ∀ unitRatio : Additive kˣ,
      boundary unitRatio = equalEndpointLineResidualClass k unitRatio.toMul)
    (hleft : coord.comp boundary = AddMonoidHom.id (Additive kˣ))
    (hright : boundary.comp coord =
      AddMonoidHom.id ((equalEndpointProjectiveRankMap.{u, u} k).ker)) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Package the proposed determinant coordinate, reducing the remaining source task to the two
  -- inverse identities for the explicit residual-boundary homomorphism.
  refine ⟨
    { coord := coord
      coord_line := ?_
      line_coord := ?_ }⟩
  · intro unitRatio
    -- The left inverse identity recovers the endpoint-unit ratio from its residual line class.
    have hboundary_unit :
        boundary (Additive.ofMul unitRatio) = equalEndpointLineResidualClass k unitRatio := by
      simpa using hboundary (Additive.ofMul unitRatio)
    have hleft_unit := DFunLike.congr_fun hleft (Additive.ofMul unitRatio)
    calc
      coord (equalEndpointLineResidualClass k unitRatio) =
          coord (boundary (Additive.ofMul unitRatio)) := by
        rw [← hboundary_unit]
      _ = Additive.ofMul unitRatio := by
        simpa [AddMonoidHom.comp_apply] using hleft_unit
  · intro z
    -- The right inverse identity says every rank-kernel class is represented by the residual
    -- line class of its determinant coordinate.
    have hboundary_coord := hboundary (coord z)
    have hright_z := DFunLike.congr_fun hright z
    calc
      equalEndpointLineResidualClass k (coord z).toMul = boundary (coord z) := by
        rw [hboundary_coord]
      _ = z := by
        simpa [AddMonoidHom.comp_apply] using hright_z

/-- Helper for Chap10 Example 10 55 5: a residual-line equivalence from endpoint-unit ratios
to the rank kernel supplies determinant-coordinate data by taking its inverse. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_lineResidualEquiv
    (e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker)
    (he : ∀ unitRatio : Additive kˣ,
      e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Use the inverse equivalence as the determinant coordinate and verify both inverse formulas
  -- against the assumed residual-line evaluation of the forward map.
  refine ⟨
    { coord := e.symm.toAddMonoidHom
      coord_line := ?_
      line_coord := ?_ }⟩
  · intro unitRatio
    apply e.injective
    calc
      e (e.symm (equalEndpointLineResidualClass k unitRatio)) =
          equalEndpointLineResidualClass k unitRatio := by
        exact e.apply_symm_apply (equalEndpointLineResidualClass k unitRatio)
      _ = e (Additive.ofMul unitRatio) := by
        exact (he (Additive.ofMul unitRatio)).symm
  · intro z
    calc
      equalEndpointLineResidualClass k (e.symm z).toMul = e (e.symm z) := by
        exact (he (e.symm z)).symm
      _ = z := e.apply_symm_apply z

/-- Helper for Chap10 Example 10 55 5: the two Cartan/Picard normal-form clauses construct the
residual-line equivalence with the prescribed forward map. -/
theorem equalEndpointLineResidualEquiv_exists_of_picardCartanClauses
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- The already-proved product law makes residual classes an additive homomorphism; the two
  -- supplied clauses are exactly the injectivity and surjectivity inputs for this homomorphism.
  let residualHom :=
    equalEndpointLineResidualHom (k := k) (hmul := equalEndpointLineResidualClass_mul k)
  have hbijective : Function.Bijective residualHom :=
    equalEndpointLineResidualHom_bijective_of_zeroPicClass_surjective k hzero_pic hsurj
  refine ⟨AddEquiv.ofBijective residualHom hbijective, ?_⟩
  intro unitRatio
  -- The equivalence built from `residualHom` has the residual Milnor-line class as its
  -- underlying forward map.
  exact equalEndpointLineResidualHom_apply (k := k)
    (hmul := equalEndpointLineResidualClass_mul k) unitRatio

/-- Helper for Chap10 Example 10 55 5: determinant-coordinate data also recovers the
residual-line equivalence with the prescribed forward map. -/
theorem equalEndpointLineResidualEquiv_exists_of_coordinateData
    (data : EqualEndpointRankKernelCoordinateData k) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- Coordinate data gives a product law and bijectivity for the residual homomorphism, so the
  -- equivalence can be taken to be that homomorphism with its known bijectivity.
  let residualHom :=
    equalEndpointLineResidualHom (k := k)
      (hmul := equalEndpointLineResidualClass_mul_of_coordinateData k data)
  have hbijective : Function.Bijective residualHom :=
    equalEndpointLineResidualHom_bijective_of_coordinateData k data
  refine ⟨AddEquiv.ofBijective residualHom hbijective, ?_⟩
  intro unitRatio
  -- The forward map is again the named residual-class computation for the homomorphism.
  exact equalEndpointLineResidualHom_apply (k := k)
    (hmul := equalEndpointLineResidualClass_mul_of_coordinateData k data) unitRatio

/-- Helper for Chap10 Example 10 55 5: surjectivity of the Milnor-line Picard homomorphism
packages the endpoint-unit Picard classification as a multiplicative equivalence. -/
theorem equalEndpointLinePicEquiv_exists_of_surjective
    (hsurj : Function.Surjective (equalEndpointLinePicHom k)) :
    ∃ e : kˣ ≃* CommRing.Pic R,
      ∀ unitRatio : kˣ, e unitRatio = equalEndpointLinePicClass k unitRatio := by
  -- Combine the already-proved injectivity with the supplied Picard-class surjectivity.
  let e : kˣ ≃* CommRing.Pic R :=
    MulEquiv.ofBijective (equalEndpointLinePicHom k)
      ⟨equalEndpointLinePicHom_injective k, hsurj⟩
  refine ⟨e, ?_⟩
  intro unitRatio
  -- The equivalence built from the homomorphism has the same forward map.
  simpa [e] using equalEndpointLinePicHom_apply (k := k) unitRatio

/-- Helper for Chap10 Example 10 55 5: composing endpoint-unit Picard classification with a
Picard-to-rank-kernel equivalence gives the normalized residual-line equivalence. -/
theorem equalEndpointLineResidualEquiv_exists_of_picEquivs
    (linePicEquiv : kˣ ≃* CommRing.Pic R)
    (hlinePic : ∀ unitRatio : kˣ,
      linePicEquiv unitRatio = equalEndpointLinePicClass k unitRatio)
    (picKernelEquiv :
      Additive (CommRing.Pic R) ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker)
    (hpicKernel : ∀ unitRatio : kˣ,
      picKernelEquiv (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
        equalEndpointLineResidualClass k unitRatio) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- Convert the multiplicative Picard classification to additive notation once, then compose.
  let linePicAddEquiv : Additive kˣ ≃+ Additive (CommRing.Pic R) :=
    MulEquiv.toAdditive linePicEquiv
  refine ⟨linePicAddEquiv.trans picKernelEquiv, ?_⟩
  intro unitRatio
  have hforward :
      (linePicAddEquiv.trans picKernelEquiv) unitRatio =
        picKernelEquiv (Additive.ofMul (linePicEquiv unitRatio.toMul)) := by
    cases unitRatio
    rfl
  -- The two computation rules identify the composite with the residual Milnor-line class.
  calc
    (linePicAddEquiv.trans picKernelEquiv) unitRatio =
        picKernelEquiv (Additive.ofMul (linePicEquiv unitRatio.toMul)) := hforward
    _ = picKernelEquiv
          (Additive.ofMul (equalEndpointLinePicClass k unitRatio.toMul)) := by
          rw [hlinePic unitRatio.toMul]
    _ = equalEndpointLineResidualClass k unitRatio.toMul :=
          hpicKernel unitRatio.toMul

/-- Helper for Chap10 Example 10 55 5: Picard-homomorphism surjectivity and a Picard comparison
to the projective-rank kernel imply the normalized residual-line equivalence. -/
theorem equalEndpointLineResidualEquiv_exists_of_picHom_surjective_and_picRankKernelEquiv
    (hpicSurj : Function.Surjective (equalEndpointLinePicHom k))
    (hpicKernel :
      ∃ ePic : Additive (CommRing.Pic R) ≃+
          (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∀ unitRatio : kˣ,
          ePic (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
            equalEndpointLineResidualClass k unitRatio) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- First package endpoint-unit Picard classes as an equivalence, then compose with the
  -- Picard-to-rank-kernel equivalence.
  rcases equalEndpointLinePicEquiv_exists_of_surjective k hpicSurj with
    ⟨linePicEquiv, hlinePic⟩
  rcases hpicKernel with ⟨picKernelEquiv, hpicKernelEval⟩
  exact equalEndpointLineResidualEquiv_exists_of_picEquivs k linePicEquiv hlinePic
    picKernelEquiv hpicKernelEval

/-- Helper for Chap10 Example 10 55 5: the two Cartan/Picard normal-form clauses already give
the determinant-coordinate data for residual Milnor-line classes. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_picardCartanClauses
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- First build the residual-line equivalence with its forward-map computation, then take its
  -- inverse as the determinant coordinate.
  rcases equalEndpointLineResidualEquiv_exists_of_picardCartanClauses k hzero_pic hsurj with
    ⟨e, he⟩
  exact equalEndpointRankKernelCoordinateData_nonempty_of_lineResidualEquiv k e he

/-- Helper for Chap10 Example 10 55 5: the Picard/Cartan exactness package supplies the
determinant-coordinate data for residual Milnor-line classes. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_picardCartanExact
    (hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Split the exactness package into its Picard-detection and rank-kernel normal-form clauses,
  -- then use the existing formal construction of the determinant coordinate.
  rcases hexact with ⟨hzero_pic, hsurj⟩
  exact equalEndpointRankKernelCoordinateData_nonempty_of_picardCartanClauses k
    hzero_pic hsurj

/-- Helper for Chap10 Example 10 55 5: bijectivity of the line-plus-rank class map gives
the determinant-rank coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_lineRankClassMap_bijective
    (hbijective : Function.Bijective (equalEndpointLineRankClassMap k)) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- First convert the line-rank bijection into the normalized product equivalence.
  rcases equalEndpointProjectiveRankProduct_exists_of_lineRankClassMap_bijective k hbijective with
    ⟨e, hrank, hline⟩
  -- The first coordinate of that product equivalence is the desired determinant coordinate.
  exact equalEndpointProjectiveDetRankData_exists_of_rankProductEquiv k e hrank hline

/-- Helper for Chap10 Example 10 55 5: bijectivity of the explicit line-plus-rank class map
supplies the determinant-coordinate data for residual Milnor-line classes. -/
theorem equalEndpointRankKernelCoordinateData_nonempty_of_lineRankClassMap_bijective
    (hbijective : Function.Bijective (equalEndpointLineRankClassMap k)) :
    Nonempty (EqualEndpointRankKernelCoordinateData k) := by
  -- Invert the explicit line-rank class map to get the normalized product equivalence, then
  -- consume the previously isolated product-to-determinant formal bridge.
  have hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
    exact equalEndpointProjectiveDetRankData_exists_of_lineRankClassMap_bijective k hbijective
  exact equalEndpointRankKernelCoordinateData_nonempty_of_detRankExists k hdetRank

end
