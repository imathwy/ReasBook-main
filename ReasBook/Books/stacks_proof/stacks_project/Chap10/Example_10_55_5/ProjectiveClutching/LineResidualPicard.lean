import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.SL2StableProduct

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the unit-ratio residual class lies in the projective-rank
kernel. -/
theorem equalEndpointLineSubmodule_one_residualClass_mem_rankKer :
    projectiveGrothendieckGroupOf R (equalEndpointLineSubmodule_oneProjectiveModule k) -
      equalEndpointProjectiveFreeClass k ∈
        (equalEndpointProjectiveRankMap.{u, u} k).ker := by
  -- The residual class is already zero, hence it is certainly killed by the rank map.
  rw [equalEndpointLineSubmodule_one_residualClass_eq_zero]
  exact AddSubgroup.zero_mem _

/-- Helper for Chap10 Example 10 55 5: the general ratio-one line projective module is
isomorphic to the free rank-one projective module. -/
noncomputable def equalEndpointLineProjectiveModule_oneIso :
    equalEndpointProjectiveFreeModule k ≅ equalEndpointLineProjectiveModule k 1 :=
  CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
    (equalEndpointLineSubmodule_one_linearEquiv k).toModuleIso

/-- Helper for Chap10 Example 10 55 5: the general Milnor-line package at ratio `1` represents
the free rank-one projective class. -/
theorem equalEndpointLineProjectiveModule_one_class_eq_freeClass :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k 1) =
      equalEndpointProjectiveFreeClass k := by
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    -- The zero module supplies the base object required by the `K₀` isomorphism relation.
    exact ⟨inferInstance, inferInstance⟩
  have h :
      ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
        (equalEndpointProjectiveFreeModule k) =
      ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
        (equalEndpointLineProjectiveModule k 1) := by
    -- Transport the class through the explicit isomorphism `R ≃ I_1`.
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
      (equalEndpointProjectiveFreeModule k)
      (equalEndpointLineProjectiveModule k 1)
      (equalEndpointLineProjectiveModule_oneIso k))
  simpa [projectiveGrothendieckGroupOf, equalEndpointProjectiveFreeClass,
    equalEndpointProjectiveFreeModule, equalEndpointLineProjectiveModule] using h.symm

/-- Helper for Chap10 Example 10 55 5: every Milnor-line residual class has projective generic
rank zero. -/
theorem equalEndpointLineProjectiveModule_residualClass_mem_rankKer (unitRatio : kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k unitRatio) -
      equalEndpointProjectiveFreeClass k ∈
        (equalEndpointProjectiveRankMap.{u, u} k).ker := by
  -- The line projective module and the free module both have generic rank one, so their
  -- difference is killed by the projective-rank map.
  rw [AddMonoidHom.mem_ker]
  rw [map_sub, equalEndpointProjectiveRankMap_apply_of,
    equalEndpointLineProjectiveModule_rank, equalEndpointProjectiveRankMap_freeClass]
  norm_num

/-- Helper for Chap10 Example 10 55 5: the residual projective class attached to an endpoint
unit, viewed as an element of the projective-rank kernel. -/
noncomputable def equalEndpointLineResidualClass (unitRatio : kˣ) :
    (equalEndpointProjectiveRankMap.{u, u} k).ker :=
  ⟨projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k unitRatio) -
      equalEndpointProjectiveFreeClass k,
    equalEndpointLineProjectiveModule_residualClass_mem_rankKer k unitRatio⟩

/-- Helper for Chap10 Example 10 55 5: the residual class has the expected underlying
projective `K₀` element. -/
theorem equalEndpointLineResidualClass_val (unitRatio : kˣ) :
    (equalEndpointLineResidualClass k unitRatio :
      projectiveGrothendieckGroup.{u, u} R) =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k unitRatio) -
        equalEndpointProjectiveFreeClass k := rfl

/-- Helper for Chap10 Example 10 55 5: a stable direct-sum class equality for Milnor lines
implies the residual product law in the projective-rank kernel. -/
theorem equalEndpointLineResidualClass_mul_of_projective_sum
    (u v : kˣ)
    (hstable :
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
          equalEndpointProjectiveFreeClass k =
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
          projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v)) :
    equalEndpointLineResidualClass k (u * v) =
      equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v := by
  let A := projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v))
  let B := projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u)
  let C := projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v)
  let F := equalEndpointProjectiveFreeClass k
  have hA : A = B + C - F := by
    -- Solve the group algebra once, turning the stable direct-sum equality into a normal form for
    -- the product-ratio line class.
    calc
      A = A + F - F := by abel
      _ = B + C - F := by rw [hstable]
  apply Subtype.ext
  -- After forgetting the kernel subtype, the residual equality is ordinary abelian-group
  -- arithmetic in `K₀`.
  change A - F = (B - F) + (C - F)
  rw [hA]
  abel

/-- Helper for Chap10 Example 10 55 5: a stable direct-sum linear equivalence gives the residual
product law for the corresponding Milnor lines. -/
theorem equalEndpointLineResidualClass_mul_of_linearEquiv
    (u v : kˣ)
    (e :
      ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          (equalEndpointProjectiveFreeModule k).obj) ≃ₗ[R]
        ((equalEndpointLineProjectiveModule k u).obj ×
          (equalEndpointLineProjectiveModule k v).obj)) :
    equalEndpointLineResidualClass k (u * v) =
      equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v := by
  -- First turn the stable module isomorphism into the K0 stable-sum equality, then consume the
  -- already-proved residual-class algebra bridge.
  exact equalEndpointLineResidualClass_mul_of_projective_sum (k := k) u v
    (equalEndpointLineProjectiveModule_sum_mul_class_of_linearEquiv (k := k) u v e)

/-- Helper for Chap10 Example 10 55 5: a nonempty stable product comparison gives the
projective `K₀` stable-sum equality for Milnor lines. -/
theorem equalEndpointLineProjectiveModule_sum_mul_class_of_nonempty_linearEquiv
    (u v : kˣ)
    (hlinear : Nonempty (equalEndpointLineStableProductLinearEquiv k u v)) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v) := by
  -- Choose the stable comparison and hand it to the already-proved K0 transport adapter.
  rcases hlinear with ⟨e⟩
  exact equalEndpointLineProjectiveModule_sum_mul_class_of_linearEquiv (k := k) u v e

/-- Helper for Chap10 Example 10 55 5: Milnor line projective classes satisfy the stable
product formula for all endpoint-unit ratios. -/
theorem equalEndpointLineProjectiveModule_sum_mul_class_all (u v : kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v) := by
  -- The stable product comparison is now supplied by the explicit SL₂ matrix path.
  exact equalEndpointLineProjectiveModule_sum_mul_class_of_nonempty_linearEquiv (k := k) u v
    (equalEndpointLineStableProductLinearEquiv_all (k := k) u v)

/-- Helper for Chap10 Example 10 55 5: the stable K₀ product formula holds when the left
endpoint-unit ratio is one. -/
theorem equalEndpointLineProjectiveModule_sum_one_mul_class (u : kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (1 * u)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k 1) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) := by
  -- The ratio-one stable product comparison is already explicit; transport it to K₀.
  exact equalEndpointLineProjectiveModule_sum_mul_class_of_nonempty_linearEquiv (k := k) 1 u
    (equalEndpointLineStableProductLinearEquiv_one_left (k := k) u)

/-- Helper for Chap10 Example 10 55 5: the stable K₀ product formula holds when the right
endpoint-unit ratio is one. -/
theorem equalEndpointLineProjectiveModule_sum_mul_one_class (u : kˣ) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * 1)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k 1) := by
  -- The ratio-one stable product comparison is already explicit; transport it to K₀.
  exact equalEndpointLineProjectiveModule_sum_mul_class_of_nonempty_linearEquiv (k := k) u 1
    (equalEndpointLineStableProductLinearEquiv_one_right (k := k) u)

/-- Helper for Chap10 Example 10 55 5: a nonempty stable product comparison gives the residual
product law for Milnor line classes. -/
theorem equalEndpointLineResidualClass_mul_of_nonempty_linearEquiv
    (u v : kˣ)
    (hlinear : Nonempty (equalEndpointLineStableProductLinearEquiv k u v)) :
    equalEndpointLineResidualClass k (u * v) =
      equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v := by
  -- The residual product law follows by transporting the chosen stable linear equivalence through
  -- the K0 class adapter.
  rcases hlinear with ⟨e⟩
  exact equalEndpointLineResidualClass_mul_of_linearEquiv (k := k) u v e

/-- Helper for Chap10 Example 10 55 5: residual Milnor-line classes are multiplicative for all
endpoint-unit ratios. -/
theorem equalEndpointLineResidualClass_mul (u v : kˣ) :
    equalEndpointLineResidualClass k (u * v) =
      equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v := by
  -- Transport the all-ratio stable product comparison through the residual-class adapter.
  exact equalEndpointLineResidualClass_mul_of_nonempty_linearEquiv (k := k) u v
    (equalEndpointLineStableProductLinearEquiv_all (k := k) u v)

/-- Helper for Chap10 Example 10 55 5: stable product comparisons plus residual exactness supply
the residual class package used by the boundary-data construction. -/
theorem equalEndpointLineResidualClasses_of_linearEquiv
    (hlinear : ∀ u v : kˣ,
      Nonempty (equalEndpointLineStableProductLinearEquiv k u v))
    (hinj : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ _hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v,
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Produce the product law pointwise from the stable comparison family, then preserve the two
  -- class-level exactness hypotheses for the residual homomorphism bridge.
  refine ⟨?_, hinj, hsurj⟩
  intro u v
  exact equalEndpointLineResidualClass_mul_of_nonempty_linearEquiv (k := k) u v (hlinear u v)

/-- Helper for Chap10 Example 10 55 5: a determinant coordinate inverse gives residual
injectivity and rank-kernel surjectivity for Milnor line classes. -/
theorem equalEndpointLineResidualClasses_of_linearEquiv_and_coordInverse
    (hlinear : ∀ u v : kˣ,
      Nonempty (equalEndpointLineStableProductLinearEquiv k u v))
    (coord : (equalEndpointProjectiveRankMap.{u, u} k).ker →+ Additive kˣ)
    (hcoord_line : ∀ unitRatio : kˣ,
      coord (equalEndpointLineResidualClass k unitRatio) = Additive.ofMul unitRatio)
    (hline_coord : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      equalEndpointLineResidualClass k (coord z).toMul = z) :
    ∃ _hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v,
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- The coordinate recovers each endpoint unit from its residual line class, so it proves
  -- injectivity; its inverse formula gives the rank-kernel normal form.
  refine equalEndpointLineResidualClasses_of_linearEquiv (k := k) hlinear ?_ ?_
  · intro u v huv
    have htag : Additive.ofMul u = Additive.ofMul v := by
      calc
        Additive.ofMul u = coord (equalEndpointLineResidualClass k u) := by
          exact (hcoord_line u).symm
        _ = coord (equalEndpointLineResidualClass k v) := by
          rw [huv]
        _ = Additive.ofMul v := hcoord_line v
    simpa using congrArg Additive.toMul htag
  · intro z
    exact ⟨(coord z).toMul, hline_coord z⟩

/-- Helper for Chap10 Example 10 55 5: stable direct-sum equalities for Milnor lines turn
into the residual-class product law, leaving only class-level exactness as input. -/
theorem equalEndpointLineResidualClasses_of_projective_sum
    (hstable : ∀ u v : kˣ,
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
          equalEndpointProjectiveFreeClass k =
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
          projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v))
    (hinj : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)
    (hsurj : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ _hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v,
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Use the stable K0 equality pointwise to produce the product law, then carry the exactness
  -- hypotheses through unchanged for the residual homomorphism bridge.
  refine ⟨?_, hinj, hsurj⟩
  intro u v
  exact equalEndpointLineResidualClass_mul_of_projective_sum (k := k) u v (hstable u v)

/-- Helper for Chap10 Example 10 55 5: the residual class for the ratio-one line is zero. -/
theorem equalEndpointLineResidualClass_one :
    equalEndpointLineResidualClass k 1 = 0 := by
  -- The underlying projective class is the free class, so the residual kernel element is zero.
  apply Subtype.ext
  rw [equalEndpointLineResidualClass_val, equalEndpointLineProjectiveModule_one_class_eq_freeClass,
    sub_self]
  rfl

/-- Helper for Chap10 Example 10 55 5: the residual product law is already true when the right
endpoint-unit ratio is `1`. -/
theorem equalEndpointLineResidualClass_mul_one (unitRatio : kˣ) :
    equalEndpointLineResidualClass k (unitRatio * 1) =
      equalEndpointLineResidualClass k unitRatio + equalEndpointLineResidualClass k 1 := by
  -- The ratio-one residual class vanishes, so this is the right-unit case of additivity.
  rw [mul_one, equalEndpointLineResidualClass_one, add_zero]

/-- Helper for Chap10 Example 10 55 5: the residual product law is already true when the left
endpoint-unit ratio is `1`. -/
theorem equalEndpointLineResidualClass_one_mul (unitRatio : kˣ) :
    equalEndpointLineResidualClass k (1 * unitRatio) =
      equalEndpointLineResidualClass k 1 + equalEndpointLineResidualClass k unitRatio := by
  -- The ratio-one residual class vanishes, so this is the left-unit case of additivity.
  rw [one_mul, equalEndpointLineResidualClass_one, zero_add]

/-- Helper for Chap10 Example 10 55 5: a residual product law makes inverse-ratio residual
classes additive inverses. -/
theorem equalEndpointLineResidualClass_inv_of_mul
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    (unitRatio : kˣ) :
    equalEndpointLineResidualClass k unitRatio⁻¹ =
      -equalEndpointLineResidualClass k unitRatio := by
  -- Evaluate the product law at `u * u⁻¹ = 1`; the ratio-one residual class is zero.
  have hsum :
      equalEndpointLineResidualClass k unitRatio +
        equalEndpointLineResidualClass k unitRatio⁻¹ = 0 := by
    have h := hmul unitRatio unitRatio⁻¹
    rw [mul_inv_cancel, equalEndpointLineResidualClass_one] at h
    exact h.symm
  exact eq_neg_of_add_eq_zero_right hsum

/-- Helper for Chap10 Example 10 55 5: the residual class assignment sends additive zero of
endpoint-unit ratios to zero in the projective-rank kernel. -/
theorem equalEndpointLineResidualClass_toAdditive_map_zero :
    equalEndpointLineResidualClass k (0 : Additive kˣ).toMul = 0 := by
  -- Additive zero is the multiplicative unit, where the residual class was already computed.
  simpa using equalEndpointLineResidualClass_one k

/-- Helper for Chap10 Example 10 55 5: a multiplicative product law for residual line classes
is exactly additivity after passing to `Additive kˣ`. -/
theorem equalEndpointLineResidualClass_toAdditive_map_add
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    (x y : Additive kˣ) :
    equalEndpointLineResidualClass k (x + y).toMul =
      equalEndpointLineResidualClass k x.toMul + equalEndpointLineResidualClass k y.toMul := by
  -- The `Additive` tag changes addition into multiplication, so the assumed line-product law
  -- is the required additivity statement.
  simpa using hmul x.toMul y.toMul

/-- Helper for Chap10 Example 10 55 5: once residual Milnor-line classes satisfy the product
law, they define an additive homomorphism from endpoint-unit ratios to the rank kernel. -/
noncomputable def equalEndpointLineResidualHom
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v) :
    Additive kˣ →+ (equalEndpointProjectiveRankMap.{u, u} k).ker :=
  { toFun := fun x => equalEndpointLineResidualClass k x.toMul
    map_zero' := equalEndpointLineResidualClass_toAdditive_map_zero k
    map_add' := equalEndpointLineResidualClass_toAdditive_map_add k hmul }

/-- Helper for Chap10 Example 10 55 5: the residual homomorphism evaluates by forgetting the
`Additive` type tag on endpoint units. -/
theorem equalEndpointLineResidualHom_apply
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v)
    (unitRatio : Additive kˣ) :
    equalEndpointLineResidualHom (k := k) (hmul := hmul) unitRatio =
      equalEndpointLineResidualClass k unitRatio.toMul := by
  -- This names the defining computation so injectivity and surjectivity can be stated without
  -- repeatedly unfolding the homomorphism.
  rfl

/-- Helper for Chap10 Example 10 55 5: injectivity of the residual homomorphism is exactly
injectivity of residual classes on endpoint-unit ratios. -/
theorem equalEndpointLineResidualHom_injective_iff
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v) :
    Function.Injective (equalEndpointLineResidualHom (k := k) (hmul := hmul)) ↔
      ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  constructor
  · intro hinj u v huv
    -- Apply hom-injectivity to the corresponding additive endpoint-unit tags.
    have htag :
        (Additive.ofMul u : Additive kˣ) = Additive.ofMul v := by
      exact hinj huv
    simpa using congrArg Additive.toMul htag
  · intro hclass x y hxy
    -- Conversely, class-level injectivity recovers equality after removing the additive tags.
    have hmulEq : x.toMul = y.toMul :=
      hclass x.toMul y.toMul hxy
    cases x
    cases y
    simpa using hmulEq

/-- Helper for Chap10 Example 10 55 5: surjectivity of the residual homomorphism is exactly
the statement that every rank-kernel class is represented by a Milnor-line residual class. -/
theorem equalEndpointLineResidualHom_surjective_iff
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v) :
    Function.Surjective (equalEndpointLineResidualHom (k := k) (hmul := hmul)) ↔
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  constructor
  · intro hsurj z
    -- A preimage in `Additive kˣ` gives the same representative after forgetting the tag.
    rcases hsurj z with ⟨unitRatio, hunitRatio⟩
    exact ⟨unitRatio.toMul, hunitRatio⟩
  · intro hclasses z
    -- A residual representative becomes a preimage after adding the `Additive` tag.
    rcases hclasses z with ⟨unitRatio, hunitRatio⟩
    refine ⟨Additive.ofMul unitRatio, ?_⟩
    exact hunitRatio

/-- Helper for Chap10 Example 10 55 5: bijectivity of the residual homomorphism is equivalent
to the class-level Milnor-line injectivity and rank-kernel normal-form statements. -/
theorem equalEndpointLineResidualHom_bijective_iff
    (hmul : ∀ u v : kˣ,
      equalEndpointLineResidualClass k (u * v) =
        equalEndpointLineResidualClass k u + equalEndpointLineResidualClass k v) :
    Function.Bijective (equalEndpointLineResidualHom (k := k) (hmul := hmul)) ↔
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Split bijectivity into injectivity and surjectivity, then use the two class-level bridges.
  constructor
  · intro hbijective
    exact ⟨
      (equalEndpointLineResidualHom_injective_iff (k := k) hmul).mp hbijective.1,
      (equalEndpointLineResidualHom_surjective_iff (k := k) hmul).mp hbijective.2⟩
  · intro hclasses
    exact ⟨
      (equalEndpointLineResidualHom_injective_iff (k := k) hmul).mpr hclasses.1,
      (equalEndpointLineResidualHom_surjective_iff (k := k) hmul).mpr hclasses.2⟩

/-- Helper for Chap10 Example 10 55 5: the Picard class of the invertible Milnor line attached
to an endpoint-unit ratio. -/
noncomputable def equalEndpointLinePicClass (unitRatio : kˣ) : CommRing.Pic R :=
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)
    (equalEndpointLineSubmoduleUnit k unitRatio)

/-- Helper for Chap10 Example 10 55 5: endpoint-unit ratios map multiplicatively to Picard
classes of their Milnor line submodules. -/
noncomputable def equalEndpointLinePicHom :
    kˣ →* CommRing.Pic R :=
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  (Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)).comp
    (equalEndpointLineSubmoduleUnitHom k)

/-- Helper for Chap10 Example 10 55 5: the Picard homomorphism evaluates to the corresponding
Milnor-line Picard class. -/
theorem equalEndpointLinePicHom_apply (unitRatio : kˣ) :
    equalEndpointLinePicHom k unitRatio =
      equalEndpointLinePicClass k unitRatio := by
  -- Both sides are the same `unitsToPic` image; this lemma names that normal form for later
  -- Picard exactness calculations.
  rfl

/-- Helper for Chap10 Example 10 55 5: a Milnor line unit is principal exactly when its Picard
class is trivial. -/
theorem equalEndpointLineSubmoduleUnit_principal_iff_picClass_eq_one (unitRatio : kˣ) :
    equalEndpointLineSubmoduleUnit k unitRatio ∈
        (Units.map (Submodule.spanSingleton R).toMonoidHom).range ↔
      equalEndpointLinePicClass k unitRatio = 1 := by
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  -- Mathlib's exactness theorem identifies principal invertible submodules with the kernel of
  -- `unitsToPic`; the Picard class definition is exactly this homomorphism applied to `I_u`.
  rw [← Submodule.ker_unitsToPic R (equalEndpointPolynomialMulModule k)]
  rfl

/-- Helper for Chap10 Example 10 55 5: the unit-ratio Milnor line has trivial Picard class. -/
theorem equalEndpointLinePicClass_one :
    equalEndpointLinePicClass k 1 = 1 := by
  -- The line-unit map and `unitsToPic` are monoid homomorphisms, so the ratio-one class is
  -- the Picard identity.
  rw [← equalEndpointLinePicHom_apply]
  exact map_one (equalEndpointLinePicHom k)


end
