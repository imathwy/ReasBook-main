import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Definition_7_46_extra_3
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped LieGroup Manifold ContDiff

universe u𝕜 uEG uHG uG uEH uHH uH

-- Semantic recall hit `Manifold.IsSmoothEmbedding`; the source-facing statement remains phrased
-- with the local `ContMDiffMonoidMorphism`, `LieGroupIsomorphism`, and `LieSubgroup` owners.

section LieSubgroupImages

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

/-- Helper for Proposition 7.17: choose the unique preimage of a point in the subgroup range of an
injective Lie-group homomorphism. -/
noncomputable def preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    F.toMonoidHom.range → G :=
  fun y ↦ Classical.choose y.2

/-- Helper for Proposition 7.17: the chosen preimage maps back to the given range point. -/
@[simp] theorem apply_preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    (y : F.toMonoidHom.range) :
    F (preimageInRangeOfInjective F y) = y := by
  -- The choice was made from a witness of `y ∈ range F`, so applying `F` recovers `y`.
  exact Classical.choose_spec y.2

/-- Helper for Proposition 7.17: injectivity forces the chosen preimage of `F x` to be `x`. -/
@[simp] theorem preimageInRangeOfInjective_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) (x : G) :
    preimageInRangeOfInjective F ⟨F x, ⟨x, rfl⟩⟩ = x := by
  -- Compare the ambient `H`-values and then use injectivity of `F`.
  apply hFinj
  simpa using
    apply_preimageInRangeOfInjective F ⟨F x, ⟨x, rfl⟩⟩

/-- Helper for Proposition 7.17: the chosen preimage function is inverse to the canonical map from
`G` to the subgroup range. -/
@[simp] theorem mk_preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : F.toMonoidHom.range) :
    (⟨F (preimageInRangeOfInjective F y),
      ⟨preimageInRangeOfInjective F y, rfl⟩⟩ : F.toMonoidHom.range) = y := by
  -- Equality of subgroup elements is equality of their ambient values.
  apply Subtype.ext
  simpa using apply_preimageInRangeOfInjective F y

/-- Helper for Proposition 7.17: an injective Lie-group homomorphism identifies `G`
multiplicatively with its subgroup range. -/
noncomputable def rangeMulEquivOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    G ≃* F.toMonoidHom.range :=
  { toFun := fun x ↦ ⟨F x, ⟨x, rfl⟩⟩
    invFun := preimageInRangeOfInjective F
    left_inv := preimageInRangeOfInjective_apply F hFinj
    right_inv := mk_preimageInRangeOfInjective F
    map_mul' := fun x y ↦ Subtype.ext <| F.map_mul x y }

/-- Helper for Proposition 7.17: the range equivalence has the expected ambient value. -/
@[simp] theorem rangeMulEquivOfInjective_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) (x : G) :
    ((rangeMulEquivOfInjective F hFinj x : F.toMonoidHom.range) : H) = F x :=
  rfl

/-- Helper for Proposition 7.17: after passing to the subgroup range, the inverse equivalence
still recovers the original ambient point. -/
@[simp] theorem rangeMulEquivOfInjective_symm_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (y : F.toMonoidHom.range) :
    F ((rangeMulEquivOfInjective F hFinj).symm y) = y := by
  -- The inverse of the range equivalence is exactly the chosen preimage function.
  simpa [rangeMulEquivOfInjective] using
    apply_preimageInRangeOfInjective F y

/-- Helper for Proposition 7.17: the subgroup inclusion factors through `F` and the inverse of the
canonical range equivalence. -/
theorem subtype_val_comp_rangeMulEquivOfInjective_symm
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    (Subtype.val : F.toMonoidHom.range → H) = F ∘ (rangeMulEquivOfInjective F hFinj).symm := by
  -- Evaluating both sides at a subgroup point reduces to the chosen-preimage identity above.
  funext y
  simpa [Function.comp] using rangeMulEquivOfInjective_symm_apply F hFinj y

/-- Helper for Proposition 7.17: the set-theoretic range and the subgroup range of a Lie-group
homomorphism have the same ambient points. -/
theorem monoidRange_carrier_eq_setRange
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (F.toMonoidHom.range : Set H) = Set.range F := by
  -- Both predicates say exactly that an ambient point is equal to `F x` for some `x : G`.
  ext y
  rfl

/-- Helper for Proposition 7.17: the ambient image `Set.range F` and the subgroup range
`F.toMonoidHom.range` are canonically equivalent. -/
noncomputable def setRangeEquivMonoidRange
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    Set.range F ≃ F.toMonoidHom.range where
  toFun := fun y ↦ ⟨y.1, y.2⟩
  invFun := fun y ↦ ⟨y.1, y.2⟩
  left_inv := by
    -- Both subtype carriers forget to the same ambient point, so the proofs are propositionally
    -- irrelevant after case splitting.
    intro y
    cases y
    rfl
  right_inv := by
    -- The inverse uses the same ambient point and witness of range membership.
    intro y
    cases y
    rfl

/-- Helper for Proposition 7.17: the canonical equivalence from `Set.range F` to the subgroup
range preserves the ambient value in `H`. -/
@[simp] theorem setRangeEquivMonoidRange_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : Set.range F) :
    ((setRangeEquivMonoidRange F y : F.toMonoidHom.range) : H) = y := by
  rfl

/-- Helper for Proposition 7.17: the inverse of the range-carrier equivalence also preserves the
ambient value in `H`. -/
@[simp] theorem setRangeEquivMonoidRange_symm_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : F.toMonoidHom.range) :
    ((setRangeEquivMonoidRange F).symm y : H) = y := by
  rfl

/-- Helper for Proposition 7.17: after transporting along the canonical equivalence from the image
subset to the subgroup range, the ambient inclusion is still the subtype map. -/
theorem subtype_val_comp_setRangeEquivMonoidRange_symm
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (Subtype.val : F.toMonoidHom.range → H) =
      (Subtype.val : Set.range F → H) ∘ (setRangeEquivMonoidRange F).symm := by
  -- Both sides evaluate to the same ambient point of `H`.
  funext y
  rfl

/-- Helper for Proposition 7.17: a smooth Lie-group homomorphism commutes with left translations. -/
lemma lieGroupHom_comp_leftTranslation_eq_leftTranslation_comp
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    F ∘ leftTranslation (I := I) g = leftTranslation (I := J) (F g) ∘ F := by
  -- Left multiplication commutes with every group homomorphism.
  funext x
  simp [Function.comp, leftTranslation_apply, map_mul]

/-- Helper for Proposition 7.17: injectivity collapses the identity fiber of `F` to the singleton
`{1}`. -/
lemma preimageOne_eq_singleton_of_injective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    F ⁻¹' ({(1 : H)} : Set H) = ({(1 : G)} : Set G) := by
  -- Compare points in the identity fiber with the group identity via injectivity of `F`.
  ext g
  constructor
  · intro hg
    have hFg : F g = F (1 : G) := by
      simpa using hg
    exact hFinj hFg
  · rintro rfl
    simp

/-- Helper for Proposition 7.17: every Lie group is boundaryless, because left translations move a
single interior chart point to any prescribed point. -/
lemma boundarylessManifold_of_lieGroup : BoundarylessManifold I G := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I (1 : G)
  have hz_target : z ∈ (extChartAt I (1 : G)).target := interior_subset hz
  have hz_target_data : z ∈ Set.range I ∧ I.symm z ∈ (chartAt HG (1 : G)).target := by
    simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz_target
  have hz_range : z ∈ Set.range I := hz_target_data.1
  have hz_chart_target : I.symm z ∈ (chartAt HG (1 : G)).target := hz_target_data.2
  let x₀ : G := (chartAt HG (1 : G)).symm (I.symm z)
  have hx₀_source : x₀ ∈ (chartAt HG (1 : G)).source := by
    simpa [x₀] using (chartAt HG (1 : G)).map_target hz_chart_target
  have hx₀_interior : I.IsInteriorPoint x₀ := by
    -- The chosen interior point in the identity chart gives an actual manifold interior point.
    refine
      (show I.IsInteriorPoint x₀ ↔
          extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target from
        @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ EG _ _ HG _ I G _ _ ∞
          inferInstance (chartAt HG (1 : G)) x₀ (by simp) (chart_mem_atlas HG (1 : G))
          hx₀_source).2 ?_
    have hx₀_extChart : extChartAt I (1 : G) x₀ = z := by
      change I ((chartAt HG (1 : G)) ((chartAt HG (1 : G)).symm (I.symm z))) = z
      rw [(chartAt HG (1 : G)).right_inv hz_chart_target]
      exact I.right_inv hz_range
    change extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target
    rw [hx₀_extChart]
    exact hz
  let Φ : G ≃ₘ⟮I, I⟯ G := leftTranslationDiffeomorph (I := I) (x * x₀⁻¹)
  have hΦx : I.IsInteriorPoint (Φ x₀) := by
    -- Diffeomorphisms preserve interior points, so translating the seed point reaches `x`.
    exact ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1 hx₀_interior
  have hΦ_apply : Φ x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    simp [mul_assoc]
  simpa [hΦ_apply] using hΦx

/-- Helper for Proposition 7.17: every point of a Lie group is an interior point for the given
model with corners. -/
lemma lieGroup_isInteriorPoint (x : G) : I.IsInteriorPoint x := by
  -- Reuse the boundaryless-manifold package proved above instead of repeating the translation
  -- argument pointwise.
  let _ : BoundarylessManifold I G := boundarylessManifold_of_lieGroup (I := I) (G := G)
  exact BoundarylessManifold.isInteriorPoint (I := I) (x := x)

/-- Helper for Proposition 7.17: the manifold interior of a Lie group fills the whole carrier. -/
lemma lieGroup_modelInterior_eq_univ : ModelWithCorners.interior (I := I) G = Set.univ := by
  -- Once every point is interior, the model interior set is definitionally all of `G`.
  let _ : BoundarylessManifold I G := boundarylessManifold_of_lieGroup (I := I) (G := G)
  simpa using (ModelWithCorners.interior_eq_univ (I := I) (M := G))

/-- Helper for Proposition 7.17: the only analytic input still missing in this file is the
model-general bridge turning injectivity of a smooth Lie-group homomorphism into an immersion. -/
theorem injectiveLieGroupHomIsImmersion
    [FiniteDimensional 𝕜 EG] [T2Space G] [SecondCountableTopology G]
    [T2Space H] [SecondCountableTopology H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    IsImmersion I J (⊤ : WithTop ℕ∞) F := by
  let _ := hFinj
  -- Route correction: the intended proof now has a clear two-step shape: first prove injectivity
  -- of `mfderiv I J F` at the identity via the singleton-kernel level-set argument, then transport
  -- that injectivity to all points by left translations.
  -- TODO: the old `I`-modeled target is still the wrong normal form for Proposition 5.18.
  -- The proved helpers `preimageOne_eq_singleton_of_injective` and
  -- `boundarylessManifold_of_lieGroup` reduce the remaining work to a self-modeled source package
  -- plus a field-generic bridge from pointwise injective `mfderiv` to `IsImmersion`.
  sorry

/-- Helper for Proposition 7.17: assuming the immersion bridge, the subgroup range of an injective
Lie-group homomorphism carries the required Lie-subgroup structure and the canonical Lie-group
isomorphism from `G`. -/
theorem rangeLieSubgroupStructureOfInjectiveImmersion
    [FiniteDimensional 𝕜 EG] [T2Space G] [SecondCountableTopology G]
    [T2Space H] [SecondCountableTopology H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (hImmF : IsImmersion I J (⊤ : WithTop ℕ∞) F) :
    ∃ S : LieSubgroup J,
      ∃ hRange : S.carrier = F.toMonoidHom.range,
          ∃ Φ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 S.ModelSpace) G S,
          ∀ x : G, (Φ x : H) = F x := by
  let e := rangeMulEquivOfInjective F hFinj
  let eRange := setRangeEquivMonoidRange F
  have hSubtypeVal :
      (Subtype.val : F.toMonoidHom.range → H) = F ∘ e.symm := by
    -- The ambient inclusion stays written as `F` after moving to the subgroup range.
    simpa [e] using subtype_val_comp_rangeMulEquivOfInjective_symm F hFinj
  have hRangeCarrier :
      (F.toMonoidHom.range : Set H) = Set.range F :=
    monoidRange_carrier_eq_setRange F
  have hSubtypeRange :
      (Subtype.val : F.toMonoidHom.range → H) =
        (Subtype.val : Set.range F → H) ∘ eRange.symm := by
    -- The canonical equivalence between the two range carriers does not move ambient points.
    simpa [eRange] using subtype_val_comp_setRangeEquivMonoidRange_symm F
  let _ := hSubtypeVal
  let _ := hRangeCarrier
  let _ := hSubtypeRange
  let _ := hImmF
  -- Route correction: after the immersion step, the remaining blocker is the self-model adapter
  -- for `G` together with the model-general immersion bridge. The carrier transport itself is now
  -- explicit: `eRange` identifies `Set.range F` with `F.toMonoidHom.range`, and `hSubtypeRange`
  -- records that the ambient inclusion is unchanged by this transport. Once `G` is presented as a
  -- boundaryless `modelWithCornersSelf 𝕜 EG` manifold and `F` is upgraded to a self-modeled
  -- immersion, Proposition 5.18 can be applied on `Set.range F` and then transported to the
  -- subgroup carrier without any additional carrier-normalization work.
  sorry

/-- Proposition 7.17: if `F : G → H` is an injective Lie group homomorphism, then its image
subgroup `F.toMonoidHom.range` has a unique smooth manifold structure such that it is a Lie
subgroup of `H` and `F : G → F(G)` is a Lie group isomorphism. -/
theorem injective_lie_group_hom_range_has_lie_subgroup_structure
    [FiniteDimensional 𝕜 EG] [T2Space G] [SecondCountableTopology G]
    [T2Space H] [SecondCountableTopology H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    ∃ S : LieSubgroup J,
      ∃ hRange : S.carrier = F.toMonoidHom.range,
        ∃ Φ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 S.ModelSpace) G S,
          ∃ hΦ : ∀ x : G, (Φ x : H) = F x,
            ∀ S' : LieSubgroup J,
              S'.carrier = F.toMonoidHom.range →
                ∀ Ψ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 S'.ModelSpace) G S',
                  (∀ x : G, (Ψ x : H) = F x) →
                    ∃ Θ : LieGroupIsomorphism
                      (modelWithCornersSelf 𝕜 S.ModelSpace)
                      (modelWithCornersSelf 𝕜 S'.ModelSpace) S S',
                      ∀ s : S, (Θ s : H) = s := by
  have hImmF : IsImmersion I J (⊤ : WithTop ℕ∞) F :=
    injectiveLieGroupHomIsImmersion F hFinj
  -- The existence half is isolated in the helper theorem so that the main proof only has to
  -- assemble uniqueness.
  rcases rangeLieSubgroupStructureOfInjectiveImmersion F hFinj hImmF with
    ⟨S, hRange, Φ, hΦ⟩
  refine ⟨S, hRange, Φ, hΦ, ?_⟩
  intro S' hRange' Ψ hΨ
  refine ⟨{ toDiffeomorph := Φ.symm.toDiffeomorph.trans Ψ.toDiffeomorph, map_mul' := ?_ }, ?_⟩
  · intro s t
    -- The comparison map is multiplicative because it is the composite of two Lie-group
    -- isomorphisms.
    calc
      Ψ (Φ.symm (s * t)) = Ψ (Φ.symm s * Φ.symm t) := by
        rw [LieGroupIsomorphism.map_mul]
      _ = Ψ (Φ.symm s) * Ψ (Φ.symm t) := by
        rw [LieGroupIsomorphism.map_mul]
  · intro s
    -- Both factorizations have ambient value `F (Φ.symm s)`, so the comparison map fixes the
    -- subgroup point after coercing into `H`.
    calc
      ((Ψ (Φ.symm s) : S') : H) = F (Φ.symm s) := hΨ (Φ.symm s)
      _ = ((Φ (Φ.symm s) : S) : H) := by rw [hΦ (Φ.symm s)]
      _ = s := by
        exact congrArg Subtype.val (Φ.toDiffeomorph.right_inv s)

/-- Unlabeled helper: any two Lie subgroup structures on the image of a Lie group homomorphism
that factor the map through Lie group isomorphisms are canonically identified by a Lie group
isomorphism commuting with the ambient inclusions into `H`. -/
theorem injective_lie_group_hom_factorization_unique
    (F : ContMDiffMonoidMorphism I J ∞ G H) (S S' : LieSubgroup J)
    (hRangeS : S.carrier = F.toMonoidHom.range)
    (Φ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 S.ModelSpace) G S)
    (hΦ : ∀ x : G, (Φ x : H) = F x)
    (hRangeS' : S'.carrier = F.toMonoidHom.range)
    (Ψ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 S'.ModelSpace) G S')
    (hΨ : ∀ x : G, (Ψ x : H) = F x) :
    ∃ Θ : LieGroupIsomorphism
      (modelWithCornersSelf 𝕜 S.ModelSpace)
      (modelWithCornersSelf 𝕜 S'.ModelSpace) S S',
      ∀ s : S, (Θ s : H) = s := by
  let _ := hRangeS
  let _ := hRangeS'
  refine ⟨{ toDiffeomorph := Φ.symm.toDiffeomorph.trans Ψ.toDiffeomorph, map_mul' := ?_ }, ?_⟩
  · intro s t
    -- The comparison map is multiplicative because it is the composite of two Lie group
    -- isomorphisms.
    calc
      Ψ (Φ.symm (s * t)) = Ψ (Φ.symm s * Φ.symm t) := by
        rw [LieGroupIsomorphism.map_mul]
      _ = Ψ (Φ.symm s) * Ψ (Φ.symm t) := by
        rw [LieGroupIsomorphism.map_mul]
  · intro s
    -- Both factorizations have ambient value `F (Φ.symm s)`, so the comparison map fixes the
    -- subgroup point after coercing into `H`.
    calc
      ((Ψ (Φ.symm s) : S') : H) = F (Φ.symm s) := hΨ (Φ.symm s)
      _ = ((Φ (Φ.symm s) : S) : H) := by rw [hΦ (Φ.symm s)]
      _ = s := by
        exact congrArg Subtype.val (Φ.toDiffeomorph.right_inv s)

end LieSubgroupImages
