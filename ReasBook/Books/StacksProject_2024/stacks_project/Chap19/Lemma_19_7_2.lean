import Mathlib
import StacksProject_2024.Chap19.Definition_19_2_4
import StacksProject_2024.Chap19.Lemma_19_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct
open AbelianSheafTransfinite
open scoped AbelianSheafTransfinite

universe w v u uβ

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable {I : Type w} (𝒢 : I → Sheaf K AddCommGrpCat.{max u v})

/-
Domain-style sampling for Lemma 19.7.2:
- primary domain: the Chapter 19.7 transfinite tower `J_[K, α](ℱ)` for abelian sheaves and the
  uniform factorization bound for maps from a fixed family into that tower;
- sampled owner declarations:
  `AbelianSheafTransfinite.J`,
  `AbelianSheafTransfinite.transition`,
  `AbelianSheafTransfinite.extend_to_successor_stage`,
  `is_alpha_small_wrt`,
  `is_alpha_small_wrt_monomorphisms_of_hasCardinalLT_cof`;
- best owner abstraction: the numbered lemma is source-facing and should be stated directly for the
  transfinite owner `J_[K, α](ℱ)` from `Lemma 19.7.1`, while `is_alpha_small_wrt` remains the
  canonical core abstraction only for a companion bridge, and the factorization surface should use
  the canonical transition map `J_[K, α](ℱ) ⟶ J_[K, β](ℱ)` rather than a truncated-stage view of
  the same recursive family;
- primitive data: the family `𝒢 : I → Sheaf K AddCommGrpCat` and the recursive tower stages
  `J_[K, α](ℱ)`;
- derived API: the existence of one ordinal `β` such that every map `𝒢 i ⟶ J_[K, β](ℱ)` factors
  through the canonical transition map from an earlier recursive stage `J_[K, α](ℱ)`, together
  with the stronger companion smallness theorem.

Source/core/bridge triage:
- `source-facing`: the uniform factorization statement for the recursive `J`-tower;
- `core/canonical`: `is_alpha_small_wrt` and the Grothendieck-abelian size owner on subobjects;
- `bridge/view`: the companion theorem below upgrading the same family bound to uniform
  `β`-smallness with respect to monomorphisms.
-/
section

/-- Helper for Lemma 19.7.2: the ordinal attached to a regular cardinal is a successor-limit
ordinal, so it is the correct transfinite stage for a source-faithful limit-step argument. -/
lemma regular_cardinal_ord_isSuccLimit
    {κ : Cardinal} (hκ : κ.IsRegular) :
    Order.IsSuccLimit κ.ord := by
  -- A regular cardinal has cofinality equal to itself, hence in particular strictly bigger than
  -- `1`; this is exactly the successor-limit criterion for ordinals.
  have hcof_gt_one : 1 < κ.ord.cof := by
    rw [hκ.cof_ord]
    exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hκ.aleph0_le
  exact (Ordinal.one_lt_cof_iff).1 hcof_gt_one

/-- Helper for Lemma 19.7.2: every covering presieve injects into the global sigma-type of arrows
of the site, so one site-wide arrow cardinal bounds all covering presieves at once. -/
lemma covering_presieve_cardinal_le_site_arrow_sigma
    (U : C) (R : Presieve U) :
    Cardinal.mk R.uncurry ≤ Cardinal.mk (Sigma fun U : C => Sigma fun V : C => V ⟶ U) := by
  -- Forget the membership proof in the presieve and remember only the ambient codomain `U`.
  refine Cardinal.mk_le_of_injective (f := fun x ↦ ⟨U, x.1⟩) ?_
  intro x y hxy
  apply Subtype.ext
  simpa using hxy

/-- Helper for Lemma 19.7.2: the covering-presieve cardinal bound is stable after applying
`Cardinal.lift`, which is the exact shape required by Sites 7.17.10. -/
lemma covering_presieve_cardinal_lift_le_site_arrow_sigma
    (U : C) (R : Presieve U) :
    Cardinal.lift (Cardinal.mk R.uncurry) ≤
      Cardinal.lift (Cardinal.mk (Sigma fun U : C => Sigma fun V : C => V ⟶ U)) := by
  -- Rewrite the lifted inequality back to the already proved injection on the underlying sets.
  exact Cardinal.lift_le.2 <|
    covering_presieve_cardinal_le_site_arrow_sigma (C := C) U R

/-- Helper for Lemma 19.7.2: once one cardinal `κG` bounds all family section-cardinals, every
fixed family member also satisfies the same cofinality bound below any `β` with `κG < β.cof`. -/
lemma family_sections_cardinal_lt_cof_of_uniform_bound
    {κG : Cardinal.{max u v w}}
    (hκG : ∀ i : I,
      Cardinal.lift (Cardinal.mk (Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U))) ≤ κG)
    {β : Ordinal.{max u v w}}
    (hβ : κG < β.cof)
    (i : I) :
    Cardinal.lift (Cardinal.mk (Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U))) < β.cof := by
  -- Specialize the uniform family bound to the chosen index and compare with `β.cof`.
  exact lt_of_le_of_lt (hκG i) hβ

/-- Helper for Lemma 19.7.2: a family of stages indexed by a set of cardinality `< β.cof` is
dominated by one stage of the ordinal `β`. This is the direct Sets 3.7.1 cofinality step used
later to replace sectionwise stage choices by one common stage. -/
lemma exists_stage_dominating_small_section_family
    {S : Type uβ} {β : Ordinal.{uβ}} (hS : Cardinal.mk S < β.cof)
    (ι : S → β.ToType) :
    ∃ j : β.ToType, ∀ s : S, ι s ≤ j := by
  -- The supremum of fewer than `β.cof` ordinals below `β` is still below `β`.
  let j : β.ToType := Ordinal.ToType.mk
    ⟨⨆ s : S, (ι s : Ordinal),
      Ordinal.iSup_lt_of_lt_cof hS fun s ↦
        (show (ι s : Ordinal) < β from (ι s).toOrd.2)⟩
  refine ⟨j, ?_⟩
  intro s
  -- Each chosen stage contributes to that supremum, hence it lies below the common bound `j`.
  have hle : (ι s).toOrd ≤ j.toOrd := by
    exact
      show (ι s : Ordinal) ≤ j.toOrd from by
        simpa [j] using Ordinal.le_iSup (fun s : S ↦ (ι s : Ordinal)) s
  simpa [j] using Ordinal.ToType.mk.monotone hle

/-- Helper for Lemma 19.7.2: the ordinal stages below `β` form a `β.cof`-filtered preorder.
This packages the same cofinality argument once so the later smallness bridge can reuse it without
rebuilding the supremum construction inline. -/
lemma isCardinalFiltered_toType_cof
    (β : Ordinal.{uβ}) :
    IsCardinalFiltered β.ToType β.cof := by
  -- Any `β.cof`-small family of stages has a common upper bound given by the supremum stage.
  exact isCardinalFiltered_preorder β.ToType β.cof fun S s hs ↦ by
    obtain ⟨j, hj⟩ :=
      exists_stage_dominating_small_section_family (S := S) (β := β) hs s
    exact ⟨j, hj⟩

/-- Helper for Lemma 19.7.2: if a family-cardinal bound `κG` is already available in the
`J`-tower universe, one successor-limit ordinal can be chosen whose cofinality dominates both the
site-arrow sigma cardinal and `κG`. -/
lemma exists_regular_bound_above_family_cardinal
    (κG : Cardinal.{max u v w}) :
    ∃ β : Ordinal.{max u v w},
      Order.IsSuccLimit β ∧
      Cardinal.lift (Cardinal.mk (Sigma fun U : C => Sigma fun V : C => V ⟶ U)) < β.cof ∧
      κG < β.cof := by
  let κ0 : Cardinal.{max u v w} :=
    max
      (Cardinal.lift (Cardinal.mk (Sigma fun U : C => Sigma fun V : C => V ⟶ U)))
      (max
        κG
        Cardinal.aleph0)
  let κ : Cardinal.{max u v w} := Order.succ κ0
  have hκreg : κ.IsRegular := by
    -- The successor of a cardinal at least `aleph0` is regular.
    change (Order.succ κ0).IsRegular
    refine Cardinal.isRegular_succ ?_
    dsimp [κ0]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨κ.ord, regular_cardinal_ord_isSuccLimit hκreg, ?_, ?_⟩
  · -- The site-arrow cardinal is below the chosen successor regular cardinal.
    rw [hκreg.cof_ord]
    exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ κ0)
  · -- The family-wide section cardinal is also below that same successor regular cardinal.
    rw [hκreg.cof_ord]
    have hκG : κG ≤ κ0 := by
      -- The prescribed family bound `κG` is one of the two inputs to the chosen maximum `κ0`.
      dsimp [κ0]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact
      lt_of_le_of_lt
        hκG
        (Order.lt_succ κ0)

/-- Helper for Lemma 19.7.2: the remaining universe-compression step is to find one cardinal in
`Cardinal.{max u v w}` bounding all family section-cardinals after lifting them into the family
universe. -/
lemma exists_uniform_family_section_bound_in_J_universe :
    ∃ κG : Cardinal.{max u v w}, ∀ i : I,
      Cardinal.lift (Cardinal.mk (Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U))) ≤ κG := by
  -- Use the honest sigma-type over the indexing family itself; this avoids any fake `[Small I]`
  -- compression and provides one ambient cardinal containing every family member's sections.
  let S : Type (max u v w) := Sigma fun i : I =>
    Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U)
  refine ⟨Cardinal.mk S, ?_⟩
  intro i
  -- Each fixed member injects into the global sigma-type by remembering its index `i`.
  simpa [S] using
    Cardinal.mk_le_of_injective
      (f := fun x : Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U) ↦ ⟨i, x⟩)
      (by
        intro x y hxy
        cases hxy
        rfl)

/-- Helper for Lemma 19.7.2: once the family-section bound `κG` is compressed into the
`J`-tower universe, the regular-cardinal step upgrades it to one ordinal whose cofinality bounds
every member of the family. -/
lemma exists_uniform_regular_bound_in_J_universe :
    ∃ β : Ordinal.{max u v w},
      Order.IsSuccLimit β ∧
      Cardinal.lift (Cardinal.mk (Sigma fun U : C => Sigma fun V : C => V ⟶ U)) < β.cof ∧
      ∀ i : I, Cardinal.lift (Cardinal.mk (Sigma fun U : C => (𝒢 i).obj.obj (Opposite.op U))) < β.cof := by
  obtain ⟨κG, hκG⟩ :=
    exists_uniform_family_section_bound_in_J_universe (C := C) (K := K) (𝒢 := 𝒢)
  obtain ⟨β, hβsucc, hβarrows, hβκG⟩ :=
    exists_regular_bound_above_family_cardinal (C := C) κG
  refine ⟨β, hβsucc, hβarrows, ?_⟩
  intro i
  -- Specialize the compressed family bound to the chosen sheaf and compare with `β.cof`.
  exact
    family_sections_cardinal_lt_cof_of_uniform_bound
      (C := C) (K := K) (𝒢 := 𝒢) hκG hβκG i

/-- Helper for Lemma 19.7.2: one successor-limit ordinal can be chosen whose cofinality dominates
the cardinality of `Subobject (𝒢 i)` for every member of the family. -/
lemma exists_uniform_regular_bound_above_subobject_cardinals :
    ∃ β : Ordinal.{max u v w},
      Order.IsSuccLimit β ∧
      ∀ i : I, Cardinal.mk (Subobject (𝒢 i)) < β.cof := by
  let κ : Cardinal.{max u v w} := Cardinal.mk (Sigma fun i : I => Subobject (𝒢 i))
  obtain ⟨β, hβsucc, -, hβκ⟩ :=
    exists_regular_bound_above_family_cardinal (C := C) (K := K) κ
  refine ⟨β, hβsucc, ?_⟩
  intro i
  refine lt_of_le_of_lt ?_ hβκ
  -- Each `Subobject (𝒢 i)` injects into the global sigma-type by remembering the family index.
  simpa [κ] using
    Cardinal.mk_le_of_injective (f := fun S : Subobject (𝒢 i) ↦ ⟨i, S⟩)
      (by
        intro S T hST
        cases hST
        rfl)

variable [HasWeakSheafify K AddCommGrpCat.{max u v}]

/-- Helper for Lemma 19.7.2: one successor-limit ordinal can be chosen so that every family
member is uniformly `β`-small with respect to monomorphisms. -/
private theorem existsUniformSuccLimitSmallnessBoundWrtMonomorphisms :
    ∃ β : Ordinal,
      Order.IsSuccLimit β ∧
      ∀ i : I, is_alpha_small_wrt (𝒢 i) (monomorphisms _) β := by
  obtain ⟨β, hβsucc, hβsub⟩ :=
    exists_uniform_regular_bound_above_subobject_cardinals (C := C) (K := K) (𝒢 := 𝒢)
  refine ⟨β, hβsucc, ?_⟩
  intro i
  -- Convert the uniform subobject-cardinality bound into the Grothendieck-abelian size owner.
  have hGi : HasCardinalLT (Subobject (𝒢 i)) β.cof := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hβsub i
  haveI : Fact β.cof.IsRegular := ⟨Cardinal.isRegular_cof hβsucc⟩
  haveI : IsCardinalFiltered β.ToType β.cof := isCardinalFiltered_toType_cof β
  intro B hB
  letI : ∀ (j j' : β.ToType) (f : j ⟶ j'), Mono (B.map f) := fun _ _ f ↦ hB f
  -- The Grothendieck-abelian owner theorem now applies directly to each family member.
  exact IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono B hGi

/-- Helper for Lemma 19.7.2: rebuild the one-step `J` construction as a local successor structure
so later proofs can use the generic `SuccStruct` transfinite-iteration API. -/
private noncomputable def jTransfiniteSuccStruct
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    SuccStruct (Sheaf K AddCommGrpCat.{max u v}) where
  X₀ := ℱ
  succ X := JOne K X
  toSucc X := jOne K X

/-- Helper for Lemma 19.7.2: the one-step map `jOne K X` is monic. -/
private theorem jOne_mono
    (X : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (jOne K X) := by
  -- Rewrite the one-step map into the sheafification comparison followed by the mapped injective
  -- envelope inclusion, so monomorphy follows from the standard componentwise mono instances.
  have hjOne :
      jOne K X =
        (sheafificationIso X).hom ≫
          (presheafToSheaf K AddCommGrpCat.{max u v}).map
            (HasFunctorialInjectiveEmbeddings.ι X.obj) := by
    rfl
  rw [hjOne]
  infer_instance

/-- Helper for Lemma 19.7.2: every transition map in the local `β.ToType` iteration of the
one-step `J` successor structure is monic. -/
private theorem jIterationMap_mono
    {β : Ordinal}
    (hβ0 : β ≠ 0)
    [NoMaxOrder β.ToType]
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    let Φ : SuccStruct (Sheaf K AddCommGrpCat.{max u v}) := jTransfiniteSuccStruct (K := K) ℱ
    let B := Φ.iterationFunctor β.ToType
    ∀ ⦃i j : β.ToType⦄ (f : i ⟶ j), Mono (B.map f) := by
  let Φ : SuccStruct (Sheaf K AddCommGrpCat.{max u v}) := jTransfiniteSuccStruct (K := K) ℱ
  letI := Ordinal.toTypeOrderBot hβ0
  let B := Φ.iterationFunctor β.ToType
  have hmonoProp :
      Φ.prop ≤ MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v}) := by
    intro F G f hf
    -- Each successor map in this local structure is exactly the one-step map `jOne`.
    cases hf
    simpa [Φ, jTransfiniteSuccStruct] using jOne_mono (K := K) F
  let htrans :
      (MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v})).TransfiniteCompositionOfShape
        β.ToType (Φ.ιIteration β.ToType) :=
    (Φ.transfiniteCompositionOfShapeιIteration β.ToType).ofLE hmonoProp
  intro i j f
  let hij : i ≤ j := leOfHom f
  let hstage := (htrans.ici i).iic (⟨j, hij⟩ : Set.Ici i)
  letI :
      (MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v})).IsStableUnderTransfiniteCompositionOfShape
        (Set.Iic (⟨j, hij⟩ : Set.Ici i)) := by
    infer_instance
  -- Restrict the transfinite composition to the interval `[i, j]`; the resulting bottom-to-top
  -- map is precisely the transition morphism `B.map f`.
  simpa [B] using
    (CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le
      (W := MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v}))
      (J := Set.Iic (⟨j, hij⟩ : Set.Ici i))) _ hstage.mem

/-- Helper for Lemma 19.7.2: every map between earlier stages in the fixed `β`-truncated local
`J`-tower is monic. -/
private theorem truncatedJTowerMap_mono
    {β : Ordinal}
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    let Φ : SuccStruct (Sheaf K AddCommGrpCat.{max u v}) := jTransfiniteSuccStruct (K := K) ℱ
    let iterTop : Φ.Iteration (⟨β, le_rfl⟩ : Set.Iic β) := Φ.iter ⟨β, le_rfl⟩
    let B := SmallObject.restrictionLT iterTop.F (le_rfl β)
    ∀ ⦃i j : Set.Iio β⦄ (f : i ⟶ j), Mono (B.map f) := by
  let Φ : SuccStruct (Sheaf K AddCommGrpCat.{max u v}) := jTransfiniteSuccStruct (K := K) ℱ
  let iterTop : Φ.Iteration (⟨β, le_rfl⟩ : Set.Iic β) := Φ.iter ⟨β, le_rfl⟩
  let B := SmallObject.restrictionLT iterTop.F (le_rfl β)
  have hmonoProp :
      Φ.prop ≤ MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v}) := by
    intro F G f hf
    -- The successor maps of the local successor structure are exactly `jOne`.
    cases hf
    simpa [Φ, jTransfiniteSuccStruct] using jOne_mono (K := K) F
  let htrans :
      (MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v})).TransfiniteCompositionOfShape
        (Set.Iic β) (Φ.ιIteration (Set.Iic β)) :=
    (Φ.transfiniteCompositionOfShapeιIteration (Set.Iic β)).ofLE hmonoProp
  intro i j f
  let i' : Set.Iic β := ⟨i.1, i.2.le⟩
  let j' : Set.Iic β := ⟨j.1, j.2.le⟩
  have hij : i' ≤ j' := by
    simpa [i', j'] using leOfHom f
  let hstage := (htrans.ici i').iic (⟨j', hij⟩ : Set.Ici i')
  letI :
      (MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v})).IsStableUnderTransfiniteCompositionOfShape
        (Set.Iic (⟨j', hij⟩ : Set.Ici i')) := by
    infer_instance
  -- Restrict the transfinite composition to the interval from the `i`th stage to the `j`th one.
  simpa [B, SmallObject.restrictionLT_map, i', j'] using
    (CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le
      (W := MorphismProperty.monomorphisms (Sheaf K AddCommGrpCat.{max u v}))
      (J := Set.Iic (⟨j', hij⟩ : Set.Ici i'))) _ hstage.mem

/-- Helper for Lemma 19.7.2: once a successor-limit ordinal witnesses `β`-smallness of a family
member with respect to monomorphisms, every map into `J_[K, β](ℱ)` factors through some earlier
stage of the transfinite `J`-tower. -/
private theorem factorThroughEarlierJStage_of_smallness
    {β : Ordinal}
    (hβsucc : Order.IsSuccLimit β)
    {i : I}
    (hsmall : is_alpha_small_wrt (𝒢 i) (monomorphisms _) β)
    (ℱ : Sheaf K AddCommGrpCat.{max u v})
    (φ : 𝒢 i ⟶ J_[K,β](ℱ)) :
    ∃ α : Ordinal, ∃ hα : α < β, ∃ ψ : 𝒢 i ⟶ J_[K,α](ℱ),
      ψ ≫ transition K hα.le ℱ = φ := by
  let Φ : SuccStruct (Sheaf K AddCommGrpCat.{max u v}) := jTransfiniteSuccStruct (K := K) ℱ
  let iterTop : Φ.Iteration (⟨β, le_rfl⟩ : Set.Iic β) := Φ.iter ⟨β, le_rfl⟩
  let B0 : Set.Iio β ⥤ Sheaf K AddCommGrpCat.{max u v} :=
    SmallObject.restrictionLT iterTop.F (le_rfl β)
  let e : β.ToType ≌ Set.Iio β :=
    ((Ordinal.ToType.mk : Set.Iio β ≃o β.ToType).symm).equivalence
  let B : β.ToType ⥤ Sheaf K AddCommGrpCat.{max u v} := e.functor ⋙ B0
  have hB :
      ∀ ⦃i j : β.ToType⦄ (f : i ⟶ j), Mono (B.map f) := by
    intro j j' f
    -- The public indexing change is only by the ordinal order equivalence `β.ToType ≃ Set.Iio β`.
    simpa [B] using
      truncatedJTowerMap_mono (C := C) (K := K) (β := β) ℱ (e.functor.map f)
  letI : PreservesColimit B (coyoneda.obj (op (𝒢 i))) :=
    hsmall B hB
  let c0 : Cocone B0 := SmallObject.coconeOfLE iterTop.F (le_rfl β)
  have hβtop : Order.IsSuccLimit (⟨β, le_rfl⟩ : Set.Iic β) := by
    simpa using hβsucc
  have hc0 : IsColimit c0 := by
    -- The fixed `β`-truncated tower presents its top stage as the colimit of earlier stages.
    simpa [c0, B0] using
      (iterTop.isColimit (⟨β, le_rfl⟩ : Set.Iic β) hβtop (show (⟨β, le_rfl⟩ : Set.Iic β) ≤ ⟨β, le_rfl⟩ by rfl))
  let c : Cocone B := c0.whisker e.functor
  have hc : IsColimit c := (IsColimit.whiskerEquivalenceEquiv e).toFun hc0
  letI : HasColimit B := HasColimit.mk ⟨c, hc⟩
  have hsurj :
      Function.Surjective (colimit.post B (coyoneda.obj (op (𝒢 i)))) := by
    exact ((isIso_iff_bijective _).1 inferInstance).2
  obtain ⟨x, hx⟩ := hsurj φ
  obtain ⟨j, ψ, rfl⟩ := Types.jointly_surjective' x
  have hfactor : ψ ≫ colimit.ι B j = φ := by
    simpa using (colimit_post_coyoneda_ι_app (𝒢 i) B j ψ).trans hx
  refine ⟨(j : Ordinal), j.2, ?_⟩
  refine ⟨?_ , ?_⟩
  · -- The chosen stage in the reindexed truncated tower is definitionally the public stage
    -- `J_[K, (j : Ordinal)](ℱ)`.
    simpa [B, B0, e] using ψ
  · -- The chosen cocone leg is definitionally the canonical transition to the top stage.
    simpa [B, B0, c, c0, e, transition, Category.assoc] using hfactor

/-- Lemma 19.7.2: for a family of abelian sheaves on a site, there is a single ordinal `β` such
that every morphism from a member of the family to the transfinite stage `J_[K, β](ℱ)` factors
through the canonical transition map from some earlier recursive stage `J_[K, α](ℱ)`. -/
theorem abelianSheaf_family_exists_uniform_J_stage_factorization_bound :
    ∃ β : Ordinal,
      ∀ (ℱ : Sheaf K AddCommGrpCat.{max u v}) (i : I) (φ : 𝒢 i ⟶ J_[K,β](ℱ)),
        ∃ α : Ordinal, ∃ hα : α < β, ∃ ψ : 𝒢 i ⟶ J_[K,α](ℱ),
          ψ ≫ transition K hα.le ℱ = φ := by
  -- Source-facing route: choose a single regular cardinal bound for the family, translate it to an
  -- ordinal `β`, and specialize the resulting `β`-smallness to the recursive transfinite tower
  -- `J_[K, ·](ℱ)` from Lemma 19.7.1 so that each map to `J_[K, β](ℱ)` factors through the
  -- canonical transition map from some earlier recursive stage `J_[K, α](ℱ)`.
  -- Route correction: the family-cardinal compression and the companion smallness theorem are now
  -- in place. The remaining transport blocker is the source-facing colimit bridge for the public
  -- `J`-tower: locally rebuild the same `SuccStruct` from `JOne`/`jOne`, prove its one-step maps
  -- are mono, identify the succ-limit cocone legs with `transition K h.le ℱ`, and then read the
  -- desired factorization off the surjectivity of `colimit.post` supplied by the companion theorem.
  obtain ⟨β, hβsucc, hβsmall⟩ :=
    existsUniformSuccLimitSmallnessBoundWrtMonomorphisms (C := C) (K := K) (𝒢 := 𝒢)
  refine ⟨β, ?_⟩
  intro ℱ i φ
  -- Specialize the uniform smallness witness to the chosen family member and map.
  exact factorThroughEarlierJStage_of_smallness
    (C := C) (K := K) (𝒢 := 𝒢) hβsucc (hβsmall i) ℱ φ

end

/-- Companion bridge: the same family admits a single ordinal bound witnessing uniform
`β`-smallness with respect to monomorphisms. -/
theorem abelianSheaf_family_exists_uniform_smallness_bound_wrt_monomorphisms
    : ∃ β : Ordinal, ∀ i : I, is_alpha_small_wrt (𝒢 i) (monomorphisms _) β := by
  obtain ⟨β, -, hβsmall⟩ :=
    existsUniformSuccLimitSmallnessBoundWrtMonomorphisms (C := C) (K := K) (𝒢 := 𝒢)
  exact ⟨β, hβsmall⟩

end
