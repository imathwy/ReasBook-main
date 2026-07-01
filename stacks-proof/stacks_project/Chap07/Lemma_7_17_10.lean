import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {K : Coverage C}
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]

local notation "J" => K.toGrothendieck

/- Domain-style sampling for Lemma 7.17.10:
- primary domain: filtered colimits of `Type`-valued sheaves on a site presented by a coverage,
  specialized to ordinal-indexed diagrams and controlled by ordinal cofinality;
- sampled owner abstractions:
  `Coverage.toGrothendieck`,
  `sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject`,
  `Ordinal.iSup_lt_of_lt_cof`,
  `colimit.post`;
- source/core/bridge triage:
  `source-facing`: the ordinal parameter `β` and the cardinal bound
  `Cardinal.lift (Cardinal.mk R.uncurry) < β.cof` on `K`-covering presieves;
  `core/canonical`: the section-comparison morphism
  `colimit.post F ((sheafSections J (Type (max u v))).obj (op U))` together with
  the filtered comparison owner family already isolated in Lemma 7.17.7;
  `bridge/view`: passing from the chosen coverage `K` to the associated Grothendieck topology, and
  from a `< β.cof`-small family of local stages to one common stage of the ordinal diagram using
  cofinality.

Primitive data are only the ordinal diagram `F` and the source cardinal bound `hcover`. The
comparison morphism is derived API, and the ambient owner family in the chapter is still the
filtered-colimit comparison of Lemma 7.17.7. There is no upstream owner for the exact
small-cover cofinality condition, so that hypothesis should remain explicit rather than being
collapsed into the different quasi-compact-overlap owner from Lemma 7.17.7.
-/
-- Proof sketch: argue directly with the source small-cover hypothesis. Injectivity comes from the
-- filtered-colimit comparison for sheaf sections, while surjectivity is obtained by representing a
-- target section on a `K`-covering presieve of cardinality `< β.cof`, then using ordinal
-- cofinality to dominate all local stages by one stage of `F`. The empty-index case `β = 0`
-- remains a separate degenerate argument.

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf J (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

/-- Helper for Lemma 7.17.10: the chosen sheaf colimit is canonically the sheafification of the
underlying presheaf colimit. -/
noncomputable def presheafColimitToSheafIso
    [hcolim : HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    ((presheafToSheaf J (Type (max u v))).obj
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅ @colimit _ _ _ _ F hcolim :=
  (colimit.isoColimitCocone
    ⟨Sheaf.sheafifyCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm

/-- Helper for Lemma 7.17.10: the source filtered colimit of sections over `U` is the evaluation
of the presheaf-colimit comparison at `U`. -/
theorem section_colimit_post_eq_eval
    (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ (sheafSections J (Type (max u v))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    colimit.post F ((sheafSections J (Type (max u v))).obj (op U)) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
          ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)) ≫
        (colimit.post F (sheafToPresheaf J (Type (max u v)))).app (op U) := by
  -- The sections functor is the composite of the forgetful functor with evaluation at `U`.
  simpa using
    (colimit.post_post F (sheafToPresheaf J (Type (max u v)))
      ((evaluation Cᵒᵖ (Type (max u v))).obj (op U))).symm

/-- Helper for Lemma 7.17.10: restriction commutes with each transition map in the ordinal-indexed
sheaf diagram. -/
theorem sheaf_transition_app_map_eq_map_app
    {i j : Set.Iio β} (f : i ⟶ j)
    {U V : C} (g : V ⟶ U) (a : (F.obj i).1.obj (op U)) :
    ((F.map f).1.app (op V)) (((F.obj i).1.map g.op) a) =
      ((F.obj j).1.map g.op) (((F.map f).1.app (op U)) a) := by
  -- This is exactly the naturality square of the underlying presheaf map.
  simpa [Function.comp] using congrFun ((F.map f).1.naturality g.op) a

include hcover

/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of stages in the ordinal diagram admits
one common upper stage below `β`. -/
lemma coveringPresieve_common_stage_of_small_family
    {ι : Type (max u v)} (f : ι → Ordinal.{max u v})
    (hf : ∀ i, f i < β)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ a : Set.Iio β, ∀ i, f i ≤ a.1 := by
  -- Pass to an explicit `ULift`-indexed supremum so `Ordinal.iSup_lt_of_lt_cof` matches the
  -- source cardinal bound without any further universe transport.
  have hiSup : ⨆ i : ULift.{max u v} ι, f i.down < β := by
    have hι' : Cardinal.mk (ULift.{max u v} ι) < β.cof := by
      simpa using hι
    simpa using Ordinal.iSup_lt_of_lt_cof hι' (fun i : ULift.{max u v} ι => hf i.down)
  refine ⟨⟨⨆ i, f i, ?_⟩, ?_⟩
  · simpa using hiSup
  · intro i
    exact Ordinal.le_iSup f i

/-- Helper for Lemma 7.17.10: every section of the presheaf colimit is represented by one stage of
the ordinal diagram after evaluating at a fixed object. -/
lemma presheafColimit_section_exists_rep
    (U : C)
    (x : (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op U)) :
    ∃ i : Set.Iio β, ∃ s : (F.obj i).1.obj (op U),
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s = x := by
  -- Evaluate the presheaf colimit pointwise, represent the resulting element there, and then
  -- transport the representative back through the pointwise-colimit comparison isomorphism.
  let e := asIso (colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
    ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)))
  obtain ⟨i, s, hs⟩ :=
    Concrete.colimit_exists_rep
      ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op U))
      (e.inv x)
  refine ⟨i, s, ?_⟩
  apply_fun e.hom at hs
  simpa using hs

/-- Helper for Lemma 7.17.10: if two sections represented at one stage become equal in the
presheaf colimit, then they already become equal after passing to a later ordinal stage. -/
lemma presheafColimit_section_eq_at_later_stage
    (U : C) {i : Set.Iio β}
    {s t : (F.obj i).1.obj (op U)}
    (h :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) t) :
    ∃ j : Set.Iio β, ∃ f : i ⟶ j,
      ((F.map f).1.app (op U)) s = ((F.map f).1.app (op U)) t := by
  -- Move the equality to the pointwise colimit, use filtered-colimit equality there, and then
  -- exploit thinness of `Set.Iio β` so both comparison maps land in the same later stage.
  let e := asIso (colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
    ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)))
  have h' :
      colimit.ι
          (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
            (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) i s =
        colimit.ι
          (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
            (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) i t := by
    apply e.hom.injective
    simpa using h
  obtain ⟨j, f, g, hfg⟩ :=
    Concrete.colimit_exists_of_rep_eq
      (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) s t h'
  have hfg' : ((F.map f).1.app (op U)) s = ((F.map g).1.app (op U)) t := by
    simpa using hfg
  subst g
  exact ⟨j, f, hfg'⟩

/-- Helper for Lemma 7.17.10: the pair index of a `< β.cof`-small covering presieve is still
`< β.cof`. -/
lemma coveringPresieve_small_overlap_index
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Cardinal.lift (Cardinal.mk (R.uncurry × R.uncurry)) < β.cof := by
  -- The source hypothesis already bounds the arrow index of the covering presieve itself.
  have hRsmall : HasCardinalLT R.uncurry β.cof := by
    simpa [HasCardinalLT] using hcover U R hR
  by_cases hne : Nonempty R.uncurry
  · -- A nonempty cover index forces `β.cof` to be infinite, so products stay small.
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk R.uncurry ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk R.uncurry) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk R.uncurry) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone (hcover U R hR)
    have hβinf : Cardinal.aleph0 ≤ β.cof := by
      exact (Ordinal.aleph0_le_cof).2 ((Ordinal.one_lt_cof_iff).1 hβone)
    have hprod : HasCardinalLT (R.uncurry × R.uncurry) β.cof :=
      hasCardinalLT_prod hβinf hRsmall hRsmall
    simpa [HasCardinalLT] using hprod
  · -- If the cover index is empty, then the pair index is empty as well.
    haveI : IsEmpty R.uncurry := not_nonempty_iff.mp hne
    haveI : IsEmpty (R.uncurry × R.uncurry) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using (hcover U R hR)
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

/-- Helper for Lemma 7.17.10: the sigma-family of first-level pullback covers chosen over a
covering presieve is still `< β.cof`. -/
lemma coveringPresieve_small_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1) :
    Cardinal.lift (Cardinal.mk (Σ i : R.uncurry, (T i).uncurry)) < β.cof := by
  by_cases hne : Nonempty R.uncurry
  · -- A nonempty cover index forces `β.cof` to be regular enough for sigma-smallness.
    have hRsmall : HasCardinalLT R.uncurry β.cof := by
      simpa [HasCardinalLT] using hcover U R hR
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk R.uncurry ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk R.uncurry) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk R.uncurry) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone (hcover U R hR)
    letI : Fact β.cof.IsRegular :=
      ⟨Cardinal.isRegular_cof ((Ordinal.one_lt_cof_iff).1 hβone)⟩
    have hTsmall : ∀ i : R.uncurry, HasCardinalLT (T i).uncurry β.cof := by
      intro i
      simpa [HasCardinalLT] using hcover i.1.1 (T i) (hT i)
    have hσ : HasCardinalLT (Σ i : R.uncurry, (T i).uncurry) β.cof :=
      hasCardinalLT_sigma (fun i : R.uncurry ↦ (T i).uncurry) β.cof hRsmall hTsmall
    simpa [HasCardinalLT] using hσ
  · -- If the original cover index is empty, then the sigma family is empty as well.
    haveI : IsEmpty R.uncurry := not_nonempty_iff.mp hne
    haveI : IsEmpty (Σ i : R.uncurry, (T i).uncurry) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using (hcover U R hR)
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

/-- Helper for Lemma 7.17.10: a `< β.cof`-small index family of `< β.cof`-small fibers has
`< β.cof`-small sigma total space. -/
lemma small_sigma_of_small_family
    {ι : Type (max u v)} (X : ι → Type (max u v))
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof)
    (hX : ∀ i, Cardinal.lift (Cardinal.mk (X i)) < β.cof) :
    Cardinal.lift (Cardinal.mk (Σ i, X i)) < β.cof := by
  by_cases hne : Nonempty ι
  · -- A nonempty small index family forces `β.cof` to be regular enough for sigma-smallness.
    have hιsmall : HasCardinalLT ι β.cof := by
      simpa [HasCardinalLT] using hι
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk ι ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk ι) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk ι) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone hι
    letI : Fact β.cof.IsRegular :=
      ⟨Cardinal.isRegular_cof ((Ordinal.one_lt_cof_iff).1 hβone)⟩
    have hXsmall : ∀ i, HasCardinalLT (X i) β.cof := by
      intro i
      simpa [HasCardinalLT] using hX i
    have hσ : HasCardinalLT (Σ i, X i) β.cof :=
      hasCardinalLT_sigma X β.cof hιsmall hXsmall
    simpa [HasCardinalLT] using hσ
  · -- If there are no indices, then the sigma family is empty as well.
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    haveI : IsEmpty (Σ i, X i) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hι
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

/-- Helper for Lemma 7.17.10: once the first-level sigma family of pullback-cover branches is
`< β.cof`, any chosen secondary pullback covers over those branches still form a `< β.cof`-small
owner family. -/
lemma coveringPresieve_small_secondary_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift (Cardinal.mk (Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry)) < β.cof := by
  -- Reuse the first-level sigma bound and the original small-cover hypothesis fiberwise.
  let ι' : Type (max u v) := Σ i : R.uncurry, (T i).uncurry
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := ι')
      (X := fun q : ι' ↦ (B q).uncurry)
      (hι := coveringPresieve_small_sigma_family
        (β := β)
        (hcover := hcover)
        (hR := hR)
        T
        hT)
      ?_
  intro q
  simpa [ι'] using hcover q.2.1.1 (B q) (hB q)

/-- Helper for Lemma 7.17.10: package one retained secondary branch together with a fixed
comparison branch of the original cover `R`. -/
def targeted_secondary_owner_index
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1) :
    Type (max u v) :=
  Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry

/-- Helper for Lemma 7.17.10: after adjoining one original-cover branch to each retained
secondary branch, the resulting targeted owner family is still `< β.cof`. -/
lemma coveringPresieve_small_targeted_secondary_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry)) <
      β.cof := by
  let κ : Type (max u v) := Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry
  -- First keep the old synchronized secondary owner family small.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun _ : κ ↦ R.uncurry)
      (hι := by
        simpa [κ] using
          coveringPresieve_small_secondary_sigma_family
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro _
  -- Then use the original small-cover bound for the retained comparison branch.
  simpa using hcover U R hR

/-- Helper for Lemma 7.17.10: the targeted owner index that remembers a fixed comparison branch
of `R` is still `< β.cof`. -/
lemma targeted_secondary_owner_index_small
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof := by
  -- Unfold the dedicated index packaging once, then reuse the existing targeted sigma bound
  -- without asking `simp` to normalize the large sigma type on its own.
  change
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry)) <
      β.cof
  exact
    coveringPresieve_small_targeted_secondary_sigma_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB

/-- Helper for Lemma 7.17.10: if each retained secondary branch carries one extra covering
presieve over its own source, the resulting sigma owner family is still `< β.cof`. -/
lemma coveringPresieve_small_targeted_secondary_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (C' : ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, Presieve p.2.1.1)
    (hC' : ∀ p, C' p ∈ K p.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, (C' p).uncurry)) <
      β.cof := by
  let κ : Type (max u v) := Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry
  -- Keep the already-synchronized secondary owner family small, then apply the original cover
  -- bound fiberwise to the new pullback owners.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun p : κ ↦ (C' p).uncurry)
      (hι := by
        simpa [κ] using
          coveringPresieve_small_secondary_sigma_family
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro p
  simpa [κ] using hcover p.2.1.1 (C' p) (hC' p)

/-- Helper for Lemma 7.17.10: once a fixed comparison branch `j` is adjoined to each retained
secondary owner, any further family of pullback covers over those fixed-target owners is still
`< β.cof`. -/
lemma coveringPresieve_small_fixed_target_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hC' : ∀ p, C' p ∈ K p.1.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
      β.cof := by
  let κ : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- First keep the fixed-target owner family small using the earlier targeted sigma bound.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun p : κ ↦ (C' p).uncurry)
      (hι := by
        simpa [κ] using
          targeted_secondary_owner_index_small
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro p
  -- Then apply the original small-cover hypothesis fiberwise to the chosen pullback cover.
  simpa [κ] using hcover p.1.2.1.1 (C' p) (hC' p)

/-- Helper for Lemma 7.17.10: one can choose a canonical pullback cover over every fixed-target
owner, and the resulting sigma owner family is still `< β.cof`. -/
lemma targeted_secondary_owner_has_small_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    ∃ C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, C' p ∈ K p.1.2.1.1) ∧
      (∀ p, (C' p).FactorsThruAlong (B p.1.1) p.1.2.1.2) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Pull back the retained secondary cover along each remembered secondary branch.
  choose C' hC' hC'fac using
    fun p : κtarget ↦ K.pullback p.1.2.1.2 (B p.1.1) (hB p.1.1)
  refine ⟨C', hC', hC'fac, ?_⟩
  -- The earlier fixed-target smallness lemma applies to this canonical pullback family.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      C'
      hC'

/-- Helper for Lemma 7.17.10: if each retained secondary owner is equipped with an actual map to
its remembered target branch of `R`, then the corresponding family of target-side pullback covers
is still `< β.cof`.

This isolates the structural datum missing from the current blocked proof: the existing
`targeted_secondary_owner_index` remembers only the branch `j : R.uncurry`, not a morphism from the
owner source to `j.1.1`. Once that morphism is part of the index, the target-pullback smallness
step is immediate. -/
lemma targeted_secondary_owner_has_small_fixed_target_pullback_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (targetMap :
      ∀ p : targeted_secondary_owner_index (T := T) B, p.1.2.1.1 ⟶ p.2.1.1) :
    ∃ Ctarget : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, Ctarget p ∈ K p.1.2.1.1) ∧
      (∀ p, (Ctarget p).FactorsThruAlong (T p.2) (targetMap p)) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (Ctarget p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Route correction: once the source-to-target branch map is explicit, the target-side pullback
  -- family is obtained by a direct coverage pullback over each fixed target branch.
  choose Ctarget hCtarget hCtargetfac using
    fun p : κtarget ↦ K.pullback (targetMap p) (T p.2) (hT p.2)
  refine ⟨Ctarget, hCtarget, hCtargetfac, ?_⟩
  -- The existing fixed-target owner cardinal bound applies to any such family of pullback covers.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      Ctarget
      hCtarget

/-- Helper for Lemma 7.17.10: a source-faithful fixed-target overlap witness remembers one
retained secondary owner `p`, one common source `X`, a map from `X` to the retained secondary
source `p.1.2.1.1`, one concrete branch of the pullback cover `T p.2` over the fixed target branch
`p.2`, and a map from `X` to that target-side branch source.

This is the exact datum used in the Stacks proof: pairwise overlap comparisons are performed only
after passing to a common source dominating both the retained secondary branch and the chosen fixed
target branch. -/
def targeted_secondary_target_overlap_witness
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (p : targeted_secondary_owner_index (T := T) B) :
    Type (max u v) :=
  Σ X : C,
    Σ u : X ⟶ p.1.2.1.1,
      Σ qj : (T p.2).uncurry,
        { v : X ⟶ qj.1.1 //
          u ≫ p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2 = v ≫ qj.1.2 ≫ p.2.1.2 }

/-- Helper for Lemma 7.17.10: the common-source branch selected in the fixed-target
comparison has the same composite to the base object as the retained secondary branch. -/
lemma pulled_back_secondary_branch_target_overlap_base_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    {r j : R.uncurry} {W Y A X A₁ A₂ N : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (nmap : N ⟶ Y)
    (i₁ : N ⟶ A₁) (e₁ : A₁ ⟶ A) (he₁ : B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩ e₁)
    (hi₁ : i₁ ≫ e₁ = nmap ≫ i)
    (k : X ⟶ N)
    (c : X ⟶ A₂) (e₂ : A₂ ⟶ j.1.1) (he₂ : T j e₂)
    (hc : c ≫ e₂ = k ≫ nmap ≫ g ≫ hj') :
    (k ≫ i₁) ≫ e₁ ≫ e₀ ≫ r.1.2 = c ≫ e₂ ≫ j.1.2 := by
  -- Normalize both composites to the same map to `U`, following the source proof's common-source
  -- overlap comparison.
  calc
    (k ≫ i₁) ≫ e₁ ≫ e₀ ≫ r.1.2 = k ≫ (i₁ ≫ e₁) ≫ e₀ ≫ r.1.2 := by
      simp [Category.assoc]
    _ = k ≫ (nmap ≫ i) ≫ e₀ ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t ≫ e₀ ≫ r.1.2) hi₁
    _ = k ≫ nmap ≫ (i ≫ e₀) ≫ r.1.2 := by
      simp [Category.assoc]
    _ = k ≫ nmap ≫ (g ≫ gr') ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ nmap ≫ t ≫ r.1.2) hie.symm
    _ = k ≫ nmap ≫ g ≫ (hj' ≫ j.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ nmap ≫ g ≫ t) hW
    _ = c ≫ e₂ ≫ j.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ j.1.2) hc.symm
    _ = c ≫ (e₂ ≫ j.1.2) := by
      simp [Category.assoc]

/-- Helper for Lemma 7.17.10: one concrete branch of the pulled-back secondary cover together
with one branch of the fixed-target cover determines the common-source overlap witness used in the
source proof. -/
def pulled_back_secondary_branch_target_overlap_witness
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    {r j : R.uncurry} {W Y A X A₁ A₂ N : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (nmap : N ⟶ Y)
    (i₁ : N ⟶ A₁) (e₁ : A₁ ⟶ A) (he₁ : B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩ e₁)
    (hi₁ : i₁ ≫ e₁ = nmap ≫ i)
    (k : X ⟶ N)
    (c : X ⟶ A₂) (e₂ : A₂ ⟶ j.1.1) (he₂ : T j e₂)
    (hc : c ≫ e₂ = k ≫ nmap ≫ g ≫ hj') :
    targeted_secondary_target_overlap_witness
      (T := T)
      (B := B)
      ⟨⟨⟨r, ⟨⟨A, e₀⟩, he⟩⟩, ⟨⟨A₁, e₁⟩, he₁⟩⟩, j⟩ :=
  ⟨X, k ≫ i₁, ⟨⟨A₂, e₂⟩, he₂⟩,
    ⟨c,
      pulled_back_secondary_branch_target_overlap_base_eq
        (β := β)
        (hcover := hcover)
        (T := T)
        (B := B)
        (gr' := gr')
        (hj' := hj')
        (hW := hW)
        (g := g)
        (i := i)
        (e₀ := e₀)
        (he := he)
        (hie := hie)
        (nmap := nmap)
        (i₁ := i₁)
        (e₁ := e₁)
        (he₁ := he₁)
        (hi₁ := hi₁)
        (k := k)
        (c := c)
        (e₂ := e₂)
        (he₂ := he₂)
        (hc := hc)⟩⟩

/-- Helper for Lemma 7.17.10: one can also choose, for every remembered secondary owner together
with a fixed branch of `R`, a canonical pullback cover of the original covering presieve along the
full composite to `U`; this keeps the total owner family `< β.cof`, but it only lands in some
branch of `R` rather than in the specifically remembered target branch. -/
lemma targeted_secondary_owner_has_small_base_cover_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    ∃ C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, C' p ∈ K p.1.2.1.1) ∧
      (∀ p,
        (C' p).FactorsThruAlong R
          (p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2)) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Pull back the original covering presieve along the full retained composite to the base object
  -- `U`; this is the strongest canonical owner family available from the coverage API alone.
  choose C' hC' hC'fac using
    fun p : κtarget ↦
      K.pullback
        (p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2)
        R
        hR
  refine ⟨C', hC', hC'fac, ?_⟩
  -- The previously established fixed-target cardinal bound applies to any family of covers over
  -- the remembered secondary-owner sources.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      C'
      hC'

/-- Helper for Lemma 7.17.10: the comparison from the presheaf colimit to the underlying presheaf
of the sheaf colimit factors through the sheafification unit and the canonical colimit
identification. -/
theorem presheaf_colimit_comparison_factorization
    [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    (CategoryTheory.toSheafify J
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≫
      (sheafToPresheaf J (Type (max u v))).map
        ((colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv) =
      colimit.post F (sheafToPresheaf J (Type (max u v))) := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))
  let c := (Sheaf.sheafifyCocone E : Cocone F)
  let e :
      ((presheafToSheaf J (Type (max u v))).obj
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅
        @colimit _ _ _ _ F inferInstance :=
    (colimit.isoColimitCocone
      ⟨Sheaf.sheafifyCocone E,
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm
  -- Compare the two candidate maps after precomposing with each presheaf-colimit injection.
  refine colimit.hom_ext ?_
  intro i
  have hleft :
      colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i ≫
          CategoryTheory.toSheafify J
            (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) ≫
            (sheafToPresheaf J (Type (max u v))).map
              e.hom =
        (c.ι.app i).hom ≫
          (sheafToPresheaf J (Type (max u v))).map
            e.hom := by
    -- The sheafified cocone leg is the presheaf-colimit leg followed by the sheafification unit.
    simpa [Category.assoc] using congrArg
      (fun f ↦ f ≫ (sheafToPresheaf J (Type (max u v))).map e.hom)
      (Sheaf.sheafifyCocone_ι_app_val E i).symm
  rw [hleft]
  have hmid :
      (c.ι.app i).hom ≫
        (sheafToPresheaf J (Type (max u v))).map
          e.hom =
      (colimit.ι F i).hom := by
    -- The canonical colimit isomorphism identifies the sheafified cocone with the chosen colimit.
    simpa [E, c, e, CategoryTheory.presheafColimitToSheafIso] using congrArg (fun f ↦ f.1)
      (colimit.isoColimitCocone_ι_inv
        ⟨Sheaf.sheafifyCocone E,
          Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩ i)
  rw [hmid]
  exact (colimit.ι_post F (sheafToPresheaf J (Type (max u v))) i).symm

/-- Helper for Lemma 7.17.10: evaluating the section-comparison map rewrites it as the pointwise
presheaf-colimit comparison, then the sheafification unit, then the canonical colimit
identification. -/
theorem colimit_post_eq_toSheafify_comparison_app
    (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))]
    [HasColimit (F ⋙ (sheafSections J (Type (max u v))).obj (op U))] :
    colimit.post F ((sheafSections J (Type (max u v))).obj (op U)) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
          ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)) ≫
        (CategoryTheory.toSheafify J
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))).app (op U) ≫
        (((colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv).1.app (op U)) := by
  -- First rewrite the sections comparison as evaluation of the presheaf comparison.
  rw [section_colimit_post_eq_eval]
  let e :
      ((presheafToSheaf J (Type (max u v))).obj
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅
        @colimit _ _ _ _ F inferInstance :=
    (colimit.isoColimitCocone
      ⟨Sheaf.sheafifyCocone
          (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm
  -- Then evaluate the presheaf-side factorization through sheafification.
  have hfactor :
      (colimit.post F (sheafToPresheaf J (Type (max u v)))).app (op U) =
        (CategoryTheory.toSheafify J
            (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))).app (op U) ≫
          (e.hom.1.app (op U)) := by
    simpa [Category.assoc] using
      (congrArg (fun f ↦ f.app (op U))
        (presheaf_colimit_comparison_factorization β F)).symm
  rw [hfactor]
  rfl

/-- Helper for Lemma 7.17.10: a presieve agrees with the arrow family indexed by its own
`uncurry` presentation. -/
lemma presieve_eq_of_uncurry {U : C} (R : Presieve U) :
    R = Presieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) := by
  -- Present each arrow of `R` by the corresponding point of `R.uncurry`, and conversely unpack
  -- membership in the arrow-family presentation.
  refine le_antisymm ?_ ?_
  · intro Y f hf
    let i : R.uncurry := ⟨⟨Y, f⟩, hf⟩
    exact Presieve.ofArrows.mk i
  · intro Y f hf
    obtain ⟨i⟩ := hf
    exact i.2

/-- Helper for Lemma 7.17.10: if two same-stage sections agree in the presheaf colimit after
restricting along every arrow of a covering presieve, then their colimit classes already agree
globally. -/
lemma presheafColimit_local_cover_eq_implies_colimit_eq
    {a : Set.Iio β} {Z : C} {T : Presieve Z} (hT : T ∈ K Z)
    {u v : (F.obj a).1.obj (op Z)}
    (hlocal :
      ∀ k : T.uncurry,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v)) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v := by
  by_cases hne : Nonempty T.uncurry
  · -- Synchronize the eventual overlap equalities to one later stage and then use sheaf-stage
    -- separatedness on the given covering presieve.
    choose b f hf using
      fun k : T.uncurry ↦
        presheafColimit_section_eq_at_later_stage
          (β := β)
          (F := F)
          k.1.1
          (i := a)
          (s := ((F.obj a).1.map k.1.2.op) u)
          (t := ((F.obj a).1.map k.1.2.op) v)
          (h := hlocal k)
    obtain ⟨c, hc⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun k : T.uncurry ↦ (b k).1)
        (hf := fun k ↦ (b k).2)
        (hι := hcover Z T hT)
    obtain ⟨k₀⟩ := hne
    have hac : a.1 ≤ c.1 := by
      exact le_trans (leOfHom (f k₀)) (hc k₀)
    let u' : (F.obj c).1.obj (op Z) :=
      ((F.map (homOfLE hac)).1.app (op Z)) u
    let v' : (F.obj c).1.obj (op Z) :=
      ((F.map (homOfLE hac)).1.app (op Z)) v
    have hsheafT : Presieve.IsSheafFor ((F.obj c).1) T := by
      exact ((Presieve.isSheaf_coverage (K := K) ((F.obj c).1)).1 (F.obj c).2) T hT
    have hlocal' :
        ∀ {Y : C} (g : Y ⟶ Z) (_ : T g),
          ((F.obj c).1.map g.op) u' = ((F.obj c).1.map g.op) v' := by
      intro Y g hg
      let k : T.uncurry := ⟨⟨Y, g⟩, hg⟩
      have hcomp :
          f k ≫ homOfLE (hc k) = homOfLE (le_trans (leOfHom (f k)) (hc k)) :=
        Subsingleton.elim _ _
      have hu :
          ((F.obj c).1.map g.op) u' =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u)) := by
        -- Rewrite the restriction of the common-stage lift as the iterated transition map
        -- through the witness stage for this arrow.
        simp only [u', hcomp, Functor.map_comp]
        rw [show
            ((F.map (homOfLE (le_trans (leOfHom (f k)) (hc k)))).1.app (op Y)) =
              ((F.map (homOfLE (hc k))).1.app (op Y)) ≫
                ((F.map (f k)).1.app (op Y)) by
              simpa [Functor.map_comp, hcomp] using
                (rfl :
                  (F.map (f k ≫ homOfLE (hc k))).1.app (op Y) =
                    (F.map (f k ≫ homOfLE (hc k))).1.app (op Y))]
        rw [Category.assoc]
        simp_rw [show
            ((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u) =
              ((F.obj (b k)).1.map g.op) (((F.map (f k)).1.app (op Z)) u) by
                simpa using
                  sheaf_transition_app_map_eq_map_app
                    (β := β)
                    (F := F)
                    (f := f k)
                    (g := g)
                    (a := u)]
        simpa [Function.comp] using
          sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE (hc k))
            (g := g)
            (a := ((F.map (f k)).1.app (op Z)) u)
      have hv :
          ((F.obj c).1.map g.op) v' =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v)) := by
        -- The same rewrite applies to the second section.
        simp only [v', hcomp, Functor.map_comp]
        rw [show
            ((F.map (homOfLE (le_trans (leOfHom (f k)) (hc k)))).1.app (op Y)) =
              ((F.map (homOfLE (hc k))).1.app (op Y)) ≫
                ((F.map (f k)).1.app (op Y)) by
              simpa [Functor.map_comp, hcomp] using
                (rfl :
                  (F.map (f k ≫ homOfLE (hc k))).1.app (op Y) =
                    (F.map (f k ≫ homOfLE (hc k))).1.app (op Y))]
        rw [Category.assoc]
        simp_rw [show
            ((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v) =
              ((F.obj (b k)).1.map g.op) (((F.map (f k)).1.app (op Z)) v) by
                simpa using
                  sheaf_transition_app_map_eq_map_app
                    (β := β)
                    (F := F)
                    (f := f k)
                    (g := g)
                    (a := v)]
        simpa [Function.comp] using
          sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE (hc k))
            (g := g)
            (a := ((F.map (f k)).1.app (op Z)) v)
      have hstage :
          ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u)) =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v)) := by
        exact congrArg (((F.map (homOfLE (hc k))).1.app (op Y))) (hf k)
      exact hu.trans (hstage.trans hv.symm)
    have huv : u' = v' := by
      apply hsheafT.isSeparatedFor.ext
      intro Y g hg
      exact hlocal' g hg
    have hu_colim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) u' := by
      -- Move the class of `u` from stage `a` to the common stage `c`.
      simpa [u'] using
        congrFun
          ((congrArg NatTrans.app
            (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac))) (op Z))
          u
    have hv_colim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) v' := by
      -- The same transport identifies the class of `v` with its common-stage image.
      simpa [v'] using
        congrFun
          ((congrArg NatTrans.app
            (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac))) (op Z))
          v
    calc
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) u' := hu_colim
      _ = ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) v' := by
            simpa [huv]
      _ = ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v := hv_colim.symm
  · -- If the covering presieve has no arrows, separatedness of the stage sheaf forces equality.
    have hsheafT : Presieve.IsSheafFor ((F.obj a).1) T := by
      exact ((Presieve.isSheaf_coverage (K := K) ((F.obj a).1)).1 (F.obj a).2) T hT
    have huv : u = v := by
      apply hsheafT.isSeparatedFor.ext
      intro Y g hg
      exact False.elim <| hne ⟨⟨⟨Y, g⟩, hg⟩⟩
    simpa [huv]

/-- Helper for Lemma 7.17.10: the presheaf colimit is separated for every `K`-covering presieve
under the small-cover cofinality hypothesis. -/
lemma presheafColimit_isSeparatedFor_of_coveringPresieveCardinal_lt_cof
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Presieve.IsSeparatedFor (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) R := by
  intro x y z₁ z₂ hz₁ hz₂
  -- Represent the two candidate amalgamations in stages and move them to one common stage.
  obtain ⟨i₁, s₁, hs₁⟩ :=
    presheafColimit_section_exists_rep (β := β) (F := F) U z₁
  obtain ⟨i₂, s₂, hs₂⟩ :=
    presheafColimit_section_exists_rep (β := β) (F := F) U z₂
  by_cases h12 : i₁.1 ≤ i₂.1
  · let a : Set.Iio β := i₂
    let u : (F.obj a).1.obj (op U) := ((F.map (homOfLE h12)).1.app (op U)) s₁
    let v : (F.obj a).1.obj (op U) := s₂
    have hu :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u = z₁ := by
      -- Transport the representative of `z₁` to the common stage.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i₁).app (op U)) s₁ =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u := by
        simpa [a, u] using
          (congrFun
            ((congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE h12))) (op U))
            s₁).symm
      exact hmap.symm.trans hs₁
    have hv :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v = z₂ := by
      simpa [a, v] using hs₂
    have hlocal :
        ∀ k : R.uncurry,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) u) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) v) := by
      intro k
      -- Rewrite the local colimit classes using the two amalgamation identities on `R`.
      calc
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₁ := by
            rw [← hu]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) u
        _ = x k.1.2 k.2 := hz₁ _ _
        _ = y k.1.2 k.2 := by rfl
        _ = (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₂ := (hz₂ _ _).symm
        _ =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v) := by
            rw [← hv]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) v
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v :=
      presheafColimit_local_cover_eq_implies_colimit_eq
        (β := β)
        (F := F)
        (hcover := hcover)
        (hT := hR)
        (u := u)
        (v := v)
        hlocal
    exact hu.symm.trans (hcolim.trans hv)
  · have h21 : i₂.1 ≤ i₁.1 := le_of_not_ge h12
    let a : Set.Iio β := i₁
    let u : (F.obj a).1.obj (op U) := s₁
    let v : (F.obj a).1.obj (op U) := ((F.map (homOfLE h21)).1.app (op U)) s₂
    have hu :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u = z₁ := by
      simpa [a, u] using hs₁
    have hv :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v = z₂ := by
      -- Transport the representative of `z₂` to the common stage.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i₂).app (op U)) s₂ =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v := by
        simpa [a, v] using
          (congrFun
            ((congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE h21))) (op U))
            s₂).symm
      exact hmap.symm.trans hs₂
    have hlocal :
        ∀ k : R.uncurry,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) u) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) v) := by
      intro k
      -- The local compatibility is again just the equality of the two amalgamations on `R`.
      calc
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₁ := by
            rw [← hu]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) u
        _ = x k.1.2 k.2 := hz₁ _ _
        _ = y k.1.2 k.2 := by rfl
        _ = (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₂ := (hz₂ _ _).symm
        _ =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v) := by
            rw [← hv]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) v
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v :=
      presheafColimit_local_cover_eq_implies_colimit_eq
        (β := β)
        (F := F)
        (hcover := hcover)
        (hT := hR)
        (u := u)
        (v := v)
        hlocal
    exact hu.symm.trans (hcolim.trans hv)

/-- Helper for Lemma 7.17.10: any `< β.cof`-small family of stagewise representatives in the
presheaf colimit can be transported to one common ordinal stage without changing its colimit
image. -/
lemma presheafColimit_common_stage_of_small_sections
    {ι : Type (max u v)} {X : ι → C}
    (x : ∀ i, (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op (X i)))
    (b : ι → Set.Iio β)
    (t : ∀ i, (F.obj (b i)).1.obj (op (X i)))
    (ht :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) (b i)).app (op (X i))) (t i) =
          x i)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ a : Set.Iio β, ∃ s : ∀ i, (F.obj a).1.obj (op (X i)),
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (X i))) (s i) = x i := by
  -- Choose one ordinal stage dominating all local representatives, then transport each section
  -- there using the colimit cocone relation.
  obtain ⟨a, ha⟩ :=
    coveringPresieve_common_stage_of_small_family
      (β := β)
      (F := F)
      (f := fun i ↦ (b i).1)
      (hf := fun i ↦ (b i).2)
      (hι := hι)
  let s : ∀ i, (F.obj a).1.obj (op (X i)) := fun i ↦
    ((F.map (homOfLE (ha i))).1.app (op (X i))) (t i)
  refine ⟨a, s, ?_⟩
  intro i
  have hmap :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) (b i)).app (op (X i))) (t i) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (X i))) (s i) := by
    -- The colimit cocone identifies the old representative with its transport to the common
    -- stage.
    simpa [s] using
      (congrFun
        ((congrArg NatTrans.app
          (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE (ha i)))) (op (X i)))
        (t i)).symm
  exact hmap.symm.trans (ht i)

/-- Helper for Lemma 7.17.10: once a compatible family is represented in one ordinal stage, any
`< β.cof`-small family of overlap equalities can be synchronized in one later stage. -/
lemma presheafColimit_common_stage_of_small_overlaps
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {a : Set.Iio β}
    (s : ∀ i : R.uncurry, (F.obj a).1.obj (op i.1.1))
    (hs_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op i.1.1)) (s i) = x i)
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q, Z q ⟶ (left q).1.1)
    (gr : ∀ q, Z q ⟶ (right q).1.1)
    (hcomm : ∀ q, gl q ≫ (left q).1.2 = gr q ≫ (right q).1.2)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ c : Set.Iio β, ∃ v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1),
      (∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i) ∧
      ∀ q,
        ((F.obj c).1.map (gl q).op) (v (left q)) =
          ((F.obj c).1.map (gr q).op) (v (right q)) := by
  by_cases hne : Nonempty ι
  · -- First upgrade each prescribed overlap equality from the colimit to some later stage.
    choose b f hf using
      fun q : ι ↦
        presheafColimit_section_eq_at_later_stage
          (β := β)
          (F := F)
          (U := Z q)
          (i := a)
          (s := ((F.obj a).1.map (gl q).op) (s (left q)))
          (t := ((F.obj a).1.map (gr q).op) (s (right q)))
          (h := by
            calc
              ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (Z q)))
                  (((F.obj a).1.map (gl q).op) (s (left q))) =
                (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gl q).op (x (left q)) := by
                  rw [← hs_image (left q)]
                  simpa [Functor.comp_map, Category.assoc] using
                    congrFun
                      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                        (gl q).op)
                      (s (left q))
              _ =
                (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gr q).op (x (right q)) := by
                  exact hx (left q) (right q) (Z q) (gl q) (gr q) (hcomm q)
              _ =
                ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (Z q)))
                  (((F.obj a).1.map (gr q).op) (s (right q))) := by
                  rw [← hs_image (right q)]
                  simpa [Functor.comp_map, Category.assoc] using
                    congrFun
                      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                        (gr q).op)
                      (s (right q))).symm
    -- Next dominate all witness stages by a single later stage.
    obtain ⟨c, hc⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun q : ι ↦ (b q).1)
        (hf := fun q ↦ (b q).2)
        (hι := hι)
    obtain ⟨q₀⟩ := hne
    have hac : a.1 ≤ c.1 := by
      exact le_trans (leOfHom (f q₀)) (hc q₀)
    let v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hac)).1.app (op i.1.1)) (s i)
    refine ⟨c, v, ?_, ?_⟩
    · intro i
      -- Transporting each representative to the common stage leaves its colimit class unchanged.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op i.1.1)) (s i) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) := by
        simpa [v] using
          (congrFun
            ((congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac)))
              (op i.1.1))
            (s i)).symm
      exact hmap.symm.trans (hs_image i)
    · intro q
      -- Rewrite both sides through the stage `b q`, where the overlap equality is already valid.
      have hcomp :
          f q ≫ homOfLE (hc q) = homOfLE hac := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj c).1.map (gl q).op) (v (left q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) := by
        simpa [v] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hac)
            (g := gl q)
            (a := s (left q))).symm
      have hright :
          ((F.obj c).1.map (gr q).op) (v (right q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) := by
        simpa [v] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hac)
            (g := gr q)
            (a := s (right q))).symm
      have hleft' :
          ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) := by
        simpa [Functor.map_comp, Function.comp, hcomp]
      have hright' :
          ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := by
        simpa [Functor.map_comp, Function.comp, hcomp]
      have hstage :
          ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := by
        exact congrArg (((F.map (homOfLE (hc q))).1.app (op (Z q)))) (hf q)
      calc
        ((F.obj c).1.map (gl q).op) (v (left q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) := hleft
        _ =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) := hleft'
        _ =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := hstage
        _ =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) := hright'.symm
        _ = ((F.obj c).1.map (gr q).op) (v (right q)) := hright.symm
  · -- If there are no overlap constraints, the original common stage already works.
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    refine ⟨a, s, hs_image, ?_⟩
    intro q
    exact isEmptyElim q

/-- Helper for Lemma 7.17.10: once the local family has been synchronized to one stage, any
overlap relation already holds after applying the stage injection into the presheaf colimit. -/
lemma presheafColimit_overlap_eq_in_colimit
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {c : Set.Iio β}
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i)
    {i j : R.uncurry} {Z : C}
    (gi : Z ⟶ i.1.1) (gj : Z ⟶ j.1.1)
    (hcomm : gi ≫ i.1.2 = gj ≫ j.1.2) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gi.op) (v i)) =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gj.op) (v j)) := by
  -- Rewrite both stage-`c` restrictions through their prescribed colimit images and then apply the
  -- original compatibility of the family `x`.
  calc
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gi.op) (v i)) =
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map gi.op (x i) := by
        rw [← hv_image i]
        simpa [Functor.comp_map, Category.assoc] using
          congrFun
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality gi.op)
            (v i)
    _ =
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map gj.op (x j) := by
        exact hx i j Z gi gj hcomm
    _ =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gj.op) (v j)) := by
        rw [← hv_image j]
        simpa [Functor.comp_map, Category.assoc] using
          (congrFun
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality gj.op)
            (v j)).symm

/-- Helper for Lemma 7.17.10: the sigma refinement built from the chosen pullback covers is a
covering sieve for the Grothendieck topology generated by `K`. -/
lemma sigma_refinement_generate_mem_toGrothendieck
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1) :
    Sieve.generate
        (Presieve.bindOfArrows
          (fun i : R.uncurry ↦ i.1.1)
          (fun i ↦ i.1.2)
          T) ∈ J U := by
  -- First view the base cover and each chosen pullback cover as covering sieves in `J`.
  have huncurry :
      Sieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) = Sieve.generate R := by
    refine Sieve.ext fun Y g ↦ ?_
    constructor
    · intro hg
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨i, a, rfl⟩
      exact ⟨i.1.1, a, i.1.2, i.2, rfl⟩
    · intro hg
      rcases hg with ⟨W, a, b, hb, rfl⟩
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨⟨⟨W, b⟩, hb⟩, a, rfl⟩
  have hbase :
      Sieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) ∈ J U := by
    have hgen_pre : Sieve.generate R ∈ K.toPrecoverage.toGrothendieck U := by
      exact Precoverage.generate_mem_toGrothendieck hR
    have hgen : Sieve.generate R ∈ K.toGrothendieck U := by
      rw [Coverage.mem_toGrothendieck]
      rw [Precoverage.mem_toGrothendieck_iff] at hgen_pre
      exact (K.saturate_iff_saturate_toPrecoverage).2 hgen_pre
    simpa [huncurry] using hgen
  have hlocal :
      ∀ i : R.uncurry, Sieve.generate (T i) ∈ J i.1.1 := by
    intro i
    have hgen_pre : Sieve.generate (T i) ∈ K.toPrecoverage.toGrothendieck i.1.1 := by
      exact Precoverage.generate_mem_toGrothendieck (hT i)
    rw [Coverage.mem_toGrothendieck]
    rw [Precoverage.mem_toGrothendieck_iff] at hgen_pre
    exact (K.saturate_iff_saturate_toPrecoverage).2 hgen_pre
  -- Then the Grothendieck-topology bind construction promotes the whole sigma refinement.
  exact GrothendieckTopology.bindOfArrows J hbase hlocal

/-- Helper for Lemma 7.17.10: the sigma refinement factors through the original covering
presieve. -/
lemma sigma_refinement_factors_thru
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1) :
    (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T).FactorsThru R := by
  -- Every sigma-refinement arrow is literally a composite through one base arrow in `R`.
  intro Z g hg
  rcases hg with ⟨i, k, hk⟩
  exact ⟨i.1.1, k, i.1.2, i.2, rfl⟩

/-- Helper for Lemma 7.17.10: each chosen pullback cover factors through the sigma refinement
along its base arrow. -/
lemma pullback_cover_factors_thru_sigma_refinement
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (i : R.uncurry) :
    (T i).FactorsThruAlong
      (Presieve.bindOfArrows
        (fun j : R.uncurry ↦ j.1.1)
        (fun j ↦ j.1.2)
        T)
      i.1.2 := by
  -- Each arrow in `T i` becomes an arrow of the sigma refinement by adjoining the branch index `i`.
  intro Z g hg
  refine ⟨Z, 𝟙 Z, g ≫ i.1.2, ?_, by simp⟩
  change
    (Presieve.bindOfArrows
      (fun j : R.uncurry ↦ j.1.1)
      (fun j ↦ j.1.2)
      T)
      (g ≫ i.1.2)
  simpa using
    (Presieve.bindOfArrows.mk
      (Y := fun j : R.uncurry ↦ j.1.1)
      (f := fun j ↦ j.1.2)
      (R := T)
      i
      g
      hg)

/-- Helper for Lemma 7.17.10: the sigma refinement can be presented by the explicit family of
composite arrows indexed by the uncurry types of the branch covers. -/
lemma sigma_refinement_eq_ofArrows
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1) :
    Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T =
      Presieve.ofArrows
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
        (fun q ↦ q.2.1.2 ≫ q.1.1.2) := by
  -- Rewrite each branch cover by its own `uncurry` arrow family, then apply the owner lemma for
  -- binding explicit arrow families.
  calc
    Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T =
      Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        (fun i ↦ Presieve.ofArrows (fun j : (T i).uncurry ↦ j.1.1) (fun j ↦ j.1.2)) := by
          congr
          funext i
          simpa using (presieve_eq_of_uncurry (β := β) (hcover := hcover) (R := T i))
    _ =
      Presieve.ofArrows
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
        (fun q ↦ q.2.1.2 ≫ q.1.1.2) := by
          simpa using
            (Presieve.bindOfArrows_ofArrows
              (X := fun i : R.uncurry ↦ i.1.1)
              (f := fun i ↦ i.1.2)
              (Y := fun i : R.uncurry ↦ fun j : (T i).uncurry ↦ j.1.1)
              (g := fun i : R.uncurry ↦ fun j : (T i).uncurry ↦ j.1.2))

/-- Helper for Lemma 7.17.10: restricting a compatible family on the base cover along the explicit
sigma-refinement arrows preserves compatibility in the presheaf colimit. -/
lemma presheafColimit_sigma_refinement_target_compatible
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (π : ∀ q : ι, Z q ⟶ U)
    (hπ : ∀ q, π q = gl q ≫ (left q).1.2)
    (x : ∀ i : R.uncurry, P.obj (op i.1.1))
    (hx : Presieve.Arrows.Compatible P (fun i : R.uncurry ↦ i.1.2) x) :
    Presieve.Arrows.Compatible P π (fun q : ι ↦ P.map (gl q).op (x (left q))) := by
  intro q₁ q₂ W r₁ r₂ h
  -- Expand the refinement arrows into their composites with the base cover and reuse the original
  -- compatibility of `x` on `R`.
  have hbase :
      (r₁ ≫ gl q₁) ≫ (left q₁).1.2 = (r₂ ≫ gl q₂) ≫ (left q₂).1.2 := by
    simpa [hπ q₁, hπ q₂, Category.assoc] using h
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using
    hx (left q₁) (left q₂) W (r₁ ≫ gl q₁) (r₂ ≫ gl q₂) hbase

/-- Helper for Lemma 7.17.10: the synchronized stage family maps to the induced sigma-refinement
family in the presheaf colimit after restricting along each refinement arrow. -/
lemma presheafColimit_sigma_refinement_image
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i) :
    ∀ q : ι,
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op (Z q)))
          (((F.obj c).1.map (gl q).op) (v (left q))) =
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gl q).op (x (left q)) := by
  intro q
  -- Rewrite the colimit class of the restricted stage section through the prescribed image of the
  -- base branch section.
  rw [← hv_image (left q)]
  simpa [Functor.comp_map, Category.assoc] using
    congrFun
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality (gl q).op)
      (v (left q))

/-- Helper for Lemma 7.17.10: once a section `tc` of the stage sheaf `(F.obj c).1` glues the
synchronized family `v` on the original cover `R`, its image in the presheaf colimit amalgamates
the original family `x`. -/
lemma presheafColimit_stage_glue_image_is_amalgamation
    {U : C} {R : Presieve U}
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i)
    (tc : (F.obj c).1.obj (op U))
    (htc : ∀ i : R.uncurry, ((F.obj c).1.map i.1.2.op) tc = v i) :
    let z := ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op U)) tc
    ∀ i : R.uncurry, (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map i.1.2.op z = x i := by
  intro z i
  -- Evaluate the colimit class of `tc` along the `i`-th branch and then rewrite using the stage
  -- gluing identity `htc` and the prescribed colimit image `hv_image`.
  dsimp [z]
  rw [← hv_image i, ← htc i]
  simpa [Functor.comp_map, Category.assoc] using
    congrFun
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality i.1.2.op)
      tc

/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of secondary branch equalities can be
synchronized to one common later stage while preserving the prescribed colimit images of the base
family. -/
lemma presheafColimit_common_stage_of_secondary_branch_equalities
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i)
    (B : ∀ q : ι, Presieve (Z q))
    (hκsmall : Cardinal.lift (Cardinal.mk (Σ q : ι, (B q).uncurry)) < β.cof)
    (hstage_witness :
      ∀ p : Σ q : ι, (B q).uncurry,
        ∃ d : Set.Iio β, ∃ f : c ⟶ d,
          ((F.map f).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) =
            ((F.map f).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1)))) :
    ∃ d : Set.Iio β,
      ∃ v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1),
        (∀ i,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) =
            x i) ∧
        (∀ p : Σ q : ι, (B q).uncurry,
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1))) := by
  let κ : Type (max u v) := Σ q : ι, (B q).uncurry
  -- Choose one later-stage witness for each secondary branch equality.
  choose b f hf using fun p : κ ↦ hstage_witness p
  by_cases hκne : Nonempty κ
  · -- Synchronize all secondary branch equalities in one common later stage `d`.
    obtain ⟨d, hd⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun p : κ ↦ (b p).1)
        (hf := fun p ↦ (b p).2)
        (hι := by simpa [κ] using hκsmall)
    obtain ⟨p₀⟩ := hκne
    have hcd : c.1 ≤ d.1 := by
      exact le_trans (leOfHom (f p₀)) (hd p₀)
    let v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)
    have hbranch_d :
        ∀ p : κ,
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)) := by
      intro p
      have hcomp : f p ≫ homOfLE (hd p) = homOfLE hcd := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) := by
        -- Rewrite the transported left branch by moving the restriction across the stage map.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := p.2.1.2 ≫ gl p.1)
            (a := v (left p.1))).symm
      have hright :
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1))) := by
        -- The same transport rewrite applies to the right branch.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := p.2.1.2 ≫ gr p.1)
            (a := v (right p.1))).symm
      have hstage :
          ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1))) := by
        -- Factor the common transport through the local witness stage `b p`.
        rw [show homOfLE hcd = f p ≫ homOfLE (hd p) by simpa using hcomp.symm]
        simpa [Functor.map_comp, Function.comp, hf p]
      exact hleft.trans (hstage.trans hright.symm)
    refine ⟨d, v', ?_, hbranch_d⟩
    intro i
    -- Transporting the synchronized family `v` to the common stage preserves its colimit image.
    have hmap :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1))
            (v' i) := by
      simpa [v'] using
        (congrFun
          ((congrArg NatTrans.app
            (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hcd)))
            (op i.1.1))
          (v i)).symm
    exact hmap.symm.trans (hv_image i)
  · -- If the secondary owner family is empty, the original synchronized stage already works.
    haveI : IsEmpty κ := not_nonempty_iff.mp hκne
    refine ⟨c, v, hv_image, ?_⟩
    intro p
    exact isEmptyElim p

/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of already-targeted branch comparisons can
be synchronized to one later stage without introducing another descent cover, together with the
transition map from the original synchronized stage. -/
lemma presheafColimit_common_stage_of_targeted_secondary_branch_equalities
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) = x i)
    (hιsmall : Cardinal.lift (Cardinal.mk ι) < β.cof)
    (hstage_witness :
      ∀ q : ι,
        ∃ d : Set.Iio β, ∃ f : c ⟶ d,
          ((F.map f).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) =
            ((F.map f).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q)))) :
    ∃ d : Set.Iio β,
      ∃ hcd : c.1 ≤ d.1,
        ∃ v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1),
          (∀ i,
            v' i = ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)) ∧
          (∀ i,
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) =
              x i) ∧
          (∀ q : ι,
            ((F.obj d).1.map (gl q).op) (v' (left q)) =
              ((F.obj d).1.map (gr q).op) (v' (right q))) := by
  -- Synchronize the explicit targeted branch witnesses exactly as in the untargeted case, but
  -- with no second descent cover because the right-hand comparison branch is already part of the
  -- owner data.
  choose b f hf using hstage_witness
  by_cases hιne : Nonempty ι
  · -- One common stage dominates every targeted comparison witness.
    obtain ⟨d, hd⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun q : ι ↦ (b q).1)
        (hf := fun q ↦ (b q).2)
        (hι := hιsmall)
    obtain ⟨q₀⟩ := hιne
    have hcd : c.1 ≤ d.1 := by
      exact le_trans (leOfHom (f q₀)) (hd q₀)
    let v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)
    have htarget_d :
        ∀ q : ι,
          ((F.obj d).1.map (gl q).op) (v' (left q)) =
            ((F.obj d).1.map (gr q).op) (v' (right q)) := by
      intro q
      have hcomp : f q ≫ homOfLE (hd q) = homOfLE hcd := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj d).1.map (gl q).op) (v' (left q)) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) := by
        -- Move the left restriction across the common transport to the synchronized stage.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := gl q)
            (a := v (left q))).symm
      have hright :
          ((F.obj d).1.map (gr q).op) (v' (right q)) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q))) := by
        -- The same transport rewrite applies to the targeted right branch.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := gr q)
            (a := v (right q))).symm
      have hstage :
          ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q))) := by
        -- Factor the common transport through the witness stage chosen for this targeted branch.
        rw [show homOfLE hcd = f q ≫ homOfLE (hd q) by simpa using hcomp.symm]
        simpa [Functor.map_comp, Function.comp, hf q]
      exact hleft.trans (hstage.trans hright.symm)
    refine ⟨d, hcd, v', ?_, ?_, htarget_d⟩
    · intro i
      rfl
    · intro i
      -- Transporting the synchronized family to the common stage preserves each colimit class.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op i.1.1)) (v i) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1))
              (v' i) := by
        simpa [v'] using
          (congrFun
            ((congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hcd)))
              (op i.1.1))
            (v i)).symm
      exact hmap.symm.trans (hv_image i)
  · -- If there are no targeted comparisons, the existing synchronized stage already works.
    haveI : IsEmpty ι := not_nonempty_iff.mp hιne
    refine ⟨c, le_rfl, v, ?_, hv_image, ?_⟩
    · intro i
      rfl
    · intro q
      exact isEmptyElim q

/-- Helper for Lemma 7.17.10: once the secondary branch equalities have been synchronized to one
stage, sheaf separatedness on each secondary pullback cover descends them to the first-level
overlap equalities. -/
lemma presheafColimit_secondary_cover_eq_at_common_stage
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (B : ∀ q : ι, Presieve (Z q))
    (hB : ∀ q, B q ∈ K (Z q))
    (hbranch_d :
      ∀ p : Σ q : ι, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1))) :
    ∀ q : ι,
      ((F.obj d).1.map (gl q).op) (v' (left q)) =
        ((F.obj d).1.map (gr q).op) (v' (right q)) := by
  intro q
  have hBd : Presieve.IsSheafFor ((F.obj d).1) (B q) := by
    -- Descend the synchronized branch equalities along the chosen secondary cover `B q`.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj d).1)).1 (F.obj d).2) (B q) (hB q)
  apply hBd.isSeparatedFor.ext
  intro Y g hg
  let p : Σ q : ι, (B q).uncurry := ⟨q, ⟨⟨Y, g⟩, hg⟩⟩
  simpa [p, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using hbranch_d p

/-- Helper for Lemma 7.17.10: normalizing the two chosen pullback factorizations identifies the
resulting overlap equality over the base object. -/
lemma pullback_branch_factorization_base_eq
    {U : C} {R : Presieve U}
    {r j k : R.uncurry}
    {W Y A : C}
    {gr' : W ⟶ r.1.1} {hj' : W ⟶ j.1.1}
    {g : Y ⟶ W} {i : Y ⟶ A} {e : A ⟶ r.1.1} {i' : A ⟶ k.1.1}
    (hie : g ≫ gr' = i ≫ e)
    (hi'e' : e ≫ r.1.2 = i' ≫ k.1.2)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2) :
    (i ≫ i') ≫ k.1.2 = (g ≫ hj') ≫ j.1.2 := by
  -- Reassociate the two branch factorizations until both sides are written over the same base
  -- composite to `U`.
  calc
    (i ≫ i') ≫ k.1.2 = i ≫ (e ≫ r.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ i ≫ t) hi'e'.symm
    _ = (i ≫ e) ≫ r.1.2 := by simp [Category.assoc]
    _ = (g ≫ gr') ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.1.2) hie.symm
    _ = g ≫ (hj' ≫ j.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) hW
    _ = (g ≫ hj') ≫ j.1.2 := by simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once the first-level pullback equalities have been synchronized at
one stage, the remaining gap is to descend them to genuine overlap compatibility on the original
cover. -/
lemma pullback_branch_restriction_eq_of_first_level_equality
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    {r : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1)
    (he : T r e)
    (hie : g ≫ gr' = i ≫ e) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((F.obj d).1.map g.op) (((F.obj d).1.map gr'.op) (v' r)) =
      ((F.obj d).1.map (i ≫ gr q).op) (v' (right q)) := by
  -- Rewrite the restricted branch through the synchronized first-level equality indexed by `e`.
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  have hq := hfirst q
  have hi := congrArg (((F.obj d).1.map i.op)) hq
  -- Normalizing both composites isolates the concrete branch map that will later be compared to
  -- the target overlap branch.
  simpa [q, FunctorToTypes.map_comp_apply, hie]
    using hi

/-- Helper for Lemma 7.17.10: first-level pullback equalities transport unchanged to any later
ordinal stage obtained by a single transition map. -/
lemma stage_family_first_level_pullback_equalities_at_later_stage
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {d e : Set.Iio β}
    (hde : d.1 ≤ e.1)
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q))) :
    ∀ q : Σ i : R.uncurry, (T i).uncurry,
      ((F.obj e).1.map q.2.1.2.op)
          (((F.map (homOfLE hde)).1.app (op q.1.1.1)) (v' q.1)) =
        ((F.obj e).1.map (gr q).op)
          (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) := by
  intro q
  -- Push the first-level equality forward along the transition map and commute restrictions with
  -- that transition on both sides.
  calc
    ((F.obj e).1.map q.2.1.2.op)
        (((F.map (homOfLE hde)).1.app (op q.1.1.1)) (v' q.1)) =
      ((F.map (homOfLE hde)).1.app (op q.2.1.1))
        (((F.obj d).1.map q.2.1.2.op) (v' q.1)) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := q.2.1.2)
              (a := v' q.1)).symm
    _ =
      ((F.map (homOfLE hde)).1.app (op q.2.1.1))
        (((F.obj d).1.map (gr q).op) (v' (right q))) := by
          exact congrArg (((F.map (homOfLE hde)).1.app (op q.2.1.1))) (hfirst q)
    _ =
      ((F.obj e).1.map (gr q).op)
        (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := gr q)
              (a := v' (right q))).symm

/-- Helper for Lemma 7.17.10: the synchronized anonymous base-cover equalities also transport
unchanged to any later ordinal stage obtained by a single transition map. -/
lemma stage_family_base_cover_owner_equalities_at_later_stage
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry)
    (baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1)
    {d e : Set.Iio β}
    (hde : d.1 ≤ e.1)
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hbase :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj d).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map (baseGr s).op) (v' (baseRight s))) :
    ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
      let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
      ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op)
          (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) =
        ((F.obj e).1.map (baseGr s).op)
          (((F.map (homOfLE hde)).1.app (op (baseRight s).1.1)) (v' (baseRight s))) := by
  intro s
  let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
  -- Push the anonymous base-cover equality forward along the later-stage transition and commute
  -- the two restrictions with that transport on both sides.
  calc
    ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op)
        (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) =
      ((F.map (homOfLE hde)).1.app (op s.2.1.1))
        (((F.obj d).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (v' (right q))) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q)
              (a := v' (right q))).symm
    _ =
      ((F.map (homOfLE hde)).1.app (op s.2.1.1))
        (((F.obj d).1.map (baseGr s).op) (v' (baseRight s))) := by
          exact congrArg (((F.map (homOfLE hde)).1.app (op s.2.1.1))) (hbase s)
    _ =
      ((F.obj e).1.map (baseGr s).op)
        (((F.map (homOfLE hde)).1.app (op (baseRight s).1.1)) (v' (baseRight s))) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := baseGr s)
              (a := v' (baseRight s))).symm

/-- Helper for Lemma 7.17.10: each branch of a retained secondary pullback cover can be refined to
one branch of the original covering family at the synchronized stage, while keeping track of the
base composite to `U`. -/
lemma stage_family_secondary_branch_refines_to_cover_branch
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hBfac : ∀ q, (B q).FactorsThruAlong (T q.1) q.2.1.2)
    (hbranch_d :
      ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ p.1.2.1.2).op) (v' p.1.1) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)))
    {r : R.uncurry} {A : C} (e : A ⟶ r.1.1) (he : T r e)
    (m : (B ⟨r, ⟨⟨A, e⟩, he⟩⟩).uncurry) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ k : R.uncurry, ∃ t : m.1.1 ⟶ k.1.1,
      ((F.obj d).1.map (m.1.2 ≫ gr q).op) (v' (right q)) =
        ((F.obj d).1.map t.op) (v' k) ∧
      t ≫ k.1.2 = (m.1.2 ≫ e) ≫ r.1.2 := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hBfac q m.2
  let q' : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A', e'⟩, he'⟩⟩
  let k : R.uncurry := right q'
  have hbranch_q :
      ((F.obj d).1.map (m.1.2 ≫ e).op) (v' r) =
        ((F.obj d).1.map (m.1.2 ≫ gr q).op) (v' (right q)) := by
    -- Evaluate the retained synchronized secondary equality on the concrete branch `m`.
    simpa [q] using hbranch_d ⟨q, m⟩
  have hstage_q' :
      ((F.obj d).1.map (m.1.2 ≫ e).op) (v' r) =
        ((F.obj d).1.map (i' ≫ gr q').op) (v' k) := by
    -- Push the first-level equality for the factorized branch `q'` across the factorization map
    -- `i' : m.1.1 ⟶ A'`.
    have hi := congrArg (((F.obj d).1.map i'.op)) (hfirst q')
    simpa [q', k, FunctorToTypes.map_comp_apply, Category.assoc, hi'e'] using hi
  refine ⟨k, i' ≫ gr q', hbranch_q.symm.trans hstage_q', ?_⟩
  -- The refined branch keeps the same composite to `U` as the original secondary branch.
  calc
    (i' ≫ gr q') ≫ k.1.2 = i' ≫ (gr q' ≫ k.1.2) := by simp [Category.assoc]
    _ = i' ≫ (e' ≫ r.1.2) := by
          simpa [q', k] using congrArg (fun t ↦ i' ≫ t) (hcomm q').symm
    _ = (i' ≫ e') ≫ r.1.2 := by simp [Category.assoc]
    _ = (m.1.2 ≫ e) ≫ r.1.2 := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.1.2) hi'e'

/-- Helper for Lemma 7.17.10: after pulling a retained secondary cover back along the outer
factorization map, each transported branch still refines to one original cover branch, and the
refined branch keeps the same composite to `U` as the fixed overlap branch. -/
lemma stage_family_pulled_back_secondary_branch_refines_to_cover_branch
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hBfac : ∀ q, (B q).FactorsThruAlong (T q.1) q.2.1.2)
    (hbranch_d :
      ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ p.1.2.1.2).op) (v' p.1.1) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong (B ⟨r, ⟨⟨A, e⟩, he⟩⟩) i) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∀ n : D.uncurry,
      ∃ k : R.uncurry, ∃ t : n.1.1 ⟶ k.1.1,
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map t.op) (v' k) ∧
        t ≫ k.1.2 = ((n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  intro n
  rcases n with ⟨u, hu⟩
  rcases u with ⟨Y', g'⟩
  have hDbranch :
      ∃ (A' : C) (i' : Y' ⟶ A') (e' : A' ⟶ A),
        B q e' ∧ i' ≫ e' = g' ≫ i := by
    exact hDfac hu
  obtain ⟨A', i', e', he', hi'e'⟩ := hDbranch
  let m : (B q).uncurry := ⟨⟨A', e'⟩, he'⟩
  obtain ⟨k, t, hstage, hbase⟩ :=
    stage_family_secondary_branch_refines_to_cover_branch
      (K := K)
      (hcover := hcover)
      (β := β)
      (F := F)
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (v' := v')
      (hfirst := hfirst)
      (B := B)
      (hBfac := hBfac)
      (hbranch_d := hbranch_d)
      (r := r)
      (e := e)
      (he := he)
      (m := m)
  refine ⟨k, i' ≫ t, ?_, ?_⟩
  · -- Transport the stage equality from the retained secondary branch to the pulled-back branch.
    have hi := congrArg (((F.obj d).1.map i'.op)) hstage
    simpa [FunctorToTypes.map_comp_apply, q, m, Category.assoc, hi'e'] using hi
  · -- Normalize the two factorizations until both branches are written over the same overlap.
    have hbranch_base :
        (g' ≫ g) ≫ gr' = i' ≫ (e' ≫ e) := by
      calc
        (g' ≫ g) ≫ gr' = g' ≫ (g ≫ gr') := by simp [Category.assoc]
        _ = g' ≫ (i ≫ e) := by
              simpa using congrArg (fun t ↦ g' ≫ t) hie
        _ = (g' ≫ i) ≫ e := by simp [Category.assoc]
        _ = (i' ≫ e') ≫ e := by
              simpa [Category.assoc] using congrArg (fun t ↦ t ≫ e) hi'e'
        _ = i' ≫ (e' ≫ e) := by simp [Category.assoc]
    have hbase_to_j :
        (i' ≫ t) ≫ k.1.2 = ((g' ≫ g) ≫ hj') ≫ j.1.2 := by
      simpa [Category.assoc] using
        pullback_branch_factorization_base_eq
          (r := r)
          (j := j)
          (k := k)
          (gr' := gr')
          (hj' := hj')
          (g := g' ≫ g)
          (i := i')
          (e := e' ≫ e)
          (i' := t)
          (hie := hbranch_base)
          (hi'e' := hbase.symm)
          (hW := hW)
    simpa [Category.assoc] using hbase_to_j

/-- Helper for Lemma 7.17.10: once the first-level pullback equalities have been synchronized at
one stage, the remaining gap is to descend them to genuine overlap compatibility on the original
cover. -/
lemma stage_family_targeted_secondary_target_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (D : Presieve Y)
    (hD : D ∈ K Y)
    (htarget :
      ∀ n : D.uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((F.obj d).1.map (i ≫ gr q).op) (v' (right q)) =
      ((F.obj d).1.map (g ≫ hj').op) (v' j) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  have hDd : Presieve.IsSheafFor ((F.obj d).1) D := by
    -- The synchronized stage is still a sheaf on the pulled-back secondary cover.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj d).1)).1 (F.obj d).2) D hD
  apply hDd.isSeparatedFor.ext
  intro X n hn
  let p : D.uncurry := ⟨⟨X, n⟩, hn⟩
  -- Evaluate the targeted branchwise equality on the concrete branch of the pulled-back cover.
  simpa [q, p, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htarget p

/-- Helper for Lemma 7.17.10: after pulling a retained secondary branch back along the outer
factorization, the refined branch still has the same composite to `U` as the fixed overlap branch
`j`. -/
lemma pulled_back_secondary_branch_base_eq_to_fixed_overlap
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    (B : Presieve A)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ m : B.uncurry, ∃ i' : n.1.1 ⟶ m.1.1,
      i' ≫ m.1.2 = n.1.2 ≫ i ∧
      ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  rcases n with ⟨⟨Y', g'⟩, hg'⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hDfac hg'
  let m : B.uncurry := ⟨⟨A', e'⟩, he'⟩
  refine ⟨m, i', ?_, ?_⟩
  · simpa [m] using hi'e'
  -- Reassociate the pulled-back secondary branch until it matches the fixed overlap branch over
  -- the common base object `U`.
  calc
    ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 =
        (i' ≫ m.1.2) ≫ (gr q ≫ (right q).1.2) := by simp [Category.assoc]
    _ = (g' ≫ i) ≫ (gr q ≫ (right q).1.2) := by
          simpa [m, Category.assoc] using congrArg (fun t ↦ t ≫ (gr q ≫ (right q).1.2)) hi'e'
    _ = (g' ≫ i) ≫ (e ≫ r.1.2) := by
          simpa [q] using congrArg (fun t ↦ (g' ≫ i) ≫ t) (hcomm q).symm
    _ = ((g' ≫ i) ≫ e) ≫ r.1.2 := by simp [Category.assoc]
    _ = ((g' ≫ g) ≫ gr') ≫ r.1.2 := by
          simpa [Category.assoc] using congrArg (fun t ↦ (g' ≫ t) ≫ r.1.2) hie.symm
    _ = (g' ≫ g) ≫ (hj' ≫ j.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (g' ≫ g) ≫ t) hW
    _ = ((g' ≫ g ≫ hj') ≫ j.1.2) := by simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once the pulled-back owner branch has been matched with the outer
factorization `i`, the fixed-overlap base equality can be rewritten directly on the source of the
pulled-back branch. -/
lemma pulled_back_secondary_branch_base_eq_to_fixed_overlap_normalized
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {r j : R.uncurry} {Y A : C}
    (hj' : Y ⟶ j.1.1)
    (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    {B : Presieve A} {D : Presieve Y}
    (n : D.uncurry)
    {m : B.uncurry} {i' : n.1.1 ⟶ m.1.1}
    (hi' : i' ≫ m.1.2 = n.1.2 ≫ i)
    (hbase :
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
      ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((n.1.2 ≫ hj') ≫ j.1.2)) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) = ((n.1.2 ≫ hj') ≫ j.1.2) := by
  -- This is only the associativity/rewriting step isolated from the later same-stage descent.
  simpa [Category.assoc, hi'] using hbase

/-- Helper for Lemma 7.17.10: after choosing one branch `n` of the pulled-back secondary cover,
any further precomposition `k` preserves the normalized equality of composites to the remembered
fixed overlap branch `j`. -/
lemma sigma_refinement_overlap_base_composite_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A X : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    {B : Presieve A} {D : Presieve Y}
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry)
    (k : X ⟶ n.1.1) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ m : B.uncurry,
      ∃ i' : n.1.1 ⟶ m.1.1,
        i' ≫ m.1.2 = n.1.2 ≫ i ∧
        ((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((k ≫ n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  rcases n with ⟨⟨Y', g'⟩, hg'⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hDfac hg'
  let m : B.uncurry := ⟨⟨A', e'⟩, he'⟩
  have hi' : i' ≫ m.1.2 = g' ≫ i := by
    simpa [m] using hi'e'
  refine ⟨m, i', ?_, ?_⟩
  · exact hi'
  -- Precomposing the normalized overlap equality keeps the source proof's base-composite route
  -- intact while exposing the exact transport needed for the later fixed-target descent.
  calc
    ((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 =
        (((k ≫ g') ≫ i) ≫ gr q) ≫ (right q).1.2 := by
          simpa [Category.assoc, hi']
    _ = ((k ≫ g') ≫ i) ≫ (gr q ≫ (right q).1.2) := by
          simp [Category.assoc]
    _ = ((k ≫ g') ≫ i) ≫ (e ≫ r.1.2) := by
          simpa [q] using congrArg (fun t ↦ ((k ≫ g') ≫ i) ≫ t) (hcomm q).symm
    _ = ((((k ≫ g') ≫ i) ≫ e) ≫ r.1.2) := by
          simp [Category.assoc]
    _ = ((((k ≫ g') ≫ g) ≫ gr') ≫ r.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (((k ≫ g') ≫ t) ≫ r.1.2)) hie.symm
    _ = (((k ≫ g') ≫ g) ≫ (hj' ≫ j.1.2)) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (((k ≫ g') ≫ g) ≫ t)) hW
    _ = ((k ≫ g' ≫ g ≫ hj') ≫ j.1.2) := by
          simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once a refined branch of `D` is further refined by a branch of the
fixed-target pullback cover over `j`, the resulting `T j`-branch has the same composite to `U` as
the corresponding retained secondary branch. -/
lemma fixed_target_pullback_branch_base_composite_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A X A' : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    {B : Presieve A} {D : Presieve Y}
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry)
    (k : X ⟶ n.1.1)
    (c : X ⟶ A') (e' : A' ⟶ j.1.1) (he' : T j e')
    (hc : c ≫ e' = k ≫ n.1.2 ≫ g ≫ hj') :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A', e'⟩, he'⟩⟩
    ((k ≫ n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) =
      ((c ≫ gr qj) ≫ (right qj).1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A', e'⟩, he'⟩⟩
  obtain ⟨m, i', hi', hbase⟩ :=
    sigma_refinement_overlap_base_composite_eq
      (K := K)
      (β := β)
      (hcover := hcover)
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (gr' := gr')
      (hj' := hj')
      (hW := hW)
      (g := g)
      (i := i)
      (e := e)
      (he := he)
      (hie := hie)
      (hDfac := hDfac)
      (n := n)
      (k := k)
  -- First rewrite the retained secondary branch to the normalized fixed-target overlap branch.
  calc
    ((k ≫ n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) =
        (((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2) := by
          simpa [Category.assoc, hi', q]
    _ = ((k ≫ n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
          simpa [q] using hbase
    _ = (c ≫ e' ≫ j.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ j.1.2) hc.symm
    _ = c ≫ (e' ≫ j.1.2) := by
          simp [Category.assoc]
    _ = c ≫ (gr qj ≫ (right qj).1.2) := by
          simpa [qj] using congrArg (fun t ↦ c ≫ t) (hcomm qj)
    _ = ((c ≫ gr qj) ≫ (right qj).1.2) := by
          simp [Category.assoc]

/-- Helper for Lemma 7.17.10: if a synchronized stage family still maps to the original
compatible colimit family, then every branch of a pulled-back secondary cover already compares to
the fixed overlap branch `j` in the presheaf colimit. -/
lemma presheafColimit_fixed_target_pullback_branch_eq_in_colimit
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) = x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (B : Presieve A)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong B i) :
    ∀ n : D.uncurry,
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
  intro n
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  obtain ⟨m, i', hi', hbase⟩ :=
    pulled_back_secondary_branch_base_eq_to_fixed_overlap
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (gr' := gr')
      (hj' := hj')
      (hW := hW)
      (g := g)
      (i := i)
      (e := e₀)
      (he := he)
      (hie := hie)
      (B := B)
      (D := D)
      (hDfac := hDfac)
      n
  -- Compare the two branches directly in the presheaf colimit, now that both composites to `U`
  -- have been normalized against the fixed target branch `j`.
  have hcolim :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (((i' ≫ m.1.2) ≫ gr q)).op) (v' (right q))) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
    exact
      presheafColimit_overlap_eq_in_colimit
        (β := β)
        (F := F)
        (x := x)
        (hx := hx)
        (v := v')
        (hv_image := hv_image)
        (((i' ≫ m.1.2) ≫ gr q))
        (n.1.2 ≫ g ≫ hj')
        hbase
  simpa [Category.assoc, q, hi'] using hcolim

/-- Helper for Lemma 7.17.10: for one fixed overlap pair and one pulled-back secondary cover, the
fixed-target branchwise colimit equalities synchronize to a single later stage while preserving
the colimit images of the base family. -/
lemma presheafColimit_common_stage_of_fixed_overlap_branch_equalities
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) = x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (B : Presieve A)
    (D : Presieve Y)
    (hD : D ∈ K Y)
    (hDfac : D.FactorsThruAlong B i) :
    ∃ e : Set.Iio β, ∃ hde : d.1 ≤ e.1,
      ∃ w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1),
        (∀ i,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i.1.1)) (w i) =
            x i) ∧
        (∀ n : D.uncurry,
          let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j)) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  choose b f hf using
    fun n : D.uncurry ↦
      presheafColimit_section_eq_at_later_stage
        (β := β)
        (F := F)
        (U := n.1.1)
        (i := d)
        (s := ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)))
        (t := ((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j))
        (h :=
          presheafColimit_fixed_target_pullback_branch_eq_in_colimit
            (β := β)
            (F := F)
            (x := x)
            (hx := hx)
            (v' := v')
            (hv_image := hv_image)
            (T := T)
            (right := right)
            (gr := gr)
            (hcomm := hcomm)
            (gr' := gr')
            (hj' := hj')
            (hW := hW)
            (g := g)
            (i := i)
            (e₀ := e₀)
            (he := he)
            (hie := hie)
            (B := B)
            (D := D)
            (hDfac := hDfac)
            n)
  by_cases hDne : Nonempty D.uncurry
  · obtain ⟨e, heD⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun n : D.uncurry ↦ (b n).1)
        (hf := fun n ↦ (b n).2)
        (hι := hcover Y D hD)
    obtain ⟨n₀⟩ := hDne
    have hde : d.1 ≤ e.1 := by
      exact le_trans (leOfHom (f n₀)) (heD n₀)
    let w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1) := fun i' ↦
      ((F.map (homOfLE hde)).1.app (op i'.1.1)) (v' i')
    have hw_image :
        ∀ i' : R.uncurry,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i'.1.1)) (w i') =
            x i' := by
      intro i'
      -- Transporting the base family to the common stage preserves its prescribed colimit image.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i'.1.1)) (v' i') =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i'.1.1)) (w i') := by
        simpa [w] using
          (congrFun
            ((congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hde)))
              (op i'.1.1))
            (v' i')).symm
      exact hmap.symm.trans (hv_image i')
    have htarget_e :
        ∀ n : D.uncurry,
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) := by
      intro n
      have hcomp : f n ≫ homOfLE (heD n) = homOfLE hde := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) := by
        -- Move the left branch restriction across the common transport to the synchronized stage.
        simpa [w] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hde)
            (g := n.1.2 ≫ i ≫ gr q)
            (a := v' (right q))).symm
      have hright :
          ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
        -- The same transport rewrite applies to the fixed target branch `j`.
        simpa [w] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hde)
            (g := n.1.2 ≫ g ≫ hj')
            (a := v' j)).symm
      have hstage :
          ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
        -- Factor the common transport through the local later-stage witness chosen for this branch.
        rw [show homOfLE hde = f n ≫ homOfLE (heD n) by simpa using hcomp.symm]
        simpa [Functor.map_comp, Function.comp, hf n]
      exact hleft.trans (hstage.trans hright.symm)
    exact ⟨e, hde, w, hw_image, htarget_e⟩
  · haveI : IsEmpty D.uncurry := not_nonempty_iff.mp hDne
    -- If there are no pulled-back branches, the current stage already satisfies the empty family
    -- of fixed-target comparisons.
    refine ⟨d, le_rfl, v', hv_image, ?_⟩
    intro n
    exact isEmptyElim n

/-- Helper for Lemma 7.17.10: after the first-level equalities are synchronized at stage `d`, one
more cofinality step synchronizes every canonical base-cover pullback branch equality to one later
stage `e` while preserving the colimit images of the base family. -/
lemma presheafColimit_common_stage_of_base_cover_pullback_owner_equalities
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) =
          x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof) :
    ∃ Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, Cbase p ∈ K p.1.2.1.1) ∧
      ∃ baseRight :
          (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry,
        ∃ baseGr :
            ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
              s.2.1.1 ⟶ (baseRight s).1.1,
          (∀ s,
            let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
            baseGr s ≫ (baseRight s).1.2 =
              ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2)) ∧
          ∃ e : Set.Iio β,
            ∃ hde : d.1 ≤ e.1,
              ∃ w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1),
                (∀ i,
                  w i = ((F.map (homOfLE hde)).1.app (op i.1.1)) (v' i)) ∧
                (∀ i,
                  ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i.1.1))
                      (w i) = x i) ∧
                (∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
                  let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
                  ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
                    ((F.obj e).1.map (baseGr s).op) (w (baseRight s))) := by
  classical
  -- The explicit targeted-owner smallness hypothesis is retained for the downstream API shape.
  let _ := hκsmall
  obtain ⟨Cbase, hCbase, hCbasefac, hCbasesmall⟩ :=
    targeted_secondary_owner_has_small_base_cover_owner_family
      (K := K)
      (hcover := hcover)
      (β := β)
      (hR := hR)
      T
      hT
      B
      hB
  let κbase : Type (max u v) := Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry
  let leftBase : κbase → R.uncurry := fun s ↦
    let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
    right q
  let baseRight : κbase → R.uncurry := fun s ↦
    let data := hCbasefac s.1 s.2.2
    match data with
    | ⟨W, m, e, he, hm⟩ => ⟨⟨W, e⟩, he⟩
  let baseGr : ∀ s : κbase, s.2.1.1 ⟶ (baseRight s).1.1 := fun s ↦
    let data := hCbasefac s.1 s.2.2
    match data with
    | ⟨W, m, e, he, hm⟩ => m
  have hbaseComp :
      ∀ s : κbase,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
    intro s
    -- Unpack the canonical base-cover factorization once so the chosen branch and comparison map
    -- are definitionally visible on this sigma owner.
    let data := hCbasefac s.1 s.2.2
    rcases data with ⟨W, m, e, he, hm⟩
    simp [baseGr, baseRight, data, Category.assoc, hCbasefac]
    simpa [data, Category.assoc] using hm.symm
  have hκbaseSmall : Cardinal.lift (Cardinal.mk κbase) < β.cof := by
    simpa [κbase] using hCbasesmall
  have hstage_witness :
      ∀ s : κbase,
        ∃ e : Set.Iio β, ∃ f : d ⟶ e,
          ((F.map f).1.app (op s.2.1.1))
              (((F.obj d).1.map
                    (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr (s.1.1.1)).op)
                  (v' (leftBase s))) =
            ((F.map f).1.app (op s.2.1.1))
              (((F.obj d).1.map (baseGr s).op) (v' (baseRight s))) := by
    intro s
    let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op s.2.1.1))
            (((F.obj d).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (v' (leftBase s))) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op s.2.1.1))
            (((F.obj d).1.map (baseGr s).op) (v' (baseRight s))) := by
      -- Both branches have the same composite to `U`, so they already agree in the presheaf
      -- colimit before the second synchronization step.
      refine
        presheafColimit_overlap_eq_in_colimit
          (β := β)
          (F := F)
          (x := x)
          (hx := hx)
          (v := v')
          (hv_image := hv_image)
          (g1 := s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q)
          (g2 := baseGr s)
          ?_
      calc
        (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q) ≫ (leftBase s).1.2 =
            ((s.2.1.2 ≫ s.1.1.2.1.2) ≫ gr q) ≫ (right q).1.2 := by
              simp [leftBase, q, Category.assoc]
        _ = (s.2.1.2 ≫ s.1.1.2.1.2) ≫ (gr q ≫ (right q).1.2) := by
              simp [Category.assoc]
        _ = (s.2.1.2 ≫ s.1.1.2.1.2) ≫ (q.2.1.2 ≫ q.1.1.2) := by
              simpa [q] using congrArg
                (fun t ↦ (s.2.1.2 ≫ s.1.1.2.1.2) ≫ t)
                (hcomm q).symm
        _ = ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
              simp [Category.assoc]
        _ = baseGr s ≫ (baseRight s).1.2 := by
              simpa [q] using (hbaseComp s).symm
    exact
      presheafColimit_section_eq_at_later_stage
        (β := β)
        (F := F)
        (U := s.2.1.1)
        (i := d)
        (s := ((F.obj d).1.map
          (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (v' (leftBase s)))
        (t := ((F.obj d).1.map (baseGr s).op) (v' (baseRight s)))
        (h := hcolim)
  obtain ⟨e, hde, w, hw_def, hw_image, hbase_e⟩ :=
    presheafColimit_common_stage_of_targeted_secondary_branch_equalities
      (β := β)
      (F := F)
      (left := leftBase)
      (right := baseRight)
      (Z := fun s : κbase ↦ s.2.1.1)
      (gl := fun s : κbase ↦
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q)
      (gr := baseGr)
      (x := x)
      (v := v')
      (hv_image := hv_image)
      (hιsmall := hκbaseSmall)
      (hstage_witness := hstage_witness)
  refine ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e, hde, w, hw_def, hw_image, ?_⟩
  intro s
  -- The global synchronized stage inherits the canonical base-cover branch equalities for every
  -- remembered owner branch.
  simpa [leftBase] using hbase_e s

/-- Helper for Lemma 7.17.10: once the desired fixed-target equality is known after restricting to
every branch of a covering presieve `D`, sheaf separatedness at stage `e` descends it to the
original overlap witness. -/
lemma stage_family_target_overlap_eq_of_cover_branch_equalities
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (p : targeted_secondary_owner_index (T := T) B)
    (z : targeted_secondary_target_overlap_witness (T := T) (B := B) p)
    (D : Presieve z.1)
    (hD : D ∈ K z.1)
    (htarget_local :
      ∀ n : D.uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
        let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
        ((F.obj e).1.map (n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (n.1.2 ≫ z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
    ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
      ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj)) := by
  let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
  have hDd : Presieve.IsSheafFor ((F.obj e).1) D := by
    -- The synchronized stage remains a sheaf on the auxiliary covering presieve used to descend
    -- the branchwise target comparison.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj e).1)).1 (F.obj e).2) D hD
  apply hDd.isSeparatedFor.ext
  intro X k hk
  let n : D.uncurry := ⟨⟨X, k⟩, hk⟩
  -- Evaluate the branchwise hypothesis on the concrete branch `n` of `D`.
  simpa [q, qj, n, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htarget_local n

/-- Helper for Lemma 7.17.10: after the anonymous base-cover owner equalities have been
synchronized at stage `e`, one more cofinality step synchronizes the fixed-target comparisons on
canonical pullback objects indexed by the small family of retained base-cover branches and target
first-level branches. Arbitrary overlap witnesses are then handled by separatedness. -/
lemma presheafColimit_common_stage_of_canonical_fixed_target_branch_equalities
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hw_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i.1.1)) (w i) =
          x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof)
    (Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hCbase : ∀ p, Cbase p ∈ K p.1.2.1.1)
    (baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry)
    (baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1)
    (hbaseComp :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2))
    (hbase_e :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s))) :
    ∃ e' : Set.Iio β,
      ∃ hee' : e.1 ≤ e'.1,
        ∃ w' : ∀ i : R.uncurry, (F.obj e').1.obj (op i.1.1),
          (∀ i,
            w' i = ((F.map (homOfLE hee')).1.app (op i.1.1)) (w i)) ∧
          (∀ i,
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e').app (op i.1.1))
                (w' i) = x i) ∧
          (∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
            let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
            ((F.obj e').1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w' (right q)) =
              ((F.obj e').1.map (baseGr s).op) (w' (baseRight s))) ∧
          (∀ p : targeted_secondary_owner_index (T := T) B,
            ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
              let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
              let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
              ((F.obj e').1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
                ((F.obj e').1.map (z.2.2.2.1 ≫ gr qj).op) (w' (right qj))) := by
  classical
  let κbase : Type (max u v) :=
    Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry
  have hκbase : Cardinal.lift (Cardinal.mk κbase) < β.cof := by
    refine
      small_sigma_of_small_family
        (C := C)
        (K := K)
        (β := β)
        (hcover := hcover)
        (ι := targeted_secondary_owner_index (T := T) B)
        (X := fun p : targeted_secondary_owner_index (T := T) B ↦ (Cbase p).uncurry)
        (hι := hκsmall)
        ?_
    intro p
    simpa [HasCardinalLT] using hcover p.1.2.1.1 (Cbase p) (hCbase p)
  let ι : Type (max u v) := Σ s : κbase, (T s.1.2).uncurry
  let targetQ : ι → Σ i : R.uncurry, (T i).uncurry := fun u ↦ ⟨u.1.1.2, u.2⟩
  let leftMapToU : ∀ u : ι, u.1.2.1.1 ⟶ U := fun u ↦
    baseGr u.1 ≫ (baseRight u.1).1.2
  let rightMapToU : ∀ u : ι, (targetQ u).2.1.1 ⟶ U := fun u ↦
    gr (targetQ u) ≫ (right (targetQ u)).1.2
  let Z : ι → C := fun u ↦ pullback (leftMapToU u) (rightMapToU u)
  let gl : ∀ u : ι, Z u ⟶ (baseRight u.1).1.1 := fun u ↦
    pullback.fst (leftMapToU u) (rightMapToU u) ≫ baseGr u.1
  let gt : ∀ u : ι, Z u ⟶ (right (targetQ u)).1.1 := fun u ↦
    pullback.snd (leftMapToU u) (rightMapToU u) ≫ gr (targetQ u)
  have hιsmall : Cardinal.lift (Cardinal.mk ι) < β.cof := by
    have hfiber : ∀ s : κbase, Cardinal.lift (Cardinal.mk ((T s.1.2).uncurry)) < β.cof := by
      intro s
      simpa using hcover s.1.2.1.1 (T s.1.2) (hT s.1.2)
    have htotal : Cardinal.lift (Cardinal.mk (Σ s : κbase, (T s.1.2).uncurry)) < β.cof := by
      exact
        small_sigma_of_small_family
          (C := C)
          (K := K)
          (β := β)
          (hcover := hcover)
          (ι := κbase)
          (X := fun s : κbase ↦ (T s.1.2).uncurry)
          (hι := hκbase)
          hfiber
    simpa [ι] using htotal
  have hstage_witness :
      ∀ u : ι,
        ∃ d : Set.Iio β, ∃ f : e ⟶ d,
          ((F.map f).1.app (op (Z u)))
              (((F.obj e).1.map (gl u).op) (w (baseRight u.1))) =
            ((F.map f).1.app (op (Z u)))
              (((F.obj e).1.map (gt u).op) (w (right (targetQ u)))) := by
    intro u
    have hoverU : (gl u) ≫ (baseRight u.1).1.2 = (gt u) ≫ (right (targetQ u)).1.2 := by
      calc
        (gl u) ≫ (baseRight u.1).1.2 =
            pullback.fst (leftMapToU u) (rightMapToU u) ≫ leftMapToU u := by
              simp [gl, leftMapToU, Category.assoc]
        _ = pullback.snd (leftMapToU u) (rightMapToU u) ≫ rightMapToU u := by
              exact pullback.condition
        _ = (gt u) ≫ (right (targetQ u)).1.2 := by
              simp [gt, rightMapToU, Category.assoc]
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op (Z u)))
            (((F.obj e).1.map (gl u).op) (w (baseRight u.1))) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op (Z u)))
            (((F.obj e).1.map (gt u).op) (w (right (targetQ u)))) := by
      exact
        presheafColimit_overlap_eq_in_colimit
          (β := β)
          (F := F)
          (x := x)
          (hx := hx)
          (v := w)
          (hv_image := hw_image)
          (i := baseRight u.1)
          (j := right (targetQ u))
          (Z := Z u)
          (gi := gl u)
          (gj := gt u)
          hoverU
    exact
      presheafColimit_section_eq_at_later_stage
        (β := β)
        (F := F)
        (U := Z u)
        (i := e)
        (s := ((F.obj e).1.map (gl u).op) (w (baseRight u.1)))
        (t := ((F.obj e).1.map (gt u).op) (w (right (targetQ u))))
        hcolim
  obtain ⟨e', hee', w', hw'_def, hw'_image, hcanon⟩ :=
    presheafColimit_common_stage_of_targeted_secondary_branch_equalities
      (β := β)
      (F := F)
      (left := fun u : ι ↦ baseRight u.1)
      (right := fun u : ι ↦ right (targetQ u))
      (Z := Z)
      (gl := gl)
      (gr := gt)
      (x := x)
      (v := w)
      (hv_image := hw_image)
      (hιsmall := hιsmall)
      (hstage_witness := hstage_witness)
  have hbase_e' :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e').1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w' (right q)) =
          ((F.obj e').1.map (baseGr s).op) (w' (baseRight s)) := by
    simpa [hw'_def] using
      stage_family_base_cover_owner_equalities_at_later_stage
        (β := β)
        (F := F)
        T
        right
        gr
        B
        Cbase
        baseRight
        baseGr
        hee'
        w
        hbase_e
  refine ⟨e', hee', w', hw'_def, hw'_image, hbase_e', ?_⟩
  intro p z
  let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
  obtain ⟨D, hD, hDfac⟩ := K.pullback z.2.1 (Cbase p) (hCbase p)
  refine
    stage_family_target_overlap_eq_of_cover_branch_equalities
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (T := T)
      (right := right)
      (gr := gr)
      (w := w')
      (B := B)
      (p := p)
      (z := z)
      (D := D)
      (hD := hD)
      ?_
  intro n
  obtain ⟨A₁, i₁, e₁, he₁, hi₁⟩ := hDfac n.2
  let s : (Cbase p).uncurry := ⟨⟨A₁, e₁⟩, he₁⟩
  have hbase_to_target :
      ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
        ((n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2) ≫ p.2.1.2) := by
    have hcomp := hbaseComp ⟨p, s⟩
    calc
      ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
          i₁ ≫ (baseGr ⟨p, s⟩ ≫ (baseRight ⟨p, s⟩).1.2) := by
            simp only [Category.assoc]
      _ = i₁ ≫ ((s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
            rw [hcomp]
      _ = ((i₁ ≫ s.1.2) ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2 := by
            simp only [Category.assoc]
      _ = ((n.1.2 ≫ z.2.1) ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2 := by
            rw [hi₁]
      _ = n.1.2 ≫ (z.2.1 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2) := by
            simp only [Category.assoc]
      _ = n.1.2 ≫ (z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2) := by
            change
              n.1.2 ≫
                  (z.2.1 ≫ p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2) =
                n.1.2 ≫ (z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2)
            rw [z.2.2.2.2]
      _ = ((n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2) ≫ p.2.1.2) := by
            simp only [Category.assoc]
  let sκ : κbase := ⟨p, s⟩
  let u : ι := ⟨sκ, z.2.2.1⟩
  have hpull :
      i₁ ≫ leftMapToU u = (n.1.2 ≫ z.2.2.2.1) ≫ rightMapToU u := by
    calc
      i₁ ≫ leftMapToU u = (i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2 := by
        simp [u, sκ, leftMapToU, Category.assoc]
      _ = ((n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2) ≫ p.2.1.2) := by
        simpa [q, qj, Category.assoc] using hbase_to_target
      _ = (n.1.2 ≫ z.2.2.2.1) ≫ rightMapToU u := by
        simp [u, sκ, qj, targetQ, rightMapToU, Category.assoc, hcomm qj]
  let l : n.1.1 ⟶ Z u := pullback.lift i₁ (n.1.2 ≫ z.2.2.2.1) hpull
  have hbase_branch :
      ((F.obj e').1.map (n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
        ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) := by
    have hs := congrArg (((F.obj e').1.map i₁.op)) (hbase_e' ⟨p, s⟩)
    simpa [q, FunctorToTypes.map_comp_apply, Category.assoc, op_comp, hi₁] using hs
  have hcanon_branch :
      ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) =
        ((F.obj e').1.map (n.1.2 ≫ z.2.2.2.1 ≫ gr qj).op) (w' (right qj)) := by
    have hu := congrArg (((F.obj e').1.map l.op)) (hcanon u)
    simpa [u, sκ, l, qj, targetQ, Z, gl, gt, FunctorToTypes.map_comp_apply,
      Category.assoc, op_comp] using hu
  exact hbase_branch.trans hcanon_branch

/-- Helper for Lemma 7.17.10: the source-faithful synchronization step should range over actual
fixed-target overlap witnesses. This wrapper keeps the already-proved anonymous base-cover
equalities and isolates the remaining global fixed-target synchronization as one explicit output
hypothesis. -/
lemma presheafColimit_common_stage_of_refined_target_overlap_equalities
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1)) (v' i) =
          x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof) :
    ∃ Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, Cbase p ∈ K p.1.2.1.1) ∧
      ∃ baseRight :
          (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry,
        ∃ baseGr :
            ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
              s.2.1.1 ⟶ (baseRight s).1.1,
          (∀ s,
            let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
            baseGr s ≫ (baseRight s).1.2 =
              ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2)) ∧
          ∃ e : Set.Iio β,
            ∃ hde : d.1 ≤ e.1,
              ∃ w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1),
                (∀ i,
                  w i = ((F.map (homOfLE hde)).1.app (op i.1.1)) (v' i)) ∧
                (∀ i,
                  ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op i.1.1))
                      (w i) = x i) ∧
                (∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
                  let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
                  ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
                    ((F.obj e).1.map (baseGr s).op) (w (baseRight s))) ∧
                (∀ p : targeted_secondary_owner_index (T := T) B,
                  ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
                    let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
                    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
                    ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
                      ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))) := by
  obtain ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e, hde, w, hw_def, hw_image, hbase_e⟩ :=
    presheafColimit_common_stage_of_base_cover_pullback_owner_equalities
      (β := β)
      (F := F)
      (hcover := hcover)
      (hR := hR)
      (x := x)
      (hx := hx)
      (v' := v')
      (hv_image := hv_image)
      T
      hT
      right
      gr
      hcomm
      B
      hB
      hκsmall
  obtain ⟨e', hee', w', hw'_def, hw'_image, hbase_e', htarget_e'⟩ :=
    presheafColimit_common_stage_of_canonical_fixed_target_branch_equalities
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (x := x)
      (hx := hx)
      (w := w)
      (hw_image := hw_image)
      (T := T)
      (hT := hT)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (B := B)
      (hB := hB)
      (hκsmall := hκsmall)
      (Cbase := Cbase)
      (hCbase := hCbase)
      (baseRight := baseRight)
      (baseGr := baseGr)
      (hbaseComp := hbaseComp)
      (hbase_e := hbase_e)
  refine
    ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e', le_trans hde hee', w', ?_, hw'_image,
      hbase_e', htarget_e'⟩
  intro i
  have hcomp : homOfLE (le_trans hde hee') = homOfLE hde ≫ homOfLE hee' := by
    exact Subsingleton.elim _ _
  calc
    w' i = ((F.map (homOfLE hee')).1.app (op i.1.1)) (w i) := hw'_def i
    _ = ((F.map (homOfLE hee')).1.app (op i.1.1))
          (((F.map (homOfLE hde)).1.app (op i.1.1)) (v' i)) := by
            rw [hw_def i]
    _ = ((F.map (homOfLE (le_trans hde hee'))).1.app (op i.1.1)) (v' i) := by
            rw [show homOfLE (le_trans hde hee') = homOfLE hde ≫ homOfLE hee' by simpa using hcomp]
            simpa [Functor.map_comp, Function.comp]

/-- Helper for Lemma 7.17.10: once a canonical base-cover branch has been identified with the
`right`-branch of an actual `T j`-element, the synchronized base-cover equality and the first-level
equality at that `T j`-element combine to recover the desired fixed-target equality.

This helper is kept as a small formal target only; the previous generated proof had an invalid
projection in the displayed target and should not drive replanning. -/
lemma stage_family_fixed_target_eq_of_base_cover_eq_and_first_level
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    {q qj : Σ i : R.uncurry, (T i).uncurry}
    {X : C}
    {a : X ⟶ (right q).1.1}
    {b : X ⟶ (right qj).1.1}
    {c : X ⟶ qj.2.1.1}
    {d : X ⟶ (qj.1).1.1}
    (hbase :
      ((F.obj e).1.map a.op) (w (right q)) =
        ((F.obj e).1.map b.op) (w (right qj)))
    (hb : b = c ≫ gr qj)
    (hc : d = c ≫ qj.2.1.2) :
    ((F.obj e).1.map a.op) (w (right q)) =
      ((F.obj e).1.map d.op) (w qj.1) := by
  -- Push the first-level equality for `qj` along `c`, so the right-hand branch is rewritten from
  -- `right qj` to the actual source branch `qj.1`.
  have hrewrite :
      ((F.obj e).1.map d.op) (w qj.1) =
        ((F.obj e).1.map b.op) (w (right qj)) := by
    have hqj := congrArg (((F.obj e).1.map c.op)) (hfirst_e qj)
    simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp, hb, hc] using hqj
  exact hbase.trans hrewrite.symm

/-- Helper for Lemma 7.17.10: after the anonymous base-cover equalities have been synchronized at
the global stage `e`, the remaining fixed-target comparison is proved branchwise by refining one
pulled-back secondary branch and then descending by separatedness. -/
lemma stage_family_fixed_target_eq_on_base_cover_refinement
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hCbase : ∀ p, Cbase p ∈ K p.1.2.1.1)
    (baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry)
    (baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1)
    (hbaseComp :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2))
    (hbase_e :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s)))
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj)))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (D : Presieve Y) (hD : D ∈ K Y)
    (hDfac : D.FactorsThruAlong (B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩) i) :
    ∀ n : D.uncurry,
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
      ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) := by
  intro n
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  obtain ⟨A₁, i₁, e₁, he₁, hi₁⟩ := hDfac n.2
  let m : (B q).uncurry := ⟨⟨A₁, e₁⟩, he₁⟩
  let p : targeted_secondary_owner_index (T := T) B := ⟨⟨q, m⟩, j⟩
  obtain ⟨E, hE, hEfac⟩ := K.pullback (n.1.2 ≫ g ≫ hj') (T j) (hT j)
  have hEe : Presieve.IsSheafFor ((F.obj e).1) E := by
    -- The global stage remains a sheaf on the concrete target-side refinement cover.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj e).1)).1 (F.obj e).2) E hE
  apply hEe.isSeparatedFor.ext
  intro X k hk
  let t : E.uncurry := ⟨⟨X, k⟩, hk⟩
  obtain ⟨A₂, c, e₂, he₂, hc⟩ := hEfac t.2
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A₂, e₂⟩, he₂⟩⟩
  -- Route correction: the fixed target branch is introduced only after entering the concrete
  -- overlap branch `n`, so the target-side pullback data are genuinely available.
  let _ := hB
  let _ := hCbase
  let _ := baseRight
  let _ := hbaseComp
  let _ := hi₁
  let _ := p
  have hoverlap :
      targeted_secondary_target_overlap_witness (T := T) (B := B) p := by
    -- Route correction: the source proof compares the retained secondary branch and the fixed
    -- target branch only after adjoining their explicit common source.
    simpa [p, q, qj, m] using
      pulled_back_secondary_branch_target_overlap_witness
        (K := K)
        (β := β)
        (hcover := hcover)
        (T := T)
        (B := B)
        (gr' := gr')
        (hj' := hj')
        (hW := hW)
        (g := g)
        (i := i)
        (e₀ := e₀)
        (he := he)
        (hie := hie)
        (i₁ := i₁)
        (e₁ := e₁)
        (he₁ := he₁)
        (hi₁ := hi₁)
        (nmap := n.1.2)
        (k := k)
        (c := c)
        (e₂ := e₂)
        (he₂ := he₂)
        (hc := hc)
  have htarget_branch :
      ((F.obj e).1.map (k ≫ n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (c ≫ gr qj).op) (w (right qj)) := by
    -- The global refined-overlap synchronization theorem is now instantiated on the concrete
    -- common-source witness constructed for this branch.
    simpa [p, q, qj, m] using htarget_e p hoverlap
  -- Once the direct fixed-target equality is available on the common source, the first-level
  -- equality for `qj` rewrites the target branch back to the actual branch `j`.
  refine
    stage_family_fixed_target_eq_of_base_cover_eq_and_first_level
      (K := K)
      (β := β)
      (F := F)
      (T := T)
      (right := right)
      (gr := gr)
      (w := w)
      (hfirst_e := hfirst_e)
      (q := q)
      (qj := qj)
      (a := k ≫ n.1.2 ≫ i ≫ gr q)
      (b := c ≫ gr qj)
      (c := c)
      (d := k ≫ n.1.2 ≫ g ≫ hj')
      htarget_branch
      rfl
      ?_
  simpa [qj, Category.assoc] using hc.symm

/-- Helper for Lemma 7.17.10: once the anonymous base-cover equalities and the first-level
equalities both live at the global stage `e`, one concrete overlap on `R` is handled by opening
the outer pullback cover, then the pulled-back secondary cover, and finally the local
fixed-target refinement. -/
lemma stage_family_overlap_of_base_cover_owner_equalities_at_global_stage
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hCbase : ∀ p, Cbase p ∈ K p.1.2.1.1)
    (baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry)
    (baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1)
    (hbaseComp :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2))
    (hbase_e :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s)))
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    ∀ {r j : R.uncurry} {W : C}
      (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1),
      gr' ≫ r.1.2 = hj' ≫ j.1.2 →
        ((F.obj e).1.map gr'.op) (w r) =
          ((F.obj e).1.map hj'.op) (w j) := by
  intro r j W gr' hj' hW
  -- Route correction: the outer pullback descent now happens at the global fixed stage `e`. The
  -- only remaining source-faithful gap is to convert the retained owner family into a
  -- fixed-target branchwise equality against the chosen branch `j`.
  obtain ⟨S, hS, hSfac⟩ := K.pullback gr' (T r) (hT r)
  have hSe : Presieve.IsSheafFor ((F.obj e).1) S := by
    -- The globally synchronized stage remains a sheaf on the outer pullback cover.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj e).1)).1 (F.obj e).2) S hS
  apply hSe.isSeparatedFor.ext
  intro Y g hg
  let m : S.uncurry := ⟨⟨Y, g⟩, hg⟩
  obtain ⟨A, i, e₀, he, hie⟩ := hSfac m.2
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  have hbranch :
      ((F.obj e).1.map g.op) (((F.obj e).1.map gr'.op) (w r)) =
        ((F.obj e).1.map (i ≫ gr q).op) (w (right q)) := by
    -- Rewrite the outer branch with the transported first-level equality indexed by `q`.
    simpa [q] using
      pullback_branch_restriction_eq_of_first_level_equality
        (K := K)
        (hcover := hcover)
        (β := β)
        (F := F)
        (T := T)
        (right := right)
        (gr := gr)
        (v' := w)
        (hfirst := hfirst_e)
        (r := r)
        (gr' := gr')
        (g := g)
        (i := i)
        (e := e₀)
        (he := he)
        (hie := hie.symm)
  have htarget :
      ((F.obj e).1.map (i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (g ≫ hj').op) (w j) := by
    obtain ⟨D, hD, hDfac⟩ := K.pullback i (B q) (hB q)
    -- The remaining descent happens on the pullback of the retained secondary cover along `i`,
    -- and the fixed target branch is introduced only inside this local branchwise refinement.
    refine
      stage_family_targeted_secondary_target_eq
        (K := K)
        (hcover := hcover)
        (β := β)
        (F := F)
        (T := T)
        (right := right)
        (gr := gr)
        (B := B)
        (hB := hB)
        (v' := w)
        (gr' := gr')
        (hj' := hj')
        (g := g)
        (i := i)
        (e := e₀)
        (he := he)
        (D := D)
        (hD := hD)
        (htarget :=
          stage_family_fixed_target_eq_on_base_cover_refinement
            (β := β)
            (F := F)
            (K := K)
            (hcover := hcover)
            (T := T)
            (hT := hT)
            (right := right)
            (gr := gr)
            (hcomm := hcomm)
            (w := w)
            (hfirst_e := hfirst_e)
            (B := B)
            (hB := hB)
            (Cbase := Cbase)
            (hCbase := hCbase)
            (baseRight := baseRight)
            (baseGr := baseGr)
            (hbaseComp := hbaseComp)
            (hbase_e := hbase_e)
            (htarget_e := htarget_e)
            (gr' := gr')
            (hj' := hj')
            (hW := hW)
            (g := g)
            (i := i)
            (e₀ := e₀)
            (he := he)
            (hie := hie.symm)
            (D := D)
            (hD := hD)
            (hDfac := hDfac))
  -- The outer descent closes once the targeted inner comparison is available on this branch.
  exact hbranch.trans htarget

/-- Helper for Lemma 7.17.10: a pointwise overlap solver packages directly into compatibility of
the synchronized stage family on the original cover. -/
lemma stage_family_compatible_of_first_level_pullback_equalities
    {U : C} {R : Presieve U}
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hoverlap :
      ∀ {r j : R.uncurry} {W : C}
        (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1),
        gr' ≫ r.1.2 = hj' ≫ j.1.2 →
          ((F.obj d).1.map gr'.op) (v' r) =
            ((F.obj d).1.map hj'.op) (v' j)) :
    Presieve.Arrows.Compatible ((F.obj d).1) (fun i : R.uncurry ↦ i.1.2) v' := by
  -- Compatibility is exactly the same overlap statement written in `Presieve.Arrows` form.
  intro r j W gr' hj' hW
  exact hoverlap gr' hj' hW

/-- Helper for Lemma 7.17.10: if a section on the sigma refinement glues the branchwise
restrictions of the stage family `v'`, then its restriction along each base branch already
recovers the original family `v'`. -/
lemma sigma_refinement_stage_glue_restricts_to_base_family
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (td : (F.obj d).1.obj (op U))
    (htd :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map (q.2.1.2 ≫ q.1.1.2).op) td =
          ((F.obj d).1.map q.2.1.2.op) (v' q.1)) :
    ∀ i : R.uncurry, ((F.obj d).1.map i.1.2.op) td = v' i := by
  intro i
  have hTi : Presieve.IsSheafFor ((F.obj d).1) (T i) := by
    -- The stage sheaf is already a sheaf for each chosen pullback cover in the coverage `K`.
    exact ((Presieve.isSheaf_coverage (K := K) ((F.obj d).1)).1 (F.obj d).2) (T i) (hT i)
  apply hTi.isSeparatedFor.ext
  intro Y g hg
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨i, ⟨⟨Y, g⟩, hg⟩⟩
  -- Evaluate the sigma-gluing identity on the branch indexed by `q`.
  simpa [q, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htd q

/-- Helper for Lemma 7.17.10: sigma-refinement compatibility is obtained by applying the previous
base-cover overlap descent to each overlap pair in the sigma refinement. -/
lemma stage_family_sigma_refinement_compatible_of_base_cover_owner_equalities
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    (Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hCbase : ∀ p, Cbase p ∈ K p.1.2.1.1)
    (baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry)
    (baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1)
    (hbaseComp :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2))
    (hbase_e :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s)))
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    Presieve.Arrows.Compatible
      ((F.obj e).1)
      (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2 ≫ q.1.1.2)
      (fun q ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1)) := by
  intro q₁ q₂ Z a b h
  -- Route correction: the sigma overlap is reduced directly to the base-cover overlap lemma,
  -- so the fixed target branch is introduced only inside the concrete local refinement.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using
    stage_family_overlap_of_base_cover_owner_equalities_at_global_stage
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (T := T)
      (hT := hT)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (Cbase := Cbase)
      (hCbase := hCbase)
      (baseRight := baseRight)
      (baseGr := baseGr)
      (hbaseComp := hbaseComp)
      (hbase_e := hbase_e)
      (htarget_e := htarget_e)
      (w := w)
      (hfirst_e := hfirst_e)
      (B := B)
      (hB := hB)
      (r := q₁.1)
      (j := q₂.1)
      (gr' := a ≫ q₁.2.1.2)
      (hj' := b ≫ q₂.2.1.2)
      (by simpa [Category.assoc] using h)

/-- Helper for Lemma 7.17.10: every stage sheaf is a sheaf for the sigma refinement because that
refinement generates a covering sieve in `J = K.toGrothendieck`. -/
lemma stage_sheaf_isSheafFor_sigma_refinement
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    {e : Set.Iio β} :
    Presieve.IsSheafFor
      ((F.obj e).1)
      (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T) := by
  -- Pass from the stage sheaf property on `J` to the explicit sigma refinement via the sieve it
  -- generates.
  exact
    (F.obj e).2.isSheafFor
      (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T)
      (sigma_refinement_generate_mem_toGrothendieck
        (β := β)
        (hcover := hcover)
        (hR := hR)
        T
        hT)

/-- Helper for Lemma 7.17.10: the presheaf colimit is a sheaf for a single `K`-covering presieve
once all representatives and overlap witnesses are synchronized in one ordinal stage.

This is the source-facing local sheaf condition used in the Stacks proof: for a chosen covering
presieve `R`, sufficiently large cofinality lets us choose one common ordinal stage for all local
sections and all pairwise overlap equalities. The previous attempted proof introduced a stronger
fixed-target pullback-branch bridge; that bridge is not part of the source statement and was the
source of the bad local statement. -/
lemma presheafColimit_isSheafFor_of_coveringPresieveCardinal_lt_cof
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Presieve.IsSheafFor (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) R := by
  -- Route correction: reduce the local sheaf condition on `R` to an explicit arrow family indexed
  -- by `R.uncurry`, then synchronize representatives and overlap equalities exactly as in the
  -- Stacks proof.
  rw [presieve_eq_of_uncurry (β := β) (hcover := hcover) R, Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hsep :
      Presieve.IsSeparatedFor
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        R :=
    presheafColimit_isSeparatedFor_of_coveringPresieveCardinal_lt_cof
      (β := β)
      (F := F)
      (hcover := hcover)
      hR
  -- Choose stagewise representatives for the given compatible family of colimit sections.
  choose b t ht using
    fun i : R.uncurry ↦
      presheafColimit_section_exists_rep
        (β := β)
        (F := F)
        i.1.1
        (x i)
  obtain ⟨a, s, hs_image⟩ :=
    presheafColimit_common_stage_of_small_sections
      (β := β)
      (F := F)
      (x := x)
      (b := b)
      (t := t)
      (ht := ht)
      (hι := hcover U R hR)
  -- Choose the canonical pullback cover over each branch of `R`.
  choose T hT right gr hcomm using
    fun i : R.uncurry ↦ K.pullback i.1.2 R hR
  obtain ⟨d, v', hv_image, hfirst⟩ :=
    presheafColimit_common_stage_of_small_overlaps
      (β := β)
      (F := F)
      (x := x)
      (hx := hx)
      (s := s)
      (hs_image := hs_image)
      (left := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.1)
      (right := right)
      (Z := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
      (gl := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2)
      (gr := gr)
      (hcomm := hcomm)
      (hι :=
        coveringPresieve_small_sigma_family
          (β := β)
          (hcover := hcover)
          (hR := hR)
          T
          hT)
  -- Pull back the first-level branch covers once more so the fixed-target overlap equalities can
  -- be synchronized in one later stage.
  choose B hB hBfac using
    fun q : Σ i : R.uncurry, (T i).uncurry ↦
      K.pullback q.2.1.2 (T q.1) (hT q.1)
  have hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof :=
    targeted_secondary_owner_index_small
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
  obtain ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e, hde, w, hw_def, hw_image, hbase_e,
      htarget_e⟩ :=
    presheafColimit_common_stage_of_refined_target_overlap_equalities
      (β := β)
      (F := F)
      (hcover := hcover)
      (hR := hR)
      (x := x)
      (hx := hx)
      (v' := v')
      (hv_image := hv_image)
      T
      hT
      right
      gr
      hcomm
      B
      hB
      hκsmall
  have hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)) :=
    stage_family_first_level_pullback_equalities_at_later_stage
      (β := β)
      (F := F)
      T
      right
      gr
      hde
      v'
      hfirst
  have hsigma_compatible :
      Presieve.Arrows.Compatible
        ((F.obj e).1)
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2 ≫ q.1.1.2)
        (fun q ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1)) :=
    stage_family_sigma_refinement_compatible_of_base_cover_owner_equalities
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      T
      hT
      right
      gr
      hcomm
      B
      hB
      w
      hfirst_e
      Cbase
      hCbase
      baseRight
      baseGr
      hbaseComp
      hbase_e
      htarget_e
  have hsigma :
      Presieve.IsSheafFor
        ((F.obj e).1)
        (Presieve.bindOfArrows
          (fun i : R.uncurry ↦ i.1.1)
          (fun i ↦ i.1.2)
          T) :=
    stage_sheaf_isSheafFor_sigma_refinement
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (hR := hR)
      T
      hT
  rw [sigma_refinement_eq_ofArrows (β := β) (F := F) (hcover := hcover) T,
    Presieve.isSheafFor_arrows_iff] at hsigma
  obtain ⟨te, hte, _⟩ := hsigma
    (fun q : Σ i : R.uncurry, (T i).uncurry ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1))
    hsigma_compatible
  have hte_base :
      ∀ i : R.uncurry, ((F.obj e).1.map i.1.2.op) te = w i :=
    sigma_refinement_stage_glue_restricts_to_base_family
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      T
      hT
      w
      te
      hte
  let z :=
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op U)) te
  refine ⟨z, ?_, ?_⟩
  · intro i
    -- The glued stage section maps to an amalgamation of the original colimit family.
    simpa [z] using
      presheafColimit_stage_glue_image_is_amalgamation
        (β := β)
        (F := F)
        (x := x)
        (v := w)
        (hv_image := hw_image)
        (tc := te)
        (htc := hte_base)
        i
  · intro z' hz'
    -- Uniqueness is exactly the separatedness of the presheaf colimit on `R`.
    apply hsep.ext
    intro Y f hf
    let i : R.uncurry := ⟨⟨Y, f⟩, hf⟩
    exact (hz i).trans (hz' i).symm

/-- Helper for Lemma 7.17.10: the underlying presheaf colimit is already a sheaf for the
Grothendieck topology generated by `K`. -/
lemma presheafColimit_isSheaf_of_coveringPresieveCardinal_lt_cof :
    Presieve.IsSheaf J (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) := by
  -- Promote the one-cover proof to all sieves in `J = K.toGrothendieck`.
  rw [Presieve.isSheaf_coverage]
  intro U R hR
  exact presheafColimit_isSheafFor_of_coveringPresieveCardinal_lt_cof β F hcover hR

/-- Helper for Lemma 7.17.10: the underlying presheaf colimit is separated under the small-cover
cofinality hypothesis. -/
lemma presheafColimit_isSeparated_of_coveringPresieveCardinal_lt_cof :
    Presieve.IsSeparated J (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) := by
  -- Sheafness gives separatedness without reopening the local compatibility argument.
  exact
    (presheafColimit_isSheaf_of_coveringPresieveCardinal_lt_cof β F hcover).isSeparated

/-- Helper for Lemma 7.17.10: once the presheaf colimit is known to be a sheaf, the canonical
comparison on sections is an isomorphism. -/
lemma comparison_isIso_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    IsIso (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := by
  let P := colimit (F ⋙ sheafToPresheaf J (Type (max u v)))
  have hP : Presieve.IsSheaf J P :=
    presheafColimit_isSheaf_of_coveringPresieveCardinal_lt_cof β F hcover
  let e :
      ((presheafToSheaf J (Type (max u v))).obj P) ≅ @colimit _ _ _ _ F inferInstance :=
    (colimit.isoColimitCocone
      ⟨Sheaf.sheafifyCocone
          (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm
  -- Rewrite the comparison as a composite of three isomorphisms.
  rw [colimit_post_eq_toSheafify_comparison_app β F U]
  haveI :
      IsIso
        (colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
          ((evaluation Cᵒᵖ (Type (max u v))).obj (op U))) := by
    infer_instance
  haveI : IsIso ((CategoryTheory.toSheafify J P).app (op U)) := by
    have hToSheafify : IsIso (CategoryTheory.toSheafify J P) := by
      exact CategoryTheory.isIso_toSheafify hP
    exact (NatTrans.isIso_iff_isIso_app _).1 hToSheafify (op U)
  haveI : IsIso (e.hom.1.app (op U)) := by
    have hMapIso : IsIso ((sheafToPresheaf J (Type (max u v))).map e.hom) := by
      infer_instance
    change IsIso
      (((sheafToPresheaf J (Type (max u v))).map e.hom).app (op U))
    exact (NatTrans.isIso_iff_isIso_app _).1 hMapIso (op U)
  infer_instance

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
injective. This is the injective half of the source-facing bijectivity statement for the canonical
owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := by
  -- The comparison map is an isomorphism once the presheaf colimit is known to be a sheaf.
  haveI : IsIso (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
    comparison_isIso_of_coveringPresieveCardinal_lt_cof β F hcover U
  exact
    (ConcreteCategory.bijective_of_isIso
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U)))).1

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
surjective. This is the surjective half of the source-facing bijectivity statement for the
canonical owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Surjective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := by
  -- The same isomorphism gives the surjective half immediately.
  haveI : IsIso (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
    comparison_isIso_of_coveringPresieveCardinal_lt_cof β F hcover U
  exact
    (ConcreteCategory.bijective_of_isIso
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U)))).2

/-- Lemma 7.17.10: let `K` be a chosen coverage on `C`. If the cofinality of `β` dominates the
cardinality of every `K`-covering presieve of each object `U`, then for every `U` the canonical
map from the filtered colimit of the section sets `F i (U)` to the section set of the colimit
sheaf is bijective. -/
theorem sheafFilteredColimitSectionsComparison_bijective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Bijective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
  ⟨sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
      β F hcover U,
    sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
      β F hcover U⟩

end

end CategoryTheory
