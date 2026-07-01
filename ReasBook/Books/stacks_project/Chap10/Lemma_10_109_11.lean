import Mathlib
import stacks_project.Chap10.Lemma_10_84_2
import stacks_project.Chap10.Lemma_10_109_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Order
open scoped Ordinal DirectSum

universe u v w

section

variable {R : Type u} [Ring R]
variable {ι : Type w} [LinearOrder ι] [IsWellOrder ι (· < ·)]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.109.11: categorical projectivity of `ModuleCat.of R P` implies the usual
module-theoretic projectivity of `P`. -/
lemma module_projective_of_categorical_projective
    {P : Type (max u v)} [AddCommGroup P] [Module R P]
    (hP : Projective (ModuleCat.of R P)) :
    Module.Projective R P := by
  -- We convert categorical lifts along epis into lifts along surjective linear maps.
  let _ : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{max u v, u} R)) ULift.up_injective
  refine Module.Projective.of_lifting_property ?_
  intro A B _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R P) := hP
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.109.11: a categorical projective-dimension bound `≤ 0` on an `R`-module
gives the usual module-theoretic projectivity of its underlying carrier. -/
lemma module_projective_of_hasProjectiveDimensionLE_zero
    {P : Type (max u v)} [AddCommGroup P] [Module R P]
    (hP : HasProjectiveDimensionLE (ModuleCat.of R P) 0) :
    Module.Projective R P := by
  -- We first rewrite the owner bound as categorical projectivity, then forget back to modules.
  have hproj_cat : Projective (ModuleCat.of R P) := by
    exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R P)).2 hP
  exact module_projective_of_categorical_projective (R := R) hproj_cat

/-- Helper for Lemma 10.109.11: if a quotient `P ⧸ N` is projective, then `N` splits off from
`P`. -/
lemma exists_isCompl_of_projective_quotient
    {P : Type (max u v)} [AddCommGroup P] [Module R P] (N : Submodule R P)
    (hproj : Module.Projective R (P ⧸ N)) :
    ∃ q : Submodule R P, IsCompl N q := by
  classical
  let _ : Module.Projective R (P ⧸ N) := hproj
  -- A projective quotient gives a section of the quotient map.
  have hsplitQ : ∃ s : (P ⧸ N) →ₗ[R] P, N.mkQ ∘ₗ s = LinearMap.id := by
    simpa using Module.projective_lifting_property N.mkQ (LinearMap.id : (P ⧸ N) →ₗ[R] (P ⧸ N))
      (Submodule.mkQ_surjective N)
  -- The splitting lemma turns that section into a retraction onto `N`.
  have hsplitN :
      ∃ r : P →ₗ[R] N, r ∘ₗ N.subtype = LinearMap.id := by
    exact
      (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ N)
        Subtype.val_injective (Submodule.mkQ_surjective N)).out 0 1 |>.mp hsplitQ
  rcases hsplitN with ⟨r, hr⟩
  -- The kernel of the retraction is the desired complementary summand.
  refine ⟨LinearMap.ker r, ?_⟩
  simpa using (LinearMap.isCompl_of_proj (p := N) (fun x ↦ by
    simpa using LinearMap.congr_fun hr x))

/-- Helper for Lemma 10.109.11: reindexing a submodule family along the ordinal enumeration of the
ambient well-order does not change its supremum. -/
lemma iSup_enum_wellOrderingRel_submodule (A : ι → Submodule R M) :
    (⨆ x : (Ordinal.type (@WellOrderingRel ι)).ToType, A (Ordinal.enum WellOrderingRel x)) =
      iSup A := by
  let o : Ordinal := Ordinal.type (@WellOrderingRel ι)
  refine le_antisymm ?_ ?_
  · -- Every reindexed summand is one of the original summands.
    refine iSup_le fun x ↦ le_iSup_of_le (Ordinal.enum WellOrderingRel x) le_rfl
  · -- Every original summand appears at its own `typein` index.
    refine iSup_le fun i ↦ ?_
    let x : o.ToType :=
      Ordinal.ToType.mk ⟨Ordinal.typein (@WellOrderingRel ι) i, Ordinal.typein_lt_type _ i⟩
    have hx : Ordinal.enum WellOrderingRel x = i := by
      simpa [x, o] using (Ordinal.enum_typein (r := @WellOrderingRel ι) i)
    simpa [hx] using
      (le_iSup (fun x : o.ToType ↦ A (Ordinal.enum WellOrderingRel x)) x)

/-- Helper for Lemma 10.109.11: reindexing a submodule family along the given well-order
enumeration preserves its supremum. -/
lemma iSup_enum_submodule (A : ι → Submodule R M) :
    (⨆ x : (Ordinal.type (α := ι) (· < ·)).ToType, A (Ordinal.enum (α := ι) (· < ·) x)) =
      iSup A := by
  let o : Ordinal := Ordinal.type (α := ι) (· < ·)
  refine le_antisymm ?_ ?_
  · -- Every reindexed summand is one of the original summands.
    refine iSup_le fun x ↦ le_iSup_of_le (Ordinal.enum (α := ι) (· < ·) x) le_rfl
  · -- Every original summand appears at its own `typein` index.
    refine iSup_le fun i ↦ ?_
    let x : o.ToType :=
      Ordinal.ToType.mk ⟨Ordinal.typein (α := ι) (· < ·) i, Ordinal.typein_lt_type _ i⟩
    have hx : Ordinal.enum (α := ι) (· < ·) x = i := by
      simpa [x, o] using (Ordinal.enum_typein (α := ι) (r := (· < ·)) i)
    exact hx ▸
      (le_iSup (fun x : o.ToType ↦ A (Ordinal.enum (α := ι) (· < ·) x)) x)

/-- Helper for Lemma 10.109.11: at the order type itself, the typein-prefix supremum recovers the
full reindexed supremum. -/
lemma typein_prefix_orderType_eq_iSup_submodule
    (B : (Ordinal.type (α := ι) (· < ·)).ToType → Submodule R M) :
    (⨆ x : {x : (Ordinal.type (α := ι) (· < ·)).ToType //
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) x <
          Ordinal.type (α := ι) (· < ·)}, B x.1) = iSup B := by
  refine le_antisymm ?_ ?_
  · -- Forgetting the rank bound embeds the prefix family into the full family.
    refine iSup_le fun x ↦ le_iSup B x.1
  · -- Every index lies below the order type of the well-ordered index set.
    refine iSup_le fun x ↦ le_iSup_of_le ⟨x, Ordinal.typein_lt_self x⟩ le_rfl

/-- Helper for Lemma 10.109.11: reindex the well-ordered filtration by its ordinal enumeration. -/
noncomputable abbrev wellOrderedStageFamily (M_ : ι → Submodule R M) :
    (Ordinal.type (α := ι) (· < ·)).ToType → Submodule R M :=
  fun x ↦ M_ (Ordinal.enum (α := ι) (· < ·) x)

/-- Helper for Lemma 10.109.11: the prefix stages of the ordinal reindexing of the filtration. -/
noncomputable abbrev wellOrderedPrefixStage (M_ : ι → Submodule R M) (β : Ordinal) :
    Submodule R M :=
  ⨆ x :
      {x : (Ordinal.type (α := ι) (· < ·)).ToType //
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) x < β},
      wellOrderedStageFamily (R := R) (M := M) M_ x.1

/-- Helper for Lemma 10.109.11: the ordinal index `b` maps back to an element whose `typein` is
exactly `b`. -/
lemma typein_wellOrderedPrefixIndex
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) (Ordinal.ToType.mk b) =
      b.1 := by
  -- The chosen ordinal representative is the enumeration point at rank `b`.
  simpa [Ordinal.ToType.mk, Ordinal.type_toType] using
    (Ordinal.typein_enum (α := (Ordinal.type (α := ι) (· < ·)).ToType) (r := (· < ·))
      (h := b.2))

/-- Helper for Lemma 10.109.11: the predecessor prefix stage is the supremum of the original
filtration stages strictly below the corresponding index. -/
lemma wellOrdered_prefixStage_eq_iSup_lt
    (M_ : ι → Submodule R M)
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    wellOrderedPrefixStage (R := R) (M := M) M_ b.1 = ⨆ e' : Set.Iio e, M_ e' := by
  classical
  let o : Ordinal := Ordinal.type (α := ι) (· < ·)
  let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
  -- Compare the prefix indices with the original order using `typein` and `enum`.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    have hxb : x.1.toOrd < b := by
      simpa using x.2
    have hlt : Ordinal.enum (α := ι) (· < ·) x.1 < e := by
      simpa [e] using
        (Ordinal.enum_lt_enum (r := (· < ·)) (o₁ := x.1.toOrd) (o₂ := b)).2 hxb
    exact le_iSup_of_le ⟨Ordinal.enum (α := ι) (· < ·) x.1, hlt⟩ le_rfl
  · refine iSup_le fun e' ↦ ?_
    let xOrd : Set.Iio o :=
      ⟨Ordinal.typein (α := ι) (· < ·) e'.1, Ordinal.typein_lt_type (r := (· < ·)) e'.1⟩
    let x : o.ToType := Ordinal.ToType.mk xOrd
    have hx_typein :
        Ordinal.typein (α := o.ToType) (· < ·) x = Ordinal.typein (α := ι) (· < ·) e'.1 := by
      -- Re-encoding `e'` through `Ordinal.ToType.mk` preserves its ordinal rank.
      simpa [x, xOrd, o, Ordinal.ToType.mk, Ordinal.type_toType] using
        (Ordinal.typein_enum (α := o.ToType) (r := (· < ·)) (h := xOrd.2))
    have he_typein : Ordinal.typein (α := ι) (· < ·) e = b.1 := by
      -- The chosen stage index `e` is exactly the element at rank `b`.
      simpa [e] using (Ordinal.typein_enum (α := ι) (r := (· < ·)) (h := b.2))
    have hxlt : Ordinal.typein (α := o.ToType) (· < ·) x < b.1 := by
      have he' :
          Ordinal.typein (α := ι) (· < ·) e'.1 < Ordinal.typein (α := ι) (· < ·) e := by
        exact (Ordinal.typein_lt_typein (r := (· < ·))).2 e'.2
      simpa [hx_typein, he_typein] using he'
    have hx_enum : Ordinal.enum (α := ι) (· < ·) x = e'.1 := by
      -- Decoding the `typein` rank of `e'` recovers `e'` itself.
      simpa [x, xOrd, o] using (Ordinal.enum_typein (α := ι) (r := (· < ·)) e'.1)
    exact le_iSup_of_le ⟨x, hxlt⟩ (by simpa [wellOrderedStageFamily, hx_enum])

/-- Helper for Lemma 10.109.11: the successor prefix stage is exactly the filtration stage indexed
by the fresh well-ordered element. -/
lemma wellOrdered_prefixStage_succ_eq_stage
    (M_ : ι → Submodule R M) (hmono : Monotone M_)
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) = M_ e := by
  classical
  let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
  have hprefix_succ :
      wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) =
        wellOrderedPrefixStage (R := R) (M := M) M_ b.1 ⊔ M_ e := by
    -- Split the prefix at `b + 1` into the old prefix and the unique fresh stage of rank `b`.
    refine le_antisymm ?_ ?_
    · refine iSup_le fun x ↦ ?_
      have hxle :
          Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) x.1 ≤ b.1 := by
        simpa using (lt_succ_iff.mp x.2)
      rcases le_iff_eq_or_lt.mp hxle with hxb | hxb
      · have hxeq : x.1 = Ordinal.ToType.mk b := by
          apply (Ordinal.typein_injective (r := (· < ·)))
          rw [typein_wellOrderedPrefixIndex b]
          exact hxb
        simpa [wellOrderedStageFamily, e, hxeq] using
          (le_sup_right : M_ e ≤
            wellOrderedPrefixStage (R := R) (M := M) M_ b.1 ⊔ M_ e)
      · exact le_sup_of_le_left <| le_iSup_of_le ⟨x.1, hxb⟩ le_rfl
    · refine sup_le ?_ ?_
      · refine iSup_le fun x ↦ ?_
        exact le_iSup_of_le ⟨x.1, lt_of_lt_of_le x.2 (le_succ b.1)⟩ le_rfl
      · have hnew_lt :
          Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·)
              (Ordinal.ToType.mk b) <
            b.1 + 1 := by
          rw [typein_wellOrderedPrefixIndex b]
          simpa using (lt_succ b.1)
        exact le_iSup_of_le ⟨Ordinal.ToType.mk b, hnew_lt⟩ (by simp [wellOrderedStageFamily, e])
  -- The old prefix already lies inside `M_e`, so the successor prefix collapses to `M_e`.
  refine le_antisymm ?_ ?_
  · rw [hprefix_succ]
    refine sup_le ?_ le_rfl
    rw [wellOrdered_prefixStage_eq_iSup_lt (R := R) (M := M) (ι := ι) (M_ := M_) (b := b)]
    refine iSup_le fun e' ↦ hmono e'.2.le
  · have hnew_lt :
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·)
            (Ordinal.ToType.mk b) <
          b.1 + 1 := by
      rw [typein_wellOrderedPrefixIndex b]
      simpa using (lt_succ b.1)
    exact le_iSup_of_le ⟨Ordinal.ToType.mk b, hnew_lt⟩ (by simp [wellOrderedStageFamily])

/-- Helper for Lemma 10.109.11: in the zero-dimensional case, a well-ordered filtration with
projective successive quotients splits as a direct sum of those quotients. -/
lemma projective_of_wellOrdered_submodule_union_of_projective_successive_quotients
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤)
    (hquot :
      ∀ e : ι,
        Module.Projective R
          (M_ e ⧸ (⨆ e' : Set.Iio e, M_ e').comap (M_ e).subtype)) :
    Module.Projective R M := by
  classical
  let o : Ordinal := Ordinal.type (α := ι) (· < ·)
  let prefixStage : Ordinal → Submodule R M :=
    wellOrderedPrefixStage (R := R) (M := M) M_
  have hprefix_zero : prefixStage 0 = ⊥ := by
    -- No index has negative rank, so the zero prefix is trivial.
    refine le_antisymm ?_ bot_le
    refine iSup_le fun x ↦ False.elim (by simpa using x.2)
  have hprefix_top : prefixStage o = ⊤ := by
    -- At the order type, the reindexed prefixes already see the whole filtration.
    calc
      prefixStage o = iSup (wellOrderedStageFamily (R := R) (M := M) M_) := by
        simpa [prefixStage, o, wellOrderedPrefixStage] using
          typein_prefix_orderType_eq_iSup_submodule
            (R := R) (M := M) (ι := ι)
            (wellOrderedStageFamily (R := R) (M := M) M_)
      _ = iSup M_ := by
        simpa [wellOrderedStageFamily, o] using
          iSup_enum_submodule (R := R) (M := M) (ι := ι) M_
      _ = ⊤ := hcover
  have hprefix_mono : Monotone prefixStage := by
    -- Enlarging the ordinal bound can only add more reindexed stages to the prefix.
    intro β γ hβγ
    refine iSup_le fun x ↦ le_iSup_of_le ⟨x.1, lt_of_lt_of_le x.2 hβγ⟩ le_rfl
  have hprefix_limit :
      ∀ {α : Ordinal}, α < o + 1 → IsSuccLimit α →
        prefixStage α = ⨆ β : Set.Iio α, prefixStage β.1 := by
    intro α hα hlimit
    -- At a limit stage, every element already appears in some earlier successor prefix.
    refine le_antisymm ?_ ?_
    · refine iSup_le fun x ↦ ?_
      have hx_lt :
          Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1 < α := by
        simpa using hlimit.succ_lt x.2
      refine le_iSup_of_le ⟨Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1, hx_lt⟩ ?_
      have hx_mem :
          Ordinal.typein (α := o.ToType) (· < ·) x.1 <
            Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1 := by
        simpa using (lt_succ (Ordinal.typein (α := o.ToType) (· < ·) x.1))
      exact le_iSup_of_le ⟨x.1, hx_mem⟩ le_rfl
    · refine iSup_le fun β ↦ hprefix_mono (le_of_lt β.2)
  have hprefix_successive_projective :
      ∀ b : Set.Iio o,
        Module.Projective R
          (prefixStage (b.1 + 1) ⧸ (prefixStage b.1).comap (prefixStage (b.1 + 1)).subtype) := by
    intro b
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    -- Rewrite the prefix quotient to the textbook quotient before invoking the hypothesis.
    change Module.Projective R
      (wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) ⧸
        (wellOrderedPrefixStage (R := R) (M := M) M_ b.1).comap
          (wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1)).subtype)
    rw [wellOrdered_prefixStage_succ_eq_stage (R := R) (M := M) (ι := ι) (M_ := M_) hmono b,
      wellOrdered_prefixStage_eq_iSup_lt (R := R) (M := M) (ι := ι) (M_ := M_) (b := b)]
    simpa [e] using hquot e
  have hlength_pos : 0 < o + 1 := by
    simpa using (Ordinal.zero_lt_succ o)
  have hiSup_stages : (⨆ α : Set.Iio (o + 1), prefixStage α.1) = ⊤ := by
    -- The top prefix occurs already at index `o`.
    refine le_antisymm le_top ?_
    rw [← hprefix_top]
    exact le_iSup_of_le ⟨o, by simpa using (lt_succ o)⟩ le_rfl
  let D : DirectSumDevissage.{u, max u v, w} R M :=
    { length := o + 1
      length_pos := hlength_pos
      stages := ⟨prefixStage, hprefix_mono⟩
      stage_zero := hprefix_zero
      iSup_stages := hiSup_stages
      stage_limit := by
        intro α hα hlimit
        exact hprefix_limit hα hlimit
      stage_succ_isCompl := by
        intro α hα
        have hsucc_le : α + 1 ≤ o := by
          have hα' : α + 1 < succ o := by
            simpa [o] using hα
          exact lt_succ_iff.mp hα'
        let b : Set.Iio o := ⟨α, (lt_succ α).trans_le hsucc_le⟩
        -- The source proof splits each successor quotient because it is projective.
        exact exists_isCompl_of_projective_quotient
          ((prefixStage α).comap (prefixStage (α + 1)).subtype)
          (hprefix_successive_projective b) }
  obtain ⟨eD⟩ := DirectSumDevissage.nonempty_linearEquiv_directSum_successiveQuotients D
  have hsum_projective :
      Module.Projective R (Π₀ α : D.successorIndex, D.successiveQuotient α) := by
    letI : ∀ α : D.successorIndex, Module.Projective R (D.successiveQuotient α) := by
      intro α
      have hsucc_le : α.1 + 1 ≤ o := by
        have hα' : α.1 + 1 < succ o := by
          simpa [D, o] using α.2
        exact lt_succ_iff.mp hα'
      let b : Set.Iio o := ⟨α.1, (lt_succ α.1).trans_le hsucc_le⟩
      -- Each successor quotient of the packaged dévissage is one of the projective prefix quotients.
      simpa [D, prefixStage, DirectSumDevissage.successiveQuotient, DirectSumDevissage.predecessorStage]
        using hprefix_successive_projective b
    infer_instance
  have hsum_projective' :
      Module.Projective R (⨁ α : D.successorIndex, D.successiveQuotient α) := by
    simpa using hsum_projective
  let _ : Module.Projective R (⨁ α : D.successorIndex, D.successiveQuotient α) :=
    hsum_projective'
  -- Rebuild `M` from the direct sum of projective successor quotients.
  exact Module.Projective.of_equiv' eD.symm

/-- Helper for Lemma 10.109.11: the supported free stages inherit monotonicity from the original
well-ordered submodule filtration. -/
lemma supported_free_cover_mono
    (M_ : ι → Submodule R M) (hmono : Monotone M_) :
    Monotone (fun e ↦ Finsupp.supported R R (↑(M_ e) : Set M)) := by
  intro e e' hee'
  -- Enlarging the module stage enlarges the allowed support set in the free cover stage.
  exact Finsupp.supported_mono
    (show (↑(M_ e) : Set M) ⊆ (↑(M_ e') : Set M) from hmono hee')

/-- Helper for Lemma 10.109.11: every element of a lower filtration stage lifts to the
corresponding lower supported free stage under the global free-cover map. -/
lemma supported_free_cover_lower_preimage
    (M_ : ι → Submodule R M) (hmono : Monotone M_) {e : ι} {m : M}
    (hm : m ∈ ⨆ e' : Set.Iio e, M_ e') :
    ∃ y : M →₀ R,
      y ∈ ⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M) ∧
      Finsupp.linearCombination R (id : M → M) y = m := by
  classical
  by_cases hne : Nonempty (Set.Iio e)
  · letI := hne
    have hdir : Directed (· ≤ ·) (fun e' : Set.Iio e ↦ M_ e'.1) := by
      intro a b
      rcases le_total a.1 b.1 with hab | hba
      · exact ⟨b, hmono hab, le_rfl⟩
      · exact ⟨a, le_rfl, hmono hba⟩
    -- Directedness lets us place the lower-stage element in one concrete earlier filtration stage.
    rcases (Submodule.mem_iSup_of_directed _ hdir).mp hm with ⟨e', hm'⟩
    refine ⟨Finsupp.single m 1, ?_, ?_⟩
    · -- The singleton basis vector is supported in that earlier stage, hence in the lower free union.
      exact Submodule.mem_iSup_of_mem e' (Finsupp.single_mem_supported R (1 : R) hm')
    · -- The global free-cover map sends that singleton generator back to `m`.
      simp [Finsupp.linearCombination_single]
  · haveI : IsEmpty (Set.Iio e) := not_nonempty_iff.mp hne
    have hm_zero : m = 0 := by
      simpa [iSup_of_empty] using hm
    refine ⟨0, ?_, ?_⟩
    · simpa [iSup_of_empty]
    · simpa [hm_zero]

/-- Helper for Lemma 10.109.11: the lower supported-free stage is exactly the supported module on
the union of the earlier stage carriers. -/
lemma supported_free_cover_lower_eq_iUnion
    (M_ : ι → Submodule R M) (e : ι) :
    (⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M)) =
      Finsupp.supported R R (⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)) := by
  -- The lower supported stage is computed pointwise from the union of the allowed supports.
  simpa using
    (Finsupp.supported_iUnion (M := R) (R := R)
      (s := fun e' : Set.Iio e ↦ (↑(M_ e'.1) : Set M))).symm

/-- Helper for Lemma 10.109.11: the successive quotient of the supported free cover is projective,
because it is the free module on the fresh elements appearing at stage `e`. -/
lemma supported_free_cover_stage_eq_sup_fresh
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (e : ι) :
    let lowerSet : Set M := ⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)
    Finsupp.supported R R (↑(M_ e) : Set M) =
      Finsupp.supported R R lowerSet ⊔
        Finsupp.supported R R ((↑(M_ e) : Set M) \ lowerSet) := by
  let lowerSet : Set M := ⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)
  have hlower_subset_stage : lowerSet ⊆ (↑(M_ e) : Set M) := by
    -- Monotonicity puts every earlier stage inside the current stage.
    intro m hm
    rcases Set.mem_iUnion.mp hm with ⟨e', hm'⟩
    exact hmono e'.2.le hm'
  -- Split the current support set into the old support set and the genuinely fresh elements.
  calc
    Finsupp.supported R R (↑(M_ e) : Set M) =
        Finsupp.supported R R (lowerSet ∪ ((↑(M_ e) : Set M) \ lowerSet)) := by
      congr 1
      exact (Set.union_diff_cancel hlower_subset_stage).symm
    _ =
        Finsupp.supported R R lowerSet ⊔
          Finsupp.supported R R ((↑(M_ e) : Set M) \ lowerSet) := by
      rw [Finsupp.supported_union]

/-- Helper for Lemma 10.109.11: the stagewise free quotient identifies with the supported free
module on the genuinely new elements appearing at stage `e`. -/
noncomputable abbrev supported_free_cover_stage_quotient_linearEquiv_fresh_supported
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (e : ι) :
    let lowerSet : Set M := ⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)
    let stage : Submodule R (M →₀ R) := Finsupp.supported R R (↑(M_ e) : Set M)
    let lower : Submodule R (M →₀ R) := Finsupp.supported R R lowerSet
    (stage ⧸ lower.comap stage.subtype) ≃ₗ[R]
      Finsupp.supported R R ((↑(M_ e) : Set M) \ lowerSet) := by
  classical
  let lowerSet : Set M := ⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)
  let freshSet : Set M := (↑(M_ e) : Set M) \ lowerSet
  let stage : Submodule R (M →₀ R) := Finsupp.supported R R (↑(M_ e) : Set M)
  let lower : Submodule R (M →₀ R) := Finsupp.supported R R lowerSet
  let fresh : Submodule R (M →₀ R) := Finsupp.supported R R freshSet
  have hlower_eq :
      (⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M)) = lower := by
    -- Rewrite the lower supported stage as support on the union of earlier carriers.
    simpa [lower, lowerSet] using
      (Finsupp.supported_iUnion (M := R) (R := R)
        (s := fun e' : Set.Iio e ↦ (↑(M_ e'.1) : Set M))).symm
  have hstage_eq : stage = lower ⊔ fresh := by
    -- Split the stage support into its old part and the genuinely fresh support.
    have hlower_subset_stage : lowerSet ⊆ (↑(M_ e) : Set M) := by
      intro m hm
      rcases Set.mem_iUnion.mp hm with ⟨e', hm'⟩
      exact hmono e'.2.le hm'
    have h_union : lowerSet ∪ freshSet = (↑(M_ e) : Set M) := by
      simpa [freshSet] using Set.union_diff_cancel hlower_subset_stage
    calc
      stage = Finsupp.supported R R (lowerSet ∪ freshSet) := by
        simpa [stage] using congrArg (Finsupp.supported R R) h_union.symm
      _ = lower ⊔ fresh := by
        simp [lower, fresh, Finsupp.supported_union]
  have hlower_le_stage : lower ≤ stage := by
    -- Every earlier stage is contained in the current stage by monotonicity.
    exact Finsupp.supported_mono <| by
      intro m hm
      rcases Set.mem_iUnion.mp hm with ⟨e', hm'⟩
      exact hmono e'.2.le hm'
  have hfresh_le_stage : fresh ≤ stage := by
    -- Fresh support points are, by definition, still points of the current stage.
    exact Finsupp.supported_mono <| by
      intro m hm
      exact hm.1
  have hdisjoint : Disjoint lower fresh := by
    -- Old support and fresh support are disjoint subsets of the stage support.
    refine Finsupp.disjoint_supported_supported ?_
    refine Set.disjoint_left.mpr ?_
    intro m hmLower hmFresh
    exact hmFresh.2 hmLower
  let old : Set.Iic stage := ⟨lower, hlower_le_stage⟩
  let new : Set.Iic stage := ⟨fresh, hfresh_le_stage⟩
  have hcompl_iic : IsCompl old new := by
    -- Inside the interval of submodules below `stage`, the old and fresh pieces are complementary.
    rw [Set.Iic.isCompl_iff]
    exact ⟨hdisjoint, by simpa [old, new] using hstage_eq.symm⟩
  have hcompl_stage :
      IsCompl (lower.comap stage.subtype) (fresh.comap stage.subtype) := by
    -- Transfer the complement decomposition from the interval view back to submodules of `stage`.
    exact ((stage.mapIic).symm.isCompl_iff (x := old) (y := new)).1 hcompl_iic
  have hmap_fresh : (fresh.comap stage.subtype).map stage.subtype = fresh := by
    -- Mapping the fresh piece back to the ambient free module recovers the original fresh summand.
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hfresh_le_stage]
  -- First identify the quotient with the complementary fresh piece inside the stage, then push
  -- that piece back into the ambient free module.
  let e0 :
      (stage ⧸ lower.comap stage.subtype) ≃ₗ[R] fresh :=
    (Submodule.quotientEquivOfIsCompl
      ((show Submodule R stage from lower.comap stage.subtype))
      ((show Submodule R stage from fresh.comap stage.subtype))
      hcompl_stage) ≪≫ₗ
      (stage.equivSubtypeMap (fresh.comap stage.subtype)) ≪≫ₗ
      LinearEquiv.ofEq _ _ hmap_fresh
  simpa [stage, lower, fresh, freshSet] using e0

/-- Helper for Lemma 10.109.11: the successive quotient of the supported free cover is projective,
because it is the free module on the fresh elements appearing at stage `e`. -/
lemma supported_free_cover_stage_quotient_projective
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (e : ι) :
    Module.Projective R
      (Finsupp.supported R R (↑(M_ e) : Set M) ⧸
        (⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M)).comap
          (Finsupp.supported R R (↑(M_ e) : Set M)).subtype) := by
  classical
  let lowerSet : Set M := ⋃ e' : Set.Iio e, (↑(M_ e'.1) : Set M)
  let freshSet : Set M := (↑(M_ e) : Set M) \ lowerSet
  let fresh : Submodule R (M →₀ R) := Finsupp.supported R R freshSet
  have hlower_eq :
      (⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M)) =
        Finsupp.supported R R lowerSet := by
    -- Rewrite the lower supported stage as support on the union of earlier carriers.
    simpa [lowerSet] using
      (Finsupp.supported_iUnion (M := R) (R := R)
        (s := fun e' : Set.Iio e ↦ (↑(M_ e'.1) : Set M))).symm
  let efresh : fresh ≃ₗ[R] (freshSet →₀ R) :=
    Finsupp.supportedEquivFinsupp freshSet
  have hfresh_projective : Module.Projective R fresh := by
    -- The fresh supported summand is a free module on the newly appearing support points.
    let _ : Module.Projective R (freshSet →₀ R) := by infer_instance
    exact Module.Projective.of_equiv' efresh.symm
  have hstage_equiv :
      (Finsupp.supported R R (↑(M_ e) : Set M) ⧸
        (⨆ e' : Set.Iio e, Finsupp.supported R R (↑(M_ e') : Set M)).comap
          (Finsupp.supported R R (↑(M_ e) : Set M)).subtype) ≃ₗ[R] fresh := by
    -- Rewrite the lower denominator to the support on the union of earlier carriers.
    convert
      supported_free_cover_stage_quotient_linearEquiv_fresh_supported
        (R := R) (M_ := M_) hmono e using 1
    rw [hlower_eq]
  -- Transport projectivity back across the quotient/fresh-support equivalence.
  exact Module.Projective.of_equiv'
    hstage_equiv.symm

/-- Helper for Lemma 10.109.11: quotienting a surjective linear map by compatible submodules
preserves surjectivity. -/
lemma mapQ_surjective_of_surjective
    {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] Q)
    (hφ : Function.Surjective φ)
    (p : Submodule R P)
    (q : Submodule R Q)
    (hpq : p ≤ Submodule.comap φ q) :
    Function.Surjective (p.mapQ q φ hpq) := by
  -- Lift a quotient representative in the target back along the original surjection.
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective q y
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Helper for Lemma 10.109.11: a projective `R`-module has projective dimension at most `n` for
every `n`. -/
lemma hasProjectiveDimensionLE_of_module_projective
    {P : Type (max u v)} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (n : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R P) n := by
  induction n with
  | zero =>
      -- In degree `0`, projective dimension `≤ 0` is exactly categorical projectivity.
      rw [← CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero]
      infer_instance
  | succ n ih =>
      -- The owner bound is monotone in the integer parameter.
      infer_instance

/-- Helper for Lemma 10.109.11: when the index set is nonempty and the original filtration covers
`M`, the supported free-cover stages cover the whole free module on `M`. -/
lemma supported_free_cover_iSup_eq_top [Nonempty ι]
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤) :
    (⨆ e : ι, Finsupp.supported R R (↑(M_ e) : Set M)) = ⊤ := by
  have hcarrier : (⋃ e : ι, (↑(M_ e) : Set M)) = Set.univ := by
    -- Every element of `M` lies in some stage because the filtration supremum is `⊤`.
    ext m
    constructor
    · intro _
      simp
    · intro _
      have hm : m ∈ iSup M_ := by
        simpa [hcover] using (show m ∈ (⊤ : Submodule R M) from by simp)
      rcases (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hm with ⟨e, he⟩
      exact Set.mem_iUnion.mpr ⟨e, he⟩
  -- Rewrite the stage supremum as support on the union of all carriers.
  calc
    (⨆ e : ι, Finsupp.supported R R (↑(M_ e) : Set M)) =
        Finsupp.supported R R (⋃ e : ι, (↑(M_ e) : Set M)) := by
      simpa using
        (Finsupp.supported_iUnion (M := R) (R := R) (s := fun e : ι ↦ (↑(M_ e) : Set M))).symm
    _ = Finsupp.supported R R (Set.univ : Set M) := by rw [hcarrier]
    _ = ⊤ := Finsupp.supported_univ

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat R` together with well-ordered filtrations by
  submodules;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`;
* best owner abstraction: the ambient owner notion is `HasProjectiveDimensionLE` on
  `ModuleCat.of R M`, while the short-exact `LT` lemmas are the canonical core step used on each
  successor quotient;
* layer triage: this item is `bridge/view`, translating the source-facing well-ordered submodule
  filtration into the canonical projective-dimension owner API;
* primitive data: the filtration `M_ : ι → Submodule R M` together with monotonicity and
  exhaustiveness;
* derived API: the bound on `M`, obtained from the owner short-exact machinery applied to the
  successive quotient hypotheses.
-/

-- Proof sketch: argue by induction on the projective-dimension bound. For `n = 0`, split each
-- successor quotient, identify `M` with the direct sum of these projective factors, and apply the
-- canonical projectivity of arbitrary direct sums. For `n + 1`, choose compatible free covers of
-- the stages, pass to the well-ordered union of the kernels, use the short exact sequence bound on
-- successive quotients from Lemma 10.109.9, and apply the induction hypothesis to the kernel
-- filtration.
/-- Lemma 10.109.11: if `M` is the union of a well-ordered increasing family of submodules `Mₑ`,
and each successive quotient `Mₑ / ⋃_{e' < e} M_{e'}` has projective dimension at most `n`, then
`M` itself has projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_of_wellOrdered_submodule_union
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤) (n : ℕ)
    (hquot :
      ∀ e : ι,
        HasProjectiveDimensionLE
          (ModuleCat.of R (M_ e ⧸ (⨆ e' : Set.Iio e, M_ e').comap (M_ e).subtype)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing M with
  | zero =>
      -- In projective dimension `0`, the source proof splits the well-ordered filtration into a
      -- direct sum of projective successive quotients.
      rw [← CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R M)]
      let _ : Module.Projective R M :=
        projective_of_wellOrdered_submodule_union_of_projective_successive_quotients
        (R := R) (M_ := M_) hmono hcover (fun e ↦
          module_projective_of_hasProjectiveDimensionLE_zero (R := R) (hquot e))
      infer_instance
  | succ n ih =>
      -- Route correction: the source successor step must use one global supported free cover,
      -- then filter its single global kernel by the stage supports.
      by_cases hι : Nonempty ι
      · letI := hι
        let π : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R (id : M → M)
        let K : Submodule R (M →₀ R) := LinearMap.ker π
        let Fstage : ι → Submodule R (M →₀ R) :=
          fun e ↦ Finsupp.supported R R (↑(M_ e) : Set M)
        let lowerF : ∀ e : ι, Submodule R (Fstage e) :=
          fun e ↦ (⨆ e' : Set.Iio e, Fstage e').comap (Fstage e).subtype
        let πStage : ∀ e : ι, Fstage e →ₗ[R] M_ e :=
          fun e ↦
            LinearMap.codRestrict (M_ e) (π.comp (Fstage e).subtype) <| by
              intro x
              change (Finsupp.linearCombination R (id : M → M)) x.1 ∈ M_ e
              have hx :
                  ↑x.1.support ⊆ (↑(M_ e) : Set M) :=
                (Finsupp.mem_supported (M := R) (R := R) (s := (↑(M_ e) : Set M)) x.1).1 x.2
              refine Submodule.sum_mem _ fun m hm ↦ ?_
              exact (M_ e).smul_mem _ (hx hm)
        let lowerM : ∀ e : ι, Submodule R (M_ e) :=
          fun e ↦ (⨆ e' : Set.Iio e, M_ e').comap (M_ e).subtype
        have hFmono : Monotone Fstage :=
          supported_free_cover_mono (R := R) (M := M) (M_ := M_) hmono
        have hFcover : iSup Fstage = ⊤ :=
          supported_free_cover_iSup_eq_top (R := R) (M := M) (M_ := M_) hmono hcover
        have hlowerF_le :
            ∀ e : ι, lowerF e ≤ Submodule.comap (πStage e) (lowerM e) := by
          intro e
          intro x hx
          change (Finsupp.linearCombination R (id : M → M)) x.1 ∈ ⨆ e' : Set.Iio e, M_ e'
          by_cases hne : Nonempty (Set.Iio e)
          · letI := hne
            have hdir : Directed (· ≤ ·) (fun e' : Set.Iio e ↦ Fstage e'.1) := by
              intro a b
              rcases le_total a.1 b.1 with hab | hba
              · exact ⟨b, hFmono hab, le_rfl⟩
              · exact ⟨a, le_rfl, hFmono hba⟩
            rcases (Submodule.mem_iSup_of_directed _ hdir).mp hx with ⟨e', hx'⟩
            have hxmem :
                ↑x.1.support ⊆ (↑(M_ e'.1) : Set M) :=
              (Finsupp.mem_supported (M := R) (R := R) (s := (↑(M_ e'.1) : Set M)) x.1).1 hx'
            have hsum : (Finsupp.linearCombination R (id : M → M)) x.1 ∈ M_ e'.1 := by
              change x.1.sum (fun m a ↦ a • m) ∈ M_ e'.1
              refine Submodule.sum_mem _ fun m hm ↦ ?_
              exact (M_ e'.1).smul_mem _ (hxmem hm)
            exact Submodule.mem_iSup_of_mem e' hsum
          · haveI : IsEmpty (Set.Iio e) := not_nonempty_iff.mp hne
            have hx0 : x = 0 := by simpa [lowerF, iSup_of_empty] using hx
            simpa [hx0]
        let πBar : ∀ e : ι, (Fstage e ⧸ lowerF e) →ₗ[R] (M_ e ⧸ lowerM e) :=
          fun e ↦ (lowerF e).mapQ (lowerM e) (πStage e) (hlowerF_le e)
        let Kstage : ι → Submodule R K :=
          fun e ↦ Submodule.comap K.subtype (Fstage e)
        have hKmono : Monotone Kstage := by
          intro e e' hee'
          exact Submodule.comap_mono (hFmono hee')
        have hKcover : iSup Kstage = ⊤ := by
          -- Every element of the global kernel has finite support, hence lies in some stage.
          have htop : (⊤ : Submodule R K) ≤ iSup Kstage := by
            intro x _
            have hxF : (x : M →₀ R) ∈ iSup Fstage := by
              rw [hFcover]
              simp
            rcases (Submodule.mem_iSup_of_directed _ hFmono.directed_le).mp hxF with ⟨e, he⟩
            exact Submodule.mem_iSup_of_mem e he
          exact top_unique htop
        have hπStage_surj : ∀ e : ι, Function.Surjective (πStage e) := by
          intro e m
          -- The basis vector at `m` already lies in the stage support and maps back to `m`.
          refine ⟨⟨Finsupp.single m 1, Finsupp.single_mem_supported R (1 : R) m.2⟩, ?_⟩
          apply Subtype.ext
          simpa [πStage, π] using
            (Finsupp.linearCombination_single (R := R) (v := (id : M → M)) (c := (1 : R))
              (a := (m : M)))
        have hπBar_surj : ∀ e : ι, Function.Surjective (πBar e) := by
          intro e
          exact mapQ_surjective_of_surjective (φ := πStage e) (hπStage_surj e)
            (p := lowerF e) (q := lowerM e) (hlowerF_le e)
        have hkernel_pd :
            ∀ e : ι, HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker (πBar e))) n := by
          intro e
          let S : ShortComplex (ModuleCat.{max u v} R) := LinearMap.shortComplexKer (πBar e)
          have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer (hπBar_surj e)
          have hmid : HasProjectiveDimensionLE (ModuleCat.of R (Fstage e ⧸ lowerF e)) n := by
            let _ : Module.Projective R (Fstage e ⧸ lowerF e) := by
              simpa [Fstage, lowerF] using
                supported_free_cover_stage_quotient_projective (R := R) (M_ := M_) hmono e
            exact hasProjectiveDimensionLE_of_module_projective (R := R) n
          have hright :
              HasProjectiveDimensionLE (ModuleCat.of R (M_ e ⧸ lowerM e)) (n + 1) := by
            simpa [lowerM] using hquot e
          simpa [S] using
            CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₁ hS n hmid hright
        let KtoStage : ∀ e : ι, Kstage e →ₗ[R] Fstage e :=
          fun e ↦
            LinearMap.codRestrict (Fstage e) (K.subtype.comp (Kstage e).subtype) fun x ↦ x.2
        let κMap : ∀ e : ι, Kstage e →ₗ[R] LinearMap.ker (πBar e) :=
          fun e ↦
            LinearMap.codRestrict (LinearMap.ker (πBar e)) ((lowerF e).mkQ.comp (KtoStage e))
              (by
                intro x
                -- Elements of the global kernel map to zero in the descended stage quotient.
                change
                  (Submodule.Quotient.mk (πStage e ((KtoStage e) x)) : M_ e ⧸ lowerM e) = 0
                rw [Submodule.Quotient.mk_eq_zero]
                have hx0 : πStage e ((KtoStage e) x) = 0 := by
                  apply Subtype.ext
                  simpa [KtoStage, πStage, π, K]
                    using (show π ((x : K) : M →₀ R) = 0 from (x : K).2)
                simpa [hx0])
        have hκ_surj : ∀ e : ι, Function.Surjective (κMap e) := by
          intro e z
          rcases z with ⟨z, hz⟩
          obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (lowerF e) z
          have hz' : (Submodule.Quotient.mk (πStage e x) : M_ e ⧸ lowerM e) = 0 := by
            simpa [πBar] using hz
          have hx_lower : (πStage e x : M) ∈ ⨆ e' : Set.Iio e, M_ e' := by
            have hx_lower' : πStage e x ∈ lowerM e :=
              (Submodule.Quotient.mk_eq_zero (p := lowerM e) (x := πStage e x)).1 hz'
            simpa [lowerM] using hx_lower'
          rcases supported_free_cover_lower_preimage
              (R := R) (M := M) (M_ := M_) hmono (e := e) (m := (πStage e x : M)) hx_lower with
            ⟨y₀, hy₀_lower, hy₀_pi⟩
          have hy₀_stage : y₀ ∈ Fstage e := by
            exact (iSup_le fun e' ↦ hFmono e'.2.le) hy₀_lower
          let y : Fstage e := ⟨y₀, hy₀_stage⟩
          have hy_lower : y ∈ lowerF e := by
            simpa [lowerF, y] using hy₀_lower
          have hxy : π x = π y := by
            simpa [πStage, π, y] using hy₀_pi.symm
          let w : Kstage e :=
            ⟨⟨x - y, by
              -- Subtract the lifted lower-stage contribution to land in the global kernel.
              rw [LinearMap.mem_ker, LinearMap.map_sub, hxy, sub_self]⟩, by
              exact Submodule.sub_mem _ x.2 y.2⟩
          refine ⟨w, Subtype.ext ?_⟩
          -- The correction term lies in the lower stage, so the quotient class is unchanged.
          change (Submodule.Quotient.mk (x - y) : Fstage e ⧸ lowerF e) = Submodule.Quotient.mk x
          apply (Submodule.Quotient.eq (lowerF e)).2
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (lowerF e).neg_mem hy_lower
        have hκ_ker :
            ∀ e : ι,
              LinearMap.ker (κMap e) =
                (⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype := by
          intro e
          ext x
          constructor
          · intro hx
            have hx0 : κMap e x = 0 := by
              simpa [LinearMap.mem_ker] using hx
            have hx_lower : (KtoStage e x) ∈ lowerF e := by
              have hxq0 :
                  ((lowerF e).mkQ ((KtoStage e) x) : Fstage e ⧸ lowerF e) = 0 := by
                exact congrArg Subtype.val hx0
              exact (Submodule.Quotient.mk_eq_zero (p := lowerF e) (x := (KtoStage e) x)).1 hxq0
            have hx_lower' : (((x : K) : M →₀ R)) ∈ ⨆ e' : Set.Iio e, Fstage e' := by
              simpa [lowerF, KtoStage] using hx_lower
            change (x : K) ∈ ⨆ e' : Set.Iio e, Kstage e'
            by_cases hne : Nonempty (Set.Iio e)
            · letI := hne
              have hdir : Directed (· ≤ ·) (fun e' : Set.Iio e ↦ Fstage e'.1) := by
                intro a b
                rcases le_total a.1 b.1 with hab | hba
                · exact ⟨b, hFmono hab, le_rfl⟩
                · exact ⟨a, le_rfl, hFmono hba⟩
              rcases (Submodule.mem_iSup_of_directed _ hdir).mp hx_lower' with ⟨e', hx'⟩
              exact Submodule.mem_iSup_of_mem e' (by simpa [Kstage] using hx')
            · haveI : IsEmpty (Set.Iio e) := not_nonempty_iff.mp hne
              simpa [iSup_of_empty, Kstage] using hx_lower'
          · intro hx
            have hx' : (x : K) ∈ ⨆ e' : Set.Iio e, Kstage e' := by
              simpa using hx
            have hx_lower' : (((x : K) : M →₀ R)) ∈ ⨆ e' : Set.Iio e, Fstage e' := by
              by_cases hne : Nonempty (Set.Iio e)
              · letI := hne
                have hdir : Directed (· ≤ ·) (fun e' : Set.Iio e ↦ Kstage e'.1) := by
                  intro a b
                  rcases le_total a.1 b.1 with hab | hba
                  · exact ⟨b, hKmono hab, le_rfl⟩
                  · exact ⟨a, le_rfl, hKmono hba⟩
                rcases (Submodule.mem_iSup_of_directed _ hdir).mp hx' with ⟨e', hx''⟩
                exact Submodule.mem_iSup_of_mem e' (by simpa [KtoStage, Kstage] using hx'')
              · haveI : IsEmpty (Set.Iio e) := not_nonempty_iff.mp hne
                simpa [iSup_of_empty, Kstage, KtoStage] using hx'
            apply LinearMap.mem_ker.2
            apply Subtype.ext
            change (Submodule.Quotient.mk ((KtoStage e) x) : Fstage e ⧸ lowerF e) = 0
            rw [Submodule.Quotient.mk_eq_zero]
            simpa [lowerF, KtoStage] using hx_lower'
        have hKquot :
            ∀ e : ι,
              HasProjectiveDimensionLE
                (ModuleCat.of R
                  (Kstage e ⧸ (⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype)) n := by
          intro e
          let eκ :
              (Kstage e ⧸ (⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype) ≃ₗ[R]
                LinearMap.ker (πBar e) :=
            (Submodule.quotEquivOfEq
                ((⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype)
                (LinearMap.ker (κMap e)) (hκ_ker e).symm) ≪≫ₗ
              (κMap e).quotKerEquivOfSurjective (hκ_surj e)
          have hker_lt :
              HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker (πBar e))) (n + 1) := by
            simpa [HasProjectiveDimensionLE] using hkernel_pd e
          let eκIso :
              ModuleCat.of R (LinearMap.ker (πBar e)) ≅
                ModuleCat.of R
                  (Kstage e ⧸ (⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype) :=
            LinearEquiv.toModuleIso eκ.symm
          have hquot_lt :
              HasProjectiveDimensionLT
                (ModuleCat.of R
                  (Kstage e ⧸ (⨆ e' : Set.Iio e, Kstage e').comap (Kstage e).subtype))
                (n + 1) := by
            let _ : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker (πBar e))) (n + 1) :=
              hker_lt
            exact CategoryTheory.hasProjectiveDimensionLT_of_iso eκIso (n + 1)
          simpa [HasProjectiveDimensionLE] using hquot_lt
        have hKpd : HasProjectiveDimensionLE (ModuleCat.of R K) n := by
          -- The induction hypothesis now applies to the global kernel filtration.
          exact ih (M := K) Kstage hKmono hKcover hKquot
        have hπ_surj : Function.Surjective π :=
          Finsupp.linearCombination_id_surjective R M
        let S : ShortComplex (ModuleCat.{max u v} R) := LinearMap.shortComplexKer π
        have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ_surj
        have hfree_pd : HasProjectiveDimensionLE (ModuleCat.of R (M →₀ R)) (n + 1) := by
          let _ : Module.Projective R (M →₀ R) := by infer_instance
          exact hasProjectiveDimensionLE_of_module_projective (R := R) (n + 1)
        -- The global short exact sequence `0 → K → (M →₀ R) → M → 0` finishes the successor step.
        simpa [S, K, π] using
          CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₃ hS n hKpd hfree_pd
      · have hsub : Subsingleton M := by
          haveI : IsEmpty ι := not_nonempty_iff.mp hι
          -- With no stages, the cover hypothesis forces `M` itself to be trivial.
          rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top]
          simpa [iSup_of_empty] using hcover
        haveI : Subsingleton M := hsub
        have hzero : Limits.IsZero (ModuleCat.of R M) :=
          (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R M)).2 hsub
        have hpd0 : HasProjectiveDimensionLT (ModuleCat.of R M) 0 :=
          (CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero
            (X := ModuleCat.of R M)).2 hzero
        let _ : HasProjectiveDimensionLT (ModuleCat.of R M) 0 := hpd0
        simpa [HasProjectiveDimensionLE] using
          (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R M) (n + 2))

end
