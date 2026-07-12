import Mathlib
import StacksProject_2024.Chap10.Lemma_10_84_2
import StacksProject_2024.Chap10.Lemma_10_95_3
import StacksProject_2024.Chap10.Lemma_10_95_5
import StacksProject_2024.Chap10.Theorem_10_84_5

-- Declarations for this item will be appended below by the statement pipeline.

open Order
open scoped TensorProduct Ordinal DirectSum

universe u v w x

namespace Module.Projective

section

variable {R : Type u} [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Theorem 10 95 6: projective faithfully flat base change descends flatness
to `M`. -/
private theorem flat_of_projectiveTensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.Flat R M := by
  -- Projective modules are flat after base change; faithful flatness reflects this flatness.
  have hflatTensor : Module.Flat S (S ⊗[R] M) := inferInstance
  exact (Module.Flat.iff_flat_tensorProduct (R := R) (M := M) S).mp hflatTensor

/-- Helper for Chap10 Theorem 10 95 6: projective faithfully flat base change descends the
Mittag-Leffler property to `M`. -/
private theorem mittagLeffler_of_projectiveTensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.MittagLeffler R M := by
  -- The projectivity criterion upstairs supplies Mittag-Lefflerness, and Lemma 10.95.1 descends it.
  have hprojectiveDataS :=
    (Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.{v, max v w, 0}
      (R := S) (M := S ⊗[R] M)).mp inferInstance
  have hMLTensor : Module.MittagLeffler S (S ⊗[R] M) := hprojectiveDataS.2.1
  letI : Module.MittagLeffler S (S ⊗[R] M) := hMLTensor
  exact Module.mittagLeffler_of_mittagLeffler_tensorProduct_of_faithfullyFlat
    (R := R) (S := S) (M := M)

/-- Helper for Chap10 Theorem 10 95 6: base change carries arbitrary suprema of submodules
to suprema after scalar extension. -/
private lemma baseChange_iSup_eq
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Sort*} (P : ι → Submodule R M) :
    (⨆ i, P i).baseChange S = ⨆ i, (P i).baseChange S := by
  -- Rewrite the downstairs supremum as a span of the union, then move the pure-tensor image
  -- through that union before applying the span/supremum formula upstairs.
  rw [Submodule.iSup_eq_span]
  rw [Submodule.baseChange_span]
  rw [Set.image_iUnion]
  rw [Submodule.span_iUnion]
  simp [Submodule.baseChange_eq_span]

/-- Helper for Chap10 Theorem 10 95 6: base change carries a binary supremum of submodules to
the binary supremum of their base changes. -/
private lemma baseChange_sup_eq
    {S : Type v} [CommRing S] [Algebra R S]
    (P P' : Submodule R M) :
    (P ⊔ P').baseChange S = P.baseChange S ⊔ P'.baseChange S := by
  -- Specialize the arbitrary-supremum lemma to the two-element indexing type.
  simpa [iSup_bool_eq] using
    (baseChange_iSup_eq (R := R) (M := M) (S := S)
      (fun b : Bool => if b then P else P'))

/-- Helper for Chap10 Theorem 10 95 6: adjoining a countably generated submodule makes a
countably generated successor quotient. -/
private lemma countablyGenerated_quotient_sup_of_right
    (P N : Submodule R M) (hN : N.CountablyGenerated) :
    Module.CountablyGenerated R
      (((P ⊔ N : Submodule R M) ⧸ P.comap (P ⊔ N : Submodule R M).subtype)) := by
  have hNle : N ≤ (P ⊔ N : Submodule R M) := le_sup_right
  let f : N →ₗ[R]
      (((P ⊔ N : Submodule R M) ⧸ P.comap (P ⊔ N : Submodule R M).subtype)) :=
    (P.comap (P ⊔ N : Submodule R M).subtype).mkQ.comp (Submodule.inclusion hNle)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective (P.comap (P ⊔ N : Submodule R M).subtype) y
    rcases Submodule.mem_sup.mp x.2 with ⟨p, hp, n, hn, hpn⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    -- In the quotient by `P`, the representative `p + n` has the same class as `n`.
    change Submodule.Quotient.mk (Submodule.inclusion hNle ⟨n, hn⟩) =
      Submodule.Quotient.mk x
    rw [Submodule.inclusion_apply]
    symm
    apply (Submodule.Quotient.eq _).2
    change x - (⟨n, hNle hn⟩ : (P ⊔ N : Submodule R M)) ∈
      P.comap (P ⊔ N : Submodule R M).subtype
    change x.1 - n ∈ P
    have hx : x.1 - n = p := by
      rw [← hpn, add_sub_cancel_right]
    simpa [hx] using hp
  have hNmod : Module.CountablyGenerated R N :=
    (Submodule.countablyGenerated_iff_moduleCountablyGenerated
      (R := R) (M := M) (Q := N)).mp hN
  -- The quotient is a surjective image of the right-hand countably generated summand.
  exact Module.countablyGenerated_of_surjective (f := f) hf hNmod

/-- Helper for Chap10 Theorem 10 95 6: extension of scalars preserves countable generation. -/
private lemma countablyGenerated_tensorProduct_of_countablyGenerated
    {S : Type v} [CommRing S] [Algebra R S]
    {N : Type x} [AddCommGroup N] [Module R N]
    (hN : Module.CountablyGenerated R N) :
    Module.CountablyGenerated S (S ⊗[R] N) := by
  rw [Module.countablyGenerated_iff] at hN ⊢
  rcases hN with ⟨t, ht, hspan⟩
  -- Pure tensors with first factor `1` over a countable spanning set span the scalar extension.
  refine ⟨(TensorProduct.mk R S N 1) '' t, ht.image _, ?_⟩
  calc
    Submodule.span S ((TensorProduct.mk R S N 1) '' t) =
        (Submodule.span R t).baseChange S := by
      rw [Submodule.baseChange_span]
    _ = (⊤ : Submodule R N).baseChange S := by
      rw [hspan]
    _ = ⊤ := by
      rw [Submodule.baseChange_top]

/-- Helper for Chap10 Theorem 10 95 6: a projective successor quotient supplies a complement
to the predecessor stage. -/
private lemma exists_isCompl_of_projective_quotient
    {P P' : Submodule R M}
    [Module.Projective R (P' ⧸ P.comap P'.subtype)] :
    ∃ q : Submodule R P', IsCompl (P.comap P'.subtype) q := by
  let K : Submodule R P' := P.comap P'.subtype
  have hsec : ∃ s : (P' ⧸ K) →ₗ[R] P', K.mkQ.comp s = LinearMap.id := by
    exact Module.projective_lifting_property K.mkQ LinearMap.id (Submodule.mkQ_surjective K)
  rcases hsec with ⟨s, hs⟩
  refine ⟨LinearMap.range s, ?_⟩
  -- A section of the quotient map splits the kernel from the range of the section.
  have hcompl : IsCompl (LinearMap.range s) (LinearMap.ker K.mkQ) := by
    exact Module.range_isCompl_ker_of_split s K.mkQ hs
  simpa [K, Submodule.ker_mkQ] using hcompl.symm

/-- Helper for Chap10 Theorem 10 95 6: reindexing a submodule family along a well-order
enumeration preserves its supremum. -/
private lemma wellOrdered_iSup_enum_submodule
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (A : ι → Submodule R M) :
    (⨆ z : (Ordinal.type (α := ι) (· < ·)).ToType,
        A (Ordinal.enum (α := ι) (· < ·) z)) = iSup A := by
  let o : Ordinal := Ordinal.type (α := ι) (· < ·)
  refine le_antisymm ?_ ?_
  · -- Every enumerated stage is one of the original stages.
    refine iSup_le fun z ↦ le_iSup_of_le (Ordinal.enum (α := ι) (· < ·) z) le_rfl
  · -- Conversely, every original index is recovered by enumerating its ordinal rank.
    refine iSup_le fun i ↦ ?_
    let z : o.ToType :=
      Ordinal.ToType.mk ⟨Ordinal.typein (α := ι) (· < ·) i,
        Ordinal.typein_lt_type (r := (· < ·)) i⟩
    have hz : Ordinal.enum (α := ι) (· < ·) z = i := by
      simpa [z, o] using (Ordinal.enum_typein (α := ι) (r := (· < ·)) i)
    exact hz ▸
      (le_iSup (fun z : o.ToType ↦ A (Ordinal.enum (α := ι) (· < ·) z)) z)

/-- Helper for Chap10 Theorem 10 95 6: the full typein prefix of a well-ordered family is its
whole supremum. -/
private lemma wellOrdered_typein_prefix_orderType_eq_iSup
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (B : (Ordinal.type (α := ι) (· < ·)).ToType → Submodule R M) :
    (⨆ z : {z : (Ordinal.type (α := ι) (· < ·)).ToType //
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) z <
          Ordinal.type (α := ι) (· < ·)}, B z.1) = iSup B := by
  refine le_antisymm ?_ ?_
  · -- Forgetting the bound embeds the prefix family into the full family.
    refine iSup_le fun z ↦ le_iSup B z.1
  · -- Every element of the order-type carrier has typein below the order type.
    refine iSup_le fun z ↦ le_iSup_of_le ⟨z, Ordinal.typein_lt_self z⟩ le_rfl

/-- Helper for Chap10 Theorem 10 95 6: the ordinal enumeration of a well-ordered filtration. -/
private noncomputable abbrev wellOrderedStageFamily
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (M_ : ι → Submodule R M) :
    (Ordinal.type (α := ι) (· < ·)).ToType → Submodule R M :=
  fun z ↦ M_ (Ordinal.enum (α := ι) (· < ·) z)

/-- Helper for Chap10 Theorem 10 95 6: prefix stages for the ordinal enumeration of a
well-ordered filtration. -/
private noncomputable abbrev wellOrderedPrefixStage
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (M_ : ι → Submodule R M) (β : Ordinal) :
    Submodule R M :=
  ⨆ z :
      {z : (Ordinal.type (α := ι) (· < ·)).ToType //
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) z < β},
      wellOrderedStageFamily (R := R) (M := M) M_ z.1

/-- Helper for Chap10 Theorem 10 95 6: an ordinal below the order type has that same typein
after coercion to the order-type carrier. -/
private lemma typein_wellOrderedPrefixIndex
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·)
        (Ordinal.ToType.mk b) = b.1 := by
  -- The order-type carrier is decoded exactly by the ordinal representative `b`.
  simpa [Ordinal.ToType.mk, Ordinal.type_toType] using
    (Ordinal.typein_enum
      (α := (Ordinal.type (α := ι) (· < ·)).ToType) (r := (· < ·)) (h := b.2))

/-- Helper for Chap10 Theorem 10 95 6: a predecessor prefix is the supremum of the original
filtration stages strictly below the corresponding well-ordered index. -/
private lemma wellOrdered_prefixStage_eq_iSup_lt
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (M_ : ι → Submodule R M)
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    wellOrderedPrefixStage (R := R) (M := M) M_ b.1 = ⨆ e' : Set.Iio e, M_ e' := by
  classical
  let o : Ordinal := Ordinal.type (α := ι) (· < ·)
  let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
  refine le_antisymm ?_ ?_
  · -- Prefix elements decode to original indices strictly below `e`.
    refine iSup_le fun z ↦ ?_
    have hzb : z.1.toOrd < b := by
      simpa using z.2
    have hzlt : Ordinal.enum (α := ι) (· < ·) z.1 < e := by
      simpa [e] using
        (Ordinal.enum_lt_enum (r := (· < ·)) (o₁ := z.1.toOrd) (o₂ := b)).2 hzb
    exact le_iSup_of_le ⟨Ordinal.enum (α := ι) (· < ·) z.1, hzlt⟩ le_rfl
  · -- Every original lower stage appears at its own typein rank in the prefix.
    refine iSup_le fun e' ↦ ?_
    let zOrd : Set.Iio o :=
      ⟨Ordinal.typein (α := ι) (· < ·) e'.1,
        Ordinal.typein_lt_type (r := (· < ·)) e'.1⟩
    let z : o.ToType := Ordinal.ToType.mk zOrd
    have hz_typein :
        Ordinal.typein (α := o.ToType) (· < ·) z =
          Ordinal.typein (α := ι) (· < ·) e'.1 := by
      simpa [z, zOrd, o, Ordinal.ToType.mk, Ordinal.type_toType] using
        (Ordinal.typein_enum (α := o.ToType) (r := (· < ·)) (h := zOrd.2))
    have he_typein : Ordinal.typein (α := ι) (· < ·) e = b.1 := by
      simpa [e] using (Ordinal.typein_enum (α := ι) (r := (· < ·)) (h := b.2))
    have hzlt : Ordinal.typein (α := o.ToType) (· < ·) z < b.1 := by
      have he' :
          Ordinal.typein (α := ι) (· < ·) e'.1 <
            Ordinal.typein (α := ι) (· < ·) e := by
        exact (Ordinal.typein_lt_typein (r := (· < ·))).2 e'.2
      simpa [hz_typein, he_typein] using he'
    have henum : Ordinal.enum (α := ι) (· < ·) z = e'.1 := by
      simpa [z, zOrd, o] using (Ordinal.enum_typein (α := ι) (r := (· < ·)) e'.1)
    exact le_iSup_of_le ⟨z, hzlt⟩ (by simpa [wellOrderedStageFamily, henum])

/-- Helper for Chap10 Theorem 10 95 6: the successor prefix of a monotone well-ordered
filtration is the fresh stage. -/
private lemma wellOrdered_prefixStage_succ_eq_stage
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (M_ : ι → Submodule R M) (hmono : Monotone M_)
    (b : Set.Iio (Ordinal.type (α := ι) (· < ·))) :
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) = M_ e := by
  classical
  let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
  have hprefix_succ :
      wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) =
        wellOrderedPrefixStage (R := R) (M := M) M_ b.1 ⊔ M_ e := by
    -- Split the successor prefix into the old prefix and the unique new rank.
    refine le_antisymm ?_ ?_
    · refine iSup_le fun z ↦ ?_
      have hzle :
          Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·) z.1 ≤
            b.1 := by
        simpa using (lt_succ_iff.mp z.2)
      rcases le_iff_eq_or_lt.mp hzle with hzb | hzb
      · have hzeq : z.1 = Ordinal.ToType.mk b := by
          apply (Ordinal.typein_injective (r := (· < ·)))
          rw [typein_wellOrderedPrefixIndex b]
          exact hzb
        simpa [wellOrderedStageFamily, e, hzeq] using
          (le_sup_right : M_ e ≤
            wellOrderedPrefixStage (R := R) (M := M) M_ b.1 ⊔ M_ e)
      · exact le_sup_of_le_left <| le_iSup_of_le ⟨z.1, hzb⟩ le_rfl
    · refine sup_le ?_ ?_
      · refine iSup_le fun z ↦ ?_
        exact le_iSup_of_le ⟨z.1, lt_of_lt_of_le z.2 (le_succ b.1)⟩ le_rfl
      · have hnew_lt :
            Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·)
                (Ordinal.ToType.mk b) < b.1 + 1 := by
          rw [typein_wellOrderedPrefixIndex b]
          simpa using (lt_succ b.1)
        exact le_iSup_of_le ⟨Ordinal.ToType.mk b, hnew_lt⟩
          (by simp [wellOrderedStageFamily, e])
  refine le_antisymm ?_ ?_
  · -- The old prefix is already contained in the fresh monotone stage.
    rw [hprefix_succ]
    refine sup_le ?_ le_rfl
    rw [wellOrdered_prefixStage_eq_iSup_lt (R := R) (M := M) (M_ := M_) (b := b)]
    refine iSup_le fun e' ↦ hmono e'.2.le
  · -- The fresh stage is explicitly present in the successor prefix.
    have hnew_lt :
        Ordinal.typein (α := (Ordinal.type (α := ι) (· < ·)).ToType) (· < ·)
            (Ordinal.ToType.mk b) < b.1 + 1 := by
      rw [typein_wellOrderedPrefixIndex b]
      simpa using (lt_succ b.1)
    exact le_iSup_of_le ⟨Ordinal.ToType.mk b, hnew_lt⟩
      (by simp [wellOrderedStageFamily])

/-- Helper for Chap10 Theorem 10 95 6: a well-ordered filtration with projective successive
quotients has projective union. -/
private lemma projective_of_wellOrdered_submodule_union_of_projective_successive_quotients
    {ι : Type x} [LinearOrder ι] [IsWellOrder ι (· < ·)]
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
    -- The zero prefix has no indices.
    refine le_antisymm ?_ bot_le
    refine iSup_le fun z ↦ False.elim (by simpa using z.2)
  have hprefix_top : prefixStage o = ⊤ := by
    -- The prefix at the order type recovers all original stages.
    calc
      prefixStage o = iSup (wellOrderedStageFamily (R := R) (M := M) M_) := by
        simpa [prefixStage, o, wellOrderedPrefixStage] using
          wellOrdered_typein_prefix_orderType_eq_iSup
            (R := R) (M := M) (ι := ι)
            (wellOrderedStageFamily (R := R) (M := M) M_)
      _ = iSup M_ := by
        simpa [wellOrderedStageFamily, o] using
          wellOrdered_iSup_enum_submodule (R := R) (M := M) (ι := ι) M_
      _ = ⊤ := hcover
  have hprefix_mono : Monotone prefixStage := by
    -- Enlarging the ordinal bound only adds more enumerated stages.
    intro β γ hβγ
    refine iSup_le fun z ↦ le_iSup_of_le ⟨z.1, lt_of_lt_of_le z.2 hβγ⟩ le_rfl
  have hprefix_limit :
      ∀ {α : Ordinal}, α < o + 1 → IsSuccLimit α →
        prefixStage α = ⨆ β : Set.Iio α, prefixStage β.1 := by
    intro α _hα hlimit
    refine le_antisymm ?_ ?_
    · -- Every generator of a limit prefix appears already in an earlier successor prefix.
      refine iSup_le fun z ↦ ?_
      have hz_lt :
          Ordinal.typein (α := o.ToType) (· < ·) z.1 + 1 < α := by
        simpa using hlimit.succ_lt z.2
      refine le_iSup_of_le ⟨Ordinal.typein (α := o.ToType) (· < ·) z.1 + 1, hz_lt⟩ ?_
      have hz_mem :
          Ordinal.typein (α := o.ToType) (· < ·) z.1 <
            Ordinal.typein (α := o.ToType) (· < ·) z.1 + 1 := by
        simpa using (lt_succ (Ordinal.typein (α := o.ToType) (· < ·) z.1))
      exact le_iSup_of_le ⟨z.1, hz_mem⟩ le_rfl
    · -- Conversely, every earlier prefix is contained by monotonicity.
      refine iSup_le fun β ↦ hprefix_mono (le_of_lt β.2)
  have hprefix_successive_projective :
      ∀ b : Set.Iio o,
        Module.Projective R
          (prefixStage (b.1 + 1) ⧸ (prefixStage b.1).comap
            (prefixStage (b.1 + 1)).subtype) := by
    intro b
    let e : ι := Ordinal.enum (α := ι) (· < ·) (Ordinal.ToType.mk b)
    -- Successor prefixes identify the dévissage quotient with the original quotient at `e`.
    change Module.Projective R
      (wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1) ⧸
        (wellOrderedPrefixStage (R := R) (M := M) M_ b.1).comap
          (wellOrderedPrefixStage (R := R) (M := M) M_ (b.1 + 1)).subtype)
    rw [wellOrdered_prefixStage_succ_eq_stage (R := R) (M := M) (M_ := M_) hmono b,
      wellOrdered_prefixStage_eq_iSup_lt (R := R) (M := M) (M_ := M_) (b := b)]
    simpa [e] using hquot e
  have hlength_pos : 0 < o + 1 := by
    simpa using (Ordinal.zero_lt_succ o)
  have hiSup_stages : (⨆ α : Set.Iio (o + 1), prefixStage α.1) = ⊤ := by
    -- The top prefix occurs at index `o`, which lies below `o + 1`.
    refine le_antisymm le_top ?_
    rw [← hprefix_top]
    exact le_iSup_of_le ⟨o, by simpa using (lt_succ o)⟩ le_rfl
  let D : DirectSumDevissage.{u, w, x} R M :=
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
        -- Projectivity of the successor quotient supplies the split complement for the stage.
        have hproj :
            Module.Projective R
              (prefixStage (α + 1) ⧸
                (prefixStage α).comap (prefixStage (α + 1)).subtype) := by
          simpa [b] using hprefix_successive_projective b
        let _ : Module.Projective R
            (prefixStage (α + 1) ⧸
              (prefixStage α).comap (prefixStage (α + 1)).subtype) := hproj
        exact exists_isCompl_of_projective_quotient
          (R := R) (M := M)
          (P := prefixStage α) (P' := prefixStage (α + 1)) }
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
      -- Each dévissage quotient is one of the verified prefix quotients.
      simpa [D, prefixStage, DirectSumDevissage.successiveQuotient,
        DirectSumDevissage.predecessorStage] using hprefix_successive_projective b
    infer_instance
  have hsum_projective' :
      Module.Projective R (⨁ α : D.successorIndex, D.successiveQuotient α) := by
    simpa using hsum_projective
  let _ : Module.Projective R (⨁ α : D.successorIndex, D.successiveQuotient α) :=
    hsum_projective'
  -- Transport projectivity back across the dévissage linear equivalence.
  exact Module.Projective.of_equiv' eD.symm

/-- Helper for Chap10 Theorem 10 95 6: a packaged well-ordered filtration with projective
successive quotients gives projectivity of the ambient module. -/
private theorem projective_of_exists_wellOrdered_projective_successor_filtration
    (hfiltration :
      ∃ (ι : Type x), ∃ (_ : LinearOrder ι), ∃ (_ : IsWellOrder ι (· < ·)),
        ∃ (P : ι → Submodule R M),
          Monotone P ∧ iSup P = ⊤ ∧
            ∀ e : ι,
              Module.Projective R
                (P e ⧸ (⨆ e' : Set.Iio e, P e').comap (P e).subtype)) :
    Module.Projective R M := by
  -- Unpack the filtration data and hand it to the already-proved ordinal assembly theorem.
  rcases hfiltration with ⟨ι, hlinear, hwell, P, hmono, hcover, hquot⟩
  letI : LinearOrder ι := hlinear
  letI : IsWellOrder ι (· < ·) := hwell
  exact projective_of_wellOrdered_submodule_union_of_projective_successive_quotients
    (R := R) (M := M) P hmono hcover hquot

/-- Helper for Chap10 Theorem 10 95 6: a cyclic submodule generated by one element is countably
generated. -/
private lemma span_singleton_countablyGenerated (x : M) :
    (Submodule.span R ({x} : Set M)).CountablyGenerated := by
  -- The singleton itself is the required countable spanning set.
  exact (Submodule.countablyGenerated_iff (P := Submodule.span R ({x} : Set M))).2
    ⟨{x}, Set.countable_singleton x, rfl⟩

/-- Helper for Chap10 Theorem 10 95 6: Lemma 10.95.5 supplies the concrete one-step
downstairs closure data, including countable generation of the successor quotient. -/
private lemma exists_kaplanskySuccessorClosure_data
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    (P : Submodule R M) (J : Set ι) (hPJ : P.baseChange S = Module.block Q J)
    (x : M) :
    ∃ (P' : Submodule R M) (J' : Set ι),
      P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
        P'.baseChange S = Module.block Q J' ∧
          Module.CountablyGenerated R (P' ⧸ P.comap P'.subtype) := by
  -- Apply Lemma 10.95.5 to the cyclic submodule generated by the new element.
  let N : Submodule R M := Submodule.span R ({x} : Set M)
  have hNcg : N.CountablyGenerated := span_singleton_countablyGenerated (R := R) (M := M) x
  rcases exists_countablyGenerated_supermodule_with_baseChange_eq_iSup_subfamily
      (R := R) (S := S) (M := M) (I := ι) Q hQindep hQtop hQcg hNcg with
    ⟨N', hNN', hN'cg, I', hN'base⟩
  refine ⟨P ⊔ N', J ∪ I', le_sup_left, ?_, fun i hi ↦ Or.inl hi, ?_, ?_⟩
  · -- The chosen cyclic generator lies in the newly adjoined submodule, hence in the sum.
    exact (le_sup_right : N' ≤ P ⊔ N') (hNN' (Submodule.subset_span (by simp)))
  · -- Base change commutes with this binary supremum, and the upstairs blocks commute with union.
    calc
      ((P ⊔ N' : Submodule R M).baseChange S) =
          P.baseChange S ⊔ N'.baseChange S := by
            exact baseChange_sup_eq (R := R) (M := M) (S := S) P N'
      _ = Module.block Q J ⊔ Module.block Q I' := by
            rw [hPJ, hN'base]
            rfl
      _ = Module.block Q (J ∪ I') := by
            rw [Module.block_union_eq_sup]
  · -- The successor quotient is generated by the countably generated right summand.
    exact countablyGenerated_quotient_sup_of_right (R := R) (M := M) P N' hN'cg

/-- Helper for Chap10 Theorem 10 95 6: a block and its complementary block form a complement
pair when the independent family has total supremum. -/
private lemma block_isCompl_compl_of_iSup_eq_top
    {S : Type v} [CommRing S]
    {N : Type w} [AddCommGroup N] [Module S N]
    {ι : Type x} (Q : ι → Submodule S N)
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤) (J : Set ι) :
    IsCompl (Module.block Q J) (Module.block Q (Set.univ \ J)) := by
  -- The two blocks are disjoint because the indexing subsets are disjoint.
  have hdisjoint_sets : Disjoint J (Set.univ \ J) := by
    refine Set.disjoint_left.2 ?_
    intro i hiJ hiDiff
    exact hiDiff.2 hiJ
  have hdisjoint_blocks :
      Disjoint (Module.block Q J) (Module.block Q (Set.univ \ J)) := by
    simpa [Module.block, iSup_subtype] using
      hQindep.disjoint_biSup_biSup (s := J) (t := Set.univ \ J) hdisjoint_sets
  -- Their union is the full block, which is the whole module by the totality hypothesis.
  have hunion : J ∪ (Set.univ \ J) = Set.univ := by
    ext i
    constructor
    · intro _hi
      exact Set.mem_univ i
    · intro _hi
      by_cases hiJ : i ∈ J
      · exact Or.inl hiJ
      · exact Or.inr ⟨Set.mem_univ i, hiJ⟩
  have hsup :
      Module.block Q J ⊔ Module.block Q (Set.univ \ J) = ⊤ := by
    have hblock_univ : Module.block Q Set.univ = iSup Q := by
      -- Reindexing over the subtype `Set.univ` does not change the supremum.
      refine le_antisymm ?_ ?_
      · refine iSup_le fun i ↦ le_iSup Q i.1
      · refine iSup_le fun i ↦ le_iSup_of_le ⟨i, Set.mem_univ i⟩ le_rfl
    calc
      Module.block Q J ⊔ Module.block Q (Set.univ \ J) =
          Module.block Q (J ∪ (Set.univ \ J)) := by
            symm
            exact Module.block_union_eq_sup (summand := Q) J (Set.univ \ J)
      _ = Module.block Q Set.univ := by rw [hunion]
      _ = ⊤ := by rw [hblock_univ, hQtop]
  exact ⟨hdisjoint_blocks, codisjoint_iff.mpr hsup⟩

/-- Helper for Chap10 Theorem 10 95 6: every block in a total independent decomposition of a
projective module is projective. -/
private lemma projective_block_of_iSup_eq_top
    {S : Type v} [CommRing S]
    {N : Type w} [AddCommGroup N] [Module S N] [Module.Projective S N]
    {ι : Type x} (Q : ι → Submodule S N)
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤) (J : Set ι) :
    Module.Projective S (Module.block Q J) := by
  -- The complement from the previous helper splits the inclusion of the block into the ambient
  -- projective module.
  let C : Submodule S N := Module.block Q (Set.univ \ J)
  have hcompl : IsCompl (Module.block Q J) C :=
    block_isCompl_compl_of_iSup_eq_top (Q := Q) hQindep hQtop J
  exact Module.Projective.of_split (Module.block Q J).subtype
    ((Module.block Q J).linearProjOfIsCompl C hcompl)
    (Submodule.linearProjOfIsCompl_comp_subtype hcompl)

/-- Helper for Chap10 Theorem 10 95 6: the quotient of a larger block by a smaller block is
projective when the ambient independent decomposition is total. -/
private lemma projective_blockQuotient_of_subset
    {S : Type v} [CommRing S]
    {N : Type w} [AddCommGroup N] [Module S N] [Module.Projective S N]
    {ι : Type x} (Q : ι → Submodule S N)
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤)
    {J J' : Set ι} (hJJ' : J ⊆ J') :
    Module.Projective S
      (Module.block Q J' ⧸ (Module.block Q J).comap (Module.block Q J').subtype) := by
  -- First split the old block inside the new block.
  rcases Module.block_succ_isCompl_of_subset (summand := Q) hQindep hJJ' with ⟨C, hcompl⟩
  have hnewProjective : Module.Projective S (Module.block Q J') :=
    projective_block_of_iSup_eq_top (Q := Q) hQindep hQtop J'
  let _ : Module.Projective S (Module.block Q J') := hnewProjective
  have hCProjective : Module.Projective S C := by
    exact Module.Projective.of_split C.subtype
      (C.linearProjOfIsCompl ((Module.block Q J).comap (Module.block Q J').subtype)
        hcompl.symm)
      (Submodule.linearProjOfIsCompl_comp_subtype hcompl.symm)
  let _ : Module.Projective S C := hCProjective
  -- The complement is linearly equivalent to the quotient by the predecessor block.
  exact Module.Projective.of_equiv'
    (Submodule.quotientEquivOfIsCompl
      ((Module.block Q J).comap (Module.block Q J').subtype) C hcompl).symm

/-- Helper for Chap10 Theorem 10 95 6: the denominator of the tensor-quotient presentation maps
to the base change of the predecessor submodule inside the base-changed successor. -/
private lemma baseChange_quotient_denominator_eq
    (S : Type v) [CommRing S] [Algebra R S] [Module.Flat R S]
    {P P' : Submodule R M} (hPP' : P ≤ P') :
    let K : Submodule R P' := P.comap P'.subtype
    (LinearMap.range
      ((TensorProduct.AlgebraTensorModule.lTensor S S) (K.subtype.restrictScalars R))).map
        (Submodule.toBaseChange.toLinearEquiv S P' : S ⊗[R] P' →ₗ[S] P'.baseChange S) =
      (P.baseChange S).comap (P'.baseChange S).subtype := by
  intro K
  have hbase_mono : P.baseChange S ≤ P'.baseChange S := by
    rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hPP' hp, rfl⟩
  let yOf : S ⊗[R] P → P'.baseChange S :=
    fun t ↦ ⟨(Submodule.toBaseChange S P t : S ⊗[R] M),
      hbase_mono (Submodule.toBaseChange S P t).2⟩
  have hmem_yOf : ∀ t : S ⊗[R] P,
      yOf t ∈
        (LinearMap.range
          ((TensorProduct.AlgebraTensorModule.lTensor S S) (K.subtype.restrictScalars R))).map
            (Submodule.toBaseChange.toLinearEquiv S P' : S ⊗[R] P' →ₗ[S] P'.baseChange S) := by
    intro t
    induction t with
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · simp
        · ext
          rfl
    | add a b ha hb =>
        -- The denominator image is a submodule, so the pure-tensor verification is additive.
        have hab := (Submodule.add_mem _ ha hb)
        simpa [yOf, map_add] using hab
    | tmul s p =>
        let k : K := ⟨⟨p.1, hPP' p.2⟩, p.2⟩
        refine ⟨s ⊗ₜ[R] k, ?_, ?_⟩
        · exact ⟨s ⊗ₜ[R] k, rfl⟩
        · ext
          simp [yOf, k]
  ext y
  constructor
  · -- Elements in the tensor denominator are finite sums of pure tensors from `P`.
    rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨t, rfl⟩
    induction t with
    | zero => simp
    | add a b ha hb =>
        simp only [map_add]
        exact (P.baseChange S).add_mem ha hb
    | tmul s k =>
        simp only [LinearMap.restrictScalars_self, TensorProduct.AlgebraTensorModule.lTensor_tmul,
          Submodule.subtype_apply, LinearEquiv.coe_coe, Submodule.toBaseChange.toLinearEquiv_apply,
          Submodule.mem_comap, Submodule.coe_toBaseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem s k.2
  · -- Conversely, write a vector in the base-changed predecessor as a tensor over `P`, then view
    -- each pure tensor in the predecessor of `P'`.
    intro hy
    rcases Submodule.toBaseChange_surjective S P ⟨y.1, hy⟩ with ⟨t, ht⟩
    have hyt : yOf t = y := by
      ext
      simpa [yOf] using congrArg Subtype.val ht
    simpa [hyt] using hmem_yOf t

/-- Helper for Chap10 Theorem 10 95 6: a block-normalized base-changed successor quotient
descends projectivity to the downstairs quotient. -/
private theorem projective_successorQuotient_of_baseChange_blocks
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤)
    {P P' : Submodule R M} {J J' : Set ι}
    (hPP' : P ≤ P') (hPJ : P.baseChange S = Module.block Q J)
    (hP'J' : P'.baseChange S = Module.block Q J') (hJJ' : J ⊆ J')
    (hcg : Module.CountablyGenerated R (P' ⧸ P.comap P'.subtype)) :
    Module.Projective R (P' ⧸ P.comap P'.subtype) := by
  -- The upstairs block quotient is now projective using the repaired totality side condition.
  -- TODO: Transport the base change of `P' / P` to this quotient of normalized blocks, then
  -- descend countably generated projectivity by Lemma 10.95.3.
  have hblockProjective :
      Module.Projective S
        (Module.block Q J' ⧸ (Module.block Q J).comap (Module.block Q J').subtype) :=
    projective_blockQuotient_of_subset (Q := Q) hQindep hQtop hJJ'
  let K : Submodule R P' := P.comap P'.subtype
  have hbaseQuotProjective :
      Module.Projective S
        (P'.baseChange S ⧸ (P.baseChange S).comap (P'.baseChange S).subtype) := by
    -- The normalized block quotient is the same quotient after rewriting the two base changes.
    rw [hPJ, hP'J']
    exact hblockProjective
  let eBase : S ⊗[R] P' ≃ₗ[S] P'.baseChange S :=
    Submodule.toBaseChange.toLinearEquiv S P'
  let eTensor : S ⊗[R] (P' ⧸ K) ≃ₗ[S]
      (S ⊗[R] P') ⧸
        LinearMap.range
          ((TensorProduct.AlgebraTensorModule.lTensor S S) (K.subtype.restrictScalars R)) :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S K
  let eQuot : ((S ⊗[R] P') ⧸
        LinearMap.range
          ((TensorProduct.AlgebraTensorModule.lTensor S S) (K.subtype.restrictScalars R))) ≃ₗ[S]
      (P'.baseChange S ⧸ (P.baseChange S).comap (P'.baseChange S).subtype) :=
    Submodule.Quotient.equiv _ _ eBase
      (baseChange_quotient_denominator_eq (R := R) (M := M) S hPP')
  let e : S ⊗[R] (P' ⧸ K) ≃ₗ[S]
      (P'.baseChange S ⧸ (P.baseChange S).comap (P'.baseChange S).subtype) :=
    eTensor.trans eQuot
  have hTensorProjective : Module.Projective S (S ⊗[R] (P' ⧸ K)) := by
    -- Transport projectivity across the tensor-quotient and base-change quotient equivalences.
    let _ : Module.Projective S
        (P'.baseChange S ⧸ (P.baseChange S).comap (P'.baseChange S).subtype) :=
      hbaseQuotProjective
    exact Module.Projective.of_equiv' e.symm
  let _ : Module.Projective S (S ⊗[R] (P' ⧸ K)) := hTensorProjective
  have hcgTensor : Module.CountablyGenerated S (S ⊗[R] (P' ⧸ K)) := by
    -- Countable generation survives extension of scalars.
    exact countablyGenerated_tensorProduct_of_countablyGenerated (R := R) (S := S) hcg
  -- Lemma 10.95.3 descends countably generated projectivity along the faithfully flat algebra.
  exact (Module.countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat
    (R := R) (S := S) (M := P' ⧸ K) hcgTensor).2

/-- Helper for Chap10 Theorem 10 95 6: one Kaplansky successor step with projective quotient,
assuming the block-quotient projectivity bridge. -/
private theorem exists_kaplanskySuccessorClosure
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q) (hQtop : iSup Q = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    (P : Submodule R M) (J : Set ι) (hPJ : P.baseChange S = Module.block Q J)
    (x : M) :
    ∃ (P' : Submodule R M) (J' : Set ι),
      P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
        P'.baseChange S = Module.block Q J' ∧
          Module.Projective R (P' ⧸ P.comap P'.subtype) := by
  -- First get the actual closure data; then feed its countably generated quotient to the
  -- isolated projectivity bridge.
  rcases exists_kaplanskySuccessorClosure_data
      (R := R) (M := M) (S := S) Q hQindep hQtop hQcg P J hPJ x with
    ⟨P', J', hPP', hxP', hJJ', hP'J', hquotCG⟩
  exact ⟨P', J', hPP', hxP', hJJ', hP'J',
    projective_successorQuotient_of_baseChange_blocks
      (R := R) (M := M) S Q hQindep hQtop hPP' hPJ hP'J' hJJ' hquotCG⟩

/-- Helper for Chap10 Theorem 10 95 6: a Kaplansky stage consists of a downstairs
submodule, an upstairs block-index set, and the equality identifying its base change with that
block. -/
private structure KaplanskyStage
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M)) where
  P : Submodule R M
  J : Set ι
  baseChange_eq : P.baseChange S = Module.block Q J

/-- Helper for Chap10 Theorem 10 95 6: one chosen Kaplansky successor stage records the
predecessor inclusion, seed containment, block-index inclusion, and projectivity of the new
successor quotient. -/
private structure KaplanskyStepData
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) where
  stage : KaplanskyStage (R := R) (M := M) Q
  pred_le : pred.P ≤ stage.P
  seed_mem : x ∈ stage.P
  indices_mono : pred.J ⊆ stage.J
  quotient_projective :
    Module.Projective R (stage.P ⧸ pred.P.comap stage.P.subtype)

/-- Helper for Chap10 Theorem 10 95 6: the union of any family of Kaplansky stages again has
base change equal to the corresponding union of upstairs blocks. -/
private lemma kaplanskyPred_baseChange_eq
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    {κ : Sort*} (A : κ → KaplanskyStage (R := R) (M := M) Q) :
    (⨆ a, (A a).P).baseChange S = Module.block Q (⋃ a, (A a).J) := by
  -- Move base change through the predecessor supremum, then replace each stage by its stored
  -- block invariant and recombine the blocks as one union.
  calc
    (⨆ a, (A a).P).baseChange S = ⨆ a, ((A a).P).baseChange S := by
      exact baseChange_iSup_eq (R := R) (M := M) (S := S) fun a ↦ (A a).P
    _ = ⨆ a, Module.block Q ((A a).J) := by
      simp [KaplanskyStage.baseChange_eq]
    _ = Module.block Q (⋃ a, (A a).J) := by
      rw [Module.block_iUnion_eq_iSup]

/-- Helper for Chap10 Theorem 10 95 6: the predecessor stage attached to a family of earlier
Kaplansky stages. -/
private noncomputable def kaplanskyStagePred
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    {κ : Sort*} (A : κ → KaplanskyStage (R := R) (M := M) Q) :
    KaplanskyStage (R := R) (M := M) Q :=
  { P := ⨆ a, (A a).P
    J := ⋃ a, (A a).J
    baseChange_eq := kaplanskyPred_baseChange_eq (R := R) (M := M) Q A }

/-- Helper for Chap10 Theorem 10 95 6: the abstract one-step closure operation provides
successor-stage data over any predecessor stage and seed element. -/
private lemma kaplanskyStepData_nonempty
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    Nonempty (KaplanskyStepData (R := R) (M := M) Q pred x) := by
  -- Apply the supplied one-step closure to the predecessor carried by the stage record.
  rcases step pred.P pred.J x pred.baseChange_eq with
    ⟨P', J', hPP', hxP', hJJ', hbase, hquot⟩
  exact ⟨
    { stage := { P := P', J := J', baseChange_eq := hbase }
      pred_le := hPP'
      seed_mem := hxP'
      indices_mono := hJJ'
      quotient_projective := hquot }⟩

/-- Helper for Chap10 Theorem 10 95 6: the chosen one-step Kaplansky successor data. -/
private noncomputable def kaplanskyStepData
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    KaplanskyStepData (R := R) (M := M) Q pred x :=
  Classical.choice (kaplanskyStepData_nonempty (R := R) (M := M) Q step pred x)

/-- Helper for Chap10 Theorem 10 95 6: the successor stage underlying the chosen one-step
Kaplansky data. -/
private noncomputable def kaplanskyStageSucc
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    KaplanskyStage (R := R) (M := M) Q :=
  (kaplanskyStepData (R := R) (M := M) Q step pred x).stage

/-- Helper for Chap10 Theorem 10 95 6: a chosen successor contains its predecessor stage. -/
private lemma kaplanskyStageSucc_pred_le
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    pred.P ≤ (kaplanskyStageSucc (R := R) (M := M) Q step pred x).P := by
  -- This is a direct projection from the chosen one-step data.
  exact (kaplanskyStepData (R := R) (M := M) Q step pred x).pred_le

/-- Helper for Chap10 Theorem 10 95 6: a chosen successor contains its seed element. -/
private lemma kaplanskyStageSucc_seed_mem
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    x ∈ (kaplanskyStageSucc (R := R) (M := M) Q step pred x).P := by
  -- This is the seed-containment field of the chosen one-step data.
  exact (kaplanskyStepData (R := R) (M := M) Q step pred x).seed_mem

/-- Helper for Chap10 Theorem 10 95 6: the quotient from a predecessor stage to its chosen
successor is projective. -/
private lemma kaplanskyStageSucc_quotient_projective
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    (pred : KaplanskyStage (R := R) (M := M) Q) (x : M) :
    Module.Projective R
      ((kaplanskyStageSucc (R := R) (M := M) Q step pred x).P ⧸
        pred.P.comap (kaplanskyStageSucc (R := R) (M := M) Q step pred x).P.subtype) := by
  -- The chosen one-step data stores exactly this successor quotient projectivity.
  exact (kaplanskyStepData (R := R) (M := M) Q step pred x).quotient_projective

/-- Helper for Chap10 Theorem 10 95 6: recursively choose a Kaplansky stage for each element of
a well-founded seed type. -/
private noncomputable def kaplanskyStage
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) :
    α → KaplanskyStage (R := R) (M := M) Q :=
  WellFoundedLT.fix
    (motive := fun _ : α ↦ KaplanskyStage (R := R) (M := M) Q)
    fun x IH ↦
      let pred :=
        kaplanskyStagePred (R := R) (M := M) Q
          (fun y : {y : α // y < x} ↦ IH y.1 y.2)
      kaplanskyStageSucc (R := R) (M := M) Q step pred (seed x)

/-- Helper for Chap10 Theorem 10 95 6: the recursive stage is the chosen successor of the
predecessor union. -/
private lemma kaplanskyStage_eq
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) (x : α) :
    kaplanskyStage (R := R) (M := M) Q step seed x =
      kaplanskyStageSucc (R := R) (M := M) Q step
        (kaplanskyStagePred (R := R) (M := M) Q
          (fun y : {y : α // y < x} ↦
            kaplanskyStage (R := R) (M := M) Q step seed y.1))
        (seed x) := by
  -- Unfold the well-founded recursion once to expose the predecessor union and successor step.
  unfold kaplanskyStage
  rw [WellFoundedLT.fix_eq]

/-- Helper for Chap10 Theorem 10 95 6: the predecessor union at a recursive stage is contained
in the current stage. -/
private lemma kaplanskyStage_pred_le
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) (x : α) :
    (⨆ y : {y : α // y < x}, (kaplanskyStage (R := R) (M := M) Q step seed y.1).P) ≤
      (kaplanskyStage (R := R) (M := M) Q step seed x).P := by
  -- Rewrite the current stage as the chosen successor of its predecessor union.
  rw [kaplanskyStage_eq (R := R) (M := M) Q step seed x]
  simpa [kaplanskyStagePred] using
    kaplanskyStageSucc_pred_le
      (R := R) (M := M) Q step
      (kaplanskyStagePred (R := R) (M := M) Q
        (fun y : {y : α // y < x} ↦
          kaplanskyStage (R := R) (M := M) Q step seed y.1))
      (seed x)

/-- Helper for Chap10 Theorem 10 95 6: the recursive Kaplansky stages are monotone. -/
private lemma kaplanskyStage_mono
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) {x y : α} (hxy : x < y) :
    (kaplanskyStage (R := R) (M := M) Q step seed x).P ≤
      (kaplanskyStage (R := R) (M := M) Q step seed y).P := by
  -- Insert the earlier stage into the predecessor union of the later stage.
  exact (le_iSup_of_le ⟨x, hxy⟩ le_rfl).trans
    (kaplanskyStage_pred_le (R := R) (M := M) Q step seed y)

/-- Helper for Chap10 Theorem 10 95 6: each recursive stage contains its seed element. -/
private lemma kaplanskyStage_seed_mem
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) (x : α) :
    seed x ∈ (kaplanskyStage (R := R) (M := M) Q step seed x).P := by
  -- Rewrite the current stage and read off seed containment from the one-step data.
  rw [kaplanskyStage_eq (R := R) (M := M) Q step seed x]
  exact kaplanskyStageSucc_seed_mem
    (R := R) (M := M) Q step
    (kaplanskyStagePred (R := R) (M := M) Q
      (fun y : {y : α // y < x} ↦
        kaplanskyStage (R := R) (M := M) Q step seed y.1))
    (seed x)

/-- Helper for Chap10 Theorem 10 95 6: if the seeds cover `M`, then the recursive stages cover
`M`. -/
private lemma kaplanskyStage_cover_of_surjective
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M)
    (hseed : Function.Surjective seed) :
    (⨆ x, (kaplanskyStage (R := R) (M := M) Q step seed x).P) = ⊤ := by
  -- Every element of `M` is a seed, and each seed lies in its own recursive stage.
  refine le_antisymm le_top ?_
  intro m _hm
  rcases hseed m with ⟨x, rfl⟩
  exact (le_iSup (fun x ↦ (kaplanskyStage (R := R) (M := M) Q step seed x).P) x)
    (kaplanskyStage_seed_mem (R := R) (M := M) Q step seed x)

/-- Helper for Chap10 Theorem 10 95 6: each recursive successor quotient is projective. -/
private lemma kaplanskyStage_quotient_projective
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype))
    {α : Type*} [LT α] [WellFoundedLT α] (seed : α → M) (x : α) :
    Module.Projective R
      ((kaplanskyStage (R := R) (M := M) Q step seed x).P ⧸
        (⨆ y : {y : α // y < x},
          (kaplanskyStage (R := R) (M := M) Q step seed y.1).P).comap
            (kaplanskyStage (R := R) (M := M) Q step seed x).P.subtype) := by
  -- Unfold the current stage as a successor; the predecessor is definitionally the `iSup`
  -- appearing in the quotient denominator.
  rw [kaplanskyStage_eq (R := R) (M := M) Q step seed x]
  simpa [kaplanskyStagePred] using
    kaplanskyStageSucc_quotient_projective
      (R := R) (M := M) Q step
      (kaplanskyStagePred (R := R) (M := M) Q
        (fun y : {y : α // y < x} ↦
          kaplanskyStage (R := R) (M := M) Q step seed y.1))
      (seed x)

/-- Helper for Chap10 Theorem 10 95 6: well-founded recursion turns the one-step Kaplansky
closure operation into a covering well-ordered filtration. -/
private theorem exists_wellOrdered_projective_successor_filtration_of_kaplanskyStep
    {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type x} (Q : ι → Submodule S (S ⊗[R] M))
    (_hbot : (⊥ : Submodule R M).baseChange S = Module.block Q ∅)
    (step :
      ∀ (P : Submodule R M) (J : Set ι) (x : M),
        P.baseChange S = Module.block Q J →
          ∃ (P' : Submodule R M) (J' : Set ι),
            P ≤ P' ∧ x ∈ P' ∧ J ⊆ J' ∧
              P'.baseChange S = Module.block Q J' ∧
                Module.Projective R (P' ⧸ P.comap P'.subtype)) :
    ∃ (o : Type (max u v w)), ∃ (_ : LinearOrder o), ∃ (_ : IsWellOrder o (· < ·)),
      ∃ (P : o → Submodule R M),
        Monotone P ∧ iSup P = ⊤ ∧
          ∀ e : o,
            Module.Projective R
              (P e ⧸ (⨆ e' : Set.Iio e, P e').comap (P e).subtype) := by
  classical
  let L : Type (max u v w) := ULift.{max u v w, w} M
  let o : Type (max u v w) := (Ordinal.type (@WellOrderingRel L)).ToType
  let seed : o → M := fun x ↦ ULift.down (Ordinal.enum WellOrderingRel x)
  let P : o → Submodule R M :=
    fun x ↦ (kaplanskyStage (R := R) (M := M) Q step seed x).P
  have hseed : Function.Surjective seed := by
    -- Enumerate `ULift M` by its well-order rank, then project the chosen seed back to `M`.
    intro m
    let lifted : L := ULift.up m
    let x : o :=
      Ordinal.ToType.mk
        ⟨Ordinal.typein (@WellOrderingRel L) lifted,
          Ordinal.typein_lt_type (@WellOrderingRel L) lifted⟩
    refine ⟨x, ?_⟩
    have hx : Ordinal.enum WellOrderingRel x = lifted := by
      simpa [x, o, L] using (Ordinal.enum_typein (r := @WellOrderingRel L) lifted)
    simpa [seed, lifted, hx]
  refine ⟨o, inferInstance, inferInstance, P, ?_, ?_, ?_⟩
  · -- Monotonicity follows because every earlier stage is part of the predecessor union used by
    -- the later recursive successor.
    intro x y hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · exact kaplanskyStage_mono (R := R) (M := M) Q step seed hlt
    · exact le_rfl
  · -- The well-order seeds cover all of `M`, so the recursive stage supremum is top.
    simpa [P] using
      kaplanskyStage_cover_of_surjective (R := R) (M := M) Q step seed hseed
  · -- Each successor quotient is one of the projective quotients stored in the chosen step data.
    intro e
    simpa [P] using kaplanskyStage_quotient_projective (R := R) (M := M) Q step seed e

/-- Helper for Chap10 Theorem 10 95 6: the remaining faithfully flat Kaplansky construction
should produce a well-ordered filtration with projective successor quotients. -/
private theorem exists_wellOrdered_projective_successor_filtration_of_projectiveTensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    ∃ (ι : Type (max u v w)), ∃ (_ : LinearOrder ι), ∃ (_ : IsWellOrder ι (· < ·)),
      ∃ (P : ι → Submodule R M),
        Monotone P ∧ iSup P = ⊤ ∧
          ∀ e : ι,
            Module.Projective R
              (P e ⧸ (⨆ e' : Set.Iio e, P e').comap (P e).subtype) := by
  classical
  -- Start from the internal decomposition of the projective base change; the missing step is to
  -- recursively close downstairs stages so their base changes are upstairs blocks.
  obtain ⟨ι, hι, Q, hQinternal, hQcountProjective⟩ :=
    projective_isDirectSumOfCountablyGeneratedProjective.{v, max v w, w}
      (R := S) (P := S ⊗[R] M)
  letI : DecidableEq ι := hι
  have hQindep : iSupIndep Q := hQinternal.submodule_iSupIndep
  have hQtop : iSup Q = ⊤ := hQinternal.submodule_iSup_eq_top
  have hQcg : ∀ i, (Q i).CountablyGenerated := by
    intro i
    exact
      (Submodule.countablyGenerated_iff_moduleCountablyGenerated
        (R := S) (M := S ⊗[R] M) (Q := Q i)).mpr
        (hQcountProjective i).countablyGenerated
  have hQprojective : ∀ i, Module.Projective S (Q i) := by
    intro i
    exact (hQcountProjective i).projective
  have hbot : (⊥ : Submodule R M).baseChange S = Module.block Q ∅ := by
    -- The empty downstairs stage base-changes to the empty upstairs block.
    rw [Submodule.baseChange_bot, Module.block]
    exact le_antisymm bot_le (iSup_le fun i ↦ False.elim i.2)
  -- Route correction: the failed route tried to count fresh upstairs indices.  The current route
  -- uses the one-step closure whose successor quotient is countably generated downstairs, and the
  -- remaining recursion theorem packages those steps into a well-ordered filtration.
  exact exists_wellOrdered_projective_successor_filtration_of_kaplanskyStep
    (R := R) (M := M) (S := S) Q hbot
    (fun P J x hPJ ↦
      exists_kaplanskySuccessorClosure
        (R := R) (M := M) S Q hQindep hQtop hQcg P J hPJ x)

/-- Helper for Chap10 Theorem 10 95 6: projectivity descends once the faithfully flat
Kaplansky filtration is built from the upstairs block decomposition. -/
private theorem projective_of_projectiveTensorProduct_of_faithfullyFlat_via_wellOrderedFiltration
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.Projective R M := by
  classical
  -- Route correction: the old route tried to finish the whole direct-sum condition directly.
  -- The stabilized route now uses the upstairs decomposition only to build projective successor
  -- quotients, then applies the proved well-ordered filtration assembly helper above.
  -- The missing construction is isolated in a single owner-style helper; once it is supplied, the
  -- generic assembly wrapper turns the filtration into projectivity of `M`.
  exact projective_of_exists_wellOrdered_projective_successor_filtration
    (R := R) (M := M)
    (exists_wellOrdered_projective_successor_filtration_of_projectiveTensorProduct_of_faithfullyFlat
      (R := R) (M := M) S)

/- Domain triage:
- primary domain: faithfully flat descent for projective modules over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat`,
  `projective_isDirectSumOfCountablyGeneratedProjective`,
  and the direct-sum owner instance `Module.Projective R (Π₀ i, A i)`;
- best owner abstraction: the owner predicate `Module.Projective R M`;
- primitive data: the faithfully flat `R`-algebra `S`, the `R`-module `M`, and the projective
  base change `S ⊗[R] M`;
- derived API: descent of the owner predicate `Module.Projective` from the base-changed module
  back to `M`.

Layering:
- this numbered item is `core/canonical` in the owner namespace `Module.Projective`: there is no
  upstream exact-interface descent theorem to recall, so the theorem below remains the chapter's
  canonical owner-level entry rather than a local wrapper.
-/
-- Proof sketch: decompose the projective `S`-module `S ⊗[R] M` as a direct sum of countably
-- generated projective summands using Theorem `10.84.5`; then descend countably generated
-- projective pieces by Lemma `10.95.3` along a transfinite Kaplansky dévissage as in the
-- textbook proof, and conclude that `M` is a direct sum of projective modules, hence projective.
/-- Chap10 Theorem 10 95 6: if `R → S` is faithfully flat and the base change `S ⊗[R] M`
is projective as an `S`-module, then `M` is projective as an `R`-module. -/
@[stacks 05A9]
theorem of_projective_tensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.Projective R M := by
  -- The dedicated helper isolates the remaining Kaplansky filtration construction and then
  -- assembles projectivity from its projective successor quotients.
  exact projective_of_projectiveTensorProduct_of_faithfullyFlat_via_wellOrderedFiltration
    (R := R) (M := M) S

end

end Module.Projective
