/-
Copyright (c) 2026 Ze Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel, Ze Yuan, Zichen Wang
-/
module

public import Mathlib.Order.WithBotTop
public import ConvexAnalysis_Rockafellar_1970.Chap01.Mathlib_Order_Interval_Set_WithBotTop
public import Mathlib.Topology.Order.WithTop

/-!
# Order topology on `WithBotTop ι`

When `ι` is a topological space with the order topology, we also endow `WithBotTop ι` with the
order topology. By definition, `WithBotTop ι` is `WithBot (WithTop ι)`, so the topology is
inferred automatically from the topologies on `WithBot` and `WithTop`.

This file provides convenience lemmas for `WithBotTop ι`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace WithBotTop

variable {ι : Type*}

namespace TopologicalSpace

instance instWithBotTopTopology [Preorder ι] : TopologicalSpace (WithBotTop ι) :=
  Preorder.topology _

instance instWithBotTopOrderTopology [LinearOrder ι] : OrderTopology (WithBotTop ι) := ⟨rfl⟩

end TopologicalSpace

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

def unbdryD (d : ι) : WithBotTop ι → ι
  | ⊥ => d
  | ⊤ => d
  | (a : ι) => a

def unbdry : ∀ x : WithBotTop ι, x ≠ ⊥ → x ≠ ⊤ → ι
  | (x : ι), _, _ => x

@[simp] lemma unbdryD_bot (d : ι) : unbdryD d (⊥ : WithBotTop ι) = d := rfl
@[simp] lemma unbdryD_top (d : ι) : unbdryD d (⊤ : WithBotTop ι) = d := rfl
@[simp] lemma unbdryD_coe (d a : ι) : unbdryD d (a : WithBotTop ι) = a := rfl

@[simp] lemma coe_unbdry (x : WithBotTop ι) (h : x ≠ ⊥) (h' : x ≠ ⊤) :
    (x.unbdry h h' : WithBotTop ι) = x :=
  match x with | (x : ι) => rfl

noncomputable abbrev unbdryA [Nonempty ι] : WithBotTop ι → ι :=
  unbdryD (Classical.arbitrary ι)

lemma unbdryA_eq_unbdry [Nonempty ι] {a : WithBotTop ι} (ha : a ≠ ⊥) (ha' : a ≠ ⊤) :
    unbdryA a = unbdry a ha ha' := by
  match a with | (a : ι) => rfl

def _root_.Equiv.withBotTopSubtypeNe :
    {y : WithBotTop ι // y ≠ (⊥ : WithBotTop ι) ∧ y ≠ (⊤ : WithBotTop ι)} ≃ ι where
  toFun := fun ⟨x, h⟩ => unbdry x h.1 h.2
  invFun x := ⟨(x : WithBotTop ι), ⟨coe_ne_bot x, coe_ne_top x⟩⟩
  left_inv x := Subtype.ext (coe_unbdry x.1 x.2.1 x.2.2)
  right_inv x := rfl

section Coe

lemma isEmbedding_coe : Topology.IsEmbedding ((↑) : ι → WithBotTop ι) :=
  let hmono : StrictMono ((↑) : ι → WithBotTop ι) :=
    fun _ _ h => WithBotTop.coe_lt_coe.2 h
  hmono.isEmbedding_of_ordConnected <| by
    rw [range_coe]
    exact ordConnected_Ioo

lemma isOpenEmbedding_coe : Topology.IsOpenEmbedding ((↑) : ι → WithBotTop ι) :=
  ⟨isEmbedding_coe, by rw [range_coe]; exact isOpen_Ioo⟩

lemma nhds_coe {r : ι} : 𝓝 (r : WithBotTop ι) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

@[fun_prop, continuity]
theorem continuous_coe : Continuous ((↑) : ι → WithBotTop ι) :=
  isEmbedding_coe.continuous

theorem tendsto_coe {α : Type*} {f : α → ι} {l : Filter α} {a : ι} :
    Tendsto f l (𝓝 a) ↔ Tendsto (fun x => (f x : WithBotTop ι)) l
      (𝓝 (a : WithBotTop ι)) :=
  isEmbedding_coe.tendsto_nhds_iff

theorem continuous_coe_iff {α : Type*} [TopologicalSpace α] {f : α → ι} :
    (Continuous fun x => (f x : WithBotTop ι)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

theorem nhds_coe_coe {r p : ι} :
    𝓝 ((r : WithBotTop ι), (p : WithBotTop ι)) =
      (𝓝 (r, p)).map fun p : ι × ι => ((p.1 : WithBotTop ι), (p.2 : WithBotTop ι)) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

end Coe

section Boundary

lemma tendsto_unbdryD (d : ι) {a : WithBotTop ι} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) :
    Tendsto (WithBotTop.unbdryD d) (𝓝 a) (𝓝 (WithBotTop.unbdryD d a)) := by
  let x := a
  lift x to ι using ⟨ha_bot, ha_top⟩
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

lemma continuousOn_unbdryD (d : ι) :
    ContinuousOn (WithBotTop.unbdryD d)
      {a : WithBotTop ι | a ≠ ⊥ ∧ a ≠ ⊤} := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_unbdryD d ha.2 ha.1)

lemma tendsto_unbdryA [Nonempty ι] {a : WithBotTop ι} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) :
    Tendsto unbdryA (𝓝 a) (𝓝 a.unbdryA) := tendsto_unbdryD _ ha_top ha_bot

lemma continuousOn_unbdryA [Nonempty ι] :
    ContinuousOn unbdryA { a : WithBotTop ι | a ≠ ⊥ ∧ a ≠ ⊤ } :=
  continuousOn_unbdryD _

lemma tendsto_unbdry (a : {a : WithBotTop ι | a ≠ ⊥ ∧ a ≠ ⊤}) :
    Tendsto (fun x ↦ unbdry x.1 x.2.1 x.2.2) (𝓝 a) (𝓝 (unbdry a a.2.1 a.2.2)) := by
  have : Nonempty ι := ⟨unbdry a a.2.1 a.2.2⟩
  simp only [← unbdryA_eq_unbdry, ne_eq, coe_setOf, mem_setOf_eq]
  exact (tendsto_unbdryA a.2.2 a.2.1).comp <| tendsto_subtype_rng.mp tendsto_id

lemma continuous_unbdry :
    Continuous (fun x : {a : WithBotTop ι | a ≠ ⊥ ∧ a ≠ ⊤} ↦ unbdry x.1 x.2.1 x.2.2) :=
  continuous_iff_continuousAt.mpr tendsto_unbdry

variable (ι) in
/-- The finite part of `WithBotTop ι` is homeomorphic to `ι`. -/
noncomputable def neBotTopHomeomorph : {a : WithBotTop ι | a ≠ ⊥ ∧ a ≠ ⊤} ≃ₜ ι where
  toEquiv := Equiv.withBotTopSubtypeNe
  continuous_toFun := continuous_unbdry
  continuous_invFun := continuous_coe.subtype_mk _

lemma tendsto_coe_iff_tendsto_unbdryD {α : Type*} {l : Filter α} {u : α → WithBotTop ι} {d a : ι}
    (hu : ∀ᶠ x in l, u x ≠ ⊥ ∧ u x ≠ ⊤) :
    Tendsto u l (𝓝 (a : WithBotTop ι)) ↔
      Tendsto (fun x ↦ (u x).unbdryD d) l (𝓝 a) := by
  refine (tendsto_congr' ?_).trans isEmbedding_coe.tendsto_nhds_iff.symm
  filter_upwards [hu] with x hx
  obtain ⟨_, h⟩ := canLift.prf (u x) hx
  simp [← h]

lemma tendsto_coe_iff_tendsto_unbdryD' {α : Type*} {l : Filter α} {u : α → WithBotTop ι} {d a : ι} :
    Tendsto u l (𝓝 (a : WithBotTop ι)) ↔
      (∀ᶠ x in l, u x ≠ ⊥ ∧ u x ≠ ⊤) ∧ Tendsto (fun x ↦ (u x).unbdryD d) l (𝓝 a) := by
  constructor
  · intro h
    let h' := (h.eventually <| isOpen_Ioo.mem_nhds ⟨bot_lt_coe a, coe_lt_top a⟩).mono
        fun _ hx ↦ (mem_Ioo_bot_top _).1 hx
    exact ⟨h', (tendsto_coe_iff_tendsto_unbdryD h').1 h⟩
  · exact fun h ↦ (tendsto_coe_iff_tendsto_unbdryD h.1).2 h.2

theorem nhds_top : 𝓝 (⊤ : WithBotTop ι) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp only [lt_top_iff_ne_top]

theorem nhds_bot : 𝓝 (⊥ : WithBotTop ι) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]

variable [Nonempty ι]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : WithBotTop ι)).HasBasis (fun _ : ι ↦ True) (Ioi ·) := by
  refine (nhds_top_basis (α := WithBotTop ι)).to_hasBasis (fun x hx => ?_)
    fun a _ ↦ ⟨(a : WithBotTop ι), by simp, Subset.rfl⟩
  match x with
  | ⊥ => exact ⟨‹Nonempty ι›.some, trivial, Ioi_subset_Ioi bot_le⟩
  | ⊤ => simp at hx
  | (a : ι) => exact ⟨a, trivial, Subset.rfl⟩

theorem nhds_top' :
    𝓝 (⊤ : WithBotTop ι) = ⨅ a : ι, 𝓟 (Ioi (a : WithBotTop ι)) := nhds_top_basis.eq_iInf

theorem mem_nhds_top_iff {s : Set (WithBotTop ι)} :
    s ∈ 𝓝 (⊤ : WithBotTop ι) ↔ ∃ y : ι, Ioi (y : WithBotTop ι) ⊆ s :=
  nhds_top_basis.mem_iff.trans <| by simp only [true_and]

lemma tendsto_nhds_top_iff {α : Type*} {f : Filter α} (x : α → WithBotTop ι) :
    Tendsto x f (𝓝 ⊤) ↔ ∀ (i : ι), ∀ᶠ (a : α) in f, i < x a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]

nonrec theorem nhds_bot_basis : (𝓝 (⊥ : WithBotTop ι)).HasBasis (fun _ : ι ↦ True) (Iio ·) := by
  refine (nhds_bot_basis (α := WithBotTop ι)).to_hasBasis (fun x hx => ?_)
    fun a _ ↦ ⟨(a : WithBotTop ι), by simp, Subset.rfl⟩
  match x with
  | ⊥ => simp at hx
  | ⊤ => exact ⟨‹Nonempty ι›.some, trivial, Iio_subset_Iio le_top⟩
  | (a : ι) => exact ⟨a, trivial, Subset.rfl⟩

theorem nhds_bot' :
    𝓝 (⊥ : WithBotTop ι) = ⨅ a : ι, 𝓟 (Iio (a : WithBotTop ι)) := nhds_bot_basis.eq_iInf

theorem mem_nhds_bot_iff {s : Set (WithBotTop ι)} :
    s ∈ 𝓝 (⊥ : WithBotTop ι) ↔ ∃ y : ι, Iio (y : WithBotTop ι) ⊆ s :=
  nhds_bot_basis.mem_iff.trans <| by simp only [true_and]

lemma tendsto_nhds_bot_iff {α : Type*} {f : Filter α} (x : α → WithBotTop ι) :
    Tendsto x f (𝓝 ⊥) ↔ ∀ (i : ι), ∀ᶠ (a : α) in f, x a < i :=
  nhds_bot_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Iio]

lemma nhdsWithin_top [NoMaxOrder ι] :
    𝓝[≠] (⊤ : WithBotTop ι) = atTop.map ((↑) : ι → WithBotTop ι) :=
  (nhdsWithin_hasBasis nhds_top_basis {⊤}ᶜ).eq_of_same_basis <| by
    simpa only [image_coe_Ioi, ← Ioi_inter_Iio, Iio_top] using
      atTop_basis_Ioi.map ((↑) : ι → WithBotTop ι)

lemma nhdsWithin_bot [NoMinOrder ι] :
    𝓝[≠] (⊥ : WithBotTop ι) = atBot.map ((↑) : ι → WithBotTop ι) :=
  (nhdsWithin_hasBasis nhds_bot_basis {⊥}ᶜ).eq_of_same_basis <| by
    simpa only [image_coe_Iio, ← Iio_inter_Ioi, Ioi_bot] using
      atBot_basis_Iio.map ((↑) : ι → WithBotTop ι)

@[simp]
lemma tendsto_coe_nhds_top_iff {α : Type*} {f : α → ι} {l : Filter α} [NoMaxOrder ι] :
    Tendsto (fun x => (f x : WithBotTop ι)) l (𝓝 ⊤) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff, atTop_basis_Ioi.tendsto_right_iff]
  simp

lemma tendsto_coe_atTop [NoMaxOrder ι] :
    Tendsto ((↑) : ι → WithBotTop ι) atTop (𝓝 ⊤) :=
  tendsto_coe_nhds_top_iff.2 tendsto_id

@[simp]
lemma tendsto_coe_nhds_bot_iff {α : Type*} {f : α → ι} {l : Filter α} [NoMinOrder ι] :
    Tendsto (fun x => (f x : WithBotTop ι)) l (𝓝 ⊥) ↔ Tendsto f l atBot := by
  rw [tendsto_nhds_bot_iff, atBot_basis_Iio.tendsto_right_iff]
  simp

lemma tendsto_coe_atBot [NoMinOrder ι] :
    Tendsto ((↑) : ι → WithBotTop ι) atBot (𝓝 ⊥) :=
  tendsto_coe_nhds_bot_iff.2 tendsto_id

lemma tendsto_unbdryD_nhdsWithin_top (d : ι) [NoMaxOrder ι] :
    Tendsto (WithBotTop.unbdryD d) (𝓝[≠] (⊤ : WithBotTop ι)) atTop := by
  rw [nhdsWithin_top, tendsto_map'_iff]
  exact tendsto_id

lemma tendsto_unbdryD_nhdsWithin_bot (d : ι) [NoMinOrder ι] :
    Tendsto (WithBotTop.unbdryD d) (𝓝[≠] (⊥ : WithBotTop ι)) atBot := by
  rw [nhdsWithin_bot, tendsto_map'_iff]
  exact tendsto_id

end Boundary

end WithBotTop
