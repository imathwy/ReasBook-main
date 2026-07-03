import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_3_1 (from Items/Chap01) -/
universe u

variable {F : Type u} [Group F]
variable [IsFreeGroup F]

/-- Proposition 1-3-1: a free group of rank greater than `1` contains a subgroup that is not
finitely generated, equivalently a free subgroup of infinite rank. -/
-- Layer triage:
-- `source-facing`: existence of a subgroup of infinite rank inside a free group of rank `> 1`.
-- `core/canonical`: the subgroup owner `H : Subgroup F`, its finite-generation predicate `H.FG`,
-- and the chosen generator type `IsFreeGroup.Generators F`.
-- `bridge/view`: for free groups, "infinite rank" is expressed here by failure of finite
-- generation of the subgroup owner, since every subgroup of a free group is itself free.
-- Domain sampling:
-- 1. `Subgroup.FG` from `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `subgroupIsFreeOfIsFree` from `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the
--    canonical owner theorem saying that subgroups of free groups are free.
-- 3. `FreeGroupBasis ι G` from `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the canonical owner
--    for an explicit free basis of a group.
-- 4. `IsFreeGroup.basis F` is the ambient chosen-basis owner used to read the source hypothesis
--    "rank greater than `1`" as the explicit input
--    `hRank : Nontrivial (IsFreeGroup.Generators F)` without introducing a parallel local rank
--    wrapper.
-- Primitive vs. derived:
-- the primitive public data are only the ambient free group `F` and the subgroup owner
-- `H : Subgroup F`; the infinite-basis formulation is derived bridge API, not primitive data.
-- Proof sketch: choose distinct free generators `x` and `y` of `F`. The conjugates
-- `y ^ (-n) * x * y ^ n` for `n : ℤ` form a countably infinite Nielsen-reduced family, hence a
-- free basis of the subgroup they generate. A subgroup with such a basis cannot be finitely
-- generated.
theorem exists_non_fg_subgroup_of_rank_gt_one
    (hRank : Nontrivial (IsFreeGroup.Generators F)) : ∃ H : Subgroup F, ¬ H.FG := by
  let _ : Nontrivial (IsFreeGroup.Generators F) := hRank
  sorry

/-- Companion bridge for Proposition 1-3-1: under the same hypothesis, one can express the
textbook phrase "a free subgroup of infinite rank" directly through the canonical owner
`FreeGroupBasis`. -/
-- Proof sketch: apply the source-facing theorem to obtain a subgroup `H ≤ F` that is not
-- finitely generated. Nielsen-Schreier gives `IsFreeGroup H`. Choosing a basis of `H`, the
-- indexing type cannot be finite, since a finite basis would make `H` finitely generated.
theorem exists_subgroup_with_infinite_free_basis_of_rank_gt_one
    (hRank : Nontrivial (IsFreeGroup.Generators F)) :
    ∃ (H : Subgroup F) (ι : Type u), Infinite ι ∧ Nonempty (FreeGroupBasis ι H) := by
  let _ : Nontrivial (IsFreeGroup.Generators F) := hRank
  sorry

/-! ### Proposition_1_3_2 (from Items/Chap01) -/
universe u v

section

variable {G : Type u} [Group G]

/-- Proposition 1-3-2: if each successor `F (i + 1)` is a subgroup of `F i` containing no element
of any basis of `F i`, then every nontrivial element of `F i` has `b`-word length at least
`i + 1`. -/
-- Layer triage:
-- `source-facing`: a descending chain `F : ℕ → Subgroup G` inside the ambient free group `G`.
-- `core/canonical`: the ambient word-length function attached to `b : FreeGroupBasis ι G`, and
-- the project owner predicate `IsPrimitiveElement` for “belongs to some free basis.”
-- `bridge/view`: each subgroup `F i` is free, so the source phrase “contains no element of any
-- basis of `F i`” is expressed intrinsically as avoidance of primitive elements of `F i`.
-- Proof sketch: argue by induction on `i`. The base case is the usual fact that a nontrivial
-- reduced word in a free basis has length at least `1`. For the induction step, choose a basis of
-- `F i`, rewrite the primitive-element avoidance hypothesis back into the source basis language,
-- use it to rule out length `1`, and then apply the Nielsen-reduction estimates from Section 2 to
-- show the ambient `b`-length grows by at least one.
theorem wordLength_lower_bound_of_descending_subgroups_avoiding_bases
    (F : ℕ → Subgroup G) (hdesc : ∀ i, F (i + 1) ≤ F i)
    (havoid : ∀ i {w : F i}, IsPrimitiveElement w → (w : G) ∉ F (i + 1))
    {ι : Type v} [DecidableEq ι] (b : FreeGroupBasis ι G) {i : ℕ} {w : F i} (hw : w ≠ 1) :
    i + 1 ≤ FreeGroup.norm (b.repr w) := by
  classical
  sorry

/-- A descending chain of subgroups satisfying the basis-avoidance hypothesis has trivial
intersection. -/
-- Proof sketch: for any nontrivial `w` in the intersection, the previous theorem gives
-- `i + 1 ≤ FreeGroup.norm (b.repr w)` for every `i`, contradicting the fixed finite word length of
-- `w` relative to any basis `b` of the ambient free group.
theorem iInf_eq_bot_of_descending_subgroups_avoiding_bases
    [IsFreeGroup G]
    (F : ℕ → Subgroup G) (hdesc : ∀ i, F (i + 1) ≤ F i)
    (havoid : ∀ i {w : F i}, IsPrimitiveElement w → (w : G) ∉ F (i + 1)) :
    (⨅ i, F i) = (⊥ : Subgroup G) := sorry

end

/-! ### Proposition_1_3_3 (from Items/Chap01) -/
universe u

open Subgroup

section

variable {G : Type u} [Group G]

private theorem subgroup_eq_top_of_basis_subset {ι : Type*} (b : FreeGroupBasis ι G)
    {K : Subgroup G} (hbK : ∀ i, b i ∈ K) :
    K = ⊤ := by
  let φ : G →* K := b.lift fun i ↦ ⟨b i, hbK i⟩
  have hsubtype_comp : K.subtype.comp φ = MonoidHom.id G := by
    apply b.ext_hom
    simp [φ]
  apply top_unique
  intro g _
  have hg : ((φ g : K) : G) = g := by
    simpa [φ] using DFunLike.congr_fun hsubtype_comp g
  exact hg.symm ▸ (φ g).2

private theorem basis_element_not_mem_proper_characteristic_subgroup {ι : Type*}
    (b : FreeGroupBasis ι G) {H : Subgroup G} (hproper : H < ⊤) (hchar : H.Characteristic)
    (i : ι) :
    b i ∉ H := by
  let _ : DecidableEq ι := Classical.decEq _
  intro hiH
  have hall : ∀ j, b j ∈ H := by
    intro j
    let φ : G ≃* G :=
      (b.repr.trans (FreeGroup.freeGroupCongr (Equiv.swap i j))).trans b.repr.symm
    have hle := (characteristic_iff_le_comap.mp hchar) φ
    have hφi : φ (b i) ∈ H := hle hiH
    simpa [φ] using hφi
  have htop : H = ⊤ := subgroup_eq_top_of_basis_subset b hall
  exact hproper.ne htop

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-3: for a descending chain of subgroups of a free group, if each successor is a
proper characteristic subgroup of its predecessor, then the intersection of the chain is trivial.
-/
-- Layer triage:
-- `source-facing`: the descending chain `FSeries : ℕ → Subgroup F`.
-- `core/canonical`: the subgroup lattice infimum `⨅ i, FSeries i`.
-- `bridge/view`: Proposition 1-3-2 already packages the owner theorem for descending chains that
-- avoid primitive elements of each stage, so this item only supplies the characteristic-subgroup
-- bridge from basis elements to that owner-level avoidance hypothesis.
theorem iInf_eq_bot_of_descending_proper_characteristic_subgroups
    (FSeries : ℕ → Subgroup F) (hproper : ∀ i, FSeries (i + 1) < FSeries i)
    (hchar : ∀ i, ((FSeries (i + 1)).subgroupOf (FSeries i)).Characteristic) :
    (⨅ i, FSeries i) = ⊥ := by
  have hdesc : ∀ i, FSeries (i + 1) ≤ FSeries i := fun i ↦ (hproper i).le
  have havoid : ∀ i {w : FSeries i}, IsPrimitiveElement w → (w : F) ∉ FSeries (i + 1) := by
    intro i w hw
    rcases hw with ⟨κ, B, k, rfl⟩
    let H : Subgroup (FSeries i) := (FSeries (i + 1)).subgroupOf (FSeries i)
    have hHproper : H < ⊤ := by
      refine lt_of_le_of_ne le_top ?_
      intro hEq
      have hle : FSeries i ≤ FSeries (i + 1) := subgroupOf_eq_top.1 hEq
      exact (hproper i).ne (le_antisymm (hproper i).le hle)
    simpa [H] using basis_element_not_mem_proper_characteristic_subgroup B hHproper (hchar i) k
  exact iInf_eq_bot_of_descending_subgroups_avoiding_bases FSeries hdesc havoid

end

end

/-! ### Proposition_1_3_4 (from Items/Chap01) -/
universe u

section

open Subgroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-4: the intersection of all terms in the derived series of a free group is
trivial. -/
-- Layer triage:
-- `source-facing`: the intersection statement for the derived series of a free group.
-- `core/canonical`: mathlib's owner sequence `derivedSeries F`.
-- `bridge/view`: the canonical comparison `derived_le_lower_central` identifies the derived-series
-- intersection as a subgroup of the lower-central-series intersection, whose triviality is already
-- the chapter owner theorem `iInf_lowerCentralSeries_eq_bot_of_isFreeGroup`.
-- Domain sampling:
-- 1. `derivedSeries F` is mathlib's owner declaration for the derived series.
-- 2. `lowerCentralSeries F` is mathlib's owner declaration for the descending central series.
-- 3. `derived_le_lower_central` is the canonical bridge from the derived series to the lower
--    central series.
-- 4. `iInf_lowerCentralSeries_eq_bot_of_isFreeGroup` is the project owner theorem for triviality
--    of the lower-central intersection in a free group.
-- Primitive vs. derived:
-- the only primitive datum is the free-group owner instance `[IsFreeGroup F]`; the subgroup infima
-- `⨅ n, derivedSeries F n` and `⨅ n, lowerCentralSeries F n` are the canonical derived lattice
-- objects encoding the source intersections.
theorem iInf_derivedSeries_eq_bot_of_isFreeGroup :
    (⨅ n : ℕ, derivedSeries F n) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hg_lower : g ∈ ⨅ n : ℕ, lowerCentralSeries F n := by
    rw [Subgroup.mem_iInf]
    intro n
    exact derived_le_lower_central n <| Subgroup.mem_iInf.mp hg n
  simpa [iInf_lowerCentralSeries_eq_bot_of_isFreeGroup] using hg_lower

end

/-! ### Proposition_1_3_5 (from Items/Chap01) -/
universe u

variable {G : Type u} [Group G]

/-- A group is Hopfian when every surjective endomorphism is injective. -/
class IsHopfian (G : Type u) [Group G] : Prop where
  injective_of_surjective (φ : G →* G) (hφ : Function.Surjective φ) : Function.Injective φ

/-- A group is cohopfian when every injective endomorphism is surjective. -/
class IsCohopfian (G : Type u) [Group G] : Prop where
  surjective_of_injective (φ : G →* G) (hφ : Function.Injective φ) : Function.Surjective φ

namespace MonoidHom

/-- A surjective endomorphism of a Hopfian group is injective. -/
theorem injective_of_surjective [IsHopfian G] (φ : G →* G) (hφ : Function.Surjective φ) :
    Function.Injective φ :=
  IsHopfian.injective_of_surjective φ hφ

/-- An injective endomorphism of a cohopfian group is surjective. -/
theorem surjective_of_injective [IsCohopfian G] (φ : G →* G) (hφ : Function.Injective φ) :
    Function.Surjective φ :=
  IsCohopfian.surjective_of_injective φ hφ

end MonoidHom

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

noncomputable section

namespace IsFreeGroup

/-- A finitely generated free group has a finite canonical generator type. -/
theorem finite_generators (F : Type u) [Group F] [IsFreeGroup F] [Group.FG F] :
    Finite (IsFreeGroup.Generators F) := by
  let α := IsFreeGroup.Generators F
  let e : F ≃* FreeGroup α := IsFreeGroup.toFreeGroup F
  let f : F →* FreeGroup α := e.toMonoidHom
  have hf : Function.Surjective f := e.surjective
  letI : Group.FG (FreeGroup α) := Group.fg_of_surjective hf
  letI : Group.FG (Abelianization (FreeGroup α)) := QuotientGroup.fg (commutator (FreeGroup α))
  letI : AddGroup.FG (Additive (Abelianization (FreeGroup α))) := AddGroup.fg_of_group_fg
  let eab : Additive (Abelianization (FreeGroup α)) ≃+ FreeAbelianGroup α := AddEquiv.refl _
  let fab : Additive (Abelianization (FreeGroup α)) →+ FreeAbelianGroup α := eab.toAddMonoidHom
  have hfab : Function.Surjective fab := eab.surjective
  letI : AddGroup.FG (FreeAbelianGroup α) := AddGroup.fg_of_surjective hfab
  exact Module.Finite.finite_basis (FreeAbelianGroup.basis α)

end IsFreeGroup

-- Primary domain: finitely generated free groups via their canonical free basis and finite
-- generating subsets.
-- `source-facing`: a surjective endomorphism `φ : F →* F` of a finitely generated free group.
-- `core/canonical`: `IsFreeGroup.basis F`, `FreeGroupBasis`, and the owner finite-generator
-- rank/basis lemmas from Proposition `1-2-9`.
-- `bridge/view`: the finite image set of the canonical basis under `φ`.
--
-- Domain sampling:
-- 1. `IsFreeGroup.basis F` is mathlib's owner basis for the ambient free group.
-- 2. `fintype_card_le_card_of_generating_finset` is the chapter owner rank inequality for a
--    finite generating set relative to a chosen free basis.
-- 3. `finset_isFreeGroupBasis_iff_card_and_closure_eq_top` is the owner criterion turning a
--    finite generating set of the correct cardinality into a free basis.
-- 4. `[Group.FG F]` is the owner interface for “finitely generated free group”; finiteness of the
--    canonical generator type is derived internally via abelianization and
--    `FreeAbelianGroup.basis`.
--
-- Primitive vs. derived:
-- the primitive data are the ambient owner basis `IsFreeGroup.basis F` and the surjective
-- endomorphism `φ`. The finiteness of `IsFreeGroup.Generators F`, the finite image set of that
-- basis, its basis property, and the resulting inverse homomorphism are derived API and should be
-- built from those owner declarations rather than from an auxiliary `Fin n` coordinate model.

/-- Proposition 1-3-5: every surjective endomorphism of a finitely generated free group is
bijective, so every finitely generated free group is Hopfian. -/
-- Proof sketch: choose the canonical finite free basis `IsFreeGroup.basis F`. The image of that
-- basis under a surjective endomorphism still generates `F`, so the rank comparison argument from
-- the preceding basis-cardinality results forces the image basis to have the same finite
-- cardinality as the original one. A surjective endomorphism carrying one free basis to another is
-- therefore an automorphism, hence bijective.
theorem surjective_endomorphism_bijective (φ : F →* F) (hφ : Function.Surjective φ) :
    Function.Bijective φ := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  letI : Fintype (IsFreeGroup.Generators F) := Fintype.ofFinite _
  letI : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  letI : DecidableEq F := Classical.decEq _
  let basis := IsFreeGroup.basis F
  let e := basis.repr.symm
  let f : IsFreeGroup.Generators F → F := fun i ↦ φ (basis i)
  let U : Finset F := Finset.univ.image f
  have hgenU : Subgroup.closure (U : Set F) = ⊤ := by
    have hlift : FreeGroup.lift f = φ.comp e.toMonoidHom := by
      apply FreeGroup.ext_hom
      intro i
      simp only [f, FreeGroup.lift_apply_of, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply]
      rfl
    have hsurj_lift :
        Function.Surjective (FreeGroup.lift f : FreeGroup (IsFreeGroup.Generators F) →* F) := by
      rw [hlift]
      exact hφ.comp e.surjective
    have htop : (FreeGroup.lift f).range = ⊤ := MonoidHom.range_eq_top.2 hsurj_lift
    simpa [U, Finset.coe_image, Set.image_univ, FreeGroup.range_lift_eq_closure] using htop
  have hrank : Fintype.card (IsFreeGroup.Generators F) ≤ U.card := by
    simpa using fintype_card_le_card_of_generating_finset basis U hgenU
  have hcard_le : U.card ≤ Fintype.card (IsFreeGroup.Generators F) := by
    have h : (Finset.univ.image f).card ≤ (Finset.univ : Finset (IsFreeGroup.Generators F)).card :=
      Finset.card_image_le
    simpa [U] using h
  have hcard : U.card = Fintype.card (IsFreeGroup.Generators F) := le_antisymm hcard_le hrank
  have hInjOn : Set.InjOn f (Finset.univ : Finset (IsFreeGroup.Generators F)) := by
    rw [← Finset.card_image_iff]
    simp [U, hcard]
  have hf_injective : Function.Injective f := by
    intro i j hij
    exact hInjOn (by simp) (by simp) hij
  have hUbasis : IsFreeGroupBasis (↑U : Set F) :=
    (finset_isFreeGroupBasis_iff_card_and_closure_eq_top basis U).2 ⟨hcard, hgenU⟩
  let toU : IsFreeGroup.Generators F → U := fun i ↦ ⟨f i, by
    change f i ∈ Finset.univ.image f
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have htoU_bijective : Function.Bijective toU := by
    constructor
    · intro i j hij
      apply hf_injective
      exact congrArg Subtype.val hij
    · intro u
      rcases Finset.mem_image.mp u.property with ⟨i, -, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  let eU : IsFreeGroup.Generators F ≃ U := Equiv.ofBijective toU htoU_bijective
  let g : U → F := fun u ↦ basis (eU.symm u)
  obtain ⟨ψ, hψ, -⟩ := hUbasis g
  have hleft : ψ.comp φ = MonoidHom.id F := by
    apply basis.ext_hom
    intro i
    have hψi : ψ (f i) = basis i := by
      have hi : eU.symm (toU i) = i := by
        change eU.symm (eU i) = i
        exact eU.left_inv i
      calc
        ψ (f i) = basis (eU.symm (toU i)) := by
          simpa [g, toU] using hψ (toU i)
        _ = basis i := by rw [hi]
    simpa [f, MonoidHom.comp_apply] using hψi
  have hleftInv : Function.LeftInverse ψ φ := by
    intro x
    simpa [MonoidHom.comp_apply] using congrArg (fun χ : F →* F ↦ χ x) hleft
  exact ⟨hleftInv.injective, hφ⟩

/-- A finitely generated free group is Hopfian. -/
instance isHopfian_of_fg_freeGroup : IsHopfian F where
  injective_of_surjective φ hφ :=
    (surjective_endomorphism_bijective φ hφ).1

end

end

/-! ### Proposition_1_3_6 (from Items/Chap01) -/
universe u

namespace Subgroup

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable (H : ℕ →o Subgroup F)

omit [IsFreeGroup F] in
private theorem group_fg_of_subgroup_fg {K : Subgroup F} (hK : K.FG) : Group.FG K :=
  (Group.fg_iff_subgroup_fg K).2 hK

/-- Proposition 1-3-6 (Takahasi): an ascending chain of free subgroups of uniformly bounded finite
rank in a free group eventually stabilizes. -/
-- Layer triage:
-- `source-facing`: an ascending chain `H : ℕ →o Subgroup F` in an ambient free group whose stages
-- have rank at most `r`.
-- `core/canonical`: the ambient owner hypothesis `[IsFreeGroup F]`, the order-hom owner for the
-- chain, the subgroup owner `Subgroup.FG`, the rank owner `Group.rank`, and equality in the
-- subgroup lattice.
-- `bridge/view`: the stabilized union `⨆ n, H n` is a derived consequence, not the main
-- source-facing statement.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib.GroupTheory.Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Group.rank` in `Mathlib.GroupTheory.Rank` is the canonical owner invariant for “generated
--    by at most `r` elements”, so bounded rank should be stated through it rather than through a
--    displayed family of finite generating sets.
-- 3. `subgroupIsFreeOfIsFree` is the canonical owner theorem deriving stagewise freeness from the
--    ambient free-group hypothesis, so `[∀ n, IsFreeGroup (H n)]` is duplicate wheel data here.
-- 4. `ℕ →o Subgroup F` is mathlib's canonical owner abstraction for an ascending subgroup chain,
--    so the monotonicity proof should be primitive data of the chain rather than a separate public
--    argument.
-- 5. `iSup_le` and `le_iSup` are the lattice owners used to pass from eventual constancy to the
--    union statement.
--
-- Primitive vs. derived:
-- the primitive public data are the ambient free group `F`, the order-hom chain `H`, the bound
-- `r`, and the owner-level bounded-rank hypotheses that each stage is finitely generated and has
-- `Group.rank` at most `r`. Stagewise freeness, a stabilizing stage, and the equality
-- `(⨆ n, H n) = H N` are derived API and should be exposed as separate companion declarations.
--
-- Proof sketch: Takahasi's argument shows that in a free group a proper inclusion between
-- finitely generated free subgroups forces the rank to increase. Since the rank of each `H n` is
-- bounded by `r`, only finitely many strict inclusions can occur, so the chain becomes constant.
theorem exists_stabilizing_index_of_bounded_rank (r : ℕ)
    (hfg : ∀ n, (H n).FG)
    (hrank :
      ∀ n,
        letI : Group.FG (H n) := group_fg_of_subgroup_fg (hfg n)
        Group.rank (H n) ≤ r) :
    ∃ N, ∀ n, N ≤ n → H n = H N := sorry

/-- Companion reformulation of Proposition `1-3-6`: once the bounded-rank ascending chain
stabilizes, its union is already one of its stages. -/
theorem exists_iSup_eq_of_bounded_rank (r : ℕ)
    (hfg : ∀ n, (H n).FG)
    (hrank :
      ∀ n,
        letI : Group.FG (H n) := group_fg_of_subgroup_fg (hfg n)
        Group.rank (H n) ≤ r) :
    ∃ N, (⨆ n, H n) = H N := by
  have hstab : ∃ N, ∀ n, N ≤ n → H n = H N :=
    exists_stabilizing_index_of_bounded_rank H r hfg hrank
  rcases hstab with ⟨N, hN⟩
  refine ⟨N, le_antisymm ?_ (le_iSup H N)⟩
  refine iSup_le fun n ↦ ?_
  by_cases hn : n ≤ N
  · exact H.monotone hn
  · exact (hN n (Nat.le_of_not_ge hn)).le

end

end Subgroup

/-! ### Proposition_1_3_7 (from Items/Chap01) -/
universe u

open FreeGroup

section

variable {X : Type u} [DecidableEq X]
variable {H : Subgroup (FreeGroup X)} {T : H.RightTransversal}

/-- Proposition 1-3-7 (1): for a Schreier transversal `T`, two nontrivial generators `γ(t₁x₁)`
and `γ(t₂x₂)` coincide only when the transversal elements and letters agree. -/
-- Layer triage:
-- `source-facing`: the uniqueness statement for the textbook elements `γ(tx)` attached to a
-- Schreier transversal of a subgroup `H`.
-- `core/canonical`: `H.RightTransversal`, the canonical selector `T.2.toRightFun`, and the owner
-- `schreierGenerator`.
-- `bridge/view`: the textbook coset representative `\bar w` is the canonical right-coset
-- selector `T.2.toRightFun w`.
-- Domain sampling:
-- 1. `Subgroup.RightTransversal` / `IsComplement` in mathlib is the owner abstraction for a
--    chosen right-coset transversal.
-- 2. `IsComplement.toRightFun` is the canonical representative map determined by that owner.
-- 3. `schreierGenerator` and `schreierGeneratorSet` in Proposition `1-3-22` are the project
--    owners for the textbook Schreier elements.
-- 4. `Subgroup.closure_mul_image_eq_top` in `Mathlib/GroupTheory/Schreier` is the owner theorem
--    showing that the subgroup data and transversal determine the generated Schreier subgroup.
-- Primitive vs. derived:
-- the primitive source data are the subgroup `H` and its right transversal `T`; the
-- representative map `T.2.toRightFun` and the resulting Schreier generators are derived.
-- Proof sketch: compare reduced words for `t₁ * of x₁` and `t₂ * of x₂`; the initial-segment
-- closure of `T` and the right-transversal normalization force the last new letter and the
-- preceding transversal representative to be uniquely determined once the nontrivial Schreier
-- generator is fixed.
theorem schreierGenerator_eq_of_ne_one
    (hT : HasInitialSegments (T : Set (FreeGroup X)))
    {t₁ t₂ : ↥(T : Set (FreeGroup X))} {x₁ x₂ : X}
    (hγ : schreierGenerator T.2.toRightFun t₁ x₁ = schreierGenerator T.2.toRightFun t₂ x₂)
    (hγ_ne : schreierGenerator T.2.toRightFun t₁ x₁ ≠ 1) :
    t₁ = t₂ ∧ x₁ = x₂ := sorry

/-- Proposition 1-3-7 (2): the nontrivial Schreier generators coming from a Schreier transversal
form a free basis of the subgroup they generate. -/
-- Layer triage:
-- `source-facing`: the set `Y` of nontrivial elements `γ(tx)` attached to a Schreier transversal
-- of the subgroup `H`.
-- `core/canonical`: the subgroup
-- `Subgroup.closure (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun)` together with
-- the subset of that subgroup consisting of generators lying in `Y`.
-- `bridge/view`: `IsFreeGroupBasis` expresses the textbook subset-style basis property for the
-- generated subgroup, while the right-transversal data are carried canonically by `T`.
-- Proof sketch: let `G` be the subgroup generated by the nontrivial Schreier generators attached
-- to `T`. The right-transversal data keep the source notion of Schreier representatives intact,
-- and the initial-segment condition organizes reductions of the generators `γ(tx)`. The
-- uniqueness statement of part (1) then shows that reduced words in these generators remain
-- nontrivial, yielding the universal property of a free basis for the subgroup generated by `Y`.
theorem schreierGeneratorSet_isFreeGroupBasis
    (hT : HasInitialSegments (T : Set (FreeGroup X))) :
    IsFreeGroupBasis
      { y : Subgroup.closure (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun) |
          (y : FreeGroup X) ∈ schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun } :=
  sorry

end

/-! ### Proposition_1_3_8 (from Items/Chap01) -/
/- Proposition 1-3-8: every subgroup of a free group is free.

This source-facing item is exactly the canonical Nielsen-Schreier theorem already available in
mathlib as `subgroupIsFreeOfIsFree`, so the file keeps a direct recall of that theorem rather than
introducing a parallel local wrapper. -/
#check subgroupIsFreeOfIsFree

/-! ### Proposition_1_3_9 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-3-9: a finite-index subgroup `H` of a finite-rank free group `F` satisfies the
exact Schreier rank-index formula
`Group.rank H - 1 = H.index * (Group.rank F - 1)`. -/
-- Layer triage:
-- `source-facing`: Schreier's rank formula for a specific finite-index subgroup `H ≤ F`.
-- `core/canonical`: `Group.rank` and `Subgroup.index`.
-- `bridge/view`: the ambient assumptions `[IsFreeGroup F] [Group.FG F]` encode the source phrase
-- “finite-rank free group”, while freeness and finite generation of `H` are derived through
-- owner instances rather than stored as primitive data.
-- Domain sampling:
-- 1. `Group.rank` in `Mathlib/GroupTheory/Rank` is the owner invariant for finite generator rank.
-- 2. `Subgroup.rank_le_index_mul_rank` in `Mathlib/GroupTheory/Schreier` is the general
--    finite-index Schreier inequality.
-- 3. `subgroupIsFreeOfIsFree` in
--    `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the owner theorem giving freeness of `H`.
-- 4. `Subgroup.fg_of_index_ne_zero` in `Mathlib/GroupTheory/Schreier` is the owner instance
--    deriving `[Group.FG H]` from `[Group.FG F] [H.FiniteIndex]`.
-- Best owner abstraction: the proposition should be stated directly in terms of the intrinsic pair
-- `Group.rank` and `Subgroup.index`, not via a chosen Schreier basis or a separate finite-rank
-- wrapper for `H`.
-- Primitive vs. derived:
-- the primitive public data are only the subgroup `H : Subgroup F` and the finite-index instance
-- `[H.FiniteIndex]`; freeness and finite generation of `H` are derived API coming from the owner
-- abstractions above.
theorem finiteIndex_subgroup_rank_sub_one_eq (H : Subgroup F) [H.FiniteIndex] :
    Group.rank H - 1 = H.index * (Group.rank F - 1) := sorry

end

/-! ### Remark_1_3_10 (from Items/Chap01) -/
-- Layer triage:
-- `source-facing`: the forward-looking textbook remark that interprets Schreier's rank-index
-- formula geometrically and relates it to the Riemann-Hurwitz formula.
-- `core/canonical`: the preceding chapter theorem `finiteIndex_subgroup_rank_sub_one_eq`, whose
-- owner invariants are `Group.rank` and `Subgroup.index`.
-- `bridge/view`: this file contributes only prose context around that theorem, so the canonical
-- refinement is a direct recall rather than a parallel local restatement.
-- Domain sampling:
-- 1. `Group.rank` in `Mathlib/GroupTheory/Rank` is the owner invariant for finite generator rank.
-- 2. `Subgroup.index` in `Mathlib/GroupTheory/Index` is the owner invariant for subgroup index.
-- 3. `Subgroup.rank_le_index_mul_rank` in `Mathlib/GroupTheory/Schreier` is the upstream
--    Schreier inequality on the same owner abstractions.
-- 4. `finiteIndex_subgroup_rank_sub_one_eq` in Proposition `1-3-9` is already the exact
--    source-faithful chapter theorem recalled by this remark.
-- Primitive vs. derived:
-- this remark introduces no new primitive mathematical data; the only relevant public content is
-- the previously established theorem itself.

/- Remark 1-3-10: the Schreier rank-index formula from the preceding proposition has a geometric
interpretation, and this interpretation is closely related to the Riemann-Hurwitz formula.

This source item is a forward-looking prose remark rather than a standalone theorem. To keep the
formalization source-faithful without inventing a surrogate proposition, the file keeps only a
direct recall of the preceding chapter theorem that already states Schreier's rank-index formula
in the canonical owner variables `Group.rank` and `Subgroup.index`. -/
#check finiteIndex_subgroup_rank_sub_one_eq

/-! ### Proposition_1_3_11 (from Items/Chap01) -/
universe u

open CategoryTheory

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable (A : Finset F) (H : Subgroup F)

/-- Proposition 1-3-11: if `F` is a free group, `A` is a finite subset of `F`, and `H` is a
finitely generated subgroup of `F` disjoint from `A`, then there exists a finite-index subgroup
`G ≤ F` that is still disjoint from `A` and in which `H` is a free factor. -/
-- Layer triage:
-- `source-facing`: the existential overgroup `G : Subgroup F` of finite index and disjoint from
-- `A`.
-- `core/canonical`: the chapter owner predicate `Subgroup.IsFreeFactorOf`.
-- `bridge/view`: the textbook phrase "H is a free factor of G" is unpacked by
-- `Subgroup.isFreeFactorOf_iff` into the overgroup relation `H ≤ G` together with a
-- complementary free factor for `H.subgroupOf G` inside `G`.
--
-- Domain sampling:
-- 1. `Subgroup.IsFreeFactorOf` in Definition `1-2-28` is the chapter owner abstraction for the
--    source phrase “`H` is a free factor of `G`”.
-- 2. `Subgroup.AreFreeFactors` remains the underlying two-factor decomposition owner inside the
--    ambient overgroup `G`.
-- 3. `Subgroup.IsFreeFactorOf.isSplitMono` packages the split-inclusion bridge for the subgroup
--    inclusion into the overgroup.
-- 4. `Subgroup.subtype_isSplitMono_iff_exists_leftInverse` is the chapter owner criterion for a
--    retract subgroup.
--
-- Primitive vs. derived:
-- the primitive source data are only the finite subset `A`, the subgroup `H`, its finite
-- generation, and disjointness from `A`. The complementary subgroup inside the overgroup and the
-- resulting split inclusion are derived owner-level consequences and should not be repackaged as
-- additional primitive data.
-- Proof sketch: apply Hall's finite-index extension argument to the explicit finite-generation
-- hypothesis `hfg : H.FG` to obtain an overgroup `G` of `H` that avoids `A`, then invoke the
-- Nielsen-Schreier free-basis construction inside `G` to split the embedded subgroup
-- `H.subgroupOf G` off as a free factor.
theorem exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor
    (hfg : H.FG) (hA : Disjoint (A : Set F) (H : Set F)) :
    ∃ G : Subgroup F,
      G.FiniteIndex ∧
        Disjoint (A : Set F) (G : Set F) ∧
        H.IsFreeFactorOf G := sorry

/-- Owner-level bridge for Proposition 1-3-11: the same finite-index overgroup can be chosen so
that the transported inclusion of `H` into `G` is split. -/
-- Layer triage:
-- `bridge/view`: this is the canonical retract-subgroup reformulation of the source-facing
-- free-factor conclusion, obtained from `Subgroup.IsFreeFactorOf.isSplitMono`.
theorem exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype
    (hfg : H.FG) (hA : Disjoint (A : Set F) (H : Set F)) :
    ∃ G : Subgroup F,
      G.FiniteIndex ∧
        Disjoint (A : Set F) (G : Set F) ∧
        IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := by
  rcases exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor A H hfg hA with
    ⟨G, hG, hdisj, hfree⟩
  exact ⟨G, hG, hdisj, hfree.isSplitMono⟩

end

/-! ### Proposition_1_3_12 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-12: a finitely generated subgroup of a free group that contains a nontrivial
normal subgroup of the ambient free group has finite index. -/
-- Layer triage:
-- `source-facing`: a finitely generated subgroup `H : Subgroup F` together with a nontrivial
-- ambient-normal subgroup `N : Subgroup F` contained in `H`.
-- `core/canonical`: the subgroup owner `Subgroup F` with the canonical predicates
-- `Subgroup.FG`, `Subgroup.Normal`, and `Subgroup.FiniteIndex`, together with the order relation
-- `N ≤ H`.
-- `bridge/view`: the textbook phrase “`H` contains a non-trivial normal subgroup of `F`” is
-- expressed directly by the witness `N` and the atomic hypotheses `N ≤ H`, `N.Normal`, and
-- `N ≠ ⊥`; no extra wrapper around contained normal subgroups is introduced.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical owner predicate for
--    finite index.
-- 3. `Subgroup.AreFreeFactors` in Definition `1-2-28` is the chapter owner abstraction for the
--    free-factor decomposition produced by Hall's theorem.
-- 4. `exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor` in Proposition `1-3-11`
--    is the chapter owner theorem that supplies the finite-index overgroup in which `H` becomes a
--    free factor.
--
-- Best owner abstraction:
-- the public statement should stay at the subgroup-owner level. The free-factor overgroup from
-- Proposition `1-3-11` is derived proof input, not additional primitive public data for this
-- proposition.
--
-- Primitive vs. derived:
-- the primitive source data are exactly `H`, `N`, finite generation of `H`, containment `N ≤ H`,
-- normality of `N`, and nontriviality of `N`. The auxiliary finite-index overgroup and its
-- complementary free factor are derived from Proposition `1-3-11`, so they should remain inside
-- the proof architecture rather than being exposed as a parallel wrapper API.
-- Proof sketch: apply Proposition 1-3-11 to enlarge `H` to a finite-index subgroup `G` in which
-- `H` is a free factor. If `H` had infinite index, the complementary free factor in `G` would be
-- nontrivial. Conjugating a nontrivial element of `N` by an element of that complement produces an
-- element of `N` that cannot lie in the free factor `H`, contradicting `N ≤ H`.
theorem finiteIndex_of_fg_of_contains_nontrivial_normal (H N : Subgroup F) (hfg : H.FG)
    (hN_le : N ≤ H) (hN_normal : N.Normal) (hN : N ≠ ⊥) : H.FiniteIndex := sorry

end

/-! ### Proposition_1_3_13 (from Items/Chap01) -/
universe u

/- Proposition 1-3-13: every nontrivial finitely generated normal subgroup of a free group has
finite index.

Layer triage:
- `source-facing`: a nontrivial finitely generated normal subgroup `N : Subgroup F`.
- `core/canonical`: the subgroup owner `Subgroup F` together with the owner predicates
  `Subgroup.FG`, `Subgroup.Normal`, and `Subgroup.FiniteIndex`.
- `bridge/view`: Proposition `1-3-13` is exactly the specialization `H = N` of Proposition
  `1-3-12`, which already expresses the canonical owner theorem for a finitely generated subgroup
  containing a nontrivial normal subgroup.

Domain sampling:
1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for finite generation
   of a subgroup.
2. `Subgroup.fg_iff` in `Mathlib/GroupTheory/Finiteness` shows that finite generation is derived
   from the canonical subgroup owner via closure of a finite set, not from extra packaged data.
3. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite index,
   and `finiteIndex_iff_finite_quotient` is its standard quotient-level bridge.
4. `finiteIndex_of_fg_of_contains_nontrivial_normal` in Proposition `1-3-12` is the chapter owner
   theorem whose diagonal specialization `H = N` is exactly this proposition.

Best owner abstraction:
the public mathematics already lives at the canonical subgroup-owner level of Proposition
`1-3-12`; this proposition adds no new owner data beyond the diagonal specialization `H = N`.

Primitive vs. derived:
the primitive mathematical data are just the subgroup `N` and the owner predicates `N.FG`,
`N.Normal`, and `N ≠ ⊥`; the finite-index conclusion is derived. Since Proposition `1-3-12`
already consumes exactly those owner-level inputs after the canonical inclusion `N ≤ N = le_rfl`,
keeping a separate local theorem would duplicate the API surface without adding mathematics.

Accordingly, this file keeps only the exact diagonal recall term rather than a parallel local
specialization theorem. -/
#check
  (fun {F : Type u} [Group F] [IsFreeGroup F] (N : Subgroup F)
      (hfg : N.FG) (hN_normal : N.Normal) (hN : N ≠ ⊥) ↦
    finiteIndex_of_fg_of_contains_nontrivial_normal N N hfg le_rfl hN_normal hN :
      ∀ {F : Type u} [Group F] [IsFreeGroup F] (N : Subgroup F),
        N.FG → N.Normal → N ≠ ⊥ → N.FiniteIndex)

/-! ### Proposition_1_3_14 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-14: the intersection of two finitely generated subgroups of a free group is
itself finitely generated. -/
-- Layer triage:
-- `source-facing`: two finitely generated subgroups `H, K : Subgroup F` of the ambient free group.
-- `core/canonical`: the subgroup lattice infimum `H ⊓ K`, the finite-generation predicate
-- `Subgroup.FG`, Hall's finite-index split-subtype enlargement theorem
-- `exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype`, the subgroup-owner view
-- `Subgroup.subgroupOf`, and Schreier's finite-generation owner `Subgroup.fg_of_index_ne_zero`.
-- `bridge/view`: the textbook phrase “intersection of subgroups” is expressed directly by `H ⊓ K`;
-- any retract data needed in the proof should be handled through the existing chapter owner API
-- `Subgroup.subtype_isSplitMono_iff_exists_leftInverse`, not by a parallel local finite-generation
-- wrapper.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for subgroup finite
--    generation.
-- 2. `exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype` in Proposition
--    `1-3-11` is the chapter owner theorem that upgrades a finitely generated subgroup to a
--    finite-index overgroup with split inclusion.
-- 3. `Subgroup.subgroupOf` in `Mathlib/Algebra/Group/Subgroup/Map` is the canonical owner for
--    transporting intersections into an overgroup.
-- 4. `Subgroup.fg_of_index_ne_zero` in `Mathlib/GroupTheory/Schreier` is the canonical owner
--    theorem that finite-index subgroups of finitely generated groups are finitely generated.
--
-- Best owner abstraction:
-- the theorem belongs directly at the subgroup-owner level `Subgroup F`, with `H ⊓ K` as the
-- canonical intersection object. Any split-inclusion or retract argument in the proof is derived
-- bridge data and should reuse the existing owner-level chapter API rather than introducing a
-- second local owner for finitely generated retracts.
--
-- Primitive vs. derived:
-- the primitive public data are only `H`, `K`, and the two hypotheses `hH : H.FG`, `hK : K.FG`.
-- Any finite-index overgroup, restricted subgroup transport, or left inverse used to descend
-- finite generation to `H ⊓ K` is derived proof input, not public data.
theorem fg_inf_of_fg (H K : Subgroup F) (hH : H.FG) (hK : K.FG) : (H ⊓ K).FG := sorry

end

/-! ### Proposition_1_3_15 (from Items/Chap01) -/
universe u

open Subgroup

-- Layer triage:
-- `source-facing`: the one-relator group `<x, y | x⁻¹ y² x = y²>` together with the normal
-- closures of the images of `x` and `z = xy`.
-- `core/canonical`: `PresentedGroup`, `normalClosure`, `commutator`, and
-- `FreeGroupBasis`.
-- `bridge/view`: the distinguished elements `x`, `y`, and `z = xy` inside the presented group.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for a group given by generators and
--    relators.
-- 2. `normalClosure S` is the canonical owner for the normal subgroup generated by a subset.
-- 3. `commutator G` is the owner for the derived subgroup `[G, G]`.
-- 4. `FreeGroupBasis ι H` is the canonical owner for an explicit free basis of a group.
-- Primitive vs. derived:
-- the primitive source data are the two generators and the single relator; the ambient presented
-- group, the two normal closures, and the commutator subgroup are canonical constructions derived
-- from those data.

/-- The generators `x` and `y` for the presentation `<x, y | x⁻¹ y² x = y²>`. -/
inductive CentralizingSquareGenerator
  | x
  | y
  deriving DecidableEq

namespace CentralizingSquare

open CentralizingSquareGenerator

/-- The relator `x⁻¹ y² x y⁻²` defining the presentation. -/
abbrev relator : FreeGroup CentralizingSquareGenerator :=
  (FreeGroup.of x)⁻¹ * FreeGroup.of y ^ (2 : ℕ) * FreeGroup.of x * (FreeGroup.of y ^ (2 : ℕ))⁻¹

/-- The presented group `<x, y | x⁻¹ y² x = y²>`. -/
abbrev Group : Type := PresentedGroup ({relator} : Set (FreeGroup CentralizingSquareGenerator))

/-- The image of the generator `x` in the presented group. -/
abbrev x : Group := PresentedGroup.of CentralizingSquareGenerator.x

/-- The image of the generator `y` in the presented group. -/
abbrev y : Group := PresentedGroup.of CentralizingSquareGenerator.y

/-- The element `z = xy` in the presented group. -/
abbrev z : Group := x * y

/-- The normal closure of `x` in the presented group. -/
abbrev normalClosureX : Subgroup Group := normalClosure ({x} : Set Group)

/-- The normal closure of `z = xy` in the presented group. -/
abbrev normalClosureZ : Subgroup Group := normalClosure ({z} : Set Group)

end CentralizingSquare

open CentralizingSquare

/-- Proposition 1-3-15 (1): in the group `<x, y | x⁻¹ y² x = y²>`, the normal closure of `x` is
a free subgroup of rank `2`. -/
-- Proof sketch: quotient by the central subgroup generated by `y²` to identify the image of the
-- normal closure with a subgroup of `ℤ ∗ C₂`; Kurosh then shows that image is free, and the
-- explicit generators `x` and `y⁻¹xy` give a basis of size two. Lift that basis back because the
-- normal closure meets the center trivially.
theorem x_normalClosure_has_basis_fin_two :
    Nonempty (FreeGroupBasis (Fin 2) normalClosureX) := sorry

/-- Proposition 1-3-15 (2): in the group `<x, y | x⁻¹ y² x = y²>`, the normal closure of
`z = xy` is a free subgroup of rank `2`. -/
-- Proof sketch: use the Tietze-transformation automorphism carrying `x` to `z = xy` and fixing
-- `y`. Transport the basis from the previous clause across the induced automorphism of the ambient
-- group and the corresponding subgroup isomorphism on normal closures.
theorem z_normalClosure_has_basis_fin_two :
    Nonempty (FreeGroupBasis (Fin 2) normalClosureZ) := sorry

/-- Proposition 1-3-15 (3): in the group `<x, y | x⁻¹ y² x = y²>`, the intersection of the normal
closures of `x` and `z = xy` is the commutator subgroup. -/
-- Proof sketch: abelianize the presented group, identify the images of the two normal closures as
-- the cyclic subgroups generated by `x₀` and `x₀ y₀`, and check that an element lies in both
-- images exactly when its abelianization is trivial. This identifies the intersection with the
-- kernel of the abelianization map, namely the commutator subgroup.
theorem x_normalClosure_inf_z_normalClosure_eq_commutator :
    normalClosureX ⊓ normalClosureZ = commutator Group := sorry

/-- Proposition 1-3-15 (4): in the group `<x, y | x⁻¹ y² x = y²>`, the commutator subgroup is a
free group of infinite rank. Together with clause (3), this gives the same conclusion for
`H ∩ K`. -/
-- Proof sketch: apply the Reidemeister-Schreier/Kurosh analysis of the commutator subgroup coming
-- from the abelianization of the presented group. The subgroup is free, and the Schreier basis
-- obtained from the infinite cyclic quotient yields an infinite indexing type.
theorem commutator_has_infinite_free_basis :
    ∃ ι : Type u, Infinite ι ∧ Nonempty (FreeGroupBasis ι (commutator Group)) := sorry

/-! ### Proposition_1_3_16 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-16: a finitely generated subgroup of a free group that is contained in no
overgroup of infinite rank has finite index. -/
-- Layer triage:
-- `source-facing`: a subgroup `H : Subgroup F` and the hypothesis that every overgroup `K ≥ H`
-- has finite rank.
-- `core/canonical`: `Subgroup.FG`, `Subgroup.FiniteIndex`, and the order relation `H ≤ K` on
-- the subgroup lattice.
-- `bridge/view`: in a free group, “infinite rank” is expressed as failure of finite generation for
-- a subgroup, since every subgroup is itself free.
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical owner predicate for
--    finite index.
-- 3. `subgroupIsFreeOfIsFree` in
--    `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the owner theorem that lets the source
--    phrase “infinite rank” be expressed through subgroup finite generation.
-- 4. `exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor` in Proposition `1-3-11`
--    is the chapter owner theorem for the finite-index free-factor enlargement used in the proof
--    architecture.
-- Best owner abstraction:
-- the proposition is intrinsically about the subgroup owner `H : Subgroup F` and the lattice of
-- its overgroups. The finite-index conclusion belongs directly at that owner level; free-factor
-- enlargements and basis choices are derived proof input, not primitive public data.
-- Primitive vs. derived:
-- the primitive public data are exactly `H` and the source-faithful overgroup condition that
-- every `K` with `H ≤ K` is finitely generated. The source phrase “`H` is finitely generated” is
-- derived already by taking `K = H`, so it should not remain as a redundant public binder. Any
-- free-basis witness for a subgroup, any complementary factor in a Hall overgroup, and any
-- infinite-rank basis extracted from a counterexample are all derived bridge data and should
-- remain internal to the proof.
-- Proof sketch: first derive `H.FG` by applying `hover` to the tautological overgroup `H ≤ H`.
-- Proposition `1-3-11` with `A = ∅` then gives a finite-index overgroup `G` of `H` in which
-- `H` is a free factor. A proper Hall free-factor enlargement of `H` inside `G` would yield an
-- overgroup of `H` that is not finitely generated, contradicting `hover`. Hence that enlargement
-- is trivial, so `H = G` and therefore `H` has finite index.
theorem finiteIndex_of_all_overgroups_fg (H : Subgroup F)
    (hover : ∀ ⦃K : Subgroup F⦄, H ≤ K → K.FG) :
    H.FiniteIndex := by
  have hfg : H.FG := hover le_rfl
  sorry

end

/-! ### Proposition_1_3_17 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-3-17: if `H` is a finite-index subgroup of a free group `F` of rank greater
than `1`, then any overgroup `G` of `H` with rank at least that of `H` must already equal `H`. -/
-- Layer triage:
-- `source-facing`: rigidity of a finite-index free subgroup against proper overgroups of equal or
-- greater rank.
-- `core/canonical`: `Group.rank`, `Subgroup.index_strictAnti`, and the chapter's canonical
-- Schreier-formula theorem `finiteIndex_subgroup_rank_sub_one_eq`.
-- `bridge/view`: the textbook comparison “rank of the overgroup versus rank of the subgroup” is
-- expressed directly by the owner invariant `Group.rank`, while finiteness of `G.index` is derived
-- from `H ≤ G` and `[H.FiniteIndex]`.
-- Domain sampling:
-- 1. `Subgroup.index_strictAnti` in `Mathlib/GroupTheory/Index` is the owner monotonicity theorem
--    for proper inclusions of finite-index subgroups.
-- 2. `Subgroup.finiteIndex_of_le` in `Mathlib/GroupTheory/Index` is the owner bridge turning the
--    overgroup relation `H ≤ G` into the derived finite-index instance on `G`.
-- 3. `finiteIndex_subgroup_rank_sub_one_eq` in `Proposition_1_3_9` is the chapter owner theorem
--    converting subgroup index inequalities into rank inequalities in finite-rank free groups.
-- Primitive vs. derived:
-- the primitive public inputs are the subgroups `H`, `G`, the finite-index hypothesis on `H`, the
-- inclusion `H ≤ G`, and the rank comparison; the finite-index structure on `G` is derived API.
-- Proof sketch: if `H < G`, then `G` also has finite index and `Subgroup.index_strictAnti` gives
-- `G.index < H.index`. Multiplying by the positive factor `Group.rank F - 1` preserves the strict
-- inequality, and Schreier's formula rewrites it as `Group.rank G - 1 < Group.rank H - 1`. This
-- contradicts the assumed inequality `Group.rank H ≤ Group.rank G`.
theorem eq_of_le_of_rank_ge_of_finiteIndex_subgroup (hF_rank : 1 < Group.rank F)
    {H G : Subgroup F} [H.FiniteIndex] (hHG : H ≤ G) [Group.FG G]
    (h_rank : Group.rank H ≤ Group.rank G) : G = H := by
  haveI : G.FiniteIndex := Subgroup.finiteIndex_of_le hHG
  by_contra hGH
  have hlt : H < G := lt_of_le_of_ne hHG (fun h ↦ hGH h.symm)
  have hrank_sub : Group.rank G - 1 < Group.rank H - 1 := by
    simpa [finiteIndex_subgroup_rank_sub_one_eq G, finiteIndex_subgroup_rank_sub_one_eq H] using
      Nat.mul_lt_mul_of_pos_right (Subgroup.index_strictAnti hlt) (Nat.sub_pos_of_lt hF_rank)
  omega

end

/-! ### Proposition_1_3_18 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-18: a finitely generated subgroup of a free group that meets every nontrivial
normal subgroup nontrivially has finite index. -/
-- Layer triage:
-- `source-facing`: a subgroup `H : Subgroup F` with the intersection property against every
-- nontrivial normal subgroup `N`.
-- `core/canonical`: Proposition 1-3-16, whose owner abstraction is the absence of infinite-rank
-- overgroups, together with `Subgroup.FG`, `Subgroup.Normal`, `Subgroup.FiniteIndex`, and the
-- lattice intersection `H ⊓ N`.
-- `bridge/view`: the textbook phrase “has non-trivial intersection with” is encoded as
-- `H ⊓ N ≠ ⊥`, and this intersection hypothesis is used only to rule out infinite-rank overgroups
-- so that Proposition 1-3-16 applies.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for finite
--    generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite
--    index.
-- 3. `finiteIndex_of_fg_of_contains_nontrivial_normal` in Proposition `1-3-12` is the earlier
--    chapter owner theorem for the stronger containment hypothesis `N ≤ H`.
-- 4. `finiteIndex_of_all_overgroups_fg` in Proposition `1-3-16` is the best owner
--    abstraction for the present item, because the source intersection hypothesis is used only to
--    derive the finite-generation of every overgroup of `H`.
--
-- Best owner abstraction:
-- Proposition `1-3-16` is the canonical owner theorem. The present proposition should therefore
-- stay source-facing only in its hypothesis, and translate that hypothesis to the owner condition
-- “every overgroup of `H` is finitely generated” rather than introducing a parallel wrapper API.
--
-- Primitive vs. derived:
-- the primitive source data are `H`, `hfg`, and the normal-intersection hypothesis `hinter`.
-- The overgroup finite-generation statement needed by Proposition `1-3-16` is derived bridge API,
-- so it is discharged locally inside the proof rather than exposed as a parallel local theorem.
--
-- Proof sketch: if an overgroup `K ≥ H` had infinite rank, Hall's finite-index free-factor
-- enlargement argument inside `K` would produce a nontrivial normal subgroup of `F` disjoint from
-- `H`, contradicting the hypothesis. Thus every overgroup of `H` has finite rank, and Proposition
-- 1-3-16 gives finite index.
theorem finiteIndex_of_fg_of_inf_ne_bot_with_every_nontrivial_normal (H : Subgroup F)
    (hfg : H.FG)
    (hinter :
      ∀ N : Subgroup F, N.Normal → N ≠ ⊥ → H ⊓ N ≠ ⊥) :
    H.FiniteIndex := by
  refine finiteIndex_of_all_overgroups_fg H ?_
  intro K hHK
  sorry

end

/-! ### Proposition_1_3_19 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-!
Primary domain: finite-index subgroup intersections in torsion-free groups, specialized here to
free groups.

Layer triage:
- `source-facing`: fixed subgroups `H K : Subgroup F`, with `H` of finite index and `K ≠ ⊥`.
- `core/canonical`: `Subgroup.FiniteIndex`, `Subgroup.finite_iff_finite_and_finiteIndex`, and the
  ambient torsion-free owner `IsMulTorsionFree`.
- `bridge/view`: the textbook phrase “has non-trivial intersection with” is expressed as
  `H ⊓ K ≠ ⊥`.

Domain sampling:
1. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite index.
2. `Subgroup.instFiniteIndex_subgroupOf` is the canonical finite-index inheritance on
   `H.subgroupOf K`.
3. `Subgroup.finite_iff_finite_and_finiteIndex` is the owner bridge from a finite finite-index
   subgroup to finiteness of the ambient subgroup.
4. Proposition `1-2-18` provides the reused owner instance `IsMulTorsionFree F` for free groups.

Primitive vs. derived:
- primitive public data: the subgroups `H` and `K`, the finite-index structure on `H`, and the
  nontriviality hypothesis `K ≠ ⊥`;
- derived API: finiteness of `K` under the contradiction hypothesis `H ⊓ K = ⊥`, and hence
  triviality of `K` from torsion-freeness.
-/

/-- A finite subgroup of a torsion-free group is trivial. -/
private theorem eq_bot_of_finite_of_isMulTorsionFree {G : Type u} [Group G]
    [IsMulTorsionFree G] (K : Subgroup G) [Finite K] : K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxK : IsOfFinOrder xK := isTorsion_of_finite xK
  simpa [xK] using hxK.eq_one'

/-- A finite-index subgroup of a torsion-free group meets every nontrivial subgroup nontrivially. -/
private theorem inf_ne_bot_of_finiteIndex_of_ne_bot_of_isMulTorsionFree
    {G : Type u} [Group G] [IsMulTorsionFree G] (H K : Subgroup G) [H.FiniteIndex]
    (hK : K ≠ ⊥) :
    H ⊓ K ≠ ⊥ := by
  intro hHK
  have hsub : H.subgroupOf K = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, hHK]
  letI : Finite (H.subgroupOf K) := by
    simpa [hsub] using (inferInstance : Finite (⊥ : Subgroup K))
  have hK_finite : Finite K :=
    (Subgroup.finite_iff_finite_and_finiteIndex (H.subgroupOf K)).2
      ⟨inferInstance, inferInstance⟩
  letI : Finite K := hK_finite
  exact hK (eq_bot_of_finite_of_isMulTorsionFree K)

/-- Proposition 1-3-19: a finite-index subgroup of a free group has nontrivial intersection with
every nontrivial subgroup. -/
-- Layer triage:
-- `source-facing`: fixed subgroups `H K : Subgroup F`, with `H` of finite index and `K ≠ ⊥`.
-- `core/canonical`: `Subgroup.FiniteIndex`, `IsMulTorsionFree`, and the subgroup lattice infimum
-- `H ⊓ K`.
-- `bridge/view`: the textbook phrase “has non-trivial intersection with” is expressed as
-- `H ⊓ K ≠ ⊥`.
-- Proof sketch: under the contradiction hypothesis `H ⊓ K = ⊥`, the induced subgroup
-- `H.subgroupOf K` is trivial and hence finite; because it still has finite index in `K`, the
-- subgroup `K` itself is finite. Proposition `1-2-18` supplies torsion-freeness of free groups, so
-- every finite subgroup is trivial, contradicting `K ≠ ⊥`.
theorem inf_ne_bot_of_finiteIndex_of_ne_bot (H K : Subgroup F) [H.FiniteIndex] (hK : K ≠ ⊥) :
    H ⊓ K ≠ ⊥ :=
  inf_ne_bot_of_finiteIndex_of_ne_bot_of_isMulTorsionFree H K hK

end

/-! ### Proposition_1_3_20 (from Items/Chap01) -/
universe u

open FreeGroup
open QuotientGroup

/-!
Primary domain: Schreier transversals and Schreier generators for subgroups of free groups.

Layer triage:
- `source-facing`: a subgroup `H ≤ FreeGroup X`, a chosen right transversal `T`, and the textbook
  minimality condition saying that the chosen representative in each right coset has least
  reduced-word length.
- `core/canonical`: `Subgroup.RightTransversal`, `rightRel H`, `IsComplement.toRightFun`, and the
  existing chapter owners `HasInitialSegments`, `schreierGeneratorSet`, and
  `schreierGeneratorSet_isFreeGroupBasis`.
- `bridge/view`: the textbook representative `\bar w` is the canonical selector `T.2.toRightFun w`,
  while “minimal Schreier transversal” is the owner predicate `T.IsMinimalSchreier` layered on top
  of the right-transversal data.

Domain sampling:
1. `Subgroup.RightTransversal` in mathlib is the owner abstraction for chosen right-coset
   representatives.
2. `QuotientGroup.rightRel` is the canonical same-right-coset relation.
3. `IsComplement.toRightFun` and `IsComplement.mul_inv_toRightFun_mem` are the owner APIs for the
   canonical representative map and the associated subgroup element `g * \bar g⁻¹`.
4. `HasInitialSegments`, `schreierGeneratorSet`, and
   `schreierGeneratorSet_isFreeGroupBasis` in Propositions `1-3-22` and `1-3-7` are the existing
   chapter owners for the Schreier prefix condition and the free-basis conclusion attached to a
   transversal.

Primitive vs. derived:
- primitive public data: only `H`, `T`, and the source-facing minimality predicate;
- derived API: the Schreier initial-segment condition, the canonical subgroup identity
  `Subgroup.closure (schreierGeneratorSet ...) = H`, the induced free-basis statement, and the
  `N`-reduced conclusion.
-/

section

variable {X : Type u} [DecidableEq X]
variable {H : Subgroup (FreeGroup X)}

namespace Subgroup.RightTransversal

/-- A minimal Schreier transversal is a right transversal whose chosen representative in each
right coset has minimal reduced-word length within that coset. -/
def IsMinimalSchreier (T : H.RightTransversal) : Prop :=
  ∀ ⦃t w : FreeGroup X⦄, t ∈ (T : Set (FreeGroup X)) → rightRel H t w → norm t ≤ norm w

/-- A minimal Schreier transversal is closed under taking initial segments of reduced words. -/
-- Layer triage:
-- `source-facing`: the textbook Schreier-prefix property for a minimal transversal.
-- `core/canonical`: `HasInitialSegments` is the chapter owner predicate for closure under
-- initial segments, while `rightRel H` is the owner same-coset relation from mathlib.
-- `bridge/view`: this theorem converts the owner minimality predicate `T.IsMinimalSchreier` to
-- the chapter Schreier-transversal predicate `HasInitialSegments (T : Set (FreeGroup X))`.
-- Proof sketch: if `t ∈ T`, every initial segment of the reduced word for `t` lies in the same
-- right coset as a shorter representative. Minimality forces that shorter representative itself to
-- be the initial segment, so the initial segment remains in `T`.
theorem hasInitialSegments {T : H.RightTransversal} (hT : T.IsMinimalSchreier) :
    HasInitialSegments (T : Set (FreeGroup X)) := sorry

end Subgroup.RightTransversal

end

section

variable {X : Type u}
variable {H : Subgroup (FreeGroup X)}

namespace Subgroup.RightTransversal

/-- The nontrivial Schreier generators attached to a right transversal generate the subgroup whose
cosets the transversal represents. -/
-- Layer triage:
-- `source-facing`: the textbook subgroup `Gp({γ(tx) ≠ 1})`.
-- `core/canonical`: `Subgroup.closure`, `H.RightTransversal`, and mathlib's owner theorem
-- `Subgroup.closure_mul_image_eq_top`.
-- `bridge/view`: `schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun` is the chapter's
-- source-facing presentation of the owner-side Schreier generating family.
-- Proof sketch: `Set.range FreeGroup.of` generates the ambient free group, so the owner theorem
-- `Subgroup.closure_mul_image_eq_top` applied to the transversal `T` shows that the subgroup of
-- `H` generated by the canonical elements `w * \bar w⁻¹` is all of `H`. Removing the trivial
-- generator `1` does not change the closure, yielding the displayed equality in the ambient free
-- group.
theorem closure_schreierGeneratorSet_eq {T : H.RightTransversal} :
    Subgroup.closure (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun) = H := sorry

end Subgroup.RightTransversal

end

section

variable {X : Type u} [DecidableEq X]
variable {H : Subgroup (FreeGroup X)}

-- Layer triage:
-- `source-facing`: the subgroup `H` together with the textbook Schreier generators `γ(tx)`.
-- `core/canonical`: Proposition `1-3-7` already owns the free-basis statement for the subgroup
-- generated by a Schreier transversal with initial segments.
-- `bridge/view`: this theorem specializes that owner basis theorem to the ambient subgroup `H`
-- by using the owner minimality predicate `T.IsMinimalSchreier` to obtain `HasInitialSegments`
-- and the owner-level subgroup identity `T.closure_schreierGeneratorSet_eq`.
-- Proof sketch: minimality gives the initial-segment property, so Proposition `1-3-7` supplies a
-- free basis of the subgroup generated by the Schreier generators. The canonical bridge
-- `T.closure_schreierGeneratorSet_eq` then identifies that generated subgroup with `H`.
namespace Subgroup.RightTransversal

/-- The nontrivial Schreier generators coming from a minimal Schreier transversal form a free basis
of the subgroup `H`. -/
theorem schreierGeneratorSet_isFreeGroupBasis {T : H.RightTransversal} (hT : T.IsMinimalSchreier) :
    IsFreeGroupBasis
      { y : H | (y : FreeGroup X) ∈ schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun } :=
  sorry

/-- Proposition 1-3-20: for a subgroup `H` of the free group on `X`, if `T` is a minimal
Schreier transversal for `H`, then the nontrivial Schreier generators `γ(tx)` form an
`N`-reduced set. Together with the companion basis theorem above, this is the textbook statement
that they form an `N`-reduced basis of `H`. -/
-- Layer triage:
-- `source-facing`: the textbook `N`-reducedness condition for the Schreier generators of a
-- minimal Schreier transversal.
-- `core/canonical`: `FreeGroup.IsNReduced` is the owner predicate for Nielsen reducedness.
-- `bridge/view`: the generators are still the chapter owner set
-- `schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun` attached to the right
-- transversal `T`.
-- Proof sketch: apply Nielsen's cancellation criteria to products of the generators
-- `γ(tx) = t * of x * \overline{tx}⁻¹`. Minimality controls how much cancellation can occur in
-- adjacent products, forcing the middle letter to survive in triple products and yielding the
-- inequalities `(N1)` and `(N2)`.
theorem schreierGeneratorSet_isNReduced {T : H.RightTransversal} (hT : T.IsMinimalSchreier) :
    FreeGroup.IsNReduced (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun) := sorry

end Subgroup.RightTransversal

end

/-! ### Proposition_1_3_21 (from Items/Chap01) -/
universe u

open FreeGroup
open QuotientGroup

section

variable {X : Type u} [DecidableEq X]
variable (H : Subgroup (FreeGroup X))
variable {r : FreeGroup X → FreeGroup X → Prop} [Std.Trichotomous r]
variable (T : H.RightTransversal)
variable
  (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
  (hmin :
    ∀ ⦃t w : FreeGroup X⦄,
      t ∈ (T : Set (FreeGroup X)) →
      rightRel H t w →
      ¬ r w t)

/-- Proposition 1-3-21: a right transversal of a subgroup of a free group whose chosen
representative in each right coset is minimal for a trichotomous relation compatible with word
length is a minimal Schreier transversal in the sense of Proposition `1-3-20`, hence in
particular a Schreier transversal. For the textbook well-order criterion, the well-foundedness
part is redundant in this implication. -/
-- Layer triage:
-- `source-facing`: a minimal right transversal `T` for the subgroup `H`.
-- `core/canonical`: `H.RightTransversal`, `FreeGroup.norm`, and `QuotientGroup.rightRel H`.
-- `bridge/view`: the minimal-comparison hypotheses furnish the owner predicate
-- `Subgroup.RightTransversal.IsMinimalSchreier T`, and Proposition `1-3-20` then supplies the Schreier
-- initial-segment conclusion.
-- Domain sampling:
-- 1. `Subgroup.RightTransversal` in mathlib is the owner abstraction for chosen right-coset
--    representatives.
-- 2. `QuotientGroup.rightRel H` is the canonical relation expressing that two elements lie in the
--    same right coset of `H`.
-- 3. `HasInitialSegments` in Proposition `1-3-22` is the chapter owner predicate for the
--    Schreier initial-segment condition.
-- 4. `Subgroup.RightTransversal.IsMinimalSchreier` and
--    `Subgroup.RightTransversal.hasInitialSegments` in Proposition `1-3-20` are the
--    canonical project-level owner declarations for this textbook notion and its consequence.
-- Proof sketch: let `t ∈ T` and let `w` lie in the same right coset. If `w = t` there is nothing
-- to show. Otherwise trichotomy compares `w` and `t`; the hypothesis `hmin`
-- rules out `r w t`, so one must have `r t w`. The length-compatibility hypothesis then yields
-- `norm t ≤ norm w`, which is exactly `Subgroup.RightTransversal.IsMinimalSchreier T`.
-- Proposition `1-3-20`
-- converts that owner statement to the initial-segment formulation.
theorem minimal_rightTransversal_isMinimalSchreier
    (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
    (hmin :
      ∀ ⦃t w : FreeGroup X⦄,
        t ∈ (T : Set (FreeGroup X)) →
        rightRel H t w →
        ¬ r w t) :
    Subgroup.RightTransversal.IsMinimalSchreier T := by
  intro t w ht hw
  rcases trichotomous_of r t w with htw | rfl | hwt
  · exact h_length htw
  · exact le_rfl
  · exact (hmin ht hw hwt).elim

/-- Proposition 1-3-21 in Schreier-transversal form: the minimal-comparison criterion above
implies that the underlying set of representatives is closed under taking initial segments. -/
theorem minimal_rightTransversal_hasInitialSegments
    (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
    (hmin :
      ∀ ⦃t w : FreeGroup X⦄,
        t ∈ (T : Set (FreeGroup X)) →
        rightRel H t w →
        ¬ r w t) :
    HasInitialSegments (T : Set (FreeGroup X)) :=
  Subgroup.RightTransversal.hasInitialSegments <|
    minimal_rightTransversal_isMinimalSchreier H T h_length hmin

end

/-! ### Proposition_1_3_22 (from Items/Chap01) -/
universe u

open FreeGroup
open Subgroup
open scoped Pointwise Symmetrization

section

variable {X : Type u} [DecidableEq X]

/-- The set `T₁` of half-length initial segments of elements of `U^{±1}`. -/
def initialHalfSegmentSet (U : Set (FreeGroup X)) : Set (FreeGroup X) :=
  { a | ∃ u ∈ U^{±1}, ∃ n : ℕ, n ≤ norm u / 2 ∧ a = FreeGroup.mk (u.toWord.take n) }

/-- A collection of reduced words is Schreier-like when it is closed under taking initial
segments. -/
def HasInitialSegments (T : Set (FreeGroup X)) : Prop :=
  ∀ ⦃t : FreeGroup X⦄, t ∈ T → ∀ n : ℕ, FreeGroup.mk (t.toWord.take n) ∈ T

/-- A balanced element of `U` contributes the first half of its reduced word. -/
private def balancedPrefixPart (u : FreeGroup X) : FreeGroup X :=
  FreeGroup.mk (u.toWord.take (norm u / 2))

/-- A balanced element of `U` contributes the first half of the reduced word of its inverse,
corresponding to the second half `b` in a decomposition `u = a * b⁻¹`. -/
private def balancedSuffixPart (u : FreeGroup X) : FreeGroup X :=
  FreeGroup.mk ((u⁻¹).toWord.take (norm u / 2))

/-- An isolated word is a half-word that occurs for exactly one balanced element of `U`, as one of
the two halves in the decomposition `u = a * b⁻¹`. -/
def IsolatedBalancedPart (U : Set (FreeGroup X)) (a : FreeGroup X) : Prop :=
  ∃! u : FreeGroup X,
    u ∈ U ∧ Even (norm u) ∧
      (a = balancedPrefixPart u ∨ a = balancedSuffixPart u)

/-- Choosing isolated parts means selecting, for each balanced basis element of `U` that has an
isolated half, exactly one such isolated half to delete from `T₁`. -/
def IsolatedPartSelection (U S : Set (FreeGroup X)) : Prop :=
  S ⊆ initialHalfSegmentSet U ∩ { a | IsolatedBalancedPart U a } ∧
    ∀ ⦃u : FreeGroup X⦄, u ∈ U → Even (norm u) →
      (IsolatedBalancedPart U (balancedPrefixPart u) ∨
        IsolatedBalancedPart U (balancedSuffixPart u)) →
        ((balancedPrefixPart u ∈ S ∧ balancedSuffixPart u ∉ S) ∨
          (balancedSuffixPart u ∈ S ∧ balancedPrefixPart u ∉ S))

/-- The transversal `T` obtained from `T₁` by deleting the chosen isolated parts. -/
def prunedInitialHalfSegmentSet (U S : Set (FreeGroup X)) : Set (FreeGroup X) :=
  initialHalfSegmentSet U \ S

/-- Membership in `T₁` means being a reduced-word prefix of some element of `U^{±1}` of length at
most half the reduced length of that element. -/
theorem mem_initialHalfSegmentSet_iff {U : Set (FreeGroup X)} {a : FreeGroup X} :
    a ∈ initialHalfSegmentSet U ↔
      ∃ u ∈ U^{±1}, ∃ n : ℕ, n ≤ norm u / 2 ∧ a = FreeGroup.mk (u.toWord.take n) := Iff.rfl

/-- Proposition 1-3-22: if `U` is an `N`-reduced basis of a subgroup `H` of the free group on
`X`, and `S` chooses one isolated half from each balanced basis element as in the textbook
construction, then the resulting set `T = T₁ \ S` underlies a Schreier right transversal for some
subgroup `G` containing `H` as a free factor. -/
-- Layer triage:
-- `source-facing`: the concrete sets `T₁` and `T = T₁ \ S` built from the reduced words in `U`.
-- `core/canonical`: `FreeGroup.IsNReduced`, `IsFreeGroupBasis` on the subgroup carrier `H`,
-- `Subgroup.RightTransversal` for the right-transversal owner, and `Subgroup.IsFreeFactorOf`.
-- `bridge/view`: the source-level set `T₁ \ S` is identified with the underlying set of the
-- canonical right transversal for `G`, and the Schreier condition is recorded by
-- `HasInitialSegments`.
-- Proof sketch: the basis hypothesis is imposed on `U` as a subset of `H`, so every element of
-- `U` lies in `H`. One then checks that deleting one isolated half from each balanced basis
-- element preserves the initial-segment closure needed for a Schreier transversal. The subgroup
-- generated by the resulting Schreier generators contains `H`, and the Hall-Schreier argument
-- shows that `H` splits off as a free factor of that overgroup.
theorem pruned_initial_half_segment_set_is_schreier_transversal_with_free_factor
    (H : Subgroup (FreeGroup X)) (U S : Set (FreeGroup X))
    (hU : U ⊆ H)
    (hBasis : IsFreeGroupBasis {x : H | (x : FreeGroup X) ∈ U})
    (hNReduced : FreeGroup.IsNReduced U)
    (hSelection : IsolatedPartSelection U S) :
    ∃ G : Subgroup (FreeGroup X),
      H.IsFreeFactorOf G ∧
        ∃ T : G.RightTransversal,
          (T : Set (FreeGroup X)) = prunedInitialHalfSegmentSet U S ∧
            HasInitialSegments (T : Set (FreeGroup X)) := sorry

end

section

variable {X : Type u}

/-- The Schreier generator `γ(tx) = t * x * \overline{tx}^{-1}` attached to a transversal element
`t` and a basis letter `x`. -/
def schreierGenerator {T : Set (FreeGroup X)} (rep : FreeGroup X → T) (t : T) (x : X) :
    FreeGroup X :=
  (t : FreeGroup X) * FreeGroup.of x * (rep ((t : FreeGroup X) * FreeGroup.of x) : FreeGroup X)⁻¹

/-- The nontrivial Schreier generators attached to a transversal representative map `rep`. -/
def schreierGeneratorSet (T : Set (FreeGroup X)) (rep : FreeGroup X → T) : Set (FreeGroup X) :=
  Set.range (fun p : T × X ↦ schreierGenerator rep p.1 p.2) \ {1}

/-- Membership in the Schreier generator set means being a nontrivial Schreier generator coming
from some transversal element `t` and basis letter `x`. -/
theorem mem_schreierGeneratorSet_iff {T : Set (FreeGroup X)} {rep : FreeGroup X → T}
    {y : FreeGroup X} :
    y ∈ schreierGeneratorSet T rep ↔
      ∃ t : T, ∃ x : X, y = schreierGenerator rep t x ∧ y ≠ 1 := by
  constructor
  · rintro ⟨hy, hy1⟩
    rcases hy with ⟨⟨t, x⟩, rfl⟩
    exact ⟨t, x, rfl, by simpa [Set.mem_singleton_iff] using hy1⟩
  · rintro ⟨t, x, rfl, hy⟩
    exact ⟨⟨⟨t, x⟩, rfl⟩, by simpa [Set.mem_singleton_iff] using hy⟩

end
