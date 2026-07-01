import stacks_project.Chap10.Definition_10_84_1
import stacks_project.Chap10.Lemma_10_84_2

-- Declarations for this item will be appended below by the statement pipeline.

open Order
open scoped Ordinal DirectSum

universe u v w x y

namespace Submodule

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.84.3: the image of a countably generated submodule under a linear map is
again countably generated. -/
lemma countablyGenerated_map (f : M →ₗ[R] P) {Q : Submodule R M}
    (hQ : Q.CountablyGenerated) :
    (Q.map f).CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := Q)).mp hQ with ⟨s, hs, hspan⟩
  -- Push the chosen countable spanning set through the linear map.
  refine (Submodule.countablyGenerated_iff (P := Q.map f)).2 ?_
  refine ⟨f '' s, hs.image f, ?_⟩
  calc
    Submodule.span R (f '' s) = (Submodule.span R s).map f := by
      rw [Submodule.map_span]
    _ = Q.map f := by
      rw [hspan]

/-- Helper for Lemma 10.84.3: a countably generated ambient submodule is countably generated as a
module in its own right. -/
lemma moduleCountablyGenerated_of_countablyGenerated {Q : Submodule R M}
    (hQ : Q.CountablyGenerated) :
    Module.CountablyGenerated R Q := by
  rcases (Submodule.countablyGenerated_iff (P := Q)).mp hQ with ⟨s, hs, hspan⟩
  have hsQ : s ⊆ Q := by
    intro x hx
    rw [← hspan]
    exact Submodule.subset_span hx
  let t : Set Q := Q.subtype ⁻¹' s
  have ht : t.Countable := hs.preimage Q.subtype_injective
  have hmap :
      (Submodule.span R t).map Q.subtype = Q := by
    calc
      (Submodule.span R t).map Q.subtype = Submodule.span R (Q.subtype '' t) := by
        rw [Submodule.map_span]
      _ = Submodule.span R s := by
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hsQ hx⟩, hx, rfl⟩
      _ = Q := hspan
  have htop : Submodule.span R t = (⊤ : Submodule R Q) := by
    apply Submodule.map_injective_of_injective Q.subtype_injective
    rw [Submodule.map_subtype_top, hmap]
  -- Reinterpret the same generators inside the subtype module.
  exact (Module.countablyGenerated_iff (R := R) (M := Q)).2 ⟨t, ht, htop⟩

/-- Helper for Lemma 10.84.3: countable generation for a submodule agrees with countable
generation of the subtype module. -/
lemma countablyGenerated_iff_moduleCountablyGenerated {Q : Submodule R M} :
    Q.CountablyGenerated ↔ Module.CountablyGenerated R Q := by
  constructor
  · exact moduleCountablyGenerated_of_countablyGenerated
  · intro hQ
    have hmap :=
      countablyGenerated_map (f := Q.subtype) (Q := (⊤ : Submodule R Q)) hQ
    simpa [Submodule.map_subtype_top] using hmap

end

end Submodule

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.84.3: countable generation is preserved under linear equivalence. -/
lemma countablyGenerated_of_linearEquiv
    (e : P ≃ₗ[R] M) (hM : Module.CountablyGenerated R M) :
    Module.CountablyGenerated R P := by
  have hmap :
      ((⊤ : Submodule R M).map (e.symm : M →ₗ[R] P)).CountablyGenerated :=
    Submodule.countablyGenerated_map (f := (e.symm : M →ₗ[R] P))
      (Q := (⊤ : Submodule R M)) hM
  simpa [Submodule.map_top] using hmap

/-- Helper for Lemma 10.84.3: an internal family remains an internal family after transport across a
linear equivalence. -/
lemma isDirectSumOfCountablyGenerated_via_linearEquiv
    (e : P ≃ₗ[R] M) (hM : Module.IsDirectSumOfCountablyGenerated.{u, v, w} R M) :
    Module.IsDirectSumOfCountablyGenerated.{u, x, w} R P := by
  rcases (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := M)).mp hM with
    ⟨ι, summand, hindep, htop, hcount⟩
  classical
  -- Transport each summand through the inverse equivalence.
  refine ⟨ι, inferInstance, fun i ↦ (summand i).map (e.symm : M →ₗ[R] P), ?_, ?_⟩
  · exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr <| by
      constructor
      · exact LinearMap.iSupIndep_map (e.symm : M →ₗ[R] P) e.symm.injective hindep
      · calc
          iSup (fun i ↦ (summand i).map (e.symm : M →ₗ[R] P))
              = (iSup summand).map (e.symm : M →ₗ[R] P) := by
                  rw [Submodule.map_iSup]
          _ = (⊤ : Submodule R M).map (e.symm : M →ₗ[R] P) := by
                  rw [htop]
          _ = ⊤ := by
                  rw [Submodule.map_top]
                  exact LinearMap.range_eq_top.2 e.symm.surjective
  · intro i
    exact Submodule.countablyGenerated_map (f := (e.symm : M →ₗ[R] P)) (hcount i)

/-- Helper for Lemma 10.84.3: each canonical inclusion into a direct sum is injective. -/
lemma lof_injective
    {ι : Type w} [DecidableEq ι] (A : ι → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (i : ι) :
    Function.Injective (DirectSum.lof R ι A i) := by
  -- Apply the matching component projection to recover the original coordinate.
  intro x y hxy
  simpa using congrArg (DirectSum.component R ι A i) hxy

/-- Helper for Lemma 10.84.3: the canonical summands of a direct sum form an internal family. -/
lemma range_lof_isInternal
    {ι : Type w} [DecidableEq ι] (A : ι → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    DirectSum.IsInternal (fun i ↦ LinearMap.range (DirectSum.lof R ι A i)) := by
  classical
  let rangeEquiv : (i : ι) → A i ≃ₗ[R] LinearMap.range (DirectSum.lof R ι A i) :=
    fun i ↦
      LinearEquiv.ofBijective ((DirectSum.lof R ι A i).rangeRestrict) <| by
        constructor
        · -- The range-restricted inclusion is injective because `lof i` is.
          rw [LinearMap.injective_rangeRestrict_iff]
          exact Module.lof_injective (R := R) A i
        · -- Surjectivity is built into `rangeRestrict`.
          exact LinearMap.surjective_rangeRestrict (DirectSum.lof R ι A i)
  let decompose :
      DirectSum ι A →ₗ[R] ⨁ i, LinearMap.range (DirectSum.lof R ι A i) :=
    (DirectSum.congrLinearEquiv (R := R) rangeEquiv).toLinearMap
  letI :
      DirectSum.Decomposition (fun i ↦ LinearMap.range (DirectSum.lof R ι A i)) :=
    -- Route correction: instead of a bespoke dependent inverse on ranges, use the
    -- componentwise `rangeRestrict` equivalences and package the inverse data as a
    -- `DirectSum.Decomposition`.
    DirectSum.Decomposition.ofLinearMap
      (ℳ := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))
      decompose
      (by
        -- On each generator, recomposing after `decompose` returns the original `lof` term.
        apply DirectSum.linearMap_ext (R := R) (ι := ι) (M := A)
        intro i
        apply LinearMap.ext
        intro x
        ext j
        by_cases hji : j = i
        · subst hji
          simp [decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv]
        · simp [decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv])
      (by
        -- On each range generator, use surjectivity of `rangeRestrict` to reduce to a `lof` term.
        apply DirectSum.linearMap_ext
          (R := R) (ι := ι) (M := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))
        intro i
        apply LinearMap.ext
        intro x
        rcases x with ⟨x, hx⟩
        rcases hx with ⟨y, rfl⟩
        simpa [LinearMap.comp_apply, decompose, DirectSum.congrLinearEquiv_toLinearMap, rangeEquiv]
          using congrArg
            (DirectSum.lof R ι (fun j ↦ LinearMap.range (DirectSum.lof R ι A j)) i)
            (Subtype.ext (by rfl) :
              (DirectSum.lof R ι A i).rangeRestrict y =
                ⟨(DirectSum.lof R ι A i) y, by exact ⟨y, rfl⟩⟩))
  exact DirectSum.Decomposition.isInternal
    (ℳ := fun i ↦ LinearMap.range (DirectSum.lof R ι A i))

/-- Helper for Lemma 10.84.3: a direct sum of countably generated modules is a direct sum of
countably generated submodules. -/
lemma isDirectSumOfCountablyGenerated_directSum
    {ι : Type w} [DecidableEq ι] (A : ι → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (hA : ∀ i, Module.CountablyGenerated R (A i)) :
    Module.IsDirectSumOfCountablyGenerated.{u, max v w, w} R (DirectSum ι A) := by
  let hInternal := Module.range_lof_isInternal (R := R) A
  -- Use the canonical `lof` ranges as the required internal family of submodules.
  refine (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := DirectSum ι A)).2 ?_
  refine ⟨ι, fun i ↦ LinearMap.range (DirectSum.lof R ι A i),
    hInternal.submodule_iSupIndep, hInternal.submodule_iSup_eq_top, ?_⟩
  intro i
  -- Each canonical range is the image of the countably generated top submodule of `A i`.
  simpa [Submodule.map_top] using
    (Submodule.countablyGenerated_map (f := DirectSum.lof R ι A i)
      (Q := (⊤ : Submodule R (A i))) (hA i))

/-- Helper for Lemma 10.84.3: reindexing an independent family along the ordinal enumeration of a
well-order preserves independence. -/
lemma iSupIndep_enum_wellOrderingRel
    {ι : Type*} (A : ι → Submodule R M) (hindep : iSupIndep A) :
    iSupIndep (fun x : (Ordinal.type (@WellOrderingRel ι)).ToType ↦
      A (Ordinal.enum WellOrderingRel x)) := by
  -- The well-order enumeration is injective, so `iSupIndep.comp` applies directly.
  refine hindep.comp ?_
  intro x y hxy
  simpa using (Ordinal.enum_inj (r := @WellOrderingRel ι)).1 hxy

/-- Helper for Lemma 10.84.3: reindexing a family along the ordinal enumeration does not change its
supremum. -/
lemma iSup_enum_wellOrderingRel
    {ι : Type*} (A : ι → Submodule R M) :
    (⨆ x : (Ordinal.type (@WellOrderingRel ι)).ToType, A (Ordinal.enum WellOrderingRel x)) =
      iSup A := by
  let o : Ordinal := Ordinal.type (@WellOrderingRel ι)
  refine le_antisymm ?_ ?_
  · -- Every reindexed summand is one of the original summands.
    refine iSup_le fun x ↦ le_iSup_of_le (Ordinal.enum WellOrderingRel x) le_rfl
  · -- Conversely, each original summand appears at its `typein` rank.
    refine iSup_le fun i ↦ ?_
    let x : o.ToType :=
      Ordinal.ToType.mk ⟨Ordinal.typein (@WellOrderingRel ι) i, Ordinal.typein_lt_type _ i⟩
    have hx : Ordinal.enum WellOrderingRel x = i := by
      simpa [x, o] using (Ordinal.enum_typein (r := @WellOrderingRel ι) i)
    simpa [hx] using
      (le_iSup (fun x : o.ToType ↦ A (Ordinal.enum WellOrderingRel x)) x)

/-- Helper for Lemma 10.84.3: at the order type itself, the typein-prefix supremum recovers the
full reindexed supremum. -/
lemma typein_prefix_orderType_eq_iSup
    {ι : Type*} (B : (Ordinal.type (@WellOrderingRel ι)).ToType → Submodule R M) :
    (⨆ x : {x : (Ordinal.type (@WellOrderingRel ι)).ToType //
        Ordinal.typein (α := (Ordinal.type (@WellOrderingRel ι)).ToType) (· < ·) x <
          Ordinal.type (@WellOrderingRel ι)}, B x.1) = iSup B := by
  refine le_antisymm ?_ ?_
  · -- Forgetting the rank bound embeds the prefix family into the full family.
    refine iSup_le fun x ↦ le_iSup B x.1
  · -- Every index lies below the order type of the well-ordered index set.
    refine iSup_le fun x ↦ le_iSup_of_le ⟨x, Ordinal.typein_lt_self x⟩ le_rfl

/-- Helper for Lemma 10.84.3: an independent spanning family of countably generated submodules can
be well ordered into a Kaplansky direct-sum devissage. -/
lemma exists_kaplanskyDevissage_of_internal_family
    {ι : Type w} (A : ι → Submodule R M)
    (hindep : iSupIndep A) (htop : iSup A = ⊤)
    (hcount : ∀ i, (A i).CountablyGenerated) :
    ∃ D : DirectSumDevissage.{u, v, w} R M, D.IsKaplansky := by
  -- Route correction: the source proof first well-orders the summands, then proves the ambient
  -- prefix-stage identities `stage (α + 1) = stage α ⊔ newSummand` and
  -- `Disjoint (stage α) newSummand`, and only after that packages the successor quotient as the
  -- new summand.
  classical
  let o : Ordinal := Ordinal.type (@WellOrderingRel ι)
  let B : o.ToType → Submodule R M := fun x ↦ A (Ordinal.enum WellOrderingRel x)
  let prefixStage : Ordinal → Submodule R M := fun β ↦
    ⨆ x : {x : o.ToType // Ordinal.typein (α := o.ToType) (· < ·) x < β}, B x.1
  have hBindep : iSupIndep B := by
    -- Reindex the original internal family by the chosen well-order.
    simpa [B, o] using Module.iSupIndep_enum_wellOrderingRel (R := R) (M := M) A hindep
  have hBtop : iSup B = ⊤ := by
    -- The well-ordered reindexing does not change the global supremum.
    calc
      iSup B = iSup A := by
        simpa [B, o] using Module.iSup_enum_wellOrderingRel (R := R) (M := M) A
      _ = ⊤ := htop
  have hBcount : ∀ x, (B x).CountablyGenerated := by
    -- Each reindexed summand is one of the original countably generated summands.
    intro x
    simpa [B] using hcount (Ordinal.enum WellOrderingRel x)
  have hprefix_zero : prefixStage 0 = ⊥ := by
    -- No summand has rank `< 0`, so the initial stage is trivial.
    refine le_antisymm ?_ bot_le
    refine iSup_le fun x ↦ ?_
    exact False.elim (by simpa using x.2)
  have hprefix_top : prefixStage o = ⊤ := by
    -- At the order type itself, the prefix family has already seen every summand.
    calc
      prefixStage o = iSup B := by
        simpa [prefixStage, o] using
          Module.typein_prefix_orderType_eq_iSup (R := R) (M := M) B
      _ = ⊤ := hBtop
  let newSummand : Set.Iio o → Submodule R M := fun b ↦ B (Ordinal.ToType.mk b)
  -- The prefix stages increase because enlarging the rank bound only adds more summands.
  have hprefix_mono : Monotone prefixStage := by
    intro β γ hβγ
    refine iSup_le fun x ↦ ?_
    exact le_iSup_of_le ⟨x.1, lt_of_lt_of_le x.2 hβγ⟩ le_rfl
  -- Record the typein of the unique fresh summand at a successor stage.
  have htypein_new :
      ∀ b : Set.Iio o,
        Ordinal.typein (α := o.ToType) (· < ·) (Ordinal.ToType.mk b) = b.1 := by
    intro b
    simpa [Ordinal.ToType.mk, Ordinal.type_toType] using
      (Ordinal.typein_enum (α := o.ToType) (· < ·) (h := b.2))
  -- A successor stage is the previous prefix together with the unique fresh summand of that rank.
  have hprefix_succ :
      ∀ b : Set.Iio o, prefixStage (b.1 + 1) = prefixStage b.1 ⊔ newSummand b := by
    intro b
    refine le_antisymm ?_ ?_
    · refine iSup_le fun x ↦ ?_
      have hxle : Ordinal.typein (α := o.ToType) (· < ·) x.1 ≤ b.1 := by
        simpa using (lt_succ_iff.mp x.2)
      rcases le_iff_eq_or_lt.mp hxle with hxb | hxb
      · have hxeq : x.1 = Ordinal.ToType.mk b := by
          apply (Ordinal.typein_injective (r := (· < ·)))
          rw [htypein_new b]
          exact hxb
        simpa [newSummand, hxeq] using
          (le_sup_right : B (Ordinal.ToType.mk b) ≤ prefixStage b.1 ⊔ newSummand b)
      · exact le_sup_of_le_left <|
          le_iSup_of_le ⟨x.1, hxb⟩ le_rfl
    · refine sup_le (hprefix_mono <| le_succ b.1) ?_
      have hnew_lt :
          Ordinal.typein (α := o.ToType) (· < ·) (Ordinal.ToType.mk b) < b.1 + 1 := by
        rw [htypein_new b]
        simpa using (lt_succ b.1)
      exact le_iSup_of_le ⟨Ordinal.ToType.mk b, hnew_lt⟩ le_rfl
  -- Independence makes the fresh successor summand disjoint from the earlier prefix.
  have hnew_disjoint_prefix :
      ∀ b : Set.Iio o, Disjoint (newSummand b) (prefixStage b.1) := by
    intro b
    have hnot_mem :
        Ordinal.ToType.mk b ∉
          {x : o.ToType | Ordinal.typein (α := o.ToType) (· < ·) x < b.1} := by
      intro hx
      have : b.1 < b.1 := by
        simpa [htypein_new b] using hx
      exact lt_irrefl _ this
    simpa [newSummand, prefixStage, iSup_subtype] using
      (hBindep.disjoint_biSup (x := Ordinal.ToType.mk b)
        (y := {x : o.ToType | Ordinal.typein (α := o.ToType) (· < ·) x < b.1}) hnot_mem)
  -- Pull the ambient complement pair back to submodules of the successor stage.
  have hprefix_successor_complement :
      ∀ b : Set.Iio o,
        ∃ q : Submodule R (prefixStage (b.1 + 1)),
          IsCompl ((prefixStage b.1).comap (prefixStage (b.1 + 1)).subtype) q ∧
            q.map (prefixStage (b.1 + 1)).subtype = newSummand b := by
    intro b
    let p : Submodule R M := prefixStage (b.1 + 1)
    have hnew_le_p : newSummand b ≤ p := by
      rw [show p = prefixStage b.1 ⊔ newSummand b by simpa [p] using hprefix_succ b]
      exact le_sup_right
    let old : Set.Iic p := ⟨prefixStage b.1, hprefix_mono (le_succ b.1)⟩
    let new : Set.Iic p := ⟨newSummand b, hnew_le_p⟩
    have hsup : prefixStage b.1 ⊔ newSummand b = p := by
      simpa [p] using (hprefix_succ b).symm
    have hIic : IsCompl old new := by
      exact (Set.Iic.isCompl_iff).2
        ⟨(hnew_disjoint_prefix b).symm, by simpa [p, old, new] using hsup⟩
    have hpull :
        IsCompl ((p.mapIic).symm old) ((p.mapIic).symm new) := by
      exact ((p.mapIic).symm.isCompl_iff (x := old) (y := new)).1 hIic
    refine ⟨(p.mapIic).symm new, ?_, ?_⟩
    · simpa [p, old, new, Submodule.mapIic, Submodule.MapSubtype.orderIso] using hpull
    · change ((p.mapIic) ((p.mapIic).symm new) : Set.Iic p).1 = newSummand b
      simp [new]
  -- Limit stages are unions of the earlier prefix stages, exactly as in the source proof.
  have hprefix_limit :
      ∀ {α : Ordinal}, α < o + 1 → IsSuccLimit α →
        prefixStage α = ⨆ β : Set.Iio α, prefixStage β.1 := by
    intro α hα hlimit
    refine le_antisymm ?_ ?_
    · refine iSup_le fun x ↦ ?_
      have hx_lt :
          Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1 < α := by
        simpa using hlimit.succ_lt x.2
      refine le_iSup_of_le ⟨Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1, hx_lt⟩ ?_
      have hx_mem :
          Ordinal.typein (α := o.ToType) (· < ·) x.1 <
            Ordinal.typein (α := o.ToType) (· < ·) x.1 + 1 := by
        simpa using
          (lt_succ (Ordinal.typein (α := o.ToType) (· < ·) x.1))
      exact le_iSup_of_le ⟨x.1, hx_mem⟩ le_rfl
    · refine iSup_le fun β ↦ hprefix_mono (le_of_lt β.2)
  -- The successor quotients identify with the fresh summands, so they are countably generated.
  have hprefix_successor_quotient_countablyGenerated :
      ∀ b : Set.Iio o,
        Module.CountablyGenerated R
          (prefixStage (b.1 + 1) ⧸
            (prefixStage b.1).comap (prefixStage (b.1 + 1)).subtype) := by
    intro b
    rcases hprefix_successor_complement b with ⟨q, hqcompl, hqmap⟩
    have hnew_count :
        Module.CountablyGenerated R (newSummand b) := by
      exact
        (Submodule.countablyGenerated_iff_moduleCountablyGenerated
          (R := R) (M := M) (Q := newSummand b)).1 <|
          by simpa [newSummand] using hBcount (Ordinal.ToType.mk b)
    have hequiv :
        (prefixStage (b.1 + 1) ⧸
          (prefixStage b.1).comap (prefixStage (b.1 + 1)).subtype) ≃ₗ[R] newSummand b := by
      exact hqmap ▸
        (Submodule.quotientEquivOfIsCompl
          ((prefixStage b.1).comap (prefixStage (b.1 + 1)).subtype) q hqcompl ≪≫ₗ
            Submodule.equivSubtypeMap (prefixStage (b.1 + 1)) q)
    exact Module.countablyGenerated_of_linearEquiv (R := R) hequiv hnew_count
  have hlength_pos : 0 < o + 1 := by
    simpa using (Ordinal.zero_lt_succ o)
  -- The top stage already appears at index `o`, so the devissage exhausts the ambient module.
  have hiSup_stages : (⨆ α : Set.Iio (o + 1), prefixStage α.1) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hprefix_top]
    exact le_iSup_of_le ⟨o, by simpa using (lt_succ o)⟩ le_rfl
  -- Package the well-ordered prefix stages into a direct-sum devissage.
  refine ⟨{ length := o + 1
          , length_pos := hlength_pos
          , stages := ⟨prefixStage, hprefix_mono⟩
          , stage_zero := hprefix_zero
          , iSup_stages := hiSup_stages
          , stage_limit := hprefix_limit
          , stage_succ_isCompl := ?_ }, ?_⟩
  · intro α hα
    have hsucc_le : α + 1 ≤ o := by
      have hα' : α + 1 < succ o := by
        simpa using hα
      exact lt_succ_iff.mp hα'
    let b : Set.Iio o := ⟨α, (lt_succ α).trans_le hsucc_le⟩
    rcases hprefix_successor_complement b with ⟨q, hqcompl, _⟩
    refine ⟨q, ?_⟩
    simpa [b] using hqcompl
  · intro α hα
    have hsucc_le : α + 1 ≤ o := by
      have hα' : α + 1 < succ o := by
        simpa using hα
      exact lt_succ_iff.mp hα'
    let b : Set.Iio o := ⟨α, (lt_succ α).trans_le hsucc_le⟩
    simpa [b, DirectSumDevissage.predecessorStage] using
      hprefix_successor_quotient_countablyGenerated b

/-- Helper for Lemma 10.84.3: a Kaplansky direct-sum devissage reconstructs the ambient module as
a direct sum of countably generated successive quotients. -/
lemma isDirectSumOfCountablyGenerated_of_hasKaplanskyDevissage
    (D : DirectSumDevissage.{u, v, w} R M) (hD : D.IsKaplansky) :
    Module.IsDirectSumOfCountablyGenerated.{u, v, w} R M := by
  classical
  -- Route correction: the source theorem only needs the successor pieces inside `M`; we therefore
  -- shrink the successor index type to `Type w` and reuse Lemma 10.84.2's internal family.
  have hsmall : Small.{w} D.successorIndex := by
    let e :
        D.successorIndex ≃ {x : D.length.ToType // x.toOrd.1 + 1 < D.length} :=
      { toFun := fun a ↦ by
          refine ⟨Ordinal.ToType.mk
            ⟨a.1, lt_of_lt_of_le (lt_succ a.1) (le_of_lt a.2)⟩, ?_⟩
          simpa using a.2
        invFun := fun x ↦ by
          exact ⟨x.1.toOrd.1, x.2⟩
        left_inv := fun a ↦ by
          -- Converting a successor index into `D.length.ToType` and back recovers the same ordinal.
          apply Subtype.ext
          simpa using congrArg Subtype.val
            (Ordinal.ToType.mk.symm_apply_apply
              ⟨a.1, lt_of_lt_of_le (lt_succ a.1) (le_of_lt a.2)⟩)
        right_inv := fun x ↦ by
          -- Every small index is the image of the corresponding ordinal below `D.length`.
          apply Subtype.ext
          simpa using congrArg Subtype.val (Ordinal.ToType.mk.apply_symm_apply x.1) }
    exact Small.mk' e
  let ι : Type w := Shrink.{w} D.successorIndex
  let eι : D.successorIndex ≃ ι := equivShrink D.successorIndex
  let summand : ι → Submodule R M := fun i ↦ D.successorPiece (eι.symm i)
  refine (Module.isDirectSumOfCountablyGenerated_iff.{u, v, w} (R := R) (M := M)).2 ?_
  refine ⟨ι, summand, ?_, ?_, ?_⟩
  · -- Reindex the successor-piece family along the chosen small equivalence.
    exact D.iSupIndep_successorPiece.comp (fun i j hij ↦ eι.symm.injective hij)
  · -- Reindexing along an equivalence does not change the ambient supremum.
    calc
      iSup summand = iSup D.successorPiece := by
        refine le_antisymm ?_ ?_
        · refine iSup_le fun i ↦ le_iSup D.successorPiece (eι.symm i)
        · refine iSup_le fun α ↦ ?_
          simpa [summand, eι] using (le_iSup summand (eι α))
      _ = ⊤ := D.iSup_successorPiece_eq_top
  · intro i
    have hquot :
        Module.CountablyGenerated R (D.successiveQuotient (eι.symm i)) :=
      hD (eι.symm i).2
    have hpiece :
        Module.CountablyGenerated R (D.successorPiece (eι.symm i)) :=
      Module.countablyGenerated_of_linearEquiv
        (R := R)
        (D.successiveQuotient_linearEquiv_successorPiece (eι.symm i)).symm hquot
    -- The successor piece is countably generated because it is linearly equivalent to the
    -- corresponding countably generated successor quotient.
    exact
      (Submodule.countablyGenerated_iff_moduleCountablyGenerated
        (R := R) (M := M) (Q := summand i)).2 <| by
          simpa [summand] using hpiece

/- Domain triage:
* primary domain: transfinite direct-sum devissages of modules and countable generation;
* sampled owner declarations:
  `Module.CountablyGenerated`,
  `Module.IsDirectSumOfCountablyGenerated`,
  the chapter owner `DirectSumDevissage`,
  and the derived predicate `DirectSumDevissage.IsKaplansky`;
* layer: `bridge/view`, since the theorem below compares the direct-sum owner predicate with the
  direct-sum devissage owner object.
-/

-- Proof sketch: well-order the summands in an internal direct-sum decomposition and take partial
-- sums to build a direct-sum devissage whose successor quotients are exactly the chosen countably
-- generated summands. Conversely, a Kaplansky direct-sum devissage reconstructs `M` as the
-- supremum of the successive countably generated quotient pieces.
/-- Lemma 10.84.3: an `R`-module is a direct sum of countably generated modules exactly when it
admits a Kaplansky devissage. -/
theorem isDirectSumOfCountablyGenerated_iff_hasKaplanskyDevissage :
    Module.IsDirectSumOfCountablyGenerated.{u, v, w} R M ↔
      ∃ D : DirectSumDevissage.{u, v, w} R M, D.IsKaplansky := by
  constructor
  · intro hM
    rcases (Module.isDirectSumOfCountablyGenerated_iff.{u, v, w} (R := R) (M := M)).mp hM with
      ⟨ι, summand, hindep, htop, hcount⟩
    -- The forward implication is the source proof: well-order the summands and take prefix sums.
    exact Module.exists_kaplanskyDevissage_of_internal_family
      (R := R) (M := M) summand hindep htop hcount
  · rintro ⟨D, hD⟩
    -- Rebuild `M` from the successive quotients and use the Kaplansky condition on each quotient.
    exact Module.isDirectSumOfCountablyGenerated_of_hasKaplanskyDevissage
      (R := R) (M := M) D hD

end

end Module
