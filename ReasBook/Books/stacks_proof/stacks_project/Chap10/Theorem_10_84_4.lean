import stacks_proof.stacks_project.Chap10.Definition_10_84_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v x

section

variable {R : Type u} [Ring R]
variable {M P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup P] [Module R P]

namespace Submodule

/-- Helper for Theorem 10.84.4: the image of a countably generated submodule under a linear map is
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

/-- Helper for Theorem 10.84.4: a countably generated ambient submodule is countably generated as a
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
    -- The same generating set spans the subtype module after transporting along the inclusion.
    apply Submodule.map_injective_of_injective Q.subtype_injective
    rw [Submodule.map_subtype_top, hmap]
  exact (Module.countablyGenerated_iff (R := R) (M := Q)).2 ⟨t, ht, htop⟩

/-- Helper for Theorem 10.84.4: countable generation for a submodule agrees with countable
generation of the subtype module. -/
lemma countablyGenerated_iff_moduleCountablyGenerated {Q : Submodule R M} :
    Q.CountablyGenerated ↔ Module.CountablyGenerated R Q := by
  constructor
  · exact moduleCountablyGenerated_of_countablyGenerated
  · intro hQ
    have hmap :=
      countablyGenerated_map (R := R) (M := Q) (P := M) (f := Q.subtype)
        (Q := (⊤ : Submodule R Q)) hQ
    simpa [Submodule.map_subtype_top] using hmap

end Submodule

namespace Module

/-- Helper for Theorem 10.84.4: a surjective linear image of a countably generated module is again
countably generated. -/
lemma countablyGenerated_of_surjective
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f)
    (hA : Module.CountablyGenerated R A) :
    Module.CountablyGenerated R B := by
  rcases (Module.countablyGenerated_iff (R := R) (M := A)).mp hA with ⟨s, hs, hspan⟩
  -- Push the chosen countable spanning set forward along the surjection.
  refine (Module.countablyGenerated_iff (R := R) (M := B)).2 ?_
  refine ⟨f '' s, hs.image f, ?_⟩
  calc
    Submodule.span R (f '' s) = Submodule.map f (Submodule.span R s) := by
      rw [Submodule.map_span]
    _ = Submodule.map f ⊤ := by rw [hspan]
    _ = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.2 hf

/-- Helper for Theorem 10.84.4: a split inclusion exhibits the ambient module as the direct sum of
its range and the kernel of the retraction. -/
lemma range_isCompl_ker_of_split
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (hs : s.comp i = LinearMap.id) :
    IsCompl (LinearMap.range i) (LinearMap.ker s) := by
  let e : M →ₗ[R] M := i.comp s
  have he : IsIdempotentElem e := by
    -- The composite `i ∘ s` is idempotent because `s ∘ i = id`.
    change e * e = e
    ext x
    change i (s (i (s x))) = i (s x)
    have hsi : s (i (s x)) = s x := by
      simpa using congrArg (fun f : P →ₗ[R] P => f (s x)) hs
    rw [hsi]
  have hrange : LinearMap.range e = LinearMap.range i := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨s y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨i y, ?_⟩
      change i (s (i y)) = i y
      have hsi : s (i y) = y := by
        simpa using congrArg (fun f : P →ₗ[R] P => f y) hs
      rw [hsi]
  have hker : LinearMap.ker e = LinearMap.ker s := by
    ext x
    constructor
    · intro hx
      change i (s x) = 0 at hx
      have hsx : s (i (s x)) = 0 := by
        simpa using congrArg s hx
      have hsi : s (i (s x)) = s x := by
        simpa using congrArg (fun f : P →ₗ[R] P => f (s x)) hs
      rw [hsi] at hsx
      exact hsx
    · intro hx
      change i (s x) = 0
      simpa using congrArg i hx
  -- Transport the standard range/kernel complement for an idempotent endomorphism.
  simpa [hrange, hker] using LinearMap.IsIdempotentElem.isCompl (f := e) he

/-- Helper for Theorem 10.84.4: linear equivalences preserve internal direct sums of countably
generated submodules. -/
lemma isDirectSumOfCountablyGenerated_via_linearEquiv
    (e : P ≃ₗ[R] M) (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := by
  rcases (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := M)).mp hM with
    ⟨ι, summand, hindep, htop, hcount⟩
  classical
  -- Transport the chosen internal family along the linear equivalence.
  refine ⟨ι, inferInstance, fun i ↦ (summand i).map (e.symm : M →ₗ[R] P), ?_, ?_⟩
  · -- Repackage the transported family as an internal direct sum.
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr <| by
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
    rcases (Submodule.countablyGenerated_iff (P := summand i)).mp (hcount i) with
      ⟨s, hs, hspan⟩
    -- Map a countable spanning set across the equivalence.
    refine (Submodule.countablyGenerated_iff (P := (summand i).map (e.symm : M →ₗ[R] P))).2 ?_
    refine ⟨e.symm '' s, hs.image e.symm, ?_⟩
    calc
      Submodule.span R (e.symm '' s)
          = (Submodule.span R s).map (e.symm : M →ₗ[R] P) := by
              simpa using (Submodule.map_span (f := (e.symm : M →ₗ[R] P)) (s := s))
      _ = (summand i).map (e.symm : M →ₗ[R] P) := by
              rw [hspan]

/-- Helper for Theorem 10.84.4: intersecting a complementary pair with an ambient submodule
preserves disjointness. -/
lemma projection_stable_block_inf_disjoint
    {A B U : Submodule R M} (hAB : IsCompl A B) :
    Disjoint (U ⊓ A) (U ⊓ B) := by
  -- Disjointness descends along the inclusions into the original complementary pair.
  exact (hAB.disjoint.mono_left inf_le_right).mono_right inf_le_right

/-- Helper for Theorem 10.84.4: if a submodule is stable under the projection onto one summand of
an ambient complementary decomposition, then it splits as the sum of its intersections with the two
summands. -/
lemma projection_stable_block_inf_eq_sup
    {A B U : Submodule R M} (hAB : IsCompl A B)
    (hU : Submodule.map (Submodule.IsCompl.projection hAB) U ≤ U) :
    U = (U ⊓ A) ⊔ (U ⊓ B) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  -- Project `x` to the `A`-summand and use stability to keep both pieces inside `U`.
  have hxAinU : (Submodule.IsCompl.projection hAB) x ∈ U := by
    apply hU
    exact ⟨x, hx, rfl⟩
  have hxBinU : (Submodule.IsCompl.projection hAB.symm) x ∈ U := by
    rw [Submodule.IsCompl.projection_eq_self_sub_projection hAB x]
    exact U.sub_mem hx hxAinU
  have hxA : (Submodule.IsCompl.projection hAB) x ∈ U ⊓ A := by
    exact ⟨hxAinU, Submodule.IsCompl.projection_apply_mem hAB x⟩
  have hxB : (Submodule.IsCompl.projection hAB.symm) x ∈ U ⊓ B := by
    exact ⟨hxBinU, Submodule.IsCompl.projection_apply_mem hAB.symm x⟩
  -- The ambient complementary decomposition gives the required sum decomposition inside `U`.
  rw [← Submodule.IsCompl.projection_add_projection_eq_self hAB x]
  exact Submodule.add_mem_sup hxA hxB

/-- Helper for Theorem 10.84.4: the ambient successor quotient attached to an inclusion
`U ≤ V`. -/
abbrev stageQuotient (U V : Submodule R M) : Type v :=
  V ⧸ Submodule.comap V.subtype U

/-- Helper for Theorem 10.84.4: the restriction of the successor quotient to the `A`-summand. -/
abbrev restrictedStageQuotient (A U V : Submodule R M) : Type v :=
  ((V ⊓ A : Submodule R M) ⧸ Submodule.comap ((V ⊓ A : Submodule R M).subtype) (U ⊓ A))

/-- Helper for Theorem 10.84.4: the quotient built from ambient intersections with `A` agrees with
the quotient built internally in the subtype module `A`. -/
noncomputable def restrictedStageQuotient_linearEquiv_comap_predecessor
    {A U V : Submodule R M} (_hUV : U ≤ V) :
    restrictedStageQuotient (A := A) (U := U) (V := V) ≃ₗ[R]
      ((V.comap A.subtype) ⧸ Submodule.comap (V.comap A.subtype).subtype (U.comap A.subtype)) := by
  let eA : V.comap A.subtype ≃ₗ[R] (V ⊓ A : Submodule R M) :=
    (A.equivSubtypeMap (V.comap A.subtype)).trans <|
      LinearEquiv.ofEq _ _ <| by
        simpa [inf_comm] using
          (Submodule.map_comap_subtype (p := A) (p' := V))
  have hpred :
      (Submodule.comap ((V ⊓ A : Submodule R M).subtype) (U ⊓ A)).map
          (eA.symm : (V ⊓ A : Submodule R M) →ₗ[R] V.comap A.subtype) =
        Submodule.comap (V.comap A.subtype).subtype (U.comap A.subtype) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      -- The transported predecessor element has the same underlying ambient vector.
      change (((eA.symm y : V.comap A.subtype) : A) : M) ∈ U
      have hyU : ((y : (V ⊓ A : Submodule R M)) : M) ∈ U := hy.1
      simpa using hyU
    · intro hx
      refine ⟨eA x, ?_, LinearEquiv.symm_apply_apply eA x⟩
      -- Conversely, an element of the restricted predecessor quotient already lies in `U ⊓ A`.
      change (((eA x : (V ⊓ A : Submodule R M)) : M) ∈ (U ⊓ A : Submodule R M))
      refine ⟨?_, (eA x).2.2⟩
      change (((x : V.comap A.subtype) : A) : M) ∈ U at hx
      simpa using hx
  -- Transport quotient classes along the subtype equivalence between `V.comap A.subtype` and
  -- `V ⊓ A`.
  exact (Submodule.Quotient.equiv
    (Submodule.comap ((V ⊓ A : Submodule R M).subtype) (U ⊓ A))
    (Submodule.comap (V.comap A.subtype).subtype (U.comap A.subtype))
    eA.symm hpred)

/-- Helper for Theorem 10.84.4: after restricting a projection-stable ambient stage `V` to the
`A`-summand, the restricted successor quotient is a surjective linear image of the ambient
successor quotient. -/
lemma restricted_successor_quotient_surjective_of_projection_stable
    {A B U V : Submodule R M} (hAB : IsCompl A B) (_hUV : U ≤ V)
    (hU : Submodule.map (Submodule.IsCompl.projection hAB) U ≤ U)
    (hV : Submodule.map (Submodule.IsCompl.projection hAB) V ≤ V) :
    ∃ f :
      stageQuotient (U := U) (V := V) →ₗ[R]
        restrictedStageQuotient (A := A) (U := U) (V := V),
        Function.Surjective f := by
  let e : M →ₗ[R] M := Submodule.IsCompl.projection hAB
  let projVA : V →ₗ[R] ↥(V ⊓ A) :=
    LinearMap.codRestrict (V ⊓ A) (e.comp V.subtype) <| by
      intro x
      -- Projection-stability keeps the `A`-component of `x ∈ V` inside `V`.
      refine ⟨?_, Submodule.IsCompl.projection_apply_mem hAB x⟩
      exact hV ⟨x, x.2, rfl⟩
  have hprojU :
      U.comap V.subtype ≤
        ((U ⊓ A).comap (V ⊓ A).subtype).comap projVA := by
    intro x hx
    -- Elements from the predecessor stage map into the restricted predecessor stage.
    refine ⟨?_, Submodule.IsCompl.projection_apply_mem hAB x⟩
    exact hU ⟨x, hx, rfl⟩
  refine ⟨Submodule.mapQ _ _ projVA hprojU, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  refine ⟨Submodule.Quotient.mk ⟨x, x.2.1⟩, ?_⟩
  -- A representative already lying in `A` is fixed by the projection, so its quotient class lifts.
  change Submodule.Quotient.mk (projVA ⟨x, x.2.1⟩) = Submodule.Quotient.mk x
  apply congrArg Submodule.Quotient.mk
  ext
  change e x = x
  simpa [e] using Submodule.IsCompl.projection_apply_left hAB ⟨(x : M), x.2.2⟩

/-- Helper for Theorem 10.84.4: the restriction quotient inherits countable generation from the
ambient successor quotient once the stages are stable under the projection onto `A`. -/
lemma countablyGenerated_restricted_successor_quotient_of_projection_stable
    {A B U V : Submodule R M} (hAB : IsCompl A B) (hUV : U ≤ V)
    (hU : Submodule.map (Submodule.IsCompl.projection hAB) U ≤ U)
    (hV : Submodule.map (Submodule.IsCompl.projection hAB) V ≤ V)
    (hquot : Module.CountablyGenerated R (stageQuotient (U := U) (V := V))) :
    Module.CountablyGenerated R (restrictedStageQuotient (A := A) (U := U) (V := V)) := by
  -- Push countable generators through the quotient map constructed above.
  rcases restricted_successor_quotient_surjective_of_projection_stable
      (A := A) (B := B) (U := U) (V := V) hAB hUV hU hV with ⟨f, hf⟩
  exact countablyGenerated_of_surjective (f := f) hf hquot

/-- Helper for Theorem 10.84.4: a countable supremum of countably generated submodules is again
countably generated. -/
private lemma countablyGenerated_iSup_submodule_of_countable_family
    {ι : Sort*} [Countable ι] (A : ι → Submodule R M)
    (hA : ∀ i, (A i).CountablyGenerated) :
    (⨆ i, A i).CountablyGenerated := by
  classical
  let spanning : ι → Set M := fun i ↦
    Classical.choose ((Submodule.countablyGenerated_iff (P := A i)).mp (hA i))
  have hspanning_countable : ∀ i, (spanning i).Countable := by
    intro i
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A i)).mp (hA i))).1
  have hspanning_eq : ∀ i, Submodule.span R (spanning i) = A i := by
    intro i
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A i)).mp (hA i))).2
  let U : Set M := ⋃ i, spanning i
  have hU_countable : U.Countable := by
    -- A countable union of countable spanning sets is still countable.
    simpa [U] using Set.countable_iUnion hspanning_countable
  -- The supremum is spanned by the union of the chosen spanning sets.
  refine (Submodule.countablyGenerated_iff (P := ⨆ i, A i)).2 ⟨U, hU_countable, ?_⟩
  calc
    Submodule.span R U = ⨆ i, Submodule.span R (spanning i) := by
      simpa [U] using (Submodule.span_iUnion (R := R) (s := spanning))
    _ = ⨆ i, A i := by
      simp [hspanning_eq]

/-- Helper for Theorem 10.84.4: the block cut out by a set of indices in a fixed family of
submodules. -/
def block {ι : Type*} (summand : ι → Submodule R M) (J : Set ι) : Submodule R M :=
  ⨆ i : J, summand i.1

/-- Helper for Theorem 10.84.4: enlarging the index set enlarges the corresponding block. -/
lemma block_mono {ι : Type*} (summand : ι → Submodule R M) {J T : Set ι}
    (hJT : J ⊆ T) :
    block summand J ≤ block summand T := by
  -- Each summand indexed by `J` also appears in the larger block indexed by `T`.
  refine iSup_le fun i ↦ ?_
  exact le_iSup_of_le ⟨i.1, hJT i.2⟩ le_rfl

/-- Helper for Theorem 10.84.4: blocks convert unions of index sets into suprema of submodules. -/
lemma block_union_eq_sup {ι : Type*} (summand : ι → Submodule R M) (J T : Set ι) :
    block summand (J ∪ T) = block summand J ⊔ block summand T := by
  refine le_antisymm ?_ ?_
  · -- A summand indexed by the union lies in one of the two pieces.
    refine iSup_le fun i ↦ ?_
    rcases i with ⟨i, hi | hi⟩
    · exact le_sup_of_le_left <| le_iSup_of_le ⟨i, hi⟩ le_rfl
    · exact le_sup_of_le_right <| le_iSup_of_le ⟨i, hi⟩ le_rfl
  · -- Each side is contained in the block indexed by the union.
    refine sup_le ?_ ?_
    · exact block_mono (summand := summand) (J := J) (T := J ∪ T) fun _ h ↦ Or.inl h
    · exact block_mono (summand := summand) (J := T) (T := J ∪ T) fun _ h ↦ Or.inr h

/-- Helper for Theorem 10.84.4: blocks convert a countable union of index sets into a supremum of
the corresponding blocks. -/
lemma block_iUnion_nat_eq_iSup {ι : Type*} (summand : ι → Submodule R M) (S : ℕ → Set ι) :
    block summand (⋃ n, S n) = ⨆ n, block summand (S n) := by
  refine le_antisymm ?_ ?_
  · -- Any index lying in the union already appears in one specific block.
    refine iSup_le fun i ↦ ?_
    rcases Set.mem_iUnion.mp i.2 with ⟨n, hn⟩
    exact le_iSup_of_le n <| le_iSup_of_le ⟨i.1, hn⟩ le_rfl
  · -- Each block indexed by `S n` is contained in the union block.
    refine iSup_le fun n ↦ ?_
    exact block_mono (summand := summand) (J := S n) (T := ⋃ m, S m) fun i hi ↦
      Set.mem_iUnion.mpr ⟨n, hi⟩

/-- Helper for Theorem 10.84.4: blocks convert an arbitrary union of index sets into the supremum
of the corresponding blocks. -/
lemma block_iUnion_eq_iSup {ι : Type*} {κ : Sort*}
    (summand : ι → Submodule R M) (S : κ → Set ι) :
    block summand (⋃ a, S a) = ⨆ a, block summand (S a) := by
  refine le_antisymm ?_ ?_
  · -- Any index in the union already lies in one specific stage of the family.
    refine iSup_le fun i ↦ ?_
    rcases Set.mem_iUnion.mp i.2 with ⟨a, ha⟩
    exact le_iSup_of_le a <| le_iSup_of_le ⟨i.1, ha⟩ le_rfl
  · -- Each block of the family injects into the block cut out by the total union.
    refine iSup_le fun a ↦ ?_
    exact block_mono (summand := summand) (J := S a) (T := ⋃ b, S b) fun i hi ↦
      Set.mem_iUnion.mpr ⟨a, hi⟩

/-- Helper for Theorem 10.84.4: if `J ⊆ J'`, then inside the larger block the old block is a
direct summand, with complement cut out by the newly added indices. -/
lemma block_succ_isCompl_of_subset {ι : Type*}
    (summand : ι → Submodule R M) (hindep : iSupIndep summand)
    {J J' : Set ι} (hJJ' : J ⊆ J') :
    ∃ q : Submodule R (block summand J'),
      IsCompl ((block summand J).comap (block summand J').subtype) q := by
  let p : Submodule R M := block summand J'
  let old : Set.Iic p := ⟨block summand J, block_mono (summand := summand) hJJ'⟩
  let new : Set.Iic p := ⟨block summand (J' \ J), block_mono (summand := summand) fun _ hi ↦ hi.1⟩
  have hdisjoint_sets : Disjoint J (J' \ J) := by
    refine Set.disjoint_left.2 ?_
    intro i hiJ hiDiff
    exact hiDiff.2 hiJ
  have hdisjoint_blocks :
      Disjoint (block summand J) (block summand (J' \ J)) := by
    -- The original independent family stays disjoint after regrouping into old and new indices.
    simpa [block, iSup_subtype] using
      hindep.disjoint_biSup_biSup (s := J) (t := J' \ J) hdisjoint_sets
  have hunion : J ∪ (J' \ J) = J' := by
    ext i
    constructor
    · intro hi
      rcases hi with hi | hi
      · exact hJJ' hi
      · exact hi.1
    · intro hi
      by_cases hiJ : i ∈ J
      · exact Or.inl hiJ
      · exact Or.inr ⟨hi, hiJ⟩
  have hsup :
      block summand J ⊔ block summand (J' \ J) = p := by
    -- Splitting the larger index set into the old part and the new part recovers the whole stage.
    calc
      block summand J ⊔ block summand (J' \ J) =
          block summand (J ∪ (J' \ J)) := by
            symm
            exact block_union_eq_sup (summand := summand) J (J' \ J)
      _ = p := by simp [p, hunion]
  have hIic : IsCompl old new := by
    -- In the interval below `p`, disjointness plus the union equality gives a complement pair.
    exact (Set.Iic.isCompl_iff).2 ⟨hdisjoint_blocks, by simpa [p, old, new] using hsup⟩
  have hpull :
      IsCompl ((p.mapIic).symm old) ((p.mapIic).symm new) := by
    -- Pull the interval complement back to submodules of the stage.
    exact ((p.mapIic).symm.isCompl_iff (x := old) (y := new)).1 hIic
  refine ⟨(p.mapIic).symm new, ?_⟩
  simpa [p, old, new, Submodule.mapIic, Submodule.MapSubtype.orderIso] using hpull

/-- Helper for Theorem 10.84.4: if every nonzero homogeneous component of `x` lies over an index
in `J`, then `x` already belongs to the corresponding block. -/
lemma mem_block_of_support_subset {ι : Type*} [DecidableEq ι]
    (summand : ι → Submodule R M) [DirectSum.Decomposition summand]
    {J : Set ι} {x : M}
    (hx : ∀ i, (DirectSum.decompose summand x i : M) ≠ 0 → i ∈ J) :
    x ∈ block summand J := by
  classical
  -- Reconstruct `x` from its finitely many nonzero homogeneous components.
  rw [← DirectSum.sum_support_decompose summand x]
  refine Submodule.sum_mem (block summand J) ?_
  intro i hi
  have hiNe : DirectSum.decompose summand x i ≠ 0 :=
    (DFinsupp.mem_support_toFun (DirectSum.decompose summand x) i).1 hi
  have hiNe' : (DirectSum.decompose summand x i : M) ≠ 0 := by
    intro hzero
    apply hiNe
    ext
    exact hzero
  have hiJ : i ∈ J := by
    exact hx i hiNe'
  exact Submodule.mem_iSup_of_mem ⟨i, hiJ⟩ (DirectSum.decompose summand x i).2

/-- Helper for Theorem 10.84.4: the image of a countably generated submodule under a fixed
projection is supported on countably many original summands. -/
lemma countable_projection_support_of_countablyGenerated {ι : Type*} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (e : M →ₗ[R] M) {Q : Submodule R M} (hQ : Q.CountablyGenerated) :
    ∃ K : Set ι, K.Countable ∧ Submodule.map e Q ≤ block summand K := by
  classical
  letI := hInternal.chooseDecomposition
  rcases (Submodule.countablyGenerated_iff (P := Q)).mp hQ with ⟨s, hs, hspan⟩
  let K : Set ι := ⋃ x ∈ s, ((DirectSum.decompose summand (e x)).support : Set ι)
  refine ⟨K, ?_, ?_⟩
  · -- A countable spanning set contributes only a countable union of finite supports.
    simpa [K] using hs.biUnion fun x _hx ↦ Finset.countable_toSet _
  · -- It is enough to control the projected generators coming from the chosen spanning set.
    calc
      Submodule.map e Q = Submodule.span R (e '' s) := by
        rw [← hspan, Submodule.map_span]
      _ ≤ block summand K := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        -- Each projected generator is supported inside the countable union `K` by construction.
        exact mem_block_of_support_subset (R := R) (M := M) summand
          (J := K) (x := e x) fun i hi ↦
            Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, by simpa using hi⟩⟩

/-- Helper for Theorem 10.84.4: a block indexed by a countable set is countably generated. -/
lemma countablyGenerated_block_of_countable {ι : Type*} (summand : ι → Submodule R M)
    (hcount : ∀ i, (summand i).CountablyGenerated) {J : Set ι} (hJ : J.Countable) :
    (block summand J).CountablyGenerated := by
  let _ : Countable J := hJ.to_subtype
  -- Reindex the block over the countable subtype of the chosen set.
  simpa [block] using
    countablyGenerated_iSup_submodule_of_countable_family
      (R := R) (M := M) (A := fun i : J ↦ summand i.1) (fun i ↦ hcount i.1)

/-- Helper for Theorem 10.84.4: the projection of a countable block is supported on another
countable block of original summands. -/
lemma countable_projection_support_of_countable_block {ι : Type*} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    {S : Set ι} (hS : S.Countable) :
    ∃ K : Set ι, K.Countable ∧ Submodule.map e (block summand S) ≤ block summand K := by
  -- Apply the general support lemma to the countably generated block over `S`.
  exact countable_projection_support_of_countablyGenerated
    (R := R) (M := M) summand hInternal e
    (Q := block summand S)
    (countablyGenerated_block_of_countable (R := R) (M := M) summand hcount hS)

/-- Helper for Theorem 10.84.4: starting from a projection-stable ambient block `J`, adjoining a
countable set of new indices can be absorbed into a larger countable block after one projection
step. -/
lemma projection_stable_countable_closure_step {ι : Type*} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    {J S : Set ι}
    (hstable : Submodule.map e (block summand J) ≤ block summand J)
    (hS : S.Countable) :
    ∃ S' : Set ι, S ⊆ S' ∧ S'.Countable ∧
      Submodule.map e (block summand (J ∪ S)) ≤ block summand (J ∪ S') := by
  rcases countable_projection_support_of_countable_block
      (R := R) (M := M) summand hInternal hcount e (S := S) hS with ⟨K, hK, hmapK⟩
  let S' : Set ι := S ∪ K
  refine ⟨S', fun _ hi ↦ Or.inl hi, hS.union hK, ?_⟩
  -- Split the union block into the old stable part and the new countable part.
  calc
    Submodule.map e (block summand (J ∪ S))
        = Submodule.map e (block summand J ⊔ block summand S) := by
            rw [block_union_eq_sup]
    _ = Submodule.map e (block summand J) ⊔ Submodule.map e (block summand S) := by
            rw [Submodule.map_sup]
    _ ≤ block summand J ⊔ block summand K := by
            refine sup_le ?_ ?_
            · exact hstable.trans <| le_sup_of_le_left le_rfl
            · exact hmapK.trans <| le_sup_of_le_right le_rfl
    _ ≤ block summand (J ∪ (S ∪ K)) := by
            refine sup_le ?_ ?_
            · exact block_mono (summand := summand) (J := J) (T := J ∪ (S ∪ K))
                fun _ hi ↦ Or.inl hi
            · exact block_mono (summand := summand) (J := K) (T := J ∪ (S ∪ K))
                fun _ hi ↦ Or.inr (Or.inr hi)
    _ = block summand (J ∪ S') := by
            simp [S']

/-- Helper for Theorem 10.84.4: iterating the one-step closure over `ℕ` produces a countable set
of new indices whose block is stable under the projection over the fixed base block `J`. -/
lemma projection_stable_countable_closure_over {ι : Type*} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    {J S : Set ι}
    (hstable : Submodule.map e (block summand J) ≤ block summand J)
    (hS : S.Countable) :
    ∃ T : Set ι, S ⊆ T ∧ T.Countable ∧
      Submodule.map e (block summand (J ∪ T)) ≤ block summand (J ∪ T) := by
  classical
  let nextData : ∀ U : {U : Set ι // U.Countable},
      ∃ U' : Set ι, U.1 ⊆ U' ∧ U'.Countable ∧
        Submodule.map e (block summand (J ∪ U.1)) ≤ block summand (J ∪ U') :=
    fun U ↦
      projection_stable_countable_closure_step
        (R := R) (M := M) summand hInternal hcount e
        (J := J) (S := U.1) hstable U.2
  let next : {U : Set ι // U.Countable} → {U : Set ι // U.Countable} := fun U ↦
    ⟨Classical.choose (nextData U), (Classical.choose_spec (nextData U)).2.1⟩
  have next_spec (U : {U : Set ι // U.Countable}) :
      U.1 ⊆ (next U).1 ∧
        Submodule.map e (block summand (J ∪ U.1)) ≤ block summand (J ∪ (next U).1) := by
    exact ⟨(Classical.choose_spec (nextData U)).1, (Classical.choose_spec (nextData U)).2.2⟩
  let stages : ℕ → {U : Set ι // U.Countable} := fun n ↦
    Nat.rec ⟨S, hS⟩ (fun _ T ↦ next T) n
  let T : Set ι := ⋃ n, (stages n).1
  refine ⟨T, ?_, ?_, ?_⟩
  · -- The initial countable set appears at stage `0`.
    intro i hi
    exact Set.mem_iUnion.mpr ⟨0, by
      change i ∈ S
      exact hi⟩
  · -- Countably many countable stages still form a countable set of indices.
    simpa [T] using Set.countable_iUnion fun n ↦ (stages n).2
  · let U : ℕ → Set ι := fun n ↦ J ∪ (stages n).1
    have hUnionU : (⋃ n, U n) = J ∪ T := by
      ext i
      constructor
      · intro hi
        rcases Set.mem_iUnion.mp hi with ⟨n, hn⟩
        rcases hn with hj | hs
        · exact Or.inl hj
        · exact Or.inr (Set.mem_iUnion.mpr ⟨n, hs⟩)
      · intro hi
        rcases hi with hj | ht
        · exact Set.mem_iUnion.mpr ⟨0, Or.inl hj⟩
        · rcases Set.mem_iUnion.mp ht with ⟨n, hn⟩
          exact Set.mem_iUnion.mpr ⟨n, Or.inr hn⟩
    have hBlockUnion :
        block summand (J ∪ T) = ⨆ n, block summand (U n) := by
      calc
        block summand (J ∪ T) = block summand (⋃ n, U n) := by
          rw [hUnionU.symm]
        _ = ⨆ n, block summand (U n) := block_iUnion_nat_eq_iSup (summand := summand) U
    have hstep :
        ∀ n, Submodule.map e (block summand (U n)) ≤ block summand (U (n + 1)) := by
      intro n
      have hsucc : stages (n + 1) = next (stages n) := by
        change next (stages n) = next (stages n)
        rfl
      simpa [U, hsucc] using (next_spec (stages n)).2
    -- Push `e` through the countable supremum and shift the resulting successor stages back into it.
    calc
      Submodule.map e (block summand (J ∪ T))
          = Submodule.map e (⨆ n, block summand (U n)) := by
              rw [hBlockUnion]
      _ = ⨆ n, Submodule.map e (block summand (U n)) := by
              rw [Submodule.map_iSup]
      _ ≤ ⨆ n, block summand (U (n + 1)) := by
              refine iSup_le fun n ↦ ?_
              exact (hstep n).trans <| le_iSup (fun m ↦ block summand (U (m + 1))) n
      _ ≤ ⨆ n, block summand (U n) := by
              refine iSup_le fun n ↦ ?_
              exact le_iSup (fun m ↦ block summand (U m)) (n + 1)
      _ = block summand (J ∪ T) := by
              rw [hBlockUnion]

/-- Helper for Theorem 10.84.4: if `J ⊆ J'` and only countably many new indices are added, then
the quotient of the larger block by the smaller one is countably generated. -/
lemma countablyGenerated_block_quotient_of_countable_extension
    {ι : Type*} (summand : ι → Submodule R M)
    (hcount : ∀ i, (summand i).CountablyGenerated) {J J' : Set ι}
    (hJJ' : J ⊆ J') (hnew : (J' \ J).Countable) :
    Module.CountablyGenerated R
      (block summand J' ⧸ ((block summand J).comap (block summand J').subtype)) := by
  let hDiffLe : block summand (J' \ J) ≤ block summand J' :=
    block_mono (summand := summand) fun _ hi ↦ hi.1
  let hBlockLe : block summand J ≤ block summand J' :=
    block_mono (summand := summand) hJJ'
  let diffInclusion : block summand (J' \ J) →ₗ[R] block summand J' :=
    Submodule.inclusion hDiffLe
  let quotientMap :
      block summand (J' \ J) →ₗ[R]
        block summand J' ⧸ ((block summand J).comap (block summand J').subtype) :=
    (((block summand J).comap (block summand J').subtype).mkQ).comp diffInclusion
  have hunion : J ∪ (J' \ J) = J' := by
    ext i
    constructor
    · intro hi
      rcases hi with hi | hi
      · exact hJJ' hi
      · exact hi.1
    · intro hi
      by_cases hmem : i ∈ J
      · exact Or.inl hmem
      · exact Or.inr ⟨hi, hmem⟩
  have hsurj : Function.Surjective quotientMap := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((block summand J).comap (block summand J').subtype) y
    have hxsplit : x.1 ∈ block summand J ⊔ block summand (J' \ J) := by
      -- Split a representative into the old block and the newly added block.
      have hx' : x.1 ∈ block summand (J ∪ (J' \ J)) := by
        simpa [hunion] using x.2
      rw [block_union_eq_sup (summand := summand) J (J' \ J)] at hx'
      exact hx'
    rcases Submodule.mem_sup.mp hxsplit with ⟨u, huJ, v, hvDiff, huv⟩
    refine ⟨⟨v, hvDiff⟩, ?_⟩
    -- The old-block component dies in the quotient, so the class is represented by `v`.
    change Submodule.Quotient.mk (diffInclusion ⟨v, hvDiff⟩) = Submodule.Quotient.mk x
    rw [Submodule.inclusion_apply]
    symm
    apply (Submodule.Quotient.eq _).2
    change x - (⟨v, hDiffLe hvDiff⟩ : block summand J') ∈
      ((block summand J).comap (block summand J').subtype)
    change x.1 - v ∈ block summand J
    have hxv : x.1 - v = u := by
      rw [← huv, add_sub_cancel_right]
    simpa [hxv] using huJ
  have hdomainSub :
      (block summand (J' \ J)).CountablyGenerated :=
    countablyGenerated_block_of_countable (R := R) (M := M) summand hcount hnew
  have hdomain :
      Module.CountablyGenerated R (block summand (J' \ J)) :=
    (Submodule.countablyGenerated_iff_moduleCountablyGenerated
      (R := R) (M := M) (Q := block summand (J' \ J))).mp hdomainSub
  -- The quotient is a surjective image of the countably generated new block.
  exact countablyGenerated_of_surjective (f := quotientMap) hsurj hdomain

/-- Helper for Theorem 10.84.4: an ambient complement on a projection-stable successor stage
restricts to a complement on the `A`-part of that stage. -/
lemma restricted_stage_isCompl_of_projection_stable_extension
    {A B U V : Submodule R M} (hAB : IsCompl A B) (_hUV : U ≤ V)
    (hU : Submodule.map (Submodule.IsCompl.projection hAB) U ≤ U)
    (hV : Submodule.map (Submodule.IsCompl.projection hAB) V ≤ V)
    {q : Submodule R V} (hq : IsCompl (U.comap V.subtype) q) :
    ∃ qA : Submodule R (V.comap A.subtype),
      IsCompl (Submodule.comap (V.comap A.subtype).subtype (U.comap A.subtype)) qA := by
  let projA : M →ₗ[R] A := Submodule.linearProjOfIsCompl A B hAB
  let inclVA : V.comap A.subtype →ₗ[R] V :=
    LinearMap.codRestrict V (A.subtype.comp (V.comap A.subtype).subtype) fun x ↦ x.2
  let projU : V →ₗ[R] V := Submodule.IsCompl.projection hq
  let VAproj : V →ₗ[R] V.comap A.subtype :=
    LinearMap.codRestrict (V.comap A.subtype) (projA.comp V.subtype) fun x ↦ by
      change ((projA x : A) : M) ∈ V
      exact hV ⟨x, x.2, rfl⟩
  let pA : Submodule R (V.comap A.subtype) :=
    Submodule.comap (V.comap A.subtype).subtype (U.comap A.subtype)
  let retr : V.comap A.subtype →ₗ[R] pA :=
    LinearMap.codRestrict pA ((VAproj.comp projU).comp inclVA) fun x ↦ by
      change ((((VAproj.comp projU).comp inclVA) x : V.comap A.subtype) : A) ∈ U.comap A.subtype
      change ((projA (((projU (inclVA x)) : V) : M) : A) : M) ∈ U
      exact hU ⟨projU (inclVA x), Submodule.IsCompl.projection_apply_mem hq (inclVA x), rfl⟩
  refine ⟨LinearMap.ker retr, ?_⟩
  -- Restrict the ambient successor retraction to `A`; on the predecessor stage it is the identity.
  exact LinearMap.isCompl_of_proj <| by
    intro x
    apply Subtype.ext
    ext
    change ((projA (((projU (inclVA x)) : V) : M) : A) : M) =
      ((((x : pA) : V.comap A.subtype) : A) : M)
    have hxU : (inclVA x : V) ∈ U.comap V.subtype := by
      change ((((x : pA) : V.comap A.subtype) : A) : M) ∈ U
      exact x.2
    have hprojU :
        projU (inclVA x) = inclVA x := by
      simpa [projU] using Submodule.IsCompl.projection_apply_left hq ⟨inclVA x, hxU⟩
    rw [hprojU]
    simpa [projA, inclVA] using congrArg (fun y : A ↦ ((y : A) : M))
      (Submodule.linearProjOfIsCompl_apply_left hAB
        ⟨(((x : pA) : V.comap A.subtype) : A), ((x : pA) : V.comap A.subtype).2⟩)

/-- Helper for Theorem 10.84.4: the small well-ordered stage index used for the ambient
projection-stable recursion over the original summand order. -/
abbrev WellOrderedStageIndex (ι : Type x) :=
  WithTop ((Ordinal.type (@WellOrderingRel ι)).ToType)

/-- Helper for Theorem 10.84.4: the empty block is stable under every endomorphism. -/
private lemma projection_stable_empty_block {ι : Type x}
    (summand : ι → Submodule R M) (e : M →ₗ[R] M) :
    Submodule.map e (block (summand := summand) (∅ : Set ι)) ≤
      block (summand := summand) (∅ : Set ι) := by
  -- The block over the empty set is trivial, so its image stays trivial.
  simp [block]

/-- Helper for Theorem 10.84.4: a union of projection-stable blocks is again projection-stable. -/
private lemma projection_stable_block_iUnion_stable {ι : Type x} {κ : Sort*}
    (summand : ι → Submodule R M) (e : M →ₗ[R] M) (S : κ → Set ι)
    (hS : ∀ a, Submodule.map e (block summand (S a)) ≤ block summand (S a)) :
    Submodule.map e (block (summand := summand) (⋃ a, S a)) ≤
      block (summand := summand) (⋃ a, S a) := by
  -- Rewrite the union block as a supremum and apply stability on each stage.
  rw [block_iUnion_eq_iSup, Submodule.map_iSup]
  refine iSup_le fun a ↦ ?_
  exact (hS a).trans <| le_iSup (fun b ↦ block summand (S b)) a

/-- Helper for Theorem 10.84.4: one successor step in the ambient projection-stable stage
construction. -/
noncomputable def projection_stable_stageSetSucc {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType)
    (J : {J : Set ι // Submodule.map e (block summand J) ≤ block summand J}) :
    {J' : Set ι // Submodule.map e (block summand J') ≤ block summand J'} :=
  let hclosure :=
    projection_stable_countable_closure_over
      (R := R) (M := M) summand hInternal hcount e
      (J := J.1) (S := {Ordinal.enum WellOrderingRel x}) J.2
      (Set.countable_singleton _)
  let T := Classical.choose hclosure
  let hT := Classical.choose_spec hclosure
  ⟨J.1 ∪ T, hT.2.2⟩

/-- Helper for Theorem 10.84.4: the chosen successor closure contains the new summand index and
adds only countably many fresh indices. -/
lemma projection_stable_stageSetSucc_spec {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType)
    (J : {J : Set ι // Submodule.map e (block summand J) ≤ block summand J}) :
    {Ordinal.enum WellOrderingRel x} ⊆
        (projection_stable_stageSetSucc (R := R) (M := M) summand hInternal hcount e x J).1 ∧
      (((projection_stable_stageSetSucc (R := R) (M := M) summand hInternal hcount e x J).1 \ J.1)
        : Set ι).Countable := by
  -- Unfold the chosen closure step and read off the seed-containment/countability conclusions.
  dsimp [projection_stable_stageSetSucc]
  let hclosure :=
    projection_stable_countable_closure_over
      (R := R) (M := M) summand hInternal hcount e
      (J := J.1) (S := {Ordinal.enum WellOrderingRel x}) J.2
      (Set.countable_singleton _)
  let hchoose := Classical.choose_spec hclosure
  constructor
  · intro i hi
    exact Or.inr (hchoose.1 hi)
  · refine (hchoose.2.1).mono ?_
    intro i hi
    rcases hi.1 with hiJ | hiT
    · exact False.elim (hi.2 hiJ)
    · exact hiT

/-- Helper for Theorem 10.84.4: a limit stage is the union of all earlier projection-stable
ambient stages. -/
noncomputable def projection_stable_stageSetLimit {ι : Type x} {κ : Sort*}
    (summand : ι → Submodule R M) (e : M →ₗ[R] M)
    (S : κ → {J : Set ι // Submodule.map e (block summand J) ≤ block summand J}) :
    {J : Set ι // Submodule.map e (block summand J) ≤ block summand J} :=
  ⟨⋃ a, (S a).1,
    projection_stable_block_iUnion_stable (R := R) (M := M) summand e
      (fun a ↦ (S a).1) fun a ↦ (S a).2⟩

/-- Helper for Theorem 10.84.4: recursively choose the projection-stable ambient block attached to
each point of the well-ordered index type. -/
noncomputable def projection_stable_stageSet {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M) :
    (Ordinal.type (@WellOrderingRel ι)).ToType →
      {J : Set ι // Submodule.map e (block summand J) ≤ block summand J} :=
  WellFoundedLT.fix
    (motive := fun _ : (Ordinal.type (@WellOrderingRel ι)).ToType ↦
      {J : Set ι // Submodule.map e (block summand J) ≤ block summand J})
    fun x IH ↦
      let Jprev :=
        projection_stable_stageSetLimit (R := R) (M := M) summand e
          (fun y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x} ↦ IH y.1 y.2)
      projection_stable_stageSetSucc (R := R) (M := M) summand hInternal hcount e x Jprev

/-- Helper for Theorem 10.84.4: the recursively chosen stage at `x` is obtained by taking the
projection-stable predecessor union and then applying one successor closure step. -/
lemma projection_stable_stageSet_eq {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x =
      projection_stable_stageSetSucc (R := R) (M := M) summand hInternal hcount e x
        (projection_stable_stageSetLimit (R := R) (M := M) summand e
          (fun y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x} ↦
            projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1)) := by
  -- Unfold the well-founded recursion once and expose the predecessor-union stage.
  unfold projection_stable_stageSet
  rw [WellFoundedLT.fix_eq]

/-- Helper for Theorem 10.84.4: the union of the earlier recursively chosen stages sits inside the
current stage. -/
lemma projection_stable_stageSet_pred_subset {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    (⋃ y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x},
        (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1).1) ⊆
      (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1 := by
  -- Rewrite the current stage using the recursive equation and keep only the predecessor union.
  rw [projection_stable_stageSet_eq (R := R) (M := M) summand hInternal hcount e x]
  intro i hi
  dsimp [projection_stable_stageSetSucc]
  exact Or.inl hi

/-- Helper for Theorem 10.84.4: the ambient stage family is monotone along the chosen well-order. -/
lemma projection_stable_stageSet_mono {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    {x y : (Ordinal.type (@WellOrderingRel ι)).ToType} (hyx : y < x) :
    (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y).1 ⊆
      (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1 := by
  -- Insert the earlier stage into the predecessor union at `x`.
  intro i hi
  exact projection_stable_stageSet_pred_subset
    (R := R) (M := M) summand hInternal hcount e x <|
      Set.mem_iUnion.mpr ⟨⟨y, hyx⟩, hi⟩

/-- Helper for Theorem 10.84.4: the predecessor union used at stage `x` is itself projection
stable. -/
lemma projection_stable_stageSet_pred_stable {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    Submodule.map e
        (block summand
          (⋃ y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x},
            (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1).1)) ≤
      block summand
        (⋃ y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x},
          (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1).1) := by
  -- The predecessor stage is exactly the limit union stage used in the recursion.
  exact
    (projection_stable_stageSetLimit (R := R) (M := M) summand e
      (fun y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x} ↦
        projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1)).2

/-- Helper for Theorem 10.84.4: each recursively chosen stage remains stable under the projection
endomorphism. -/
lemma projection_stable_stageSet_stable {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    Submodule.map e
        (block summand
          (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1) ≤
      block summand
        (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1 :=
  (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).2

/-- Helper for Theorem 10.84.4: each stage contains the original summand indexed by its seed
element. -/
lemma projection_stable_stageSet_seed_mem {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    Ordinal.enum WellOrderingRel x ∈
      (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1 := by
  -- Read off the singleton-seed inclusion from the one-step closure specification.
  rw [projection_stable_stageSet_eq (R := R) (M := M) summand hInternal hcount e x]
  exact
    (projection_stable_stageSetSucc_spec
      (R := R) (M := M) summand hInternal hcount e x
      (projection_stable_stageSetLimit (R := R) (M := M) summand e
        (fun y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x} ↦
          projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1))).1 <| by
      simp

/-- Helper for Theorem 10.84.4: the fresh indices added at each recursive stage form a countable
set. -/
lemma projection_stable_stageSet_fresh_countable {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (x : (Ordinal.type (@WellOrderingRel ι)).ToType) :
    (((projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1 \
        ⋃ y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x},
          (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1).1)
      : Set ι).Countable := by
  -- After unfolding one recursion step, this is exactly the countability assertion for the chosen
  -- successor closure.
  rw [projection_stable_stageSet_eq (R := R) (M := M) summand hInternal hcount e x]
  simpa using
    (projection_stable_stageSetSucc_spec
      (R := R) (M := M) summand hInternal hcount e x
      (projection_stable_stageSetLimit (R := R) (M := M) summand e
        (fun y : {y : (Ordinal.type (@WellOrderingRel ι)).ToType // y < x} ↦
          projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e y.1))).2

/-- Helper for Theorem 10.84.4: the recursive ambient stages eventually cover every original
summand index. -/
lemma projection_stable_stageSet_indices_cover {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M) :
    (⋃ x : (Ordinal.type (@WellOrderingRel ι)).ToType,
        (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1) =
      (Set.univ : Set ι) := by
  ext i
  constructor
  · intro _hi
    simp
  · intro _hi
    let x : (Ordinal.type (@WellOrderingRel ι)).ToType :=
      Ordinal.ToType.mk
        ⟨Ordinal.typein (@WellOrderingRel ι) i, Ordinal.typein_lt_type (@WellOrderingRel ι) i⟩
    have hx : Ordinal.enum WellOrderingRel x = i := by
      simpa [x] using (Ordinal.enum_typein (r := @WellOrderingRel ι) i)
    -- The stage indexed by the rank of `i` contains `i` by the singleton-seed property.
    exact Set.mem_iUnion.mpr ⟨x, by
      simpa [hx] using
        projection_stable_stageSet_seed_mem
          (R := R) (M := M) summand hInternal hcount e x⟩

/-- Helper for Theorem 10.84.4: the union of the recursive ambient stages spans the whole ambient
module. -/
lemma projection_stable_stageSet_cover {ι : Type x} [DecidableEq ι]
    (summand : ι → Submodule R M) (hInternal : DirectSum.IsInternal summand)
    (hcount : ∀ i, (summand i).CountablyGenerated) (e : M →ₗ[R] M)
    (htop : iSup summand = ⊤) :
    block summand
        (⋃ x : (Ordinal.type (@WellOrderingRel ι)).ToType,
          (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1) = ⊤ := by
  -- Every original summand index appears at its own well-ordered stage, so the total block is the
  -- full internal direct sum.
  calc
    block summand
        (⋃ x : (Ordinal.type (@WellOrderingRel ι)).ToType,
          (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1) =
      block summand (Set.univ : Set ι) := by
        rw [projection_stable_stageSet_indices_cover
          (R := R) (M := M) summand hInternal hcount e]
    _ = iSup summand := by
        simp [block, iSup_subtype]
    _ = ⊤ := htop

/-- Helper for Theorem 10.84.4: a complemented submodule of a direct sum of countably generated
modules is again such a direct sum. -/
theorem isDirectSumOfCountablyGenerated_of_isCompl_submodule
    (A B : Submodule R M) (hAB : IsCompl A B)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R A := by
  classical
  rcases (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := M)).mp hM with
    ⟨ι, summand, hindep, htop, hcount⟩
  have hInternal : DirectSum.IsInternal summand := by
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨hindep, htop⟩
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    letI : DecidableEq ι := Classical.decEq ι
    let e : M →ₗ[R] M := Submodule.IsCompl.projection hAB
    let o : Type x := (Ordinal.type (@WellOrderingRel ι)).ToType
    let J : o → Set ι := fun x ↦
      (projection_stable_stageSet (R := R) (M := M) summand hInternal hcount e x).1
    let Jprev : o → Set ι := fun x ↦ ⋃ y : {y : o // y < x}, J y.1
    let Vprev : o → Submodule R M := fun x ↦ block summand (Jprev x)
    let Vcur : o → Submodule R M := fun x ↦ block summand (J x)
    let Aprev : o → Submodule R A := fun x ↦ (Vprev x).comap A.subtype
    let Acur : o → Submodule R A := fun x ↦ (Vcur x).comap A.subtype
    have hJmono : ∀ {y z : o}, y ≤ z → J y ⊆ J z := by
      intro y z hyz
      rcases lt_or_eq_of_le hyz with hyz | rfl
      · exact projection_stable_stageSet_mono
          (R := R) (M := M) summand hInternal hcount e hyz
      · exact subset_rfl
    have hVmono : ∀ {y z : o}, y ≤ z → Vcur y ≤ Vcur z := by
      intro y z hyz
      exact block_mono (summand := summand) (hJmono hyz)
    have hVprev_le_Vcur : ∀ x : o, Vprev x ≤ Vcur x := by
      intro x
      exact block_mono (summand := summand) <|
        projection_stable_stageSet_pred_subset
          (R := R) (M := M) summand hInternal hcount e x
    have hAprev_le_Acur : ∀ x : o, Aprev x ≤ Acur x := by
      intro x a ha
      change ((a : A) : M) ∈ Vcur x
      exact hVprev_le_Vcur x <| by
        simpa [Aprev, Vprev] using ha
    have hAmbientCompl :
        ∀ x : o, ∃ q : Submodule R (Vcur x),
          IsCompl ((Vprev x).comap (Vcur x).subtype) q := by
      intro x
      simpa [Vprev, Vcur, Jprev, J] using
        block_succ_isCompl_of_subset
          (R := R) (M := M) (summand := summand) hindep
          (projection_stable_stageSet_pred_subset
            (R := R) (M := M) summand hInternal hcount e x)
    have hRestrictedCompl :
        ∀ x : o, ∃ qA : Submodule R (Acur x),
          IsCompl (Submodule.comap (Acur x).subtype (Aprev x)) qA := by
      intro x
      rcases hAmbientCompl x with ⟨q, hq⟩
      simpa [Aprev, Acur, Vprev, Vcur] using
        restricted_stage_isCompl_of_projection_stable_extension
          (R := R) (M := M) (A := A) (B := B)
          (U := Vprev x) (V := Vcur x) hAB (hVprev_le_Vcur x)
          (projection_stable_stageSet_pred_stable
            (R := R) (M := M) summand hInternal hcount e x)
          (projection_stable_stageSet_stable
            (R := R) (M := M) summand hInternal hcount e x)
          hq
    let pieceRaw : (x : o) → Submodule R (Acur x) := fun x ↦ Classical.choose (hRestrictedCompl x)
    let piece : o → Submodule R A := fun x ↦ (pieceRaw x).map (Acur x).subtype
    have hpieceRaw_isCompl :
        ∀ x : o, IsCompl (Submodule.comap (Acur x).subtype (Aprev x)) (pieceRaw x) := by
      intro x
      exact Classical.choose_spec (hRestrictedCompl x)
    have hpiece_le_Acur : ∀ x : o, piece x ≤ Acur x := by
      intro x a ha
      rcases Submodule.mem_map.1 ha with ⟨b, hb, rfl⟩
      exact b.2
    have hpiece_disjoint : ∀ x : o, Disjoint (Aprev x) (piece x) := by
      intro x
      have hmap :
          (Submodule.comap (Acur x).subtype (Aprev x)).map (Acur x).subtype = Aprev x := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr (hAprev_le_Acur x)
      have hdisjoint :
          Disjoint
            ((Submodule.comap (Acur x).subtype (Aprev x)).map (Acur x).subtype)
            (piece x) :=
        Submodule.disjoint_map Subtype.val_injective (hpieceRaw_isCompl x).disjoint
      simpa [piece, hmap] using hdisjoint
    have hAcur_eq_sup_piece : ∀ x : o, Acur x = Aprev x ⊔ piece x := by
      intro x
      have hmap :
          (Submodule.comap (Acur x).subtype (Aprev x)).map (Acur x).subtype = Aprev x := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr (hAprev_le_Acur x)
      have hsup :
          (Submodule.comap (Acur x).subtype (Aprev x)).map (Acur x).subtype ⊔ piece x =
            Acur x := by
        rw [← Submodule.map_sup, (hpieceRaw_isCompl x).sup_eq_top, Submodule.map_top,
          Submodule.range_subtype]
      simpa [piece, hmap] using hsup.symm
    have hAprev_eq_iSup_Acur :
        ∀ x : o, Aprev x = ⨆ y : {y : o // y < x}, Acur y.1 := by
      intro x
      refine le_antisymm ?_ ?_
      · intro a ha
        have haVprev : ((a : A) : M) ∈ Vprev x := by
          simpa [Aprev, Vprev] using ha
        have haUnion : ((a : A) : M) ∈ ⨆ y : {y : o // y < x}, Vcur y.1 := by
          simpa [Vprev, Jprev, Vcur, J, block_iUnion_eq_iSup] using haVprev
        by_cases hne : Nonempty {y : o // y < x}
        · letI : Nonempty {y : o // y < x} := hne
          have hdir :
              Directed (· ≤ ·) (fun y : {y : o // y < x} ↦ Vcur y.1) := by
            intro y z
            rcases le_total y.1 z.1 with hyz | hzy
            · exact ⟨z, hVmono hyz, le_rfl⟩
            · exact ⟨y, le_rfl, hVmono hzy⟩
          rcases (Submodule.mem_iSup_of_directed _ hdir).mp haUnion with ⟨y, hy⟩
          exact Submodule.mem_iSup_of_mem y <| by
            simpa [Acur, Vcur] using hy
        · letI : IsEmpty {y : o // y < x} := not_nonempty_iff.mp hne
          have ha0 : a = 0 := by
            have hUnionBot : (⨆ y : {y : o // y < x}, Vcur y.1) = (⊥ : Submodule R M) := by
              simpa using (iSup_of_empty (fun y : {y : o // y < x} ↦ Vcur y.1))
            have haBot : ((a : A) : M) ∈ (⊥ : Submodule R M) := by
              rw [← hUnionBot]
              exact haUnion
            apply Subtype.ext
            simpa using haBot
          simpa [ha0]
      · refine iSup_le fun y ↦ ?_
        intro a ha
        change ((a : A) : M) ∈ Vprev x
        have hstage : Vcur y.1 ≤ Vprev x := by
          exact block_mono (summand := summand) fun i hi ↦ Set.mem_iUnion.mpr ⟨y, hi⟩
        exact hstage <| by
          simpa [Acur, Vcur] using ha
    have hAcur_le_iSup_piece : ∀ x : o, Acur x ≤ ⨆ y, piece y := by
      intro x
      induction x using WellFoundedLT.induction with
      | ind x IH =>
          rw [hAcur_eq_sup_piece x]
          refine sup_le ?_ (le_iSup piece x)
          rw [hAprev_eq_iSup_Acur x]
          refine iSup_le fun y ↦ ?_
          exact IH y.1 y.2
    have hpiece_count : ∀ x : o, (piece x).CountablyGenerated := by
      intro x
      have hquotAmbient :
          Module.CountablyGenerated R (stageQuotient (U := Vprev x) (V := Vcur x)) := by
        refine countablyGenerated_block_quotient_of_countable_extension
          (R := R) (M := M) summand hcount
          (projection_stable_stageSet_pred_subset
            (R := R) (M := M) summand hInternal hcount e x) ?_
        simpa [J, Jprev] using
          projection_stable_stageSet_fresh_countable
            (R := R) (M := M) summand hInternal hcount e x
      have hquotRestr :
          Module.CountablyGenerated R
            (restrictedStageQuotient (A := A) (U := Vprev x) (V := Vcur x)) := by
        exact countablyGenerated_restricted_successor_quotient_of_projection_stable
          (R := R) (M := M) (A := A) (B := B)
          (U := Vprev x) (V := Vcur x) hAB (hVprev_le_Vcur x)
          (projection_stable_stageSet_pred_stable
            (R := R) (M := M) summand hInternal hcount e x)
          (projection_stable_stageSet_stable
            (R := R) (M := M) summand hInternal hcount e x)
          hquotAmbient
      let eRestr :=
        restrictedStageQuotient_linearEquiv_comap_predecessor
          (R := R) (M := M) (A := A) (U := Vprev x) (V := Vcur x) (hVprev_le_Vcur x)
      have hquotAcur :
          Module.CountablyGenerated R
            (Acur x ⧸ Submodule.comap (Acur x).subtype (Aprev x)) := by
        exact countablyGenerated_of_surjective (f := (eRestr : _ →ₗ[R] _))
          eRestr.surjective hquotRestr
      let ePiece :=
        Submodule.quotientEquivOfIsCompl
          (Submodule.comap (Acur x).subtype (Aprev x)) (pieceRaw x) (hpieceRaw_isCompl x)
      have hrawModule : Module.CountablyGenerated R (pieceRaw x) := by
        exact countablyGenerated_of_surjective (f := (ePiece : _ →ₗ[R] _))
          ePiece.surjective hquotAcur
      have hrawCount : (pieceRaw x).CountablyGenerated := by
        exact (Submodule.countablyGenerated_iff_moduleCountablyGenerated
          (R := R) (M := Acur x) (Q := pieceRaw x)).2 hrawModule
      exact Submodule.countablyGenerated_map (R := R) (M := Acur x) (P := A)
        (f := (Acur x).subtype) hrawCount
    have hpairwise : Pairwise (fun x y ↦ Disjoint (piece x) (piece y)) := by
      intro x y hxy
      rcases lt_or_gt_of_ne hxy with hxy | hyx
      · have hle : piece x ≤ Aprev y := by
          refine (hpiece_le_Acur x).trans ?_
          rw [hAprev_eq_iSup_Acur y]
          exact le_iSup_of_le ⟨x, hxy⟩ le_rfl
        exact (hpiece_disjoint y).mono_left hle
      · have hle : piece y ≤ Aprev x := by
          refine (hpiece_le_Acur y).trans ?_
          rw [hAprev_eq_iSup_Acur x]
          exact le_iSup_of_le ⟨y, hyx⟩ le_rfl
        exact Disjoint.symm ((hpiece_disjoint x).mono_left hle)
    have ho : Nonempty o := by
      rcases hι with ⟨i⟩
      refine ⟨Ordinal.ToType.mk
        ⟨Ordinal.typein (@WellOrderingRel ι) i, Ordinal.typein_lt_type (@WellOrderingRel ι) i⟩⟩
    letI : Nonempty o := ho
    have hAllStagesTop : (⨆ x : o, Vcur x) = ⊤ := by
      calc
        (⨆ x : o, Vcur x) = block summand (⋃ x : o, J x) := by
          symm
          exact block_iUnion_eq_iSup (summand := summand) J
        _ = ⊤ := by
          dsimp [J]
          exact projection_stable_stageSet_cover
            (R := R) (M := M) summand hInternal hcount e htop
    have hpiece_top : iSup piece = ⊤ := by
      apply top_unique
      intro a _ha
      have haStage : ((a : A) : M) ∈ ⨆ x : o, Vcur x := by
        rw [hAllStagesTop]
        simp
      have hdir : Directed (· ≤ ·) Vcur := by
        intro y z
        rcases le_total y z with hyz | hzy
        · exact ⟨z, hVmono hyz, le_rfl⟩
        · exact ⟨y, le_rfl, hVmono hzy⟩
      rcases (Submodule.mem_iSup_of_directed _ hdir).mp haStage with ⟨x, hx⟩
      exact hAcur_le_iSup_piece x <| by
        simpa [Acur, Vcur] using hx
    have hindepPiece : iSupIndep piece := by
      rw [iSupIndep_iff_supIndep]
      intro s
      classical
      refine s.strongInductionOn ?_
      intro s IH
      by_cases hs : s.Nonempty
      · let m : o := s.max' hs
        have hmem : m ∈ s := Finset.max'_mem s hs
        have herase : (s.erase m).SupIndep piece := by
          exact IH (s.erase m) (Finset.erase_ssubset hmem)
        have hsup_le : (s.erase m).sup piece ≤ Aprev m := by
          refine Finset.sup_le ?_
          intro j hj
          refine (hpiece_le_Acur j).trans ?_
          rw [hAprev_eq_iSup_Acur m]
          exact le_iSup_of_le ⟨j, by
            simpa [m] using (Finset.lt_max'_of_mem_erase_max' (s := s) (H := hs) hj)⟩ le_rfl
        have hdisj : Disjoint (piece m) ((s.erase m).sup piece) := by
          exact Disjoint.symm ((hpiece_disjoint m).mono_left hsup_le)
        have hinsert : (insert m (s.erase m)).SupIndep piece := herase.insert hdisj
        simpa [m, Finset.insert_erase hmem] using hinsert
      · simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using Finset.supIndep_empty piece
    -- The restricted successor pieces are countably generated, pairwise disjoint, and span `A`.
    exact (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := A)).2 ⟨o, piece,
      hindepPiece, hpiece_top, hpiece_count⟩
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    have htop_bot : (⊤ : Submodule R M) = ⊥ := by
      have hiSup_bot : iSup summand = (⊥ : Submodule R M) := by
        simpa using (iSup_of_empty summand)
      have : (⊥ : Submodule R M) = ⊤ := by
        rw [← hiSup_bot, htop]
      simpa using this.symm
    have hSubsingletonA : Subsingleton A := by
      refine ⟨fun a b ↦ ?_⟩
      apply Subtype.ext
      have ha0 : ((a : A) : M) = 0 := by
        have : ((a : A) : M) ∈ (⊥ : Submodule R M) := by
          simpa [htop_bot] using (show ((a : A) : M) ∈ (⊤ : Submodule R M) from trivial)
        simpa using this
      have hb0 : ((b : A) : M) = 0 := by
        have : ((b : A) : M) ∈ (⊥ : Submodule R M) := by
          simpa [htop_bot] using (show ((b : A) : M) ∈ (⊤ : Submodule R M) from trivial)
        simpa using this
      simpa [ha0, hb0]
    have hAtop_bot : (⊤ : Submodule R A) = ⊥ := by
      ext a
      simp [Subsingleton.elim a 0]
    -- In the degenerate ambient-zero case, the summand `A` is also zero.
    exact (Module.isDirectSumOfCountablyGenerated_iff (R := R) (M := A)).2
      ⟨PUnit, fun _ ↦ (⊥ : Submodule R A),
        by simpa using iSupIndep_subsingleton (fun _ : PUnit ↦ (⊥ : Submodule R A)),
        by simpa [hAtop_bot],
        fun _ ↦ (Submodule.countablyGenerated_iff (R := R) (M := A) (P := (⊥ : Submodule R A))).2
          ⟨∅, Set.countable_empty, by simp⟩⟩

-- Proof sketch: run the Kaplansky transfinite dévissage on `M` and transport each stage across the
-- split injection `i : P →ₗ[R] M` and retraction `s : M →ₗ[R] P`; the splitting identity
-- `s.comp i = LinearMap.id` makes the induced stages on `P` compatible with the successor
-- complements, so they again form an internal direct-sum decomposition by countably generated
-- submodules.
/-- Theorem 10.84.4: if `M` is an internal direct sum of countably generated `R`-submodules and
`P` is a direct summand of `M`, exhibited by `R`-linear maps `i : P →ₗ[R] M` and
`s : M →ₗ[R] P` with `s.comp i = LinearMap.id`, then `P` is also an internal direct sum of
countably generated `R`-submodules. -/
@[stacks 058X]
theorem directSummand_isDirectSumOfCountablyGenerated
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (hs : s.comp i = LinearMap.id)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := by
  have hi : Function.Injective i := by
    intro x y hxy
    have hix : s (i x) = x := by
      simpa using congrArg (fun f : P →ₗ[R] P => f x) hs
    have hiy : s (i y) = y := by
      simpa using congrArg (fun f : P →ₗ[R] P => f y) hs
    -- Apply the retraction to the equality in the ambient module.
    rw [← hix, ← hiy]
    exact congrArg s hxy
  let eRange : P ≃ₗ[R] LinearMap.range i := LinearEquiv.ofInjective i hi
  -- Transport the complemented-submodule statement from the range back to the source module.
  exact isDirectSumOfCountablyGenerated_via_linearEquiv eRange <|
    isDirectSumOfCountablyGenerated_of_isCompl_submodule
      (A := LinearMap.range i) (B := LinearMap.ker s) (range_isCompl_ker_of_split i s hs) hM

-- Proof sketch: apply Theorem `10.84.4` to the linear equivalence `e`, viewed as split inclusion
-- and retraction data.
/-- A linear equivalence preserves the property of being an internal direct sum of countably
generated submodules. -/
theorem isDirectSumOfCountablyGenerated_of_linearEquiv
    (e : P ≃ₗ[R] M) (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := by
  -- This is exactly the transport helper proved above.
  simpa using isDirectSumOfCountablyGenerated_via_linearEquiv e hM

-- Proof sketch: a complemented submodule `P ≤ M` carries canonical split inclusion/projection
-- data, so this is the bridge/view specialization of Theorem `10.84.4` to the concrete submodule
-- presentation of a direct summand.
/-- Bridge form of Theorem 10.84.4 for a complemented submodule realization of a direct summand. -/
theorem isDirectSumOfCountablyGenerated_of_isComplemented
    (P : Submodule R M) (hP : IsComplemented P)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := by
  rcases hP with ⟨Q, hQ⟩
  -- Use the complemented-submodule form directly.
  simpa using isDirectSumOfCountablyGenerated_of_isCompl_submodule
    (A := P) (B := Q) hQ hM

end Module

end
