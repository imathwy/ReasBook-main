import Mathlib
import stacks_project.Chap10.Lemma_10_60_13
import stacks_project.Chap10.Lemma_10_104_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing
open scoped Pointwise

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing B] [Module.CohenMacaulay B B]

/-
Source/core/bridge triage:
* primary domain: regular sequences in Cohen-Macaulay local rings and their source-ring lifts along
  a local homomorphism;
* source-facing: existence of a regular sequence in `B` whose terms are images of elements of `A`;
* core/canonical: `Module.CohenMacaulay B B`, `RingTheory.Sequence.IsRegular B`, and the owner
  theorem `exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq`;
* bridge/view: the local homomorphism `φ : A →+* B` and the radical condition on
  `Ideal.map φ (maximalIdeal A)`.

Primitive data are only the local map `φ` and the radical equality. The target length is derived
canonically from `ringKrullDim B`, so a separate public binder `d` with a rewriting hypothesis
`ringKrullDim B = d` is redundant here.
-/

-- Proof sketch: argue by induction on `ringKrullDim B`. For the inductive step, use the
-- Cohen--Macaulay hypothesis and Lemma `10.104.2` to reduce to finding `f : A` whose image in
-- `B` avoids every minimal prime of `B`; the radical condition shows `maximalIdeal A` is not
-- contained in the preimage of any minimal prime, so prime avoidance produces such an `f`.
-- Quotient by `φ f` and iterate.
/-- Helper for Lemma 10.104.10: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ n : ℕ, ringKrullDim R = n := by
  -- Convert the finite local Krull dimension into an actual natural number.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim R = (ringKrullDim R).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.104.10: positive target dimension and the radical-maximal-ideal
hypothesis produce a source element whose image avoids every minimal prime of `B`. -/
private lemma exists_mem_maximalIdeal_avoiding_minimalPrimes_of_radical_maximalIdeal
    (φ : A →+* B) [IsLocalHom φ]
    (hpos : 0 < ringKrullDim B)
    (hrad : maximalIdeal B = (Ideal.map φ (maximalIdeal A)).radical) :
    ∃ f ∈ maximalIdeal A, ∀ q ∈ minimalPrimes B, φ f ∉ q := by
  let comapMin : Set (Ideal A) := Ideal.comap φ '' minimalPrimes B
  let U : Set A := ⋃ p ∈ comapMin, (p : Set A)
  have hfinite : comapMin.Finite := (minimalPrimes.finite_of_isNoetherianRing B).image _
  have hnot_subset : ¬ (maximalIdeal A : Set A) ⊆ U := by
    -- If the maximal ideal were covered by those comaps, prime avoidance would force one minimal
    -- prime of `B` to contain the mapped maximal ideal, contradicting positive dimension.
    intro hsubset
    obtain ⟨p, hp, hmp⟩ :=
      ((maximalIdeal A).subset_union_prime_finite hfinite (maximalIdeal A) (maximalIdeal A)
        (fun p hp _ _ ↦ by
          rcases hp with ⟨q, hq, rfl⟩
          letI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
          exact Ideal.comap_isPrime φ q)).mp hsubset
    rcases hp with ⟨q, hq, rfl⟩
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    have hmap_le_q : Ideal.map φ (maximalIdeal A) ≤ q := by
      exact (Ideal.map_le_iff_le_comap).2 hmp
    have hmax_le_q : maximalIdeal B ≤ q := by
      have hqrad : q.IsRadical := (show q.IsPrime from inferInstance).isRadical
      rw [hrad]
      exact hqrad.radical_le_iff.mpr hmap_le_q
    have hqeq : q = maximalIdeal B := by
      refine le_antisymm ?_ hmax_le_q
      exact le_maximalIdeal Ideal.IsPrime.ne_top'
    have hpheight : (maximalIdeal B).primeHeight = 0 := by
      simpa [hqeq] using (Ideal.primeHeight_eq_zero_iff (I := q)).2 hq
    have hheight : (maximalIdeal B).height = 0 := by
      simpa [Ideal.height_eq_primeHeight (I := maximalIdeal B)] using hpheight
    have hheight' : ↑(maximalIdeal B).height = (0 : WithBot ℕ∞) := by
      exact_mod_cast hheight
    have hzero : ringKrullDim B = 0 := by
      calc
        ringKrullDim B = ↑(maximalIdeal B).height := by
          exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
        _ = 0 := hheight'
    exact (ne_of_gt hpos) hzero
  obtain ⟨f, hf_mem, hf_not_mem⟩ := Set.not_subset.mp hnot_subset
  refine ⟨f, hf_mem, ?_⟩
  intro q hq hφf
  apply hf_not_mem
  refine Set.mem_iUnion.2 ?_
  refine ⟨Ideal.comap φ q, Set.mem_iUnion.2 ?_⟩
  refine ⟨⟨q, hq, rfl⟩, ?_⟩
  exact hφf

/-- Helper for Lemma 10.104.10: an element of `maximalIdeal B` avoiding every minimal prime gives
the regular singleton head and the exact dimension drop. -/
private lemma regular_singleton_and_cm_quotient_of_avoids_minimalPrimes
    (x : B) (hx : x ∈ maximalIdeal B) (hmin : ∀ q ∈ minimalPrimes B, x ∉ q) :
    IsRegular B [x] ∧
      ringKrullDim (B ⧸ Ideal.ofList [x]) + 1 = ringKrullDim B := by
  -- The dimension drop is the canonical owner theorem for quotienting by an element outside the
  -- minimal primes.
  have hspan_eq_ofList : Ideal.span ({x} : Set B) = Ideal.ofList [x] := by
    simpa [Ideal.ofList_singleton]
  have hquot_span :
      ringKrullDim (B ⧸ Ideal.span ({x} : Set B)) + 1 = ringKrullDim B := by
    exact
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := B) x hx hmin |>.symm
  have hquot_ofList :
      ringKrullDim (B ⧸ Ideal.ofList [x]) + 1 = ringKrullDim B := by
    rw [← hspan_eq_ofList]
    exact hquot_span
  have hx_mem : ∀ y ∈ ([x] : List B), y ∈ maximalIdeal B := by
    intro y hy
    rcases List.mem_singleton.mp hy with rfl
    exact hx
  have hreg : IsRegular B [x] := by
    -- Lemma `10.104.2` turns the exact quotient dimension formula into regularity.
    refine
      (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := B) (xs := [x]) hx_mem).2 ?_
    simpa using hquot_ofList
  exact ⟨hreg, hquot_ofList⟩

/-- Helper for Lemma 10.104.10: the radical-maximal-ideal hypothesis descends along quotienting by
the chosen head image. -/
private lemma quotient_radical_maximalIdeal_of_radical_maximalIdeal
    (φ : A →+* B) [IsLocalHom φ] {f : A} (hf : f ∈ maximalIdeal A)
    (hrad : maximalIdeal B = (Ideal.map φ (maximalIdeal A)).radical) :
    let I : Ideal B := Ideal.ofList [φ f]
    let Q := B ⧸ I
    let _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top
        (by
          simpa [I, Ideal.ofList_singleton] using
            (Ideal.span_singleton_le_iff_mem (I := maximalIdeal B)).2
              ((IsLocalRing.map_maximalIdeal_le φ) (Ideal.mem_map_of_mem φ hf)))
    let _ : IsLocalRing Q :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let ψ : A →+* Q := (Ideal.Quotient.mk I).comp φ
    maximalIdeal Q = (Ideal.map ψ (maximalIdeal A)).radical := by
  let I : Ideal B := Ideal.ofList [φ f]
  let Q := B ⧸ I
  have hI_le_max : I ≤ maximalIdeal B := by
    simpa [I, Ideal.ofList_singleton] using
      (Ideal.span_singleton_le_iff_mem (I := maximalIdeal B)).2
        ((IsLocalRing.map_maximalIdeal_le φ) (Ideal.mem_map_of_mem φ hf))
  have hI_ne_top : I ≠ ⊤ := by
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hI_le_max
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let ψ : A →+* Q := (Ideal.Quotient.mk I).comp φ
  have hI_le_map : I ≤ Ideal.map φ (maximalIdeal A) := by
    -- The quotient kernel is generated by the chosen image `φ f`, which already lies in the
    -- mapped maximal ideal.
    simpa [I, Ideal.ofList_singleton] using
      (Ideal.span_singleton_le_iff_mem (I := Ideal.map φ (maximalIdeal A))).2
        (Ideal.mem_map_of_mem φ hf)
  have hmap_max :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B) = maximalIdeal Q := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmap_rad :
      Ideal.map (Ideal.Quotient.mk I) ((Ideal.map φ (maximalIdeal A)).radical) =
        (Ideal.map (Ideal.Quotient.mk I) (Ideal.map φ (maximalIdeal A))).radical := by
    have hker_le :
        RingHom.ker (Ideal.Quotient.mk I) ≤ Ideal.map φ (maximalIdeal A) := by
      simpa [I] using hI_le_map
    exact Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective hker_le
  -- Map the original radical identity through the quotient map and rewrite the composite as `ψ`.
  calc
    maximalIdeal Q = Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B) := by
      rw [hmap_max]
    _ = Ideal.map (Ideal.Quotient.mk I) ((Ideal.map φ (maximalIdeal A)).radical) := by
      rw [hrad]
    _ = (Ideal.map (Ideal.Quotient.mk I) (Ideal.map φ (maximalIdeal A))).radical := hmap_rad
    _ = (Ideal.map ψ (maximalIdeal A)).radical := by
      simp [ψ, Ideal.map_map]

/-- Helper for Lemma 10.104.10: regularity on `QuotSMulTop x B` is equivalent to regularity of the
mapped list on the quotient ring `B ⧸ (x)`. -/
private theorem isRegular_quotSMulTop_iff_quotient_span_singleton
    {x : B} {rs : List B} :
    IsRegular (QuotSMulTop x B) rs ↔
      IsRegular (B ⧸ Ideal.ofList [x])
        (rs.map (Ideal.Quotient.mk (Ideal.ofList [x]))) := by
  have hspan : Ideal.ofList [x] = x • (⊤ : Ideal B) := by
    -- The quotient ring `B ⧸ Ideal.ofList [x]` is the standard owner quotient `QuotSMulTop x B`.
    calc
      Ideal.ofList [x] = Ideal.span ({x} : Set B) := by
        simp [Ideal.ofList_singleton]
      _ = x • (⊤ : Ideal B) := by
        simp [← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop x B ≃+ B ⧸ Ideal.ofList [x] :=
    (Ideal.quotientEquivAlgOfEq B hspan).symm.toRingEquiv.toAddEquiv
  -- Transport regularity across the quotient identification elementwise.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha y
  change e (a • y) = Ideal.Quotient.mk (Ideal.ofList [x]) a • e y
  rcases Quotient.exists_rep y with ⟨z, rfl⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simpa [e, smul_eq_mul] using e.map_mul a z

/-- Helper for Lemma 10.104.10: the induction hypothesis returns regularity on the quotient ring,
which is the same as regularity of the original mapped tail on `QuotSMulTop x B`. -/
private theorem quotient_tail_isRegular_on_quotSMulTop_of_map_regular
    (φ : A →+* B) (x : B) (gs : List A)
    (hreg :
      IsRegular (B ⧸ Ideal.ofList [x])
        (gs.map ((Ideal.Quotient.mk (Ideal.ofList [x])).comp φ))) :
    IsRegular (QuotSMulTop x B) (gs.map φ) := by
  -- Rewrite the quotient-side list as the image of `gs.map φ` under the quotient map.
  have hmap :
      (gs.map φ).map (Ideal.Quotient.mk (Ideal.ofList [x])) =
        gs.map ((Ideal.Quotient.mk (Ideal.ofList [x])).comp φ) := by
    simp [List.map_map]
  -- The quotient/`QuotSMulTop` equivalence from Lemma `10.104.2` supplies the transport.
  refine
    (isRegular_quotSMulTop_iff_quotient_span_singleton (B := B) (x := x) (rs := gs.map φ)).2 ?_
  simpa [hmap] using hreg

/-- Helper for Lemma 10.104.10: after identifying `ringKrullDim B` with a natural number, the
source-faithful induction constructs a length-`n` source list whose image is regular in `B`. -/
private theorem exists_regularSequence_map_of_radical_maximalIdeal_of_ringKrullDim_eq_nat
    (n : ℕ) :
    ∀ {B' : Type v} [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B']
      (hcm : Module.CohenMacaulay B' B')
      (φ : A →+* B') [IsLocalHom φ]
      (hrad : maximalIdeal B' = (Ideal.map φ (maximalIdeal A)).radical)
      (hdim : ringKrullDim B' = n),
      ∃ fs : List A, fs.length = ringKrullDim B' ∧ IsRegular B' (fs.map φ) := by
  induction n with
  | zero =>
      intro B' _ _ _ hcm φ _ hrad hdim
      letI : Module.CohenMacaulay B' B' := hcm
      -- When the dimension is zero, the empty sequence already has the required length.
      refine ⟨[], ?_, ?_⟩
      · simpa [hdim]
      · simpa using (IsRegular.nil B' B')
  | succ n ih =>
      intro B' _ _ _ hcm φ _ hrad hdim
      letI : Module.CohenMacaulay B' B' := hcm
      have hpos : 0 < ringKrullDim B' := by
        -- The positive-dimensional induction step matches the textbook one-element choice.
        calc
          (0 : WithBot ℕ∞) < (n + 1 : WithBot ℕ∞) := by exact_mod_cast Nat.succ_pos n
          _ = ringKrullDim B' := by simpa [hdim]
      obtain ⟨f, hf_mem, hf_avoid⟩ :=
        exists_mem_maximalIdeal_avoiding_minimalPrimes_of_radical_maximalIdeal
          (A := A) (B := B') φ hpos hrad
      have hφf_mem : φ f ∈ maximalIdeal B' := by
        exact (IsLocalRing.map_maximalIdeal_le φ) (Ideal.mem_map_of_mem φ hf_mem)
      obtain ⟨hhead_reg, hquot_dim⟩ :=
        regular_singleton_and_cm_quotient_of_avoids_minimalPrimes
          (B := B') (x := φ f) hφf_mem hf_avoid
      let I : Ideal B' := Ideal.ofList [φ f]
      let Q := B' ⧸ I
      let ψ : A →+* Q := (Ideal.Quotient.mk I).comp φ
      have hI_le_max : I ≤ maximalIdeal B' := by
        simpa [I, Ideal.ofList_singleton] using
          (Ideal.span_singleton_le_iff_mem (I := maximalIdeal B')).2 hφf_mem
      have hI_ne_top : I ≠ ⊤ := by
        exact ne_top_of_le_ne_top (maximalIdeal.isMaximal B').ne_top hI_le_max
      letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
      letI : IsLocalRing Q :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hquot_cm : Module.CohenMacaulay Q Q := by
        -- The quotient by the regular singleton stays Cohen--Macaulay.
        exact
          (selfModule_cohenMacaulay_quotient_take_of_isRegular
            (R := B') (xs := [φ f]) hhead_reg (i := 1))
      have hradQ :
          maximalIdeal Q = (Ideal.map ψ (maximalIdeal A)).radical := by
        simpa [I, Q, ψ] using
          quotient_radical_maximalIdeal_of_radical_maximalIdeal
            (A := A) (B := B') φ hf_mem hrad
      letI : IsLocalHom (Ideal.Quotient.mk I) :=
        isLocalHom_of_le_jacobson_bot I <| hI_le_max.trans (maximalIdeal_le_jacobson _)
      letI : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
      obtain ⟨m, hQ_nat⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (R := Q)
      have hm_succ : m + 1 = n + 1 := by
        have hm_succ' : (((m + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) := by
          simpa [hQ_nat, hdim, I, Q] using hquot_dim
        exact_mod_cast hm_succ'
      have hQdim : ringKrullDim Q = n := by
        have hm : m = n := by omega
        simpa [Q, hQ_nat, hm]
      have hrec :
          ∃ gs : List A,
            gs.length = ringKrullDim (B' ⧸ Ideal.ofList [φ f]) ∧
              IsRegular (B' ⧸ Ideal.ofList [φ f]) (gs.map ψ) := by
        -- Route correction: pass the quotient Cohen--Macaulay proof as explicit data, so the
        -- recursive step no longer depends on fragile local typeclass synthesis.
        simpa [I, Q, ψ] using
          ih hquot_cm ψ hradQ hQdim
      obtain ⟨gs, hgs_len, hgs_reg⟩ := hrec
      have htail_reg :
          IsRegular (QuotSMulTop (φ f) B') (gs.map φ) := by
        -- The recursive regularity statement comes back from the quotient ring to `QuotSMulTop`.
        simpa [I, ψ] using
          quotient_tail_isRegular_on_quotSMulTop_of_map_regular
            (A := A) (B := B') φ (φ f) gs hgs_reg
      have hφf_regular : IsSMulRegular B' (φ f) := by
        -- The singleton regular sequence records exactly the head non-zero-divisor property.
        simpa using ((isRegular_cons_iff (M := B') (φ f) []).1 hhead_reg).1
      refine ⟨f :: gs, ?_, ?_⟩
      · -- The quotient has dimension `n`, so adjoining the head restores length `n + 1`.
        simpa [hdim, hgs_len]
      · -- Finish by adjoining the regular head to the transported regular tail.
        simpa using IsRegular.cons hφf_regular htail_reg

/-- Lemma 10.104.10: let `φ : A →+* B` be a local homomorphism of local rings. Assume that `B` is
Noetherian and Cohen--Macaulay, and that the maximal ideal of `B` is the radical of the ideal
generated by the image of the maximal ideal of `A`. Then there exists a list
`fs = [f₁, …, f_d]` of elements of `A`, where `d = dim(B)`, whose image `fs.map φ` is a regular
sequence in `B`. -/
theorem exists_regularSequence_map_of_radical_maximalIdeal
    (φ : A →+* B) [IsLocalHom φ]
    (hrad : maximalIdeal B = (Ideal.map φ (maximalIdeal A)).radical) :
    ∃ fs : List A, fs.length = ringKrullDim B ∧ IsRegular B (fs.map φ) := by
  -- Follow the source proof literally: rewrite the Krull dimension as a natural number and run
  -- the one-step prime-avoidance induction from the previous helper.
  obtain ⟨n, hdim⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (R := B)
  exact exists_regularSequence_map_of_radical_maximalIdeal_of_ringKrullDim_eq_nat
    (A := A) n inferInstance φ hrad hdim

end
