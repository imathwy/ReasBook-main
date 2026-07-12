import Mathlib
import StacksProject_2024.Chap10.Lemma_10_68_10
import StacksProject_2024.Chap10.Lemma_10_72_7
import StacksProject_2024.Chap10.Proposition_10_103_4
import StacksProject_2024.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence IsLocalRing Ideal.Quotient
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-
Source/core/bridge triage:
* primary domain: regular sequences and Cohen-Macaulay local rings in commutative algebra;
* source-facing: Lemma `10.104.2`, specialized from Proposition `10.103.4` to the self-module
  `R`, together with its quotient consequences stated at the local owner level from Definition
  `10.104.1`;
* core/canonical: `RingTheory.Sequence.IsRegular`, `Module.CohenMacaulay`, and the owner theorem
  `Module.exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay`;
* bridge/view: the quotient rings `R ⧸ Ideal.ofList xs` and `R ⧸ Ideal.ofList (xs.take i)`.

Primitive data are only the list `xs`, its maximal-ideal membership when the source assumes it,
and the owner abstractions above. The quotient Cohen-Macaulay consequences are stated directly as
self-module properties of the quotient rings, not upgraded here to the later global ring owner.
-/

private theorem ofList_take_le_maximalIdeal_of_isRegular {xs : List R} (hreg : IsRegular R xs)
    {i : ℕ} : Ideal.ofList (xs.take i) ≤ maximalIdeal R := by
  have hxs : Ideal.ofList xs ≤ maximalIdeal R :=
    IsRegular.ofList_le_maximalIdeal hreg
  refine Ideal.span_le.mpr ?_
  intro x hx
  exact hxs <| Ideal.subset_span <| List.mem_of_mem_take hx

private theorem quotient_isLocalRing_of_isRegular_take {xs : List R} (hreg : IsRegular R xs)
    {i : ℕ} : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)) := by
  have hI : Ideal.ofList (xs.take i) ≤ maximalIdeal R :=
    ofList_take_le_maximalIdeal_of_isRegular hreg
  have hne : Ideal.ofList (xs.take i) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  have : Nontrivial (R ⧸ Ideal.ofList (xs.take i)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact hne
  exact IsLocalRing.of_surjective' (mk _) mk_surjective

-- Proof sketch: this is Proposition `10.103.4` specialized to the self-module `R`, after
-- rewriting `supportDim R R` as `ringKrullDim R` and the quotient support dimension as the Krull
-- dimension of `R ⧸ Ideal.ofList xs`.
/-- Lemma 10.104.2: in a Noetherian local Cohen-Macaulay ring `R`, if
`ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R`, then `xs` extends to a regular
sequence of length `ringKrullDim R`. In a local ring, maximal-ideal containment of the extended
sequence is recovered from regularity by the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. -/
@[stacks 02JN]
theorem exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq
    {xs : List R} (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R)
    (hquot : ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R) :
    ∃ xs' : List R,
      IsRegular R (xs ++ xs') ∧ ringKrullDim R = (xs ++ xs').length := by
  -- Specialize Proposition `10.103.4` to the self-module `R`, after extracting the finite
  -- natural number underlying `ringKrullDim R`.
  have hR_ne_bot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  set dEnat : ℕ∞ := (ringKrullDim R).unbot hR_ne_bot
  have hR_ne_top : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  have hdEnat_ne_top : dEnat ≠ ⊤ := by
    intro hdEnat_top
    exact hR_ne_top <| by
      calc
        ringKrullDim R = ((dEnat : ℕ∞) : WithBot ℕ∞) := by
          simpa [dEnat] using (WithBot.coe_unbot (ringKrullDim R) hR_ne_bot).symm
        _ = ⊤ := by simpa [hdEnat_top]
  set d : ℕ := dEnat.toNat
  have hdEnat_eq : dEnat = d := by
    calc
      dEnat = (dEnat.toNat : ℕ∞) := by
        simpa [hdEnat_ne_top] using (ENat.coe_toNat hdEnat_ne_top).symm
      _ = (d : ℕ∞) := rfl
  have hdim : Module.supportDim R R = d := by
    calc
      Module.supportDim R R = ringKrullDim R := by
        simpa using (Module.supportDim_self_eq_ringKrullDim R)
      _ = ((dEnat : ℕ∞) : WithBot ℕ∞) := by
        simpa [dEnat] using (WithBot.coe_unbot (ringKrullDim R) hR_ne_bot).symm
      _ = d := by
        simpa using congrArg (fun n : ℕ∞ ↦ ((n : ℕ∞) : WithBot ℕ∞)) hdEnat_eq
  have hquot' :
      Module.supportDim R (R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))) + xs.length =
        Module.supportDim R R := by
    -- On the self-module, quotient support dimension is ordinary Krull dimension.
    have hsmul :
        Ideal.ofList xs • (⊤ : Submodule R R) = (Ideal.ofList xs : Ideal R) := by
      ext x
      simp [Ideal.mul_top]
    calc
      Module.supportDim R (R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))) + xs.length =
          ringKrullDim (R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))) + xs.length := by
            rw [Module.supportDim_quotient_eq_ringKrullDim]
      _ = ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length := by rw [hsmul]
      _ = ringKrullDim R := hquot
      _ = Module.supportDim R R := by rw [Module.supportDim_self_eq_ringKrullDim]
  obtain ⟨xs', hreg, hlen⟩ :=
    Module.exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
      (R := R) (M := R) (d := d) hxs hdim hquot'
  refine ⟨xs', hreg, ?_⟩
  calc
    ringKrullDim R = (d : WithBot ℕ∞) := by
      calc
        ringKrullDim R = ((dEnat : ℕ∞) : WithBot ℕ∞) := by
          simpa [dEnat] using (WithBot.coe_unbot (ringKrullDim R) hR_ne_bot).symm
        _ = d := by
          simpa using congrArg (fun n : ℕ∞ ↦ ((n : ℕ∞) : WithBot ℕ∞)) hdEnat_eq
    _ = (xs ++ xs').length := by exact_mod_cast hlen

/-- Helper for Lemma 10.104.2: in a Noetherian local ring, a regular sequence whose length already
equals the Krull dimension forces the ring to be Cohen--Macaulay. -/
private theorem cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {ys : List S}
    (hreg : IsRegular S ys) (hlen : ys.length = ringKrullDim S) :
    Module.CohenMacaulay S S := by
  have hSdim : Module.supportDim S S = ys.length := by
    rw [Module.supportDim_self_eq_ringKrullDim, ← hlen]
  -- Extend the sequence up to module depth and show that the added tail is empty.
  obtain ⟨ys', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  letI : Nontrivial S := hreg.nontrivial
  have hIneTop : Ideal.ofList (ys ++ ys') • (⊤ : Submodule S S) ≠ ⊤ := by
    simpa [ne_comm] using hreg'.top_ne_smul
  letI : Nontrivial (S ⧸ (Ideal.ofList (ys ++ ys') • (⊤ : Submodule S S))) :=
    Submodule.Quotient.nontrivial_iff.2 hIneTop
  have hquot_nonbot :
      Module.supportDim S (S ⧸ (Ideal.ofList (ys ++ ys') • (⊤ : Submodule S S))) ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial S _
  have hlen_le :
      (((ys ++ ys').length : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim S S := by
    -- The quotient support dimension is nonnegative, so the regular-sequence formula bounds
    -- the full length by the ambient support dimension.
    rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular (M := S) (rs := ys ++ ys') hreg']
    simpa [add_comm] using
      WithBot.le_add_self hquot_nonbot ((((ys ++ ys').length : ℕ∞) : WithBot ℕ∞))
  have htail_len : ys'.length = 0 := by
    have hsum_le :
        (((ys.length + ys'.length : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
          (((ys.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hSdim, List.length_append] using hlen_le
    have hsum_le_nat : ys.length + ys'.length ≤ ys.length := by
      exact_mod_cast hsum_le
    omega
  have htail : ys' = [] := List.length_eq_zero_iff.mp htail_len
  -- With no tail left, the depth identity is exactly the Cohen--Macaulay equality.
  refine Module.CohenMacaulay.mk ?_
  rw [hdepth, htail]
  simpa using hSdim

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: the head principal ideal is contained in the ideal generated by the
whole list. -/
private theorem full_tail_quotient_ringEquiv_head_le
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Ideal.span ({r} : Set A) ≤ Ideal.ofList (r :: rs) := by
  -- The head generator is one of the generators of the full list ideal.
  simpa [Ideal.ofList_cons] using
    (le_sup_left : Ideal.span ({r} : Set A) ≤ Ideal.span ({r} : Set A) ⊔ Ideal.ofList rs)

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: after quotienting by the head element, the remaining list ideal is
the image of the whole list ideal. -/
private theorem full_tail_quotient_ringEquiv_map_eq
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) =
      (Ideal.ofList (r :: rs)).map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) := by
  -- Modding out by `r` kills the head generator and leaves the mapped tail generators.
  rw [Ideal.map_ofList, List.map_cons, Ideal.ofList_cons]
  simp

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: quotienting first by the head and then by the mapped tail is the
same as quotienting once by the whole prefix. -/
private noncomputable def full_tail_quotient_ringEquiv
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃+*
      A ⧸ Ideal.ofList (r :: rs) :=
  (Ideal.quotEquivOfEq (full_tail_quotient_ringEquiv_map_eq (A := A) (r := r) (rs := rs))).trans
    (DoubleQuot.quotQuotEquivQuotOfLE
      (full_tail_quotient_ringEquiv_head_le (A := A) (r := r) (rs := rs)))

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: the iterated quotient equivalence sends a doubly-quotiented
generator to its class in the full quotient. -/
@[simp] private theorem full_tail_quotient_ringEquiv_apply_mk_mk
    {A : Type u} [CommRing A] {r : A} {rs : List A} (x : A) :
    full_tail_quotient_ringEquiv (A := A) (r := r) (rs := rs)
      (Ideal.Quotient.mk
        (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
        (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x := by
  -- Unfold the composite and use the third isomorphism theorem on representatives.
  change
    (DoubleQuot.quotQuotEquivQuotOfLE
      (full_tail_quotient_ringEquiv_head_le (A := A) (r := r) (rs := rs)))
      ((Ideal.quotEquivOfEq (full_tail_quotient_ringEquiv_map_eq (A := A) (r := r) (rs := rs)))
        (Ideal.Quotient.mk
          (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
          (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x))) =
    Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x
  rw [Ideal.quotEquivOfEq_mk]
  simpa [DoubleQuot.quotQuotMk] using
    (DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk
      (I := Ideal.span ({r} : Set A)) (J := Ideal.ofList (r :: rs)) x
      (h := full_tail_quotient_ringEquiv_head_le (A := A) (r := r) (rs := rs)))

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: the owner quotient module by a singleton ideal is the same as the
quotient ring by the corresponding principal ideal for regularity questions. -/
private theorem isRegular_quotSMulTop_iff_quotient_span_singleton
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    IsRegular (QuotSMulTop r A) rs ↔
      IsRegular (A ⧸ Ideal.span ({r} : Set A))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  have hspan : Ideal.span ({r} : Set A) = r • (⊤ : Ideal A) := by
    -- The quotient ring `A ⧸ (r)` is the same quotient object as `A / rA`.
    simp [smul_eq_mul, ← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop r A ≃+ A ⧸ Ideal.span ({r} : Set A) :=
    (Ideal.quotientEquivAlgOfEq A hspan).symm.toRingEquiv.toAddEquiv
  -- Transport regularity across the canonical additive equivalence while mapping scalars through
  -- the quotient map `A → A ⧸ (r)`.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  change e (a • x) = Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a • e x
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  -- On representatives, the transported scalar action is multiplication by the image of `a`.
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simp [e, smul_eq_mul]

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: the tail regularity on `QuotSMulTop r A` becomes regularity of the
mapped tail on the quotient ring `A ⧸ Ideal.span {r}`. -/
private theorem quotientTail_isRegular_on_quotientRing
    {A : Type u} [CommRing A] {r : A} {rs : List A}
    (hreg : IsRegular (QuotSMulTop r A) rs) :
    IsRegular (A ⧸ Ideal.span ({r} : Set A))
      (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  -- The one-step quotient identification packages the transport needed for the induction step.
  exact (isRegular_quotSMulTop_iff_quotient_span_singleton (A := A) (r := r) (rs := rs)).1 hreg

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: quotienting by the empty prefix leaves the regularity statement
unchanged after identifying `S ⧸ 0` with `S`. -/
private theorem regular_tail_on_prefix_quotient_nil
    {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {zs : List S}
    (hreg : IsRegular S zs) :
    IsRegular (S ⧸ Ideal.ofList ([] : List S))
      (zs.map (Ideal.Quotient.mk (Ideal.ofList ([] : List S)))) := by
  let e : S ≃+* S ⧸ Ideal.ofList ([] : List S) :=
    (RingEquiv.quotientBot S).symm.trans
      (Ideal.quotEquivOfEq (Ideal.ofList_nil (R := S)).symm)
  -- Transport regularity across the quotient-by-zero identification.
  exact (e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun a _ x => by
        change e (a * x) = Ideal.Quotient.mk (Ideal.ofList ([] : List S)) a * e x
        simpa [e, Ideal.Quotient.algebraMap_eq] using e.map_mul a x).1 hreg

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: after quotienting by a regular prefix `ys`, the mapped tail `zs`
remains regular; the induction is organized by `ys.length` so the ambient quotient ring is only a
parameter of the recursive call. -/
private theorem regular_tail_on_prefix_quotient_of_isRegular_append_length
    (n : ℕ) :
    ∀ {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {ys zs : List S},
      ys.length = n → IsRegular S (ys ++ zs) →
      IsRegular (S ⧸ Ideal.ofList ys) (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))) := by
  induction n with
  | zero =>
      intro S _ _ _ ys zs hlen hfull
      cases ys with
      | nil =>
          -- With no prefix, this is exactly the quotient-by-zero identification.
          simpa using regular_tail_on_prefix_quotient_nil hfull
      | cons r ys =>
          cases hlen
  | succ n ih =>
      intro S _ _ _ ys zs hlen hfull
      cases ys with
      | nil =>
          cases hlen
      | cons r ys =>
          have hlen_tail : ys.length = n := by
            simpa using Nat.succ.inj hlen
          -- Split the full regular sequence into the head nonzerodivisor and the regular tail on
          -- the first quotient.
          rcases (isRegular_cons_iff (M := S) r (ys ++ zs)).1 (by simpa using hfull) with
            ⟨hr_regular, htail_regular⟩
          have hr_mem : r ∈ maximalIdeal S := by
            -- In a local ring, every element of a regular sequence lies in the maximal ideal.
            have hle : Ideal.ofList ((r :: ys) ++ zs) ≤ maximalIdeal S :=
              IsRegular.ofList_le_maximalIdeal hfull
            exact hle (Ideal.subset_span (by simp))
          have hspan_ne_top : Ideal.span ({r} : Set S) ≠ ⊤ := by
            intro htop
            have hr_nonunit : ¬ IsUnit r := by
              rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr_mem
            exact hr_nonunit (Ideal.span_singleton_eq_top.mp htop)
          letI : Nontrivial (S ⧸ Ideal.span ({r} : Set S)) :=
            Ideal.Quotient.nontrivial_iff.mpr hspan_ne_top
          letI : IsLocalRing (S ⧸ Ideal.span ({r} : Set S)) :=
            IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))
              Ideal.Quotient.mk_surjective
          have hmapped_full :
              IsRegular (S ⧸ Ideal.span ({r} : Set S))
                ((ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))) ++
                  (zs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))) := by
            -- The quotient transport keeps the remaining concatenated sequence regular.
            simpa [List.map_append] using
              quotientTail_isRegular_on_quotientRing (A := S) (r := r) htail_regular
          have htail_on_iterated :
              IsRegular
                (((S ⧸ Ideal.span ({r} : Set S)) ⧸
                  Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))))
                ((zs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))).map
                  (Ideal.Quotient.mk
                    (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))))) := by
            -- Recurse on the shorter mapped prefix inside the first quotient ring.
            exact ih (S := S ⧸ Ideal.span ({r} : Set S))
              (ys := ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))
              (zs := zs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))
              (by simpa using hlen_tail) hmapped_full
          -- Flatten the iterated quotient back to the quotient by the full prefix.
          let e := full_tail_quotient_ringEquiv (A := S) (r := r) (rs := ys)
          have htransport :
              IsRegular
                (((S ⧸ Ideal.span ({r} : Set S)) ⧸
                  Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))))
                ((zs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))).map
                  (Ideal.Quotient.mk
                    (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))))) ↔
              IsRegular (S ⧸ Ideal.ofList (r :: ys))
                (zs.map (Ideal.Quotient.mk (Ideal.ofList (r :: ys))) ) := by
            -- The quotient equivalence identifies each doubly-quotiented generator with its class
            -- in the single quotient by the full prefix.
            refine e.toAddEquiv.isRegular_congr ?_
            have hcompat :
                ∀ ws : List S,
                  List.Forall₂
                    (fun a b =>
                      ∀ x : ((S ⧸ Ideal.span ({r} : Set S)) ⧸
                        Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S))))),
                        e (a • x) = b • e x)
                    ((ws.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))).map
                      (Ideal.Quotient.mk
                        (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))))))
                    (ws.map (Ideal.Quotient.mk (Ideal.ofList (r :: ys)))) := by
              -- We verify the compatibility one generator at a time along the original tail list.
              intro ws
              induction ws with
              | nil =>
                  simp
              | cons z ws ihws =>
                  refine List.Forall₂.cons ?_ ihws
                  intro x
                  change e
                      (Ideal.Quotient.mk
                        (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))))
                        (Ideal.Quotient.mk (Ideal.span ({r} : Set S)) z) * x) =
                    Ideal.Quotient.mk (Ideal.ofList (r :: ys)) z * e x
                  calc
                    e
                        (Ideal.Quotient.mk
                          (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))))
                          (Ideal.Quotient.mk (Ideal.span ({r} : Set S)) z) * x) =
                        e
                          (Ideal.Quotient.mk
                            (Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span ({r} : Set S)))))
                            (Ideal.Quotient.mk (Ideal.span ({r} : Set S)) z)) * e x := by
                              rw [map_mul]
                    _ = Ideal.Quotient.mk (Ideal.ofList (r :: ys)) z * e x := by
                          simpa [e] using
                            congrArg (fun t ↦ t * e x)
                              (full_tail_quotient_ringEquiv_apply_mk_mk
                                (A := S) (r := r) (rs := ys) z)
            exact hcompat zs
          exact htransport.1 htail_on_iterated

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: if `ys ++ zs` is regular in a local ring, then after quotienting by
the prefix ideal `Ideal.ofList ys`, the mapped tail `zs` is still regular. -/
private theorem regular_tail_on_prefix_quotient_of_isRegular_append
    {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {ys zs : List S}
    (hfull : IsRegular S (ys ++ zs)) :
    IsRegular (S ⧸ Ideal.ofList ys) (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))) := by
  -- Route correction: recurse on the prefix length so the changing quotient ring is only a
  -- parameter of the induction hypothesis.
  exact regular_tail_on_prefix_quotient_of_isRegular_append_length ys.length rfl hfull

omit [Module.CohenMacaulay R R] in
/-- Helper for Lemma 10.104.2: if a regular prefix `ys` extends to a full regular sequence of
length `ringKrullDim R`, then the mapped tail on `R ⧸ Ideal.ofList ys` has length exactly the
Krull dimension of that quotient. -/
private theorem mapped_tail_length_eq_ringKrullDim_of_regular_extension {ys zs : List R}
    (hys : IsRegular R ys) (hfull : ringKrullDim R = (ys ++ zs).length) :
    (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))).length = ringKrullDim (R ⧸ Ideal.ofList ys) := by
  have hdim :
      ringKrullDim (R ⧸ Ideal.ofList ys) + ys.length = ringKrullDim R :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ys hys
  have hsum :
      ys.length + ringKrullDim (R ⧸ Ideal.ofList ys) = ys.length + zs.length := by
    -- Rewrite the full-length equality so that right-cancellation by the prefix length applies.
    calc
      ys.length + ringKrullDim (R ⧸ Ideal.ofList ys) =
          ringKrullDim (R ⧸ Ideal.ofList ys) + ys.length := by rw [add_comm]
      _ = ringKrullDim R := hdim
      _ = (ys ++ zs).length := hfull
      _ = ys.length + zs.length := by simp [List.length_append]
  have htail_dim : ringKrullDim (R ⧸ Ideal.ofList ys) = zs.length :=
    (ENat.WithBot.natCast_add_cancel :
      ys.length + ringKrullDim (R ⧸ Ideal.ofList ys) = ys.length + zs.length ↔
        ringKrullDim (R ⧸ Ideal.ofList ys) = zs.length).mp hsum
  -- Mapping the tail does not change its length.
  simpa [List.length_map] using htail_dim.symm

-- Proof sketch: every prefix `xs.take i` of a regular sequence is regular, and quotienting a
-- Cohen-Macaulay local ring by a regular sequence stays Cohen-Macaulay at the local owner level
-- `Module.CohenMacaulay Q Q`. No separate bound `i ≤ xs.length` belongs in the public API, since
-- `xs.take i = xs` once `i` is past the end.
/-- If `xs` is a regular sequence, then every intermediate quotient
`R ⧸ Ideal.ofList (xs.take i)` is Cohen-Macaulay as a module over itself. -/
theorem selfModule_cohenMacaulay_quotient_take_of_isRegular {xs : List R}
    (hreg : IsRegular R xs) {i : ℕ} :
    let _ : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)) :=
      quotient_isLocalRing_of_isRegular_take hreg
    Module.CohenMacaulay (R ⧸ Ideal.ofList (xs.take i)) (R ⧸ Ideal.ofList (xs.take i)) := by
  let ys := xs.take i
  letI : IsLocalRing (R ⧸ Ideal.ofList ys) := by
    dsimp [ys]
    exact quotient_isLocalRing_of_isRegular_take hreg
  have htake : IsRegular R (ys ++ xs.drop i) := by
    -- Split the original regular sequence into the chosen prefix and tail.
    simpa [ys, List.take_append_drop] using hreg
  have hysreg : IsRegular R ys :=
    isRegular_left_of_isRegular_append (M := R) htake
  have hys_mem : ∀ y ∈ ys, y ∈ maximalIdeal R := by
    -- Regular sequences in a local ring lie in the maximal ideal.
    have hys_max : Ideal.ofList ys ≤ maximalIdeal R := IsRegular.ofList_le_maximalIdeal hysreg
    intro y hy
    exact hys_max (Ideal.subset_span hy)
  have hdim_prefix :
      ringKrullDim (R ⧸ Ideal.ofList ys) + ys.length = ringKrullDim R :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ys hysreg
  obtain ⟨zs, hfull, hlen_full⟩ :=
    exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq hys_mem
      hdim_prefix
  have htail_reg :
      IsRegular (R ⧸ Ideal.ofList ys) (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))) :=
    regular_tail_on_prefix_quotient_of_isRegular_append hfull
  have htail_len :
      (zs.map (Ideal.Quotient.mk (Ideal.ofList ys))).length =
        ringKrullDim (R ⧸ Ideal.ofList ys) :=
    mapped_tail_length_eq_ringKrullDim_of_regular_extension hysreg hlen_full
  -- The prefix quotient now has a full-length regular sequence, so it is Cohen-Macaulay.
  simpa [ys] using
    (cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim
      (S := R ⧸ Ideal.ofList ys) htail_reg htail_len)

-- Proof sketch: the prefix `xs.take i` of a regular sequence is regular, and mathlib already
-- supplies the additive dimension formula for quotienting by a regular sequence. Here the bound
-- `i ≤ xs.length` is part of the mathematical content because the conclusion is written with `+ i`
-- rather than `+ (xs.take i).length`.
/-- If `xs` is a regular sequence, then every intermediate quotient
`R ⧸ Ideal.ofList (xs.take i)` has dimension `ringKrullDim R - i`, written canonically as
`ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R`. -/
theorem ringKrullDim_quotient_take_add_eq_ringKrullDim_of_isRegular {xs : List R}
    (hreg : IsRegular R xs) {i : ℕ} (hi : i ≤ xs.length) :
    ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R := by
  have htake :
      IsRegular R (xs.take i ++ xs.drop i) := by
    simpa [List.take_append_drop] using hreg
  have htakeReg : IsRegular R (xs.take i) :=
    isRegular_left_of_isRegular_append (M := R) htake
  -- Apply the standard dimension formula to the regular prefix.
  simpa [List.length_take_of_le hi] using
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular (xs.take i) htakeReg

-- Proof sketch: the forward implication is the standard dimension formula for regular sequences.
-- For the converse, specialize Proposition `10.103.4` to the self-module `R`, as in the extension
-- theorem above, and pass from the maximal extension back to the initial segment `xs`.
/-- Companion criterion from Lemma 10.104.2: in a Noetherian local Cohen-Macaulay ring `R`, a
list `xs` of elements of `maximalIdeal R` is a regular sequence if and only if
`ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R`. -/
theorem isRegular_iff_ringKrullDim_quotient_add_length_eq {xs : List R}
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    IsRegular R xs ↔ ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R := by
  constructor
  · intro hreg
    -- The forward implication is the standard dimension formula for a regular sequence.
    simpa using ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg
  · intro hquot
    -- The converse comes from the maximal-extension theorem, then forgetting the added tail.
    obtain ⟨xs', hreg', -⟩ :=
      exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq hxs hquot
    exact isRegular_left_of_isRegular_append (M := R) hreg'

end
