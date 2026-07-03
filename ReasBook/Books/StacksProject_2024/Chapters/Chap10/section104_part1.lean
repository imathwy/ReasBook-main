import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_104_1 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain-style sampling for the Cohen-Macaulay local-ring condition:
- primary domain: Cohen-Macaulay modules and their self-module specialization over Noetherian
  local rings;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `Module.MaximalCohenMacaulay`,
  `Module.LocallyCohenMacaulay`;
- best owner abstraction: `Module.CohenMacaulay R R`;
- primitive data: exactly the owner data already carried by `Module.CohenMacaulay R R`;
- derived API: the field projection
  `Module.CohenMacaulay.supportDim_eq_moduleDepth` and the later global owner
  `Module.LocallyCohenMacaulay R R`.

Source/core/bridge triage:
* source-facing: Definition 10.104.1 is the local-ring specialization of the Cohen-Macaulay
  module condition;
* core/canonical: `Module.CohenMacaulay R R`;
* bridge/view: none, since the source item adds no extra data beyond the self-module
  specialization.

A separate ring-level alias here would only duplicate the owner abstraction and create a parallel
API surface.
-/
/- Definition 10.104.1: a Noetherian local ring is Cohen-Macaulay if it is Cohen-Macaulay as a
module over itself. -/
#check (Module.CohenMacaulay R R)

end

/-! ### Lemma_10_104_2 (from Chap10) -/
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

/-! ### Lemma_10_104_3 (from Chap10) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling for the prime-chain statement:
- primary domain: Cohen-Macaulay modules over Noetherian local rings, specialized to the
  self-module `R`;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay`,
  `Module.support_of_algebra`,
  `Module.supportDim_self_eq_ringKrullDim`;
- best owner abstraction: `Module.CohenMacaulay R R`;
- primitive data: the owner hypothesis `hCM : Module.CohenMacaulay R R`;
- derived API: full support of the self-module and the maximal-chain length theorem for a
  Cohen-Macaulay module with full support.

Source/core/bridge triage:
* source-facing: this lemma is the textbook self-module specialization for Cohen-Macaulay local
  rings;
* core/canonical: `ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay`;
* bridge/view: the canonical self-support fact `Module.support R R = Set.univ`.
-/
-- Proof sketch: this is the self-module specialization of Lemma `10.103.9`. The hypothesis `hCM`
-- is the self-module Cohen-Macaulay owner `Module.CohenMacaulay R R`; the support of the
-- self-module is all of `Spec R`, so the general maximal-chain statement applies directly.
/-- Lemma 10.104.3: if `R` is a Noetherian local Cohen-Macaulay ring, then every maximal chain of
prime ideals of `R`, encoded as an `LTSeries` with maximal range, has length `ringKrullDim R`. -/
theorem length_maximal_prime_chain_eq_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    p.length = ringKrullDim R := by
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  simpa using
    (ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay
      hCM hsupp p hp).symm

end

/-! ### Lemma_10_104_4 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: Krull-dimension formulas for Cohen-Macaulay local rings, viewed as the
  self-module specialization of the general Cohen-Macaulay module theorem;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay`,
  `Module.support_of_algebra`,
  `CohenMacaulayRing`;
* best owner abstraction: `Module.CohenMacaulay R R`;
* primitive data: the ambient local Noetherian ring, the self-module owner hypothesis
  `hCM : Module.CohenMacaulay R R`, and the prime ideal `p`;
* derived API: the full-support fact for the self-module, obtained canonically from
  `Module.support_of_algebra`.

Source/core/bridge triage:
* source-facing: the textbook dimension formula for a Cohen-Macaulay local ring;
* core/canonical: `Module.CohenMacaulay R R` together with the general module theorem
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay`;
* bridge/view: the self-support identification `Module.support R R = Set.univ`.

The later class `CohenMacaulayRing` is not the owner abstraction for this local statement: it is a
global ring property introduced later in the chapter. This file should stay a thin source-facing
self-module specialization of the earlier owner theorem, not a second ring-level owner. -/

-- Proof sketch: specialize Lemma `10.103.10` to the self-module `M = R`. The hypothesis
-- `hCM : Module.CohenMacaulay R R` is exactly the Cohen-Macaulay condition for this module, and
-- the self-module `R` has full support, so the general dimension formula yields the claimed
-- equality.
/-- Lemma 10.104.4: if `R` is a Noetherian local Cohen-Macaulay ring, then for every prime ideal
`p` of `R` the dimension of `R` is the sum of the dimensions of the localization `Rₚ` and the
quotient `R / p`. -/
theorem ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := by
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  exact ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
    hCM hsupp p

end

/-! ### Lemma_10_104_5 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

namespace Module.CohenMacaulay

/- Domain-style sampling:
* primary domain: Cohen-Macaulay rings/modules under localization in commutative algebra;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.localizedModule_atPrime`,
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`;
* best owner abstraction: the earlier chapter owner `Module.CohenMacaulay R R`;
* primitive data: the local Noetherian ring `R` together with the self-module owner instance
  `[Module.CohenMacaulay R R]`;
* derived API: the localized self-module statement, obtained canonically from
  `Module.CohenMacaulay.localizedModule_atPrime`.

Source/core/bridge triage:
* source-facing: the textbook local-ring statement that a Cohen-Macaulay local ring stays
  Cohen-Macaulay after localization at a prime ideal;
* core/canonical: `Module.CohenMacaulay` together with the earlier localization theorem
  `Module.CohenMacaulay.localizedModule_atPrime`;
* bridge/view: the present theorem, which is only the self-module specialization of that owner
  theorem.
-/

variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p

-- Proof sketch: specialize `Module.CohenMacaulay.localizedModule_atPrime` to the self-module
-- `M = R`. The source-facing local-ring statement is exactly this thin specialization, so no
-- later ring-level wrapper is needed.
/-- Lemma 10.104.5: if `R` is a Cohen-Macaulay local ring and `p` is a prime ideal of `R`, then
the localization `Rₚ` is Cohen-Macaulay. -/
theorem cohenMacaulay_localizationAtPrime_self : Module.CohenMacaulay Rₚ Rₚ := by
  simpa using localizedModule_atPrime p

end Module.CohenMacaulay

end

/-! ### Definition_10_104_6 (from Chap10) -/
universe u

open PrimeSpectrum
open scoped ENat

section

variable (R : Type u) [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `CohenMacaulayRing R`, the textbook global ring notion;
* core/canonical: `Module.LocallyCohenMacaulay R R`, the chapter owner saying the self-module is
  Cohen-Macaulay after localization at every prime;
* bridge/view: the self-module specialization of `Module.CohenMacaulay` on each localized ring.

Primitive data are exactly the Noetherian hypothesis together with the owner class
`Module.LocallyCohenMacaulay R R`. The old primewise depth-equals-dimension field was duplicate
derived API for the self-module, so it should be recovered from the owner abstraction rather than
stored as primitive public data.
-/
/-- Definition 10.104.6: a ring is Cohen-Macaulay if it is Noetherian and every localization at a
prime ideal is a Cohen-Macaulay local ring. -/
class CohenMacaulayRing : Prop extends IsNoetherianRing R, Module.LocallyCohenMacaulay R R

/-- A Cohen-Macaulay ring is Noetherian. -/
instance isNoetherianRing_of_cohenMacaulayRing [h : CohenMacaulayRing R] : IsNoetherianRing R :=
  h.toIsNoetherian

/-- Every localization of a Cohen-Macaulay ring is a Cohen-Macaulay self-module. -/
theorem localizedRing_cohenMacaulay (p : PrimeSpectrum R) [h : CohenMacaulayRing R] :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  simpa using h.toLocallyCohenMacaulay.localizedModule_cohenMacaulay p

/-- Every localization of a Cohen-Macaulay ring satisfies the depth-equals-dimension condition. -/
theorem localizedRing_moduleDepth_eq_ringKrullDim (p : PrimeSpectrum R) [h : CohenMacaulayRing R] :
    WithBot.some (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact (localizedRing_cohenMacaulay R p).supportDim_eq_moduleDepth.symm

namespace CohenMacaulayRing

/-- A Cohen-Macaulay ring satisfies LinearRepresentations_Serre_1977's condition `(S_k)` for every `k`. -/
theorem serreConditionS (k : ℕ) [h : CohenMacaulayRing R] : SerreConditionS R k := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  rw [Module.supportDim_self_eq_ringKrullDim, localizedRing_moduleDepth_eq_ringKrullDim R p]
  exact min_le_right _ _

/-- A Noetherian ring is Cohen-Macaulay if it satisfies LinearRepresentations_Serre_1977's condition `(S_k)` for every
`k`. -/
theorem of_serreConditionS [IsNoetherianRing R] (hS : ∀ k : ℕ, SerreConditionS R k) :
    CohenMacaulayRing R := by
  refine
    { toIsNoetherian := inferInstance
      toLocallyCohenMacaulay := ?_ }
  refine
    { toFinite := inferInstance
      localizedModule_cohenMacaulay := ?_ }
  intro p
  let h := p.asIdeal.height
  have hp : h ≠ ⊤ := by
    simpa [h] using Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  let k := h.toNat
  let _ : SerreConditionS R k := hS k
  refine Module.CohenMacaulay.mk ?_
  have hdepth_ge :
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≥
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    have hserre :=
      SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) (k := k)
        (h := inferInstance) p
    have hdim :
        ringKrullDim (Localization.AtPrime p.asIdeal) = (k : WithBot ℕ∞) := by
      calc
        ringKrullDim (Localization.AtPrime p.asIdeal) = ↑p.asIdeal.height := by
          simpa using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
              (Localization.AtPrime p.asIdeal))
        _ = k := by
          simpa [h, k] using
            congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hp).symm
    simpa [hdim] using hserre
  have hdepth_le :
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≤
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact depth_le_supportDim
  rw [Module.supportDim_self_eq_ringKrullDim]
  exact (le_antisymm hdepth_le hdepth_ge).symm

end CohenMacaulayRing

end

/-! ### Lemma_10_104_7 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

open RingTheory Sequence
open scoped ENat TensorProduct

section

variable {R : Type u} [CommRing R]

private theorem regularSequenceLengths_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem ideal_depth_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) : Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

private theorem Module.CohenMacaulay.of_linearEquiv [IsLocalRing R] [IsNoetherianRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [h : Module.CohenMacaulay R M] : Module.CohenMacaulay R N := by
  let _ : Module.Finite R N := Module.Finite.equiv e
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e, h.supportDim_eq_moduleDepth]⟩

private theorem Module.LocallyCohenMacaulay.of_linearEquiv [IsNoetherianRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [h : Module.LocallyCohenMacaulay R M] : Module.LocallyCohenMacaulay R N := by
  let _ : Module.Finite R N := Module.Finite.equiv e
  exact ⟨fun p ↦ by
    let ep : LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal N :=
      LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
        ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
          LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
    let _ :
        Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :=
      h.localizedModule_cohenMacaulay p
    exact Module.CohenMacaulay.of_linearEquiv ep⟩

-- Proof sketch: view a Cohen-Macaulay ring as a locally Cohen-Macaulay self-module, apply
-- `Module.LocallyCohenMacaulay.mvPolynomial` with `M = R`, and translate the resulting local
-- self-module statement back to the owner class `CohenMacaulayRing` for the polynomial ring using
-- the canonical `MvPolynomial (Fin n) R ⊗[R] R ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) R`.
/-- Lemma 10.104.7: if `R` is a Noetherian Cohen-Macaulay ring, then every finite polynomial ring
`R[x₁, …, xₙ]`, represented by `MvPolynomial (Fin n) R`, is Cohen-Macaulay. -/
theorem cohenMacaulayRing_mvPolynomial (hCM : CohenMacaulayRing R) (n : ℕ) :
    CohenMacaulayRing (MvPolynomial (Fin n) R) := by
  let _ : CohenMacaulayRing R := hCM
  let S := MvPolynomial (Fin n) R
  let _ : Module.LocallyCohenMacaulay S (S ⊗[R] R) :=
    Module.LocallyCohenMacaulay.mvPolynomial (inferInstance : Module.LocallyCohenMacaulay R R) n
  let _ : Module.LocallyCohenMacaulay S S :=
    Module.LocallyCohenMacaulay.of_linearEquiv (Algebra.TensorProduct.rid R S S).toLinearEquiv
  exact CohenMacaulayRing.mk

end

/-! ### Lemma_10_104_8 (from Chap10) -/
universe u

open CategoryTheory

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}

/-- Helper for Lemma 10.104.8: a linear equivalence preserves the set of regular-sequence lengths
in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and reverse the argument.
  ext n
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.104.8: ideal depth is invariant under a linear equivalence of finite
modules. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The branch `I • M = M` is preserved by the equivalence, and otherwise the same
  -- regular-sequence lengths compute the depth on both sides.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

/-- Helper for Lemma 10.104.8: a linear equivalence preserves module depth for finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Specialize ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (IsLocalRing.maximalIdeal R) e

/-- Helper for Lemma 10.104.8: a finite subsingleton module has depth `⊤`. -/
private theorem moduleDepth_eq_top_of_subsingleton (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a zero module, `𝔪 • M = M`, so the depth definition lands in the top branch.
  have htopbot : (⊤ : Submodule R M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : IsLocalRing.maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext x
    simp
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htopbot, hsmul_bot]
  change Ideal.depth (IsLocalRing.maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal R) M hsmul

/-- Helper for Lemma 10.104.8: a Cohen-Macaulay local ring is nontrivial. -/
private theorem nontrivial_of_cohenMacaulay_self (hCM : Module.CohenMacaulay R R) : Nontrivial R := by
  by_contra hR
  letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
  have hsupp : Module.supportDim R R = ⊥ :=
    Module.supportDim_eq_bot_of_subsingleton (R := R) (M := R)
  have hdepth : Module.supportDim R R = .some (moduleDepth R R) := hCM.supportDim_eq_moduleDepth
  simpa [hsupp] using hdepth

/-- Helper for Lemma 10.104.8: a nonzero finite module has depth at most the ambient Krull
dimension. -/
private theorem moduleDepth_le_ringKrullDim_of_nontrivial {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] {d : ℕ} (hdim : ringKrullDim R = d) :
    moduleDepth R M ≤ d := by
  -- Combine the standard depth-support inequality with the support-dimension upper bound.
  have hdepth :
      WithBot.some (moduleDepth R M : ℕ∞) ≤ Module.supportDim R M :=
    depth_le_supportDim (R := R) (M := M)
  have hsupp : Module.supportDim R M ≤ ringKrullDim R :=
    Module.supportDim_le_ringKrullDim (R := R) (M := M)
  have hle : WithBot.some (moduleDepth R M : ℕ∞) ≤ d := by
    exact le_trans hdepth (by simpa [hdim] using hsupp)
  exact WithBot.coe_le_coe.mp hle

/-- Helper for Lemma 10.104.8: the self-module of a Cohen-Macaulay local ring has depth equal to
the Krull dimension. -/
private theorem moduleDepth_self_eq_ringKrullDim {d : ℕ}
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R R = d := by
  -- Rewrite the Cohen-Macaulay self-module equality in the ring-dimension normalization.
  have hdepth : WithBot.some (moduleDepth R R : ℕ∞) = d := by
    simpa [Module.supportDim_self_eq_ringKrullDim, hdim] using hCM.supportDim_eq_moduleDepth.symm
  exact WithBot.coe_eq_coe.mp hdepth

/-- Helper for Lemma 10.104.8: the numerical endgame behind the depth trichotomy is an elementary
fact about natural numbers. -/
private theorem strict_gt_or_both_eq_dim_of_ge_min_succ_nat {a b d : ℕ}
    (hmin : min d (b + 1) ≤ a) (ha : a ≤ d) (hb : b ≤ d) :
    a > b ∨ (a = d ∧ b = d) := by
  -- Separate the quotient depth according to whether it already reaches the ambient dimension.
  rcases lt_or_eq_of_le hb with hb_lt | hb_eq
  · left
    have hsucc : b + 1 ≤ d := Nat.succ_le_of_lt hb_lt
    have hba : b + 1 ≤ a := by
      calc
        b + 1 = min d (b + 1) := (Nat.min_eq_right hsucc).symm
        _ ≤ a := hmin
    exact lt_of_lt_of_le (Nat.lt_succ_self b) hba
  · right
    have hd_le : d ≤ a := by
      simpa [hb_eq] using hmin
    exact ⟨le_antisymm ha hd_le, hb_eq⟩

/-- Helper for Lemma 10.104.8: a finite free module with `n + 1` generators has depth equal to
the ambient Cohen-Macaulay dimension. -/
private theorem moduleDepth_piFinSucc_eq_ringKrullDim {d : ℕ} (n : ℕ)
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R (Fin n.succ → R) = d := by
  have hRdepth : moduleDepth R R = d := moduleDepth_self_eq_ringKrullDim (R := R) hCM hdim
  haveI : Nontrivial R := nontrivial_of_cohenMacaulay_self (R := R) hCM
  induction n with
  | zero =>
      -- `Fin 1 → R` is linearly equivalent to `R` itself.
      simpa [hRdepth] using
        (moduleDepth_eq_of_linearEquiv (R := R)
          (M := Fin 1 → R) (N := R) (LinearEquiv.funUnique (Fin 1) R R))
  | succ n ih =>
      let T : ShortComplex (ModuleCat R) :=
        ModuleCat.shortComplexOfCompEqZero
          (LinearMap.inl R R (Fin n.succ → R))
          (LinearMap.snd R R (Fin n.succ → R))
          (by ext x <;> rfl)
      have hT : T.ShortExact :=
        ModuleCat.shortComplex_shortExact T
          Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      -- The split exact sequence `0 → R → R × R^n → R^n → 0` forces the middle depth up to `d`.
      have hmid_ge : moduleDepth R (R × (Fin n.succ → R)) ≥ d := by
        have hmiddle := moduleDepth_middle_ge_min (R := R) (S := T) hT
        simpa [T, hRdepth, ih] using hmiddle
      -- The general support-dimension estimate gives the complementary upper bound.
      have hmid_le : moduleDepth R (R × (Fin n.succ → R)) ≤ d :=
        moduleDepth_le_ringKrullDim_of_nontrivial (R := R)
          (M := R × (Fin n.succ → R)) hdim
      have hmid : moduleDepth R (R × (Fin n.succ → R)) = d := le_antisymm hmid_le hmid_ge
      -- Transport the product calculation back to the standard `Fin`-indexed model.
      calc
        moduleDepth R (Fin n.succ.succ → R)
            = moduleDepth R (R × (Fin n.succ → R)) := by
              symm
              exact moduleDepth_eq_of_linearEquiv (R := R)
                (M := R × (Fin n.succ → R)) (N := Fin n.succ.succ → R)
                (Fin.consLinearEquiv R (fun _ : Fin n.succ.succ => R))
        _ = d := hmid

/-- Helper for Lemma 10.104.8: every nonzero finite free finite module over a Cohen-Macaulay local
ring has depth equal to the ambient Krull dimension. -/
private theorem moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free {d : ℕ} {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P] [Nontrivial P]
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R P = d := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex R P) R P := Module.Free.chooseBasis R P
  let ι := Module.Free.ChooseBasisIndex R P
  letI : Finite ι := Module.Finite.finite_basis b
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let eBasis : (ι → R) ≃ₗ[R] P := b.equivFun.symm
  let eFin : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin ι)
  have hι_nonempty : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      have : eBasis.symm x = eBasis.symm y := Subsingleton.elim _ _
      exact eBasis.symm.injective this
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hcard_ne_zero : Fintype.card ι ≠ 0 := Nat.ne_of_gt (Fintype.card_pos_iff.mpr hι_nonempty)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard_ne_zero
  -- Choose finite coordinates for the free module and invoke the `Fin`-indexed computation.
  calc
    moduleDepth R P = moduleDepth R (ι → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv (R := R) (M := ι → R) (N := P) eBasis
    _ = moduleDepth R (Fin (Fintype.card ι) → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv (R := R)
        (M := Fin (Fintype.card ι) → R) (N := ι → R) eFin
    _ = d := by
      have hfin : moduleDepth R (Fin (Fintype.card ι) → R) = d := by
        rw [hn]
        exact moduleDepth_piFinSucc_eq_ringKrullDim (R := R) (d := d) n hCM hdim
      exact hfin

/-
Domain-style sampling:
* primary domain: module depth in short exact sequences over Noetherian local Cohen-Macaulay rings;
* sampled owner declarations:
  `moduleDepth`,
  `Module.CohenMacaulay`,
  `Module.Free`,
  `Module.Finite`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min`;
* best owner abstraction: the short exact complex `S` with `hS : S.ShortExact`; the finite free
  middle term is expressed intrinsically by `[Module.Free R S.X₂]` and
  `[Module.Finite R S.X₂]`;
* source/core/bridge triage:
  this theorem remains `source-facing`, because it records the special trichotomy for an exact
  sequence whose middle term is finite free over a Cohen-Macaulay local ring;
  the exact-sequence data itself is `core/canonical`, carried by `hS : S.ShortExact`;
  any coordinate identification of `S.X₂` with a finite product of copies of `R` is only the
  `bridge/view`, obtained internally from `Module.Free.chooseBasis R S.X₂`;
* primitive data: `hS`, the Cohen-Macaulay owner hypothesis `hCM : Module.CohenMacaulay R R`, the
  dimension equality `hdim`, and the intrinsic finite-free owner data on `S.X₂`;
* derived API: `S.X₃` is finite because it is a quotient of the finite middle term, and then `S.X₁`
  is finite by the canonical exact-sequence owner theorem `Module.Finite.of_exact_of_finitePresentation`;
  the depth comparisons belong to the existing owner lemmas from Lemma `10.72.6`, while any basis
  choice and transfer of depth across the resulting linear equivalence are proof-level derived data.
-/

-- Proof sketch: if `S.X₃ = 0`, this is the first alternative. Otherwise `S.X₂` is nonzero because
-- `hS.moduleCat_surjective_g` is onto. Choose a basis of the finite free module `S.X₂`, whose
-- finite index type is derived from `[Module.Finite R S.X₂]`, and use the induced linear
-- equivalence with a finite product of copies of `R` to identify `moduleDepth R S.X₂` with `d`
-- from `hCM` and `hdim`. Then apply the canonical short-exact depth inequalities from
-- Lemma `10.72.6` to compare `moduleDepth R S.X₁` and `moduleDepth R S.X₃`, obtaining either a
-- strict increase or equality at the top value `d`.
/-- Lemma 10.104.8: let `R` be a Noetherian local Cohen-Macaulay ring of dimension `d`, and let
`0 → K → P → M → 0` be a short exact sequence of `R`-modules with `P` finite free. In the
chapter's canonical owner language, this is a short exact complex `S` whose middle term `S.X₂`
carries `[Module.Free R S.X₂]` and `[Module.Finite R S.X₂]`; the endpoint finiteness needed for
`moduleDepth` is derived internally from `hS`. Then either `M = 0`, or `depth(K) > depth(M)`, or
`depth(K) = depth(M) = d`. -/
theorem moduleDepth_kernel_trichotomy_of_exact_free_over_cohenMacaulayLocalRing
    {d : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hS : S.ShortExact) [Module.Free R S.X₂] [Module.Finite R S.X₂] :
    letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
    letI : Module.Finite R S.X₁ := by
      letI : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_finite R S.X₃
      exact Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
        ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    Subsingleton S.X₃ ∨ moduleDepth R S.X₁ > moduleDepth R S.X₃ ∨
      (moduleDepth R S.X₁ = d ∧ moduleDepth R S.X₃ = d) := by
  classical
  letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
  letI : Module.Finite R S.X₁ := by
    letI : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_finite R S.X₃
    exact Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
      ((moduleCat_exact_iff_function_exact S).mp hS.exact)
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, the first alternative is exactly the claim.
    exact Or.inl hX₃
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the kernel vanishes while the quotient is nonzero, its depth is `⊤`, hence strictly
    -- larger than the finite quotient depth.
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₃_le : moduleDepth R S.X₃ ≤ d :=
      moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₃) hdim
    right
    left
    rw [hdepth₁]
    exact lt_top_iff_ne_top.mpr <|
      ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₃_le
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₂ := Function.Surjective.nontrivial hS.moduleCat_surjective_g
  -- Compute the finite free middle term's depth from the Cohen-Macaulay hypothesis on `R`.
  have hdepth₂ : moduleDepth R S.X₂ = d :=
    moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free (R := R) (P := S.X₂) hCM hdim
  -- The left-hand depth lemma is the promised special case of Lemma `10.72.6`.
  have hleft : min (d : ℕ∞) (moduleDepth R S.X₃ + 1) ≤ moduleDepth R S.X₁ := by
    have hleft' := moduleDepth_left_ge_min (R := R) (S := S) hS
    simpa [hdepth₂] using hleft'
  -- Both nonzero endpoint depths are finite and bounded by the ambient dimension.
  have hdepth₁_le : moduleDepth R S.X₁ ≤ d :=
    moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₁) hdim
  have hdepth₃_le : moduleDepth R S.X₃ ≤ d :=
    moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₃) hdim
  have hdepth₁_ne_top : moduleDepth R S.X₁ ≠ ⊤ :=
    ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₁_le
  have hdepth₃_ne_top : moduleDepth R S.X₃ ≠ ⊤ :=
    ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₃_le
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hdepth₁_ne_top
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hdepth₃_ne_top
  have hmin_nat : min d (b + 1) ≤ a := by
    exact WithTop.coe_le_coe.mp (by simpa [ha, hb] using hleft)
  have ha_le : a ≤ d := by
    exact WithTop.coe_le_coe.mp (by simpa [ha] using hdepth₁_le)
  have hb_le : b ≤ d := by
    exact WithTop.coe_le_coe.mp (by simpa [hb] using hdepth₃_le)
  -- The remaining trichotomy is pure arithmetic on the finite depth values.
  rcases strict_gt_or_both_eq_dim_of_ge_min_succ_nat hmin_nat ha_le hb_le with hgt | ⟨ha_eq, hb_eq⟩
  · right
    left
    change moduleDepth R S.X₃ < moduleDepth R S.X₁
    rw [← hb, ← ha]
    exact WithTop.coe_lt_coe.mpr hgt
  · right
    right
    refine ⟨?_, ?_⟩
    · calc
        moduleDepth R S.X₁ = (a : ℕ∞) := ha.symm
        _ = d := by exact_mod_cast ha_eq
    · calc
        moduleDepth R S.X₃ = (b : ℕ∞) := hb.symm
        _ = d := by exact_mod_cast hb_eq

end

end ShortExact
end ShortComplex
end CategoryTheory

/-! ### Lemma_10_104_9 (from Chap10) -/
open CategoryTheory ChainComplex

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: finite free resolutions and maximal Cohen-Macaulay syzygies over Noetherian
  local Cohen-Macaulay rings;
* sampled owner declarations:
  `module_exists_finite_free_resolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `Module.MaximalCohenMacaulay`,
  `Module.CohenMacaulay`;
* best owner abstraction: a chosen finite free resolution
  `π : F ⟶ moduleSingle[R] M`, together with the textbook syzygy indexing convention;
* source/core/bridge triage:
  `ChainComplex.SyzygyMaximalCohenMacaulay` is the source-facing owner predicate for the textbook
  `(d - e)`th syzygy of an augmented free resolution;
  `ChainComplex.IsFiniteFreeResolution π` is the canonical owner of the chosen finite free
  resolution data;
  the main theorem is the source-facing existence statement obtained by choosing such a
  resolution and proving the chosen-resolution helper below.
-/

namespace ChainComplex

/-- The `n`th syzygy of an augmentation `π : F ⟶ moduleSingle[R] M` is maximal Cohen-Macaulay,
with the chapter's indexing convention: degree `0` is `M`, degree `1` is the augmentation kernel,
and degree `n + 2` is the kernel of the differential `F.X (n + 1) ⟶ F.X n`. -/
def SyzygyMaximalCohenMacaulay {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : Prop :=
  match n with
  | 0 => Module.MaximalCohenMacaulay R M
  | 1 => Module.MaximalCohenMacaulay R (LinearMap.ker (π.f 0).hom)
  | n + 2 => Module.MaximalCohenMacaulay R (LinearMap.ker (F.d (n + 1) n).hom)

end ChainComplex

/-- Helper for Lemma 10.104.9: every chosen finite free resolution has maximal Cohen-Macaulay
`(d - e)`th syzygy when `moduleDepth R M = e`. -/
private theorem isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    ChainComplex.SyzygyMaximalCohenMacaulay π (d - e) :=
  -- TODO: follow the source-faithful route by iterating Lemma 10.104.8 along the short exact
  -- syzygy sequences inside a chosen finite free resolution until the depth reaches `d`.
  sorry

-- Proof sketch: choose any finite free resolution of `M`, then invoke the chosen-resolution
-- helper above to obtain the maximal Cohen-Macaulay syzygy at the source-prescribed stage.
/-- Lemma 10.104.9: if `R` is a local Noetherian Cohen-Macaulay ring of dimension `d` and `M` is
a finite `R`-module of depth `e`, then `M` admits a finite free resolution whose `(d - e)`th
syzygy is maximal Cohen-Macaulay. Equivalently, truncating that resolution after `d - e` steps
gives an exact complex
`0 → K → F_{d - e - 1} → ⋯ → F₀ → M → 0`
with the `Fᵢ` finite free and `K` maximal Cohen-Macaulay. With the chapter's convention, the `0`th
syzygy is `M` itself, the `1`st syzygy is `ker (F₀ ⟶ M)`, and the `(n + 2)`nd syzygy is
`ker (F_{n+1} ⟶ F_n)`. -/
theorem exists_maximalCohenMacaulay_syzygy_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
      IsFiniteFreeResolution π ∧
      SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Choose a finite free resolution and transfer the remaining work to the chosen-resolution
  -- helper.
  rcases module_exists_finite_free_resolution (R := R) (M := M) with ⟨F, π, hπ⟩
  refine ⟨F, π, hπ, ?_⟩
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

/-- Companion form of Lemma 10.104.9 for a chosen finite free resolution: every finite free
resolution of `M` has maximal Cohen-Macaulay `(d - e)`th syzygy. -/
theorem maximalCohenMacaulay_syzygy_of_isFiniteFreeResolution_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Reuse the private chosen-resolution helper directly; this is the source-facing fixed
  -- resolution form of the lemma.
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

end
