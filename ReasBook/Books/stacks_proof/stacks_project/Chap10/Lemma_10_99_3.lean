import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_99_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing RingTheory
open scoped Pointwise

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => S ⧸ 𝔪S

/- Domain sampling pass:
* primary domain: regular sequences under flat local base change and flatness of the resulting
  quotient rings;
* sampled owner declarations:
  - `RingTheory.Sequence.IsRegular`;
  - `RingTheory.Sequence.isRegular_cons_iff'`;
  - `RingTheory.Sequence.IsRegular.ndrecIterModByRegularWithRing`;
  - `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor`;
* source-facing layer: regularity of the image of `fs` in the closed-fiber quotient `ClosedFiber`;
* core/canonical layer: the owner predicate `RingTheory.Sequence.IsRegular`;
* bridge/view layer: the prefix quotients `S ⧸ Ideal.ofList (fs.take (i + 1))`.

Primitive data vs derived API:
* primitive data: the flat local map `R → S` and the regularity hypothesis on the image sequence in
  `ClosedFiber`, together with the Noetherian hypothesis on `S` needed by the flat-quotient owner
  theorem for each regular element;
* derived API: regularity of `fs` in `S` and flatness of the successive quotient rings.
-/

-- Proof sketch: use the owner induction principle
-- `Sequence.IsRegular.ndrecIterModByRegularWithRing` on the regular sequence in `ClosedFiber`. For
-- the first element, apply `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor` to the head
-- in the closed fiber. Then pass to the quotient by that head and use the inductive
-- characterization of `Sequence.IsRegular` for the tail.
/-- Helper for Lemma 10.99.3: regularity on the owner quotient module `QuotSMulTop r A` is the
same as regularity on the principal ring quotient `A ⧸ Ideal.span {r}` after mapping the tail. -/
private theorem isRegular_quotSMulTop_iff_quotient_span_singleton
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Sequence.IsRegular (QuotSMulTop r A) rs ↔
      Sequence.IsRegular (A ⧸ Ideal.span ({r} : Set A))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  have hspan : Ideal.span ({r} : Set A) = r • (⊤ : Ideal A) := by
    -- The principal ring quotient is the same additive quotient as `A / rA`.
    simp [smul_eq_mul, ← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop r A ≃+ A ⧸ Ideal.span ({r} : Set A) :=
    (Ideal.quotientEquivAlgOfEq A hspan).symm.toRingEquiv.toAddEquiv
  -- Transport regularity through the quotient equivalence while mapping the scalars.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  change e (a • x) = Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a • e x
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  -- On representatives, the scalar action becomes multiplication by the residue class of `a`.
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simp [e, smul_eq_mul]

/-- Helper for Lemma 10.99.3: a ring equivalence transports a regular sequence to the mapped
coefficient list. -/
private theorem isRegular_map_iff_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) (rs : List A) :
    Sequence.IsRegular A rs ↔ Sequence.IsRegular B (rs.map e) := by
  -- For self-modules, scalar compatibility is just preservation of multiplication.
  refine e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  simpa [Algebra.smul_def] using e.map_mul a x

/-- Helper for Lemma 10.99.3: on a commutative ring, scalar-regularity on the regular module gives
regularity of the underlying ring element. -/
private theorem isRegular_of_isSMulRegular_self
    {A : Type u} [CommRing A] {a : A} (h : IsSMulRegular A a) : IsRegular a := by
  -- For the regular module over a commutative ring, scalar multiplication is multiplication.
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at h
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Lemma 10.99.3: regularity of a ring element gives scalar-regularity on the regular
module over that ring. -/
private theorem isSMulRegular_self_of_isRegular
    {A : Type u} [CommRing A] {a : A} (h : IsRegular a) : IsSMulRegular A a := by
  -- In the commutative self-module case, ring regularity is the same injectivity statement.
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at h
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Lemma 10.99.3: after quotienting by the head element, the remaining list ideal is
the image of the full list ideal. -/
private theorem full_tail_quotient_algEquiv_map_eq
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A} {rs : List A} :
    Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) =
      (Ideal.ofList rs).map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) := by
  -- Mapping an ideal generated by a list is the ideal generated by the mapped list.
  rw [Ideal.map_ofList]

/-- Helper for Lemma 10.99.3: quotienting by the head element and then by a mapped tail list is
canonically equivalent, as an `R'`-algebra, to quotienting once by the full list. -/
private noncomputable def full_tail_quotient_algEquiv
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A} {rs : List A} :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃ₐ[R'] A ⧸
      Ideal.ofList (r :: rs) :=
  (Ideal.quotientEquivAlgOfEq R'
      (full_tail_quotient_algEquiv_map_eq (R' := R') (r := r) (rs := rs))).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)).trans
      (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm))

/-- Helper for Lemma 10.99.3: the iterated quotient equivalence sends a doubly-quotiented element
to its class in the single quotient by the full list. -/
@[simp] private theorem full_tail_quotient_algEquiv_apply_mk_mk
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A} {rs : List A}
    (x : A) :
    full_tail_quotient_algEquiv (R' := R') (r := r) (rs := rs)
      (Ideal.Quotient.mk
        (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
        (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x := by
  -- Route correction: compute the composite on the canonical double-quotient generator rather than
  -- relying on `simp` to unfold the intermediate equivalences.
  change
    (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm)
      (DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)
        ((Ideal.quotientEquivAlgOfEq R'
          (full_tail_quotient_algEquiv_map_eq (R' := R') (r := r) (rs := rs)))
          (Ideal.Quotient.mk
            (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
            (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)))) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x
  have hquot :
      DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)
        ((Ideal.quotientEquivAlgOfEq R'
          (full_tail_quotient_algEquiv_map_eq (R' := R') (r := r) (rs := rs)))
          (Ideal.Quotient.mk
            (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
            (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x))) =
        Ideal.Quotient.mk (Ideal.span ({r} : Set A) ⊔ Ideal.ofList rs) x := by
    -- The middle double quotient equivalence is computed by the canonical `quotQuotMk`.
    simpa [DoubleQuot.quotQuotMk] using
      (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk
        (I := Ideal.span ({r} : Set A)) (J := Ideal.ofList rs) x)
  -- Apply the final quotient-by-equality equivalence to move from the sum ideal to `Ideal.ofList`.
  simpa [Ideal.ofList_cons] using
    congrArg (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm) hquot

section

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Flat R S]

/-- Helper for Lemma 10.99.3: quotienting the closed fiber by the image of `f` is the same as
taking the closed fiber after quotienting `S` by `f`. -/
private theorem closedFiber_quotient_by_head_left_map_eq (f : S) :
    Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber) =
      Ideal.map (Ideal.Quotient.mk 𝔪S) (Ideal.span ({f} : Set S)) := by
  -- Mapping the principal ideal generated by `f` produces the principal ideal generated by `f̄`.
  symm
  simpa using Ideal.map_span (f := Ideal.Quotient.mk 𝔪S) ({f} : Set S)

/-- Helper for Lemma 10.99.3: the maximal-ideal fiber ideal after quotienting by `f` is the image
of `𝔪S` in the quotient ring `S ⧸ (f)`. -/
private theorem closedFiber_quotient_by_head_right_map_eq (f : S) :
    Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S))) 𝔪S := by
  -- The quotient algebra map is the composition `R → S → S ⧸ (f)`.
  rw [show algebraMap R (S ⧸ Ideal.span ({f} : Set S)) =
      (Ideal.Quotient.mk (Ideal.span ({f} : Set S))).comp (algebraMap R S) by
        ext x
        rfl]
  exact
    (Ideal.map_map (I := maximalIdeal R)
      (algebraMap R S) (Ideal.Quotient.mk (Ideal.span ({f} : Set S)))).symm

/-- Helper for Lemma 10.99.3: the closed fiber after killing the head element is canonically
identified with the quotient of the old closed fiber by the image of that head. -/
private noncomputable def closedFiber_quotient_by_head_equiv (f : S) :
    (ClosedFiber ⧸ Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber)) ≃+*
      ((S ⧸ Ideal.span ({f} : Set S)) ⧸
        Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R)) := by
  let eLeft :
      (ClosedFiber ⧸ Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber)) ≃+*
        S ⧸ (𝔪S ⊔ Ideal.span ({f} : Set S)) :=
    (Ideal.quotEquivOfEq
      (closedFiber_quotient_by_head_left_map_eq (R := R) (S := S) f)).trans
      (DoubleQuot.quotQuotEquivQuotSup 𝔪S (Ideal.span ({f} : Set S)))
  let eRight :
      ((S ⧸ Ideal.span ({f} : Set S)) ⧸
        Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R)) ≃+*
          S ⧸ (Ideal.span ({f} : Set S) ⊔ 𝔪S) :=
    (Ideal.quotEquivOfEq
      (closedFiber_quotient_by_head_right_map_eq (R := R) (S := S) f)).trans
      (DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({f} : Set S)) 𝔪S)
  -- Both routes identify the same quotient by the sum ideal, up to `sup_comm`.
  exact eLeft.trans ((Ideal.quotEquivOfEq (R := S) (sup_comm 𝔪S (Ideal.span ({f} : Set S)))).trans
    eRight.symm)

/-- Helper for Lemma 10.99.3: the closed-fiber quotient equivalence sends a doubly-quotiented
element to its class in the quotient closed fiber after quotienting by `f`. -/
@[simp] private theorem closedFiber_quotient_by_head_equiv_apply_mk_mk (f x : S) :
    closedFiber_quotient_by_head_equiv (R := R) (S := S) f
      (Ideal.Quotient.mk
      (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber))
      (Ideal.Quotient.mk 𝔪S x)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x) := by
  -- Route correction: rewrite the definition through `DoubleQuot.quotQuotEquivComm`, whose action
  -- on double-quotient generators is a named computation rule.
  change
    (Ideal.quotEquivOfEq (closedFiber_quotient_by_head_right_map_eq (R := R) (S := S) f)).symm
      (DoubleQuot.quotQuotEquivComm 𝔪S (Ideal.span ({f} : Set S))
        ((Ideal.quotEquivOfEq
          (closedFiber_quotient_by_head_left_map_eq (R := R) (S := S) f))
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber))
            (Ideal.Quotient.mk 𝔪S x)))) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)
  rw [Ideal.quotEquivOfEq_mk, DoubleQuot.quotQuotEquivComm_mk_mk, Ideal.quotEquivOfEq_symm]
  change
    (Ideal.quotEquivOfEq (closedFiber_quotient_by_head_right_map_eq (R := R) (S := S) f).symm)
      (Ideal.Quotient.mk
        (Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S))) 𝔪S)
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)
  rw [Ideal.quotEquivOfEq_mk]

/-- Helper for Lemma 10.99.3: splitting a regular closed-fiber sequence at its head yields the
regularity of the mapped tail on the new closed fiber after quotienting by that head. -/
private theorem tail_closedFiber_isRegular_of_cons {f : S} {gs : List S}
    (h : Sequence.IsRegular ClosedFiber ((f :: gs).map (Ideal.Quotient.mk 𝔪S))) :
    Sequence.IsRegular
      ((S ⧸ Ideal.span ({f} : Set S)) ⧸
        Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
      ((gs.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S)))).map
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R)))) := by
  -- Split the closed-fiber regular sequence into the head regularity and the tail regularity on
  -- the quotient by the head.
  have hsplit :
      IsSMulRegular ClosedFiber (Ideal.Quotient.mk 𝔪S f) ∧
        Sequence.IsRegular (QuotSMulTop (Ideal.Quotient.mk 𝔪S f) ClosedFiber)
          (gs.map (Ideal.Quotient.mk 𝔪S)) := by
    simpa [List.map_cons] using
      (RingTheory.Sequence.isRegular_cons_iff ClosedFiber
        (Ideal.Quotient.mk 𝔪S f) (gs.map (Ideal.Quotient.mk 𝔪S))).1 h
  have htail_ring :
      Sequence.IsRegular
        (ClosedFiber ⧸ Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber))
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber))))) := by
    -- Replace the owner quotient module by the principal quotient ring.
    exact
      (isRegular_quotSMulTop_iff_quotient_span_singleton
        (A := ClosedFiber) (r := Ideal.Quotient.mk 𝔪S f)
        (rs := gs.map (Ideal.Quotient.mk 𝔪S))).1 hsplit.2
  have htail_transport :
      Sequence.IsRegular
        ((S ⧸ Ideal.span ({f} : Set S)) ⧸
          Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber)))).map
          (closedFiber_quotient_by_head_equiv (R := R) (S := S) f)) := by
    -- Transport the tail regularity across the closed-fiber quotient equivalence.
    exact
      (isRegular_map_iff_of_ringEquiv
        (closedFiber_quotient_by_head_equiv (R := R) (S := S) f)
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set ClosedFiber)))))).1 htail_ring
  -- Compute the transported list entrywise using the generator formula for the quotient
  -- equivalence.
  simpa [List.map_map] using htail_transport

end

/-- Helper for Lemma 10.99.3: the theorem is proved by induction on the sequence, keeping the
ambient ring variable general so the induction hypothesis can be applied after quotienting by the
head element. -/
private theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular_aux
    {A : Type v} [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsLocalHom (algebraMap R A)] [IsNoetherianRing A] [Module.Flat R A]
    (fs : List A)
    (hfs : Sequence.IsRegular (A ⧸ Ideal.map (algebraMap R A) (maximalIdeal R))
      (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) (maximalIdeal R))))) :
    Sequence.IsRegular A fs ∧
      ∀ i : Fin fs.length, Module.Flat R (A ⧸ Ideal.ofList (fs.take (i + 1))) := by
  let conclusion :
      ∀ n : ℕ,
        ∀ {B : Type v} [CommRing B] [Algebra R B]
          [IsLocalRing B] [IsLocalHom (algebraMap R B)] [IsNoetherianRing B] [Module.Flat R B]
          (gs : List B),
          gs.length = n →
          Sequence.IsRegular (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
            (gs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)))) →
          Sequence.IsRegular B gs ∧
            ∀ i : Fin gs.length, Module.Flat R (B ⧸ Ideal.ofList (gs.take (i + 1))) := by
    intro n
    induction n with
    | zero =>
        intro B _ _ _ _ _ _ gs hlen hgs
        have hnil : gs = [] := by
          simpa using hlen
        subst hnil
        haveI : Nontrivial B := inferInstance
        refine ⟨?_, ?_⟩
        · -- The empty sequence is regular on any nontrivial local ring.
          simpa using (RingTheory.Sequence.IsRegular.nil B B)
        · intro i
          exact Fin.elim0 i
    | succ n ihn =>
        intro B _ _ _ _ _ _ gs hlen hgs
        cases gs with
        | nil =>
            cases hlen
        | cons g hs =>
            have hhs_len : hs.length = n := Nat.succ.inj hlen
            have hsplit :
                IsSMulRegular
                    (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
                    (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g) ∧
                  Sequence.IsRegular
                    (QuotSMulTop
                      (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g)
                      (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R)))
                    (hs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)))) := by
              -- Split the closed-fiber regular sequence into the head and the tail quotient.
              simpa [List.map_cons] using
                (RingTheory.Sequence.isRegular_cons_iff
                  (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
                  (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g)
                  (hs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R))))).1 hgs
            have hhead_regular :
                IsRegular (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g) :=
              isRegular_of_isSMulRegular_self hsplit.1
            -- Lemma 10.99.2 gives the first flat quotient and regularity of the head upstairs.
            obtain ⟨hflat_head, hg_regular⟩ :=
              flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor
                (R := R) (S := B) g hhead_regular
            have htail_closed :
                Sequence.IsRegular
                  ((B ⧸ Ideal.span ({g} : Set B)) ⧸
                    Ideal.map (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) (maximalIdeal R))
                  ((hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))).map
                    (Ideal.Quotient.mk
                      (Ideal.map (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) (maximalIdeal R)))) := by
              -- Re-identify the quotient closed fiber with the quotient of the old closed fiber.
              exact tail_closedFiber_isRegular_of_cons (R := R) (S := B) (f := g) hgs
            let J : Ideal (B ⧸ Ideal.span ({g} : Set B)) :=
              Ideal.map (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) (maximalIdeal R)
            have htail_closed' :
                Sequence.IsRegular ((B ⧸ Ideal.span ({g} : Set B)) ⧸ J)
                  ((hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))).map
                    (Ideal.Quotient.mk J)) := by
              simpa [J] using htail_closed
            letI : Nontrivial ((B ⧸ Ideal.span ({g} : Set B)) ⧸ J) :=
              RingTheory.Sequence.IsRegular.nontrivial htail_closed'
            letI : Nontrivial (B ⧸ Ideal.span ({g} : Set B)) :=
              (Ideal.Quotient.mk_surjective (I := J)).nontrivial
            letI : IsLocalRing (B ⧸ Ideal.span ({g} : Set B)) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))
                Ideal.Quotient.mk_surjective
            letI : IsLocalHom (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) := by
              let hquot :
                  IsLocalHom (Ideal.Quotient.mk (Ideal.span ({g} : Set B))) :=
                IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
              let hcomp :
                  IsLocalHom ((Ideal.Quotient.mk (Ideal.span ({g} : Set B))).comp
                    (algebraMap R B)) := by
                infer_instance
              change IsLocalHom ((Ideal.Quotient.mk (Ideal.span ({g} : Set B))).comp
                (algebraMap R B))
              exact hcomp
            letI : Module.Flat R (B ⧸ Ideal.span ({g} : Set B)) := hflat_head
            have hrec :=
              ihn (B := B ⧸ Ideal.span ({g} : Set B))
                (gs := hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B))))
                (by simpa [hhs_len]) htail_closed'
            have htail_module : Sequence.IsRegular (QuotSMulTop g B) hs := by
              -- Move the recursive regularity statement back to the owner quotient module.
              exact
                (isRegular_quotSMulTop_iff_quotient_span_singleton
                  (A := B) (r := g) (rs := hs)).2 hrec.1
            have hregular_cons : Sequence.IsRegular B (g :: hs) := by
              -- Reassemble the sequence from the regular head and the regular tail quotient.
              exact
                (RingTheory.Sequence.isRegular_cons_iff B g hs).2
                  ⟨isSMulRegular_self_of_isRegular hg_regular, htail_module⟩
            refine ⟨hregular_cons, ?_⟩
            intro i
            refine Fin.cases ?_ ?_ i
            · -- The first prefix quotient is exactly the principal quotient handled by Lemma 10.99.2.
              change Module.Flat R (B ⧸ Ideal.ofList [g])
              rw [Ideal.ofList_singleton]
              exact hflat_head
            · intro j
              let j' :
                  Fin (List.length (hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B))))) :=
                ⟨j.1, by simpa using j.2⟩
              have hflat_tail' :
                  Module.Flat R
                    ((B ⧸ Ideal.span ({g} : Set B)) ⧸
                      Ideal.ofList
                        ((hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))).take
                          (j' + 1))) :=
                hrec.2 j'
              have htake :
                  (hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))).take (j' + 1) =
                    (hs.take (j + 1)).map (Ideal.Quotient.mk (Ideal.span ({g} : Set B))) := by
                simpa [j'] using
                  (List.map_take (Ideal.Quotient.mk (Ideal.span ({g} : Set B))) (j + 1) hs).symm
              have hflat_tail :
                  Module.Flat R
                    ((B ⧸ Ideal.span ({g} : Set B)) ⧸
                      Ideal.ofList
                        ((hs.take (j + 1)).map
                          (Ideal.Quotient.mk (Ideal.span ({g} : Set B))))) := by
                -- Rewrite the recursive flatness clause into the literal quotient by the taken tail.
                rw [← htake]
                exact hflat_tail'
              letI :
                  Module.Flat R
                    ((B ⧸ Ideal.span ({g} : Set B)) ⧸
                      Ideal.ofList
                        ((hs.take (j + 1)).map
                          (Ideal.Quotient.mk (Ideal.span ({g} : Set B))))) := hflat_tail
              have hflat_full :
                  Module.Flat R (B ⧸ Ideal.ofList (g :: hs.take (j + 1))) := by
                -- Transport flatness from the iterated quotient to the single quotient by the full
                -- prefix through the canonical quotient equivalence.
                exact Module.Flat.of_linearEquiv
                  (full_tail_quotient_algEquiv
                    (R' := R) (r := g) (rs := hs.take (j + 1))).toLinearEquiv.symm
              -- The successor prefix in `(g :: hs)` is definitionally `g :: hs.take (j + 1)`.
              change Module.Flat R (B ⧸ Ideal.ofList (g :: hs.take (j + 1)))
              exact hflat_full
  exact conclusion fs.length fs rfl hfs

/-- Lemma 10.99.3: if `R → S` is a flat local homomorphism of local rings, `S` is Noetherian, and
the images of a finite sequence `fs` in the closed fibre `S / 𝔪S`, where `𝔪` is the maximal ideal
of `R`, form a regular sequence, then `fs` is a regular sequence in `S`, and each quotient by a
nonempty initial segment of `fs` is flat over `R`. -/
@[stacks 00MG]
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (Ideal.Quotient.mk 𝔪S))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := by
  -- Apply the generalized induction theorem to the original ambient ring `S`.
  exact
    isRegular_and_flat_quotient_take_of_closedFiber_isRegular_aux
      (R := R) (A := S) fs hfs

end
