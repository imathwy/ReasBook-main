import stacks_proof.stacks_project.Chap10.Lemma_10_128_5
import stacks_proof.stacks_project.Chap10.Lemma_10_52_13
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing RingTheory
open scoped Pointwise

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

/- Domain-style sampling for Lemma 10.128.6:
- primary domain: regular sequences on the canonical closed fiber of a flat local map, together
  with flatness of the successive quotient rings over the base;
- sampled owner declarations:
  `Ideal.Fiber`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff'`,
  `flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation`,
  `isRegular_and_flat_quotient_take_of_closedFiber_isRegular`;
- best owner abstraction: the core owner is the regular-sequence predicate
  `RingTheory.Sequence.IsRegular` on the canonical fiber ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the quotient-by-prefix rings
  `S ⧸ Ideal.ofList (fs.take (i + 1))` are derived bridge data;
- primitive data: the flat local map `R → S`, the essential finite presentation hypothesis
  `RingHom.EssFinitePresentation (algebraMap R S)`, and regularity of the image sequence in the
  canonical closed fiber under `algebraMap S ClosedFiber`;
- derived API: regularity of `fs` in `S` and flatness of the nonempty prefix quotients over `R`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for sequences regular on the closed fiber;
- `core/canonical`: `Ideal.Fiber`, `RingTheory.Sequence.IsRegular`,
  `RingHom.EssFinitePresentation`, and `Module.Flat`;
- `bridge/view`: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of `ClosedFiber`, together with the explicit
  quotient rings `S ⧸ Ideal.ofList (fs.take (i + 1))`.
-/

/-- Helper for Chap10 Lemma 10 128 6: scalar-regularity on the regular module over a commutative
ring is ordinary regularity of the element. -/
private theorem isRegular_of_isSMulRegular_self
    {A : Type u} [CommRing A] {a : A} (h : IsSMulRegular A a) :
    IsRegular a := by
  -- Proof comment: for the self-module, scalar multiplication is ring multiplication.
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at h
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Chap10 Lemma 10 128 6: ordinary regularity of an element gives scalar-regularity
on the regular module over a commutative ring. -/
private theorem isSMulRegular_self_of_isRegular
    {A : Type u} [CommRing A] {a : A} (h : IsRegular a) :
    IsSMulRegular A a := by
  -- Proof comment: rewrite both statements as injectivity of multiplication by `a`.
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at h
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Chap10 Lemma 10 128 6: a ring equivalence transports a regular sequence to the
entrywise mapped list. -/
private theorem isRegular_map_iff_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) (rs : List A) :
    Sequence.IsRegular A rs ↔ Sequence.IsRegular B (rs.map e) := by
  -- Proof comment: self-module scalar compatibility is preservation of multiplication.
  refine e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  simpa [Algebra.smul_def] using e.map_mul a x

/-- Helper for Chap10 Lemma 10 128 6: regularity on the quotient owner `QuotSMulTop r A` is the
same as regularity on the principal quotient ring by `r`. -/
private theorem isRegular_quotSMulTop_iff_quotient_span_singleton
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Sequence.IsRegular (QuotSMulTop r A) rs ↔
      Sequence.IsRegular (A ⧸ Ideal.span ({r} : Set A))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  have hspan : Ideal.span ({r} : Set A) = r • (⊤ : Ideal A) := by
    -- Proof comment: the principal ring quotient is the additive quotient by `rA`.
    simp [smul_eq_mul, ← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop r A ≃+ A ⧸ Ideal.span ({r} : Set A) :=
    (Ideal.quotientEquivAlgOfEq A hspan).symm.toRingEquiv.toAddEquiv
  -- Proof comment: transport regularity while checking scalar actions on representatives.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  change e (a • x) = Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a • e x
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simp [e, smul_eq_mul]

/-- Helper for Chap10 Lemma 10 128 6: after quotienting by the head element, the remaining list
ideal in the quotient is the image of the tail ideal. -/
private theorem fullTailQuotientAlgEquivMap_eq
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A}
    {rs : List A} :
    Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) =
      (Ideal.ofList rs).map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) := by
  -- Proof comment: mapping a list-generated ideal maps each generator of the list.
  rw [Ideal.map_ofList]

/-- Helper for Chap10 Lemma 10 128 6: quotienting first by the head and then by the mapped tail is
canonically the same `R'`-algebra as quotienting once by the full list. -/
private noncomputable def fullTailQuotientAlgEquiv
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A}
    {rs : List A} :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃ₐ[R'] A ⧸
      Ideal.ofList (r :: rs) :=
  (Ideal.quotientEquivAlgOfEq R'
      (fullTailQuotientAlgEquivMap_eq (R' := R') (r := r) (rs := rs))).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)).trans
      (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm))

/-- Helper for Chap10 Lemma 10 128 6: the iterated quotient comparison sends a double quotient
class to the corresponding class modulo the full head-and-tail ideal. -/
@[simp] private theorem fullTailQuotientAlgEquiv_apply_mk_mk
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A] [Algebra R' A] {r : A}
    {rs : List A} (x : A) :
    fullTailQuotientAlgEquiv (R' := R') (r := r) (rs := rs)
      (Ideal.Quotient.mk
        (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
        (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x := by
  -- Proof comment: compute the comparison through the standard double-quotient generator rule.
  change
    (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm)
      (DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)
        ((Ideal.quotientEquivAlgOfEq R'
          (fullTailQuotientAlgEquivMap_eq (R' := R') (r := r) (rs := rs)))
          (Ideal.Quotient.mk
            (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
            (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x)))) =
      Ideal.Quotient.mk (Ideal.ofList (r :: rs)) x
  have hquot :
      DoubleQuot.quotQuotEquivQuotSupₐ R' (Ideal.span ({r} : Set A)) (Ideal.ofList rs)
        ((Ideal.quotientEquivAlgOfEq R'
          (fullTailQuotientAlgEquivMap_eq (R' := R') (r := r) (rs := rs)))
          (Ideal.Quotient.mk
            (Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))))
            (Ideal.Quotient.mk (Ideal.span ({r} : Set A)) x))) =
        Ideal.Quotient.mk (Ideal.span ({r} : Set A) ⊔ Ideal.ofList rs) x := by
    simpa [DoubleQuot.quotQuotMk] using
      (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk
        (I := Ideal.span ({r} : Set A)) (J := Ideal.ofList rs) x)
  -- Proof comment: the final equality quotient converts the sum ideal into `Ideal.ofList`.
  simpa [Ideal.ofList_cons] using
    congrArg (Ideal.quotientEquivAlgOfEq R' (Ideal.ofList_cons r rs).symm) hquot

section QuotientFiber

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

/-- Helper for Chap10 Lemma 10 128 6: quotienting the old quotient-closed-fiber by the image of
the head is the same as mapping the principal ideal generated by the head. -/
private theorem quotientFiberByHeadLeftMap_eq (f : S) :
    Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S)) =
      Ideal.map (Ideal.Quotient.mk 𝔪S) (Ideal.span ({f} : Set S)) := by
  -- Proof comment: the image of a principal ideal is generated by the image of its generator.
  symm
  simpa using Ideal.map_span (f := Ideal.Quotient.mk 𝔪S) ({f} : Set S)

/-- Helper for Chap10 Lemma 10 128 6: the maximal-ideal fiber ideal after quotienting by `f` is
the image of the original fiber ideal in the quotient ring. -/
private theorem quotientFiberByHeadRightMap_eq (f : S) :
    Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S))) 𝔪S := by
  -- Proof comment: the quotient algebra map is the composite `R → S → S/(f)`.
  have hmap : algebraMap R (S ⧸ Ideal.span ({f} : Set S)) =
      (Ideal.Quotient.mk (Ideal.span ({f} : Set S))).comp (algebraMap R S) := rfl
  rw [hmap]
  exact
    (Ideal.map_map (I := maximalIdeal R)
      (algebraMap R S) (Ideal.Quotient.mk (Ideal.span ({f} : Set S)))).symm

/-- Helper for Chap10 Lemma 10 128 6: the quotient of the old quotient-fiber by the head is
canonically identified with the quotient-presentation closed fiber after killing the head. -/
private noncomputable def quotientFiberByHeadEquiv (f : S) :
    ((S ⧸ 𝔪S) ⧸ Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S))) ≃+*
      ((S ⧸ Ideal.span ({f} : Set S)) ⧸
        Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R)) :=
  ((Ideal.quotEquivOfEq (quotientFiberByHeadLeftMap_eq (R := R) (S := S) f)).trans
      (DoubleQuot.quotQuotEquivQuotSup 𝔪S (Ideal.span ({f} : Set S)))).trans
    ((Ideal.quotEquivOfEq (R := S) (sup_comm 𝔪S (Ideal.span ({f} : Set S)))).trans
      ((Ideal.quotEquivOfEq (quotientFiberByHeadRightMap_eq (R := R) (S := S) f)).trans
        (DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({f} : Set S)) 𝔪S)).symm)

/-- Helper for Chap10 Lemma 10 128 6: the closed-fiber quotient comparison sends a doubly
quotiented representative to the corresponding representative in the quotient ring's fiber. -/
@[simp] private theorem quotientFiberByHeadEquiv_apply_mk_mk (f x : S) :
    quotientFiberByHeadEquiv (R := R) (S := S) f
      (Ideal.Quotient.mk
        (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S)))
        (Ideal.Quotient.mk 𝔪S x)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x) := by
  -- Proof comment: reduce the composite equivalence to the named commutation rule for double
  -- quotients, then apply the equality-quotient computation.
  change
    (Ideal.quotEquivOfEq (quotientFiberByHeadRightMap_eq (R := R) (S := S) f)).symm
      (DoubleQuot.quotQuotEquivComm 𝔪S (Ideal.span ({f} : Set S))
        ((Ideal.quotEquivOfEq
          (quotientFiberByHeadLeftMap_eq (R := R) (S := S) f))
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S)))
            (Ideal.Quotient.mk 𝔪S x)))) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)
  rw [Ideal.quotEquivOfEq_mk, DoubleQuot.quotQuotEquivComm_mk_mk, Ideal.quotEquivOfEq_symm]
  change
    (Ideal.quotEquivOfEq (quotientFiberByHeadRightMap_eq (R := R) (S := S) f).symm)
      (Ideal.Quotient.mk
        (Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S))) 𝔪S)
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (Ideal.Quotient.mk (Ideal.span ({f} : Set S)) x)
  rw [Ideal.quotEquivOfEq_mk]

/-- Helper for Chap10 Lemma 10 128 6: splitting a regular sequence on the quotient-presentation
closed fiber gives regularity of the mapped tail on the quotient ring's closed fiber. -/
private theorem tailQuotientFiberIsRegularOfCons {f : S} {gs : List S}
    (h : Sequence.IsRegular (S ⧸ 𝔪S) ((f :: gs).map (Ideal.Quotient.mk 𝔪S))) :
    Sequence.IsRegular
      ((S ⧸ Ideal.span ({f} : Set S)) ⧸
        Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
      ((gs.map (Ideal.Quotient.mk (Ideal.span ({f} : Set S)))).map
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R)))) := by
  -- Proof comment: first split off the head in the old quotient fiber.
  have hsplit :
      IsSMulRegular (S ⧸ 𝔪S) (Ideal.Quotient.mk 𝔪S f) ∧
        Sequence.IsRegular (QuotSMulTop (Ideal.Quotient.mk 𝔪S f) (S ⧸ 𝔪S))
          (gs.map (Ideal.Quotient.mk 𝔪S)) := by
    simpa [List.map_cons] using
      (RingTheory.Sequence.isRegular_cons_iff (S ⧸ 𝔪S)
        (Ideal.Quotient.mk 𝔪S f) (gs.map (Ideal.Quotient.mk 𝔪S))).1 h
  have htail_ring :
      Sequence.IsRegular
        ((S ⧸ 𝔪S) ⧸ Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S)))
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S)))))) := by
    -- Proof comment: replace the owner quotient module by the principal ring quotient.
    exact
      (isRegular_quotSMulTop_iff_quotient_span_singleton
        (A := S ⧸ 𝔪S) (r := Ideal.Quotient.mk 𝔪S f)
        (rs := gs.map (Ideal.Quotient.mk 𝔪S))).1 hsplit.2
  have htail_transport :
      Sequence.IsRegular
        ((S ⧸ Ideal.span ({f} : Set S)) ⧸
          Ideal.map (algebraMap R (S ⧸ Ideal.span ({f} : Set S))) (maximalIdeal R))
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S))))).map
          (quotientFiberByHeadEquiv (R := R) (S := S) f)) := by
    -- Proof comment: transport the tail through the quotient-fiber comparison.
    exact
      (isRegular_map_iff_of_ringEquiv
        (quotientFiberByHeadEquiv (R := R) (S := S) f)
        (((gs.map (Ideal.Quotient.mk 𝔪S)).map
          (Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk 𝔪S f} : Set (S ⧸ 𝔪S))))))).1 htail_ring
  -- Proof comment: the comparison computes generatorwise to the quotient map from `S/(f)`.
  simpa [List.map_map] using htail_transport

end QuotientFiber

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 6: essential finite presentation is preserved after quotienting
the target by a principal ideal. -/
private theorem essFinitePresentationQuotientSpanSingleton
    {A : Type v} [CommRing A] [Algebra R A]
    (hess : RingHom.EssFinitePresentation (algebraMap R A)) (f : A) :
    RingHom.EssFinitePresentation (algebraMap R (A ⧸ Ideal.span ({f} : Set A))) := by
  -- Proof comment: a principal quotient is finitely presented over `A`, then compose with `R → A`.
  have hquotAlg : Algebra.FinitePresentation A (A ⧸ Ideal.span ({f} : Set A)) := by
    exact Algebra.FinitePresentation.quotient
      (I := Ideal.span ({f} : Set A)) (Submodule.fg_span_singleton f)
  have hquot : RingHom.EssFinitePresentation
      (algebraMap A (A ⧸ Ideal.span ({f} : Set A))) := by
    change Algebra.EssFinitePresentation A (A ⧸ Ideal.span ({f} : Set A))
    exact Algebra.EssFinitePresentation.of_finitePresentation A
      (A ⧸ Ideal.span ({f} : Set A))
  have hcomp := RingHom.EssFinitePresentation.comp hess hquot
  simpa using hcomp

/-- Helper for Chap10 Lemma 10 128 6: the regular-sequence theorem with flat nonempty prefix
quotients, stated for the quotient presentation of the closed fiber so the induction can recurse
through principal quotients. -/
private theorem regularSequenceFlatPrefixesOfQuotientFiberRegularAux
    {A : Type v} [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    (hess : RingHom.EssFinitePresentation (algebraMap R A)) (fs : List A)
    (hfs : Sequence.IsRegular (A ⧸ Ideal.map (algebraMap R A) (maximalIdeal R))
      (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) (maximalIdeal R))))) :
    Sequence.IsRegular A fs ∧
      ∀ i : Fin fs.length, Module.Flat R (A ⧸ Ideal.ofList (fs.take (i + 1))) := by
  -- Proof comment: induct on the sequence length while allowing the ambient algebra to change to
  -- the quotient by the current head.
  let conclusion :
      ∀ n : ℕ,
        ∀ {B : Type v} [CommRing B] [Algebra R B]
          [IsLocalRing B] [IsLocalHom (algebraMap R B)] [Module.Flat R B],
          RingHom.EssFinitePresentation (algebraMap R B) →
          (gs : List B) →
          gs.length = n →
          Sequence.IsRegular (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
            (gs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)))) →
          Sequence.IsRegular B gs ∧
            ∀ i : Fin gs.length, Module.Flat R (B ⧸ Ideal.ofList (gs.take (i + 1))) := by
    intro n
    induction n with
    | zero =>
        intro B _ _ _ _ _ hessB gs hlen hgs
        have hnil : gs = [] := by
          simpa using hlen
        subst hnil
        haveI : Nontrivial B := inferInstance
        refine ⟨?_, ?_⟩
        · -- Proof comment: the empty sequence is regular in any nontrivial local ring.
          simpa using (RingTheory.Sequence.IsRegular.nil B B)
        · intro i
          exact Fin.elim0 i
    | succ n ihn =>
        intro B _ _ _ _ _ hessB gs hlen hgs
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
                    (hs.map
                      (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)))) := by
              -- Proof comment: split regularity on the closed fiber into the head and tail.
              simpa [List.map_cons] using
                (RingTheory.Sequence.isRegular_cons_iff
                  (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))
                  (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g)
                  (hs.map
                    (Ideal.Quotient.mk
                      (Ideal.map (algebraMap R B) (maximalIdeal R))))).1 hgs
            have hhead_regular :
                IsRegular
                  (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (maximalIdeal R)) g) :=
              isRegular_of_isSMulRegular_self hsplit.1
            -- Proof comment: Lemma 10.128.5 gives regularity of the head upstairs and flatness of
            -- the first quotient.
            have hhead_step :
                Module.Flat R (B ⧸ Ideal.span ({g} : Set B)) ∧ IsRegular g := by
              -- Route correction: the single-element criterion is now available from the
              -- preceding item, so the head step is a direct dependency application.
              exact
                flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation
                  hessB g hhead_regular
            obtain ⟨hflat_head, hg_regular⟩ := hhead_step
            have htail_closed :
                Sequence.IsRegular
                  ((B ⧸ Ideal.span ({g} : Set B)) ⧸
                    Ideal.map (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) (maximalIdeal R))
                  ((hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B)))).map
                    (Ideal.Quotient.mk
                      (Ideal.map (algebraMap R (B ⧸ Ideal.span ({g} : Set B)))
                        (maximalIdeal R)))) := by
              -- Proof comment: identify the tail closed fiber after killing the head.
              exact tailQuotientFiberIsRegularOfCons (R := R) (S := B) (f := g) hgs
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
              -- Proof comment: the quotient map is local, so its composite with `R → B` is local.
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
            have hess_quot :
                RingHom.EssFinitePresentation
                  (algebraMap R (B ⧸ Ideal.span ({g} : Set B))) :=
              essFinitePresentationQuotientSpanSingleton (R := R) hessB g
            have hrec :=
              ihn (B := B ⧸ Ideal.span ({g} : Set B)) hess_quot
                (hs.map (Ideal.Quotient.mk (Ideal.span ({g} : Set B))))
                (by simpa [hhs_len]) htail_closed'
            have htail_module : Sequence.IsRegular (QuotSMulTop g B) hs := by
              -- Proof comment: move recursive regularity back from the principal quotient ring to
              -- the owner quotient module.
              exact
                (isRegular_quotSMulTop_iff_quotient_span_singleton
                  (A := B) (r := g) (rs := hs)).2 hrec.1
            have hregular_cons : Sequence.IsRegular B (g :: hs) := by
              -- Proof comment: reassemble the head and quotient-tail regularity.
              exact
                (RingTheory.Sequence.isRegular_cons_iff B g hs).2
                  ⟨isSMulRegular_self_of_isRegular hg_regular, htail_module⟩
            refine ⟨hregular_cons, ?_⟩
            intro i
            refine Fin.cases ?_ ?_ i
            · -- Proof comment: the first prefix quotient is the principal quotient from the
              -- single-element theorem.
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
                -- Proof comment: rewrite the recursive flatness clause to the literal taken tail.
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
                -- Proof comment: transport flatness across the canonical single-quotient
                -- comparison.
                exact Module.Flat.of_linearEquiv
                  (fullTailQuotientAlgEquiv
                    (R' := R) (r := g) (rs := hs.take (j + 1))).toLinearEquiv.symm
              change Module.Flat R (B ⧸ Ideal.ofList (g :: hs.take (j + 1)))
              exact hflat_full
  exact conclusion fs.length hess fs rfl hfs

-- Proof sketch: argue by induction on `fs`. The base step is trivial. For the inductive step,
-- transport regularity of the head along the canonical quotient view
-- `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and apply Lemma `10.128.5`
-- to get that the head is regular in `S` and that the first quotient is flat over `R`. Then pass
-- to the quotient by the head and apply the induction hypothesis to the tail sequence.
/-- Chap10 Lemma 10 128 6: for a flat essentially finitely presented local homomorphism `R → S`,
if the images of a finite sequence `fs` in the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently in the quotient
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, form a regular sequence, then `fs` is a
regular sequence in `S`, and each quotient by a nonempty initial segment of `fs` is flat over
`R`. -/
@[stacks 0470]
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular_of_essFinitePresentation
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (algebraMap S ClosedFiber))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := by
  -- Proof comment: first move the canonical closed-fiber regularity to the quotient model used by
  -- the induction.
  have hfs_quot :
      Sequence.IsRegular (S ⧸ 𝔪S) (fs.map (Ideal.Quotient.mk 𝔪S)) := by
    have htransport :
        Sequence.IsRegular ClosedFiber
          ((fs.map (Ideal.Quotient.mk 𝔪S)).map
            (closedFiber_quotient_equiv (A := R) (B := S)).toRingEquiv) := by
      have hlist :
          ((fs.map (Ideal.Quotient.mk 𝔪S)).map
            (closedFiber_quotient_equiv (A := R) (B := S)).toRingEquiv) =
            fs.map (algebraMap S ClosedFiber) := by
        -- Proof comment: compute the quotient-to-closed-fiber equivalence on each representative.
        induction fs with
        | nil =>
            rfl
        | cons s ss ih =>
            simp
      rw [hlist]
      exact hfs
    exact
      (isRegular_map_iff_of_ringEquiv
        (closedFiber_quotient_equiv (A := R) (B := S)).toRingEquiv
        (fs.map (Ideal.Quotient.mk 𝔪S))).2 htransport
  -- Proof comment: apply the generalized induction theorem to the original ambient ring.
  exact
    regularSequenceFlatPrefixesOfQuotientFiberRegularAux
      (R := R) (A := S) hess fs hfs_quot

end
