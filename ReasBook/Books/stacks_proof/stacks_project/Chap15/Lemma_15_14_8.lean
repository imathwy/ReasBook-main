import stacks_proof.stacks_project.Chap15.Definition_15_11_1
import stacks_proof.stacks_project.Chap15.Definition_15_14_1
import stacks_proof.stacks_project.Chap15.Lemma_15_11_6
import stacks_proof.stacks_project.Chap15.Lemma_15_14_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial

universe u

section

variable {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs over absolutely integrally closed rings, with the canonical
  owner `HenselianRing A I` and quotient idempotent lifting as derived API;
- sampled owner-level declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.le_ring_jacobson_of_henselianRing`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `quotientMk_injective_on_idempotents_of_le_jacobson`;
- best owner abstraction: this lemma is `source-facing`, but its proof should be organized around
  the existing henselian owner `HenselianRing A I` and the chapter-level idempotent-lifting owner
  `I.HasFiniteAlgebraIdempotentLifting`, not around a parallel local criterion;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, and the Jacobson plus
  quotient-idempotent surjectivity conditions from the source statement;
- derived API: injectivity of the quotient idempotent map from the Jacobson condition, the
  finite-algebra idempotent-lifting owner obtained from the chapter TFAE, and the resulting
  henselian conclusion.

Source/core/bridge triage:
- `source-facing`: the present equivalence specialized to absolutely integrally closed rings;
- `core/canonical`: `HenselianRing A I` and `I.HasFiniteAlgebraIdempotentLifting`;
- `bridge/view`: the internal Gabber-root-criterion step from Lemma `15.11.6` and the
  quotient-idempotent map `(Ideal.Quotient.mk I).idempotentMap`.
-/

-- Proof sketch: the forward implication should not rebuild idempotent lifting locally; instead,
-- specialize the finite-algebra idempotent clause of Lemma `15.11.6` to `B = A`. For the
-- converse, the source-specific step is first to turn surjectivity on quotient idempotents over
-- an absolutely integrally closed ring into Gabber's root criterion, and then immediately package
-- that step through the canonical owner `I.HasFiniteAlgebraIdempotentLifting`.

/-- Helper for Lemma 15.14.8: the Gabber factorization `X^n * (X - 1)` is coprime. -/
private theorem x_pow_isCoprime_x_sub_one (R : Type*) [CommRing R] (n : ℕ) :
    IsCoprime (X ^ n : R[X]) (X - 1) := by
  -- The geometric-series identity gives an explicit Bezout relation.
  refine ⟨1, -(∑ i ∈ Finset.range n, (X : R[X]) ^ i), ?_⟩
  calc
    (1 : R[X]) * X ^ n + -(∑ i ∈ Finset.range n, (X : R[X]) ^ i) * (X - 1)
        = X ^ n - ((∑ i ∈ Finset.range n, (X : R[X]) ^ i) * (X - 1)) := by
            ring
    _ = X ^ n - (X ^ n - 1) := by
          rw [geom_sum_mul]
    _ = 1 := by
          ring

/-- Helper for Lemma 15.14.8: under the Jacobson hypothesis, a monic lift of `X - 1` has a root
in `1 + I`. -/
private theorem exists_isRoot_of_monic_map_eq_X_sub_one
    (I : Ideal A) (hI : I ≤ Ring.jacobson A) {h : A[X]} (hh : h.Monic)
    (hmap : h.map (Ideal.Quotient.mk I) = (X - 1 : (A ⧸ I)[X])) :
    ∃ i : I, h.IsRoot (1 + ↑i) := by
  by_cases hA : Subsingleton A
  · -- In the degenerate ring, every evaluation is forced to vanish.
    let i : I := ⟨0, Ideal.zero_mem I⟩
    refine ⟨i, ?_⟩
    rw [Polynomial.IsRoot]
    exact Subsingleton.elim _ 0
  · let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    have hItop : I ≠ ⊤ := by
      -- A Jacobson ideal is proper in a nontrivial ring.
      intro htop
      have hJacTop : Ring.jacobson A = ⊤ := eq_top_iff.mpr <| by
        simpa [htop] using hI
      have hBotTop : (⊥ : Ideal A) = ⊤ := by
        exact (Ideal.jacobson_eq_top_iff (I := (⊥ : Ideal A))).mp <| by
          simpa [Ideal.jacobson_bot] using hJacTop
      exact bot_ne_top hBotTop
    let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
    have hdeg : h.degree ≠ 0 := by
      -- Mapping preserves the degree of a nonzero monic polynomial.
      have hXdeg : ((X - 1 : (A ⧸ I)[X])).degree = 1 := by
        simpa using Polynomial.degree_X_sub_C (1 : A ⧸ I)
      have hdegMap :
          (h.map (Ideal.Quotient.mk I)).degree ≠ 0 := by
        simpa [hmap, hXdeg]
      rwa [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero (Ideal.Quotient.mk I)
        (by simpa [hh.leadingCoeff] using (show (1 : A) ≠ 0 from one_ne_zero))] at hdegMap
    -- Absolute integral closedness now supplies an actual root of `h`.
    obtain ⟨a, ha⟩ := IsAbsolutelyIntegrallyClosed.exists_root h hh hdeg
    have haq : (Ideal.Quotient.mk I) a = 1 := by
      -- After mapping to the quotient, the root must specialize to the unique root of `X - 1`.
      have hrootq : (h.map (Ideal.Quotient.mk I)).IsRoot ((Ideal.Quotient.mk I) a) := by
        rw [Polynomial.IsRoot, Polynomial.eval_map]
        simpa using congrArg (Ideal.Quotient.mk I) ha.eq_zero
      rw [Polynomial.IsRoot, hmap] at hrootq
      have hrootq' : (Ideal.Quotient.mk I) a - 1 = 0 := by
        simpa using hrootq
      exact sub_eq_zero.mp hrootq'
    have ha_mem : a - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, haq]
      simp
    refine ⟨⟨a - 1, ha_mem⟩, ?_⟩
    -- Repackage the lifted root in the requested `1 + I` form.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha

/-- Helper for Lemma 15.14.8: evaluating Bézout data at a chosen quotient root produces the
idempotent that decides on which side of the factorization the root lies. -/
private theorem root_partition_idempotent_eval
    (I : Ideal A) {f : A[X]} {g₀ h₀ k₀ l₀ : (A ⧸ I)[X]} {a : A}
    (ha : f.IsRoot a) (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (hbez : k₀ * g₀ + l₀ * h₀ = 1) :
    IsIdempotentElem (h₀.eval ((Ideal.Quotient.mk I) a) * l₀.eval ((Ideal.Quotient.mk I) a)) ∧
      ((h₀.eval ((Ideal.Quotient.mk I) a) * l₀.eval ((Ideal.Quotient.mk I) a) = 1) →
        g₀.IsRoot ((Ideal.Quotient.mk I) a)) ∧
      ((h₀.eval ((Ideal.Quotient.mk I) a) * l₀.eval ((Ideal.Quotient.mk I) a) = 0) →
        h₀.IsRoot ((Ideal.Quotient.mk I) a)) := by
  let aq : A ⧸ I := (Ideal.Quotient.mk I) a
  let ebar : A ⧸ I := h₀.eval aq * l₀.eval aq
  rw [Polynomial.IsRoot] at ha ⊢
  have hroot_eval : g₀.eval aq * h₀.eval aq = 0 := by
    -- The chosen root of `f` remains a quotient root of `g₀ * h₀`.
    have hmap_root : (f.map (Ideal.Quotient.mk I)).eval aq = 0 := by
      rw [← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_apply]
      exact congrArg (Ideal.Quotient.mk I) ha
    rw [hfactor, Polynomial.eval_mul] at hmap_root
    exact hmap_root
  have hbez_eval : k₀.eval aq * g₀.eval aq + l₀.eval aq * h₀.eval aq = 1 := by
    -- Evaluating the Bézout relation gives a partition of unity at the chosen quotient root.
    exact
      (by
        simpa [Polynomial.eval_add, Polynomial.eval_mul] using
          congrArg (fun p : (A ⧸ I)[X] => p.eval aq) hbez)
  have hsplit : k₀.eval aq * g₀.eval aq + ebar = 1 := by
    simpa [ebar, mul_comm, mul_left_comm, mul_assoc] using hbez_eval
  have hcross : (k₀.eval aq * g₀.eval aq) * ebar = 0 := by
    -- The two complementary summands are orthogonal because `g₀(aq) * h₀(aq) = 0`.
    calc
      (k₀.eval aq * g₀.eval aq) * ebar
          = (k₀.eval aq * l₀.eval aq) * (g₀.eval aq * h₀.eval aq) := by
              dsimp [ebar]
              ring
      _ = 0 := by rw [hroot_eval, mul_zero]
  have hebar_idem : ebar * ebar = ebar := by
    -- Multiplying the partition of unity by `ebar` kills the complementary term.
    have hmul :
        (k₀.eval aq * g₀.eval aq) * ebar + ebar * ebar = ebar := by
      calc
        (k₀.eval aq * g₀.eval aq) * ebar + ebar * ebar
            = (k₀.eval aq * g₀.eval aq + ebar) * ebar := by ring
        _ = 1 * ebar := by rw [hsplit]
        _ = ebar := by simp
    simpa [hcross] using hmul
  constructor
  · -- The evaluated Bézout term is the idempotent from the source proof.
    simpa [IsIdempotentElem, ebar] using hebar_idem
  constructor
  · intro hebar_one
    -- If the idempotent equals `1`, then `h₀(aq)` is invertible, so `g₀(aq) = 0`.
    have hebar_one' : ebar = 1 := by
      simpa [ebar] using hebar_one
    have hone_ebar : (1 : A ⧸ I) = ebar := hebar_one'.symm
    have hg_eval : g₀.eval aq = 0 := by
      calc
        g₀.eval aq = g₀.eval aq * 1 := by simp
        _ = g₀.eval aq * ebar := by rw [hone_ebar]
        _ = (g₀.eval aq * h₀.eval aq) * l₀.eval aq := by
              dsimp [ebar]
              ring
        _ = 0 := by rw [hroot_eval, zero_mul]
    simpa [aq] using hg_eval
  · intro hebar_zero
    -- If the idempotent equals `0`, then the complementary Bézout factor is `1`, forcing
    -- `h₀(aq) = 0`.
    have hebar_zero' : ebar = 0 := by
      simpa [ebar] using hebar_zero
    have hleft_unit : k₀.eval aq * g₀.eval aq = 1 := by
      have hsplit_zero : k₀.eval aq * g₀.eval aq + 0 = 1 := by
        simpa [hebar_zero'] using hsplit
      simpa using hsplit_zero
    have hh_eval : h₀.eval aq = 0 := by
      calc
        h₀.eval aq = (k₀.eval aq * g₀.eval aq) * h₀.eval aq := by rw [hleft_unit, one_mul]
        _ = k₀.eval aq * (g₀.eval aq * h₀.eval aq) := by ring
        _ = 0 := by rw [hroot_eval, mul_zero]
    simpa [aq] using hh_eval

/-- Helper for Lemma 15.14.8: over a Jacobson ideal, an idempotent is determined by its quotient
class. -/
private theorem eq_of_quotient_eq_of_idempotent
    (I : Ideal A) (hI : I ≤ Ring.jacobson A) {e₁ e₂ : A}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hquot : (Ideal.Quotient.mk I) e₁ = (Ideal.Quotient.mk I) e₂) :
    e₁ = e₂ := by
  -- Proof comment: Jacobson injectivity on quotient idempotents lets us compare the two lifts
  -- directly on the idempotent subtype instead of repeating elementwise algebra.
  have hinj : Function.Injective (Ideal.Quotient.mk I).idempotentMap :=
    quotientMk_injective_on_idempotents_of_le_jacobson (A := A) I hI
  have hidem :
      (Ideal.Quotient.mk I).idempotentMap ⟨e₁, he₁⟩ =
        (Ideal.Quotient.mk I).idempotentMap ⟨e₂, he₂⟩ := by
    apply Subtype.ext
    simpa [RingHom.idempotentMap] using hquot
  exact congrArg Subtype.val (hinj hidem)

/-- Helper for Lemma 15.14.8: Jacobson containment descends along a surjective ring map. -/
private theorem ideal_map_le_ring_jacobson_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (J : Ideal R) (hJ : J ≤ Ring.jacobson R) :
    Ideal.map f J ≤ Ring.jacobson S := by
  -- Proof comment: test the Jacobson condition on `1 + y`, then pull `y` back through the
  -- surjection and map the resulting unit forward.
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro y hy
  rcases (Ideal.mem_map_iff_of_surjective f hf).mp hy with ⟨x, hx, rfl⟩
  have hxUnit : IsUnit (1 + x) :=
    (ideal_le_ring_jacobson_iff_isUnit_one_add J).mp hJ x hx
  simpa using IsUnit.map f hxUnit

/-- Helper for Lemma 15.14.8: the factorization lift is trivial when the source polynomial has
degree zero. -/
private theorem exists_monic_coprime_factorization_lift_of_natDegree_eq_zero
    (I : Ideal A) {f : A[X]} (hf : f.Monic) {g₀ h₀ : (A ⧸ I)[X]} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) (hdeg : f.natDegree = 0) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧
        f = g * h ∧
          g.map (Ideal.Quotient.mk I) = g₀ ∧
            h.map (Ideal.Quotient.mk I) = h₀ := by
  -- Proof comment: a monic degree-zero polynomial is `1`, so both monic quotient factors are
  -- forced to be `1` as well.
  have hf_one : f = 1 := hf.natDegree_eq_zero.mp hdeg
  have hprod_deg : (g₀ * h₀).natDegree = 0 := by
    simpa [hf_one] using congrArg Polynomial.natDegree hfactor.symm
  have hsum_deg : g₀.natDegree + h₀.natDegree = 0 := by
    simpa [hg₀.natDegree_mul hh₀] using hprod_deg
  have hgdeg : g₀.natDegree = 0 := by
    omega
  have hhdeg : h₀.natDegree = 0 := by
    omega
  have hg₀_one : g₀ = 1 := hg₀.natDegree_eq_zero.mp hgdeg
  have hh₀_one : h₀ = 1 := hh₀.natDegree_eq_zero.mp hhdeg
  refine ⟨1, 1, by simpa, by simpa, ?_, ?_, ?_⟩
  · simpa [hf_one]
  · simpa [hg₀_one]
  · simpa [hh₀_one]

/-- Helper for Lemma 15.14.8: after splitting by a lifted idempotent `e`, the branch residue
rings are canonically the quotient branches cut out by the quotient idempotent `ebar`. -/
private theorem component_residue_ringEquiv_after_idempotent_split
    (I : Ideal A) {e : A} {ebar : A ⧸ I}
    (hquot_e : (Ideal.Quotient.mk I) e = ebar) :
    ∃ φ₀ :
        ((A ⧸ Ideal.span ({e} : Set A)) ⧸
            Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I) ≃+*
          ((A ⧸ I) ⧸ Ideal.span ({ebar} : Set (A ⧸ I))),
      ∃ φ₁ :
          ((A ⧸ Ideal.span ({1 - e} : Set A)) ⧸
              Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I) ≃+*
            ((A ⧸ I) ⧸ Ideal.span ({1 - ebar} : Set (A ⧸ I))),
        (∀ a : A,
            φ₀
                ((Ideal.Quotient.mk
                    (Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I))
                  ((Ideal.Quotient.mk (Ideal.span ({e} : Set A))) a)) =
              (Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) ∧
          (∀ a : A,
            φ₁
                ((Ideal.Quotient.mk
                    (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I))
                  ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) a)) =
              (Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) := by
  -- Proof comment: identify each iterated quotient with its common quotient by a supremum ideal,
  -- then rewrite the quotient-side ideal via the image of the singleton generator.
  have hmap_e :
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({e} : Set A)) =
        Ideal.span ({ebar} : Set (A ⧸ I)) := by
    calc
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({e} : Set A))
          = Ideal.span ((Ideal.Quotient.mk I) '' ({e} : Set A)) := by
              rw [Ideal.map_span]
      _ = Ideal.span ({ebar} : Set (A ⧸ I)) := by
            congr
            ext x
            simp [hquot_e]
  have hmap_one_sub :
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({1 - e} : Set A)) =
        Ideal.span ({1 - ebar} : Set (A ⧸ I)) := by
    calc
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({1 - e} : Set A))
          = Ideal.span ((Ideal.Quotient.mk I) '' ({1 - e} : Set A)) := by
              rw [Ideal.map_span]
      _ = Ideal.span ({1 - ebar} : Set (A ⧸ I)) := by
            congr
            ext x
            simp [hquot_e]
  let leftEquiv₀ :
      ((A ⧸ Ideal.span ({e} : Set A)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I) ≃+*
        (A ⧸ (Ideal.span ({e} : Set A) ⊔ I)) := by
    simpa [Ideal.add_eq_sup] using
      DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({e} : Set A)) I
  let rightEquiv₀ :
      ((A ⧸ I) ⧸ Ideal.span ({ebar} : Set (A ⧸ I))) ≃+*
        (A ⧸ (Ideal.span ({e} : Set A) ⊔ I)) :=
    (((Ideal.quotEquivOfEq hmap_e).symm.trans <|
        by
          simpa [Ideal.add_eq_sup] using
            DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({e} : Set A))).trans
      (Ideal.quotEquivOfEq (sup_comm I (Ideal.span ({e} : Set A)) :
        I ⊔ Ideal.span ({e} : Set A) =
        Ideal.span ({e} : Set A) ⊔ I)))
  let φ₀ := leftEquiv₀.trans rightEquiv₀.symm
  let leftEquiv₁ :
      ((A ⧸ Ideal.span ({1 - e} : Set A)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I) ≃+*
        (A ⧸ (Ideal.span ({1 - e} : Set A) ⊔ I)) := by
    simpa [Ideal.add_eq_sup] using
      DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({1 - e} : Set A)) I
  let rightEquiv₁ :
      ((A ⧸ I) ⧸ Ideal.span ({1 - ebar} : Set (A ⧸ I))) ≃+*
        (A ⧸ (Ideal.span ({1 - e} : Set A) ⊔ I)) :=
    (((Ideal.quotEquivOfEq hmap_one_sub).symm.trans <|
        by
          simpa [Ideal.add_eq_sup] using
            DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({1 - e} : Set A))).trans
      (Ideal.quotEquivOfEq (sup_comm I (Ideal.span ({1 - e} : Set A)) :
        I ⊔ Ideal.span ({1 - e} : Set A) =
        Ideal.span ({1 - e} : Set A) ⊔ I)))
  let φ₁ := leftEquiv₁.trans rightEquiv₁.symm
  refine ⟨φ₀, φ₁, ?_⟩
  constructor
  · intro a
    have hleft :
        leftEquiv₀
            ((Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I))
              ((Ideal.Quotient.mk (Ideal.span ({e} : Set A))) a)) =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set A) ⊔ I)) a := by
      -- Proof comment: the left branch double quotient is the quotient by the supremum ideal.
      dsimp [leftEquiv₀]
      rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
    have hright :
        rightEquiv₀
            ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a)) =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set A) ⊔ I)) a := by
      -- Proof comment: the right branch first rewrites the quotient ideal, then collapses the
      -- iterated quotient to the same supremum quotient.
      have hrewrite :
          (Ideal.quotEquivOfEq hmap_e).symm
              ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) =
            DoubleQuot.quotQuotMk I (Ideal.span ({e} : Set A)) a := by
        apply (Ideal.quotEquivOfEq hmap_e).symm_apply_eq.2
        rw [Ideal.quotEquivOfEq_mk]
      dsimp [rightEquiv₀]
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hrewrite]
      rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
    -- Proof comment: both quotient branches now agree after transport to the common quotient.
    apply rightEquiv₀.injective
    simpa [φ₀, RingEquiv.trans_apply] using hleft.trans hright.symm
  · intro a
    have hleft :
        leftEquiv₁
            ((Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I))
              ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) a)) =
          (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A) ⊔ I)) a := by
      -- Proof comment: this is the complementary branch version of the same double-quotient
      -- computation.
      dsimp [leftEquiv₁]
      rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
    have hright :
        rightEquiv₁
            ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a)) =
          (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A) ⊔ I)) a := by
      -- Proof comment: again rewrite the quotient ideal on representatives before collapsing the
      -- iterated quotient.
      have hrewrite :
          (Ideal.quotEquivOfEq hmap_one_sub).symm
              ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) =
            DoubleQuot.quotQuotMk I (Ideal.span ({1 - e} : Set A)) a := by
        apply (Ideal.quotEquivOfEq hmap_one_sub).symm_apply_eq.2
        rw [Ideal.quotEquivOfEq_mk]
      dsimp [rightEquiv₁]
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hrewrite]
      rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
    -- Proof comment: the complementary branch also lands in the same supremum quotient.
    apply rightEquiv₁.injective
    simpa [φ₁, RingEquiv.trans_apply] using hleft.trans hright.symm

/-- Helper for Lemma 15.14.8: a ring equivalence induces a bijection on idempotents. -/
private theorem ringEquiv_bijective_idempotentMap {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Function.Bijective e.toRingHom.idempotentMap := by
  constructor
  · intro x y hxy
    -- Proof comment: compare underlying elements and cancel the equivalence.
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  · intro y
    -- Proof comment: transport the idempotent back along the inverse equivalence.
    refine ⟨⟨e.symm y.1, y.2.map e.symm.toRingHom⟩, ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply y.1

/-- Helper for Lemma 15.14.8: the first projection from a product ring is surjective on
idempotents. -/
private theorem prod_fst_surjective_idempotentMap {R S : Type*} [CommRing R] [CommRing S] :
    Function.Surjective (RingHom.idempotentMap (RingHom.fst R S)) := by
  intro x
  refine ⟨⟨(x.1, 0), ?_⟩, ?_⟩
  · -- Proof comment: pair the chosen idempotent with the zero idempotent in the second factor.
    change IsIdempotentElem (x.1, (0 : S))
    simpa [IsIdempotentElem] using
      show x.1 * x.1 = x.1 ∧ (0 : S) * 0 = 0 from ⟨x.2.eq, by simp⟩
  · -- Proof comment: projection forgets the zero component by definition.
    apply Subtype.ext
    rfl

/-- Helper for Lemma 15.14.8: quotienting by the ideal generated by an idempotent is surjective on
idempotents. -/
private theorem quotientMk_span_singleton_surjective_idempotentMap
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    Function.Surjective (Ideal.Quotient.mk (Ideal.span ({e} : Set R))).idempotentMap := by
  have hsum : e + (1 - e) = 1 := by
    simp
  have hmul : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  let split :
      R ≃+* ((R ⧸ Ideal.span ({e} : Set R)) × (R ⧸ Ideal.span ({1 - e} : Set R))) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub hsum hmul
  have hsplit :
      Function.Bijective split.toRingHom.idempotentMap :=
    ringEquiv_bijective_idempotentMap split
  have hfst :
      Function.Surjective
        (RingHom.idempotentMap
          (RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
            (R ⧸ Ideal.span ({1 - e} : Set R)))) :=
    prod_fst_surjective_idempotentMap
  have hfst_comp :
      ((RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
          (R ⧸ Ideal.span ({1 - e} : Set R))).comp split.toRingHom) =
        Ideal.Quotient.mk (Ideal.span ({e} : Set R)) := by
    ext x
    -- Proof comment: the canonical product decomposition records the quotient maps as its two
    -- coordinates.
    exact congrArg Prod.fst <|
      AlgEquiv.prodQuotientOfIsIdempotentElem_apply R he he.one_sub hsum hmul x
  intro x
  obtain ⟨y, hy⟩ := hfst x
  obtain ⟨z, hz⟩ := hsplit.2 y
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hz_val : split z.1 = y.1 := congrArg Subtype.val hz
  have hy_val :
      (RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
        (R ⧸ Ideal.span ({1 - e} : Set R))) y.1 = x.1 :=
    congrArg Subtype.val hy
  calc
    (Ideal.Quotient.mk (Ideal.span ({e} : Set R))) z.1
        = ((RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
            (R ⧸ Ideal.span ({1 - e} : Set R))).comp split.toRingHom) z.1 := by
            rw [hfst_comp]
    _ = (RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
          (R ⧸ Ideal.span ({1 - e} : Set R))) (split z.1) := by
            rfl
    _ = (RingHom.fst (R ⧸ Ideal.span ({e} : Set R))
          (R ⧸ Ideal.span ({1 - e} : Set R))) y.1 := by
            rw [hz_val]
    _ = x.1 := hy_val

/-- Helper for Lemma 15.14.8: a commuting branch equivalence transports idempotent surjectivity
from the quotient-side split branch back to the corresponding quotient branch of `A`. -/
private theorem component_idempotent_surjectivity_after_idempotent_split
    (I : Ideal A) {B : Type*} [CommRing B] (π : A →+* B) (J : Ideal B)
    (K : Ideal (A ⧸ I)) (φ : (B ⧸ J) ≃+* ((A ⧸ I) ⧸ K))
    (hφ :
      ∀ a : A,
        φ ((Ideal.Quotient.mk J) (π a)) =
          (Ideal.Quotient.mk K) ((Ideal.Quotient.mk I) a))
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap)
    (hquotSurj : Function.Surjective (Ideal.Quotient.mk K).idempotentMap) :
    Function.Surjective (Ideal.Quotient.mk J).idempotentMap := by
  intro x
  let y := φ.toRingHom.idempotentMap x
  obtain ⟨z, hz⟩ := hquotSurj y
  obtain ⟨w, hw⟩ := hsurj z
  refine ⟨⟨π w.1, w.2.map π⟩, ?_⟩
  have hφinj : Function.Injective φ.toRingHom.idempotentMap :=
    (ringEquiv_bijective_idempotentMap φ).1
  apply hφinj
  apply Subtype.ext
  -- Proof comment: the commuting formula `hφ` turns the chosen lift in `A` into the prescribed
  -- branch quotient idempotent after applying the branch equivalence.
  change φ ((Ideal.Quotient.mk J) (π w.1)) = φ x.1
  have hw_val : (Ideal.Quotient.mk I) w.1 = z.1 := by
    simpa [RingHom.idempotentMap] using congrArg Subtype.val hw
  have hz_val : (Ideal.Quotient.mk K) z.1 = y.1 := by
    simpa [RingHom.idempotentMap, y] using congrArg Subtype.val hz
  calc
    φ ((Ideal.Quotient.mk J) (π w.1))
        = (Ideal.Quotient.mk K) ((Ideal.Quotient.mk I) w.1) := hφ w.1
    _ = (Ideal.Quotient.mk K) z.1 := by rw [hw_val]
    _ = y.1 := hz_val
    _ = φ x.1 := rfl

/-- Helper for Lemma 15.14.8: the source proof lifts coprime monic factorizations modulo `I`
under the Jacobson and idempotent-surjectivity hypotheses. -/
private theorem
    exists_monic_coprime_factorization_lift_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap)
    {f : A[X]} (hf : f.Monic) {g₀ h₀ : (A ⧸ I)[X]} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcoprime : IsCoprime g₀ h₀) (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧
        f = g * h ∧
          g.map (Ideal.Quotient.mk I) = g₀ ∧
            h.map (Ideal.Quotient.mk I) = h₀ := by
  -- Route correction: the source proof is a one-root induction, not a simultaneous split over all
  -- roots of `f`. The verified bridge above isolates the quotient idempotent evaluated at the
  -- chosen root, which is the controller for the next binary product decomposition step.
  by_cases hA : Subsingleton A
  · -- Proof comment: in the degenerate ring, every polynomial and every quotient class are forced.
    refine ⟨1, f, by simpa, hf, by simp, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  by_cases hdeg0 : f.natDegree = 0
  · -- Proof comment: the constant case is already rigid enough that no idempotent splitting is
    -- needed.
    exact exists_monic_coprime_factorization_lift_of_natDegree_eq_zero
      (I := I) hf hg₀ hh₀ hfactor hdeg0
  · let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    have hdeg : f.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hf.ne_zero]
      simpa using hdeg0
    -- Proof comment: in positive degree, absolute integral closedness gives the root that drives
    -- the source induction step.
    obtain ⟨a, ha⟩ := IsAbsolutelyIntegrallyClosed.exists_root f hf hdeg
    rcases hcoprime with ⟨k₀, l₀, hbez⟩
    let aq : A ⧸ I := (Ideal.Quotient.mk I) a
    let ebar : A ⧸ I := h₀.eval aq * l₀.eval aq
    have hpartition :
        IsIdempotentElem ebar ∧
          (ebar = 1 → g₀.IsRoot aq) ∧
          (ebar = 0 → h₀.IsRoot aq) := by
      simpa [aq, ebar] using
        root_partition_idempotent_eval (I := I) (a := a) ha hfactor hbez
    obtain ⟨⟨e, he⟩, heLift⟩ := hsurj ⟨ebar, hpartition.1⟩
    have hquot_e : (Ideal.Quotient.mk I) e = ebar := by
      -- Proof comment: unwrap the idempotent-map surjectivity witness to recover the quotient
      -- class of the chosen lift.
      simpa [RingHom.idempotentMap, ebar] using congrArg Subtype.val heLift
    have he_one_of_ebar_one : ebar = 1 → e = 1 := by
      intro hebar_one
      exact eq_of_quotient_eq_of_idempotent (I := I) hI he (by simp [IsIdempotentElem]) <| by
        simpa [hquot_e, hebar_one]
    have he_zero_of_ebar_zero : ebar = 0 → e = 0 := by
      intro hebar_zero
      exact eq_of_quotient_eq_of_idempotent (I := I) hI he (by simp [IsIdempotentElem]) <| by
        simpa [hquot_e, hebar_zero]
    let π₀ : A →+* A ⧸ Ideal.span ({e} : Set A) := Ideal.Quotient.mk _
    let π₁ : A →+* A ⧸ Ideal.span ({1 - e} : Set A) := Ideal.Quotient.mk _
    let J₀ : Ideal (A ⧸ Ideal.span ({e} : Set A)) := Ideal.map π₀ I
    let J₁ : Ideal (A ⧸ Ideal.span ({1 - e} : Set A)) := Ideal.map π₁ I
    have hJ₀ :
        J₀ ≤ Ring.jacobson (A ⧸ Ideal.span ({e} : Set A)) := by
      -- Proof comment: the `e = 0` component inherits the Jacobson hypothesis from `A`.
      simpa [J₀, π₀] using
        ideal_map_le_ring_jacobson_of_surjective
          (f := π₀) Ideal.Quotient.mk_surjective I hI
    have hJ₁ :
        J₁ ≤ Ring.jacobson (A ⧸ Ideal.span ({1 - e} : Set A)) := by
      -- Proof comment: the complementary `e = 1` component inherits the same Jacobson control.
      simpa [J₁, π₁] using
        ideal_map_le_ring_jacobson_of_surjective
          (f := π₁) Ideal.Quotient.mk_surjective I hI
    let B₀ := A ⧸ Ideal.span ({e} : Set A)
    let B₁ := A ⧸ Ideal.span ({1 - e} : Set A)
    let _ : IsAbsolutelyIntegrallyClosed B₀ := inferInstance
    let _ : IsAbsolutelyIntegrallyClosed B₁ := inferInstance
    obtain ⟨φ₀, φ₁, hφ₀, hφ₁⟩ :=
      component_residue_ringEquiv_after_idempotent_split (I := I) hquot_e
    have hcomponentEquivs :
        ((B₀ ⧸ J₀) ≃+* ((A ⧸ I) ⧸ Ideal.span ({ebar} : Set (A ⧸ I)))) ×
          ((B₁ ⧸ J₁) ≃+* ((A ⧸ I) ⧸ Ideal.span ({1 - ebar} : Set (A ⧸ I)))) := by
      -- Proof comment: this is the transport package from Agent C's product-split plan; it
      -- replaces the previous direct component-by-component quotient comparison attempts.
      exact ⟨by simpa [B₀, J₀, π₀] using φ₀, by simpa [B₁, J₁, π₁] using φ₁⟩
    have hquotSurj₀ :
        Function.Surjective
          (Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I)))).idempotentMap :=
      -- Proof comment: the `ebar = 0` quotient branch is itself an idempotent quotient, so its
      -- idempotents already lift before transporting back to `B₀`.
      quotientMk_span_singleton_surjective_idempotentMap (R := A ⧸ I) hpartition.1
    have hquotSurj₁ :
        Function.Surjective
          (Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I)))).idempotentMap :=
      -- Proof comment: the complementary quotient branch is the same canonical idempotent split.
      quotientMk_span_singleton_surjective_idempotentMap
        (R := A ⧸ I) hpartition.1.one_sub
    have hsurj₀ :
        Function.Surjective (Ideal.Quotient.mk J₀).idempotentMap := by
      -- Proof comment: the `e = 0` branch inherits idempotent lifting by transporting along the
      -- already verified quotient equivalence `φ₀`.
      exact
        component_idempotent_surjectivity_after_idempotent_split
          (I := I) π₀ J₀ (Ideal.span ({ebar} : Set (A ⧸ I))) φ₀ hφ₀ hsurj hquotSurj₀
    have hsurj₁ :
        Function.Surjective (Ideal.Quotient.mk J₁).idempotentMap := by
      -- Proof comment: the complementary branch is identical after replacing `e` by `1 - e`.
      exact
        component_idempotent_surjectivity_after_idempotent_split
          (I := I) π₁ J₁ (Ideal.span ({1 - ebar} : Set (A ⧸ I))) φ₁ hφ₁ hsurj hquotSurj₁
    -- TODO: use `hsurj₀` and `hsurj₁` to transport the quotient factorization to the two branch
    -- rings, prove the branch root-orientation statements, recurse after removing the linear
    -- factor in the vanishing branch, and glue the two lifted branch factorizations back through
    -- `AlgEquiv.prodQuotientOfIsIdempotentElem`.
    let _ := hcomponentEquivs
    let _ := hsurj₀
    let _ := hsurj₁
    sorry

private theorem satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    I.SatisfiesGabberRootCriterion := by
  refine ⟨hI, ?_⟩
  intro f hf
  rcases hf with ⟨n, hn, hmonic, hmap⟩
  have hcoprime :
      IsCoprime (X ^ n : (A ⧸ I)[X]) (X - 1) :=
    x_pow_isCoprime_x_sub_one (R := A ⧸ I) n
  -- The structural source step is to lift the special quotient factorization.
  obtain ⟨g, h, hg, hh, hgh, hgmap, hhmap⟩ :=
    exists_monic_coprime_factorization_lift_of_le_jacobson_and_surjective_on_idempotents
      I hI hsurj hmonic
      (by simpa using monic_X_pow n)
      (by simpa using monic_X_sub_C (1 : A ⧸ I))
      hcoprime hmap
  -- Once the `X - 1` factor is lifted, the absolute integral closedness argument gives a root in
  -- `1 + I`, and that root is automatically a root of `f`.
  obtain ⟨i, hi⟩ := exists_isRoot_of_monic_map_eq_X_sub_one I hI hh hhmap
  refine ⟨i, ?_⟩
  rw [hgh, Polynomial.IsRoot, eval_mul, hi.eq_zero, mul_zero]

/-- Over an absolutely integrally closed ring, the source hypotheses in Lemma `15.14.8` imply the
henselian owner by way of Gabber's criterion. -/
private theorem henselianRing_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    HenselianRing A I := by
  have hGabber : I.SatisfiesGabberRootCriterion :=
    satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents I hI hsurj
  exact I.henselianRing_of_satisfiesGabberRootCriterion hGabber

/-- Lemma 15.14.8: for an absolutely integrally closed ring `A` and an ideal `I`, the pair
`(A, I)` is henselian if and only if `I` is contained in the Jacobson radical of `A` and the
quotient map `A → A ⧸ I` induces a surjection on idempotents. -/
@[stacks 0DCT]
theorem henselianRing_iff_le_jacobson_and_surjective_on_idempotents (I : Ideal A) :
    HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧
        Function.Surjective (Ideal.Quotient.mk I).idempotentMap := by
  constructor
  · intro hH
    haveI := hH
    refine ⟨I.le_ring_jacobson_of_henselianRing, ?_⟩
    exact I.quotientMk_bijective_idempotentMap_of_henselianRing.surjective
  · rintro ⟨hI, hsurj⟩
    exact henselianRing_of_le_jacobson_and_surjective_on_idempotents I hI hsurj

end Ideal

end
