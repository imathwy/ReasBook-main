import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_108_1 (from Chap10) -/
/- Definition 10.108.1: an ideal `I ⊆ R` is pure when the quotient ring `R ⧸ I` is flat as an
`R`-module; this is the canonical owner predicate `Ideal.Pure I`, so no separate chapter-local
wrapper is needed here. -/
recall Ideal.Pure

/-! ### Lemma_10_108_2 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

namespace Ideal

/- Domain-style sampling:
* primary domain: commutative algebra of pure ideals and the localization at `1 + I`;
* sampled owner declarations:
  `Ideal.Pure`,
  `Ideal.inf_eq_mul_of_pure`,
  `Ideal.Pure.of_inf_eq_mul`,
  `Ideal.exists_eq_mul_of_pure`;
* best owner abstraction: the chapter item is source-facing `TFAE` data for the canonical owner
  `Ideal.Pure I`;
* layer triage:
  - `source-facing`: the Stacks equivalence package for a fixed ideal `I`;
  - `core/canonical`: the mathlib owner `Ideal.Pure` and its canonical derived lemmas;
  - `bridge/view`: the source-facing localization submonoid `1 + I`, implemented by the local
    owner `Ideal.oneAdd`;
* primitive data: the ideal `I` and the source-facing submonoid `1 + I`;
* derived API: the inf-equals-product criteria, the pointwise idempotence criterion, the local
  prime-support criterion, and the quotient/localization formulations.
-/

-- Proof sketch: write `a = 1 + x` and `b = 1 + y` with `x, y ∈ I`; then
-- `(1 + x) * (1 + y) = 1 + (x + y + x * y)` and the parenthesized term lies in `I` because `I`
-- is closed under addition and multiplication by ring elements.
/-- If `a` and `b` are of the form `1 + i` with `i ∈ I`, then so is `a * b`. -/
private theorem exists_mem_and_eq_one_add_of_mul {I : Ideal R} (a b : R)
    (ha : ∃ x ∈ I, a = 1 + x) (hb : ∃ y ∈ I, b = 1 + y) :
    ∃ z ∈ I, a * b = 1 + z := by
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  refine ⟨x + y + x * y, I.add_mem (I.add_mem hx hy) (I.mul_mem_right y hx), ?_⟩
  ring

/-- The multiplicative subset `1 + I` associated to the ideal `I`. -/
def oneAdd (I : Ideal R) : Submonoid R where
  carrier := { x : R | ∃ y ∈ I, x = 1 + y }
  one_mem' := ⟨0, I.zero_mem, (add_zero 1).symm⟩
  mul_mem' := fun {a b} ha hb ↦
    show a * b ∈ { x : R | ∃ y ∈ I, x = 1 + y } from
      exists_mem_and_eq_one_add_of_mul a b ha hb

/-
Lean cannot export the raw textbook notation `1 + I` as an ordinary parser notation here without
capturing genuine ring expressions `1 + x`, so the source-facing multiplicative subset is exposed
through the short owner `Ideal.oneAdd`.
-/

-- Proof sketch: this is immediate from the definition of `Ideal.oneAdd`.
/-- Membership in `1 + I` means being congruent to `1` modulo `I`. -/
@[simp] theorem mem_oneAdd_iff {I : Ideal R} {x : R} :
    x ∈ I.oneAdd ↔ ∃ y ∈ I, x = 1 + y := by
  simp [oneAdd]

/-- Helper for Lemma 10.108.2: if each factor `f a` lies in `I`, then
`1 - ∏ a ∈ s, (1 - f a)` also lies in `I`. -/
private theorem one_sub_prod_one_sub_mem {α : Type*} (I : Ideal R)
    (s : Finset α) (f : α → R) (hf : ∀ a ∈ s, f a ∈ I) :
    ((1 : R) - s.prod (fun a ↦ 1 - f a)) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is `1`, so the desired element is `0`.
      simpa using I.zero_mem
  | insert a s ha ih =>
      -- Peel off the new factor and rewrite the target in a form stable under the ideal operations.
      have hfa : f a ∈ I := hf a (by simp)
      have hs : ∀ b ∈ s, f b ∈ I := fun b hb ↦ hf b (by simp [hb])
      have htail : ((1 : R) - s.prod (fun b ↦ 1 - f b)) ∈ I := ih hs
      have hmul : (1 - f a) * ((1 : R) - s.prod (fun b ↦ 1 - f b)) ∈ I := I.mul_mem_left _ htail
      have hsum : f a + (1 - f a) * ((1 : R) - s.prod (fun b ↦ 1 - f b)) ∈ I := I.add_mem hfa hmul
      have hrewrite :
          (1 : R) - (insert a s).prod (fun b ↦ 1 - f b) =
            f a + (1 - f a) * ((1 : R) - s.prod (fun b ↦ 1 - f b)) := by
        rw [Finset.prod_insert ha]
        ring
      rw [hrewrite]
      exact hsum

/-- Helper for Lemma 10.108.2: localizing the ideal `I` at `p` is nontrivial exactly when the
localized ideal is not the zero ideal. -/
private theorem mem_support_iff_ideal_map_ne_bot (I : Ideal R) (p : PrimeSpectrum R) :
    p ∈ Module.support R I ↔
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I ≠ ⊥ := by
  -- Replace the localized module of `I` by the canonical localized ideal model.
  let e :
      LocalizedModule p.asIdeal.primeCompl I ≃ₗ[R]
        Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I :=
    IsLocalizedModule.iso p.asIdeal.primeCompl
      (Algebra.idealMap (Localization.AtPrime p.asIdeal) I)
  rw [Module.mem_support_iff]
  calc
    Nontrivial (LocalizedModule p.asIdeal.primeCompl I) ↔
        Nontrivial ↥(Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I) :=
      e.toEquiv.nontrivial_congr
    _ ↔ Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I ≠ ⊥ :=
      Submodule.nontrivial_iff_ne_bot

/-- Helper for Lemma 10.108.2: the localization of `I` at `p` is the unit ideal precisely when
`p` does not contain `I`. -/
private theorem ideal_map_atPrime_eq_top_iff_not_le (I : Ideal R) (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤ ↔ ¬ I ≤ p.asIdeal := by
  constructor
  · intro htop hle
    -- A prime containing `I` is disjoint from its prime complement, so the localized ideal
    -- cannot become the whole ring.
    have hdisjoint : Disjoint (p.asIdeal.primeCompl : Set R) (I : Set R) := by
      rw [Set.disjoint_left]
      intro x hxmem hxI
      exact hxmem (hle hxI)
    have hneTop :
        Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I ≠ ⊤ :=
      (IsLocalization.map_algebraMap_ne_top_iff_disjoint
        (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal) I).2 hdisjoint
    exact hneTop htop
  · intro hnotle
    -- Away from `V(I)`, the localized ideal contains a unit.
    exact IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime p.asIdeal) (I := I) (p := p.asIdeal) hnotle

/-- Helper for Lemma 10.108.2: kernel-membership in the localization at `1 + I` is equivalent to
the pointwise idempotence relation `x = x * y` for some `y ∈ I`. -/
private theorem mem_ker_oneAdd_localization_iff {I : Ideal R} {x : R} :
    x ∈ RingHom.ker (algebraMap R (Localization I.oneAdd)) ↔ ∃ y ∈ I, x = x * y := by
  -- Rewrite kernel-membership as the ordinary zero criterion in the localization.
  rw [RingHom.mem_ker, ← IsLocalization.mk'_one (M := I.oneAdd) (S := Localization I.oneAdd) x]
  constructor
  · intro hx
    rcases (IsLocalization.mk'_eq_zero_iff (S := Localization I.oneAdd) x 1).1 hx with ⟨s, hs⟩
    rcases (Ideal.mem_oneAdd_iff).1 s.2 with ⟨z, hz, hs_eq⟩
    have hs' : x * (1 + z) = 0 := by
      simpa [hs_eq, mul_comm] using hs
    have hrewrite : x = x * (-z) := by
      calc
        x = x * 1 := by simp
        _ = x * ((1 + z) + (-z)) := by ring
        _ = x * (1 + z) + x * (-z) := by rw [mul_add]
        _ = x * (-z) := by rw [hs', zero_add]
    exact ⟨-z, I.neg_mem hz, hrewrite⟩
  · rintro ⟨y, hy, hxy⟩
    have hy_mem : 1 + (-y) ∈ I.oneAdd := by
      exact (Ideal.mem_oneAdd_iff).2 ⟨-y, I.neg_mem hy, rfl⟩
    have hxy' : x * y = x := by
      simpa [mul_comm] using hxy.symm
    have hzero : (1 + (-y)) * x = 0 := by
      calc
        (1 + (-y)) * x = x - x * y := by ring
        _ = 0 := by rw [hxy', sub_self]
    exact (IsLocalization.mk'_eq_zero_iff (S := Localization I.oneAdd) x 1).2
      ⟨⟨1 + (-y), hy_mem⟩, hzero⟩

/-- Helper for Lemma 10.108.2: under the pointwise idempotence criterion, a prime is disjoint
from `1 + I` exactly when it contains `I`. -/
private theorem disjoint_oneAdd_iff_le_of_pointwise_idempotent {I : Ideal R}
    (h5 : ∀ x : R, x ∈ I → ∃ y ∈ I, x = x * y) (p : PrimeSpectrum R) :
    Disjoint (I.oneAdd : Set R) (p.asIdeal : Set R) ↔ I ≤ p.asIdeal := by
  constructor
  · intro hdisjoint x hx
    -- Use the source pointwise relation to build an element of `1 + I` that annihilates `x`.
    rcases h5 x hx with ⟨y, hy, hxy⟩
    have hy_mem : 1 + (-y) ∈ I.oneAdd := by
      exact (Ideal.mem_oneAdd_iff).2 ⟨-y, I.neg_mem hy, rfl⟩
    have hxy' : x * y = x := by
      simpa [mul_comm] using hxy.symm
    have hprod : (1 + (-y)) * x = 0 := by
      calc
        (1 + (-y)) * x = x - x * y := by ring
        _ = 0 := by rw [hxy', sub_self]
    have hprod_mem : (1 + (-y)) * x ∈ p.asIdeal := by
      simpa [hprod] using p.asIdeal.zero_mem
    have hone_not_mem : 1 + (-y) ∉ p.asIdeal := by
      intro hone_mem
      exact hdisjoint.le_bot ⟨hy_mem, hone_mem⟩
    exact (p.isPrime.mul_mem_iff_mem_or_mem.mp hprod_mem).resolve_left hone_not_mem
  · intro hle
    -- If `I ≤ p`, then no element of `1 + I` can belong to the prime `p`.
    rw [Set.disjoint_left]
    intro x hxone hxprime
    rcases (Ideal.mem_oneAdd_iff).1 hxone with ⟨y, hy, rfl⟩
    have hy_mem : y ∈ p.asIdeal := hle hy
    have hone : (1 : R) ∈ p.asIdeal := by
      simpa using p.asIdeal.sub_mem hxprime hy_mem
    have htop : p.asIdeal = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      exact hone
    exact p.isPrime.ne_top htop

/-- Helper for Lemma 10.108.2: localizing `R ⧸ I` at `p` agrees with quotienting the local ring
by the localized ideal. -/
private noncomputable def localized_quotient_atPrime_linearEquiv_quotient_map
    (I : Ideal R) (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal (R ⧸ I) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I :=
  (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (R ⧸ I)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (Localization.AtPrime p.asIdeal) I).symm.toLinearEquiv

/-- Helper for Lemma 10.108.2: if an ideal is either `⊥` or `⊤`, then its quotient is flat over
the ambient ring. -/
private theorem flat_quotient_of_eq_bot_or_eq_top {A : Type*} [CommRing A]
    (J : Ideal A) (hJ : J = ⊥ ∨ J = ⊤) : Module.Flat A (A ⧸ J) := by
  rcases hJ with rfl | rfl
  · -- Quotienting by `⊥` gives back the ambient ring, which is flat over itself.
    exact Module.Flat.of_linearEquiv (AlgEquiv.quotientBot A A).toLinearEquiv
  · -- Quotienting by `⊤` gives the zero module, so every tensor inclusion is trivially injective.
    rw [Module.Flat.iff_lTensor_injectiveₛ]
    intro P _ _ N
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := (Ideal.Quotient.subsingleton_iff).2 rfl
    exact Function.injective_of_subsingleton _

/-- Helper for Lemma 10.108.2: clause `(7)` gives the flatness of each prime localization of
`R ⧸ I` by first identifying it with a quotient of the localized ring. -/
private theorem localized_quotient_atPrime_flat_of_map_eq_bot_or_top
    (I : Ideal R) (p : PrimeSpectrum R)
    (h :
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊥ ∨
        Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤) :
    Module.Flat (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal (R ⧸ I)) := by
  -- First prove flatness on the quotient model controlled directly by clause `(7)`.
  have hflatQuot :
      Module.Flat (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I) :=
    flat_quotient_of_eq_bot_or_eq_top
      (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I) h
  letI :
      Module.Flat (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I) :=
    hflatQuot
  -- Transport flatness back across the canonical localization/quotient comparison.
  exact Module.Flat.of_linearEquiv
    (localized_quotient_atPrime_linearEquiv_quotient_map I p)

-- Proof sketch: combine the flatness criterion for pure ideals from Lemma `10.39.5` with the
-- canonical statements in `Mathlib/RingTheory/Ideal/Pure.lean`. The implications between the
-- finite-family, localization, support, kernel, and localization-quotient formulations follow the
-- Stacks proof by comparing `I` with its localizations and the localization at the multiplicative
-- subset `1 + I`.
/-- Lemma 10.108.2: for an ideal `I` of a commutative ring `R`, the following are equivalent:
`I` is pure; intersections with `I` agree with ideal products for all ideals, for finitely
generated ideals, and for principal ideals; each element or finite family of elements of `I` is
fixed by multiplication by some element of `I`; every localization of `I` at a prime is either
zero or the unit ideal; `Supp(I) = Spec(R) \ V(I)`; `I` is the kernel of the map
`R → (1 + I)⁻¹R`; `R ⧸ I` is isomorphic to a localization of `R`; and specifically
`R ⧸ I ≃ (1 + I)⁻¹R` as `R`-algebras. Clauses `(2)`, `(3)`, `(4)`, and `(5)` are stated in the
same canonical orientation as the owner lemmas
`Ideal.inf_eq_mul_of_pure`, `Ideal.Pure.of_inf_eq_mul`, and `Ideal.exists_eq_mul_of_pure`. -/
theorem pure_tfae (I : Ideal R) :
    List.TFAE
      [ I.Pure
      , ∀ J : Ideal R, I ⊓ J = I * J
      , ∀ ⦃J : Ideal R⦄, J.FG → I ⊓ J = I * J
      , ∀ x : R, I ⊓ Ideal.span ({x} : Set R) = I * Ideal.span ({x} : Set R)
      , ∀ x : R, x ∈ I → ∃ y ∈ I, x = x * y
      , ∀ s : Finset R, (∀ x ∈ s, x ∈ I) → ∃ y ∈ I, ∀ x ∈ s, x = x * y
      , ∀ p : PrimeSpectrum R,
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊥ ∨
            Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤
      , Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ
      , RingHom.ker (algebraMap R (Localization I.oneAdd)) = I
      , ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S)
      , Nonempty ((R ⧸ I) ≃ₐ[R] Localization I.oneAdd)
      ] := by
  -- Follow the source proof cycle: the owner API handles `(1)` through `(5)`, then the finite-set,
  -- localization, support, kernel, and quotient-localization clauses complete the equivalence.
  tfae_have 1 → 2 := by
    intro hI J
    -- Once `I` is pure, the canonical owner theorem gives the intersection/product equality.
    letI : I.Pure := hI
    simpa using (Ideal.inf_eq_mul_of_pure I J)
  tfae_have 2 → 3 := by
    intro h2 J hJ
    -- Clause `(3)` is the finitely generated specialization of clause `(2)`.
    exact h2 J
  tfae_have 3 → 4 := by
    intro h3 x
    -- Principal ideals are finitely generated, so clause `(4)` is an immediate specialization.
    exact h3 (Submodule.fg_span_singleton x)
  tfae_have 4 → 5 := by
    intro h4 x hx
    -- Place `x` in the intersection with its principal ideal and then unpack the product membership.
    have hxmul : x ∈ I * Ideal.span ({x} : Set R) := by
      rw [← h4 x]
      exact ⟨hx, Ideal.subset_span (by simp)⟩
    rcases (Ideal.mem_mul_span_singleton).1 hxmul with ⟨y, hy, hyx⟩
    exact ⟨y, hy, by simpa [mul_comm] using hyx.symm⟩
  tfae_have 5 → 6 := by
    intro h5 s hs
    classical
    -- Choose the source witnesses `y_x` and package them into the single element
    -- `1 - ∏ (1 - y_x)` from the textbook proof.
    let f : R → R := fun x ↦ if hx : x ∈ s then Classical.choose (h5 x (hs x hx)) else 0
    have hf_mem : ∀ x ∈ s, f x ∈ I := by
      intro x hx
      have hchoose := Classical.choose_spec (h5 x (hs x hx))
      dsimp [f]
      rw [dif_pos hx]
      exact hchoose.1
    have hf_fix : ∀ x ∈ s, x = x * f x := by
      intro x hx
      have hchoose := Classical.choose_spec (h5 x (hs x hx))
      dsimp [f]
      rw [dif_pos hx]
      exact hchoose.2
    refine ⟨((1 : R) - s.prod (fun x ↦ 1 - f x)), one_sub_prod_one_sub_mem I s f hf_mem, ?_⟩
    intro x hx
    have hxf : x * (1 - f x) = 0 := by
      have hfix' : x * f x = x := (hf_fix x hx).symm
      calc
        x * (1 - f x) = x - x * f x := by ring
        _ = 0 := by rw [hfix', sub_self]
    have hprod_zero : x * s.prod (fun a ↦ 1 - f a) = 0 := by
      calc
        x * s.prod (fun a ↦ 1 - f a)
            = x * ((1 - f x) * (s.erase x).prod (fun a ↦ 1 - f a)) := by
                rw [← Finset.mul_prod_erase s (fun a ↦ 1 - f a) hx]
        _ = (x * (1 - f x)) * (s.erase x).prod (fun a ↦ 1 - f a) := by ring
        _ = 0 := by rw [hxf, zero_mul]
    -- The chosen product annihilates the complementary factor, so multiplication by the new `y`
    -- fixes `x`.
    have hy_fix : x * ((1 : R) - s.prod (fun a ↦ 1 - f a)) = x := by
      calc
        x * ((1 : R) - s.prod (fun a ↦ 1 - f a)) = x - x * s.prod (fun a ↦ 1 - f a) := by ring
        _ = x := by rw [hprod_zero, sub_zero]
    exact hy_fix.symm
  tfae_have 6 → 5 := by
    intro h6 x hx
    -- Apply the finite-set clause to the singleton `{x}`.
    have hsingle : ∀ z ∈ ({x} : Finset R), z ∈ I := by
      intro z hz
      have hz' : z = x := by simpa using hz
      simpa [hz'] using hx
    rcases h6 {x} hsingle with ⟨y, hy, hxy⟩
    exact ⟨y, hy, by simpa using hxy x (by simp)⟩
  tfae_have 3 → 1 := by
    intro h3
    -- This is exactly the converse owner criterion for pure ideals.
    exact Ideal.Pure.of_inf_eq_mul I h3
  tfae_have 5 → 7 := by
    intro h5 p
    by_cases hle : I ≤ p.asIdeal
    · -- Over primes containing `I`, the source criterion forces the localized ideal to vanish.
      left
      exact (Ideal.map_eq_bot_iff_le_ker (algebraMap R (Localization.AtPrime p.asIdeal))).2
        (Ideal.le_ker_atPrime_of_forall_exists_eq_mul h5 hle)
    · -- Away from `V(I)`, the localized ideal contains a unit.
      right
      exact IsLocalization.AtPrime.map_eq_top_of_not_le
        (S := Localization.AtPrime p.asIdeal) (I := I) (p := p.asIdeal) hle
  tfae_have 7 → 1 := by
    intro h7
    -- Route correction: prove purity by checking flatness primewise on `R ⧸ I`, then identify
    -- each maximal localization with the quotient of the local ring by the localized ideal.
    change Module.Flat R (R ⧸ I)
    apply Module.flat_of_localized_maximal
    intro P hP
    -- Clause `(7)` is exactly the `⊥/⊤` alternative needed for the localized quotient model.
    rw [← Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl]
    simpa [LocalizedModule.AtPrime] using
      localized_quotient_atPrime_flat_of_map_eq_bot_or_top I ⟨P, inferInstance⟩
        (h7 ⟨P, inferInstance⟩)
  tfae_have 7 → 8 := by
    intro h7
    ext p
    rw [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro hp hle
      -- Under clause `(7)`, nontriviality of the localized ideal forces the non-vanishing branch.
      have hneBot := (mem_support_iff_ideal_map_ne_bot I p).1 hp
      rcases h7 p with hbot | htop
      · exact hneBot hbot
      · exact ((ideal_map_atPrime_eq_top_iff_not_le I p).1 htop) hle
    · intro hp
      -- Outside `V(I)`, the localized ideal is `⊤`, hence certainly nontrivial.
      have htop :
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤ :=
        (ideal_map_atPrime_eq_top_iff_not_le I p).2 hp
      exact (mem_support_iff_ideal_map_ne_bot I p).2 (by simpa [htop])
  tfae_have 8 → 7 := by
    intro h8 p
    by_cases hle : I ≤ p.asIdeal
    · -- On `V(I)`, the support description says the localized ideal is trivial.
      left
      by_contra hneBot
      have hpnot : p ∉ Module.support R I := by
        rw [h8, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus]
        exact not_not.mpr hle
      exact hpnot ((mem_support_iff_ideal_map_ne_bot I p).2 hneBot)
    · -- Off `V(I)`, the localized ideal is the whole localized ring.
      right
      exact (ideal_map_atPrime_eq_top_iff_not_le I p).2 hle
  tfae_have 5 → 9 := by
    intro h5
    ext x
    constructor
    · intro hxker
      rcases (mem_ker_oneAdd_localization_iff (I := I) (x := x)).1 hxker with ⟨y, hy, hxy⟩
      -- The kernel is always contained in `I` because `x = x * y` with `y ∈ I`.
      rw [hxy]
      exact I.mul_mem_left x hy
    · intro hx
      rcases h5 x hx with ⟨y, hy, hxy⟩
      -- Clause `(5)` provides exactly the annihilating denominator in `1 + I`.
      exact (mem_ker_oneAdd_localization_iff (I := I) (x := x)).2 ⟨y, hy, hxy⟩
  tfae_have 9 → 5 := by
    intro h9 x hx
    have hxker : x ∈ RingHom.ker (algebraMap R (Localization I.oneAdd)) := by
      simpa [h9] using hx
    -- Re-read the kernel equality as the source pointwise idempotence condition.
    exact (mem_ker_oneAdd_localization_iff (I := I) (x := x)).1 hxker
  tfae_have 9 → 11 := by
    intro h9
    have h5 : ∀ x : R, x ∈ I → ∃ y ∈ I, x = x * y := by
      intro x hx
      have hxker : x ∈ RingHom.ker (algebraMap R (Localization I.oneAdd)) := by
        simpa [h9] using hx
      exact (mem_ker_oneAdd_localization_iff (I := I) (x := x)).1 hxker
    have hrange :
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization I.oneAdd))) =
          PrimeSpectrum.zeroLocus (I : Set R) := by
      -- The source pointwise criterion identifies the image of the localization map with `V(I)`.
      rw [PrimeSpectrum.localization_comap_range (S := Localization I.oneAdd) (M := I.oneAdd)]
      ext p
      rw [Set.mem_setOf_eq]
      simpa [PrimeSpectrum.mem_zeroLocus] using
        (disjoint_oneAdd_iff_le_of_pointwise_idempotent (I := I) h5 p)
    have hclosed :
        IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization I.oneAdd)))) := by
      rw [hrange]
      exact PrimeSpectrum.isClosed_zeroLocus (I : Set R)
    have hsurj :
        Function.Surjective (algebraMap R (Localization I.oneAdd)) :=
      algebraMap_surjective_of_isClosed_range_comap (R := R) (S := I.oneAdd) hclosed
    let f : R →ₐ[R] Localization I.oneAdd := Algebra.ofId R (Localization I.oneAdd)
    have hf : Function.Surjective f := by
      simpa [f] using hsurj
    let e : (R ⧸ RingHom.ker f) ≃ₐ[R] Localization I.oneAdd := by
      simpa [f] using (Ideal.quotientKerAlgEquivOfSurjective hf :
        (R ⧸ RingHom.ker f) ≃ₐ[R] Localization I.oneAdd)
    have hkerf : RingHom.ker f = I := by
      simpa [f] using h9
    -- Surjectivity identifies the localization with the quotient by its kernel, and clause `(9)`
    -- identifies that kernel with `I`.
    exact ⟨(Ideal.quotientEquivAlgOfEq R hkerf.symm).trans e⟩
  tfae_have 11 → 10 := by
    intro h11
    -- Clause `(11)` is the special case `S = 1 + I`.
    exact ⟨I.oneAdd, h11⟩
  tfae_have 10 → 1 := by
    rintro ⟨T, ⟨e⟩⟩
    -- Transport flatness across the algebra equivalence from the localization model.
    letI : Module.Flat R (Localization T) := IsLocalization.flat (Localization T) T
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  tfae_finish

end Ideal

end

/-! ### Lemma_10_108_3 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.108.3: if `I, J ⊆ R` are pure ideals and `V(I) = V(J)` in `Spec(R)`, then `I = J`.
This is exactly the canonical theorem `Ideal.zeroLocus_inj_of_pure`. -/
recall Ideal.zeroLocus_inj_of_pure

end

/-! ### Lemma_10_108_4 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

namespace Ideal

/-- Helper for Lemma 10.108.4: the textbook ideal
`{x : R | ∃ y ∈ J, x = x * y}` contains `0`. -/
private theorem pointwiseFixedIdeal_zero_mem (J : Ideal R) :
    (0 : R) ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- The zero element is fixed by multiplication with `0 ∈ J`.
  exact ⟨0, J.zero_mem, by simp⟩

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under addition. -/
private theorem add_fixed_by_pointwise_witness {x y f g : R}
    (hx : x = x * f) (hy : y = y * g) :
    x + y = (x + y) * (f + g - f * g) := by
  -- Rewrite the mixed terms using the original fixed-point identities.
  have hxg : x * g = x * (f * g) := by
    calc
      x * g = (x * f) * g := by rw [← hx]
      _ = x * (f * g) := by rw [mul_assoc]
  have hyf : y * f = y * (f * g) := by
    calc
      y * f = (y * g) * f := by rw [← hy]
      _ = y * (g * f) := by rw [mul_assoc]
      _ = y * (f * g) := by rw [mul_comm g f]
  -- Expand the textbook witness and cancel the cross terms explicitly.
  calc
    x + y = x * f + y := by rw [← hx]
    _ = x * f + y * g := by rw [← hy]
    _ = x * f + x * g - x * (f * g) + (y * f + y * g - y * (f * g)) := by
      rw [hxg, hyf]
      ring
    _ = (x + y) * (f + g - f * g) := by ring

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under addition. -/
private theorem pointwiseFixedIdeal_add_mem {J : Ideal R} {x y : R}
    (hx : x ∈ { x : R | ∃ y ∈ J, x = x * y })
    (hy : y ∈ { x : R | ∃ y ∈ J, x = x * y }) :
    x + y ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- Use the textbook witness `f + g - f * g` coming from the two fixed-point relations.
  rcases hx with ⟨f, hf, hxf⟩
  rcases hy with ⟨g, hg, hyg⟩
  refine ⟨f + g - f * g, ?_, ?_⟩
  · -- Ideal closure gives membership of the textbook witness in `J`.
    exact J.sub_mem (J.add_mem hf hg) (J.mul_mem_right g hf)
  · -- The standalone algebra lemma packages the verification-left-to-the-reader identity.
    exact add_fixed_by_pointwise_witness hxf hyg

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under multiplication
by ring elements. -/
private theorem pointwiseFixedIdeal_smul_mem {J : Ideal R} (r : R) {x : R}
    (hx : x ∈ { x : R | ∃ y ∈ J, x = x * y }) :
    r * x ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- The same witness works after multiplying the fixed element by `r`.
  rcases hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, by simpa [mul_assoc] using congrArg (fun t : R ↦ r * t) hxy⟩

/-- Helper for Lemma 10.108.4: the textbook multiplicative set `(R \ p)(1 + J)`. -/
private def primeComplMulOneAdd (p : PrimeSpectrum R) (J : Ideal R) : Submonoid R where
  carrier := { x : R | ∃ a ∈ p.asIdeal.primeCompl, ∃ b ∈ J.oneAdd, x = a * b }
  one_mem' := by
    refine ⟨1, ?_, 1, (Ideal.mem_oneAdd_iff (I := J) (x := (1 : R))).2 ⟨0, J.zero_mem, by simp⟩, by simp⟩
    show (1 : R) ∉ p.asIdeal
    intro h1
    exact p.2.1 ((Ideal.eq_top_iff_one _).2 h1)
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, ?_, b * d, J.oneAdd.mul_mem hb hd, by ring⟩
    show a * c ∈ p.asIdeal.primeCompl
    intro hac
    exact (p.2.mem_or_mem hac).elim ha hc

/-- Helper for Lemma 10.108.4: the source ideal
`I = {x : R | ∃ y ∈ J, x = x * y}`. -/
def pointwiseFixedIdeal (J : Ideal R) : Ideal R where
  carrier := { x : R | ∃ y ∈ J, x = x * y }
  zero_mem' := pointwiseFixedIdeal_zero_mem J
  add_mem' := fun hx hy ↦ pointwiseFixedIdeal_add_mem hx hy
  smul_mem' := fun r _ hx ↦ pointwiseFixedIdeal_smul_mem r hx

/-- Helper for Lemma 10.108.4: the textbook source ideal is contained in `J`. -/
theorem pointwiseFixedIdeal_le (J : Ideal R) :
    pointwiseFixedIdeal J ≤ J := by
  -- Any witness `x = x * y` with `y ∈ J` puts `x` back into `J`.
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩
  rw [hxy]
  exact J.mul_mem_left x hy

/-- Helper for Lemma 10.108.4: if `x = x * y`, then `x = x * y ^ (n + 1)` for every `n`. -/
private theorem eq_mul_pow_succ_of_eq_mul {x y : R} (hxy : x = x * y) :
    ∀ n : ℕ, x = x * y ^ (n + 1) := by
  -- First show that every positive power of `y` still fixes `x`.
  have hpow : ∀ n : ℕ, x * y ^ n = x := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          x * y ^ (n + 1) = (x * y ^ n) * y := by rw [pow_succ, mul_assoc]
          _ = x * y := by rw [ihn]
          _ = x := by rw [← hxy]
  intro n
  exact (hpow (n + 1)).symm

-- Proof sketch: identify `V(I)` with `Spec (R ⧸ I)` via the quotient-spectrum equivalence. Since
-- `I` is pure, the quotient map `R → R ⧸ I` is flat, so `Spec (R ⧸ I) → Spec R` is generalizing by
-- `RingHom.Flat.generalizingMap_comap`. Transporting this along the quotient identification shows
-- that `V(I)` is stable under generalization.
/-- The zero locus of a pure ideal is stable under generalization in `Spec(R)`. -/
theorem stableUnderGeneralization_zeroLocus_of_pure (I : Ideal R) (hI : I.Pure) :
    StableUnderGeneralization (zeroLocus (I : Set R)) := by
  -- The quotient map realizes `V(I)` as the range of `Spec(R ⧸ I) → Spec(R)`.
  let image : Set (PrimeSpectrum R) := Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  have himage : StableUnderGeneralization image := by
    letI : (Ideal.Quotient.mk I).Flat := hI
    exact (RingHom.Flat.generalizingMap_comap (f := Ideal.Quotient.mk I) hI).stableUnderGeneralization_range
  have hrange : image = zeroLocus (I : Set R) := by
    simpa [image, Ideal.mk_ker] using
      (range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  simpa [image, hrange] using himage

/-- Helper for Lemma 10.108.4: for a radical ideal `J` whose zero locus is stable under
generalization, the source ideal `pointwiseFixedIdeal J` cuts out the same closed subset. -/
theorem zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization {J : Ideal R}
    (hJrad : J.IsRadical) (hJgen : StableUnderGeneralization (zeroLocus (J : Set R))) :
    zeroLocus (pointwiseFixedIdeal J : Set R) = zeroLocus (J : Set R) := by
  apply Set.Subset.antisymm
  · intro p hp
    -- Route correction: keep the Stacks multiplicative-set argument instead of switching to a
    -- clopen/idempotent classification of the closed subset.
    let T : Submonoid R := primeComplMulOneAdd p J
    have hzero_not_mem : (0 : R) ∉ T := by
      intro hzero
      rcases hzero with ⟨a, ha, b, hb, hab⟩
      rcases (Ideal.mem_oneAdd_iff (I := J)).1 hb with ⟨y, hy, hby⟩
      have hab' : a * (1 + y) = 0 := by
        simpa [hby] using hab.symm
      have ha_mem : a ∈ pointwiseFixedIdeal J := by
        refine ⟨-y, J.neg_mem hy, ?_⟩
        calc
          a = a * 1 := by simp
          _ = a * ((1 + y) + (-y)) := by ring
          _ = a * (1 + y) + a * (-y) := by rw [mul_add]
          _ = a * (-y) := by rw [hab', zero_add]
      have ha_in_p : a ∈ p.asIdeal := hp (show a ∈ pointwiseFixedIdeal J from ha_mem)
      exact ha ha_in_p
    have hdisj0 : Disjoint ((⊥ : Ideal R) : Set R) (T : Set R) := by
      rw [Set.disjoint_left]
      intro x hxbot hxT
      have hx0 : x = 0 := by simpa using hxbot
      exact hzero_not_mem (by simpa [hx0] using hxT)
    obtain ⟨q, hqprime, -, hqdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) T hdisj0
    have hqle : q ≤ p.asIdeal := by
      intro x hxq
      by_contra hxp
      have hxT : x ∈ T := by
        refine ⟨x, hxp, 1, (Ideal.mem_oneAdd_iff (I := J) (x := (1 : R))).2 ⟨0, J.zero_mem, by simp⟩, by simp⟩
      exact hqdisj.le_bot ⟨hxq, hxT⟩
    have hq_oneAdd_disj : Disjoint (q : Set R) (J.oneAdd : Set R) := by
      rw [Set.disjoint_left]
      intro x hxq hxone
      have hxT : x ∈ T := by
        refine ⟨1, ?_, x, hxone, by simp⟩
        show (1 : R) ∉ p.asIdeal
        intro h1
        exact p.2.1 ((Ideal.eq_top_iff_one _).2 h1)
      exact hqdisj.le_bot ⟨hxq, hxT⟩
    have hproper : q ⊔ J ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ q ⊔ J := by simpa [htop]
      rcases Submodule.mem_sup.1 h1 with ⟨a, haq, b, hbj, hab⟩
      have hone_eq : 1 - b = a := by
        calc
          1 - b = a + b - b := by rw [hab]
          _ = a := by ring
      have hone_sub : 1 - b ∈ q := by
        simpa [hone_eq] using haq
      have hone_mem : 1 - b ∈ J.oneAdd := by
        exact (Ideal.mem_oneAdd_iff (I := J) (x := 1 - b)).2 ⟨-b, J.neg_mem hbj, by ring⟩
      exact hq_oneAdd_disj.le_bot ⟨hone_sub, hone_mem⟩
    obtain ⟨m, hmmax, hqmJ⟩ := Ideal.exists_le_maximal (q ⊔ J) hproper
    let qSpec : PrimeSpectrum R := ⟨q, hqprime⟩
    let mSpec : PrimeSpectrum R := ⟨m, hmmax.isPrime⟩
    have hm_mem : mSpec ∈ zeroLocus (J : Set R) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      show J ≤ m
      exact le_trans le_sup_right hqmJ
    have hqm : qSpec ≤ mSpec := by
      show q ≤ m
      exact le_trans le_sup_left hqmJ
    have hq_mem : qSpec ∈ zeroLocus (J : Set R) := by
      exact hJgen ((PrimeSpectrum.le_iff_specializes qSpec mSpec).mp hqm) hm_mem
    rw [PrimeSpectrum.mem_zeroLocus] at hq_mem ⊢
    exact le_trans hq_mem hqle
  · -- The source ideal is contained in `J`, so its zero locus contains `V(J)`.
    exact PrimeSpectrum.zeroLocus_anti_mono_ideal (pointwiseFixedIdeal_le J)

/-- Helper for Lemma 10.108.4: if `J` is contained in the radical of its source ideal, then the
source ideal is pure. -/
theorem pointwiseFixedIdeal_pure_of_le_radical (J : Ideal R)
    (hJle : J ≤ (pointwiseFixedIdeal J).radical) :
    (pointwiseFixedIdeal J).Pure := by
  -- Use clause `(5)` of Lemma `10.108.2`, replacing the original witness in `J` by a power that
  -- already lies in the source ideal.
  exact ((Ideal.pure_tfae (pointwiseFixedIdeal J)).out 4 0).mp <| by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases (Ideal.mem_radical_iff.mp (hJle hy)) with ⟨n, hn⟩
    cases n with
    | zero =>
        have htop : pointwiseFixedIdeal J = ⊤ :=
          (pointwiseFixedIdeal J).eq_top_of_isUnit_mem (by simpa using hn) (by simpa)
        refine ⟨1, by simpa [htop], ?_⟩
        simp
    | succ n =>
        refine ⟨y ^ (n + 1), hn, ?_⟩
        simpa using eq_mul_pow_succ_of_eq_mul hxy n

end Ideal

-- Proof sketch: well-definedness is `Ideal.stableUnderGeneralization_zeroLocus_of_pure` together
-- with `PrimeSpectrum.isClosed_zeroLocus`. Injectivity is Lemma `10.108.3`, i.e.
-- `Ideal.zeroLocus_inj_of_pure`. For surjectivity, write a closed generalization-stable subset as
-- `V(J)` for a radical ideal `J`, then define the ideal `I = {x | ∃ y ∈ J, x = x * y}` from the
-- Stacks proof and use Lemma `10.108.2` to show `I` is pure and still satisfies `V(I) = V(J)`.
/-- Lemma 10.108.4: the rule `I ↦ V(I)` gives a bijection between pure ideals of `R` and closed
subsets of `Spec(R)` that are stable under generalization. -/
theorem pureIdeal_zeroLocus_bijective :
    Function.Bijective
      (fun I : { I : Ideal R // I.Pure } ↦
        (⟨zeroLocus (I.1 : Set R), isClosed_zeroLocus (I.1 : Set R),
          Ideal.stableUnderGeneralization_zeroLocus_of_pure I.1 I.2⟩ :
            { Z : Set (PrimeSpectrum R) // IsClosed Z ∧ StableUnderGeneralization Z })) := by
  constructor
  · intro I J hIJ
    -- Injectivity is the canonical owner theorem for pure ideals with the same zero locus.
    apply Subtype.ext
    letI : I.1.Pure := I.2
    letI : J.1.Pure := J.2
    exact (Ideal.zeroLocus_inj_of_pure).mp (congrArg Subtype.val hIJ)
  · intro Z
    -- Start from the radical ideal defining the given closed subset.
    let J : Ideal R := PrimeSpectrum.vanishingIdeal Z.1
    have hJrad : J.IsRadical := PrimeSpectrum.isRadical_vanishingIdeal Z.1
    have hZeq : zeroLocus (J : Set R) = Z.1 := by
      dsimp [J]
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed.mpr Z.2.1]
    have hJgen : StableUnderGeneralization (zeroLocus (J : Set R)) := by
      simpa [hZeq] using Z.2.2
    have hzero :
        zeroLocus (Ideal.pointwiseFixedIdeal J : Set R) = Z.1 := by
      exact
        (Ideal.zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization
          hJrad hJgen).trans hZeq
    have hJle : J ≤ (Ideal.pointwiseFixedIdeal J).radical := by
      simpa [hJrad.radical] using Eq.le ((PrimeSpectrum.zeroLocus_eq_iff).mp
        (Ideal.zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization
          hJrad hJgen)).symm
    have hPure : (Ideal.pointwiseFixedIdeal J).Pure :=
      Ideal.pointwiseFixedIdeal_pure_of_le_radical J hJle
    refine ⟨⟨Ideal.pointwiseFixedIdeal J, hPure⟩, ?_⟩
    apply Subtype.ext
    exact hzero

end

/-! ### Lemma_10_108_5 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/- 
Domain triage:
- primary domain: commutative algebra of pure ideals, finitely generated idempotent ideals, and
  projective quotient modules;
- sampled owner-style declarations of the same kind:
  `Ideal.Pure`,
  `Ideal.isIdempotentElem_iff_of_fg`,
  `Ideal.zeroLocus_inj_of_pure`,
  `module_finite_projective_tfae`;
- owner abstraction: `Ideal.Pure` for purity, `IsIdempotentElem I` for the ideal-side
  idempotence, and `Module.Projective R (R ⧸ I)` for the quotient clause;
- primitive data: a commutative ring `R` and an ideal `I`;
- derived/source-facing API: finite generation, openness of `V(I)`, and the textbook phrasing
  “generated by an idempotent element”.

This item stays `source-facing`, but clause `(2)` is best expressed through the canonical owner
`IsIdempotentElem I` together with finite generation; the existential generator form is then a
derived bridge via `Ideal.isIdempotentElem_iff_of_fg`.
-/

/-- The predicate that the ideal `I` is pure and finitely generated. -/
private abbrev Ideal.PureAndFg (I : Ideal R) : Prop :=
  I.Pure ∧ I.FG

/-- The canonical ideal-theoretic predicate that `I` is idempotent as
an ideal and finitely generated, which is equivalent to being generated by an idempotent element. -/
private abbrev Ideal.IsIdempotentElemAndFg (I : Ideal R) : Prop :=
  IsIdempotentElem I ∧ I.FG

/-- The predicate that `I` is pure and its zero locus is open in `Spec(R)`. -/
private abbrev Ideal.PureAndOpenZeroLocus (I : Ideal R) : Prop :=
  I.Pure ∧ IsOpen (zeroLocus (I : Set R))

/-- Helper for Lemma 10.108.5: the quotient module `R ⧸ I` is finitely presented exactly when the
kernel ideal `I` is finitely generated. -/
private lemma finitePresentation_quotient_iff_ideal_fg (I : Ideal R) :
    Module.FinitePresentation R (R ⧸ I) ↔ I.FG := by
  constructor
  · intro hfp
    letI : Module.FinitePresentation R (R ⧸ I) := hfp
    letI : Algebra.FinitePresentation R (R ⧸ I) :=
      Algebra.FinitePresentation.of_finitePresentation R (R ⧸ I)
    -- Finite presentation of the quotient algebra forces finite generation of its kernel ideal.
    simpa using
      (Algebra.FinitePresentation.ker_fG_of_surjective
        (Algebra.ofId R (R ⧸ I)) (Ideal.Quotient.mk_surjective (I := I)))
  · intro hfg
    letI : Algebra.FinitePresentation R (R ⧸ I) :=
      Algebra.FinitePresentation.quotient (R := R) (A := R) hfg
    -- The quotient ring is cyclic as an `R`-module, so algebraic finite presentation upgrades to
    -- module finite presentation.
    exact Module.FinitePresentation.of_finite_of_finitePresentation (R := R) (S := R ⧸ I)

/-- Helper for Lemma 10.108.5: the quotient `R ⧸ I` is projective exactly when `I` is pure and
finitely generated. -/
private lemma projective_quotient_iff_pure_and_fg (I : Ideal R) :
    Module.Projective R (R ⧸ I) ↔ I.Pure ∧ I.FG := by
  have hprojective :
      (Module.Finite R (R ⧸ I) ∧ Module.Projective R (R ⧸ I)) ↔
        Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I) := by
    simpa using
      ((module_finite_projective_tfae (R := R) (M := R ⧸ I)).out 1 0
        (a := Module.Finite R (R ⧸ I) ∧ Module.Projective R (R ⧸ I))
        (b := Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I)) rfl rfl)
  have hflat :
      (Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I)) ↔
        Module.Finite R (R ⧸ I) ∧ Module.Projective R (R ⧸ I) := by
    simpa using
      ((module_finite_projective_tfae (R := R) (M := R ⧸ I)).out 0 1
        (a := Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I))
        (b := Module.Finite R (R ⧸ I) ∧ Module.Projective R (R ⧸ I)) rfl rfl)
  constructor
  · intro hproj
    have hfp_flat : Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I) := by
      -- Lemma `10.78.2` identifies projective quotients with finitely presented flat quotients.
      exact hprojective.mp ⟨inferInstance, hproj⟩
    -- Rewrite finite presentation of the quotient through finite generation of the kernel ideal.
    exact ⟨hfp_flat.2, (finitePresentation_quotient_iff_ideal_fg (R := R) I).mp hfp_flat.1⟩
  · rintro ⟨hPure, hfg⟩
    have hfp_flat : Module.FinitePresentation R (R ⧸ I) ∧ Module.Flat R (R ⧸ I) := by
      -- Purity already is flatness of the quotient, and the quotient bridge supplies finite
      -- presentation.
      exact ⟨(finitePresentation_quotient_iff_ideal_fg (R := R) I).mpr hfg, hPure⟩
    -- Return to the projective clause of Lemma `10.78.2`.
    exact (hflat.mp hfp_flat).2

/-- Helper for Lemma 10.108.5: a pure ideal with open zero locus is generated by an idempotent
element. -/
private lemma exists_idempotent_generator_of_pure_and_open_zeroLocus (I : Ideal R)
    (hPure : I.Pure) (hopen : IsOpen (zeroLocus (I : Set R))) :
    ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e := by
  letI : I.Pure := hPure
  have hclopen : IsClopen (zeroLocus (I : Set R)) := by
    exact ⟨PrimeSpectrum.isClosed_zeroLocus _, hopen⟩
  -- Lemma `10.21.3` identifies the clopen zero locus with a unique basic open cut out by an
  -- idempotent element.
  obtain ⟨e, he, heq⟩ :=
    (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hclopen).exists
  let J : Ideal R := R ∙ (1 - e)
  have hJfg : J.FG := by
    simpa [J] using (Submodule.fg_span_singleton (R := R) (x := 1 - e))
  have hJidem : IsIdempotentElem J := by
    exact (Ideal.isIdempotentElem_iff_of_fg J hJfg).mpr ⟨1 - e, he.one_sub, rfl⟩
  letI : J.Pure := Ideal.Pure.of_isIdempotentElem hJfg hJidem
  have hJspan : J = Ideal.span ({1 - e} : Set R) := rfl
  have hzero : zeroLocus (I : Set R) = zeroLocus (J : Set R) := by
    calc
      zeroLocus (I : Set R) = basicOpen e := heq
      _ = zeroLocus (J : Set R) := by
        rw [hJspan, PrimeSpectrum.zeroLocus_span]
        simpa [J] using
          (PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem (1 - e) he.one_sub).symm
  -- Lemma `10.108.3` identifies pure ideals from their equal zero loci.
  have hIJ : I = J := (Ideal.zeroLocus_inj_of_pure (I := I) (J := J)).mp hzero
  refine ⟨1 - e, he.one_sub, ?_⟩
  simpa [J] using hIJ

-- Proof sketch: use Lemma `10.108.2` to convert purity into idempotence `I = I ^ 2`, then
-- Lemma `10.21.5` to obtain an idempotent generator from finite generation. An idempotent
-- generator makes `I` pure and `V(I)` open via the standard decomposition of `R` by the
-- complementary idempotent, and also makes `R ⧸ I` a direct summand of `R`, hence projective.
-- Conversely, if `I` is pure and `V(I)` is open, then `V(I)` is clopen, so Lemma `10.21.3`
-- identifies it with `D(1 - e)` for an idempotent `e`; Lemma `10.108.3` then gives
-- `I = R ∙ e`. Finally, `R ⧸ I` is projective iff it is flat and finitely
-- presented by Lemma `10.78.2`, and finite presentation of `R ⧸ I` is equivalent to finite
-- generation of `I` by Lemma `10.5.3`.
/-- Lemma 10.108.5: for an ideal `I` of a commutative ring `R`, the following are equivalent:
`I` is pure and finitely generated; `I` is generated by an idempotent element, expressed here
canonically as `IsIdempotentElem I ∧ I.FG`; `I` is pure and `V(I)` is open in `Spec(R)`; and
`R ⧸ I` is a projective `R`-module. -/
theorem pure_fg_generated_by_idempotent_open_zeroLocus_projective_quotient_tfae (I : Ideal R) :
    List.TFAE
      [ I.PureAndFg
      , I.IsIdempotentElemAndFg
      , I.PureAndOpenZeroLocus
      , Module.Projective R (R ⧸ I)
      ] := by
  -- Use clause `(1)` as the algebraic hub: purity controls idempotence, and Lemma `10.78.2`
  -- translates the quotient-projective clause into finite presentation plus flatness.
  tfae_have 1 → 2 := by
    rintro ⟨hPure, hfg⟩
    letI : I.Pure := hPure
    -- A pure ideal is idempotent, and finite generation is already part of clause `(1)`.
    exact ⟨Ideal.isIdempotentElem_of_pure I, hfg⟩
  tfae_have 2 → 1 := by
    rintro ⟨hidem, hfg⟩
    -- A finitely generated idempotent ideal is pure.
    exact ⟨Ideal.Pure.of_isIdempotentElem hfg hidem, hfg⟩
  tfae_have 2 → 3 := by
    rintro ⟨hidem, hfg⟩
    obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem
    have hspan : (R ∙ e : Ideal R) = Ideal.span ({e} : Set R) := rfl
    have hzero : zeroLocus (I : Set R) = basicOpen (1 - e) := by
      calc
        zeroLocus (I : Set R) = zeroLocus ({e} : Set R) := by
          rw [hI, hspan, PrimeSpectrum.zeroLocus_span]
        _ = basicOpen (1 - e) := by
          simpa using PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he
    -- An idempotent generator makes the quotient flat and identifies the zero locus with a basic
    -- open.
    refine ⟨Ideal.Pure.of_isIdempotentElem hfg hidem, ?_⟩
    rw [hzero]
    exact PrimeSpectrum.isOpen_basicOpen
  tfae_have 3 → 2 := by
    rintro ⟨hPure, hopen⟩
    obtain ⟨e, he, hI⟩ :=
      exists_idempotent_generator_of_pure_and_open_zeroLocus (R := R) I hPure hopen
    have hfg : I.FG := by
      rw [hI]
      simpa using (Submodule.fg_span_singleton (R := R) (x := e))
    -- Recover ideal idempotence from the principal idempotent generator.
    exact ⟨(Ideal.isIdempotentElem_iff_of_fg I hfg).mpr ⟨e, he, hI⟩, hfg⟩
  tfae_have 1 ↔ 4 := by
    -- Lemma `10.78.2` turns the quotient-projective clause into finite presentation plus
    -- flatness, and the quotient bridge identifies finite presentation with finite generation of
    -- the kernel ideal.
    simpa [Ideal.PureAndFg] using (projective_quotient_iff_pure_and_fg (R := R) I).symm
  tfae_finish

end

/-! ### Lemma_10_108_6 (from Chap10) -/
universe u v

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.108.6: a closed subset of `Spec(R)` that is stable under generalization is
the zero locus of a pure ideal. -/
theorem exists_pure_ideal_zeroLocus_eq_of_isClosed_of_stableUnderGeneralization
    (Z : Set (PrimeSpectrum R)) (hZClosed : IsClosed Z)
    (hZGeneralizing : StableUnderGeneralization Z) :
    ∃ I : Ideal R, I.Pure ∧ zeroLocus (I : Set R) = Z := by
  -- Unpack the surjectivity direction of the pure-ideal/zero-locus bijection from Lemma 10.108.4.
  rcases (pureIdeal_zeroLocus_bijective (R := R)).surjective ⟨Z, hZClosed, hZGeneralizing⟩ with
    ⟨⟨I, hI⟩, hIeq⟩
  refine ⟨I, hI, ?_⟩
  exact congrArg Subtype.val hIeq

/-- Helper for Lemma 10.108.6: if the quotient by a pure ideal is finite locally free, then its
zero locus is open. -/
theorem isOpen_zeroLocus_of_pure_of_finiteLocallyFree_quotient
    (I : Ideal R) (_hPure : I.Pure) (hFiniteLocallyFree : Module.FiniteLocallyFree R (R ⧸ I)) :
    IsOpen (zeroLocus (I : Set R)) := by
  -- Convert finite local freeness of the quotient into projectivity via the chapter TFAE.
  obtain ⟨_, hProjective⟩ :=
    ((module_finite_projective_tfae (R := R) (M := R ⧸ I)).out 6 1).mp hFiniteLocallyFree
  -- A projective quotient is generated by an idempotent, so its zero locus is a basic open.
  rcases exists_idempotent_generator_of_projective_quotient I hProjective with
    ⟨e, he, _, hIeq⟩
  rw [hIeq, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
  exact (basicOpen (1 - e)).2

/-- Helper for Lemma 10.108.6: for a finite flat module, localization along a generalization
preserves the stalk rank. -/
theorem rankAtStalk_eq_of_le_of_finite_flat
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]
    {p q : PrimeSpectrum R} (hpq : p ≤ q) :
    Module.rankAtStalk (R := R) N p = Module.rankAtStalk (R := R) N q := by
  -- Route correction: compare both stalks after localizing at `q`, where finite flat modules are
  -- free and hence have constant stalk rank across `Spec(R_q)`.
  let S := Localization.AtPrime q.asIdeal
  let pLoc : PrimeSpectrum S :=
    ⟨Ideal.map (algebraMap R S) p.asIdeal,
      Ideal.isPrime_map_of_isLocalizationAtPrime (q := q.asIdeal) (S := S) (p := p.asIdeal) hpq⟩
  have hpLoc_comap : PrimeSpectrum.comap (algebraMap R S) pLoc = p := by
    -- The prime of `Spec(R_q)` cut out by `p` contracts back to `p`.
    apply PrimeSpectrum.ext
    simpa [S, pLoc] using
      (Ideal.under_map_of_isLocalizationAtPrime (q := q.asIdeal) (S := S) (p := p.asIdeal) hpq)
  have hqLoc_comap : PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S) = q := by
    -- The closed point of `Spec(R_q)` contracts to `q`.
    apply PrimeSpectrum.ext
    simpa [S] using (Localization.AtPrime.comap_maximalIdeal (R := R) (I := q.asIdeal))
  let T := TensorProduct R S N
  have hpBase :
      Module.rankAtStalk (R := S) T pLoc =
        Module.rankAtStalk (R := R) N p := by
    -- Base change to `R_q`, then contract the chosen prime of `Spec(R_q)` back to `p`.
    calc
      Module.rankAtStalk (R := S) T pLoc =
          Module.rankAtStalk (R := R) N (PrimeSpectrum.comap (algebraMap R S) pLoc) := by
            simpa [S] using
              (Module.rankAtStalk_baseChange (R := R) (S := S) (M := N) pLoc)
      _ = Module.rankAtStalk (R := R) N p := by rw [hpLoc_comap]
  have hqBase :
      Module.rankAtStalk (R := S) T (IsLocalRing.closedPoint S) =
        Module.rankAtStalk (R := R) N q := by
    -- Evaluate the same base-change formula at the closed point of `Spec(R_q)`.
    calc
      Module.rankAtStalk (R := S) T (IsLocalRing.closedPoint S) =
          Module.rankAtStalk (R := R) N
            (PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S)) := by
            simpa [S] using
              (Module.rankAtStalk_baseChange (R := R) (S := S) (M := N)
                (IsLocalRing.closedPoint S))
      _ = Module.rankAtStalk (R := R) N q := by rw [hqLoc_comap]
  letI : Module.Free S T := Module.free_of_flat_of_isLocalRing
  have hpFree :
      Module.rankAtStalk (R := S) T pLoc = Module.finrank S T := by
    -- Over the local ring `R_q`, the base-changed module is free of constant rank.
    exact congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := T)) pLoc
  have hqFree :
      Module.rankAtStalk (R := S) T (IsLocalRing.closedPoint S) = Module.finrank S T := by
    -- The same constant-rank formula holds at the closed point of `Spec(R_q)`.
    exact congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := T)) (IsLocalRing.closedPoint S)
  -- Chaining the two base-change identifications with the constant free rank proves the claim.
  calc
    Module.rankAtStalk (R := R) N p =
        Module.rankAtStalk (R := S) T pLoc := by
          symm
          exact hpBase
    _ = Module.finrank S T := hpFree
    _ = Module.rankAtStalk (R := S) T (IsLocalRing.closedPoint S) := by
          symm
          exact hqFree
    _ = Module.rankAtStalk (R := R) N q := hqBase

/-- Helper for Lemma 10.108.6: the support of a finite flat module is closed under
generalization. -/
theorem stableUnderGeneralization_support_of_finite_flat
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N] :
    StableUnderGeneralization (Module.support R N) := by
  intro p q hpq hq
  have hpq_le : q ≤ p := (PrimeSpectrum.le_iff_specializes q p).mpr hpq
  -- Rewrite support membership through positivity of the stalk rank and use rank constancy along
  -- generalization for finite flat modules.
  rw [← Module.rankAtStalk_pos_iff_mem_support (R := R) (M := N) q]
  rw [rankAtStalk_eq_of_le_of_finite_flat (R := R) (N := N) hpq_le]
  exact (Module.rankAtStalk_pos_iff_mem_support (R := R) (M := N) p).2 hq

/-- Helper for Lemma 10.108.6: under the global openness hypothesis, the support of a finite flat
module is open. -/
theorem isOpen_support_of_finite_flat_of_closed_generalizationStable_open
    (hOpen : ∀ Z : Set (PrimeSpectrum R), IsClosed Z →
      StableUnderGeneralization Z → IsOpen Z)
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N] :
    IsOpen (Module.support R N) := by
  -- Combine the canonical closedness of support with the previous generalization-stability lemma.
  exact hOpen (Module.support R N)
    (Module.isClosed_support (R := R) (M := N))
    (stableUnderGeneralization_support_of_finite_flat (R := R) (N := N))

/-- Helper for Lemma 10.108.6: every upper stalk-rank level set of a finite flat module is stable
under generalization. -/
theorem stableUnderGeneralization_upper_rank_level_of_finite_flat
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]
    (i : ℕ) :
    StableUnderGeneralization {p : PrimeSpectrum R | i ≤ Module.rankAtStalk (R := R) N p} := by
  intro p q hpq hq
  have hpq_le : q ≤ p := (PrimeSpectrum.le_iff_specializes q p).mpr hpq
  -- The rank is constant along generalizations for finite flat modules, so the upper-level
  -- condition transfers unchanged.
  dsimp at hq ⊢
  rw [rankAtStalk_eq_of_le_of_finite_flat (R := R) (N := N) hpq_le]
  exact hq

/-- Helper for Lemma 10.108.6: if `M` is generated by `r` elements, then its `(r + 1)`st exterior
power vanishes, so the terminal support stratum in the source filtration is empty. -/
theorem support_exteriorPower_top_eq_empty_of_surjective_free_cover
    {M : Type v} [AddCommGroup M] [Module R M] {r : ℕ}
    (π : (Fin r → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Module.support R (⋀[R]^(r + 1) M) = ∅ := by
  have hmapSurj : Function.Surjective (exteriorPower.map (r + 1) π) :=
    exteriorPower.map_surjective (n := r + 1) hπ
  have hsourceSubsingleton : Subsingleton (⋀[R]^(r + 1) (Fin r → R)) := by
    by_cases hR : Nontrivial R
    · letI : Nontrivial R := hR
      let _ : Module.Free R (Fin r → R) := Module.Free.of_basis (Pi.basisFun R (Fin r))
      let _ : Module.Finite R (Fin r → R) := Module.Finite.of_basis (Pi.basisFun R (Fin r))
      let _ : Module.Free R (⋀[R]^(r + 1) (Fin r → R)) := inferInstance
      let _ : Module.Finite R (⋀[R]^(r + 1) (Fin r → R)) := inferInstance
      have hfinrank : Module.finrank R (⋀[R]^(r + 1) (Fin r → R)) = 0 := by
        rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis (Pi.basisFun R (Fin r))]
        simpa using Nat.choose_eq_zero_of_lt (Nat.lt_succ_self r)
      exact (Module.finrank_eq_zero_iff_of_free R _).mp hfinrank
    · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      exact Module.subsingleton R _
  have htargetSubsingleton : Subsingleton (⋀[R]^(r + 1) M) :=
    Function.Surjective.subsingleton hmapSurj
  -- Convert the vanishing of the module itself into emptiness of its support.
  exact Module.support_eq_empty_iff.mpr htargetSubsingleton

/-- Helper for Lemma 10.108.6: the canonical left tensor map onto the next exterior power is
surjective. -/
-- TODO: prove surjectivity by showing each pure wedge in `⋀^(n + 1) M` is hit by the obvious
-- tensor `m₀ ⊗ (m₁ ∧ ... ∧ mₙ)`.
theorem exteriorPower_leftTensorMap_surjective
    {M : Type v} [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Surjective
      (exteriorPower.leftTensorMap (R := R) n (LinearMap.id : M →ₗ[R] M)) := sorry

/-- Helper for Lemma 10.108.6: support pulls back along a surjective map of finite modules. -/
-- TODO: after tensoring with the residue field at `p`, use surjectivity of `LinearMap.rTensor`
-- to transport nontriviality of the fiber.
theorem support_subset_of_surjective
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Set.Subset (Module.support R B) (Module.support R A) := sorry

/-- Helper for Lemma 10.108.6: the support of a tensor product lies in the support of the right
factor. -/
-- TODO: identify the residue-field fiber of `A ⊗[R] B` with `(κ(p) ⊗ A) ⊗[κ(p)] (κ(p) ⊗ B)` and
-- use vanishing of the right factor to force vanishing of the whole tensor product.
theorem support_tensorProduct_subset_right
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B] :
    Set.Subset (Module.support R (TensorProduct R A B)) (Module.support R B) := sorry

/-- Helper for Lemma 10.108.6: the exterior-power support filtration is nested. -/
-- TODO: combine the surjection `M ⊗ ⋀^n M → ⋀^(n + 1) M` with the support pullback lemmas above.
theorem support_exteriorPower_succ_subset
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) :
    Module.support R (⋀[R]^(n + 1) M) ⊆ Module.support R (⋀[R]^n M) := sorry

/-- Helper for Lemma 10.108.6: if every upper level set of a nat-valued function is clopen, then
its coercion to `ℤ` is locally constant. -/
theorem isLocallyConstant_int_of_clopen_upper_level
    {X : Type*} [TopologicalSpace X] (f : X → ℕ)
    (hopen : ∀ n : ℕ, IsOpen {x : X | n ≤ f x})
    (hclosed : ∀ n : ℕ, IsClosed {x : X | n ≤ f x}) :
    IsLocallyConstant (fun x : X ↦ (f x : ℤ)) := by
  -- Check openness of each singleton fiber using the description
  -- `{f = n} = {n ≤ f} \ {n + 1 ≤ f}`.
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro z
  cases z with
  | ofNat n =>
      have hfiber :
          (fun x : X ↦ (f x : ℤ)) ⁻¹' ({Int.ofNat n} : Set ℤ) =
            {x : X | n ≤ f x} ∩ {x : X | ¬ n + 1 ≤ f x} := by
        ext x
        constructor
        · intro hx
          have hfx : f x = n := Int.ofNat.inj hx
          subst hfx
          exact ⟨Nat.le_refl _, by simp⟩
        · rintro ⟨hn, hnot⟩
          change Int.ofNat (f x) = Int.ofNat n
          exact congrArg Int.ofNat <| le_antisymm
            (Nat.lt_succ_iff.mp <| Nat.lt_of_not_ge hnot)
            hn
      -- Intersect the open upper level set with the open complement of the next closed upper
      -- level set.
      rw [hfiber]
      exact (hopen n).inter (hclosed (n + 1)).isOpen_compl
  | negSucc n =>
      -- Negative integers never occur as `Int.ofNat (f x)`.
      have hfiber :
          (fun x : X ↦ (f x : ℤ)) ⁻¹' ({Int.negSucc n} : Set ℤ) = ∅ := by
        ext x
        simp
      rw [hfiber]
      exact isOpen_empty

/-- Helper for Lemma 10.108.6: the support of the `i`th exterior power of a finite flat module is
exactly the upper stalk-rank level set `{p | i ≤ rankAtStalk M p}`. -/
-- TODO: construct the residue-field comparison `κ(p) ⊗ ⋀^i M → ⋀^i(κ(p) ⊗ M)`, prove it is
-- surjective on pure wedges, and then translate support membership into the nonvanishing criterion
-- for exterior powers of finite-dimensional vector spaces.
theorem mem_support_exteriorPower_iff_le_rankAtStalk_of_finite_flat
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (p : PrimeSpectrum R) (i : ℕ) :
    p ∈ Module.support R (⋀[R]^i M) ↔ i ≤ Module.rankAtStalk (R := R) M p := sorry

/-- Helper for Lemma 10.108.6: under the openness hypothesis for closed subsets stable under
generalization, a finite flat module is finite locally free. -/
-- TODO: use the support/rank identification above to show all upper stalk-rank level sets are
-- clopen, deduce local constancy of the rank function, and invoke clause `(8) ⇒ (7)` of
-- `module_finite_projective_tfae`.
theorem finiteLocallyFree_of_closed_generalizationStable_open
    (hOpen : ∀ Z : Set (PrimeSpectrum R), IsClosed Z →
      StableUnderGeneralization Z → IsOpen Z)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.FiniteLocallyFree R M := sorry

/-- Helper for Lemma 10.108.6: under the openness hypothesis for closed subsets stable under
generalization, the stalk-rank function of a finite flat module is locally constant. -/
theorem isLocallyConstant_rankAtStalk_of_closed_generalizationStable_open
    (hOpen : ∀ Z : Set (PrimeSpectrum R), IsClosed Z →
      StableUnderGeneralization Z → IsOpen Z)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)) := by
  -- Once the source-local argument produces finite local freeness, the chapter TFAE turns it into
  -- local constancy of the stalk-rank function.
  have hFiniteLocallyFree :
      Module.FiniteLocallyFree R M :=
    finiteLocallyFree_of_closed_generalizationStable_open (R := R) (M := M) hOpen
  have hTfae :
      Module.Finite R M ∧
        Module.freeLocus R M = Set.univ ∧
          IsLocallyConstant
            (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)) :=
    ((module_finite_projective_tfae (R := R) (M := M)).out 6 7).mp hFiniteLocallyFree
  exact hTfae.2.2

/- Domain triage:
* primary domain: commutative algebra on `Spec R`, relating generalization-stable closed subsets to
  Zariski-local finite freeness of finite flat modules;
* sampled owner declarations in this domain:
  `StableUnderGeneralization`,
  `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`,
  `Module.FiniteLocallyFree`,
  and `module_finite_projective_tfae`;
* owner abstraction choice: the right-hand side should use the chapter owner
  `Module.FiniteLocallyFree`, and the left-hand side should use the topological owner
  `StableUnderGeneralization` rather than the wrong order-theoretic surrogate `IsLowerSet`;
* layer: `source-facing`, since the item states the textbook equivalence itself, while both sides
  are expressed through their canonical owners.
-/

-- Proof sketch: for `(2) → (1)`, apply the finite-flat-to-finite-locally-free hypothesis to the
-- quotient by a pure ideal cutting out the closed subset and then use the pure-ideal description
-- of Lemma `10.108.4` to identify the resulting open subset. For `(1) → (2)`, show that the
-- support of a finite flat module is closed and closed under generalizations, hence open by
-- hypothesis; then use the exterior powers of a finite generating family to stratify `Spec(R)` by
-- constant rank and conclude local freeness on each clopen piece.
/-- Lemma 10.108.6: every closed subset of `Spec(R)` that is closed under generalizations is open
if and only if every finite flat `R`-module is finite locally free. -/
theorem primeSpectrum_closed_generalizationClosed_isOpen_iff_finiteFlat_finiteLocallyFree :
    (∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
        Module.FiniteLocallyFree R M := by
  constructor
  · intro hOpen M _ _ _ _
    -- Route correction: the forward implication should now terminate at finite local freeness
    -- itself, not at the auxiliary rank-local-constancy statement.
    exact finiteLocallyFree_of_closed_generalizationStable_open (R := R) (M := M) hOpen
  · intro hFiniteFlatLocallyFree Z hZClosed hZGeneralizing
    -- Route correction: the reverse implication can now follow the source route directly through
    -- the pure-ideal description and the projective-quotient criterion.
    rcases exists_pure_ideal_zeroLocus_eq_of_isClosed_of_stableUnderGeneralization
        Z hZClosed hZGeneralizing with ⟨I, hPure, hZeq⟩
    -- Apply the finite-flat hypothesis to the quotient by the pure ideal cutting out `Z`.
    letI : I.Pure := hPure
    have hFiniteLocallyFreeQuot : Module.FiniteLocallyFree R (R ⧸ I) :=
      hFiniteFlatLocallyFree (R ⧸ I)
    -- The remaining pure-ideal bridge turns projectivity of the quotient into openness of `V(I)`.
    have hOpenZeroLocus : IsOpen (zeroLocus (I : Set R)) :=
      isOpen_zeroLocus_of_pure_of_finiteLocallyFree_quotient I hPure hFiniteLocallyFreeQuot
    simpa [hZeq] using hOpenZeroLocus

end
