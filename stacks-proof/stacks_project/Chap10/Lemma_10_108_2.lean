import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_33_1

-- Declarations for this item will be appended below by the statement pipeline.

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
