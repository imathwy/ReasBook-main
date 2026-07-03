import Mathlib
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_18_4_1 (from Chap18) -/
noncomputable section

open CategoryTheory
open scoped Representation IsMulCommutative

universe u

namespace Representation

section CharacterRingLift

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance : AddCommMonoid (R₀[k](G)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid

local instance : AddCommGroup (R₀[k](G)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)

local instance : Module ℤ (R₀[k](G)) := AddCommGroup.toIntModule (R₀[k](G))

/-- Helper for Theorem 18-18.4-1: once each restricted simple class already lifts on every
elementary subgroup, the ambient transformed simple class satisfies LinearRepresentations_Serre_1977's elementary-subgroup
frontier. -/
private theorem simple_class_elementary_frontier_of_local_restricted_simple_cases_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S]
    (hlocal :
      ∀ H : Subgroup G, IsElementary H →
        ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H)) :
    ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction
        ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
          pRegularComponentVirtualModularCharacter_isClassFunction
            (p := p) (k := k) (K := K) (G := G) lift [S]₀⟩ : H → K) ∈ R[K](H) := by
  intro H hH
  -- Rewrite the ambient restriction as the same transform built from the restricted module.
  simpa [pRegularComponentVirtualModularCharacter_restrict_simple_class
    (p := p) (k := k) (K := K) (G := G) (lift := lift) H S] using hlocal H hH

/-- Helper for Theorem 18-18.4-1: once the ordinary-elementary detection bridge is available, the
transformed simple class becomes an ordinary virtual character as soon as its elementary
restrictions are known to be ordinary. -/
private theorem associated_subgroup_explicit_character_bridge_for_simple_class_of_detection_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S]
    (hdetect :
      ∀ φ : classFunctionSubmodule K G,
        (∀ H : Subgroup G, IsElementary H →
          (H.classFunctionRestriction φ : H → K) ∈ R[K](H)) →
        (φ : G → K) ∈ R[K](G))
    (hfrontier :
      ∀ H : Subgroup G, IsElementary H →
        (H.classFunctionRestriction
          ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
            pRegularComponentVirtualModularCharacter_isClassFunction
              (p := p) (k := k) (K := K) (G := G) lift [S]₀⟩ : H → K) ∈ R[K](H)) :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Apply the global detection bridge to the bundled transformed simple class.
  exact hdetect
    ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
      pRegularComponentVirtualModularCharacter_isClassFunction
        (p := p) (k := k) (K := K) (G := G) lift [S]₀⟩
    hfrontier

/-- Helper for Theorem 18-18.4-1: after the fixed-prime elementary split is exposed, the only
remaining local source-faithful gap is the textbook simple-case lift on an elementary subgroup
`H = S × P`, before the additive basis expansion is applied. -/
private theorem fst_eq_one_of_isPElement_of_coprime_card_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P]
    (hS : Nat.Coprime p (Nat.card S)) {x : S × P} (hx : IsPElement p x) :
    x.1 = 1 := by
  -- Project the `p`-element to the prime-to-`p` factor and compare orders.
  rcases hx with ⟨n, hn⟩
  have hdiv : orderOf x.1 ∣ orderOf x := orderOf_map_dvd (MonoidHom.fst S P) x
  have hpow : orderOf x.1 ∣ p ^ n := by
    simpa [hn] using hdiv
  rcases (Nat.dvd_prime_pow Fact.out).1 hpow with ⟨m, -, hm⟩
  exact orderOf_eq_one_iff.mp <|
    calc
      orderOf x.1 = p ^ m := hm
      _ = 1 := Nat.Coprime.eq_one_of_dvd (hS.pow_left m) (hm ▸ orderOf_dvd_natCard x.1)

/-- Helper for Theorem 18-18.4-1: in a product `S × P` with `P` a `p`-group, the `P`-coordinate
of a `p`-regular element is trivial. -/
private theorem snd_eq_one_of_isPRegular_of_pGroup_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    (hP : IsPGroup p P) {x : S × P} (hx : IsPRegular p x) :
    x.2 = 1 := by
  -- Project to the `p`-group factor and use that a `p`-regular element there must have order `1`.
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) x.2
  have hdiv : orderOf x.2 ∣ orderOf x := orderOf_map_dvd (MonoidHom.snd S P) x
  have hone : orderOf x.2 = 1 := by
    exact hn.trans (Nat.Coprime.eq_one_of_dvd (hx.pow_left n) (hn ▸ hdiv))
  exact orderOf_eq_one_iff.mp hone

/-- Helper for Theorem 18-18.4-1: on `S × P`, with `|S|` prime to `p` and `P` a `p`-group, the
chosen `p`-regular component is exactly the left coordinate. -/
private theorem pRegularComponent_prod_eq_left_of_coprime_left_pGroup_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hS : Nat.Coprime p (Nat.card S)) (hP : IsPGroup p P) (x : S × P) :
    pRegularComponent p x = (x.1, 1) := by
  -- The first coordinate of the `p`-unipotent part is forced to be trivial, and the second
  -- coordinate of the `p`-regular part is forced to be trivial.
  let xu := pUnipotentComponent p x
  let xr := pRegularComponent p x
  have hdecomp : IsPComponentDecomposition p x xu xr := by
    simpa [xu, xr] using
      p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
  have hxufst : xu.1 = 1 := by
    exact fst_eq_one_of_isPElement_of_coprime_card_local (p := p) hS hdecomp.isPElement
  have hxr_snd : xr.2 = 1 := by
    exact snd_eq_one_of_isPRegular_of_pGroup_local (p := p) hP hdecomp.isPRegular
  have hxr_fst : xr.1 = x.1 := by
    have hmul := congrArg Prod.fst hdecomp.eq_mul
    simpa [xu, xr, hxufst] using hmul.symm
  exact Prod.ext hxr_fst hxr_snd

/-- Helper for Theorem 18-18.4-1: a multiplicative equivalence preserves the chosen
`p`-regular component. -/
private theorem pRegularComponent_mulEquiv_apply_local
    {A : Type u} [Group A] [Finite A] {B : Type u} [Group B] [Finite B]
    (e : A ≃* B) (x : A) :
    e (pRegularComponent p x) = pRegularComponent p (e x) := by
  -- Transport the canonical `p`-component decomposition across the equivalence and appeal to
  -- uniqueness on the target group.
  have hdecomp :
      IsPComponentDecomposition p x (pUnipotentComponent p x) (pRegularComponent p x) := by
    exact p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
  have hmap :
      IsPComponentDecomposition p (e x) (e (pUnipotentComponent p x))
        (e (pRegularComponent p x)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hdecomp.isPElement with ⟨n, hn⟩
      exact ⟨n, by simpa [e.orderOf_eq _] using hn⟩
    ·
      change Nat.Coprime p (orderOf (e (pRegularComponent p x)))
      simpa [e.orderOf_eq _] using hdecomp.isPRegular
    · simpa using hdecomp.commute.map e.toMonoidHom
    · simpa using congrArg e hdecomp.mul_eq
  exact hmap.eq_pRegularComponent

/-- Helper for Theorem 18-18.4-1: on a finite group whose order is prime to `p`, every element is
already `p`-regular. -/
private theorem isPRegular_of_coprime_card_local
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (s : S) :
    IsPRegular p s := by
  -- The order of any element divides the group order, so the prime-to-`p` cardinality forces the
  -- same coprimality for each element order.
  exact hS.coprime_dvd_right (orderOf_dvd_natCard s)

/-- Helper for Theorem 18-18.4-1: on a group whose order is prime to `p`, LinearRepresentations_Serre_1977's transformed
simple class is exactly the zero extension of the modular character, because every element is
already `p`-regular. -/
private theorem primeToP_simple_class_eq_zeroExtension_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) :
    ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] =
      FDRep.modularCharacterZeroExtension U (PrimeToPRoot.toFieldLift lift) := by
  -- On a prime-to-`p` group there is no singular branch, so both source-facing constructions
  -- evaluate by the same modular character at every element.
  ext s
  have hs : IsPRegular p s := isPRegular_of_coprime_card_local (p := p) hS s
  rw [FDRep.modularCharacterZeroExtension, dif_pos hs]
  rw [pRegularComponentVirtualModularCharacter_apply_of_isPRegular
    (p := p) (k := k) (K := K) (G := S) (lift := lift) (x := [U]₀) ⟨s, hs⟩]
  rw [virtualModularCharacter_class]

/-- Helper for Theorem 18-18.4-1: a finite group of order prime to `p` is `p`-solvable in one
step, by taking the whole group as the initial coprime layer. -/
private theorem isPSolvable_of_coprime_card_local
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) :
    IsPSolvable p S := by
  -- The height-one witness is the trivial quotient by the whole group.
  refine ⟨1, ?_⟩
  refine ⟨⊤, inferInstance, Or.inl ?_, ?_⟩
  · simpa using hS
  · letI : Subsingleton (S ⧸ (⊤ : Subgroup S)) := by
        refine ⟨?_⟩
        intro x y
        refine Quotient.inductionOn₂ x y ?_
        intro a b
        exact Quotient.sound' <| by
          simp [QuotientGroup.leftRel_apply]
    simpa using (show IsPSolvableOfHeight p 0 (S ⧸ (⊤ : Subgroup S)) from ‹_›)

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, the source `15.7` step should
directly produce the `R[K](S)` witness consumed by the later `S × P` shell. -/
private theorem primeToP_simple_class_character_witness_via_character_field_transport_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Route correction: expose LinearRepresentations_Serre_1977's exact `15.7` interface first.
  -- The local source-faithful consumer only needs the direct left-factor witness in `R[K](S)`;
  -- the earlier `PRegularConjClass`-level existential obscured that exact interface.
  have hSsolv : IsPSolvable p S :=
    isPSolvable_of_coprime_card_local (p := p) hS
  have hUirr : Representation.IsIrreducible U.ρ := FDRep.isIrreducible_of_simple U
  let _ := hSsolv
  let _ := hUirr
  -- TODO: apply the source-faithful Chapter `15.7` character-field transport on the coprime
  -- factor `S` to realize the zero extension
  -- `FDRep.modularCharacterZeroExtension U (PrimeToPRoot.toFieldLift lift)` as an ordinary
  -- character over `K`; the new helper
  -- `primeToP_simple_class_eq_zeroExtension_local` already reduces the present goal to that exact
  -- ordinary-character realization.
  sorry

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the ordinary witness required in LinearRepresentations_Serre_1977's elementary `S × P` argument. -/
private theorem primeToP_character_eq_of_pRegularConjClass_eq_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S))
    (U : FDRep k S) (X : FDRep K S)
    (hχ :
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀) :
    X.character = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Once every element of `S` is `p`-regular, equality on `PRegularConjClass S p` upgrades
  -- immediately to the pointwise equality of ordinary and transformed characters on `S`.
  ext s
  have hs : IsPRegular p s := by
    exact isPRegular_of_coprime_card_local (p := p) hS s
  have hχs := congrFun hχ (PRegularConjClass.ofSubtype p ⟨s, hs⟩)
  calc
    X.character s
        = FDRep.ordinaryCharacterOnPRegularConjClass
            (p := p) X (PRegularConjClass.ofSubtype p ⟨s, hs⟩) := by
              symm
              exact FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype
                (p := p) X ⟨s, hs⟩
    _ = virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀ (PRegularConjClass.ofSubtype p ⟨s, hs⟩) := by
            simpa using hχs
    _ = virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [U]₀ ⟨s, hs⟩ := by
          rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
    _ = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] s := by
          symm
          exact pRegularComponentVirtualModularCharacter_apply_of_isPRegular
            (p := p) (k := k) (K := K) (G := S) (lift := lift) [U]₀ ⟨s, hs⟩

/-- Helper for Theorem 18-18.4-1: a `PRegularConjClass`-level ordinary witness on a prime-to-`p`
group `S` already packages into the pointwise character-ring witness used in the source `S × P`
argument. -/
private theorem primeToP_characterRing_witness_of_pRegularConjClass_eq_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S))
    (U : FDRep k S) (X : FDRep K S)
    (hχ :
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀) :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Package the ordinary character of `X` and then collapse the restricted equality to all of
  -- `S` using that `p` does not divide `|S|`.
  let χS : R[K](S) :=
    ⟨X.character, Representation.rep_character_mem_characterRingOverField (Rep.of X.ρ)⟩
  refine ⟨χS, ?_⟩
  exact primeToP_character_eq_of_pRegularConjClass_eq_local
    (p := p) (k := k) (K := K) lift hS U X hχ

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the direct character-ring witness required in LinearRepresentations_Serre_1977's elementary `S × P` argument. -/
private theorem primeToP_simple_class_mem_characterRingOverField_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](S) := by
  -- Consume the direct `15.7` left-factor witness produced at the abstraction level LinearRepresentations_Serre_1977 uses.
  obtain ⟨χS, hχS⟩ :=
    primeToP_simple_class_character_witness_via_character_field_transport_local
      (p := p) (k := k) (K := K) lift hS U
  simpa [hχS] using χS.2

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the ordinary witness required in LinearRepresentations_Serre_1977's elementary `S × P` argument. -/
private theorem primeToP_simple_class_character_witness_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Route correction: expose the exact left-factor witness that the later `S × P` shell consumes,
  -- rather than keeping an auxiliary `PRegularConjClass` package on the critical path.
  let χS : R[K](S) :=
    ⟨([U]₀)′[p, PrimeToPRoot.toFieldLift lift],
      primeToP_simple_class_mem_characterRingOverField_local
        (p := p) (k := k) (K := K) lift hS U⟩
  -- Once the direct membership theorem is available, the source shell only needs this packaging.
  exact ⟨χS, rfl⟩

/-- Helper for Theorem 18-18.4-1: if a simple `k[S]`-module already provides the left factor of
the source `S × P` proof, then its inflated transformed class is an ordinary virtual character on
`S × P`. -/
private theorem split_product_inflated_simple_class_mem_characterRingOverField_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hS : Nat.Coprime p (Nat.card S)) (hP : IsPGroup p P)
    (U : FDRep k S) [Simple U] :
    ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
      R[K](S × P) := by
  -- The local source computation is now isolated to one adapter step:
  -- build the `fst`-pullback of the left-factor witness from
  -- `primeToP_simple_class_character_witness_local`, then identify the inflated transform with
  -- that pullback using `pRegularComponent_prod_eq_left_of_coprime_left_pGroup_local`.
  obtain ⟨χS, hχS⟩ :=
    primeToP_simple_class_character_witness_local
      (p := p) (k := k) (K := K) lift hS U
  have hprecomp :
      (fun sp : S × P ↦ (χS : S → K) sp.1) ∈ R[K](S × P) := by
    -- Pull the left-factor ordinary witness back along the projection `fst : S × P → S`.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χS.2
    · intro ψ hψ
      rcases hψ with ⟨ρ, hρfd, -, rfl⟩
      change (Rep.res (MonoidHom.fst S P) ρ).ρ.character ∈ R[K](S × P)
      letI : FiniteDimensional K ρ := hρfd
      letI : FiniteDimensional K (Rep.res (MonoidHom.fst S P) ρ) := by infer_instance
      exact Representation.rep_character_mem_characterRingOverField (Rep.res (MonoidHom.fst S P) ρ)
    · intro n
      exact (R[K](S × P)).algebraMap_mem n
    · intro x y _ _ hx hy
      simpa using (R[K](S × P)).add_mem hx hy
    · intro x y _ _ hx hy
      simpa using (R[K](S × P)).mul_mem hx hy
  have hpoint :
      ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] =
        fun sp : S × P ↦ (χS : S → K) sp.1 := by
    -- On `S × P`, the chosen `p`-regular component is exactly `(sp.1, 1)`, so the inflated
    -- transform is the `fst`-pullback of the left-factor class function.
    ext sp
    have hregS : IsPRegular p sp.1 := by
      exact hS.coprime_dvd_right (orderOf_dvd_natCard sp.1)
    have hprod :
        pRegularComponent p sp = (sp.1, (1 : P)) :=
      pRegularComponent_prod_eq_left_of_coprime_left_pGroup_local
        (p := p) hS hP sp
    have hregProd : IsPRegular p (sp.1, (1 : P)) := by
      simpa [hprod] using
        (isPRegular_pRegularComponent sp : IsPRegular p (pRegularComponent p sp))
    calc
      ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] sp
          = virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
              [FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀
              ⟨pRegularComponent p sp, isPRegular_pRegularComponent sp⟩ := by
                rw [pRegularComponentVirtualModularCharacter_apply]
      _ = virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
            [FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀
            ⟨(sp.1, (1 : P)), hregProd⟩ := by
              simpa [hprod]
      _ = virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [U]₀ ⟨sp.1, hregS⟩ := by
            -- Evaluating the inflated representation at `(sp.1, 1)` is literally evaluation of
            -- the left-factor representation at `sp.1`.
            rw [virtualModularCharacter_class, virtualModularCharacter_class]
            change
              (Multiset.map
                (fun μ ↦
                  ((lift
                      (charpolyRoot_primeToPRoot (p := p) (k := k)
                        (U.ρ.comp (MonoidHom.fst S P)) hregProd μ.2) : Kˣ) : K))
                ((U.ρ ((MonoidHom.fst S P) (sp.1, (1 : P)))).charpoly.roots.attach)).sum =
                (Multiset.map
                  (fun μ ↦
                    ((lift
                        (charpolyRoot_primeToPRoot (p := p) (k := k)
                          U.ρ hregS μ.2) : Kˣ) : K))
                  ((U.ρ sp.1).charpoly.roots.attach)).sum
            apply congrArg Multiset.sum
            congr
            ext μ
            apply congrArg (fun ζ : PrimeToPRoot p k => ((lift ζ : Kˣ) : K))
            ext
            simp [charpolyRoot_primeToPRoot_coe]
      _ = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] sp.1 := by
            symm
            exact pRegularComponentVirtualModularCharacter_apply_of_isPRegular
              (p := p) (k := k) (K := K) (G := S) (lift := lift) [U]₀ ⟨sp.1, hregS⟩
      _ = (χS : S → K) sp.1 := by
            simpa using (congrFun hχS sp.1).symm
  rw [hpoint]
  exact hprecomp

/-- Helper for Theorem 18-18.4-1: LinearRepresentations_Serre_1977's `f ↦ f'` transform commutes with transport across a
group equivalence. -/
private theorem transformed_fdRep_class_precomp_mulEquiv_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {A : Type u} [Group A] [Finite A] {B : Type u} [Group B] [Finite B]
    (e : A ≃* B) (V : FDRep k B) :
    ([FDRep.of (V.ρ.comp e.toMonoidHom)]₀)′[p, PrimeToPRoot.toFieldLift lift] =
      fun a : A ↦ ([V]₀)′[p, PrimeToPRoot.toFieldLift lift] (e a) := by
  -- Rewrite both transforms through the defining `p`-regular-component formula.
  ext a
  rw [pRegularComponentVirtualModularCharacter_apply,
    pRegularComponentVirtualModularCharacter_apply]
  -- Transport the chosen `p`-regular component across the multiplicative equivalence.
  rw [virtualModularCharacter_class, virtualModularCharacter_class]
  let aReg : { x : A // IsPRegular p x } :=
    ⟨pRegularComponent p a, isPRegular_pRegularComponent a⟩
  let bReg : { x : B // IsPRegular p x } :=
    ⟨pRegularComponent p (e a), isPRegular_pRegularComponent (e a)⟩
  have hreg :
      e (pRegularComponent p a) = pRegularComponent p (e a) :=
    pRegularComponent_mulEquiv_apply_local (p := p) e a
  have hreg' : IsPRegular p (e (pRegularComponent p a)) := by
    simpa [hreg] using (isPRegular_pRegularComponent (e a) : IsPRegular p (pRegularComponent p (e a)))
  have hsubtype :
      ((⟨e (pRegularComponent p a), hreg'⟩ : { x : B // IsPRegular p x })) = bReg := by
    apply Subtype.ext
    simpa [bReg, hreg]
  -- After identifying the two regular elements, the transported representation acts by the same
  -- operator as the original one evaluated at `e a`.
  change
    modularCharacter (PrimeToPRoot.toFieldLift lift) (V.ρ.comp e.toMonoidHom) aReg =
      modularCharacter (PrimeToPRoot.toFieldLift lift) V.ρ bReg
  change
    (Multiset.map
      (fun μ ↦
        ((lift
            (charpolyRoot_primeToPRoot (p := p) (k := k) (V.ρ.comp e.toMonoidHom)
              aReg.2 μ.2) : Kˣ) : K))
      (((V.ρ.comp e.toMonoidHom) aReg.1).charpoly.roots.attach)).sum =
      (Multiset.map
        (fun μ ↦
          ((lift
              (charpolyRoot_primeToPRoot (p := p) (k := k) V.ρ bReg.2 μ.2) : Kˣ) : K))
        ((V.ρ bReg.1).charpoly.roots.attach)).sum
  rw [show bReg = ⟨e (pRegularComponent p a), hreg'⟩ by simpa using hsubtype.symm]
  apply congrArg Multiset.sum
  congr
  ext μ
  apply congrArg (fun ζ : PrimeToPRoot p k => ((lift ζ : Kˣ) : K))
  ext
  simp [charpolyRoot_primeToPRoot_coe, aReg]

/-- Helper for Theorem 18-18.4-1: the remaining source-faithful `15.7` input on `S × P` is the
existence of a simple left-factor module whose inflation gives the transported simple module. -/
private theorem split_product_source_factorization_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    {H : Type u} [Group H]
    (hS : Nat.Coprime p (Nat.card S)) (hP : IsPGroup p P)
    (e : S × P ≃* H) (T : FDRep k H) [Simple T] :
    ∃ ρS : Representation k S T, Representation.IsIrreducible ρS ∧
      T.ρ.comp e.toMonoidHom = (ρS.comp (MonoidHom.fst S P)) := by
  -- Route correction: expose the transported `S × P`-action first, then kill the right `P`-factor
  -- by irreducibility in characteristic `p`.
  let _ := hS
  let ρprod : Representation k (S × P) T := T.ρ.comp e.toMonoidHom
  letI : Representation.IsIrreducible T.ρ := FDRep.isIrreducible_of_simple T
  letI : Representation.IsIrreducible ρprod :=
    isIrreducible_comp_of_mulEquiv_local e T.ρ
  let N : Subgroup (S × P) := (⊥ : Subgroup S).prod (⊤ : Subgroup P)
  let eN : P ≃* N :=
    { toFun := fun p' ↦ ⟨(1, p'), by
        show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
        exact ⟨by simp, by simp⟩⟩
      invFun := fun n ↦ n.1.2
      left_inv := by
        intro p'
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rcases n with ⟨⟨s, p'⟩, hn⟩
        change (1, p') = (s, p')
        have hs : s = 1 := by
          simpa [N] using hn.1
        simp [hs]
      map_mul' := by
        intro p₁ p₂
        apply Subtype.ext
        simp }
  have hN_p : IsPGroup p N := hP.of_equiv eN
  letI : Representation.IsTrivial (ρprod.comp N.subtype) :=
    isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
      (p := p) (k := k) (ρ := ρprod) N hN_p
  have hTriv_inr : Representation.IsTrivial (ρprod.comp (MonoidHom.inr S P)) := by
    refine ⟨fun p' ↦ ?_⟩
    ext x
    let n : N := ⟨(1, p'), by
      show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
      exact ⟨by simp, by simp⟩⟩
    simpa [ρprod, n] using isTrivial_apply (ρprod.comp N.subtype) n x
  let ρS : Representation k S T := ρprod.comp (MonoidHom.inl S P)
  have hρS_irreducible : Representation.IsIrreducible ρS := by
    letI : Representation.IsTrivial (ρprod.comp (MonoidHom.inr S P)) := hTriv_inr
    classical
    letI : Nontrivial (Subrepresentation ρS) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro hbot
      have hbot' : (⊥ : Subrepresentation ρprod) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        simpa [ρS] using congrArg Subrepresentation.toSubmodule hbot
      exact IsSimpleOrder.bot_ne_top hbot'
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro W hW
    let W' : Subrepresentation ρprod :=
      { toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          rcases g with ⟨s, p'⟩
          have hp' : ρprod (1, p') x = x := by
            simpa [ρprod] using isTrivial_apply (ρprod.comp (MonoidHom.inr S P)) p' x
          have hact : ρprod (s, p') x = ρS s x := by
            calc
              ρprod (s, p') x = ρprod ((s, 1) * (1, p')) x := by simp
              _ = ρprod (s, 1) (ρprod (1, p') x) := by
                    rw [map_mul]
                    rfl
              _ = ρprod (s, 1) x := by simp [hp']
              _ = ρS s x := rfl
          exact hact ▸ W.apply_mem_toSubmodule s hx }
    have hW'_ne_bot : W' ≠ ⊥ := by
      intro hW'
      apply hW
      apply Subrepresentation.toSubmodule_injective
      simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'
    have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
    apply Subrepresentation.toSubmodule_injective
    simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'_top
  have hρeq :
      ρprod = ρS.comp (MonoidHom.fst S P) := by
    ext g x
    rcases g with ⟨s, p'⟩
    calc
      ρprod (s, p') x = ρprod ((s, 1) * (1, p')) x := by simp
      _ = ρprod (s, 1) (ρprod (1, p') x) := by
            rw [map_mul]
            rfl
      _ = ρprod (s, 1) x := by
            have hp' : ρprod (1, p') x = x := by
              simpa [ρprod] using isTrivial_apply (ρprod.comp (MonoidHom.inr S P)) p' x
            simp [hp']
      _ = (ρS.comp (MonoidHom.fst S P)) (s, p') x := rfl
  refine ⟨ρS, hρS_irreducible, ?_⟩
  simpa [ρprod, ρS] using hρeq

private theorem elementary_simple_class_mem_characterRingOverField_local
    (lift : PrimeToPRoot p k →* Kˣ) {H : Subgroup G} (hH : IsElementary H)
    (T : FDRep k H) [Simple T] :
    ([T]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  -- Route correction: the local `H = S × P` frontier has now been reduced to three named source
  -- inputs: the `15.7` factorization theorem, the prime-to-`p` left-factor witness, and the
  -- transport of `f ↦ f'` across the product equivalence.
  obtain ⟨S, P, hS, hP, hSPcent, hSPcomp⟩ :=
    elementary_exists_primeToP_pGroup_complement_local (p := p) H hH
  have hcomm : ∀ s : S, ∀ p' : P, Commute (s : H) (p' : H) := by
    intro s p'
    exact (Subgroup.mem_centralizer_iff.mp (hSPcent s.2) p' p'.2).symm
  let e : S × P ≃* H := hSPcomp.prodMulEquiv hcomm
  obtain ⟨ρS, hρSirr, hfactor⟩ :=
    split_product_source_factorization_local
      (p := p) (k := k) (S := S) (P := P) (H := H) hS hP e T
  let U : FDRep k S := FDRep.of ρS
  letI : Representation.IsIrreducible U.ρ := by
    simpa [U] using hρSirr
  letI : Simple U := FDRep.simple_of_isIrreducible U
  have hinflated :
      ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
        R[K](S × P) :=
    split_product_inflated_simple_class_mem_characterRingOverField_local
      (p := p) (k := k) (K := K) lift hS hP U
  have hprecomp :
      (fun h : H ↦
        ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift]
          (e.symm h)) ∈ R[K](H) := by
    -- Precompose the verified `S × P` witness along `e.symm`.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_
      (show
        ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
          R[K](S × P) from hinflated)
    · intro ψ hψ
      rcases hψ with ⟨ρ, hρfd, -, rfl⟩
      change (Rep.res e.symm.toMonoidHom ρ).ρ.character ∈ R[K](H)
      letI : FiniteDimensional K ρ := hρfd
      letI : FiniteDimensional K (Rep.res e.symm.toMonoidHom ρ) := by infer_instance
      exact Representation.rep_character_mem_characterRingOverField
        (Rep.res e.symm.toMonoidHom ρ)
    · intro n
      exact (R[K](H)).algebraMap_mem n
    · intro x y _ _ hx hy
      simpa using (R[K](H)).add_mem hx hy
    · intro x y _ _ hx hy
      simpa using (R[K](H)).mul_mem hx hy
  have htransport :
      (fun h : H ↦
        ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift]
          (e.symm h)) =
        ([T]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
    -- Transport the inflated `S × P` witness back to `H` along the product equivalence.
    ext h
    have hfactor_comp :
        (U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom = T.ρ := by
      ext h' x
      calc
        ((U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom) h' x
            = (U.ρ.comp (MonoidHom.fst S P)) (e.symm h') x := rfl
        _ = (T.ρ.comp e.toMonoidHom) (e.symm h') x := by
              simpa [U] using
                congrArg (fun f : Representation k (S × P) T => f (e.symm h') x) hfactor.symm
        _ = T.ρ h' x := by simp
    have hpoint :
        ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift]
            (e.symm h) =
          ([FDRep.of ((U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom)]₀)′[p,
            PrimeToPRoot.toFieldLift lift] h := by
      simpa using
        (congrFun
          (transformed_fdRep_class_precomp_mulEquiv_local
            (p := p) (k := k) (K := K) (lift := lift)
            (A := H) (B := S × P) e.symm
            (FDRep.of (U.ρ.comp (MonoidHom.fst S P)))) h).symm
    have hleft :
        ([FDRep.of ((U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom)]₀)′[p,
          PrimeToPRoot.toFieldLift lift] h =
        ([T]₀)′[p, PrimeToPRoot.toFieldLift lift] h := by
      simpa using
        congrArg
          (fun ρ : Representation k H T.V =>
            modularCharacter (PrimeToPRoot.toFieldLift lift) ρ
              ⟨pRegularComponent p h, isPRegular_pRegularComponent h⟩)
          hfactor_comp
    exact hpoint.trans hleft
  rw [← htransport]
  exact hprecomp

/-- Helper for Theorem 18-18.4-1: once the simple source-faithful lift on `H = S × P` is
available, extend it additively from simple modules to arbitrary virtual modular classes on the
same elementary subgroup. -/
private theorem elementary_virtual_modular_character_mem_characterRingOverField_local
    (lift : PrimeToPRoot p k →* Kˣ) {H : Subgroup G} (hH : IsElementary H)
    (x : R₀[k](H)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  classical
  letI : AddCommMonoid (R₀[k](H)) :=
    (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid
  letI : AddCommGroup (R₀[k](H)) :=
    QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)
  letI : Module ℤ (R₀[k](H)) := AddCommGroup.toIntModule (R₀[k](H))
  rcases
      exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
        (k := k) (G := H) with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  let b₀ := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let φ : R₀[k](H) →+ H → K :=
    pRegularComponentVirtualModularCharacter (G := H) p (PrimeToPRoot.toFieldLift lift)
  have hbasis_mem : ∀ i, φ (b₀ i) ∈ R[K](H) := by
    intro i
    -- Each basis vector is the class of a simple `k[H]`-module, so the remaining source-faithful
    -- simple-case theorem applies directly.
    letI : Simple (π i) := hπ_complete.isSimple i
    simpa [φ, b₀, simple_finiteRep_classes_basis_of_complete_family_apply] using
      elementary_simple_class_mem_characterRingOverField_local
        (p := p) (k := k) (K := K) (G := G) lift hH (π i)
  let χw : R[K](H) := ∑ i, (b₀.repr x i) • ⟨φ (b₀ i), hbasis_mem i⟩
  let χ : H → K := χw
  have hχ :
      x′[p, PrimeToPRoot.toFieldLift lift] = (χ : H → K) := by
    -- Once the simple case is available, the rest is the flat additive basis expansion inside
    -- `R₀[k](H)`.
    calc
      x′[p, PrimeToPRoot.toFieldLift lift] = φ x := rfl
      _ = φ (∑ i, (b₀.repr x i) • b₀ i) := by
            exact congrArg φ (b₀.sum_repr x).symm
      _ = ∑ i, (b₀.repr x i) • φ (b₀ i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [map_zsmul]
      _ = χ := by
            ext h
            simp [χ, χw]
  rw [hχ]
  exact χw.2

/-- Helper for Theorem 18-18.4-1: once the ambient elementary theorem on `H` is available, the
restricted class of an ambient simple module is just its special case. -/
private theorem simple_class_restricted_to_elementary_mem_characterRingOverField_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ∀ H : Subgroup G, IsElementary H →
      ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  intro H hH
  -- The restricted simple frontier is now only the ambient elementary theorem specialized to the
  -- class of the restricted module.
  exact elementary_virtual_modular_character_mem_characterRingOverField_local
    (p := p) (k := k) (K := K) (G := G) lift hH [FDRep.of (S.ρ.comp H.subtype)]₀

/-- Helper for Theorem 18-18.4-1: every ordinary elementary subgroup is automatically
`Γ`-elementary for any ambient arithmetic subgroup, because the source decomposition already uses
the identity power action. -/
private theorem Subgroup.IsElementary.isGammaElementary_local
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {H : Subgroup G}
    (hH : IsElementary H) :
    Subgroup.IsGammaElementary ΓK H := by
  rcases hH with ⟨q, C, P, hCP⟩
  refine ⟨q, C, P, ?_⟩
  refine ⟨hCP.prime, hCP.finite_pGroup_factor, hCP.cyclic, hCP.coprime_card,
    hCP.isPGroup, hCP.isComplement, ?_⟩
  intro y
  refine ⟨⟨1, by simp⟩, ?_⟩
  intro x
  have hcomm :
      (((y : P) : H) : G) * (((x : C) : H) : G) = (((x : C) : H) : G) * (((y : P) : H) : G) := by
    exact congrArg Subtype.val (hCP.commute x y).eq.symm
  calc
    (((y : P) : H) : G) * (((x : C) : H) : G) * (((y : P) : H) : G)⁻¹
        = (((x : C) : H) : G) := by
            rw [hcomm]
            simp [mul_assoc]
    _ = (((x : C) : H) : G) ^ (⟨1, by simp⟩ : ΓK) := by
          rw [pow_subgroup_eq_pow_nat]
          have hpow :
              (((x : C) : H) : G) ^ (1 % Monoid.exponent G) = (((x : C) : H) : G) ^ 1 := by
            simpa using
              (Eq.symm (@Monoid.pow_eq_mod_exponent G _ 1 (((x : C) : H) : G)))
          simpa [galoisPowerExponentUnit, ZMod.val_one_eq_one_mod] using hpow.symm

/-- Helper for Theorem 18-18.4-1: a `Γ_K`-`p`-elementary decomposition places the subgroup inside
the associated subgroup built from a generator of its cyclic factor. -/
private theorem Subgroup.IsGammaPElementaryDecomposition.exists_le_associatedGammaPElementarySubgroup_local
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    {q : ℕ} [Fact q.Prime]
    {H : Subgroup G} {C P : Subgroup H}
    (h : Subgroup.IsGammaPElementaryDecomposition ΓK q C P) :
    ∃ x : H, ∃ Q : Sylow q N[ΓK]((x : G)),
      IsPRegular q (x : G) ∧ H ≤ associatedGammaPElementarySubgroup ΓK (x : G) Q := by
  obtain ⟨x, hxC⟩ := C.isCyclic_iff_exists_zpowers_eq_top.mp h.cyclic
  have hx_mem_C : x ∈ C := by
    rw [← hxC]
    exact Subgroup.mem_zpowers x
  have hx_regular_H : IsPRegular q x := by
    exact h.coprime_card.coprime_dvd_right <| by
      simpa [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨x, hx_mem_C⟩ : C)
  have hx_regular : IsPRegular q (x : G) := by
    simpa [IsPRegular, Subgroup.orderOf_mk] using hx_regular_H
  let Nx : Subgroup G := N[ΓK]((x : G))
  let P' : Subgroup G := P.map H.subtype
  have hP'_le_gammaNormalizer : P' ≤ Nx := by
    rintro _ ⟨y, hy, rfl⟩
    rcases h.conjugation_eq_pow ⟨y, hy⟩ with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa using ht ⟨x, hx_mem_C⟩
  have hP' : IsPGroup q P' :=
    h.isPGroup.of_surjective (H.subtype.subgroupMap P) (H.subtype.subgroupMap_surjective P)
  have hP'_gammaNormalizer : IsPGroup q (P'.subgroupOf Nx) :=
    hP'.of_equiv (Subgroup.subgroupOfEquivOfLe hP'_le_gammaNormalizer).symm
  obtain ⟨Q, hPQ⟩ := hP'_gammaNormalizer.exists_le_sylow
  have hP'_le_Qmap : P' ≤ Subgroup.map Nx.subtype (Q : Subgroup Nx) := by
    calc
      P' = Subgroup.map Nx.subtype (P'.subgroupOf Nx) := by
        symm
        exact Subgroup.map_subgroupOf_eq_of_le hP'_le_gammaNormalizer
      _ ≤ Subgroup.map Nx.subtype (Q : Subgroup Nx) := Subgroup.map_mono hPQ
  have hH_eq :
      H = Subgroup.zpowers (x : G) ⊔ P' := by
    calc
      H = (⊤ : Subgroup H).map H.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (C ⊔ P).map H.subtype := by
        rw [← h.isComplement.sup_eq_top]
      _ = (Subgroup.zpowers x ⊔ P).map H.subtype := by
        rw [hxC]
      _ = Subgroup.zpowers (H.subtype x) ⊔ P' := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      _ = Subgroup.zpowers (x : G) ⊔ P.map H.subtype := by
        rfl
  refine ⟨x, Q, hx_regular, ?_⟩
  calc
    H = Subgroup.zpowers (x : G) ⊔ P' := hH_eq
    _ ≤ Subgroup.zpowers (x : G) ⊔ Subgroup.map Nx.subtype (Q : Subgroup Nx) :=
      sup_le_sup le_rfl hP'_le_Qmap
    _ = associatedGammaPElementarySubgroup ΓK (x : G) Q := by
      simp [associatedGammaPElementarySubgroup, Nx]

/-- Helper for Theorem 18-18.4-1: the value of a unit-valued character is integral over `ℚ`
because it is a root of unity. -/
private theorem lift_value_isIntegral_rat_local
    (lift : PrimeToPRoot p k →* Kˣ) (ζ : PrimeToPRoot p k) :
    IsIntegral ℚ ((lift ζ : Kˣ) : K) := by
  -- A prime-to-`p` root has positive finite order, so its lift satisfies a monic equation over
  -- `ℚ`.
  have hpos : 0 < orderOf (ζ : kˣ) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hcop : Nat.Coprime p (orderOf (ζ : kˣ)) := ζ.2
    have hp1 : p = 1 := by
      simpa [hzero] using hcop
    exact Nat.Prime.ne_one Fact.out hp1
  refine IsIntegral.of_pow (n := orderOf (ζ : kˣ)) hpos ?_
  rw [show ((lift ζ : K) ^ orderOf (ζ : kˣ)) = 1 by
    have hpowζ : ζ ^ orderOf (ζ : kˣ) = 1 := by
      apply Subtype.ext
      simpa using (pow_orderOf_eq_one (ζ : kˣ))
    have hpowUnits : (lift ζ) ^ orderOf (ζ : kˣ) = 1 := by
      rw [← map_pow]
      simpa using hpowζ
    exact congrArg (fun u : Kˣ => (u : K)) hpowUnits]
  exact isIntegral_one

/-- Helper for Theorem 18-18.4-1: every modular-character value produced by the chosen lift is
algebraic over `ℚ`, since it is a finite sum of lifted roots of unity. -/
private theorem modularCharacter_isIntegral_rat_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {H : Type u} [Group H] [Finite H]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k H V) (s : { g : H // IsPRegular p g }) :
    IsIntegral ℚ (modularCharacter (PrimeToPRoot.toFieldLift lift) ρ s) := by
  classical
  -- Unfold LinearRepresentations_Serre_1977's modular-character packet and verify integrality termwise on the root multiset.
  simp only [Representation.modularCharacter]
  refine IsIntegral.multiset_sum ?_
  intro z hz
  rcases Multiset.mem_map.mp hz with ⟨μ, hμ, rfl⟩
  simpa [PrimeToPRoot.toFieldLift] using
    lift_value_isIntegral_rat_local
      (p := p) (k := k) (K := K) lift
      (charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 μ.2)

/-- Helper for Theorem 18-18.4-1: the transformed simple-class values generate a finite-dimensional
`ℚ`-subfield of `K`. This isolates the number-field half of the value-field descent. -/
private theorem transformed_simple_class_value_field_finiteDimensional_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    FiniteDimensional ℚ
      ↥(IntermediateField.adjoin ℚ
        (Set.range (([S]₀)′[p, PrimeToPRoot.toFieldLift lift] : G → K))) := by
  let ψ : G → K := ([S]₀)′[p, PrimeToPRoot.toFieldLift lift]
  have hψfinite : (Set.range ψ).Finite := Set.finite_range ψ
  letI : Fintype (Set.range ψ) := hψfinite.fintype
  -- The adjoin field is finite-dimensional because `ψ` has finite range and each value is
  -- integral over `ℚ`.
  refine IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := Set.range ψ) ?_
  intro x hx
  rcases hx with ⟨g, rfl⟩
  have hψg :
      ψ g =
        modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ
          ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩ := by
    -- Evaluate the transformed class at `g` by moving to the chosen `p`-regular component.
    calc
      ψ g =
          virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [S]₀
            ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩ := by
        simp [ψ, pRegularComponentVirtualModularCharacter_apply]
      _ = modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ
            ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩ := by
        rw [virtualModularCharacter_class]
  exact hψg ▸
    modularCharacter_isIntegral_rat_local
      (p := p) (k := k) (K := K) (lift := lift) S.ρ
      ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩

/-- Helper for Theorem 18-18.4-1: the finite value field generated by the transformed simple
class is a number field. This closes the finite-dimensional half of the value-field descent. -/
private theorem transformed_simple_class_value_field_numberField_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    NumberField
      ↥(IntermediateField.adjoin ℚ
        (Set.range (([S]₀)′[p, PrimeToPRoot.toFieldLift lift] : G → K))) := by
  -- The value field is finite-dimensional over `ℚ`, so the standard number-field instance
  -- applies immediately.
  letI :
      FiniteDimensional ℚ
        ↥(IntermediateField.adjoin ℚ
          (Set.range (([S]₀)′[p, PrimeToPRoot.toFieldLift lift] : G → K))) :=
    transformed_simple_class_value_field_finiteDimensional_local
      (p := p) (k := k) (K := K) (G := G) lift S
  exact NumberField.of_module_finite ℚ _

/-- Helper for Theorem 18-18.4-1: after the local `H = S × P` step is closed, the remaining
global source-faithful task is to shrink the transformed simple class to one value field and then
apply Chapter `12` there. -/
private theorem transformed_simple_class_value_field_data_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ∃ K0 : IntermediateField ℚ K,
      ∃ φ0 : classFunctionSubmodule K0 G,
        (fun g : G => algebraMap K0 K (φ0 g)) =
          ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  let ψ : G → K := ([S]₀)′[p, PrimeToPRoot.toFieldLift lift]
  let K0 : IntermediateField ℚ K := IntermediateField.adjoin ℚ (Set.range ψ)
  have hψ_mem : ∀ g : G, ψ g ∈ K0 := by
    intro g
    exact IntermediateField.subset_adjoin ℚ (Set.range ψ) ⟨g, rfl⟩
  let φ0 : classFunctionSubmodule K0 G :=
    ⟨fun g ↦ ⟨ψ g, hψ_mem g⟩, by
      -- The bundled value-field class function inherits conjugacy invariance from the ambient
      -- transformed simple class.
      refine (mem_classFunctionSubmodule_iff K0 _).2 ?_
      refine ⟨?_⟩
      intro s t hst
      apply Subtype.ext
      exact
        ((_root_.IsClassFunction.eq_of_isConj
          ((mem_classFunctionSubmodule_iff K _).1
            (pRegularComponentVirtualModularCharacter_isClassFunction
              (p := p) (k := k) (K := K) (G := G) lift [S]₀))
          (ConjClasses.mk_eq_mk_iff_isConj.mp hst)))
      ⟩
  refine ⟨K0, φ0, ?_⟩
  -- The ambient transformed simple class is recovered by forgetting the value-field packaging.
  funext g
  rfl

/-- Helper for Theorem 18-18.4-1: scalar extension of an ordinary representation changes its
character only by applying the coefficient-field inclusion pointwise. -/
private theorem scalarExtension_character_eq_coefficient_map_local
    {K0 : IntermediateField ℚ K}
    {H : Type u} [Group H] [Finite H]
    {V : Type u} [AddCommGroup V] [Module K0 V] [FiniteDimensional K0 V]
    (ρ : Representation K0 H V) :
    (Representation.scalarExtension ρ).character =
      fun h : H ↦ algebraMap K0 K (ρ.character h) := by
  -- Trace commutes with base change, so scalar extension only changes coefficients.
  ext h
  exact LinearMap.trace_baseChange (ρ h) K

/-- Helper for Theorem 18-18.4-1: extending coefficients from a value field `K₀ ⊆ K` preserves
membership in the ordinary character ring. -/
private theorem map_mem_characterRingOverField_of_mem_intermediateField_characterRing_local
    (K0 : IntermediateField ℚ K)
    {H : Type u} [Group H] [Finite H]
    {χ : H → K0} (hχ : χ ∈ R[K0](H)) :
    (fun h : H ↦ algebraMap K0 K (χ h)) ∈ R[K](H) := by
  -- Push coefficient extension through the algebra-adjoin presentation of `R[K₀](H)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional K0 ρ := hρfd
    let ρK : Rep K H := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (fun h : H ↦ algebraMap K0 K (ρ.ρ.character h)) = ρK.ρ.character := by
      -- Compare the mapped character with the scalar-extended honest character.
      ext h
      simpa [ρK] using
        (congrFun
          (scalarExtension_character_eq_coefficient_map_local
            (K := K) (ρ := ρ.ρ)) h).symm
    exact hchar.symm ▸ Representation.rep_character_mem_characterRingOverField ρK
  · intro n
    -- Integer-valued constant functions stay in the target character ring.
    change (fun _ : H ↦ algebraMap K0 K (algebraMap ℤ K0 n)) ∈ R[K](H)
    have hconst :
        (fun _ : H ↦ algebraMap K0 K (algebraMap ℤ K0 n)) = algebraMap ℤ (H → K) n := by
      ext h
      simp
    rw [hconst]
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    -- The target character ring is closed under addition.
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    -- The target character ring is closed under multiplication.
    simpa using (R[K](H)).mul_mem hx hy

/-- Helper for Theorem 18-18.4-1: restricting an intermediate-field ordinary virtual character
along a subgroup inclusion preserves character-ring membership. This is the exact transport step
needed after placing a `Γ`-elementary subgroup inside its associated subgroup. -/
private theorem restrict_mem_intermediateField_characterRing_of_le_local
    {K0 : Type u} [Field K0] {H A : Subgroup G} (hHA : H ≤ A)
    {χ : A → K0} (hχ : χ ∈ R[K0](A)) :
    (fun h : H ↦ χ (Subgroup.inclusion hHA h)) ∈ R[K0](H) := by
  -- Apply the canonical subgroup-restriction map on LinearRepresentations_Serre_1977's ordinary character ring.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res (Subgroup.inclusion hHA) ρ).ρ.character ∈ R[K0](H)
    letI : FiniteDimensional K0 ρ := hρfd
    letI : FiniteDimensional K0 (Rep.res (Subgroup.inclusion hHA) ρ) := by infer_instance
    exact Representation.rep_character_mem_characterRingOverField
      (Rep.res (Subgroup.inclusion hHA) ρ)
  · intro n
    exact (R[K0](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K0](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K0](H)).mul_mem hx hy

/-- Helper for Theorem 18-18.4-1: if the packaged value-field class function is already ordinary
on a larger subgroup `A`, then its restriction is ordinary on every smaller subgroup `H ≤ A`. -/
private theorem classFunctionRestriction_mem_intermediateField_characterRing_of_le_local
    {K0 : Type u} [Field K0] {φ0 : classFunctionSubmodule K0 G}
    {H A : Subgroup G} (hHA : H ≤ A)
    (hA : (A.classFunctionRestriction φ0 : A → K0) ∈ R[K0](A)) :
    (H.classFunctionRestriction φ0 : H → K0) ∈ R[K0](H) := by
  -- Rewrite `H`-restriction as restriction of the already-known `A`-restriction along `H ≤ A`.
  simpa [Subgroup.classFunctionRestriction_apply] using
    restrict_mem_intermediateField_characterRing_of_le_local
      (G := G) (hHA := hHA) hA

/-- Helper for Theorem 18-18.4-1: when LinearRepresentations_Serre_1977's associated-subgroup witnesses are already known
for the trivial arithmetic subgroup `Γ = ⊥`, every ordinary elementary subgroup restriction is
obtained just by placing that subgroup inside the corresponding associated subgroup and then
restricting along the inclusion. -/
private theorem classFunction_restrict_mem_characterRingOverField_on_elementary_of_associated_bot_local
    {L : Type u} [Field L] {φ : classFunctionSubmodule L G}
    (hassoc :
      ∀ {q : ℕ} [Fact q.Prime] {x : G} (hx : IsPRegular q x)
        {Q : Sylow q N[(⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)](x)},
        ((associatedGammaPElementarySubgroup
            (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) x Q).classFunctionRestriction φ :
            associatedGammaPElementarySubgroup
              (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) x Q → L) ∈
          R[L](associatedGammaPElementarySubgroup
            (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) x Q)) :
    ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → L) ∈ R[L](H) := by
  intro H hH
  -- Rewrite the ordinary elementary hypothesis as the corresponding `Γ = ⊥` statement.
  have hHΓ :
      Subgroup.IsGammaElementary
        (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H :=
    (Subgroup.isGammaElementary_bot_iff_isElementary (G := G) H).2 hH
  -- Choose a prime and a `Γ = ⊥` elementary decomposition, then place `H` inside its associated
  -- subgroup generated by the cyclic factor.
  rcases
      Subgroup.IsGammaElementary.exists_prime_and_pElementary
        (ΓK := (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)) hHΓ with
    ⟨q, hq, hHq⟩
  letI : Fact q.Prime := ⟨hq⟩
  rcases hHq with ⟨C, P, hdecomp⟩
  obtain ⟨x, Q, hx, hHA⟩ :=
    Subgroup.IsGammaPElementaryDecomposition.exists_le_associatedGammaPElementarySubgroup_local
      (G := G) (ΓK := (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)) (q := q) hdecomp
  -- The associated-subgroup witness now restricts down to the original elementary subgroup.
  exact classFunctionRestriction_mem_intermediateField_characterRing_of_le_local
    (G := G) (φ0 := φ) (hHA := hHA) (hA := hassoc hx)

/-- Helper for Theorem 18-18.4-1: once the packaged value-field class function is known to be
ordinary on every associated subgroup `A = ⟨x⟩ ⋅ Q`, the remaining subgroup descent to an
arbitrary `Γ[K₀](G)`-elementary subgroup `H` is only the canonical inclusion-restriction step
`H ≤ A`. -/
private theorem
    transformed_simple_class_restrict_mem_intermediateField_characterRing_on_gammaElementary_of_associated_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    {K0 : IntermediateField ℚ K} {φ0 : classFunctionSubmodule K0 G}
    (hassoc :
      ∀ {q : ℕ} [Fact q.Prime] {x : G} (hx : IsPRegular q x)
        {Q : Sylow q N[Γ[K0](G)](x)},
        ((associatedGammaPElementarySubgroup (Γ[K0](G)) x Q).classFunctionRestriction φ0 :
            associatedGammaPElementarySubgroup (Γ[K0](G)) x Q → K0) ∈
          R[K0](associatedGammaPElementarySubgroup (Γ[K0](G)) x Q)) :
    ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K0](G)) H →
      (H.classFunctionRestriction φ0 : H → K0) ∈ R[K0](H) := by
  intro H hH
  -- Choose a prime `q` and a `Γ[K₀](G)`-`q`-elementary decomposition of `H`, then place `H`
  -- inside the associated subgroup generated by the cyclic factor.
  rcases
      Subgroup.IsGammaElementary.exists_prime_and_pElementary
        (ΓK := Γ[K0](G)) hH with
    ⟨q, hq, hHq⟩
  letI : Fact q.Prime := ⟨hq⟩
  rcases hHq with ⟨C, P, hdecomp⟩
  obtain ⟨x, Q, hx, hHA⟩ :=
    Subgroup.IsGammaPElementaryDecomposition.exists_le_associatedGammaPElementarySubgroup_local
      (G := G) (ΓK := Γ[K0](G)) (q := q) hdecomp
  -- Apply the assumed associated-subgroup witness and then restrict it along `H ≤ A`.
  exact classFunctionRestriction_mem_intermediateField_characterRing_of_le_local
    (G := G) (φ0 := φ0) (hHA := hHA) (hA := hassoc hx)

/-- Helper for Theorem 18-18.4-1: once the Chapter `12` gamma-elementary detector is available
over `K₀`, the associated-subgroup witnesses already proved above are enough to upgrade the
packaged intermediate-field class function to an element of `R[K₀](G)`. -/
private theorem
    classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups_import_safe_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (K0 : IntermediateField ℚ K) (φ0 : classFunctionSubmodule K0 G) :
    (φ0 : G → K0) ∈ R[K0](G) ↔
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K0](G)) H →
        (H.classFunctionRestriction φ0 : H → K0) ∈ R[K0](H) := by
  -- Reuse Proposition `12-12.6-4` directly, but keep the current file's restriction notation and
  -- intermediate-field specialization explicit so the downstream detector step stays collision-free.
  simpa using
    (Representation.classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups
      (L := K) (G := G) K0 φ0)

/-- Helper for Theorem 18-18.4-1: once the Chapter `12` gamma-elementary detector is available
over `K₀`, the associated-subgroup witnesses already proved above are enough to upgrade the
packaged intermediate-field class function to an element of `R[K₀](G)`. -/
private theorem classFunction_mem_intermediateField_characterRing_of_associated_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    {K0 : IntermediateField ℚ K} {φ0 : classFunctionSubmodule K0 G}
    (hassoc :
      ∀ {q : ℕ} [Fact q.Prime] {x : G} (hx : IsPRegular q x)
        {Q : Sylow q N[Γ[K0](G)](x)},
        ((associatedGammaPElementarySubgroup (Γ[K0](G)) x Q).classFunctionRestriction φ0 :
            associatedGammaPElementarySubgroup (Γ[K0](G)) x Q → K0) ∈
          R[K0](associatedGammaPElementarySubgroup (Γ[K0](G)) x Q)) :
    (φ0 : G → K0) ∈ R[K0](G) := by
  -- First descend the associated-subgroup witnesses to all `Γ[K₀](G)`-elementary subgroups.
  have hrestrict :
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K0](G)) H →
        (H.classFunctionRestriction φ0 : H → K0) ∈ R[K0](H) :=
    transformed_simple_class_restrict_mem_intermediateField_characterRing_on_gammaElementary_of_associated_local
      (G := G) (K := K) (K0 := K0) (φ0 := φ0) hassoc
  -- The restriction frontier is complete, so the local import-safe detector alias closes the
  -- Chapter `12` step without changing the ambient source-faithful route.
  exact
    (classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups_import_safe_local
      (G := G) (K := K) K0 φ0).2 hrestrict

/-- Helper for Theorem 18-18.4-1: once the value-field package of the transformed simple class is
known to lie in `R[K₀](G)`, coefficient extension immediately returns the desired element of
`R[K](G)`. -/
private theorem transformed_simple_class_detection_of_value_field_membership_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S]
    {K0 : IntermediateField ℚ K} {φ0 : classFunctionSubmodule K0 G}
    (hφ0 :
      (fun g : G ↦ algebraMap K0 K (φ0 g)) =
        ([S]₀)′[p, PrimeToPRoot.toFieldLift lift])
    (hmem : (φ0 : G → K0) ∈ R[K0](G)) :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Extend coefficients from `K₀` to `K` and rewrite the packaged class function back to `f'`.
  have hmap :
      (fun g : G ↦ algebraMap K0 K (φ0 g)) ∈ R[K](G) :=
    map_mem_characterRingOverField_of_mem_intermediateField_characterRing_local
      (K := K) K0 hmem
  exact hφ0 ▸ hmap

/-- Helper for Theorem 18-18.4-1: after shrinking the transformed simple class to one finite
value field inside `K`, the remaining global task is to perform the later cyclotomic descent in
an external overfield rather than forcing cyclotomic structure on that intermediate subfield. -/
private theorem transformed_simple_class_fixedField_data_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ∃ K0 : IntermediateField ℚ K,
      ∃ φ0 : classFunctionSubmodule K0 G,
        (fun g : G ↦ algebraMap K0 K (φ0 g)) =
            ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∧
          NumberField K0 := by
  -- Route correction: the previous intermediate-field cyclotomic package was too strong for
  -- arbitrary characteristic-zero `K`; such a `K` need not contain a cyclotomic subfield of
  -- exponent `Monoid.exponent G`. The source-faithful usable prefix is the finite value-field
  -- package inside `K`, and the cyclotomic descent must happen later through an overfield.
  let ψ : G → K := ([S]₀)′[p, PrimeToPRoot.toFieldLift lift]
  let K0 : IntermediateField ℚ K := IntermediateField.adjoin ℚ (Set.range ψ)
  have hψ_mem : ∀ g : G, ψ g ∈ K0 := by
    intro g
    exact IntermediateField.subset_adjoin ℚ (Set.range ψ) ⟨g, rfl⟩
  let φ0 : classFunctionSubmodule K0 G :=
    ⟨fun g ↦ ⟨ψ g, hψ_mem g⟩, by
      -- The packaged value-field class function inherits conjugacy invariance from the ambient
      -- transformed simple class.
      refine (mem_classFunctionSubmodule_iff K0 _).2 ?_
      refine ⟨?_⟩
      intro s t hst
      apply Subtype.ext
      exact
        ((_root_.IsClassFunction.eq_of_isConj
          ((mem_classFunctionSubmodule_iff K _).1
            (pRegularComponentVirtualModularCharacter_isClassFunction
              (p := p) (k := k) (K := K) (G := G) lift [S]₀))
          (ConjClasses.mk_eq_mk_iff_isConj.mp hst)))
      ⟩
  refine ⟨K0, φ0, ?_, ?_⟩
  · -- Forgetting the value-field packaging recovers the original transformed simple class.
    funext g
    rfl
  · -- The packaged coefficient field is exactly the finite adjoin field generated by those
    -- transformed values, so the previously proved number-field bridge applies directly.
    simpa [K0, ψ] using
      transformed_simple_class_value_field_numberField_local
        (p := p) (k := k) (K := K) (G := G) lift S

/-- Helper for Theorem 18-18.4-1: after shrinking the transformed simple class to one value
field, the remaining global task is exactly to show that packaged `K₀`-valued class function
already lies in `R[K₀](G)`. -/
private theorem transformed_simple_class_mem_intermediateField_characterRing_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S]
    {K0 : IntermediateField ℚ K} {φ0 : classFunctionSubmodule K0 G}
    (hφ0 :
      (fun g : G ↦ algebraMap K0 K (φ0 g)) =
        ([S]₀)′[p, PrimeToPRoot.toFieldLift lift]) :
    (φ0 : G → K0) ∈ R[K0](G) := by
  -- Route correction: do not keep the blocker as a coarse arbitrary-`φ₀` statement.
  -- The real remaining interface is the associated-subgroup `K₀`-witness consumed by the local
  -- Chapter `12` detector, but that witness must now be obtained by descending from an external
  -- cyclotomic overfield: an arbitrary intermediate field `K₀ ⊆ K` need not itself be cyclotomic
  -- for `Monoid.exponent G`.
  let _ := hφ0
  -- TODO: build one external cyclotomic model for the scalar extension of `φ₀`, prove the
  -- associated-subgroup restrictions descend from that model back to `K₀`, and then feed those
  -- descended witnesses into `classFunction_mem_intermediateField_characterRing_of_associated_local`.
  sorry

/-- Helper for Theorem 18-18.4-1: after the local `H = S × P` step is closed, the remaining
global source-faithful task is to shrink the transformed simple class to one value field and then
apply Chapter `12` there. -/
private theorem transformed_simple_class_detection_via_value_field_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Route correction: the old arbitrary-`φ` detector was the wrong abstraction level.
  -- The only ambient object that matters here is the transformed simple class itself, after
  -- shrinking its values to a finite intermediate field and checking the Chapter `12`
  -- gamma-elementary restrictions there.
  obtain ⟨K0, φ0, hφ0, hK0_numberField⟩ :=
    transformed_simple_class_fixedField_data_local
      (p := p) (k := k) (K := K) (G := G) lift S
  letI : NumberField K0 := hK0_numberField
  have hφ0_mem :
      (φ0 : G → K0) ∈ R[K0](G) :=
    transformed_simple_class_mem_intermediateField_characterRing_local
      (p := p) (k := k) (K := K) (G := G) (K0 := K0) (φ0 := φ0) lift S hφ0
  exact transformed_simple_class_detection_of_value_field_membership_local
    (p := p) (k := k) (K := K) (G := G) lift S
    hφ0 hφ0_mem

/-- Helper for Theorem 18-18.4-1: after the fixed-prime elementary split is exposed, the only
remaining source-faithful gaps are the textbook local lift on elementary subgroups and the final
over-field elementary detection bridge. -/
private theorem associated_subgroup_explicit_character_bridge_for_simple_class_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- The generic detector shell has been removed from the critical path. Once the prime-to-`p`
  -- local witness is available, the global closure should be the value-field descent theorem
  -- specialized to this transformed simple class.
  exact transformed_simple_class_detection_via_value_field_local
    (p := p) (k := k) (K := K) (G := G) lift S

/-- Helper for Theorem 18-18.4-1: the remaining work is to realize the `p`-regular-component
transform of a simple modular class as an ordinary virtual character. -/
private theorem pRegularComponentVirtualModularCharacter_simple_class_mem_characterRingOverField
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Route correction: the simple case is now reduced to the explicit associated-subgroup bridge
  -- just above, so the remaining blocker is isolated to one named source-faithful step.
  exact associated_subgroup_explicit_character_bridge_for_simple_class_local
    (p := p) (k := k) (K := K) (G := G) lift S

-- Proof sketch: restrict first to the case of a simple modular class, where LinearRepresentations_Serre_1977's elementary
-- subgroup argument realizes the `p`-regular-component class function as an ordinary character;
-- then extend by additivity to arbitrary classes in `R_k(G)`.
/-- Theorem 18-18.4-1 (1): for a class `x ∈ R_k(G)`, the class function `f'` obtained by
evaluating its virtual modular character on the chosen `p`-regular component of each element of
`G` is an ordinary virtual character of `G`, realized here as an element of `R[K](G)` for the
characteristic-zero coefficient field `K`. -/
theorem pRegularComponentVirtualModularCharacter_mem_characterRingOverField
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  classical
  rcases
      exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
        (k := k) (G := G) with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  let b₀ := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let φ : R₀[k](G) →+ G → K :=
    pRegularComponentVirtualModularCharacter (G := G) p (PrimeToPRoot.toFieldLift lift)
  have hbasis_mem : ∀ i, φ (b₀ i) ∈ R[K](G) := by
    intro i
    -- Each simple basis vector is the class of a simple representation, so the remaining
    -- simple-case theorem places its transformed class in the ordinary character ring.
    letI : Simple (π i) := hπ_complete.isSimple i
    simpa [φ, b₀, simple_finiteRep_classes_basis_of_complete_family_apply] using
      pRegularComponentVirtualModularCharacter_simple_class_mem_characterRingOverField
        (p := p) (k := k) (K := K) (G := G) lift (π i)
  let χw : R[K](G) := ∑ i, (b₀.repr x i) • ⟨φ (b₀ i), hbasis_mem i⟩
  let χ : G → K := χw
  have hχ :
      x′[p, PrimeToPRoot.toFieldLift lift] = (χ : G → K) := by
    -- Route correction: once the simple case is available, the general case is only the additive
    -- simple-basis expansion already used in the commutative `p'` argument above.
    calc
      x′[p, PrimeToPRoot.toFieldLift lift] = φ x := rfl
      _ = φ (∑ i, (b₀.repr x i) • b₀ i) := by
            exact congrArg φ (b₀.sum_repr x).symm
      _ = ∑ i, (b₀.repr x i) • φ (b₀ i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [map_zsmul]
      _ = χ := by
            ext g
            simp [χ, χw]
  rw [hχ]
  exact χw.2

variable (p)

/-- Theorem 18-18.4-1, source-facing additive owner: LinearRepresentations_Serre_1977's `x ↦ x'` construction viewed
directly as a homomorphism from `R_k(G)` to the ordinary character ring `R_K(G)`. -/
def pRegularComponentVirtualCharacter
    (lift : PrimeToPRoot p k →* Kˣ) :
    R₀[k](G) →+ R[K](G) :=
  (pRegularComponentVirtualModularCharacter p (PrimeToPRoot.toFieldLift lift)).codRestrict
    (R[K](G))
    (fun x ↦ pRegularComponentVirtualModularCharacter_mem_characterRingOverField lift x)

@[simp] theorem pRegularComponentVirtualCharacter_apply
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G)) (g : G) :
    pRegularComponentVirtualCharacter p lift x g =
      x′[p, PrimeToPRoot.toFieldLift lift] g :=
  rfl

/-- Helper for Theorem 18-18.4-1: on a `p`-regular element, LinearRepresentations_Serre_1977's `f ↦ f'` construction simply
recovers the original virtual modular character. -/
@[simp] theorem pRegularComponentVirtualCharacter_apply_of_isPRegular
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G))
    (s : { g : G // IsPRegular p g }) :
    pRegularComponentVirtualCharacter p lift x s.1 =
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) x s := by
  -- On the `p`-regular locus, the canonical `p`-regular component is the point itself.
  simp [pRegularComponentVirtualCharacter_apply,
    pRegularComponent_eq_self_of_isPRegular s.2]

end CharacterRingLift

section

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 18-18.4-1: reducing an ordinary virtual character and then evaluating its
Brauer character on the `p`-regular locus agrees with restricting the original ordinary character
to the `p`-regular subtype. -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_local
    (lift : PrimeToPRoot p k →* Kˣ) (y : R₀[K](G)) :
    virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  -- Route correction: this is the exact Chapter `18.3` comparison used in part `(2)`.
  -- Descend the stable-lattice generator identity through the Grothendieck quotient exactly as in
  -- Theorem `18-18.3-1`, rather than rebuilding the `p`-regular restriction comparison from
  -- scratch inside this file.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class maps to the zero class function on both sides.
    ext s
    simp
  · intro E
    obtain ⟨L⟩ := Representation.exists_stableLattice A E.ρ
    -- On a generator `[E]₀`, Chapter `18.3` already identifies the modular character of the
    -- reduction with the restriction of the ordinary character of `E`.
    ext s
    change
      (virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) [E]₀)) s =
        ((finiteRepGrothendieckCharacter K G [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) E L,
      virtualModularCharacter_class, finiteRepGrothendieckCharacter_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := A) (K := K) (G := G) lift E.ρ L s)
  · intro a ha
    -- Additivity carries the comparison through negation.
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    -- Additivity carries the comparison through sums.
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

/-- Helper for Theorem 18-18.4-1: once an additive section of
`finiteRepGrothendieckCharacter` is fixed, composing it with LinearRepresentations_Serre_1977's `x ↦ x'` map immediately
recovers `pRegularComponentVirtualCharacter` after applying
`finiteRepGrothendieckCharacter`. -/
theorem finiteRepGrothendieckCharacter_comp_section_eq_pRegularComponentVirtualCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (t : R[K](G) →+ R₀[K](G))
    (ht : Function.LeftInverse (finiteRepGrothendieckCharacter K G) t) :
    (finiteRepGrothendieckCharacter K G).comp (t.comp (pRegularComponentVirtualCharacter p lift)) =
      pRegularComponentVirtualCharacter p lift := by
  ext x g
  -- Evaluate the left-inverse identity pointwise on the ordinary character side.
  simpa [AddMonoidHom.comp_apply] using
    congrArg (fun χ : R[K](G) ↦ χ g)
      (ht (((pRegularComponentVirtualCharacter p lift).comp
        (QuotientAddGroup.mk' (finiteRepGrothendieckRelations k G))) (FreeAbelianGroup.of x)))

/-- Helper for Theorem 18-18.4-1: with an injective lift of the prime-to-`p` roots, any additive
section of `finiteRepGrothendieckCharacter` becomes a left inverse to `decompositionHom` after
composition with LinearRepresentations_Serre_1977's `x ↦ x'` construction. -/
theorem decompositionHom_leftInverse_of_pRegularComponent_section
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (t : R[K](G) →+ R₀[K](G))
    (ht : Function.LeftInverse (finiteRepGrothendieckCharacter K G) t) :
    Function.LeftInverse (decompositionHom A K G)
      (t.comp (pRegularComponentVirtualCharacter p lift)) := by
  intro x
  -- Route correction: after strengthening `lift` to be injective, the final comparison is purely
  -- on the `p`-regular locus, so Chapter `18` injectivity closes the equality in `R₀[k](G)`.
  apply (virtualModularCharacterOnPRegularConjClass_injective lift hlift)
  ext c
  rcases c with ⟨c, hc⟩
  obtain ⟨s, rfl⟩ := ConjClasses.mk_surjective c
  have hs : IsPRegular p s := hc s <| by
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hsubtype :
      PRegularConjClass.ofSubtype p ⟨s, hs⟩ =
        ⟨ConjClasses.mk s, hc⟩ := by
    apply Subtype.ext
    rfl
  -- Evaluate both descended Brauer characters on the chosen `p`-regular representative.
  rw [← hsubtype]
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype,
    virtualModularCharacterOnPRegularConjClass_ofSubtype,
    virtualModularCharacter_decomposition_eq_character_restriction_local]
  have hchar :
      (finiteRepGrothendieckCharacter K G) (t (pRegularComponentVirtualCharacter p lift x)) =
        pRegularComponentVirtualCharacter p lift x :=
    ht (pRegularComponentVirtualCharacter p lift x)
  simpa [pRegularComponent_eq_self_of_isPRegular hs] using
    congrArg (fun χ : R[K](G) ↦ χ s) hchar

/-- Helper for Theorem 18-18.4-1: on the simple-class basis of `R₀[K](G)`,
`finiteRepGrothendieckCharacter` is the matching irreducible-character basis map. -/
theorem finiteRepGrothendieckCharacter_basis_image_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∀ i,
      finiteRepGrothendieckCharacter K G
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i) =
        irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete i := by
  intro i
  -- Rewrite both basis vectors to the same irreducible representation before evaluating the
  -- Grothendieck-group character map.
  rw [show
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i = [π i]₀ by
        simp [simple_finiteRep_classes_basis_of_complete_family_apply]]
  rw [show
      irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete i =
        FDRep.irreducibleCharacter K (π i) by
        simp [irreducible_characters_basis_of_complete_family_apply]]
  ext g
  simp

/-- Helper for Theorem 18-18.4-1: choose one representative of each isomorphism class of simple
finite-dimensional `K[G]`-representations in the characteristic-zero section argument. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_characteristic_zero_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep K G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep K G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot admit an isomorphism.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 18-18.4-1: in characteristic zero, the Grothendieck-group character map
admits an additive section constructed by matching the ordinary-character basis with the
simple-class basis. -/
theorem finiteRepGrothendieckCharacter_has_section_local :
    ∃ t : R[K](G) →+ R₀[K](G),
      Function.LeftInverse (finiteRepGrothendieckCharacter K G) t := by
  classical
  rcases
      exists_complete_pairwise_nonisomorphic_simple_family_characteristic_zero_local
      (K := K) (G := G) with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  let b₀ := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let t : R[K](G) →+ R₀[K](G) :=
    { toFun := fun χ ↦ ∑ i, (bR.repr χ i) • b₀ i
      map_zero' := by
        -- Zero has vanishing coordinates in the ordinary-character basis.
        simp [bR]
      map_add' := by
        intro χ ψ
        -- The section is defined coefficientwise in the ordinary-character basis.
        simp [bR, Finset.sum_add_distrib, add_zsmul, map_add] }
  refine ⟨t, ?_⟩
  intro χ
  -- Expand `χ` in the ordinary-character basis and send the matching simple-class expansion
  -- through `finiteRepGrothendieckCharacter`.
  calc
    finiteRepGrothendieckCharacter K G (t χ)
        = finiteRepGrothendieckCharacter K G (∑ i, (bR.repr χ i) • b₀ i) := rfl
    _ = ∑ i, (bR.repr χ i) • finiteRepGrothendieckCharacter K G (b₀ i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [map_zsmul]
    _ = ∑ i, (bR.repr χ i) • bR i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          -- Each simple-class basis vector is sent to the matching irreducible-character basis
          -- vector, and scaling commutes with that basis identification.
          exact congrArg (fun z : R[K](G) ↦ (bR.repr χ i) • z) <|
            finiteRepGrothendieckCharacter_basis_image_local
              (K := K) (G := G) π hπ_pairwise hπ_complete i
    _ = χ := bR.sum_repr χ

-- Proof sketch: clause (1) shows that the assignment `x ↦ x'` lands in characteristic-zero
-- virtual characters in `R[K](G)`; choose Grothendieck-group lifts of those character-ring
-- elements and arrange them additively so that `finiteRepGrothendieckCharacter` recovers `x ↦ x'`
-- and `decompositionHom A K G` is a left inverse.
/-- Theorem 18-18.4-1 (2): the assignment `x ↦ x'`, obtained by evaluating the virtual modular
character of `x ∈ R_k(G)` on the chosen `p`-regular component of each element of `G`, is induced,
via the canonical bridge `finiteRepGrothendieckCharacter : R₀[K](G) → R[K](G)`, by an additive
section of the decomposition homomorphism `d : R₀[K](G) → R₀[k](G)` for the
characteristic-zero coefficient field `K`. In the source-faithful Brauer-lift setting, the lift
on `p'`-roots must be genuine; in this Lean surface we record that by requiring the chosen
`lift` to be injective. -/
theorem exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    :
    ∃ s : R₀[k](G) →+ R₀[K](G),
      Function.LeftInverse (decompositionHom A K G) s ∧
      (finiteRepGrothendieckCharacter K G).comp s = pRegularComponentVirtualCharacter p lift :=
      by
        -- Route correction: first construct the characteristic-zero section of
        -- `finiteRepGrothendieckCharacter`, then compose it with LinearRepresentations_Serre_1977's `x ↦ x'` map.
        rcases finiteRepGrothendieckCharacter_has_section_local (K := K) (G := G) with ⟨t, ht⟩
        refine ⟨t.comp (pRegularComponentVirtualCharacter p lift), ?_, ?_⟩
        · -- On the `p`-regular locus, Corollary `18-18.2-4` turns the ordinary-character section
          -- identity into the required left inverse for `decompositionHom`.
          exact decompositionHom_leftInverse_of_pRegularComponent_section
            (p := p) (A := A) (K := K) (G := G) lift hlift t ht
        · -- The chosen section was built precisely so that applying
          -- `finiteRepGrothendieckCharacter` recovers LinearRepresentations_Serre_1977's `x ↦ x'` character.
          exact finiteRepGrothendieckCharacter_comp_section_eq_pRegularComponentVirtualCharacter
            (p := p) (K := K) (G := G) lift t ht

end

end Representation
