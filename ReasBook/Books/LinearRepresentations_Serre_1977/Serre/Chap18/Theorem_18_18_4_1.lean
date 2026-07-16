import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap08.Proposition_8_8_2_1.InductionBridge
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_6_4
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_3
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.GrothendieckCharacter
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Corollary_18_18_2_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.SourceFaithfulBasis
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_4_1.CharacterTransformCore
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_4_1.ElementaryPrimeSplit

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation IsMulCommutative

universe u

namespace Representation

section CharacterRingLift

variable {p : ℕ} [Fact p.Prime]
variable {O : Type u} [CommRing O] [IsLocalRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [HenselianLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable [IsAlgClosed (IsLocalRing.ResidueField O)] [CharP (IsLocalRing.ResidueField O) p]
variable {K : Type u} [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField O

local instance : AddCommMonoid (R₀[k](G)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid

local instance : AddCommGroup (R₀[k](G)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)

local instance : Module ℤ (R₀[k](G)) := AddCommGroup.toIntModule (R₀[k](G))

/-- Helper for Theorem 18-18.4-1: the virtual modular character only depends on the chosen lift
through its values on the finite `pRegularExponent p G`-torsion subgroup used by Serre. -/
private theorem virtualModularCharacter_congr_of_eqOn_pRegularExponent_torsion_local
    (lift₁ lift₂ : PrimeToPRoot p k → K)
    (h :
      ∀ ζ : PrimeToPRoot p k, ζ ^ pRegularExponent p G = 1 →
        lift₁ ζ = lift₂ ζ)
    (x : R₀[k](G)) :
    virtualModularCharacter lift₁ x = virtualModularCharacter lift₂ x := by
  -- Reduce the congruence from virtual classes to honest finite-dimensional representations.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp [virtualModularCharacter]
  · intro E
    -- On generators this is exactly the finite-torsion congruence for modular characters.
    ext s
    simpa [virtualModularCharacter, finiteRepGrothendieckClass] using
      modularCharacter_congr_of_eqOn_torsion
        (p := p) (G := G) h E.ρ s
  · intro a ha
    -- Additivity transports the generator-level congruence through negation.
    ext s
    simpa [map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    -- Additivity transports the generator-level congruence through sums.
    ext s
    simpa [map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

/-- Helper for Theorem 18-18.4-1: Serre's `f ↦ f'` transform only depends on lift values on the
`pRegularExponent p G`-torsion roots that actually occur as eigenvalues on `p`-regular elements. -/
private theorem pRegularComponentVirtualModularCharacter_congr_of_eqOn_pRegularExponent_torsion_local
    (lift₁ lift₂ : PrimeToPRoot p k → K)
    (h :
      ∀ ζ : PrimeToPRoot p k, ζ ^ pRegularExponent p G = 1 →
        lift₁ ζ = lift₂ ζ)
    (x : R₀[k](G)) :
    x′[p, lift₁] = x′[p, lift₂] := by
  -- Evaluate both transforms at the canonical `p`-regular component and use the virtual-character
  -- congruence just proved.
  ext g
  rw [pRegularComponentVirtualModularCharacter_apply,
    pRegularComponentVirtualModularCharacter_apply]
  exact
    congrFun
      (virtualModularCharacter_congr_of_eqOn_pRegularExponent_torsion_local
        (p := p) (O := O) (K := K) (G := G) lift₁ lift₂ h x)
      ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩

/-- Helper for Theorem 18-18.4-1: the `p`-regular-component transform is a class function for any
field-valued finite torsion lift, not only for a globally multiplicative unit-valued lift. -/
private theorem pRegularComponentVirtualModularCharacter_isClassFunction_of_fieldLift_local
    (lift : PrimeToPRoot p k → K) (x : R₀[k](G)) :
    x′[p, lift] ∈ classFunctionSubmodule K G := by
  -- Conjugating the input conjugates its `p`-regular component, and virtual modular characters are
  -- already constant on conjugacy classes of `p`-regular elements.
  refine (mem_classFunctionSubmodule_iff K _).2 ?_
  refine ⟨?_⟩
  intro s t hst
  rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
  have hconj : t = (a : G) * s * (a : G)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).2
    simpa [mul_assoc] using ha.eq.symm
  rw [hconj]
  simpa [pRegularComponentVirtualModularCharacter_apply, pRegularComponent_conj] using
    virtualModularCharacter_conj
      (lift := lift) (x := x)
      (s := pRegularComponent p s) (t := a)
      (isPRegular_pRegularComponent s) |>.symm

/-- Helper for Theorem 18-18.4-1: ordinary-character membership for `f'` is unchanged when the
lift is replaced by another lift with the same values on Serre's finite torsion subgroup. -/
private theorem pRegularComponentVirtualModularCharacter_mem_characterRingOverField_of_eqOn_torsion_local
    (lift₁ lift₂ : PrimeToPRoot p k → K)
    (h :
      ∀ ζ : PrimeToPRoot p k, ζ ^ pRegularExponent p G = 1 →
        lift₁ ζ = lift₂ ζ)
    (x : R₀[k](G))
    (hmem : x′[p, lift₂] ∈ R[K](G)) :
    x′[p, lift₁] ∈ R[K](G) := by
  -- Rewrite the transformed class function through the finite-torsion congruence.
  rwa [
    pRegularComponentVirtualModularCharacter_congr_of_eqOn_pRegularExponent_torsion_local
      (p := p) (O := O) (K := K) (G := G) lift₁ lift₂ h x]

/-- Helper for Theorem 18-18.4-1: once each restricted simple class already lifts on every
elementary subgroup, the ambient transformed simple class satisfies Serre's elementary-subgroup
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
            (p := p) (K := K) (G := G) lift [S]₀⟩ : H → K) ∈ R[K](H) := by
  intro H hH
  -- Rewrite the ambient restriction as the same transform built from the restricted module.
  simpa [pRegularComponentVirtualModularCharacter_restrict_simple_class
    (p := p) (K := K) (G := G) (lift := lift) H S] using hlocal H hH

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
              (p := p) (K := K) (G := G) lift [S]₀⟩ : H → K) ∈ R[K](H)) :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Apply the global detection bridge to the bundled transformed simple class.
  exact hdetect
    ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
      pRegularComponentVirtualModularCharacter_isClassFunction
        (p := p) (K := K) (G := G) lift [S]₀⟩
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

/-- Helper for Theorem 18-18.4-1: on a group whose order is prime to `p`, Serre's transformed
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
    (p := p) (K := K) (G := S) (lift := lift) (x := [U]₀) ⟨s, hs⟩]
  rw [virtualModularCharacter_class]
  apply congrArg (fun f : PrimeToPRoot p k → K => modularCharacter f U.ρ ⟨s, hs⟩)
  funext x
  rfl

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

/-- Helper for Theorem 18-18.4-1: an injective Brauer lift contains a primitive `n`-th root in
the characteristic-zero field whenever `n` is prime to `p`. -/
private theorem exists_isPrimitiveRoot_of_primeToPRoot_lift_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    {n : ℕ} (hn : Nat.Coprime p n) :
    ∃ ζ : K, IsPrimitiveRoot ζ n := by
  have hnot_p_dvd_n : ¬ p ∣ n :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hn
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    exact hnot_p_dvd_n (by simp [hn0])
  letI : NeZero n := ⟨hn_ne_zero⟩
  letI : NeZero (n : k) := NeZero.of_not_dvd k hnot_p_dvd_n
  letI : IsSepClosed k := inferInstance
  letI : HasEnoughRootsOfUnity k n := IsSepClosed.hasEnoughRootsOfUnity k n
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := k) (n := n)
  let ζu : rootsOfUnity n k := hζ.toRootsOfUnity
  let η : PrimeToPRoot p k := PrimeToPRoot.ofRootsOfUnity hn ζu
  have hηprim_units : IsPrimitiveRoot (η : kˣ) n := by
    have hζu_prim : IsPrimitiveRoot (ζu : kˣ) n :=
      IsPrimitiveRoot.coe_units_iff.1 (by simpa [ζu] using hζ)
    simpa [η, PrimeToPRoot.ofRootsOfUnity, ζu] using hζu_prim
  have horder_eta : orderOf η = n := by
    simpa using (IsPrimitiveRoot.iff_orderOf.mp hηprim_units)
  have horder_lift : orderOf (lift η) = n := by
    simpa [horder_eta] using orderOf_injective lift hlift η
  have hlift_prim_units : IsPrimitiveRoot (lift η) n := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact horder_lift
  exact ⟨((lift η : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.2 hlift_prim_units⟩

/-- Helper for Theorem 18-18.4-1: an injective Brauer lift makes `K` contain enough `n`-th roots
of unity for every `n` prime to `p`. -/
private theorem hasEnoughRootsOfUnity_of_primeToPRoot_lift_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    {n : ℕ} (hn : Nat.Coprime p n) :
    HasEnoughRootsOfUnity K n := by
  have hnot_p_dvd_n : ¬ p ∣ n :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hn
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    exact hnot_p_dvd_n (by simp [hn0])
  letI : NeZero n := ⟨hn_ne_zero⟩
  exact {
    prim := exists_isPrimitiveRoot_of_primeToPRoot_lift_local
      (p := p) (O := O) (K := K) lift hlift hn
    cyc := rootsOfUnity.isCyclic _ _ }

/-- Helper for Theorem 18-18.4-1: on a finite prime-to-`p` group, an injective Brauer lift
supplies enough roots of unity in `K` for the group exponent. -/
private theorem hasEnoughRootsOfUnity_exponent_of_primeToP_card_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    {S : Type u} [Group S] [Finite S]
  (hS : Nat.Coprime p (Nat.card S)) :
    HasEnoughRootsOfUnity K (Monoid.exponent S) := by
  have hExp : Nat.Coprime p (Monoid.exponent S) :=
    hS.coprime_dvd_right (Group.exponent_dvd_nat_card (G := S))
  exact hasEnoughRootsOfUnity_of_primeToPRoot_lift_local
    (p := p) (O := O) (K := K) lift hlift hExp

/-- Helper for Theorem 18-18.4-1: reducing an ordinary virtual character and then evaluating its
Brauer character on the `p`-regular locus agrees with restricting the original ordinary character
to the `p`-regular subtype. -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_primeToP_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (y : R₀[K](G)) :
    virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom O K G) y) =
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G) y : G → K) ∘ Subtype.val := by
  -- This is the source stable-lattice comparison, descended through the Grothendieck quotient.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · ext s
    simp
  · intro E
    obtain ⟨L⟩ := Representation.exists_stableLattice O E.ρ
    ext s
    change
      (virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom O K G) [E]₀)) s =
        ((ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (G := G) [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := O) (K := K) (G := G) E L,
      virtualModularCharacter_class,
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := O) (K := K) (G := G) lift hred E.ρ L s (hω s.1 s.2))
  · intro a ha
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, the source `15.7` step should
directly produce the `R[K](S)` witness consumed by the later `S × P` shell. -/
private theorem primeToP_simple_class_character_witness_via_character_field_transport_local
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Lift the simple `k[S]`-module through the Chapter 15 projective owner, compare characters
  -- through the decomposition map, and use that every element of `S` is `p`-regular.
  have hS_not_dvd : ¬ p ∣ Nat.card S :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hS
  obtain ⟨Q, hQU⟩ :=
    exists_projective_lift_reducing_to_simple_of_order_prime_to_p
      (A := O) (p := p) (G := S) hS_not_dvd U
  let X : FDRep K S := Q.scalarExtension K
  have hdecomp :
      decompositionHom O K S [X]₀ = [U]₀ := by
    simpa [X] using
      decompositionHom_projective_scalarExtension_class_eq_iso_target_local
        (A := O) (K := K) (G := S) Q hQU
  have hωS : ∀ s : S, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    letI : HasEnoughRootsOfUnity K (Monoid.exponent S) :=
      hasEnoughRootsOfUnity_exponent_of_primeToP_card_local
        (p := p) (O := O) (K := K) lift hlift hS
    haveI : HasEnoughRootsOfUnity K (orderOf s) := by
      exact HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  have hchars :
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀ := by
    ext c
    let s := PRegularConjClass.representative (G := S) (p := p) c
    have hs :
        PRegularConjClass.ofSubtype (G := S) p s = c := by
      apply Subtype.ext
      change ConjClasses.mk (PRegularConjClass.representative (G := S) (p := p) c).1 = c.1
      exact PRegularConjClass.mk_representative (G := S) (p := p) c
    have hcomparison :=
      virtualModularCharacter_decomposition_eq_character_restriction_primeToP_local
        (p := p) (O := O) (K := K) (G := S) lift hred hωS [X]₀
    have hcomparisonU :
        virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [U]₀ =
          (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K) (G := S) [X]₀ : S → K) ∘ Subtype.val := by
      simpa [hdecomp] using hcomparison
    rw [← hs]
    rw [FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype,
      virtualModularCharacterOnPRegularConjClass_ofSubtype]
    simpa [ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class]
      using (congrFun hcomparisonU s).symm
  let χS : R[K](S) :=
    ⟨X.character, Representation.rep_character_mem_characterRingOverField (Rep.of X.ρ)⟩
  refine ⟨χS, ?_⟩
  ext s
  have hs : IsPRegular p s :=
    isPRegular_of_coprime_card_local (p := p) hS s
  have hχs := congrFun hchars (PRegularConjClass.ofSubtype p ⟨s, hs⟩)
  calc
    χS s = X.character s := rfl
    _ = FDRep.ordinaryCharacterOnPRegularConjClass
          (p := p) X (PRegularConjClass.ofSubtype p ⟨s, hs⟩) := by
            symm
            exact FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype
              (p := p) X ⟨s, hs⟩
    _ = virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀ (PRegularConjClass.ofSubtype p ⟨s, hs⟩) := by
            simpa using hχs
    _ = virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [U]₀ ⟨s, hs⟩ := by
          rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
    _ = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] s := by
          symm
          exact pRegularComponentVirtualModularCharacter_apply_of_isPRegular
            (p := p) (K := K) (G := S) (lift := lift) [U]₀ ⟨s, hs⟩

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the ordinary witness required in Serre's elementary `S × P` argument. -/
private theorem primeToP_character_eq_of_pRegularConjClass_eq_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S))
    (U : FDRep k S) (X : FDRep K S)
    (hχ :
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := S)
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
          (p := p) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀ (PRegularConjClass.ofSubtype p ⟨s, hs⟩) := by
            simpa using hχs
    _ = virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [U]₀ ⟨s, hs⟩ := by
          rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
    _ = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] s := by
          symm
          exact pRegularComponentVirtualModularCharacter_apply_of_isPRegular
            (p := p) (K := K) (G := S) (lift := lift) [U]₀ ⟨s, hs⟩

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
          (p := p) (A := K) (G := S)
          (PrimeToPRoot.toFieldLift lift) [U]₀) :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Package the ordinary character of `X` and then collapse the restricted equality to all of
  -- `S` using that `p` does not divide `|S|`.
  let χS : R[K](S) :=
    ⟨X.character, Representation.rep_character_mem_characterRingOverField (Rep.of X.ρ)⟩
  refine ⟨χS, ?_⟩
  exact primeToP_character_eq_of_pRegularConjClass_eq_local
    (p := p) (O := O) (K := K) lift hS U X hχ

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the direct character-ring witness required in Serre's elementary `S × P` argument. -/
private theorem primeToP_simple_class_mem_characterRingOverField_local
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](S) := by
  -- Consume the direct `15.7` left-factor witness produced at the abstraction level Serre uses.
  obtain ⟨χS, hχS⟩ :=
    primeToP_simple_class_character_witness_via_character_field_transport_local
      (p := p) (O := O) (K := K) lift hred hlift hS U
  simpa [hχS] using χS.2

/-- Helper for Theorem 18-18.4-1: on a prime-to-`p` group `S`, a simple modular class already
has the ordinary witness required in Serre's elementary `S × P` argument. -/
private theorem primeToP_simple_class_character_witness_local
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  -- Route correction: expose the exact left-factor witness that the later `S × P` shell consumes,
  -- rather than keeping an auxiliary `PRegularConjClass` package on the critical path.
  let χS : R[K](S) :=
    ⟨([U]₀)′[p, PrimeToPRoot.toFieldLift lift],
      primeToP_simple_class_mem_characterRingOverField_local
        (p := p) (O := O) (K := K) lift hred hlift hS U⟩
  -- Once the direct membership theorem is available, the source shell only needs this packaging.
  exact ⟨χS, rfl⟩

/-- Helper for Theorem 18-18.4-1: an explicit ordinary witness on the prime-to-`p` left factor is
enough to inflate across the direct product with a `p`-group. -/
private theorem split_product_inflated_simple_class_mem_characterRingOverField_of_left_witness_local
    (lift : PrimeToPRoot p k →* Kˣ)
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hS : Nat.Coprime p (Nat.card S)) (hP : IsPGroup p P)
    (U : FDRep k S) [Simple U]
    (hleft :
      ∃ χS : R[K](S), (χS : S → K) = ([U]₀)′[p, PrimeToPRoot.toFieldLift lift]) :
    ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
      R[K](S × P) := by
  -- The local source computation is now isolated to one adapter step:
  -- build the `fst`-pullback of the left-factor witness from
  -- `primeToP_simple_class_character_witness_local`, then identify the inflated transform with
  -- that pullback using `pRegularComponent_prod_eq_left_of_coprime_left_pGroup_local`.
  obtain ⟨χS, hχS⟩ := hleft
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
                      (charpolyRoot_primeToPRoot (p := p) (U.ρ.comp (MonoidHom.fst S P)) hregProd μ.2) : Kˣ) : K))
                ((U.ρ ((MonoidHom.fst S P) (sp.1, (1 : P)))).charpoly.roots.attach)).sum =
                (Multiset.map
                  (fun μ ↦
                    ((lift
                        (charpolyRoot_primeToPRoot (p := p) U.ρ hregS μ.2) : Kˣ) : K))
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
              (p := p) (K := K) (G := S) (lift := lift) [U]₀ ⟨sp.1, hregS⟩
      _ = (χS : S → K) sp.1 := by
            simpa using (congrFun hχS sp.1).symm
  rw [hpoint]
  exact hprecomp

/-- Helper for Theorem 18-18.4-1: if a simple `k[S]`-module already provides the left factor of
the source `S × P` proof, then its inflated transformed class is an ordinary virtual character on
`S × P`. -/
private theorem split_product_inflated_simple_class_mem_characterRingOverField_local
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hS : Nat.Coprime p (Nat.card S)) (hP : IsPGroup p P)
    (U : FDRep k S) [Simple U] :
    ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
      R[K](S × P) := by
  exact
    split_product_inflated_simple_class_mem_characterRingOverField_of_left_witness_local
      (p := p) (O := O) (K := K) lift hS hP U
      (primeToP_simple_class_character_witness_local
        (p := p) (O := O) (K := K) lift hred hlift hS U)

/-- Helper for Theorem 18-18.4-1: Serre's `f ↦ f'` transform commutes with transport across a
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
            (charpolyRoot_primeToPRoot (p := p) (V.ρ.comp e.toMonoidHom)
              aReg.2 μ.2) : Kˣ) : K))
      (((V.ρ.comp e.toMonoidHom) aReg.1).charpoly.roots.attach)).sum =
      (Multiset.map
        (fun μ ↦
          ((lift
              (charpolyRoot_primeToPRoot (p := p) V.ρ bReg.2 μ.2) : Kˣ) : K))
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
      (p := p) (ρ := ρprod) N hN_p
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
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {H : Subgroup G} (hH : IsElementary H)
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
      (p := p) (S := S) (P := P) (H := H) hS hP e T
  let U : FDRep k S := FDRep.of ρS
  letI : Representation.IsIrreducible U.ρ := by
    simpa [U] using hρSirr
  letI : Simple U := FDRep.simple_of_isIrreducible U
  have hinflated :
      ([FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈
        R[K](S × P) :=
    split_product_inflated_simple_class_mem_characterRingOverField_local
      (p := p) (O := O) (K := K) lift hred hlift hS hP U
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
            (p := p) (O := O) (K := K) (lift := lift)
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
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    {H : Subgroup G} (hH : IsElementary H)
    (x : R₀[k](H)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  classical
  letI : AddCommMonoid (R₀[k](H)) :=
    (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid
  letI : AddCommGroup (R₀[k](H)) :=
    QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)
  letI : Module ℤ (R₀[k](H)) := AddCommGroup.toIntModule (R₀[k](H))
  have hfamilies :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep k H),
        CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
  rcases hfamilies with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  -- Route correction: in characteristic `p` the index type is finite because the Brauer
  -- characters form a basis of the finite-dimensional regular class-function space (the
  -- semisimple `finite_index` owner needs `NeZero (|H| : k)`, unavailable here).
  letI : Fintype (PRegularConjClass H p) := Fintype.ofFinite (PRegularConjClass H p)
  letI : Module.Finite k (PRegularConjClass H p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass H p))
  letI : Finite ι :=
    Module.Finite.finite_basis
      (irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
        π hπ_pairwise hπ_complete)
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
        (p := p) (O := O) (K := K) (G := G) lift hred hlift hH (π i)
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
    [NumberField K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ∀ H : Subgroup G, IsElementary H →
      ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  intro H hH
  -- The restricted simple frontier is now only the ambient elementary theorem specialized to the
  -- class of the restricted module.
  exact elementary_virtual_modular_character_mem_characterRingOverField_local
    (p := p) (O := O) (K := K) (G := G) lift hred hlift hH
    [FDRep.of (S.ρ.comp H.subtype)]₀

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
  -- Unfold Serre's modular-character packet and verify integrality termwise on the root multiset.
  simp only [Representation.modularCharacter]
  refine IsIntegral.multiset_sum ?_
  intro z hz
  rcases Multiset.mem_map.mp hz with ⟨μ, hμ, rfl⟩
  simpa [PrimeToPRoot.toFieldLift] using
    lift_value_isIntegral_rat_local
      (p := p) (O := O) (K := K) lift
      (charpolyRoot_primeToPRoot (p := p) ρ s.2 μ.2)

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
      (p := p) (O := O) (K := K) (lift := lift) S.ρ
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
      (p := p) (O := O) (K := K) (G := G) lift S
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
              (p := p) (K := K) (G := G) lift [S]₀))
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
    simpa [map_add] using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    -- The target character ring is closed under multiplication.
    simpa [map_mul] using (R[K](H)).mul_mem hx hy

/-- Helper for Theorem 18-18.4-1: a lift into `Kˣ` canonically lands in the top
intermediate field of `K`. This is the coefficient-field bridge used in the sufficiently-large
cyclotomic case of Serre's proof. -/
private def top_primeToPRootLift_local
    (lift : PrimeToPRoot p k →* Kˣ) :
    PrimeToPRoot p k →* (⊤ : IntermediateField ℚ K)ˣ where
  toFun ζ :=
    { val := ⟨((lift ζ : Kˣ) : K), by simp⟩
      inv := ⟨(((lift ζ : Kˣ)⁻¹ : Kˣ) : K), by simp⟩
      val_inv := by
        ext
        simp
      inv_val := by
        ext
        simp }
  map_one' := by
    ext
    simp
  map_mul' ζ η := by
    ext
    simp

/-- Helper for Theorem 18-18.4-1: the top-field lift is injective exactly when the original
Brauer lift into `Kˣ` is injective. -/
private theorem top_primeToPRootLift_injective_local
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) :
    Function.Injective (top_primeToPRootLift_local (p := p) (O := O) (K := K) lift) := by
  intro ζ ξ hζξ
  apply hlift
  ext
  have hcoe :=
    congrArg
      (fun z : (⊤ : IntermediateField ℚ K)ˣ => ((z : (⊤ : IntermediateField ℚ K)) : K))
      hζξ
  simpa [top_primeToPRootLift_local] using hcoe

/-- Helper for Theorem 18-18.4-1: after mapping coefficients from the top intermediate field back
to `K`, the transformed simple class formed with the top-field lift is the original transformed
simple class. -/
private theorem transformed_simple_class_top_lift_map_eq_local
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) :
    (fun g : G =>
        algebraMap (⊤ : IntermediateField ℚ K) K
          (([S]₀)′[p,
            PrimeToPRoot.toFieldLift
              (top_primeToPRootLift_local (p := p) (O := O) (K := K) lift)] g)) =
      ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  ext g
  simp [pRegularComponentVirtualModularCharacter_apply, virtualModularCharacter_class,
    modularCharacter, PrimeToPRoot.toFieldLift, top_primeToPRootLift_local]

/-- Helper for Theorem 18-18.4-1: at the top intermediate field of a cyclotomic realization,
Serre's arithmetic subgroup is trivial. -/
private theorem gammaSubgroup_top_eq_bot_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K] :
    Γ[(⊤ : IntermediateField ℚ K)](G) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simpa using
    OrderIso.map_bot
      (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) K).mapSubgroup

/-- Helper for Theorem 18-18.4-1: in the sufficiently-large cyclotomic case, Serre's elementary
subgroup criterion over the top intermediate field turns the local elementary calculation into the
global ordinary-character membership. -/
private theorem transformed_simple_class_detection_via_cyclotomic_top_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  let Ktop : IntermediateField ℚ K := ⊤
  letI : Algebra O Ktop :=
    ((IntermediateField.topEquiv : Ktop ≃ₐ[ℚ] K).symm.toRingHom.comp
      (algebraMap O K)).toAlgebra
  let eKtop : K ≃ₐ[O] Ktop :=
    { (IntermediateField.topEquiv : Ktop ≃ₐ[ℚ] K).symm with
      commutes' := by
        intro a
        rfl }
  letI : IsFractionRing O Ktop := IsFractionRing.of_algEquiv eKtop
  let liftTop : PrimeToPRoot p k →* Ktopˣ :=
    top_primeToPRootLift_local (p := p) (O := O) (K := K) lift
  have hliftTop : Function.Injective liftTop := by
    simpa [Ktop, liftTop] using
      top_primeToPRootLift_injective_local (p := p) (O := O) (K := K) lift hlift
  have hredTop : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O Ktop a = ((liftTop x : Ktopˣ) : Ktop) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k) := by
    intro x
    rcases hred x with ⟨a, haK, hres⟩
    refine ⟨a, ?_, hres⟩
    apply Subtype.ext
    simpa [Ktop, liftTop, top_primeToPRootLift_local] using haK
  let φtop : classFunctionSubmodule Ktop G :=
    ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift liftTop],
      pRegularComponentVirtualModularCharacter_isClassFunction
        (p := p) (K := Ktop) (G := G) liftTop [S]₀⟩
  have hφtop_mem : (φtop : G → Ktop) ∈ R[Ktop](G) := by
    refine
      (classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups
        (L := K) (G := G) Ktop φtop).2 ?_
    intro H hHΓ
    have hHΓbot :
        Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H := by
      simpa [Ktop, gammaSubgroup_top_eq_bot_local (K := K) (G := G)] using hHΓ
    have hH : IsElementary H :=
      (Subgroup.IsGammaElementary.bot_iff_isElementary (G := G) H).1 hHΓbot
    have hlocal :
        ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift liftTop] ∈
          R[Ktop](H) :=
      simple_class_restricted_to_elementary_mem_characterRingOverField_local
        (p := p) (O := O) (K := Ktop) (G := G) liftTop hredTop hliftTop S H hH
    simpa [φtop, Ktop,
      pRegularComponentVirtualModularCharacter_restrict_simple_class
        (p := p) (K := Ktop) (G := G) (lift := liftTop) H S] using hlocal
  have hmap :
      (fun g : G => algebraMap Ktop K (φtop g)) ∈ R[K](G) :=
    map_mem_characterRingOverField_of_mem_intermediateField_characterRing_local
      (K := K) Ktop hφtop_mem
  have hmap_eq :
      (fun g : G => algebraMap Ktop K (φtop g)) =
        ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
    simpa [φtop, Ktop, liftTop] using
      transformed_simple_class_top_lift_map_eq_local
        (p := p) (O := O) (K := K) (G := G) lift S
  exact hmap_eq ▸ hmap

/-- Helper for Theorem 18-18.4-1: restricting an intermediate-field ordinary virtual character
along a subgroup inclusion preserves character-ring membership. This is the exact transport step
needed after placing a `Γ`-elementary subgroup inside its associated subgroup. -/
private theorem restrict_mem_intermediateField_characterRing_of_le_local
    {K0 : Type u} [Field K0] {H A : Subgroup G} (hHA : H ≤ A)
    {χ : A → K0} (hχ : χ ∈ R[K0](A)) :
    (fun h : H ↦ χ (Subgroup.inclusion hHA h)) ∈ R[K0](H) := by
  -- Apply the canonical subgroup-restriction map on Serre's ordinary character ring.
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

/-- Helper for Theorem 18-18.4-1: when Serre's associated-subgroup witnesses are already known
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
    (Subgroup.IsGammaElementary.bot_iff_isElementary (G := G) H).2 hH
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
              (p := p) (K := K) (G := G) lift [S]₀))
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
        (p := p) (O := O) (K := K) (G := G) lift S

/-- Helper for Theorem 18-18.4-1: in the source theorem's sufficiently-large cyclotomic setting,
the intermediate-field detour collapses to the top-field elementary detection argument. -/
private theorem transformed_simple_class_mem_intermediateField_characterRing_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  exact transformed_simple_class_detection_via_cyclotomic_top_local
    (p := p) (O := O) (K := K) (G := G) lift hred hlift S

/-- Helper for Theorem 18-18.4-1: after the local `H = S × P` step is closed, the remaining
global source-faithful task is to shrink the transformed simple class to one value field and then
apply Chapter `12` there. -/
private theorem transformed_simple_class_detection_via_value_field_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  exact transformed_simple_class_mem_intermediateField_characterRing_local
    (p := p) (O := O) (K := K) (G := G) lift hred hlift S

/-- Helper for Theorem 18-18.4-1: after the fixed-prime elementary split is exposed, the only
remaining source-faithful gaps are the textbook local lift on elementary subgroups and the final
over-field elementary detection bridge. -/
private theorem associated_subgroup_explicit_character_bridge_for_simple_class_local
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- The generic detector shell has been removed from the critical path. Once the prime-to-`p`
  -- local witness is available, the global closure should be the value-field descent theorem
  -- specialized to this transformed simple class.
  exact transformed_simple_class_detection_via_value_field_local
    (p := p) (O := O) (K := K) (G := G) lift hred hlift S

/-- Helper for Theorem 18-18.4-1: the remaining work is to realize the `p`-regular-component
transform of a simple modular class as an ordinary virtual character. -/
private theorem pRegularComponentVirtualModularCharacter_simple_class_mem_characterRingOverField
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (S : FDRep k G) [Simple S] :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Route correction: the simple case is now reduced to the explicit associated-subgroup bridge
  -- just above, so the remaining blocker is isolated to one named source-faithful step.
  exact associated_subgroup_explicit_character_bridge_for_simple_class_local
    (p := p) (O := O) (K := K) (G := G) lift hred hlift S

-- Proof sketch: restrict first to the case of a simple modular class, where Serre's elementary
-- subgroup argument realizes the `p`-regular-component class function as an ordinary character;
-- then extend by additivity to arbitrary classes in `R_k(G)`.
/-- Theorem 18-18.4-1 (1): for a class `x ∈ R_k(G)`, the class function `f'` obtained by
evaluating its virtual modular character on the chosen `p`-regular component of each element of
`G` is an ordinary virtual character of `G`, realized here as an element of `R[K](G)` for the
characteristic-zero coefficient field `K`. -/
theorem pRegularComponentVirtualModularCharacter_mem_characterRingOverField
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (x : R₀[k](G)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  classical
  have hfamilies :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
        CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
  rcases hfamilies with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  -- Route correction: in characteristic `p` the index type is finite because the Brauer
  -- characters form a basis of the finite-dimensional regular class-function space (the
  -- semisimple `finite_index` owner needs `NeZero (|G| : k)`, unavailable here).
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite ι :=
    Module.Finite.finite_basis
      (irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
        π hπ_pairwise hπ_complete)
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
        (p := p) (O := O) (K := K) (G := G) lift hred hlift (π i)
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

/-- Theorem 18-18.4-1, source-facing additive owner: Serre's `x ↦ x'` construction viewed
directly as a homomorphism from `R_k(G)` to the ordinary character ring `R_K(G)`. -/
def pRegularComponentVirtualCharacter
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift) :
    R₀[k](G) →+ R[K](G) :=
  (pRegularComponentVirtualModularCharacter p (PrimeToPRoot.toFieldLift lift)).codRestrict
    (R[K](G))
    (fun x ↦
      pRegularComponentVirtualModularCharacter_mem_characterRingOverField lift hred hlift x)

@[simp] theorem pRegularComponentVirtualCharacter_apply
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (x : R₀[k](G)) (g : G) :
    pRegularComponentVirtualCharacter p lift hred hlift x g =
      x′[p, PrimeToPRoot.toFieldLift lift] g :=
  rfl

/-- Helper for Theorem 18-18.4-1: on a `p`-regular element, Serre's `f ↦ f'` construction simply
recovers the original virtual modular character. -/
@[simp] theorem pRegularComponentVirtualCharacter_apply_of_isPRegular
    [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift) (x : R₀[k](G))
    (s : { g : G // IsPRegular p g }) :
    pRegularComponentVirtualCharacter p lift hred hlift x s.1 =
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) x s := by
  -- On the `p`-regular locus, the canonical `p`-regular component is the point itself.
  simp [pRegularComponentVirtualCharacter_apply,
    pRegularComponent_eq_self_of_isPRegular s.2]

end CharacterRingLift

section

variable {p : ℕ} [Fact p.Prime]
variable {O : Type u} [CommRing O] [IsLocalRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [HenselianLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {K : Type u} [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
variable {G : Type u} [Group G] [Finite G]
variable [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
variable [IsAlgClosed (IsLocalRing.ResidueField O)] [CharP (IsLocalRing.ResidueField O) p]

local notation "k" => IsLocalRing.ResidueField O

local instance instFintypeTheorem181841Section : Fintype G := Fintype.ofFinite G

/-- Helper for Theorem 18-18.4-1: reducing an ordinary virtual character and then evaluating its
Brauer character on the `p`-regular locus agrees with restricting the original ordinary character
to the `p`-regular subtype. -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (y : R₀[K](G)) :
    virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom O K G) y) =
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G) y : G → K) ∘ Subtype.val := by
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
    obtain ⟨L⟩ := Representation.exists_stableLattice O E.ρ
    -- On a generator `[E]₀`, Chapter `18.3` already identifies the modular character of the
    -- reduction with the restriction of the ordinary character of `E`.
    ext s
    change
      (virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom O K G) [E]₀)) s =
        ((ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (G := G) [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := O) (K := K) (G := G) E L,
      virtualModularCharacter_class,
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := O) (K := K) (G := G) lift hred E.ρ L s (hω s.1 s.2))
  · intro a ha
    -- Additivity carries the comparison through negation.
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    -- Additivity carries the comparison through sums.
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

/-- Helper for Theorem 18-18.4-1: once an additive section of
`finiteRepGrothendieckCharacter` is fixed, composing it with Serre's `x ↦ x'` map immediately
recovers `pRegularComponentVirtualCharacter` after applying
`finiteRepGrothendieckCharacter`. -/
theorem finiteRepGrothendieckCharacter_comp_section_eq_pRegularComponentVirtualCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hlift : Function.Injective lift)
    (t : R[K](G) →+ R₀[K](G))
    (ht : Function.LeftInverse
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G)) t) :
    (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
      (F := K) (G := G)).comp
        (t.comp (pRegularComponentVirtualCharacter p lift hred hlift)) =
      pRegularComponentVirtualCharacter p lift hred hlift := by
  ext x g
  -- Evaluate the left-inverse identity pointwise on the ordinary character side.
  simpa [AddMonoidHom.comp_apply] using
    congrArg (fun χ : R[K](G) ↦ χ g)
      (ht (((pRegularComponentVirtualCharacter p lift hred hlift).comp
        (QuotientAddGroup.mk' (finiteRepGrothendieckRelations k G))) (FreeAbelianGroup.of x)))

/-- Helper for Theorem 18-18.4-1: with an injective lift of the prime-to-`p` roots, any additive
section of `finiteRepGrothendieckCharacter` becomes a left inverse to `decompositionHom` after
composition with Serre's `x ↦ x'` construction. -/
theorem decompositionHom_leftInverse_of_pRegularComponent_section
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (hlift : Function.Injective lift)
    (t : R[K](G) →+ R₀[K](G))
    (ht : Function.LeftInverse
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G)) t) :
    Function.LeftInverse (decompositionHom O K G)
      (t.comp (pRegularComponentVirtualCharacter p lift hred hlift)) := by
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
    virtualModularCharacter_decomposition_eq_character_restriction_local
      (p := p) (O := O) (K := K) (G := G) lift hred hω]
  have hchar :
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G)) (t (pRegularComponentVirtualCharacter p lift hred hlift x)) =
        pRegularComponentVirtualCharacter p lift hred hlift x :=
    ht (pRegularComponentVirtualCharacter p lift hred hlift x)
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
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G)
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

/-- Helper for Theorem 18-18.4-1: the normalized pairing is additive on finite
`K`-linear combinations in its left argument. -/
private theorem groupFunctionPairing_sum_smul_left_characteristic_zero_local
    {ι : Type*} (s : Finset ι) (a : ι → K) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, a j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, groupFunctionPairing_smul_left,
        ih, Finset.sum_insert hi]

/-- Helper for Theorem 18-18.4-1: pairwise nonisomorphic irreducible characters are already
`K`-linearly independent as class functions in characteristic zero. -/
private theorem linearIndependent_character_functions_of_pairwiseNonisomorphic_local
    {ι : Type*} (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π) :
    LinearIndependent K (fun i ↦ (π i).character) := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpair0 :=
    congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hg
  have hpair :
      ⟪∑ j ∈ s, g j • (π j).character, (π i).character⟫ = (0 : K) := by
    simpa [Representation.groupFunctionPairingOverField] using hpair0
  rw [groupFunctionPairing_sum_smul_left_characteristic_zero_local
      (K := K) (G := G) (s := s) g (fun j ↦ (π j).character) ((π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · have hself_ne :
        ⟪(π i).character, (π i).character⟫ ≠ (0 : K) :=
      groupFunctionPairingOverField_character_self_ne_zero (K := K) (G := G) (π i)
    exact (mul_eq_zero.mp hpair).resolve_right hself_ne
  · intro j _ hji
    simp [horth hji]
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Theorem 18-18.4-1: a complete pairwise nonisomorphic irreducible family over a
finite characteristic-zero group has only finitely many members. -/
private theorem finite_index_of_complete_pairwiseNonisomorphic_characteristic_zero_local
    {ι : Type*} (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  classical
  letI : FiniteDimensional K (G → K) := by
    infer_instance
  have hlin :
      LinearIndependent K (fun i ↦ (π i).character) :=
    linearIndependent_character_functions_of_pairwiseNonisomorphic_local
      (K := K) (G := G) π hπ_complete hπ_pairwise
  exact Cardinal.lt_aleph0_iff_finite.mp
    (LinearIndependent.lt_aleph0_of_finiteDimensional hlin)

/-- Helper for Theorem 18-18.4-1: in characteristic zero, the Grothendieck-group character map
admits an additive section constructed by matching the ordinary-character basis with the
simple-class basis. -/
theorem finiteRepGrothendieckCharacter_has_section_local :
    ∃ t : R[K](G) →+ R₀[K](G),
      Function.LeftInverse
        (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (G := G)) t := by
  classical
  rcases
      exists_complete_pairwise_nonisomorphic_simple_family_characteristic_zero_local
      (K := K) (G := G) with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  letI : Finite ι :=
    finite_index_of_complete_pairwiseNonisomorphic_characteristic_zero_local
      (K := K) (G := G) π hπ_pairwise hπ_complete
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
        calc
          (∑ i, (bR.repr (χ + ψ) i) • b₀ i)
              = ∑ i, ((bR.repr χ i) + (bR.repr ψ i)) • b₀ i := by
                refine Finset.sum_congr rfl ?_
                intro i _
                have hrepr := congrArg (fun f : ι →₀ ℤ => f i) (map_add bR.repr χ ψ)
                simpa using hrepr
          _ = ∑ i, ((bR.repr χ i) • b₀ i + (bR.repr ψ i) • b₀ i) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                exact add_smul (bR.repr χ i) (bR.repr ψ i) (b₀ i)
          _ = (∑ i, (bR.repr χ i) • b₀ i) +
                (∑ i, (bR.repr ψ i) • b₀ i) := by
                rw [Finset.sum_add_distrib] }
  refine ⟨t, ?_⟩
  intro χ
  -- Expand `χ` in the ordinary-character basis and send the matching simple-class expansion
  -- through `finiteRepGrothendieckCharacter`.
  calc
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G) (t χ)
        = ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (G := G) (∑ i, (bR.repr χ i) • b₀ i) := rfl
    _ = ∑ i, (bR.repr χ i) •
          ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K) (G := G) (b₀ i) := by
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
-- and `decompositionHom O K G` is a left inverse.
/-- Theorem 18-18.4-1 (2): the assignment `x ↦ x'`, obtained by evaluating the virtual modular
character of `x ∈ R_k(G)` on the chosen `p`-regular component of each element of `G`, is induced,
via the canonical bridge `finiteRepGrothendieckCharacter : R₀[K](G) → R[K](G)`, by an additive
section of the decomposition homomorphism `d : R₀[K](G) → R₀[k](G)` for the
characteristic-zero coefficient field `K`. In the source-faithful Brauer-lift setting, the lift
on `p'`-roots must be genuine; in this Lean surface we record that by requiring the chosen
`lift` to be injective. -/
theorem exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : O,
      algebraMap O K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue O a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (hlift : Function.Injective lift)
    :
    ∃ s : R₀[k](G) →+ R₀[K](G),
      Function.LeftInverse (decompositionHom O K G) s ∧
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G)).comp s =
          pRegularComponentVirtualCharacter p lift hred hlift :=
      by
        -- Route correction: first construct the characteristic-zero section of
        -- `finiteRepGrothendieckCharacter`, then compose it with Serre's `x ↦ x'` map.
        rcases finiteRepGrothendieckCharacter_has_section_local (K := K) (G := G) with ⟨t, ht⟩
        refine ⟨t.comp (pRegularComponentVirtualCharacter p lift hred hlift), ?_, ?_⟩
        · -- On the `p`-regular locus, Corollary `18-18.2-4` turns the ordinary-character section
          -- identity into the required left inverse for `decompositionHom`.
          exact decompositionHom_leftInverse_of_pRegularComponent_section
            (p := p) (O := O) (K := K) (G := G) lift hred hω hlift t ht
        · -- The chosen section was built precisely so that applying
          -- `finiteRepGrothendieckCharacter` recovers Serre's `x ↦ x'` character.
          exact finiteRepGrothendieckCharacter_comp_section_eq_pRegularComponentVirtualCharacter
            (p := p) (O := O) (K := K) (G := G) lift hred hlift t ht
-- #print axioms exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter
end

end Representation
