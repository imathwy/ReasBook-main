import Mathlib
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_18_3_1 (from Chap18) -/
noncomputable section

universe u

namespace Representation

open CategoryTheory
open scoped Pointwise
open scoped MonoidAlgebra
open scoped MonoidalCategory
open scoped Representation
open scoped Representation.ExternalTensor
open scoped TensorProduct
open scoped ZeroObject

section

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation "pPartCardG" => p ^ Nat.factorization (Nat.card G) p
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

/-- Helper for Theorem 18-18.3-1: a normal `p`-subgroup acts trivially on an irreducible
characteristic-`p` representation. -/
private theorem isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  classical
  let ρN : Representation k N V := ρ.comp N.subtype
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let U : Subrepresentation ρ :=
    { toSubmodule := ρN.invariants
      apply_mem_toSubmodule := by
        intro g x hx
        rw [ρN.mem_invariants] at hx ⊢
        intro n
        have hconj : g⁻¹ * (n : G) * g ∈ N :=
          Subgroup.Normal.conj_mem' inferInstance (n : G) n.2 g
        have hxconj : ρ (g⁻¹ * (n : G) * g) x = x := hx ⟨g⁻¹ * (n : G) * g, hconj⟩
        calc
          ρ (n : G) (ρ g x) = ρ ((n : G) * g) x := by
            simp [map_mul]
          _ = ρ (g * (g⁻¹ * (n : G) * g)) x := by
            simp [mul_assoc]
          _ = ρ g (ρ (g⁻¹ * (n : G) * g) x) := by
            simp [map_mul]
          _ = ρ g x := by
            rw [hxconj] }
  have hU_ne_bot : U ≠ ⊥ := by
    -- The restricted `p`-group action fixes a nonzero vector.
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP (ρ := ρN) hN) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  -- Irreducibility upgrades the invariant subspace to the whole carrier.
  refine ⟨fun n ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hx : x ∈ ρN.invariants := by
    simpa [U] using hxU
  exact (ρN.mem_invariants x).1 hx n

section ElementaryPrimeSplitLocal

variable {H : Subgroup G}

/-- Helper for Theorem 18-18.3-1: a cyclic subgroup splits into its prime-to-`p` and `p` parts. -/
private theorem cyclic_subgroup_exists_primeToP_pGroup_split_local
    (C : Subgroup H) (hC : IsCyclic C) :
    ∃ (S P : Subgroup H),
      S ≤ C ∧
        P ≤ C ∧
          Nat.Coprime p (Nat.card S) ∧
            IsPGroup p P ∧
              S ≤ Subgroup.centralizer (P : Set H) ∧
                Disjoint S P ∧
                  C = S ⊔ P := by
  letI : Finite H := Finite.of_injective H.subtype H.subtype_injective
  letI : IsCyclic C := hC
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := C)
  let cH : H := c
  let S : Subgroup H := Subgroup.zpowers (pRegularComponent p cH)
  let P : Subgroup H := Subgroup.zpowers (pUnipotentComponent p cH)
  have hC_eq : C = Subgroup.zpowers cH := by
    -- The chosen generator of `C` still generates the same subgroup inside `H`.
    ext x
    constructor
    · intro hx
      have hxgen : (⟨x, hx⟩ : C) ∈ Subgroup.zpowers c := hcgen ⟨x, hx⟩
      rcases (Subgroup.mem_zpowers_iff.mp hxgen) with ⟨n, hn⟩
      exact (Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩)
    · intro hx
      exact ((Subgroup.zpowers_le).2 c.2) hx
  let hdecomp :=
    p_component_decomposition_exists (p := p) cH (isOfFinOrder_of_finite cH)
  have hS_le : S ≤ C := by
    -- The `p`-regular component is a power of the generator `c`.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.right_mem_zpowers
  have hP_le : P ≤ C := by
    -- The `p`-unipotent component is also a power of the generator `c`.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.left_mem_zpowers
  have hS_coprime : Nat.Coprime p (Nat.card S) := by
    -- The cyclic subgroup generated by the `p`-regular component has prime-to-`p` order.
    simpa [S, Nat.card_zpowers] using hdecomp.isPRegular
  have hP_isPGroup : IsPGroup p P := by
    -- The cyclic subgroup generated by the `p`-unipotent component is a `p`-group.
    rw [isPGroup_iff_forall_isPElement]
    intro y
    have hy_div :
        orderOf ((y : P) : H) ∣ orderOf (pUnipotentComponent p cH) :=
      orderOf_dvd_of_mem_zpowers y.2
    rcases hdecomp.isPElement with ⟨n, hn⟩
    have hy_pow : orderOf ((y : P) : H) ∣ p ^ n := by
      simpa [hn] using hy_div
    rcases (Nat.dvd_prime_pow Fact.out).1 hy_pow with ⟨m, -, hm⟩
    exact ⟨m, by simpa [Subgroup.orderOf_mk] using hm⟩
  have hS_cent : S ≤ Subgroup.centralizer (P : Set H) := by
    -- Both factors are generated by powers of the same element, so they commute.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases (Subgroup.mem_zpowers_iff.mp hs) with ⟨m, rfl⟩
    rcases (Subgroup.mem_zpowers_iff.mp hu) with ⟨n, rfl⟩
    simpa using ((hdecomp.commute.zpow_left n).zpow_right m).eq
  have hSP_disjoint : Disjoint S P := by
    -- An element in both factors has order both prime to `p` and a `p`-power.
    rw [disjoint_iff]
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_inf] at hz
      have hzS : z ∈ S := hz.1
      have hzP : z ∈ P := hz.2
      have hzDivS : orderOf z ∣ orderOf (pRegularComponent p cH) :=
        orderOf_dvd_of_mem_zpowers hzS
      have hzDivP : orderOf z ∣ orderOf (pUnipotentComponent p cH) :=
        orderOf_dvd_of_mem_zpowers hzP
      rcases hdecomp.isPElement with ⟨n, hn⟩
      have hzPow : orderOf z ∣ p ^ n := by
        simpa [hn] using hzDivP
      rcases (Nat.dvd_prime_pow Fact.out).1 hzPow with ⟨m, -, hm⟩
      have hzOne : orderOf z = 1 := by
        exact hm.trans (Nat.Coprime.eq_one_of_dvd (hdecomp.isPRegular.pow_left m) (hm ▸ hzDivS))
      exact orderOf_eq_one_iff.mp hzOne
    · intro hz
      rw [Subgroup.mem_inf]
      have hz1 : z = 1 := Subgroup.mem_bot.mp hz
      constructor <;> simp [hz1]
  have hC_le_sup : C ≤ S ⊔ P := by
    -- The original generator is the product of its chosen `p`-regular and `p`-unipotent parts.
    have hc_sup : cH ∈ S ⊔ P := by
      rw [show cH = pRegularComponent p cH * pUnipotentComponent p cH by
        calc
          cH = pUnipotentComponent p cH * pRegularComponent p cH := hdecomp.eq_mul
          _ = pRegularComponent p cH * pUnipotentComponent p cH := by
                simpa using hdecomp.commute.eq]
      exact Subgroup.mul_mem (S ⊔ P)
        ((show S ≤ S ⊔ P from le_sup_left) (Subgroup.mem_zpowers (pRegularComponent p cH)))
        ((show P ≤ S ⊔ P from le_sup_right) (Subgroup.mem_zpowers (pUnipotentComponent p cH)))
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hc_sup
  have hsup_le_C : S ⊔ P ≤ C := sup_le hS_le hP_le
  refine ⟨S, P, hS_le, hP_le, hS_coprime, hP_isPGroup, hS_cent, hSP_disjoint, ?_⟩
  exact le_antisymm hC_le_sup hsup_le_C

/-- Helper for Theorem 18-18.3-1: if `Q` centralizes a cyclic factor `C`, then it centralizes the
`p`-primary factor cut out inside `C`. -/
private theorem qgroup_centralizes_pgroup_factor_of_cyclic_split_local
    {q : ℕ} [Fact q.Prime]
    {C Q P₀ : Subgroup H}
    (hCQcent : C ≤ Subgroup.centralizer (Q : Set H))
    (hP₀C : P₀ ≤ C) :
    Q ≤ Subgroup.centralizer (P₀ : Set H) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hCQcent (hP₀C hu) q hq).symm

/-- Helper for Theorem 18-18.3-1: after splitting the cyclic factor of an elementary subgroup,
one obtains a complement by a prime-to-`p` subgroup and a `p`-group. -/
private theorem primeToP_pGroup_complement_of_cyclic_split_and_qgroup_complement_local
    {q : ℕ} [Fact q.Prime]
    {C Q S₀ P₀ : Subgroup H}
    (hCQ : C.IsComplement' Q)
    (hCQcent : C ≤ Subgroup.centralizer (Q : Set H))
    (hQ : IsPGroup q Q) (hqp : q ≠ p)
    (hS₀C : S₀ ≤ C) (hP₀C : P₀ ≤ C)
    (hS₀ : Nat.Coprime p (Nat.card S₀)) (hP₀ : IsPGroup p P₀)
    (hS₀cent : S₀ ≤ Subgroup.centralizer (P₀ : Set H))
    (hS₀P₀disj : Disjoint S₀ P₀)
    (hCeq : C = S₀ ⊔ P₀) :
    Nat.Coprime p (Nat.card ↥(S₀ ⊔ Q)) ∧
      (S₀ ⊔ Q) ≤ Subgroup.centralizer (P₀ : Set H) ∧
      (S₀ ⊔ Q).IsComplement' P₀ := by
  have hcent_norm {B : Subgroup H} :
      Subgroup.centralizer (B : Set H) ≤ Subgroup.normalizer B := by
    -- Centralizing a subgroup is stronger than normalizing it.
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have hzEq : z * u * z⁻¹ = u := by
        calc
          z * u * z⁻¹ = u * z * z⁻¹ := by
            rw [← hz u hu]
          _ = u := by
            simp [mul_assoc]
      rw [hzEq]
      exact hu
    · intro hu
      let q : H := z * u * z⁻¹
      have hq : q ∈ B := hu
      have hqEq : z * q * z⁻¹ = q := by
        calc
          z * q * z⁻¹ = q * z * z⁻¹ := by
            rw [← hz q hq]
          _ = q := by
            simp [mul_assoc, q]
      have huEq : u = z * u * z⁻¹ := by
        calc
          u = z⁻¹ * q * z := by
            simp [q, mul_assoc]
          _ = z⁻¹ * (z * q * z⁻¹) * z := by
            rw [hqEq]
          _ = q := by
            simp [mul_assoc]
          _ = z * u * z⁻¹ := rfl
      rw [huEq]
      exact hu
  have hQcent : Q ≤ Subgroup.centralizer (P₀ : Set H) :=
    qgroup_centralizes_pgroup_factor_of_cyclic_split_local
      (q := q) (C := C) (Q := Q) (P₀ := P₀)
      (hCQcent := hCQcent) (hP₀C := hP₀C)
  have hS₀Qcent : (S₀ ⊔ Q) ≤ Subgroup.centralizer (P₀ : Set H) := by
    -- Both the `S₀` and `Q` factors centralize `P₀`.
    rw [sup_le_iff]
    exact ⟨hS₀cent, hQcent⟩
  have hS₀Qdisj : Disjoint S₀ Q := hCQ.disjoint.mono_left hS₀C
  have hS₀Qnorm : S₀ ≤ Subgroup.normalizer Q := by
    -- Centralizing `Q` is enough to normalize it.
    intro s hs
    exact (hcent_norm (B := Q)) (hCQcent (hS₀C hs))
  have hS₀Qset : (↑(S₀ ⊔ Q) : Set H) = (↑S₀ : Set H) * (↑Q : Set H) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S₀ Q hS₀Qnorm
  have hSQP₀disj : Disjoint (S₀ ⊔ Q) P₀ := by
    -- A mixed factorization inside `P₀` collapses to the identity by the two disjointness
    -- relations.
    rw [Subgroup.disjoint_def]
    intro x hx hxP
    have hx' : (x : H) ∈ (↑(S₀ ⊔ Q) : Set H) := hx
    rw [hS₀Qset] at hx'
    rcases hx' with ⟨s, hs, u, hu, hxu⟩
    have hsuP : s * u ∈ P₀ := by
      simpa [hxu] using hxP
    have hsInC : s ∈ C := hS₀C hs
    have huC : u ∈ C := by
      have hsInvC : s⁻¹ ∈ C := C.inv_mem hsInC
      have hmulC : s⁻¹ * (s * u) ∈ C := C.mul_mem hsInvC (hP₀C hsuP)
      simpa [mul_assoc] using hmulC
    have hCQdisj := hCQ.disjoint
    rw [Subgroup.disjoint_def] at hCQdisj
    have hu1 : u = 1 := hCQdisj huC hu
    have hsP : s ∈ P₀ := by
      simpa [hu1] using hsuP
    have hS₀P₀disj' := hS₀P₀disj
    rw [Subgroup.disjoint_def] at hS₀P₀disj'
    have hs1 : s = 1 := hS₀P₀disj' hs hsP
    calc
      x = s * u := hxu.symm
      _ = 1 := by
        simp [hs1, hu1]
  have hS₀Qcard : Nat.card ↥(S₀ ⊔ Q) = Nat.card S₀ * Nat.card Q := by
    -- The join is literally the product set because `S₀` normalizes `Q`.
    let f : S₀ × Q → ↥(S₀ ⊔ Q) := fun x ↦
      ⟨(x.1 : H) * x.2, by
        exact Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hf_bij : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have hmul : (a.1 : H) * a.2 = (b.1 : H) * b.2 := congrArg Subtype.val hab
        exact (Subgroup.mul_injective_of_disjoint hS₀Qdisj) hmul
      · intro x
        have hx : (x : H) ∈ (↑S₀ : Set H) * (↑Q : Set H) := by
          rw [← hS₀Qset]
          exact x.2
        rcases hx with ⟨s, hs, u, hu, hsu⟩
        refine ⟨(⟨s, hs⟩, ⟨u, hu⟩), ?_⟩
        exact Subtype.ext hsu
    simpa [Nat.card_prod] using (Nat.card_eq_of_bijective f hf_bij).symm
  have hQcop : Nat.Coprime p (Nat.card Q) :=
    coprime_card_of_isPGroup_of_ne (p := p) (q := q) hqp.symm hQ
  have hSQcop : Nat.Coprime p (Nat.card ↥(S₀ ⊔ Q)) := by
    -- Both factors in the new left side have order prime to `p`.
    rw [hS₀Qcard]
    exact hS₀.mul_right hQcop
  have hsup_top : (S₀ ⊔ Q) ⊔ P₀ = ⊤ := by
    calc
      (S₀ ⊔ Q) ⊔ P₀ = (S₀ ⊔ P₀) ⊔ Q := by
        ac_rfl
      _ = C ⊔ Q := by
        rw [← hCeq]
      _ = ⊤ := hCQ.sup_eq_top
  have hSQP₀norm : (S₀ ⊔ Q) ≤ Subgroup.normalizer P₀ := by
    -- The whole new left factor centralizes `P₀`.
    intro x hx
    exact (hcent_norm (B := P₀)) (hS₀Qcent hx)
  have hmul_univ : ((↑(S₀ ⊔ Q) : Set H) * (↑P₀ : Set H)) = (Set.univ : Set H) := by
    calc
      ((↑(S₀ ⊔ Q) : Set H) * (↑P₀ : Set H)) = ↑((S₀ ⊔ Q) ⊔ P₀) := by
        symm
        exact Subgroup.coe_mul_of_left_le_normalizer_right (S₀ ⊔ Q) P₀ hSQP₀norm
      _ = Set.univ := by
        simp [hsup_top]
  exact ⟨hSQcop, hS₀Qcent,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hSQP₀disj hmul_univ⟩

/-- Helper for Theorem 18-18.3-1: every ordinary elementary subgroup admits the source-faithful
split into a prime-to-`p` factor and a `p`-group factor. -/
private theorem elementary_exists_primeToP_pGroup_complement_local
    (H : Subgroup G) (hH : IsElementary H) :
    ∃ (S P : Subgroup H),
      Nat.Coprime p (Nat.card S) ∧
        IsPGroup p P ∧
          S ≤ Subgroup.centralizer (P : Set H) ∧
            S.IsComplement' P := by
  rcases hH with ⟨q, C, Q, hCQ⟩
  letI : Fact q.Prime := ⟨hCQ.prime⟩
  by_cases hqp : q = p
  · subst hqp
    -- When the elementary prime matches `p`, the original decomposition already has the required
    -- form.
    exact ⟨C, Q, hCQ.coprime_card, hCQ.isPGroup, hCQ.centralizes, hCQ.isComplement⟩
  · obtain ⟨S₀, P₀, hS₀C, hP₀C, hS₀, hP₀, hS₀cent, hS₀P₀disj, hCeq⟩ :=
      cyclic_subgroup_exists_primeToP_pGroup_split_local (p := p) C hCQ.cyclic
    obtain ⟨hSQ, hPcent, hSPcomp⟩ :=
      primeToP_pGroup_complement_of_cyclic_split_and_qgroup_complement_local
        (p := p) (hCQ := hCQ.isComplement) (hCQcent := hCQ.centralizes)
        (hQ := hCQ.isPGroup) (hqp := hqp) (hS₀C := hS₀C) (hP₀C := hP₀C)
        (hS₀ := hS₀) (hP₀ := hP₀) (hS₀cent := hS₀cent) (hS₀P₀disj := hS₀P₀disj)
        (hCeq := hCeq)
    exact ⟨S₀ ⊔ Q, P₀, hSQ, hP₀, hPcent, hSPcomp⟩

end ElementaryPrimeSplitLocal

/-- Helper for Theorem 18-18.3-1: natural-number scalar multiplication on `R₀[k](H)` distributes
over a finite sum indexed by a `Fintype`. -/
private theorem grothendieck_nsmul_sum_local
    {H : Type u} [Group H] {ι : Type*} [Fintype ι]
    (N : ℕ) (f : ι → R₀[k](H)) :
    (N : ℕ) • ∑ i, f i = ∑ i, (N : ℕ) • f i := by
  classical
  -- Rewrite the scalar as multiplication in the Grothendieck ring and use distributivity once.
  simpa [nsmul_eq_mul] using
    (Finset.mul_sum Finset.univ (fun i ↦ f i) (((N : ℕ) : R₀[k](H))))

/-- Helper for Theorem 18-18.3-1: the ordinary character of a finite-dimensional
`K[G]`-representation belongs to LinearRepresentations_Serre_1977's character ring owner `R[K](G)`. -/
private theorem finiteRepCharacter_mem_characterRingOverField_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] (V : FDRep K G) :
    V.character ∈ R[K](G) := by
  simpa using Representation.rep_character_mem_characterRingOverField
    (Rep.of V.ρ)

/-- Helper for Theorem 18-18.3-1: the generator-level ordinary-character lift from the free
abelian group on finite-dimensional `K[G]`-representations into `R[K](G)`. -/
private abbrev finiteRepGrothendieckCharacterLiftLocal
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    FreeAbelianGroup (FDRep K G) →+ R[K](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRingOverField_local K G V⟩

/-- Helper for Theorem 18-18.3-1: the ordinary character is additive on short exact
sequences of finite-dimensional representations. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G]
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[K] S.X₂.V := ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule K S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[K] S.X₃.V := W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.g) a x
  have hchar₁ : S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ : S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    simpa [W, qg] using (Representation.char_iso e₃).symm
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
            simpa [W] using
              character_eq_add_character_quotient_of_invariant_submodule_local
                (K := K) (G := G) S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

/-- Helper for Theorem 18-18.3-1: the defining Grothendieck relations already vanish under the
generator-level ordinary-character lift. -/
private theorem finiteRepGrothendieckRelations_le_characterLift_ker_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    finiteRepGrothendieckRelations K G ≤
      (finiteRepGrothendieckCharacterLiftLocal K G).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLiftLocal K G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local K G S hS) g
  simpa [finiteRepGrothendieckCharacterLiftLocal, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using sub_eq_zero.mpr hchar

/-- Helper for Theorem 18-18.3-1: the ordinary-character map on `R₀[K](G)`. -/
private noncomputable def finiteRepGrothendieckCharacter
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    R₀[K](G) →+ R[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckCharacterLiftLocal K G)
    (finiteRepGrothendieckRelations_le_characterLift_ker_local K G)

/-- Helper for Theorem 18-18.3-1: on a genuine finite-dimensional representation class, the
ordinary Grothendieck-character owner evaluates to the ordinary character. -/
@[simp] private theorem finiteRepGrothendieckCharacter_class
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G]
    (V : FDRep K G) (g : G) :
    finiteRepGrothendieckCharacter K G [V]₀ g = V.character g := by
  simp [finiteRepGrothendieckCharacter, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLiftLocal]

/-- Helper for Theorem 18-18.3-1: the free lift sending a finite-dimensional class on `A` to its
pullback along `φ : B →* A`. -/
private abbrev finiteRepGrothendieckPrecomposeLiftLocal
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁) :
    FreeAbelianGroup (FDRep k G₁) →+ R₀[k](G₂) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.of (V.ρ.comp φ)]₀

/-- Helper for Theorem 18-18.3-1: transport an `FDRep` morphism along `φ : B →* A` by keeping
its underlying `k`-linear map and rechecking equivariance only on the pulled-back `B`-action. -/
private abbrev finiteRep_precompose_map_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁)
    {V W : FDRep k G₁} (f : V ⟶ W) :
    FDRep.of (V.ρ.comp φ) ⟶ FDRep.of (W.ρ.comp φ) :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.ofHom ⟨((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.toLinearMap, fun b => by
      -- The original intertwining identity applies after evaluating at `φ b`.
      simpa using (((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.isIntertwining' (φ b))⟩)

/-- Helper for Theorem 18-18.3-1: forgetting the pulled-back `FDRep` morphism recovers the
explicit `Rep` morphism built from the same linear map. -/
private theorem finiteRep_precompose_map_forget_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁)
    {V W : FDRep k G₁} (f : V ⟶ W) :
    (forget₂ (FDRep k G₂) (Rep k G₂)).map
        (finiteRep_precompose_map_local (G₁ := G₁) (G₂ := G₂) φ f) =
      Rep.ofHom
        ⟨(((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.toLinearMap), fun b => by
          -- Again evaluate the original intertwining identity at `φ b`.
          simpa using (((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.isIntertwining' (φ b))⟩ := by
  -- `finiteRep_precompose_map_local` was defined by transporting this `Rep` map back through
  -- `FDRep.forget₂HomLinearEquiv`.
  let fφ :
      ((forget₂ (FDRep k G₂) (Rep k G₂)).obj (FDRep.of (V.ρ.comp φ)) ⟶
        (forget₂ (FDRep k G₂) (Rep k G₂)).obj (FDRep.of (W.ρ.comp φ))) :=
    Rep.ofHom
      ⟨(((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.toLinearMap), fun b => by
        simpa using (((forget₂ (FDRep k G₁) (Rep k G₁)).map f).hom.isIntertwining' (φ b))⟩
  have hforget :
      (forget₂ (FDRep k G₂) (Rep k G₂)).map
          (finiteRep_precompose_map_local (G₁ := G₁) (G₂ := G₂) φ f) = fφ := by
    change (FDRep.forget₂HomLinearEquiv (FDRep.of (V.ρ.comp φ)) (FDRep.of (W.ρ.comp φ))).symm
        ((FDRep.forget₂HomLinearEquiv (FDRep.of (V.ρ.comp φ)) (FDRep.of (W.ρ.comp φ))) fφ) = fφ
    exact (FDRep.forget₂HomLinearEquiv _ _).left_inv fφ
  simpa [fφ] using hforget

/-- Helper for Theorem 18-18.3-1: the explicit short complex obtained by precomposing the three
terms of `S` with `φ`, while keeping the underlying `k`-linear maps unchanged. -/
private abbrev finiteRepGrothendieckPrecompose_shortComplex_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁)
    (S : ShortComplex (FDRep k G₁)) : ShortComplex (FDRep k G₂) :=
  ShortComplex.mk
    (finiteRep_precompose_map_local (G₁ := G₁) (G₂ := G₂) φ S.f)
    (finiteRep_precompose_map_local (G₁ := G₁) (G₂ := G₂) φ S.g)
    (by
      -- After forgetting to `Rep k B`, composition is still zero because the linear maps did not
      -- change from the original short complex over `A`.
      apply (forget₂ (FDRep k G₂) (Rep k G₂)).map_injective
      rw [Functor.map_comp]
      rw [finiteRep_precompose_map_forget_local (G₁ := G₁) (G₂ := G₂) φ S.f]
      rw [finiteRep_precompose_map_forget_local (G₁ := G₁) (G₂ := G₂) φ S.g]
      ext x
      have hzero :=
        LinearMap.congr_fun
          (congrArg
            (fun m => m.hom.toLinearMap)
            ((S.map (forget₂ (FDRep k G₁) (Rep k G₁))).zero)) x
      simpa using hzero)

/-- Helper for Theorem 18-18.3-1: precomposing a short exact sequence of finite-dimensional
representations with `φ : B →* A` keeps it short exact because only the group action changes. -/
private theorem finiteRepGrothendieckPrecompose_shortExact_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁)
    (S : ShortComplex (FDRep k G₁)) (hS : S.ShortExact) :
    (finiteRepGrothendieckPrecompose_shortComplex_local (G₁ := G₁) (G₂ := G₂) φ S).ShortExact := by
  let F : FDRep k G₁ ⥤ ModuleCat k :=
    (forget₂ (FDRep k G₁) (Rep k G₁)) ⋙ (forget₂ (Rep k G₁) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat k` exposes the unchanged linear maps of the original short exact
    -- sequence.
    simpa [F] using hS.map_of_exact F
  let fA : S.X₁ →ₗ[k] S.X₂ := (((forget₂ (FDRep k G₁) (Rep k G₁)).map S.f).hom.toLinearMap)
  let gA : S.X₂ →ₗ[k] S.X₃ := (((forget₂ (FDRep k G₁) (Rep k G₁)).map S.g).hom.toLinearMap)
  have hExact : Function.Exact fA gA := by
    -- On underlying `k`-modules, `S` is exact.
    simpa [F, fA, gA] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hInj : Function.Injective fA := by
    -- The left map stays injective after forgetting to modules.
    simpa [F, fA] using hSF.moduleCat_injective_f
  have hSurj : Function.Surjective gA := by
    -- The right map stays surjective after the same forgetful step.
    simpa [F, gA] using hSF.moduleCat_surjective_g
  let TRep : ShortComplex (Rep k G₂) :=
    (finiteRepGrothendieckPrecompose_shortComplex_local (G₁ := G₁) (G₂ := G₂) φ S).map
      (forget₂ (FDRep k G₂) (Rep k G₂))
  have hRepMap : (TRep.map (forget₂ (Rep k G₂) (ModuleCat k))).ShortExact := by
    -- After precomposition, the underlying module short complex uses the same linear maps, so the
    -- exactness/injectivity/surjectivity data transfers unchanged.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (TRep.map (forget₂ (Rep k G₂) (ModuleCat k)))).2 <| by
            simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
              finiteRep_precompose_map_local, fA, gA] using hExact
    · rw [ModuleCat.mono_iff_injective]
      simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
        finiteRep_precompose_map_local, fA] using hInj
    · rw [ModuleCat.epi_iff_surjective]
      simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
        finiteRep_precompose_map_local, gA] using hSurj
  have hRepShort : TRep.ShortExact := by
    -- Reflect short exactness from `ModuleCat k` back to `Rep k B`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := TRep) (F := forget₂ (Rep k G₂) (ModuleCat k))).1 hRepMap
  have hTRep :
      ((finiteRepGrothendieckPrecompose_shortComplex_local
          (G₁ := G₁) (G₂ := G₂) φ S).map
        (forget₂ (FDRep k G₂) (Rep k G₂))).ShortExact := by
    -- The explicit `Rep` short complex is definitionally the image of the `FDRep` one.
    simpa [TRep] using hRepShort
  -- Reflect once more from `Rep k B` back to `FDRep k B`.
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := finiteRepGrothendieckPrecompose_shortComplex_local
        (G₁ := G₁) (G₂ := G₂) φ S)
      (F := forget₂ (FDRep k G₂) (Rep k G₂))).1 hTRep

/-- Helper for Theorem 18-18.3-1: pulling back along a monoid hom preserves the defining
Grothendieck relations because it preserves short exact sequences on the unchanged underlying
vector-space carriers. -/
private theorem finiteRepGrothendieckRelations_le_precomposeLift_ker_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁) :
    finiteRepGrothendieckRelations k G₁ ≤
      (finiteRepGrothendieckPrecomposeLiftLocal φ).ker := by
  -- Evaluate the precomposition lift on each defining short-exact-sequence generator.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  have hPre :
      (finiteRepGrothendieckPrecompose_shortComplex_local
        (G₁ := G₁) (G₂ := G₂) φ S).ShortExact :=
    finiteRepGrothendieckPrecompose_shortExact_local
      (G₁ := G₁) (G₂ := G₂) φ S hS
  have hRelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G₂)
      (finiteRepGrothendieckPrecompose_shortComplex_local
        (G₁ := G₁) (G₂ := G₂) φ S) hPre
  -- The free lift rewrites the defining relation to the corresponding relation in the pulled-back
  -- short exact sequence over `B`.
  change
    finiteRepGrothendieckPrecomposeLiftLocal φ
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  change
    [FDRep.of (S.X₂.ρ.comp φ)]₀ -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ = 0
  calc
    [FDRep.of (S.X₂.ρ.comp φ)]₀ -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ =
      ([FDRep.of (S.X₁.ρ.comp φ)]₀ + [FDRep.of (S.X₃.ρ.comp φ)]₀) -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ := by
          rw [hRelation]
    _ = 0 := by
          abel

/-- Helper for Theorem 18-18.3-1: pull back LinearRepresentations_Serre_1977's Grothendieck classes along a group
homomorphism. -/
private def finiteRepGrothendieckPrecomposeLocal
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁) :
    R₀[k](G₁) →+ R₀[k](G₂) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G₁)
    (finiteRepGrothendieckPrecomposeLiftLocal φ)
    (finiteRepGrothendieckRelations_le_precomposeLift_ker_local φ)

/-- Helper for Theorem 18-18.3-1: the pullback map on `R₀` sends a generator class to the class of
the pulled-back representation. -/
@[simp] private theorem finiteRepGrothendieckPrecompose_apply_class_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁) (V : FDRep k G₁) :
    finiteRepGrothendieckPrecomposeLocal φ [V]₀ =
      [FDRep.of (V.ρ.comp φ)]₀ := by
  rfl

/-- Helper for Theorem 18-18.3-1: pulling back the trivial class stays trivial. -/
@[simp] private theorem finiteRepGrothendieckPrecompose_trivial_class_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂] (φ : G₂ →* G₁) :
    finiteRepGrothendieckPrecomposeLocal φ
        (([𝟙_ (FDRep k G₁)]₀ : R₀[k](G₁))) =
      ([𝟙_ (FDRep k G₂)]₀ : R₀[k](G₂)) := by
  rw [finiteRepGrothendieckPrecompose_apply_class_local]
  rfl

/-- Helper for Theorem 18-18.3-1: precomposing a representation with a group equivalence preserves
irreducibility over the coefficient field. -/
private theorem isIrreducible_comp_of_mulEquiv_local
    {G₁ : Type u} [Group G₁] {G₂ : Type u} [Group G₂]
    {V : Type u} [AddCommGroup V] [Module k V]
    (e : G₁ ≃* G₂) (σ : Representation k G₂ V)
    [Representation.IsIrreducible σ] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport subrepresentations across the group equivalence and reuse irreducibility of `σ`.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro b x hx
        simpa using W.apply_mem_toSubmodule (e.symm b) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Theorem 18-18.3-1: the source of a projective envelope of a simple module is
cyclic, hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    {S : Type u} [Group S] {P M : Type u} [AddCommGroup P] [Module k[S] P]
    [AddCommGroup M] [Module k[S] M] [IsSimpleModule k[S] M]
    {f : P →ₗ[k[S]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[S] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[S]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[S] P := Submodule.span k[S] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero element of the simple target.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[S] P x) := by
    -- Once the cyclic span is all of `P`, the canonical map from `k[S]` is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[S]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[S] P x) hsurj

/-- Helper for Theorem 18-18.3-1: every simple finite-dimensional `k[S]`-representation admits a
finite projective envelope inside the canonical projective-owner category. -/
private theorem exists_finite_projective_envelope_of_simple_local
    {S : Type u} [Group S] [Finite S]
    (U : FDRep k S) [Simple U] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k S,
      ∃ f : P.V →ₗ[k[S]] asModule U.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k S U := U.ρ
  letI : Module k[S] U := by
    -- Expose the ambient `k[S]`-module structure carried by the owner `U`.
    simpa [ρ] using (inferInstance : Module k[S] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity of `U` implies irreducibility of its bundled representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple U)
  letI : IsSimpleModule k[S] U := by
    -- The projective-envelope owner theorem is stated for `k[S]`-modules.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[S] := ModuleCat.of k[S] U
  let _ : Module.Finite k k[S] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[S] := IsArtinianRing.of_finite k k[S]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[S] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (S := S) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[S] := by
    -- Repackage the envelope source as a finite projective owner.
    refine ⟨P', ?_⟩
    change Module.Finite k[S] P'
    exact hfinite
  have hproj : Module.Projective k[S] Pfg := by
    -- Projectivity is already part of the envelope source structure.
    change Module.Projective k[S] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k S := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Theorem 18-18.3-1: once `p ∤ |S|`, the source of a projective envelope already has
the same Grothendieck class as its target, because Maschke makes the target projective. -/
private theorem projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p_local
    {S : Type u} [Group S] [Finite S]
    (hS : ¬ p ∣ Nat.card S)
    {π : FDRep k S}
    {P : FiniteProjectiveGroupAlgebraModule k S}
    {f : P.V →ₗ[k[S]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    [P.toFiniteRep]₀ = [π]₀ := by
  -- Route correction: replay the Chapter `15` Maschke argument locally instead of importing the
  -- aggregate proposition file. The source route is unchanged: the target module is projective
  -- because `p ∤ |S|`, so a projective envelope is already isomorphic to the target.
  let M : ModuleCat k[S] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k S) (Rep k S)).obj π)
  have hM_projective : Module.Projective k[S] M := by
    -- Maschke's theorem makes the group algebra semisimple in the prime-to-`p` case.
    let _ : Fintype S := Fintype.ofFinite S
    let _ : NeZero (Nat.card S : k) := NeZero.of_not_dvd k hS
    let _ : IsSemisimpleRing k[S] := by
      infer_instance
    exact Module.projective_of_isSemisimpleRing k[S] M
  let _ : Module.Projective k[S] M := hM_projective
  let f' : P.V →ₗ[k[S]] M := by
    -- The target module is just `π` viewed through its canonical `ModuleCat` owner.
    simpa using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The projective-envelope structure is definitionally unchanged by the rebundling.
    simpa [f'] using hf
  obtain ⟨eLin⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k S) (Rep k S)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k S) (Rep k S)).obj π)).symm
  let eRep : ((forget₂ (FDRep k S) (Rep k S)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k S) (Rep k S)).obj π) := by
    -- Forgetting `P.toFiniteRep` returns the same `Rep` object as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  let e : P.toFiniteRep ≅ π :=
    ⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
      (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv,
      by
        apply (forget₂ (FDRep k S) (Rep k S)).map_injective
        change eRep.hom ≫ eRep.inv = 𝟙 _
        exact eRep.hom_inv_id,
      by
        apply (forget₂ (FDRep k S) (Rep k S)).map_injective
        change eRep.inv ≫ eRep.hom = 𝟙 _
        exact eRep.inv_hom_id⟩
  -- Isomorphic finite-dimensional owners define the same class in `R₀[k](S)`.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := S) ⟨e⟩

/-- Helper for Theorem 18-18.3-1: on the prime-to-`p` factor, a simple class comes from a
concrete finite projective owner, not only abstractly from the Cartan range. -/
private theorem exists_projective_owner_of_simple_of_order_prime_to_p_local
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ Q : FiniteProjectiveGroupAlgebraModule k S, cartanHom k S [Q]ₚ₀ = [U]₀ := by
  have hS_not_dvd : ¬ p ∣ Nat.card S :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hS
  obtain ⟨Q, f, hf⟩ := exists_finite_projective_envelope_of_simple_local (U := U)
  refine ⟨Q, ?_⟩
  -- Maschke makes the target itself projective, so the projective envelope already has the same
  -- Grothendieck class as the simple target.
  calc
    cartanHom k S [Q]ₚ₀ = [Q.toFiniteRep]₀ := by
      exact cartanHom_projectiveClass_eq k S Q
    _ = [U]₀ := by
      simpa using
        (projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p_local
          (p := p) (S := S) hS_not_dvd (π := U) (P := Q) (f := f) hf)

/-- Helper for Theorem 18-18.3-1: on a simple representation of `S × P`, the right `p`-group
factor acts trivially. -/
private theorem simple_right_factor_isTrivial_of_isPGroup_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) (τ : FDRep k (S × P)) [Simple τ] :
    Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := by
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
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
  letI : Representation.IsTrivial (τ.ρ.comp N.subtype) :=
    isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
      (p := p) (ρ := τ.ρ) N hN_p
  -- Evaluate the normal-subgroup triviality on the explicit right-axis elements.
  refine ⟨fun p' ↦ ?_⟩
  ext x
  let n : N := ⟨(1, p'), by
    show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
    exact ⟨by simp, by simp⟩⟩
  change ((τ.ρ.comp N.subtype) n) x = x
  exact isTrivial_apply (τ.ρ.comp N.subtype) n x

/-- Helper for Theorem 18-18.3-1: if the right factor acts trivially, the whole `S × P`-action
inflates from the left factor along `fst`. -/
private theorem representation_eq_comp_inl_comp_fst_of_trivial_right_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k (S × P) V)
    (hTriv : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P))) :
    ρ = (ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P) := by
  letI : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P)) := hTriv
  ext g x
  rcases g with ⟨s, p'⟩
  calc
    ρ (s, p') x = ρ ((s, 1) * (1, p')) x := by simp
    _ = ρ (s, 1) (ρ (1, p') x) := by
          rw [map_mul]
          rfl
    _ = ρ (s, 1) x := by
          have hp' : ρ (1, p') x = x := by
            change ((ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (ρ.comp (MonoidHom.inr S P)) p' x
          simp [hp']
    _ = ((ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P)) (s, p') x := rfl

/-- Helper for Theorem 18-18.3-1: after killing the right `p`-group factor, a simple
`S × P`-representation comes from an irreducible left-factor representation. -/
private theorem split_product_simple_factorization_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    (τ : FDRep k (S × P)) [Simple τ]
    (hTriv : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P))) :
    ∃ ρS : Representation k S τ, Representation.IsIrreducible ρS ∧
      τ.ρ = ρS.comp (MonoidHom.fst S P) := by
  let ρS : Representation k S τ := τ.ρ.comp (MonoidHom.inl S P)
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  letI : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := hTriv
  have hρS_irreducible : Representation.IsIrreducible ρS := by
    classical
    -- Pull a nonzero `ρS`-subrepresentation back to an `S × P`-stable subrepresentation of `τ`.
    letI : Nontrivial (Subrepresentation ρS) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro hbot
      have hbot' : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        simpa [ρS] using congrArg Subrepresentation.toSubmodule hbot
      exact IsSimpleOrder.bot_ne_top hbot'
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro W hW
    let W' : Subrepresentation τ.ρ :=
      { toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          rcases g with ⟨s, p'⟩
          have hp' : τ.ρ (1, p') x = x := by
            change ((τ.ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (τ.ρ.comp (MonoidHom.inr S P)) p' x
          have hact : τ.ρ (s, p') x = ρS s x := by
            calc
              τ.ρ (s, p') x = τ.ρ ((s, 1) * (1, p')) x := by simp
              _ = τ.ρ (s, 1) (τ.ρ (1, p') x) := by
                    rw [map_mul]
                    rfl
              _ = τ.ρ (s, 1) x := by simp [hp']
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
  -- The triviality of the right factor identifies the full action with inflation from `S`.
  refine ⟨ρS, hρS_irreducible, ?_⟩
  exact representation_eq_comp_inl_comp_fst_of_trivial_right_local τ.ρ hTriv

/-- Helper for Theorem 18-18.3-1: for a simple class on an elementary subgroup, LinearRepresentations_Serre_1977's `S × P`
decomposition directly produces the local Cartan witness of size `ordProj[p] |H|`. -/
private theorem simple_class_ordProj_nsmul_mem_cartan_range_of_elementary_local
    (H : Subgroup G) (hH : IsElementary H)
    (τ : FDRep k H) [Simple τ] :
    ((ordProj[p] (Nat.card H) : ℕ) • [τ]₀) ∈ (cartanHom k H).range := by
  let n : ℕ := Nat.factorization (Nat.card H) p
  let m : ℕ := ordCompl[p] (Nat.card H)
  have hcard : Nat.card H = p ^ n * m := by
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p).symm
  have hm : Nat.Coprime p m := by
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hord : ordProj[p] (Nat.card H) = p ^ n :=
    ordProj_card_eq_p_pow_of_card_factorization
      (p := p) (G := H) n m hcard hm
  rw [hord]
  simpa [n, m] using
    (Representation.cartanHom_surjective_on_p_part_multiples
      (p := p) n m hcard hm [τ]₀)

/-- Helper for Theorem 18-18.3-1: on an elementary subgroup, the `p`-part of the subgroup order
times any modular class belongs to the local Cartan image. -/
private theorem elementary_ordProj_nsmul_mem_cartan_range_local
    (H : Subgroup G) (hH : IsElementary H) (y : R₀[k](H)) :
    ((ordProj[p] (Nat.card H) : ℕ) • y) ∈ (cartanHom k H).range := by
  let n : ℕ := Nat.factorization (Nat.card H) p
  let m : ℕ := ordCompl[p] (Nat.card H)
  have hcard : Nat.card H = p ^ n * m := by
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p).symm
  have hm : Nat.Coprime p m := by
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hord : ordProj[p] (Nat.card H) = p ^ n :=
    ordProj_card_eq_p_pow_of_card_factorization
      (p := p) (G := H) n m hcard hm
  rw [hord]
  simpa [n, m] using
    (Representation.cartanHom_surjective_on_p_part_multiples
      (p := p) n m hcard hm y)

/-- Helper for Theorem 18-18.3-1: a local Cartan witness on a subgroup stays a Cartan witness
after applying subgroup induction to both the projective source and the finite-dimensional class. -/
private theorem subgroup_induction_nsmul_mem_cartan_range_local
    (H : Subgroup G) (N : ℕ) (z : R₀[k](H))
    (hlocal : ((N : ℕ) • z) ∈ (cartanHom k H).range) :
    ((N : ℕ) • finiteRep_subgroupInduction (G := G) H z) ∈
      (cartanHom k G).range := by
  rcases hlocal with ⟨x, hx⟩
  refine ⟨projective_subgroupInduction (G := G) H x, ?_⟩
  -- Commute Cartan with subgroup induction, then rewrite the chosen local witness.
  calc
    cartanHom k G (projective_subgroupInduction (G := G) H x)
        =
          finiteRep_subgroupInduction (G := G) H (cartanHom k H x) := by
            rw [cartanHom_subgroupInduction_eq_subgroupInduction_cartanHom]
    _ =
        finiteRep_subgroupInduction (G := G) H ((N : ℕ) • z) := by
          rw [hx]
    _ =
        ((N : ℕ) • finiteRep_subgroupInduction (G := G) H z) := by
          rw [map_nsmul]

/-- Helper for Theorem 18-18.3-1: after the source-faithful elementary decomposition, LinearRepresentations_Serre_1977's
argument assembles the local Cartan witnesses into a global `p ^ n` witness on `G`. -/
private theorem p_part_nsmul_mem_cartan_range_of_card_factorization_local
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m)
    (y : R₀[k](G)) :
    ((p ^ n : ℕ) • y) ∈ (cartanHom k G).range := by
  simpa using
    (Representation.cartanHom_surjective_on_p_part_multiples
      (p := p) n m hcard hm y)

/-- Helper for Theorem 18-18.3-1: if `Nat.card G = p ^ n * m` with `m` prime to `p`, then every
element of `R₀[k](G)` divisible by `p ^ n` lies in the image of the Cartan homomorphism. -/
private theorem cartanHom_surjective_on_p_part_multiples_local
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m)
    (y : R₀[k](G)) :
    (p ^ n) • y ∈ (cartanHom k G).range := by
  simpa using
    (Representation.cartanHom_surjective_on_p_part_multiples
      (p := p) n m hcard hm y)

/-- Helper for Theorem 18-18.3-1: descend the generator-level modular character to the free
abelian group on finite-dimensional `k[G]`-representations, keeping the Chapter `18.3`
Grothendieck route local to this file. -/
private abbrev virtualModularCharacterLiftLocal
    (lift : PrimeToPRoot p k → K) :
    FreeAbelianGroup (FDRep k G) →+ ({ s : G // IsPRegular p s } → K) :=
  FreeAbelianGroup.lift fun E ↦ modularCharacter lift E.ρ

/-- Helper for Theorem 18-18.3-1: the standard Grothendieck relations already vanish under the
local modular-character lift, so the lift descends to `R₀[k](G)`. -/
private theorem finiteRepGrothendieckRelations_le_virtualModularCharacterLiftLocal_ker
    (lift : PrimeToPRoot p k → K) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterLiftLocal (p := p) (K := K) (G := G) lift).ker := by
  -- Route correction: replace the broken import edge to `Remark_18_18_1_3` with the same
  -- Grothendieck-descent construction inside this theorem file, so the Cartan/projective proof
  -- keeps the original source route while avoiding the missing compiled artifact.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change virtualModularCharacterLiftLocal (p := p) (K := K) (G := G) lift
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext s
  -- The short-exact-sequence generator dies by modular-character additivity.
  have hchar :
      φ[lift](S.X₂.ρ) s = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s :=
    modularCharacter_add_of_shortExactSequence (p := p) (lift := lift) S hS s
  simpa [virtualModularCharacterLiftLocal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using sub_eq_zero.mpr hchar

/-- Helper for Theorem 18-18.3-1: the modular character extends additively to a virtual modular
character on `R₀[k](G)`, stated locally to avoid the broken remark import. -/
private def virtualModularCharacterLocal
    (lift : PrimeToPRoot p k → K) :
    R₀[k](G) →+ ({ s : G // IsPRegular p s } → K) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterLiftLocal (p := p) (K := K) (G := G) lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterLiftLocal_ker
      (p := p) (K := K) (G := G) lift)

/-- Helper for Theorem 18-18.3-1: on an honest representation class, the local virtual modular
character recovers the original modular character. -/
@[simp] private theorem virtualModularCharacterLocal_class
    (lift : PrimeToPRoot p k → K) (E : FDRep k G) :
    virtualModularCharacterLocal (p := p) (K := K) (G := G) lift [E]₀ =
      modularCharacter lift E.ρ := by
  -- The quotient lift was defined from the generator-level modular character.
  simp [virtualModularCharacterLocal, virtualModularCharacterLiftLocal,
    finiteRepGrothendieckClass]

/-- Helper for Theorem 18-18.3-1: reducing an ordinary virtual character and then evaluating its
Brauer character on the `p`-regular locus agrees with restricting the original ordinary character
to the `p`-regular subtype. -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_local
    (lift : PrimeToPRoot p k →* Kˣ) (y : R₀[K](G)) :
    virtualModularCharacterLocal (p := p) (K := K) (G := G)
        (PrimeToPRoot.toFieldLift lift) (decompositionHom A K G y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · ext s
    simp
  · intro E
    obtain ⟨L⟩ := Representation.exists_stableLattice A E.ρ
    ext s
    change
      (virtualModularCharacterLocal (p := p) (K := K) (G := G)
          (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) [E]₀)) s =
        ((finiteRepGrothendieckCharacter K G [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) E L,
      virtualModularCharacterLocal_class, finiteRepGrothendieckCharacter_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := A) (K := K) (G := G) lift E.ρ L s)
  · intro a ha
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

/-- Helper for Theorem 18-18.3-1: if a projective class maps under the Cartan homomorphism to the
`p`-part multiple of `[E]₀`, then its scalar extension decomposes back to that same multiple. -/
private theorem decomposition_projective_scalar_extension_eq_p_part_multiple
    (E : FDRep k G) (P : P_k(G))
    (hP : cartanHom k G P = (pPartCardG : ℕ) • [E]₀) :
    decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) P) =
      (pPartCardG : ℕ) • [E]₀ := by
  -- Reprove LinearRepresentations_Serre_1977's `d ∘ e = c` bridge locally by induction on projective classes, using the
  -- literal stable lattice on an actual projective lift in the generator case.
  have htriangle :
      ∀ x : P_k(G),
        decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) x) =
          cartanHom k G x := by
    intro x
    refine QuotientAddGroup.induction_on x ?_
    intro a
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · simp
    · intro Q
      obtain ⟨Qlift, hQlift⟩ :=
        exists_projective_lift_of_residueField_projective (A := A) (G := G) Q
      have hQclass :
          [Qlift.residueFieldReduction]ₚ₀ = [Q]ₚ₀ := by
        exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
          (A := k) (G := G) hQlift
      have hred_lift :
          projectiveGrothendieckReductionEquiv (A := A) (G := G) [Qlift]ₚ₀ =
            [Qlift.residueFieldReduction]ₚ₀ := by
        change projectiveGrothendieckReductionHom (A := A) (G := G) [Qlift]ₚ₀ =
          [Qlift.residueFieldReduction]ₚ₀
        simpa using projectiveGrothendieckReductionHom_projectiveClass_eq
          (A := A) (G := G) Qlift
      have hred :
          projectiveGrothendieckReductionEquiv (A := A) (G := G) [Qlift]ₚ₀ = [Q]ₚ₀ := by
        rw [hred_lift, hQclass]
      have hsymm :
          (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [Q]ₚ₀ = [Qlift]ₚ₀ := by
        exact
          (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred.symm
      obtain ⟨L, hL⟩ :=
        projective_scalarExtension_literal_reduction_class_support
          (A := A) (K := K) (G := G) Qlift
      calc
        decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) [Q]ₚ₀) =
            decompositionHom A K G [Qlift.scalarExtension K]₀ := by
              rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm,
                projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
        _ = [FDRep.of L.reductionRepresentation]₀ := by
              sorry
        _ = [Qlift.residueFieldReduction.toFiniteRep]₀ := hL
        _ = cartanHom k G [Qlift.residueFieldReduction]ₚ₀ := by
              symm
              simpa using (cartanHom_projectiveClass_eq k G Qlift.residueFieldReduction)
        _ = cartanHom k G [Q]ₚ₀ := by
              rw [← hQclass]
    · intro a ha
      simpa [map_neg] using congrArg Neg.neg ha
    · intro a b ha hb
      simp [map_add, ha, hb]
  calc
    decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) P) =
        cartanHom k G P := htriangle P
    _ = (pPartCardG : ℕ) • [E]₀ := hP

/-- Helper for Theorem 18-18.3-1: ordinary characters coming from projective scalar extension
vanish on `p`-singular elements. -/
private theorem projectiveLiftCharacter_eq_zero_on_pSingular_local
    (Q : FiniteProjectiveGroupAlgebraModule k G) (g : G) (hg : ¬ IsPRegular p g) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter Q
        (projectiveGrothendieckScalarExtensionHom A K) g = 0 := by
  sorry

private theorem finiteRepGrothendieckCharacter_projective_scalar_extension_eq_zero_on_pSingular
    (P : P_k(G)) (g : G) (hg : ¬ IsPRegular p g) :
    ((finiteRepGrothendieckCharacter K G
        ((projectiveGrothendieckScalarExtensionHom A K) P)) : G → K) g = 0 := by
  refine QuotientAddGroup.induction_on P ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro Q
    change
      FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter Q
        (projectiveGrothendieckScalarExtensionHom A K) g = 0
    exact projectiveLiftCharacter_eq_zero_on_pSingular_local
      (p := p) (A := A) (K := K) (G := G) Q g hg
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add, ha, hb] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Theorem 18-18.3-1: on a `p`-regular element, the zero extension of the modular
character agrees with the virtual modular character of the original class. -/
private theorem modularCharacterZeroExtension_eq_virtualModularCharacter_of_isPRegular
    (lift : PrimeToPRoot p k →* Kˣ) (E : FDRep k G) {g : G} (hg : IsPRegular p g) :
    FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) g =
      virtualModularCharacterLocal (p := p) (K := K) (G := G)
        (PrimeToPRoot.toFieldLift lift) [E]₀ ⟨g, hg⟩ := by
  -- On the regular locus, the zero extension is defined by the original modular character class.
  rw [virtualModularCharacterLocal_class]
  rw [FDRep.modularCharacterZeroExtension, dif_pos hg]
  rfl

/-- Helper for Theorem 18-18.3-1: on a `p`-singular element, every `pPartCardG`-multiple of the
zero-extended modular character still vanishes. -/
private theorem nsmul_modularCharacterZeroExtension_eq_zero_of_not_isPRegular_local
    (lift : PrimeToPRoot p k →* Kˣ) (E : FDRep k G) {g : G} (hg : ¬ IsPRegular p g) :
    ((pPartCardG : ℕ) •
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)) g = 0 := by
  -- The zero extension is already zero away from the `p`-regular locus, so every natural-number
  -- scalar multiple vanishes there as well.
  simp [FDRep.modularCharacterZeroExtension, hg]

/-- Helper for Theorem 18-18.3-1: a class function agreeing with the `p`-part multiple of the
zero-extended modular character on the `p`-regular locus and vanishing on the `p`-singular locus
is exactly that multiple of the zero extension. -/
private theorem nsmul_modularCharacterZeroExtension_eq_of_regular_singular_local
    (lift : PrimeToPRoot p k →* Kˣ) (E : FDRep k G) (χ : R[K](G))
    (hregular :
      virtualModularCharacterLocal (p := p) (K := K) (G := G)
          (PrimeToPRoot.toFieldLift lift) ((pPartCardG : ℕ) • [E]₀) =
        (χ : G → K) ∘ Subtype.val)
    (hsingular : ∀ g : G, ¬ IsPRegular p g → (χ : G → K) g = 0) :
    ((pPartCardG : ℕ) •
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)) =
        (χ : G → K) := by
  -- Compare the two class functions pointwise, using the regular-locus identification and the
  -- singular-locus vanishing separately.
  funext g
  by_cases hg : IsPRegular p g
  · have hregular' :
        (pPartCardG : ℕ) •
            virtualModularCharacterLocal (p := p) (K := K) (G := G)
              (PrimeToPRoot.toFieldLift lift) [E]₀ ⟨g, hg⟩ =
          (χ : G → K) g := by
      have hregular₀ :
          virtualModularCharacterLocal (p := p) (K := K) (G := G)
              (PrimeToPRoot.toFieldLift lift) ((pPartCardG : ℕ) • [E]₀) ⟨g, hg⟩ =
            (χ : G → K) g := congrFun hregular ⟨g, hg⟩
      rw [map_nsmul] at hregular₀
      simpa [Pi.smul_apply, virtualModularCharacterLocal_class] using hregular₀
    simpa [modularCharacterZeroExtension_eq_virtualModularCharacter_of_isPRegular
      (p := p) (A := A) (K := K) (G := G) lift E hg] using hregular'
  · -- On the singular locus, the zero extension is definitionally zero and `χ` vanishes by
    -- hypothesis.
    calc
      ((pPartCardG : ℕ) •
          FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)) g = 0 := by
            exact
              nsmul_modularCharacterZeroExtension_eq_zero_of_not_isPRegular_local
                (p := p) (A := A) (K := K) (G := G) lift E hg
      _ = (χ : G → K) g := by
            symm
            exact hsingular g hg

/-- Theorem 18-18.3-1: if `p ^ Nat.factorization (Nat.card G) p` is the largest power of `p`
dividing `|G|`, then for every modular character `φ` of a finite-dimensional
`k[G]`-module `E`, with `k = IsLocalRing.ResidueField A` and values defined using a chosen
multiplicative lift `lift : PrimeToPRoot p k →* Kˣ`, the class function on `G` that equals the
integral multiple `(p ^ Nat.factorization (Nat.card G) p : ℤ) • φ` on the `p`-regular elements
and `0` on the
`p`-singular elements is a virtual character of `G`, realized here as an element of `R[K](G)`. -/
theorem p_part_zeroExtension_modularCharacter_mem_characterRingOverField
    (lift : PrimeToPRoot p k →* Kˣ) (E : FDRep k G) :
    ((pPartCardG : ℤ) •
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)) ∈ R[K](G) := by
  -- Route correction: follow LinearRepresentations_Serre_1977's Cartan/projective route directly. First realize the
  -- `p`-part multiple of `[E]₀` in the Cartan image, then compare on the regular locus and use
  -- projective vanishing on the singular locus.
  let n : ℕ := Nat.factorization (Nat.card G) p
  let m : ℕ := ordCompl[p] (Nat.card G)
  have hcard : Nat.card G = p ^ n * m := by
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hm : Nat.Coprime p m := by
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hcartan :
      (pPartCardG : ℕ) • [E]₀ ∈ (cartanHom k G).range := by
    change
      (p ^ Nat.factorization (Nat.card G) p : ℕ) • [E]₀ ∈ (cartanHom k G).range
    simpa [n] using
      cartanHom_surjective_on_p_part_multiples_local
        (p := p) (G := G) n m hcard hm [E]₀
  rcases hcartan with ⟨P, hP⟩
  let y : R₀[K](G) := (projectiveGrothendieckScalarExtensionHom A K) P
  let χ : R[K](G) := finiteRepGrothendieckCharacter K G y
  have hy_decomp :
      decompositionHom A K G y = (pPartCardG : ℕ) • [E]₀ := by
    -- Apply the Cartan-image helper to the chosen projective witness `P`.
    change decompositionHom A K G y =
      (p ^ Nat.factorization (Nat.card G) p : ℕ) • [E]₀
    simpa [y, n] using
      decomposition_projective_scalar_extension_eq_p_part_multiple
        (p := p) (A := A) (K := K) (G := G) E P hP
  have hregular :
      virtualModularCharacterLocal (p := p) (K := K) (G := G)
          (PrimeToPRoot.toFieldLift lift) ((pPartCardG : ℕ) • [E]₀) =
        (χ : G → K) ∘ Subtype.val := by
    -- Rewrite through the chosen scalar-extended projective class, then invoke the Grothendieck
    -- comparison on the `p`-regular locus.
    rw [← hy_decomp]
    simpa [χ, y] using
      virtualModularCharacter_decomposition_eq_character_restriction_local
        (p := p) (A := A) (K := K) (G := G) lift y
  have hsingular :
      ∀ g : G, ¬ IsPRegular p g → (χ : G → K) g = 0 := by
    intro g hg
    -- The ordinary character `χ` comes from projective scalar extension, so it vanishes on
    -- `p`-singular elements.
    simpa [χ, y] using
      finiteRepGrothendieckCharacter_projective_scalar_extension_eq_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) P g hg
  have hχ_nat :
      ((pPartCardG : ℕ) • FDRep.modularCharacterZeroExtension E
          (PrimeToPRoot.toFieldLift lift)) =
        (χ : G → K) := by
    -- The regular/singular comparison has been isolated as a dedicated local helper.
    exact
      nsmul_modularCharacterZeroExtension_eq_of_regular_singular_local
        (p := p) (A := A) (K := K) (G := G) lift E χ hregular hsingular
  have hχ :
      ((pPartCardG : ℤ) • FDRep.modularCharacterZeroExtension E
          (PrimeToPRoot.toFieldLift lift)) =
        (χ : G → K) := by
    simpa using hχ_nat
  simpa [hχ] using χ.property

end

end Representation
