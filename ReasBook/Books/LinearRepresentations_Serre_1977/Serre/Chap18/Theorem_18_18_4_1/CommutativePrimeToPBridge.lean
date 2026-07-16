import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_4_1.CharacterTransformCore

noncomputable section

open CategoryTheory
open scoped Representation IsMulCommutative

universe u

namespace Representation

section CharacterRingLift

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K] [CharZero K]

/-- Helper for Theorem 18-18.4-1: a one-dimensional representation over `k` is afforded by a
unit-valued linear character. -/
private theorem representation_character_eq_unit_character_of_finrank_one
    {H : Type u} [Group H] {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) [FiniteDimensional k V]
    (hdim : Module.finrank k V = 1) :
    ∃ α : H →* kˣ, ρ.character = (oneDimensionalRepresentation α).character := by
  let scalarEquiv : k ≃ₗ[k] (V →ₗ[k] V) := LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : k) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let α₀ : H → k := fun g ↦ scalarEquiv.symm (ρ g)
  have hα₀_eq (g : H) : ρ g = α₀ g • LinearMap.id := by
    calc
      ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    have hscalar1 : scalarEquiv (1 : k) = (1 : V →ₗ[k] V) := by
      simpa using hscalar (1 : k)
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[k] V) := by
        simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hα₀_mul (g h : H) : α₀ (g * h) = α₀ g * α₀ h := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = ρ (g * h) := by
        simp [α₀]
      _ = ρ g * ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext v
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : H) : α₀ g ≠ 0 := by
    have hpos : 0 < Module.finrank k V := by
      simpa [hdim]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ g = 0 := by
      simp [hα₀_eq, hzero]
    have hmul : ρ g * ρ g⁻¹ = (1 : V →ₗ[k] V) := by
      simpa using (ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[k] V) = 0 := by
      calc
        (1 : V →ₗ[k] V) = ρ g * ρ g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : H →* kˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        simpa using hα₀_one
      map_mul' g h := by
        ext
        simpa using hα₀_mul g h }
  refine ⟨α, ?_⟩
  ext g
  rw [Representation.character, oneDimensionalRepresentation_character_apply]
  let b := Module.Free.chooseBasis k V
  rw [LinearMap.trace_eq_matrix_trace k b]
  have hmatrix :
      LinearMap.toMatrix b b (ρ g) = Matrix.diagonal fun _ ↦ α₀ g := by
    rw [hα₀_eq]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex k V) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex k V, hdim]
  rw [hmatrix]
  simp [Matrix.trace, hcard, α]

omit [IsAlgClosed k] in
/-- Helper for Theorem 18-18.4-1: a one-dimensional unit-valued representation is irreducible. -/
private theorem oneDimensionalRepresentation_isIrreducible
    {H : Type u} [Group H] (β : H →* kˣ) :
    (oneDimensionalRepresentation β).IsIrreducible := by
  have hfinrank : Module.finrank k k = 1 := by
    simp
  letI : Nontrivial (Subrepresentation (oneDimensionalRepresentation β)) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule k k) :=
    (isSimpleModule_iff k k).1 ((isSimpleModule_iff_finrank_eq_one).2 hfinrank)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact (hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)).elim
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Theorem 18-18.4-1: a simple module over a finite commutative group is equivariantly
isomorphic to a one-dimensional unit-valued character representation. -/
private theorem simple_commutative_representation_iso_one_dimensional_local
    {H : Type u} [Group H] [Finite H] [IsMulCommutative H]
    (S : FDRep k H) [Simple S] :
    ∃ α : H →* kˣ,
      Nonempty (Representation.Equiv S.ρ (oneDimensionalRepresentation α)) := by
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hdimS : Module.finrank k S = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative S.ρ
  let e : S ≃ₗ[k] k := LinearEquiv.ofFinrankEq S k (by simpa using hdimS)
  let ρk : Representation k H k :=
    { toFun := fun h ↦ e.toLinearMap.comp (S.ρ h) |>.comp e.symm.toLinearMap
      map_one' := by
        apply LinearMap.ext
        intro y
        simp [LinearMap.comp_assoc, e]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro y
        simp [LinearMap.comp_assoc, e] }
  have hρk_scalar (h : H) (x : k) : ρk h x = x * ρk h 1 := by
    calc
      ρk h x = ρk h (x • (1 : k)) := by simp
      _ = x • ρk h 1 := by rw [LinearMap.map_smul]
      _ = x * ρk h 1 := by simp [mul_comm]
  have hρk_ne_zero (h : H) : ρk h 1 ≠ 0 := by
    intro hzero
    have hzeroMap : ρk h = 0 := by
      apply LinearMap.ext
      intro y
      calc
        ρk h y = y * ρk h 1 := hρk_scalar h y
        _ = 0 := by rw [hzero, mul_zero]
    have hmul : ρk h * ρk h⁻¹ = (1 : k →ₗ[k] k) := by
      simpa using (ρk.map_mul h h⁻¹).symm
    have hidzero : (1 : k →ₗ[k] k) = 0 := by
      calc
        (1 : k →ₗ[k] k) = ρk h * ρk h⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : H →* kˣ :=
    { toFun := fun h ↦ Units.mk0 (ρk h 1) (hρk_ne_zero h)
      map_one' := by
        ext
        simp [ρk]
      map_mul' g h := by
        ext
        have hmul_scalar :
            ρk (g * h) 1 = ρk g 1 * ρk h 1 := by
          have hcomp :=
            congrArg (fun f : k →ₗ[k] k => f 1) (ρk.map_mul g h)
          calc
            ρk (g * h) 1 = (ρk g * ρk h) 1 := hcomp
            _ = ρk g (ρk h 1) := rfl
            _ = ρk h 1 * ρk g 1 := hρk_scalar g (ρk h 1)
            _ = ρk g 1 * ρk h 1 := mul_comm _ _
        exact hmul_scalar }
  have hρk_eq (h : H) : ρk h = (oneDimensionalRepresentation α) h := by
    apply LinearMap.ext
    intro y
    calc
      ρk h y = y * ρk h 1 := hρk_scalar h y
      _ = ((α h : kˣ) : k) * y := by simp [α, mul_comm]
      _ = (oneDimensionalRepresentation α h) y := by
            change ((α h : kˣ) : k) * y = ((α h : kˣ) : k) * y
            rfl
  refine ⟨α, ?_⟩
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro h
  simpa [ρk, LinearMap.comp_assoc] using
    congrArg (fun f => f.comp e.toLinearMap) (hρk_eq h)

/-- Helper for Theorem 18-18.4-1: a simple module over a finite commutative group has the same
Grothendieck class as a one-dimensional unit-valued character representation. -/
private theorem simple_commutative_representation_class_eq_linear_character_class
    {H : Type u} [Group H] [Finite H] [IsMulCommutative H]
    (S : FDRep k H) [Simple S] :
    ∃ α : H →* kˣ, [S]₀ = [FDRep.of (oneDimensionalRepresentation α)]₀ := by
  rcases simple_commutative_representation_iso_one_dimensional_local
      S with ⟨α, hα⟩
  refine ⟨α, ?_⟩
  rcases hα with ⟨e⟩
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := H) ⟨e.toFDRepIso⟩

/-- Helper for Theorem 18-18.4-1: every `Nat.card H`-th root of unity is automatically a
prime-to-`p` root whenever `Nat.card H` is prime to `p`. -/
private def rootsOfUnityToPrimeToPRoot
    {H : Type u} [Group H] [Finite H]
    (hpn : Nat.Coprime p (Nat.card H)) :
    rootsOfUnity (Nat.card H) k →* PrimeToPRoot p k :=
  { toFun := PrimeToPRoot.ofRootsOfUnity hpn
    map_one' := by
      ext
      simp [PrimeToPRoot.ofRootsOfUnity]
    map_mul' ζ ξ := by
      ext
      simp [PrimeToPRoot.ofRootsOfUnity, mul_assoc] }

/-- Helper for Theorem 18-18.4-1: a unit-valued character on a finite group canonically lands in
the subgroup of `Nat.card H`-th roots of unity. -/
private def rootsOfUnityCharacter
    {H : Type u} [Group H] [Finite H]
    (β : H →* kˣ) : H →* rootsOfUnity (Nat.card H) k where
  toFun h := by
    letI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
    refine rootsOfUnity.mkOfPowEq (M := k) (n := Nat.card H) (((β h : kˣ) : k)) ?_
    exact congrArg (fun ζ : kˣ ↦ (ζ : k)) <|
      (orderOf_dvd_iff_pow_eq_one).mp <|
        (orderOf_map_dvd β h).trans (orderOf_dvd_natCard h)
  map_one' := by
    apply Subtype.ext
    exact Units.ext <| by
      simp
  map_mul' x y := by
    apply Subtype.ext
    exact Units.ext <| by
      simp

/-- Helper for Theorem 18-18.4-1: after choosing a lift of the prime-to-`p` roots into `Kˣ`, a
linear character over `k` on a group of order prime to `p` canonically lifts to a linear
character over `K`. -/
private def liftedLinearCharacter
    {H : Type u} [Group H] [Finite H]
    (hpn : Nat.Coprime p (Nat.card H))
    (lift : PrimeToPRoot p k →* Kˣ) (β : H →* kˣ) : H →* Kˣ :=
  lift.comp <|
    (rootsOfUnityToPrimeToPRoot (p := p) (k := k) hpn).comp
      (rootsOfUnityCharacter (k := k) β)

/-- Helper for Theorem 18-18.4-1: the characteristic polynomial of a one-dimensional unit-valued
representation is `X - β(h)`. -/
private theorem linear_charpoly
    {H : Type u} [Group H] [Finite H]
    (β : H →* kˣ) (h : H) :
    LinearMap.charpoly ((oneDimensionalRepresentation β) h) =
      Polynomial.X - Polynomial.C ((β h : kˣ) : k) := by
  let b := Module.Free.chooseBasis k k
  rw [← LinearMap.charpoly_toMatrix ((oneDimensionalRepresentation β) h) b]
  have hmat :
      LinearMap.toMatrix b b ((oneDimensionalRepresentation β) h) =
        Matrix.diagonal fun _ ↦ ((β h : kˣ) : k) := by
    convert (Algebra.toMatrix_lsmul (b := b) (((β h : kˣ) : k))) using 1
  rw [hmat, Matrix.charpoly_diagonal]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex k k) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex k k, Module.finrank_self]
  simp [hcard]

/-- Helper for Theorem 18-18.4-1: if two root multisets agree, then sums over their attached
copies agree once the summands are transported termwise along that equality. -/
private theorem attached_sum_eq_of_eq_local
    {A : Type u} [AddCommMonoid A]
    {m₁ m₂ : Multiset k} (hm : m₁ = m₂)
    (f₁ : {x // x ∈ m₁} → A) (f₂ : {x // x ∈ m₂} → A)
    (hfun : ∀ μ : {x // x ∈ m₁}, f₁ μ = f₂ ⟨μ.1, hm ▸ μ.2⟩) :
    (Multiset.map f₁ m₁.attach).sum = (Multiset.map f₂ m₂.attach).sum := by
  subst hm
  have hmap :
      Multiset.map f₁ m₁.attach = Multiset.map f₂ m₁.attach := by
    apply Multiset.map_congr rfl
    intro μ _
    simpa using hfun μ
  simpa [hmap]

/-- Helper for Theorem 18-18.4-1: the unique root in the one-dimensional characteristic packet
produces the same packaged prime-to-`p` root as the canonical roots-of-unity character value. -/
private theorem one_dimensional_charpoly_root_primeToPRoot_eq_rootsOfUnityCharacter_local
    {H : Type u} [Group H] [Finite H]
    (hpn : Nat.Coprime p (Nat.card H))
    (β : H →* kˣ) (s : { x : H // IsPRegular p x })
    (μ : {x // x ∈ ((oneDimensionalRepresentation β) s.1).charpoly.roots}) :
    charpolyRoot_primeToPRoot (p := p) (k := k) (oneDimensionalRepresentation β) s.2 μ.2 =
      rootsOfUnityToPrimeToPRoot (p := p) (k := k) hpn
        (rootsOfUnityCharacter (k := k) β s.1) := by
  apply Subtype.ext
  apply Units.ext
  have hμroot : μ.1 = ((β s.1 : kˣ) : k) := by
    simpa [linear_charpoly] using μ.2
  change ((charpolyRoot_primeToPRoot (p := p) (k := k) (oneDimensionalRepresentation β) s.2 μ.2 :
      PrimeToPRoot p k) : k) =
    ((rootsOfUnityToPrimeToPRoot (p := p) (k := k) hpn
      (rootsOfUnityCharacter (k := k) β s.1) : PrimeToPRoot p k) : k)
  rw [charpolyRoot_primeToPRoot_coe]
  simpa [rootsOfUnityToPrimeToPRoot, rootsOfUnityCharacter, PrimeToPRoot.ofRootsOfUnity] using
    hμroot

/-- Helper for Theorem 18-18.4-1: on a one-dimensional unit-valued representation of a group of
order prime to `p`, the modular character is exactly the ordinary character of the lifted linear
character over `K`. -/
private theorem modularCharacter_oneDimensionalRepresentation_eq_lifted
    {H : Type u} [Group H] [Finite H]
    (hpn : Nat.Coprime p (Nat.card H))
    (lift : PrimeToPRoot p k →* Kˣ) (β : H →* kˣ)
    (s : { x : H // IsPRegular p x }) :
    modularCharacter (PrimeToPRoot.toFieldLift lift) (oneDimensionalRepresentation β) s =
      ((liftedLinearCharacter (p := p) (k := k) hpn lift β s.1 : Kˣ) : K) := by
  classical
  let a : k := ((β s.1 : kˣ) : k)
  have hroots :
      ((oneDimensionalRepresentation β) s.1).charpoly.roots = ({a} : Multiset k) := by
    simpa [a, linear_charpoly] using (Polynomial.roots_X_sub_C a)
  rw [Representation.modularCharacter]
  have hsum :
      (Multiset.map
        (fun μ : {x // x ∈ ((oneDimensionalRepresentation β) s.1).charpoly.roots} ↦
          ((lift
              (charpolyRoot_primeToPRoot (p := p) (k := k) (oneDimensionalRepresentation β)
                s.2 μ.2) : Kˣ) : K))
        (((oneDimensionalRepresentation β) s.1).charpoly.roots.attach)).sum =
      (Multiset.map
        (fun _μ : {x // x ∈ ({a} : Multiset k)} ↦
          ((lift
              (rootsOfUnityToPrimeToPRoot (p := p) (k := k) hpn
                (rootsOfUnityCharacter (k := k) β s.1)) : Kˣ) : K))
        (({a} : Multiset k).attach)).sum := by
    exact attached_sum_eq_of_eq_local (k := k) hroots _ _
      (fun μ ↦ by
        simpa [a] using
          congrArg (fun ζ : PrimeToPRoot p k => ((lift ζ : Kˣ) : K))
            (one_dimensional_charpoly_root_primeToPRoot_eq_rootsOfUnityCharacter_local
              (p := p) (k := k) (H := H) hpn β s μ))
  have hsingleton :
      (Multiset.map
        (fun _μ : {x // x ∈ ({a} : Multiset k)} ↦
          ((lift
              (rootsOfUnityToPrimeToPRoot (p := p) (k := k) hpn
                (rootsOfUnityCharacter (k := k) β s.1)) : Kˣ) : K))
        (({a} : Multiset k).attach)).sum =
      ((liftedLinearCharacter (p := p) (k := k) hpn lift β s.1 : Kˣ) : K) := by
    simp [a, liftedLinearCharacter]
  simpa [PrimeToPRoot.toFieldLift] using hsum.trans hsingleton

/-- Helper for Theorem 18-18.4-1: on a group of order prime to `p`, the `p`-regular-component
transform of a one-dimensional class is already the ordinary character of the lifted linear
character over `K`. -/
private theorem
    pRegularComponentVirtualModularCharacter_linear_class_mem_characterRingOverField_of_coprime_card
    {H : Type u} [Group H] [Finite H]
    (lift : PrimeToPRoot p k →* Kˣ) (β : H →* kˣ)
    (hpn : Nat.Coprime p (Nat.card H)) :
    ([FDRep.of (oneDimensionalRepresentation β)]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  let χK : R[K](H) :=
    ⟨(oneDimensionalRepresentation (K := K)
        (liftedLinearCharacter (p := p) (k := k) hpn lift β)).character,
      Representation.rep_character_mem_characterRingOverField (K := K) (G := H)
        (Rep.of (oneDimensionalRepresentation (K := K)
          (liftedLinearCharacter (p := p) (k := k) hpn lift β)))⟩
  have hχK :
      ([FDRep.of (oneDimensionalRepresentation β)]₀)′[p, PrimeToPRoot.toFieldLift lift] =
        (χK : H → K) := by
    ext s
    have hs : IsPRegular p s := hpn.coprime_dvd_right (orderOf_dvd_natCard s)
    rw [pRegularComponentVirtualModularCharacter_apply_of_isPRegular
      (p := p) (k := k) (K := K) (G := H)
      (lift := lift) (x := [FDRep.of (oneDimensionalRepresentation β)]₀) ⟨s, hs⟩]
    rw [virtualModularCharacter_class]
    simpa [χK, oneDimensionalRepresentation_character_apply] using
      modularCharacter_oneDimensionalRepresentation_eq_lifted
        (p := p) (k := k) (K := K) (H := H) hpn lift β ⟨s, hs⟩
  rw [hχK]
  exact χK.2

/-- Helper for Theorem 18-18.4-1: for a simple class on a finite commutative group of order
prime to `p`, Serre's transform already comes from a genuine ordinary linear character over `K`. -/
theorem pRegularComponentVirtualModularCharacter_simple_class_mem_characterRingOverField_of_commutative_coprime
    {H : Type u} [Group H] [Finite H] [IsMulCommutative H]
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k H) [Simple S]
  (hpn : Nat.Coprime p (Nat.card H)) :
    ([S]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  rcases simple_commutative_representation_class_eq_linear_character_class
      S with ⟨α, hα⟩
  rw [hα]
  exact pRegularComponentVirtualModularCharacter_linear_class_mem_characterRingOverField_of_coprime_card
    (p := p) (k := k) (K := K) lift α hpn

/-- Helper for Theorem 18-18.4-1: on a finite commutative group of order prime to `p`, Serre's
transform of any virtual modular class is already an ordinary virtual character over `K`. -/
theorem pRegularComponentVirtualModularCharacter_mem_characterRingOverField_of_commutative_coprime
    {H : Type u} [Group H] [Finite H] [IsMulCommutative H]
    (lift : PrimeToPRoot p k →* Kˣ) (hpn : Nat.Coprime p (Nat.card H))
    (x : R₀[k](H)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](H) := by
  classical
  rcases
      exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
        (k := k) (G := H) with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  -- `p` is coprime to `|H|`, so `|H|` does not vanish in the characteristic-`p` field `k` and
  -- the semisimple finite-index owner applies.
  letI : NeZero ((Nat.card H : k)) := ⟨by
    intro h0
    exact
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hpn
        ((CharP.cast_eq_zero_iff k p (Nat.card H)).mp h0)⟩
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : AddCommMonoid (R₀[k](H)) :=
    (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid
  letI : AddCommGroup (R₀[k](H)) :=
    QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)
  letI : Module ℤ (R₀[k](H)) := AddCommGroup.toIntModule (R₀[k](H))
  let b₀ := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let φ : R₀[k](H) →+ H → K :=
    pRegularComponentVirtualModularCharacter (G := H) p (PrimeToPRoot.toFieldLift lift)
  have hbasis_mem : ∀ i, φ (b₀ i) ∈ R[K](H) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    simpa [φ, b₀, simple_finiteRep_classes_basis_of_complete_family_apply] using
      pRegularComponentVirtualModularCharacter_simple_class_mem_characterRingOverField_of_commutative_coprime
        (p := p) (k := k) (K := K) (H := H) lift (π i) hpn
  let χw : R[K](H) := ∑ i, (b₀.repr x i) • ⟨φ (b₀ i), hbasis_mem i⟩
  let χ : H → K := χw
  have hχ :
      x′[p, PrimeToPRoot.toFieldLift lift] = (χ : H → K) := by
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

end CharacterRingLift

end Representation
