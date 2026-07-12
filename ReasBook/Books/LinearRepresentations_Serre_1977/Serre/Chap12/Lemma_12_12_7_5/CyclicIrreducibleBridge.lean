import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_5.AssociatedElementaryCore
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing

open Representation
open scoped Pointwise Representation

noncomputable section

universe u v

section Representation

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) (x : G)

/-- Helper for Lemma 12-12.7-5: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeLemma121275CyclicIrreducibleBridge : Fintype G :=
  Fintype.ofFinite G

attribute [local instance] instFintypeLemma121275CyclicIrreducibleBridge

local notation "C" => Subgroup.zpowers x

/-- Helper for Lemma 12-12.7-5: conjugating a representation through a linear equivalence preserves
the identity element of the acting monoid. -/
private theorem conjRepresentation_map_one
    {H : Type*} [Monoid H]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Lemma 12-12.7-5: conjugating a representation through a linear equivalence preserves
multiplication. -/
private theorem conjRepresentation_map_mul
    {H : Type*} [Monoid H]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) (g h : H) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Lemma 12-12.7-5: a representation may be transported across a linear equivalence. -/
def transportRepresentation
    {H : Type*} [Monoid H]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) : Representation K H W where
  toFun g := e.conj (ρ g)
  map_one' := conjRepresentation_map_one (K := K) e ρ
  map_mul' g h := conjRepresentation_map_mul (K := K) e ρ g h

/-- Helper for Lemma 12-12.7-5: transporting a representation along an equivariant linear
equivalence recovers the target representation exactly. -/
private theorem transportRepresentation_eq_of_equiv
    {H : Type*} [Monoid H]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ρ : Representation K H V} {τ : Representation K H W}
    (e : τ.Equiv ρ) :
    transportRepresentation (K := K) e.toLinearEquiv τ = ρ := by
  ext h v
  have hintertwine :
      e.toLinearEquiv (τ h (e.toLinearEquiv.symm v)) =
        ρ h (e.toLinearEquiv (e.toLinearEquiv.symm v)) :=
    LinearMap.congr_fun (e.toIntertwiningMap.2 h) (e.toLinearEquiv.symm v)
  simpa [transportRepresentation] using
    hintertwine.trans (by rw [e.toLinearEquiv.apply_symm_apply])

/-- Helper for Lemma 12-12.7-5: once an equivalent `C`-model extends across `H`, transporting
that extension along the equivalence yields an extension of the original `C`-representation. -/
theorem exists_extension_of_equiv_of_extension
    {H : Subgroup G} {D : Subgroup G} (hD : D ≤ H)
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K D V) (τ : Representation K D W)
    (e : τ.Equiv ρ)
    (σ : Representation K H W)
    (hσ : σ.comp (Subgroup.inclusion hD) = τ) :
    ∃ σ' : Representation K H V,
      σ'.comp (Subgroup.inclusion hD) = ρ := by
  refine ⟨transportRepresentation (K := K) e.toLinearEquiv σ, ?_⟩
  ext c v
  have hσc : σ (Subgroup.inclusion hD c) = τ c := by
    simpa using congrArg (fun π : Representation K D W ↦ π c) hσ
  rw [show
      (transportRepresentation (K := K) e.toLinearEquiv σ).comp (Subgroup.inclusion hD) c =
        e.toLinearEquiv.conj (σ (Subgroup.inclusion hD c)) by rfl]
  rw [hσc]
  have hτc :
      (transportRepresentation (K := K) e.toLinearEquiv τ) c = ρ c := by
    simpa using congrArg (fun π : Representation K D V ↦ π c)
      (transportRepresentation_eq_of_equiv (K := K) e)
  simpa [transportRepresentation] using LinearMap.congr_fun hτc v

omit [Finite G] in
/-- Helper for Lemma 12-12.7-5: an irreducible representation has a nontrivial carrier. -/
private theorem irreducible_representation_nontrivial_local
    {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module K W]
    (τ : Representation K H W) [τ.IsIrreducible] : Nontrivial W := by
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top : (⊥ : Subrepresentation τ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext w
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim w 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

omit [Finite G] in
/-- Helper for Lemma 12-12.7-5: over an algebraically closed field, an irreducible
representation of the cyclic subgroup `C = ⟨x⟩` is afforded by a linear character. -/
private theorem algClosed_cyclic_irreducible_has_linear_character
    {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (τ : Representation F C W) [τ.IsIrreducible] :
    ∃ β : C →* Fˣ, τ.character = fun g ↦ ((β g : Fˣ) : F) := by
  letI : IsMulCommutative C := Subgroup.zpowers_isMulCommutative x
  have hdim : Module.finrank F W = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative τ
  let scalarEquiv : F ≃ₗ[F] (W →ₗ[F] W) :=
    LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : F) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let β₀ : C → F := fun g ↦ scalarEquiv.symm (τ g)
  have hβ₀_eq (g : C) : τ g = β₀ g • LinearMap.id := by
    calc
      τ g = scalarEquiv (β₀ g) := by simp [β₀]
      _ = β₀ g • LinearMap.id := hscalar _
  have hβ₀_one : β₀ 1 = 1 := by
    have hscalar1 : scalarEquiv (1 : F) = (1 : W →ₗ[F] W) := by
      simpa using hscalar (1 : F)
    apply scalarEquiv.injective
    calc
      scalarEquiv (β₀ 1) = τ 1 := by simp [β₀]
      _ = (1 : W →ₗ[F] W) := by simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hβ₀_mul (g h : C) : β₀ (g * h) = β₀ g * β₀ h := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (β₀ (g * h)) = τ (g * h) := by simp [β₀]
      _ = τ g * τ h := by simp
      _ = (β₀ g * β₀ h) • LinearMap.id := by
        rw [hβ₀_eq, hβ₀_eq]
        ext w
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (β₀ g * β₀ h) := (hscalar _).symm
  have hβ₀_ne_zero (g : C) : β₀ g ≠ 0 := by
    have hpos : 0 < Module.finrank F W := by
      simpa [hdim]
    letI : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : τ g = 0 := by
      simp [hβ₀_eq, hzero]
    have hmul : τ g * τ g⁻¹ = (1 : W →ₗ[F] W) := by
      simpa using (τ.map_mul g g⁻¹).symm
    have hidzero : (1 : W →ₗ[F] W) = 0 := by
      calc
        (1 : W →ₗ[F] W) = τ g * τ g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let β : C →* Fˣ :=
    { toFun := fun g ↦ Units.mk0 (β₀ g) (hβ₀_ne_zero g)
      map_one' := by
        ext
        simpa using hβ₀_one
      map_mul' g h := by
        ext
        simpa using hβ₀_mul g h }
  refine ⟨β, ?_⟩
  ext g
  simp [Representation.character, hβ₀_eq, hdim, β]

/-- Helper for Lemma 12-12.7-5: every irreducible representation of the cyclic subgroup
`C = ⟨x⟩` over `AlgebraicClosure K` has character given by a linear character. -/
theorem algClosed_cyclic_irreducible_character_eq_linearCharacter
    {W : Type*} [AddCommGroup W] [Module (AlgebraicClosure K) W]
    [FiniteDimensional (AlgebraicClosure K) W]
    (τ : Representation (AlgebraicClosure K) C W) [τ.IsIrreducible] :
    ∃ β : C →* (AlgebraicClosure K)ˣ, τ.character = fun g ↦ ↑(β g) := by
  -- This public wrapper exposes the cyclic irreducible classification for later constituent
  -- arguments without reopening the one-dimensional proof each time.
  exact algClosed_cyclic_irreducible_has_linear_character (x := x) τ

/-- Helper for Lemma 12-12.7-5: after scalar extension to an algebraic closure, an irreducible
`K`-representation of `C = ⟨x⟩` has an irreducible constituent afforded by a linear character. -/
theorem choose_algClosed_linear_constituent
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K C V) [ρ.IsIrreducible] :
    ∃ σ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ),
      σ.toRepresentation.IsIrreducible ∧
        ∃ β : C →* (AlgebraicClosure K)ˣ,
          σ.toRepresentation.character = fun g ↦ ↑(β g) := by
  classical
  have hcard_ne : (Nat.card C : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card C : AlgebraicClosure K) := ⟨hcard_ne⟩
  letI : Nontrivial V := irreducible_representation_nontrivial_local (K := K) ρ
  letI : Nontrivial (TensorProduct K (AlgebraicClosure K) V) := inferInstance
  obtain ⟨ι, _, σ, _, hσ_top, hσ_irr⟩ :
      ∃ (ι : Type (max u v)) (_ : Fintype ι)
        (σ : ι → Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure K) ρ)),
          iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
            (⨆ i, (σ i).toSubmodule) = ⊤ ∧
            ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_isInternal_irreducible_subrepresentations
      (ρ := Representation.scalarExtension (k := AlgebraicClosure K) ρ)
  have hι : Nonempty ι := by
    by_cases hcard0 : Fintype.card ι = 0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
      have hbot :
          (⨆ i : ι, (σ i).toSubmodule) =
            (⊥ : Submodule (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V)) := by
        simp
      have htop :
          (⊥ : Submodule (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V)) = ⊤ := by
        exact hbot.symm.trans hσ_top
      have hzero :
          Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V) = 0 := by
        have hfinrank :=
          congrArg
            (fun S : Submodule (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V) ↦
              Module.finrank (AlgebraicClosure K) S) htop
        simpa using hfinrank.symm
      have hbase :
          Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V) =
            Module.finrank K V := by
        simpa using
          (Module.finrank_baseChange (R := AlgebraicClosure K) (S := K) (M' := V))
      have hpos : 0 < Module.finrank K V := Module.finrank_pos
      omega
    · exact Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard0)
  let i : ι := Classical.choice hι
  refine ⟨σ i, hσ_irr i, ?_⟩
  exact algClosed_cyclic_irreducible_has_linear_character (x := x) (σ i).toRepresentation

/-- Helper for Lemma 12-12.7-5: for finite-dimensional irreducible representations over `K`,
equality of `K`-characters already forces an equivariant linear equivalence. -/
theorem nonempty_equiv_of_character_eq_of_isIrreducible_local
    {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K H V) (σ : Representation K H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  letI : Invertible (Nat.card H : K) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hself_pos : 0 < Module.finrank K (ρ.IntertwiningMap ρ) := by
    letI : Nontrivial V := irreducible_representation_nontrivial_local (K := K) ρ
    have hId_ne : (Representation.IntertwiningMap.id ρ : ρ.IntertwiningMap ρ) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      intro hzero
      have hvalue := congrArg (fun F : ρ.IntertwiningMap ρ ↦ F v) hzero
      exact hv (by simpa using hvalue)
    letI : Nontrivial (ρ.IntertwiningMap ρ) := ⟨⟨Representation.IntertwiningMap.id ρ, 0, hId_ne⟩⟩
    exact Module.finrank_pos
  have hfinrank_eq :
      Module.finrank K (ρ.IntertwiningMap σ) =
        Module.finrank K (ρ.IntertwiningMap ρ) := by
    -- Orthogonality shows that equal characters give the same intertwining-space dimension.
    exact Nat.cast_injective (R := K) <|
      calc
        (Module.finrank K (ρ.IntertwiningMap σ) : K) = ⟪ρ.character, σ.character⟫ := by
          symm
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K ρ σ
        _ = ⟪ρ.character, ρ.character⟫ := by simp [hchar]
        _ = Module.finrank K (ρ.IntertwiningMap ρ) := by
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K ρ ρ
  have hpos : 0 < Module.finrank K (ρ.IntertwiningMap σ) := by
    rw [hfinrank_eq]
    exact hself_pos
  obtain ⟨f, hf⟩ : ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
    exact Module.finrank_pos_iff_exists_ne_zero.mp hpos
  -- A nonzero intertwiner between irreducibles is already bijective, hence an equivalence.
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

end Representation
