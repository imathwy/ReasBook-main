import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open AlgEquiv

universe u v w

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
variable {M : Type w} [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M] [IsGalois K M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for Lemma 15.111.11:
- primary domain: decomposition and inertia groups in a tower of integral closures under Galois
  restriction
- sampled owner declarations:
  `MulAction.stabilizer`,
  `Ideal.inertia`,
  `Ideal.under`,
  `AlgEquiv.restrictNormalHom`,
  `IsIntegralClosure.MulSemiringAction`
- best owner abstraction: the canonical subgroup owners `MulAction.stabilizer G I` and `I.inertia G`
  together with the restriction homomorphism `restrictNormalHom`
- primitive data: the canonical `B`-algebra structure on `C` induced by `L ⊆ M` and a prime ideal
  `r : Ideal C`
- derived API: the image equalities for the decomposition and inertia groups of the contracted
  prime `r.under B`

Layer triage:
- `source-facing`: the two image-equality statements in the tower
- `core/canonical`: `MulAction.stabilizer`, `Ideal.inertia`, and `restrictNormalHom`
- `bridge/view`: contraction of `r` to `B`, canonically expressed as `r.under B`

The file should keep the source-facing statements, but state them directly in terms of those owner
declarations instead of repeating the integral-closure map inline or using a parallel inertia
surface. -/

private noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

/-- The canonical `Gal(M / K)`-action on the integral closure `C` of `A` in `M`. -/
private local instance integralClosureMulSemiringAction_top :
    MulSemiringAction Gal(M/K) C :=
  IsIntegralClosure.MulSemiringAction A K M C

/-- The canonical `Gal(L / K)`-action on the integral closure `B` of `A` in `L`. -/
private local instance integralClosureMulSemiringAction_base :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

/-- Helper for Lemma 15.111.11: the restricted automorphism on `L` is characterized by commuting
with the tower map `L → M`. -/
private lemma restrictNormalHom_commutes_tower_map
    (τ : Gal(M/K)) (x : L) :
    τ (algebraMap L M x) = algebraMap L M (restrictNormalHom L τ x) := by
  -- This is exactly the defining commutative-square property of `restrictNormalHom`.
  exact (AlgEquiv.restrictNormal_commutes (χ := τ) (E := L) (x := x)).symm

/-- Helper for Lemma 15.111.11: the tower map `B → C` intertwines the upstairs Galois action with
the restricted action downstairs. -/
private theorem smul_algebraMap_eq_algebraMap_restrictNormalHom_smul
    (τ : Gal(M/K)) (b : B) :
    τ • algebraMap B C b = algebraMap B C (restrictNormalHom L τ • b) := by
  -- Compare the two integral-closure elements after coercing them to the ambient field `M`.
  apply Subtype.ext
  simpa using (AlgEquiv.restrictNormal_commutes (χ := τ) (E := L) (x := (b : L))).symm

/-- Helper for Lemma 15.111.11: contracting a conjugated prime from `C` to `B` agrees with first
restricting the Galois automorphism to `L` and then acting on the contracted prime. -/
private lemma under_smul_eq_restrictNormalHom_smul_under
    (τ : Gal(M/K)) (r : Ideal C) :
    (τ • r).under B = restrictNormalHom L τ • (r.under B) := by
  -- Compare membership in the two contracted ideals elementwise through the tower map `B → C`.
  ext b
  constructor
  · intro hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hb_top : algebraMap B C b ∈ τ • r := by
      simpa [Ideal.under_def] using hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb_top
    have htop :
        algebraMap B C ((restrictNormalHom L τ)⁻¹ • b) ∈ r := by
      simpa [smul_algebraMap_eq_algebraMap_restrictNormalHom_smul, mul_smul] using hb_top
    simpa [Ideal.under_def] using htop
  · intro hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have hb_top :
        algebraMap B C ((restrictNormalHom L τ)⁻¹ • b) ∈ r := by
      simpa [Ideal.under_def] using hb
    have htop : algebraMap B C b ∈ τ • r := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [smul_algebraMap_eq_algebraMap_restrictNormalHom_smul, mul_smul] using hb_top
    simpa [Ideal.under_def] using htop

/-- Helper for Lemma 15.111.11: the intermediate integral closure `B` has fraction field `L`. -/
private lemma integralClosureBase_isFractionRing :
    IsFractionRing B L := by
  letI : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  -- The standard integral-closure owner theorem upgrades algebraicity to the fraction-ring fact.
  exact integralClosure.isFractionRing_of_algebraic (A := A) (L := L) fun x hx ↦
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply A K L x).symm.trans hx)

/-- Helper for Lemma 15.111.11: the upper integral closure `C` is also the integral closure of
`B` inside `M`. -/
private lemma integralClosureTop_isIntegralClosure_over_base :
    IsIntegralClosure C B M := by
  -- The integral closure of `A` in `M` is automatically the integral closure over any integral
  -- intermediate ring between `A` and `M`.
  exact IsIntegralClosure.tower_top (R := A) (A := B)

/-- Helper for Lemma 15.111.11: relative to the intermediate ring `B`, the upper integral
closure `C` still has fraction field `M`. -/
private lemma integralClosureTop_isFractionRing_over_base :
    IsFractionRing C M := by
  letI := integralClosureBase_isFractionRing (A := A) (K := K) (L := L)
  letI : IsIntegralClosure C B M :=
    integralClosureTop_isIntegralClosure_over_base (A := A) (K := K) (L := L) (M := M)
  letI : Algebra.IsAlgebraic B M := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic L M)
  -- Apply the generic fraction-ring theorem for a relative integral closure.
  exact IsIntegralClosure.isFractionRing_of_algebraic B C fun x hx ↦
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap L M).mp <| (IsScalarTower.algebraMap_apply B L M x).symm.trans hx)

/-- Helper for Lemma 15.111.11: the relative tower `M / L` is Galois. -/
private lemma isGalois_relative :
    IsGalois L M := by
  -- This is the tower-top Galois fact for `K ⊆ L ⊆ M`.
  exact IsGalois.tower_top_of_isGalois (F := K) (E := L) (K := M)

/-- The canonical `Gal(M / L)`-action on the integral closure `C` over the intermediate ring
`B`. -/
private local instance integralClosureMulSemiringAction_relative :
    MulSemiringAction Gal(M/L) C := by
  letI : IsFractionRing B L := integralClosureBase_isFractionRing (A := A) (K := K) (L := L)
  letI : IsIntegralClosure C B M :=
    integralClosureTop_isIntegralClosure_over_base (A := A) (K := K) (L := L) (M := M)
  letI : IsGalois L M := isGalois_relative (A := A) (K := K) (L := L) (M := M)
  exact IsIntegralClosure.MulSemiringAction B L M C

/-- The relative `Gal(M / L)`-action makes `C` into the canonical Galois closure over `B`. -/
private local instance integralClosure_isGaloisGroup_relative :
    IsGaloisGroup Gal(M/L) B C := by
  letI : IsFractionRing B L := integralClosureBase_isFractionRing (A := A) (K := K) (L := L)
  letI : IsFractionRing C M :=
    integralClosureTop_isFractionRing_over_base (A := A) (K := K) (L := L) (M := M)
  letI : IsGalois L M := isGalois_relative (A := A) (K := K) (L := L) (M := M)
  letI : IsIntegralClosure C B M :=
    integralClosureTop_isIntegralClosure_over_base (A := A) (K := K) (L := L) (M := M)
  -- The relative Galois owner theorem now applies to `B ⊆ C`.
  exact IsGaloisGroup.of_isFractionRing (G := Gal(M / L)) (A := B) (B := C) (K := L) (L := M)

/-- Helper for Lemma 15.111.11: relative automorphisms fix `B` pointwise, so their action on `C`
commutes with the `B`-scalar action. -/
private local instance integralClosureMulSemiringAction_relative_smulCommClass :
    SMulCommClass Gal(M/L) B C where
  smul_comm υ b c := by
    apply Subtype.ext
    change υ ((algebraMap B C b : C) * c : C) = (algebraMap B C b : C) * (υ c : C)
    rw [map_mul]
    congr 1
    apply Subtype.ext
    simpa using (υ.commutes (b : L))

/-- Helper for Lemma 15.111.11: after viewing `Gal(M / L)` inside `Gal(M / K)`, its action on
`C` agrees with the relative action. -/
private lemma relative_smul_eq_top_smul
    (υ : Gal(M/L)) (c : C) :
    υ • c = (MulSemiringAction.toAlgAut Gal(M/L) K M υ) • c := by
  -- Both actions come from the same field automorphism of `M`, so they agree on `C`.
  apply Subtype.ext
  rfl

/-- Helper for Lemma 15.111.11: the same comparison holds on ideals of `C`. -/
private lemma relative_smul_eq_top_smul_ideal
    (υ : Gal(M/L)) (I : Ideal C) :
    υ • I = (MulSemiringAction.toAlgAut Gal(M/L) K M υ) • I := by
  -- Compare membership after rewriting both ideal actions elementwise.
  ext c
  have hInv :
      (MulSemiringAction.toAlgAut Gal(M/L) K M υ)⁻¹ • c = υ⁻¹ • c := by
    simpa using (relative_smul_eq_top_smul (A := A) (K := K) (L := L) (M := M)
      (υ := υ⁻¹) (c := c)).symm
  constructor
  · intro hc
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hc ⊢
    exact hInv ▸ hc
  · intro hc
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hc ⊢
    exact hInv.symm ▸ hc

/-- Helper for Lemma 15.111.11: the corresponding ambient `K`-automorphism from `Gal(M / L)`
restricts trivially to `L`. -/
private lemma relative_to_top_restrictNormalHom_eq_one
    (υ : Gal(M/L)) :
    restrictNormalHom L (MulSemiringAction.toAlgAut Gal(M/L) K M υ) = 1 := by
  -- An `L`-automorphism fixes `L` pointwise, so its ambient restriction is the identity.
  ext x
  apply (algebraMap L M).injective
  simpa using (υ.commutes x)

/-- Helper for Lemma 15.111.11: a relative stabilizer element also stabilizes `r` after promotion
to `Gal(M / K)`. -/
private theorem promoted_relative_mem_stabilizer
    (r : Ideal C) [r.IsPrime]
    (υ : MulAction.stabilizer Gal(M/L) r) :
    (MulSemiringAction.toAlgAut Gal(M/L) K M υ.1) ∈ MulAction.stabilizer Gal(M/K) r := by
  -- The promoted action on ideals agrees with the relative action, so the stabilizer equation is
  -- unchanged.
  rw [MulAction.mem_stabilizer_iff]
  calc
    (MulSemiringAction.toAlgAut Gal(M/L) K M υ.1) • r = υ.1 • r := by
      symm
      exact relative_smul_eq_top_smul_ideal (A := A) (K := K) (L := L) (M := M) υ.1 r
    _ = r := υ.2

/-- Helper for Lemma 15.111.11: if two prime ideals of `C` contract to the same prime of `B`,
then an element of `Gal(M / L)` carries one to the other after viewing it inside `Gal(M / K)`. -/
private lemma exists_gal_over_base_smul_eq_of_under_eq
    (r₁ r₂ : Ideal C) [r₁.IsPrime] [r₂.IsPrime]
    (hunder : r₁.under B = r₂.under B) :
    ∃ υ : Gal(M/L), (MulSemiringAction.toAlgAut Gal(M/L) K M υ) • r₁ = r₂ := by
  -- The relative invariant-theory transitivity theorem supplies the correcting element over `B`.
  letI : IsGalois L M := isGalois_relative (A := A) (K := K) (L := L) (M := M)
  obtain ⟨υ, hυ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := B) (G := Gal(M / L))
      r₁ r₂ hunder
  refine ⟨υ, ?_⟩
  -- Rewrite the relative action on ideals as the promoted ambient action.
  calc
    (MulSemiringAction.toAlgAut Gal(M/L) K M υ) • r₁ = υ • r₁ := by
      exact relative_smul_eq_top_smul_ideal (A := A) (K := K) (L := L) (M := M) υ r₁
    _ = r₂ := hυ.symm

/-- Helper for Lemma 15.111.11: restricting an element of the decomposition group of `r` lands in
the decomposition group of the contracted prime `r.under B`. -/
private theorem restrictNormalHom_mem_decompositionGroup
    (r : Ideal C) [r.IsPrime]
    (σ : MulAction.stabilizer Gal(M/K) r) :
    restrictNormalHom L σ.1 ∈ MulAction.stabilizer Gal(L/K) (r.under B) := by
  -- Contract the stabilizer equality from `C` to `B` and rewrite it using the transport lemma.
  rw [MulAction.mem_stabilizer_iff]
  exact
    calc
      restrictNormalHom L σ.1 • (r.under B) = (σ.1 • r).under B := by
        symm
        exact under_smul_eq_restrictNormalHom_smul_under (A := A) (K := K) (L := L) σ.1 r
      _ = r.under B := by
        simpa using congrArg (fun I : Ideal C ↦ I.under B) (MulAction.mem_stabilizer_iff.mp σ.2)

/-- Helper for Lemma 15.111.11: ideal-theoretic inertia is the pointwise congruence condition
modulo the chosen ideal. -/
private theorem ideal_inertia_mem_iff
    {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    (J : Ideal R) (σ : G) :
    σ ∈ Ideal.inertia G J ↔ ∀ x : R, σ • x - x ∈ J := by
  -- This is just the defining shape of `Ideal.inertia`.
  rfl

/-- Helper for Lemma 15.111.11: every prime ideal lies over its own contraction. -/
private local instance idealLiesOver_under
    (r : Ideal C) : Ideal.LiesOver r (r.under B) := by
  simpa using (Ideal.over_under r : Ideal.LiesOver r (r.under B))

/-- Helper for Lemma 15.111.11: restricting an inertia element of `r` lands in the inertia group
of the contracted prime `r.under B`. -/
private theorem restrictNormalHom_mem_inertiaGroup
    (r : Ideal C) [r.IsPrime]
    (σ : r.inertia Gal(M/K)) :
    restrictNormalHom L σ.1 ∈ (r.under B).inertia Gal(L/K) := by
  have hσ : ∀ c : C, σ.1 • c - c ∈ r := by
    -- Unpack upstairs inertia as pointwise congruence modulo `r`.
    exact (ideal_inertia_mem_iff (J := r) σ.1).mp σ.2
  rw [ideal_inertia_mem_iff (J := r.under B)]
  intro b
  -- Transport the upstairs congruence on the image of `b` along the tower map `B → C`.
  simpa [Ideal.under_def, map_sub, smul_algebraMap_eq_algebraMap_restrictNormalHom_smul] using
    hσ (algebraMap B C b)

/-- Helper for Lemma 15.111.11: over the intermediate integral closure `B`, the relative
decomposition group of `r` surjects onto the residue-field automorphism group of `κ(r)`. -/
private theorem relative_stabilizerHom_surjective_over_contracted_prime
    (r : Ideal C) [r.IsPrime] :
    Function.Surjective
      (IsFractionRing.stabilizerHom Gal(M/L) (r.under B) r
        (Ideal.ResidueField (r.under B)) r.ResidueField) := by
  letI : IsFractionRing B L := integralClosureBase_isFractionRing (A := A) (K := K) (L := L)
  letI : IsFractionRing C M :=
    integralClosureTop_isFractionRing_over_base (A := A) (K := K) (L := L) (M := M)
  letI : IsGalois L M := isGalois_relative (A := A) (K := K) (L := L) (M := M)
  letI : IsIntegralClosure C B M :=
    integralClosureTop_isIntegralClosure_over_base (A := A) (K := K) (L := L) (M := M)
  letI : Ideal.LiesOver r (r.under B) := by
    simpa using (Ideal.over_under r : Ideal.LiesOver r (r.under B))
  -- This is the canonical relative residue-field surjectivity owner specialized to `B ⊆ C`.
  exact IsFractionRing.stabilizerHom_surjective
    (A := B) (B := C) (G := Gal(M / L)) (P := r.under B) (Q := r)
    (Ideal.ResidueField (r.under B)) r.ResidueField

/-- Helper for Lemma 15.111.11: a relative inertia element acts trivially on the quotient
`C ⧸ r`. -/
private theorem relative_inertia_quotient_stabilizerHom_eq_one
    (r : Ideal C) [r.IsPrime]
    (υ : r.inertia Gal(M/L)) :
    Ideal.Quotient.stabilizerHom r (r.under B) Gal(M/L)
      ⟨υ.1, (Ideal.inertia_le_stabilizer (M := Gal(M / L)) (R := C) r) υ.2⟩ = 1 := by
  -- Route correction: keep the correction step at the quotient level, where inertia is the kernel
  -- of the canonical stabilizer action.
  ext x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Unpack the inertia condition as the defining congruence modulo `r`.
  change Ideal.Quotient.mk r (υ.1 • c) = Ideal.Quotient.mk r c
  rw [Ideal.Quotient.eq]
  exact (ideal_inertia_mem_iff (J := r) υ.1).mp υ.2 c

-- Proof sketch: for `σ ∈ Gal(L / K)`, lift `σ` to some `τ ∈ Gal(M / K)` by surjectivity of
-- `restrictNormalHom`. Then `τ • r` and `r` contract to the same prime of `B`, so
-- Lemma `15.111.10` produces an element of `Gal(M / L)` carrying `τ • r` back to `r`. Composing
-- with `τ` yields an element of the decomposition group of `r` restricting to `σ`.
/-- Lemma 15.111.11 (1): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the decomposition group of `r` is the
decomposition group of `q`. -/
theorem restrictNormalHom_image_decompositionGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (MulAction.stabilizer Gal(M / K) r) =
    MulAction.stabilizer Gal(L / K) (r.under B) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact restrictNormalHom_mem_decompositionGroup (A := A) (K := K) (L := L) r ⟨τ, hτ⟩
  · intro hσ
    obtain ⟨τ, hτrestrict⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    have hunder : (τ • r).under B = r.under B := by
      calc
        (τ • r).under B = restrictNormalHom L τ • (r.under B) :=
          under_smul_eq_restrictNormalHom_smul_under (A := A) (K := K) (L := L) τ r
        _ = r.under B := by
          simpa [hτrestrict] using (MulAction.mem_stabilizer_iff.mp hσ)
    obtain ⟨υ, hυ⟩ :=
      exists_gal_over_base_smul_eq_of_under_eq (A := A) (K := K) (L := L) (M := M) (τ • r) r hunder
    refine ⟨(MulSemiringAction.toAlgAut Gal(M / L) K M υ) * τ, ?_, ?_⟩
    · -- The correction element from `Gal(M / L)` carries `τ • r` back to `r`.
      rw [MulAction.mem_stabilizer_iff]
      simpa [mul_smul] using hυ
    · -- Its restriction is trivial on `L`, so the composite still restricts to `σ`.
      rw [MonoidHom.map_mul, relative_to_top_restrictNormalHom_eq_one, one_mul, hτrestrict]

/-- Helper for Lemma 15.111.11: a downstairs inertia element first lifts to the upstairs
decomposition group by the already proved decomposition-group image theorem. -/
private theorem exists_stabilizer_lift_of_mem_under_inertia
    (r : Ideal C) [r.IsPrime] {σ : Gal(L/K)}
    (hσ : σ ∈ (r.under B).inertia Gal(L/K)) :
    ∃ τ : MulAction.stabilizer Gal(M/K) r, restrictNormalHom L τ.1 = σ := by
  -- Forget inertia to decomposition, then apply the source-faithful lift from clause `(1)`.
  have hσdecomp : σ ∈ MulAction.stabilizer Gal(L/K) (r.under B) :=
    (Ideal.inertia_le_stabilizer (M := Gal(L / K)) (R := B) (r.under B)) hσ
  have hσmap :
      σ ∈ Subgroup.map (restrictNormalHom L) (MulAction.stabilizer Gal(M / K) r) := by
    simpa [restrictNormalHom_image_decompositionGroup_eq (A := A) (K := K) (L := L) r] using hσdecomp
  rcases hσmap with ⟨τ, hτ, hτrestrict⟩
  exact ⟨⟨τ, hτ⟩, hτrestrict⟩

-- Proof sketch: use the same lifting argument as in clause `(1)`, but now compare the induced
-- actions on the residue fields. Lemma `15.111.10` gives surjectivity from the decomposition group
-- onto residue-field automorphisms, so the lift may be adjusted by an element of `Gal(M / L)`
-- acting trivially on the residue field at `r`, placing the adjusted lift in the inertia group.
/-- Lemma 15.111.11 (2): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the inertia group of `r` is the inertia
group of `q`. -/
theorem restrictNormalHom_image_inertiaGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (r.inertia Gal(M/K)) =
    (r.under B).inertia Gal(L/K) := by
  -- Route correction: the decomposition-group part is now proved via lift-and-correct over `B`.
  -- What remains is the quotient-action compatibility needed to run the same correction inside the
  -- inertia subgroup.
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact restrictNormalHom_mem_inertiaGroup (A := A) (K := K) (L := L) r ⟨τ, hτ⟩
  · intro hσ
    -- Follow the source proof exactly: first lift the downstairs inertia element to the upstairs
    -- decomposition group, postponing the correction step to `Gal(M / L)`.
    obtain ⟨τ₀, hτ₀restrict⟩ :=
      exists_stabilizer_lift_of_mem_under_inertia (A := A) (K := K) (L := L) (M := M) r hσ
    -- TODO for Lemma 15.111.11: the remaining source-faithful step is to package the induced
    -- quotient action of `τ₀` on `C ⧸ r` as a `(B ⧸ r.under B)`-algebra automorphism, using `hσ`
    -- to prove the required scalar-compatibility. The failed route tried to invoke the canonical
    -- owner `Ideal.Quotient.stabilizerHom r (r.under B) Gal(M / K)` directly, but that owner is
    -- not available upstairs because the `Gal(M / K)`-action does not commute with arbitrary
    -- `B`-scalars. The next plan must instead build this quotient action explicitly, choose a
    -- relative inverse by `Ideal.Quotient.stabilizerHom_surjective`, and then use quotient
    -- triviality to conclude inertiality.
    have : ∃ τ : MulAction.stabilizer Gal(M/K) r, restrictNormalHom L τ.1 = σ := by
      exact ⟨τ₀, hτ₀restrict⟩
    sorry

end
