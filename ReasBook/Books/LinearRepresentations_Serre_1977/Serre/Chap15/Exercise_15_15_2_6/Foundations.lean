import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

namespace LinearMap.BilinForm

variable {E : Type v} [AddCommGroup E] [Module ℤ E]
variable {R : Type*} [CommSemiring R]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- A bilinear form on a representation is invariant if each group element acts by an isometry for
that form. -/
def IsInvariantUnder (B : BilinForm R V) (ρ : Representation R G V) : Prop :=
  ∀ g : G, B.comp (ρ g) (ρ g) = B

/-- A bilinear form on a representation is invariant exactly when it is preserved pointwise by the
action of every group element. -/
theorem isInvariantUnder_iff (B : BilinForm R V) (ρ : Representation R G V) :
    B.IsInvariantUnder ρ ↔ ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y := by
  constructor
  · intro h g x y
    simpa using BilinForm.congr_fun (h g) x y
  · intro h g
    ext x y
    simpa using h g x y

variable {E : Type v} [AddCommGroup E] [Module ℤ E]

/-- An integral bilinear form is even when every diagonal value is an even integer. -/
def IsEven (B : BilinForm ℤ E) : Prop :=
  ∀ x : E, Even (B x x)

/-- A vector is characteristic modulo `2` for a bilinear form if it matches the diagonal values of
the form modulo `2`. -/
def IsCharacteristicModTwo (B : BilinForm ℤ E) (x : E) : Prop :=
  ∀ y : E, B y y ≡ B x y [ZMOD 2]

/-- Source-facing form of Serre's assertion that the integral lattice `E` is equal to its
`B`-dual lattice inside `ℚ ⊗[ℤ] E`. The previous statement encoded this as the dual of
`(⊤ : Submodule ℤ E).baseChange ℚ`, which is only the whole ambient rational space and loses the
integral lattice. Until the integral-lattice embedding is available as a first-class owner, we
record the self-dual integral-lattice surface by its unimodular Gram-matrix consequence. -/
def IsSelfDualIntegralLattice (B : BilinForm ℤ E) : Prop :=
  ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ E),
    Matrix.det (B.toMatrix b) = 1

/-- Source-facing form of Serre's assertion in Exercise 15.4(b) that the `B`-dual integral
lattice is a rational homothety of the original lattice. Route correction: the owner now stores
the actual rescaled integral form on `E`, because the later self-duality step needs the rescaling
data itself rather than only nondegeneracy. -/
def DualIntegralLatticeIsRationalHomothety (B : BilinForm ℤ E) : Prop :=
  ∃ (m : ℕ) (_hm : 0 < m) (B' : BilinForm ℤ E), B = (m : ℤ) • B' ∧
    IsSelfDualIntegralLattice B'

/-- A symmetric positive definite integral bilinear form is nondegenerate. -/
theorem nondegenerate_of_isSymm_of_posDef (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hB : B.toQuadraticMap.PosDef) :
    B.Nondegenerate := by
  refine ⟨BilinForm.separatingLeft_of_anisotropic hB.anisotropic, ?_⟩
  intro x hx
  apply BilinForm.separatingLeft_of_anisotropic hB.anisotropic x
  intro y
  rw [hB_symm.eq x y]
  exact hx y

end LinearMap.BilinForm

open LinearMap.BilinForm

namespace Representation

/-- The prime ideal `(p)` of `ℤ`, viewed as the ideal used for `p`-localization. -/
abbrev primeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

instance (p : ℕ) [Fact p.Prime] : (primeIdeal p).IsMaximal := by
  dsimp [primeIdeal]
  infer_instance

instance (p : ℕ) [Fact p.Prime] : Field (ℤ ⧸ primeIdeal p) := by
  letI : (primeIdeal p).IsMaximal := inferInstance
  exact Ideal.Quotient.field (primeIdeal p)

section PrimeReductions

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

/-- The representation obtained from `ρ` by localizing the underlying `ℤ`-module at the prime
ideal `(p)`. This is the `p`-local owner object to which Definition `15-15.2-1` applies. -/
def localizedAtPrime (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Representation (Localization.AtPrime (primeIdeal p)) G
      (LocalizedModule.AtPrime (primeIdeal p) E) where
  toFun g := LocalizedModule.map (primeIdeal p).primeCompl (ρ g)
  map_one' := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp
  map_mul' g h := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk]

variable [Module.Finite ℤ E]

/-- The whole localized module, viewed as the canonical `p`-local stable lattice inside the
localized representation. -/
def primeStableLattice (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    StableLattice (Localization.AtPrime (primeIdeal p)) (ρ.localizedAtPrime p) where
  toSubmodule := ⊤
  apply_mem_toSubmodule g := by simp
  isLattice := by
    refine ⟨Module.Finite.fg_top, ?_⟩
    simp

/-- The canonical reduction of `ρ` at the prime `p` is irreducible. -/
def HasIrreduciblePrimeReduction (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] : Prop :=
  (ρ.primeStableLattice p).reductionRepresentation.IsIrreducible

/-- The representation `ρ` has simple prime reductions when, for every prime `p`, the canonical
`p`-local stable-lattice reduction is irreducible. This is the source hypothesis expressed through
the chapter's stable-lattice reduction owner rather than a parallel quotient owner. -/
def HasSimplePrimeReductions (ρ : Representation ℤ G E) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ρ.HasIrreduciblePrimeReduction p

/-- The canonical reduction of `ρ` at the prime `p` is not the trivial representation. This is the
extra mod-`p` hypothesis needed when irreducibility alone would still allow the one-dimensional
trivial reduction. -/
def HasNontrivialPrimeReduction (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] : Prop :=
  ¬ Representation.IsTrivial (ρ.primeStableLattice p).reductionRepresentation

instance (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Module (ℤ ⧸ primeIdeal p) (ρ.primeStableLattice p).reduction :=
  Module.compHom _ (algebraMap (ℤ ⧸ primeIdeal p) (primeIdeal p).ResidueField)

theorem HasSimplePrimeReductions.irreducible
    {ρ : Representation ℤ G E} (hρ : ρ.HasSimplePrimeReductions) (p : ℕ) [Fact p.Prime] :
    ρ.HasIrreduciblePrimeReduction p :=
  hρ p

end PrimeReductions

end Representation

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section FractionFieldDualLattice

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {V : Type*} [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
variable {H : Type*} [Group H]

/-- Helper for Exercise 15-15.2-6: extending an `A`-basis of a lattice to the fraction field does
not change its `A`-span inside the ambient space. -/
theorem span_range_extendOfIsLattice_eq
    {L : Submodule A V} [Submodule.IsLattice K L] {ι : Type*} (b : Module.Basis ι A L) :
    Submodule.span A (Set.range (b.extendOfIsLattice K : Module.Basis ι K V)) = L := by
  classical
  letI : Module.Finite A L :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := L))
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  let e : Module.Basis ι K V := b.extendOfIsLattice K
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simpa [e, Module.Basis.extendOfIsLattice_apply] using (b i).property
  · intro x hx
    let xL : L := ⟨x, hx⟩
    have hx_eq : x = ∑ i, (b.repr xL i : A) • e i := by
      have hxL_eq : (∑ i, (b.repr xL i : A) • b i : L) = xL := by
        simpa using b.sum_repr xL
      have hsum_coe :
          (((∑ i, (b.repr xL i : A) • b i : L)) : V) =
            ∑ i, (b.repr xL i : A) • ((b i : L) : V) := by
        simpa [Submodule.coe_smul_of_tower] using
          (Submodule.coe_sum (p := L) (s := Finset.univ)
            (x := fun i ↦ ((b.repr xL i : A) • b i : L)))
      calc
        x = ((xL : L) : V) := rfl
        _ = (((∑ i, (b.repr xL i : A) • b i : L)) : V) := by
              exact congrArg Subtype.val hxL_eq.symm
        _ = ∑ i, (b.repr xL i : A) • ((b i : L) : V) := hsum_coe
        _ = ∑ i, (b.repr xL i : A) • e i := by
              simp [e, Module.Basis.extendOfIsLattice_apply]
    rw [hx_eq]
    refine Submodule.sum_mem _ ?_
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Helper for Exercise 15-15.2-6: a nondegenerate pairing sends an `A`-lattice to another
`A`-lattice, namely its dual lattice in the fraction-field representation. -/
theorem dualSubmodule_isLattice
    (B : BilinForm K V) (hB : B.Nondegenerate) (L : Submodule A V) [Submodule.IsLattice K L] :
    Submodule.IsLattice K (B.dualSubmodule L) := by
  classical
  letI : Module.Finite A L :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := L))
  letI : Module.IsTorsionFree A L := inferInstance
  letI : Module.Free A L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex A L
  let b : Module.Basis ι A L := Module.Free.chooseBasis A L
  let e : Module.Basis ι K V := b.extendOfIsLattice K
  have hspan : Submodule.span A (Set.range e) = L :=
    span_range_extendOfIsLattice_eq (K := K) b
  have hdual :
      B.dualSubmodule L = Submodule.span A (Set.range (B.dualBasis hB e)) := by
    calc
      B.dualSubmodule L = B.dualSubmodule (Submodule.span A (Set.range e)) := by rw [hspan]
      _ = Submodule.span A (Set.range (B.dualBasis hB e)) := by
            simpa using LinearMap.BilinForm.dualSubmodule_span_of_basis (B := B) hB e
  refine ⟨?_, ?_⟩
  · rw [hdual]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [hdual]
    simpa [Submodule.span_span_of_tower] using (B.dualBasis hB e).span_eq

/-- Helper for Exercise 15-15.2-6: invariance lets the group action preserve the dual lattice of a
stable lattice. -/
theorem dualSubmodule_map_mem_of_isInvariantUnder
    (ρ : Representation K H V) (B : BilinForm K V) (hB : B.IsInvariantUnder ρ)
    (L : StableLattice A ρ) (g : H) {x : V}
    (hx : x ∈ B.flip.dualSubmodule L.toSubmodule) :
    ρ g x ∈ B.flip.dualSubmodule L.toSubmodule := by
  intro y hy
  have hB_pointwise := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB
  have hy' : ρ g⁻¹ y ∈ L.toSubmodule := L.apply_mem_toSubmodule g⁻¹ hy
  have hpair : B y (ρ g x) = B (ρ g⁻¹ y) x := by
    simpa using hB_pointwise g (ρ g⁻¹ y) x
  simpa [hpair] using hx (ρ g⁻¹ y) hy'

/-- Helper for Exercise 15-15.2-6: a nondegenerate invariant pairing on a fraction-field
representation equips the dual lattice of any stable lattice with the same stable-lattice owner. -/
noncomputable def StableLattice.flipDual
    {ρ : Representation K H V} (L : StableLattice A ρ) (B : BilinForm K V)
    (hB_invariant : B.IsInvariantUnder ρ) (hB_nondegenerate : B.Nondegenerate) :
    StableLattice A ρ where
  toSubmodule := B.flip.dualSubmodule L.toSubmodule
  apply_mem_toSubmodule := dualSubmodule_map_mem_of_isInvariantUnder ρ B hB_invariant L
  isLattice := dualSubmodule_isLattice (K := K) B.flip hB_nondegenerate.flip L.toSubmodule

/-- Helper for Exercise 15-15.2-6: the stable lattice created from the dual pairing has the
expected underlying `A`-submodule. -/
@[simp] theorem StableLattice.flipDual_toSubmodule
    {ρ : Representation K H V} (L : StableLattice A ρ) (B : BilinForm K V)
    (hB_invariant : B.IsInvariantUnder ρ) (hB_nondegenerate : B.Nondegenerate) :
    (L.flipDual B hB_invariant hB_nondegenerate).toSubmodule = B.flip.dualSubmodule L.toSubmodule :=
  rfl

end FractionFieldDualLattice

section ReductionTransport

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {K : Type*} [CommRing K] [Algebra A K]
variable {G' : Type*} [Monoid G']
variable {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁]
variable [IsScalarTower A K V₁]
variable {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂]
variable [IsScalarTower A K V₂]

namespace StableLattice

variable {ρ₁ : Representation K G' V₁}
variable {ρ₂ : Representation K G' V₂}

/-- Helper for Exercise 15-15.2-6: an `A`-linear equivalence between two stable lattices carries
their maximal-ideal multiples onto each other. -/
theorem maximalIdealSubmodule_map_linearEquiv
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule) :
    L₁.maximalIdealSubmodule.map e.toLinearMap = L₂.maximalIdealSubmodule := by
  rw [StableLattice.maximalIdealSubmodule, StableLattice.maximalIdealSubmodule,
    Submodule.map_smul'']
  have htop : (⊤ : Submodule A L₁.toSubmodule).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.2 e.surjective
  simp [htop]

/-- Helper for Exercise 15-15.2-6: an `A`-linear equivalence of stable lattices induces the
canonical `A`-linear equivalence between their reductions modulo the maximal ideal. -/
noncomputable def reductionLinearEquivOfLinearEquivA
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule) :
    L₁.reduction ≃ₗ[A] L₂.reduction :=
  Submodule.Quotient.equiv L₁.maximalIdealSubmodule L₂.maximalIdealSubmodule e
    (maximalIdealSubmodule_map_linearEquiv e)

/-- Helper for Exercise 15-15.2-6: on represented quotient classes, the reduction equivalence
induced by a lattice linear equivalence is the obvious quotient class of the image upstairs. -/
@[simp] theorem reductionLinearEquivOfLinearEquivA_apply_mk
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (x : L₁.toSubmodule) :
    reductionLinearEquivOfLinearEquivA e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := by
  simp [reductionLinearEquivOfLinearEquivA, Submodule.Quotient.equiv_apply]

/-- Helper for Exercise 15-15.2-6: an `A`-linear equivalence of stable lattices also induces the
expected residue-field linear equivalence between their reductions. -/
noncomputable def reductionLinearEquivOfLinearEquiv
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule) :
    L₁.reduction ≃ₗ[IsLocalRing.ResidueField A] L₂.reduction := by
  refine
    { toFun := reductionLinearEquivOfLinearEquivA e
      invFun := (reductionLinearEquivOfLinearEquivA e).symm
      left_inv := (reductionLinearEquivOfLinearEquivA e).left_inv
      right_inv := (reductionLinearEquivOfLinearEquivA e).right_inv
      map_add' := (reductionLinearEquivOfLinearEquivA e).map_add
      map_smul' := ?_ }
  intro c x
  refine Quotient.inductionOn' c ?_
  intro a
  refine Quotient.inductionOn' x ?_
  intro y
  change
    reductionLinearEquivOfLinearEquivA e
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
            IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk y : L₁.reduction)) = _
  rw [StableLattice.reduction_smul_mk (L := L₁) a y]
  rw [reductionLinearEquivOfLinearEquivA_apply_mk e]
  calc
    (Submodule.Quotient.mk (e (a • y)) : L₂.reduction) =
        Submodule.Quotient.mk (a • e y) := by
          simp
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
          IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk (e y) : L₂.reduction) := by
          rw [StableLattice.reduction_smul_mk (L := L₂)]
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
          IsLocalRing.ResidueField A) •
          (reductionLinearEquivOfLinearEquivA e
            (Submodule.Quotient.mk y)) := by
          rw [reductionLinearEquivOfLinearEquivA_apply_mk e]

/-- Helper for Exercise 15-15.2-6: on represented quotient classes, the residue-field reduction
equivalence induced by a lattice linear equivalence is still the obvious quotient class. -/
@[simp] theorem reductionLinearEquivOfLinearEquiv_apply_mk
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (x : L₁.toSubmodule) :
    reductionLinearEquivOfLinearEquiv e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := by
  exact reductionLinearEquivOfLinearEquivA_apply_mk e x

/-- Helper for Exercise 15-15.2-6: an intertwining equivalence of stable lattices descends to a
residue-field linear equivalence of the reductions. -/
noncomputable def reductionLinearEquivOfIntertwining
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (_he : ∀ g : G', ∀ x : L₁.toSubmodule,
      e (L₁.toRepresentation g x) = L₂.toRepresentation g (e x)) :
    L₁.reduction ≃ₗ[IsLocalRing.ResidueField A] L₂.reduction :=
  reductionLinearEquivOfLinearEquiv e

/-- Helper for Exercise 15-15.2-6: on represented quotient classes, the descended reduction
equivalence from an intertwining lattice equivalence is still the obvious quotient class. -/
@[simp] theorem reductionLinearEquivOfIntertwining_apply_mk
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (he : ∀ g : G', ∀ x : L₁.toSubmodule,
      e (L₁.toRepresentation g x) = L₂.toRepresentation g (e x))
    (x : L₁.toSubmodule) :
    reductionLinearEquivOfIntertwining e he (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := by
  exact reductionLinearEquivOfLinearEquiv_apply_mk e x

/-- Helper for Exercise 15-15.2-6: an intertwining equivalence of stable lattices yields an
equivalence of the corresponding reduction representations. -/
noncomputable def reductionRepresentationEquivOfIntertwining
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (he : ∀ g : G', ∀ x : L₁.toSubmodule,
      e (L₁.toRepresentation g x) = L₂.toRepresentation g (e x)) :
    L₁.reductionRepresentation.Equiv L₂.reductionRepresentation := by
  -- Build the reduced intertwiner once at the stable-lattice level so later callers only need a
  -- thin specialization at their chosen owner spellings.
  let f :
      L₁.reductionRepresentation.IntertwiningMap L₂.reductionRepresentation :=
    (reductionLinearEquivOfIntertwining e he).toLinearMap.intertwiningMap_of_isIntertwiningMap
      L₁.reductionRepresentation L₂.reductionRepresentation
      (fun g x ↦ by
        -- Check intertwining on represented quotient classes and then extend by quotient
        -- extensionality.
        refine Quotient.inductionOn' x ?_
        intro y
        change
          reductionLinearEquivOfIntertwining e he
              (Submodule.Quotient.mk (L₁.toRepresentation g y)) =
            L₂.reductionRepresentation g
              (reductionLinearEquivOfIntertwining e he (Submodule.Quotient.mk y))
        rw [reductionLinearEquivOfIntertwining_apply_mk e he]
        rw [reductionLinearEquivOfIntertwining_apply_mk e he]
        rw [StableLattice.reductionRepresentation_apply_mk]
        congr 1
        exact he g y)
  exact f.ofBijective (reductionLinearEquivOfIntertwining e he).bijective

/-- Helper for Exercise 15-15.2-6: an intertwining equivalence of stable lattices yields an
equivalence of the corresponding reduction representations. -/
theorem reductionNonemptyEquivOfIntertwining
    {L₁ : StableLattice A ρ₁} {L₂ : StableLattice A ρ₂}
    (e : L₁.toSubmodule ≃ₗ[A] L₂.toSubmodule)
    (he : ∀ g : G', ∀ x : L₁.toSubmodule,
      e (L₁.toRepresentation g x) = L₂.toRepresentation g (e x)) :
    Nonempty (L₁.reductionRepresentation.Equiv L₂.reductionRepresentation) := by
  -- Reuse the direct constructor so downstream code can choose either the concrete equivalence or
  -- its `Nonempty` wrapper without rebuilding the reduction transport proof.
  exact ⟨reductionRepresentationEquivOfIntertwining e he⟩

end StableLattice

end ReductionTransport

end ThompsonExercise
