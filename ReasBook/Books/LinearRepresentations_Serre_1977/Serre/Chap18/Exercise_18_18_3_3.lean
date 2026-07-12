import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLiftDecomposition
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u x

namespace Representation

section

open PrimeToPRoot FDRep

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
variable {ι : Type x}

/-- Throughout this file we work in Serre's `p`-modular system `(K, A, k)`: `A` is a discrete
valuation ring with fraction field `K` of characteristic `0` and (algebraically closed) residue
field `k = A/𝔪` of characteristic `p`.  This is the faithful setting of Exercise 18.6, in which the
decomposition map and the Brauer/ordinary character comparison both make sense. -/
local notation "k" => IsLocalRing.ResidueField A

-- The Fong–Swan import (`Theorem_17_17_6_1`) brings the global instance `Field.henselian` (every
-- field is a Henselian local ring) into scope.  Combined with the residue-field instances it makes
-- type-class search on `p`-regular class functions loop on `Field.henselian`/residue-field
-- instances
-- (an unbounded storm).  We never need `Field.henselian` here (the lift uses the explicit
-- `[HenselianLocalRing A]` on the DVR `A`), so removing it from instance search restores fast
-- resolution — no heartbeat limit is changed.
attribute [-instance] Field.henselian

/- Domain-style sampling:
* primary domain: Brauer and ordinary characters on the canonical owner
  `PRegularConjClass G p`;
* relevant owner declarations inspected upstream in the chapter/project:
  `FDRep.ordinaryCharacterOnPRegularConjClass`,
  `FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype`,
  `FDRep.modularCharacterOnPRegularConjClass`,
  `FDRep.modularCharacterOnPRegularConjClass_ofSubtype`,
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`,
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply`,
  `Representation.exists_residueFieldLift_of_isIrreducible_of_isPSolvable`;
* best owner abstraction: class functions on `PRegularConjClass G p`, with ordinary and modular
  character constructions treated as the source-facing views on that owner;
* primitive data: for parts `(1)` and `(2)`, an injective multiplicative lift
  `PrimeToPRoot p k →* Kˣ` and a simple modular representation `S`; for part `(3)`, only the
  same multiplicative lift, together with a complete pairwise-nonisomorphic irreducible family
  `E : ι → FDRep k G`, a simple ordinary representation `X`, and its nonnegative integral
  expansion in the Brauer-character basis;
* derived API: the existence and uniqueness statements in Exercise `18-18.3-3`, phrased on the
  canonical Brauer and restricted ordinary character owners.

Layer triage:
* source-facing: the three exercise statements comparing simple Brauer characters with restricted
  ordinary characters;
* core/canonical: `PRegularConjClass G p → K`;
* bridge/view: `PrimeToPRoot.toFieldLift`, used only where the source-facing statement genuinely
  starts from a multiplicative lift into `Kˣ`;
  `Representation.exists_residueFieldLift_of_isIrreducible_of_isPSolvable` stays only as a
  proof-route bridge rather than as public ambient data.
-/

/-- Helper for Exercise 18-18.3-3: a finite-dimensional representation is canonically isomorphic to
the `FDRep` rebuilt from its own underlying representation. -/
private noncomputable def fdRepIsoOfRho_local
    {F : Type u} [Field F] {H : Type u} [Group H] (τ : FDRep F H) :
    τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Exercise 18-18.3-3: **Fong–Swan** in Serre's `p`-modular system `(K, A, k)` with
`G` `p`-solvable says that the Brauer character of a simple `k[G]`-module `S`, viewed on
`PRegularConjClass G p` through a multiplicative lift of the prime-to-`p` roots of unity into
`Kˣ`, is the restriction to the `p`-regular classes of the ordinary character of some simple
`K[G]`-module.

Faithful framing: `A` is a Henselian discrete valuation ring with fraction field `K` and residue
field `k`; `hred` says the lift `lift` is the reduction-compatible Teichmüller lift, and `hω` says
`K` contains the relevant roots of unity (Serre's "`K` sufficiently large"). -/
theorem simple_modularCharacter_exists_restricted_ordinary_character
    [HenselianLocalRing A]
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) (hp : Nat.Prime p) (hG : IsPSolvable p G)
    (hlift : Function.Injective lift)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (hS : Simple S) :
    ∃ X : FDRep K G,
      Simple X ∧
        modularCharacterOnPRegularConjClass S (toFieldLift lift) =
          ordinaryCharacterOnPRegularConjClass p X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Simple S := hS
  haveI hSirr : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  -- Fong–Swan: lift the simple residue-field module to a free finitely generated `A[G]`-module.
  obtain ⟨P, _, _, _, _, ρA, red, hlift_resid⟩ :=
    exists_residueFieldLift_of_isIrreducible_of_isPSolvable (A := A) hp hG S.ρ
  -- The canonical stable lattice in its scalar extension to `K` reduces back to `S`.
  obtain ⟨L, hLiso⟩ :=
    residueFieldLift_scalarExtension_reduction_iso (A := A) (K := K) (G := G) S.ρ ρA red hlift_resid
  rcases hLiso with ⟨eL⟩
  -- Canonical isomorphism `S ≅ FDRep.of S.ρ`.
  have eS : S ≅ FDRep.of S.ρ := fdRepIsoOfRho_local S
  refine ⟨residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA, ?_, ?_⟩
  · -- Simplicity: the reduction of the lattice is `S`, which is simple, so the lift is irreducible.
    haveI : Simple (FDRep.of S.ρ) := CategoryTheory.Simple.of_iso eS.symm
    haveI : Simple (FDRep.of L.reductionRepresentation) := CategoryTheory.Simple.of_iso eL
    have hredIrr : Representation.IsIrreducible L.reductionRepresentation :=
      FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
    haveI :
        Representation.IsIrreducible
          (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).ρ :=
      simple_reduction_implies_isIrreducible _ L hredIrr
    exact FDRep.simple_of_isIrreducible _
  · -- Character comparison via the decomposition bridge (Theorem 18.2.1 / Corollary 18.2.4 core).
    have hbridge :
        virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
            ((decompositionHom A K G)
              [residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA]₀) =
          ordinaryCharacterOnPRegularConjClass p
            (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA) :=
      virtualModularCharacterOnPRegularConjClass_decomposition_finiteRepClass_eq
        (p := p) (A := A) (K := K) (G := G) lift hred hω
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA) L
    have hd :
        (decompositionHom A K G)
            [residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA]₀ =
          [FDRep.of S.ρ]₀ :=
      decompositionHom_fdRepOf_scalarExtension_eq_of_isResidueFieldLift
        (A := A) (K := K) (G := G) S.ρ ρA red hlift_resid
    rw [← hbridge, hd,
      show ([FDRep.of S.ρ]₀ : R₀[k](G)) = [S]₀ from
        finiteRepGrothendieckClass_eq_of_nonempty_iso ⟨eS.symm⟩,
      virtualModularCharacterOnPRegularConjClass_class]

/-- Helper for Exercise 18-18.3-3: a simple finite-dimensional representation has positive
dimension. -/
private lemma simple_fdRep_finrank_pos
    (V : FDRep K G) [Simple V] :
    0 < Module.finrank K V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero V hzero
  letI : Nontrivial V := hV_nontriv
  -- Positive dimension is the linear-algebra witness that the identity character value is
  -- nonzero for a simple representation.
  exact Module.finrank_pos

/-- Helper for Exercise 18-18.3-3: every finite group over a field admits a complete pairwise
nonisomorphic family of simple finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_explicit_local
    {F : Type u} [Field F]
    {H : Type u} [Group H] [Finite H] :
    ∃ (κ : Type (u + 1)) (π : κ → FDRep F H),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F H // Simple τ }
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
  let κ : Type (u + 1) := Quotient r
  let π : κ → FDRep F H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot admit an isomorphism.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : κ) = (⟦Quotient.out q'⟧ : κ) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : κ) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : κ) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : κ := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨κ, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 18-18.3-3: once the coordinates of an element in a `ℤ`-basis are known to
be nonnegative, that element is already a finite `ℕ`-linear combination of the same basis
vectors. -/
private lemma basis_eq_nat_sum_of_nonneg_repr
    {κ : Type*} {M : Type*} [AddCommGroup M]
    (b : Module.Basis κ ℤ M)
    (x : M)
    (hx : ∀ i, 0 ≤ b.repr x i) :
    ∃ c : κ →₀ ℕ, x = c.sum fun i m ↦ (m : ℤ) • b i := by
  classical
  let r : κ →₀ ℤ := b.repr x
  let c : κ →₀ ℕ :=
    Finsupp.onFinset r.support (fun i ↦ Int.toNat (r i)) fun i hi ↦ by
      exact Finsupp.mem_support_iff.mpr <| by
        intro hzero
        apply hi
        simp [hzero]
  refine ⟨c, ?_⟩
  -- Rebuild `x` from its basis coordinates, now viewed as natural-number coefficients.
  calc
    x = r.sum (fun i a ↦ a • b i) := by
      simpa [r, Finsupp.linearCombination_apply, Finsupp.sum] using
        (b.linearCombination_repr x).symm
    _ = Finset.sum r.support (fun i ↦ ((Int.toNat (r i) : ℕ) : ℤ) • b i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Int.toNat_of_nonneg (hx i)]
    _ = c.sum (fun i m ↦ (m : ℤ) • b i) := by
      symm
      simpa [c] using
        (Finsupp.onFinset_sum
          (s := r.support)
          (f := fun i ↦ Int.toNat (r i))
          (g := fun i m ↦ (m : ℤ) • b i)
          (hf := fun i hi ↦ by
            exact Finsupp.mem_support_iff.mpr <| by
              intro hzero
              apply hi
              simp [hzero])
          (hg := fun _ ↦ by simp))

/-- Helper for Exercise 18-18.3-3: nested finite-support sums with natural coefficients flatten
after casting the coefficients into any scalar semiring. -/
private lemma finsupp_sum_natCast_smul_sum_eq_sum_sum
    {κ : Type*} {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ι →₀ ℕ) (m : ι → κ →₀ ℕ) (v : κ → M) :
    n.sum (fun i a ↦ (a : R) • ((m i).sum fun j b ↦ (b : R) • v j)) =
      (n.sum fun i a ↦ a • m i).sum fun j b ↦ (b : R) • v j := by
  let Φ : (κ →₀ ℕ) →+ M :=
    { toFun := fun d ↦ d.sum fun j b ↦ (b : R) • v j
      map_zero' := by simp
      map_add' := fun d₁ d₂ ↦
        Finsupp.sum_add_index' (fun j ↦ by simp) (fun j a b ↦ by push_cast; rw [add_smul]) }
  have hmap : Φ (n.sum fun i a ↦ a • m i) = n.sum fun i a ↦ Φ (a • m i) := by
    simp only [Finsupp.sum, map_sum]
  -- Compare the nested expression with the additive-hom image of the flattened coefficient
  -- family; the only arithmetic bridge is `ℕ`-scalar multiplication versus scalar multiplication
  -- by the cast natural number.
  calc
    n.sum (fun i a ↦ (a : R) • ((m i).sum fun j b ↦ (b : R) • v j))
        = n.sum (fun i a ↦ Φ (a • m i)) := by
          refine Finsupp.sum_congr fun i _ ↦ ?_
          rw [map_nsmul]
          exact Nat.cast_smul_eq_nsmul (R := R) (n := n i) (b := Φ (m i))
    _ = Φ (n.sum fun i a ↦ a • m i) := hmap.symm
    _ = (n.sum fun i a ↦ a • m i).sum (fun j b ↦ (b : R) • v j) := rfl

/-- Helper for Exercise 18-18.3-3: once the simple-class coordinates of a Grothendieck class are
known to be nonnegative in a complete simple basis, that class is already a finite
`ℕ`-combination of the corresponding simple classes. -/
lemma finiteRep_class_eq_nat_sum_of_complete_simple_family_of_nonneg
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (x : R₀[k](G))
    (hx :
      ∀ i,
        0 ≤
          (simple_finiteRep_classes_basis_of_complete_family
            E hE_pairwise hE_complete).repr x i) :
    ∃ c : ι →₀ ℕ,
      x = c.sum (fun i m ↦ (m : ℤ) • [E i]₀) := by
  let b :=
    simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete
  obtain ⟨c, hc⟩ := basis_eq_nat_sum_of_nonneg_repr b x hx
  -- Replace the basis vectors by the matching simple classes of the chosen complete family.
  refine ⟨c, ?_⟩
  simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using hc

/-- Helper for Exercise 18-18.3-3: over the residue field `k = A/𝔪`, the coordinate of a
Grothendieck class `[M]₀` in a complete simple basis is nonnegative, because Chapter `16` identifies
it with a fixed-simple Jordan–Hölder multiplicity, which is a nonnegative integer. -/
lemma simple_class_basis_coord_nonneg_over_field
    [Fact p.Prime]
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (M : FDRep k G)
    (i : ι) :
    0 ≤
      (simple_finiteRep_classes_basis_of_complete_family
        E hE_pairwise hE_complete).repr [M]₀ i := by
  classical
  -- A complete pairwise-nonisomorphic simple family over the residue field `k` is finite: its
  -- Brauer characters form a basis of the finite-dimensional space of `p`-regular class functions
  -- (Theorem 18.2.1).  (The char-`0` route `IsCompleteIrreducibleFamily.finite_index` is unusable
  -- here since `NeZero (|G| : k)` fails in characteristic `p`.)
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite _
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite ι :=
    Module.Finite.finite_basis
      (Representation.irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
        E hE_pairwise hE_complete)
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Simple (E i) := hE_complete.isSimple i
  -- Identify the basis coordinate with the fixed-simple multiplicity of `E i` in `[M]₀` and use
  -- that the multiplicity hom is nonnegative on honest module classes.
  rw [show
        (simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete).repr [M]₀ i =
          simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (E i) [M]₀ from
        (simple_basis_coord_eq_fixed_simple_multiplicity_local
          (A := A) (G := G) (S := E i) E hE_pairwise hE_complete i ⟨Iso.refl _⟩ [M]₀)]
  exact simple_factor_multiplicity_hom_fixed_local_class_nonneg (A := A) (G := G) (E i) M

/-- Helper for Exercise 18-18.3-3: each restricted ordinary character of a simple ordinary module
should be a finite `ℕ`-combination of the Brauer-character basis attached to a complete simple
modular family. -/
lemma restricted_ordinary_character_eq_nonnegative_modular_sum_of_simple
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hp : Nat.Prime p)
    (X : FDRep K G) [Simple X] :
    ∃ c : ι →₀ ℕ,
      (c.sum fun i m ↦
        (m : K) • modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)) =
          ordinaryCharacterOnPRegularConjClass p X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- Choose a stable `A`-lattice in `X` and reduce it modulo `𝔪`.  The decomposition class
  -- `d[X]₀` is the honest module class of that reduction, hence its simple-basis coordinates are
  -- the (nonnegative) decomposition numbers `D_{E_i, X}`.
  obtain ⟨L⟩ := Representation.exists_stableLattice (A := A) X.ρ
  have hdred : decompositionHom A K G [X]₀ = [FDRep.of L.reductionRepresentation]₀ :=
    decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L
  obtain ⟨c, hc⟩ :=
    finiteRep_class_eq_nat_sum_of_complete_simple_family_of_nonneg
      (E := E) hE_pairwise hE_complete (decompositionHom A K G [X]₀)
      (fun i ↦ by
        rw [hdred]
        exact simple_class_basis_coord_nonneg_over_field E hE_pairwise hE_complete
          (FDRep.of L.reductionRepresentation) i)
  refine ⟨c, ?_⟩
  -- Apply the descended virtual modular character (an additive hom) to the lattice identity: on the
  -- left the decomposition bridge gives the restricted ordinary character of `X`, and on each
  -- generator the Brauer-character evaluation `vMC [E i]₀ = φ_{E i}`.
  have hbridge :
      virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
          (decompositionHom A K G [X]₀) =
        ordinaryCharacterOnPRegularConjClass p X :=
    virtualModularCharacterOnPRegularConjClass_decomposition_finiteRepClass_eq
      (p := p) (A := A) (K := K) (G := G) lift hred hω X L
  have hpush :
      virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
          (c.sum fun i m ↦ (m : ℤ) • [E i]₀) =
        c.sum (fun i m ↦
          virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
            ((m : ℤ) • [E i]₀)) := by
    simp only [Finsupp.sum, map_sum]
  rw [← hbridge, hc, hpush]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [map_zsmul, virtualModularCharacterOnPRegularConjClass_class,
    Nat.cast_smul_eq_nsmul (R := K), Nat.cast_smul_eq_nsmul (R := ℤ)]

/-- Helper for Exercise 18-18.3-3: if a nonnegative combination of nonzero nonnegative columns is
the singleton basis vector at `j`, then exactly one outer coefficient survives, and its column is
the same singleton basis vector. -/
lemma nonnegative_column_sum_eq_singleton
    {κ : Type*}
    (n : ι →₀ ℕ)
    (m : ι → κ →₀ ℕ)
    (j : κ)
    (hm_nonzero : ∀ i, n i ≠ 0 → m i ≠ 0)
    (h :
      n.sum (fun i a ↦ a • m i) = Finsupp.single j 1) :
    ∃ i, n = Finsupp.single i 1 ∧ m i = Finsupp.single j 1 := by
  classical
  have hcoord_zero :
      ∀ {b : κ}, b ≠ j → ∀ i, n i ≠ 0 → m i b = 0 := by
    intro b hk i hi
    -- Off the distinguished coordinate `j`, every summand must vanish because the total sum is
    -- the singleton column `single j 1`.
    have hk_sum :
        Finset.sum n.support (fun l ↦ n l * m l b) = 0 := by
      have hk_eval := congrArg (fun c : κ →₀ ℕ ↦ c b) h
      simpa [Finsupp.sum, Finsupp.single_apply, hk] using hk_eval
    have hk_terms :
        ∀ l ∈ n.support, n l * m l b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦ Nat.zero_le _).mp hk_sum
    have hi_mem : i ∈ n.support := Finsupp.mem_support_iff.mpr hi
    exact (Nat.mul_eq_zero.mp (hk_terms i hi_mem)).resolve_left hi
  have hcolumn_single :
      ∀ i, n i ≠ 0 → m i = Finsupp.single j (m i j) := by
    intro i hi
    -- A supported column has no mass away from `j`, so it is a singleton column.
    ext b
    by_cases hk : b = j
    · subst hk
      simp
    · simp [hk, hcoord_zero hk i hi]
  let dj : ι →₀ ℕ :=
    Finsupp.onFinset n.support (fun i ↦ n i * m i j) fun i hi ↦
      Finsupp.mem_support_iff.mpr <| by
        intro hni
        exact hi (by simp [hni])
  have hsum_j :
      Finset.sum n.support (fun i ↦ n i * m i j) = 1 := by
    -- The `j`-coordinate of the singleton equality is the scalar identity `∑ n_i m_i(j) = 1`.
    have hj_eval := congrArg (fun c : κ →₀ ℕ ↦ c j) h
    simpa [Finsupp.sum, Finsupp.single_apply] using hj_eval
  have hdj_sum : dj.sum (fun _ a ↦ a) = 1 := by
    -- Package the `j`-coordinate products into a finitely supported family so `sum_eq_one_iff`
    -- can isolate the unique surviving index.
    calc
      dj.sum (fun _ a ↦ a) = Finset.sum n.support (fun i ↦ n i * m i j) := by
        simpa [dj] using
          (Finsupp.onFinset_sum
            (s := n.support)
            (f := fun i ↦ n i * m i j)
            (g := fun _ a ↦ a)
            (hf := fun i hi ↦
              Finsupp.mem_support_iff.mpr <| by
                intro hni
                exact hi (by simp [hni]))
            (hg := fun _ ↦ rfl))
      _ = 1 := hsum_j
  obtain ⟨i₀, hsingle_dj⟩ := (Finsupp.sum_eq_one_iff dj).mp hdj_sum
  have hsupported_unique : ∀ i, n i ≠ 0 → i = i₀ := by
    intro i hi
    have hmi_ne : m i ≠ 0 := hm_nonzero i hi
    have hmij_ne : m i j ≠ 0 := by
      intro hmij
      have hmi_single : m i = Finsupp.single j (m i j) := hcolumn_single i hi
      have hmi_zero : m i = 0 := by
        ext b
        by_cases hk : b = j
        · subst hk
          simp [hmij] at hmi_single ⊢
        · simp [hcoord_zero hk i hi]
      exact hmi_ne hmi_zero
    have hdj_ne : dj i ≠ 0 := by
      simpa [dj] using Nat.mul_ne_zero hi hmij_ne
    by_contra hii
    have : dj i = 0 := by
      simp [hsingle_dj, hii]
    exact hdj_ne this
  have hprod_i₀ : n i₀ * m i₀ j = 1 := by
    -- The distinguished index contributes the unique nonzero `j`-coordinate product.
    simpa [dj] using congrArg (fun c : ι →₀ ℕ ↦ c i₀) hsingle_dj
  have hn_i₀ : n i₀ = 1 := Nat.eq_one_of_mul_eq_one_right hprod_i₀
  have hm_i₀j : m i₀ j = 1 := Nat.eq_one_of_mul_eq_one_left hprod_i₀
  have hn_single : n = Finsupp.single i₀ 1 := by
    -- Since any supported index must be `i₀`, the outer coefficient family is itself a singleton.
    ext i
    by_cases hi : i = i₀
    · subst hi
      simp [hn_i₀]
    · have hni : n i = 0 := by
        by_contra hni_ne
        exact hi (hsupported_unique i hni_ne)
      simp [hi, hni]
  have hm_single : m i₀ = Finsupp.single j 1 := by
    -- The surviving column is concentrated at `j`, and its `j`-coordinate is forced to be `1`.
    simpa [hm_i₀j] using hcolumn_single i₀ (by simp [hn_i₀])
  exact ⟨i₀, hn_single, hm_single⟩

/-- Helper for Exercise 18-18.3-3: once a complete simple modular family is fixed, a nonnegative
combination of its Brauer characters can equal one basis vector only for the corresponding
singleton coefficient family. -/
lemma modular_basis_singleton_of_eq_sum
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hp : Nat.Prime p)
    (i : ι) (n : ι →₀ ℕ)
    (h :
      modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) =
        n.sum fun j m ↦
          (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift)) :
    n = Finsupp.single i 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  let nK : ι →₀ K := n.mapRange (fun a : ℕ ↦ (a : K)) (by simp)
  have hsupp_nK : nK.support = n.support := by
    simpa [nK] using
      (Finsupp.support_mapRange_of_injective
        (e := fun a : ℕ ↦ (a : K)) (by simp) n (Nat.cast_injective (R := K)))
  have hlinear :
      Finsupp.linearCombination K b nK =
        n.sum fun j m ↦
          (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift) := by
    ext c
    rw [Finsupp.linearCombination_apply, Finsupp.sum, hsupp_nK, Finsupp.sum]
    simp [nK, b, Finsupp.mapRange_apply]
  have hrepr_rhs :
      b.repr
        (n.sum fun j m ↦
          (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift)) = nK := by
    -- Rewrite the Brauer-character sum as the basis linear combination with coefficient family
    -- `nK`, then apply the basis coordinate identity.
    calc
      b.repr
          (n.sum fun j m ↦
            (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift))
        = b.repr (Finsupp.linearCombination K b nK) := by rw [hlinear.symm]
      _ = nK := b.repr_linearCombination nK
  have hrepr_lhs :
      b.repr (modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)) =
        Finsupp.single i (1 : K) := by
    -- The `i`-th irreducible Brauer character is the `i`-th basis vector.
    rw [← irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
      (p := p) (K := K) (G := G) lift hlift E hE_pairwise hE_complete i]
    exact b.repr_self i
  have hnK :
      nK = Finsupp.single i (1 : K) := by
    calc
      nK = b.repr
          (n.sum fun j m ↦
            (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift)) :=
              hrepr_rhs.symm
      _ = b.repr (modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)) := by
            rw [← h]
      _ = Finsupp.single i (1 : K) := hrepr_lhs
  ext j
  -- Compare the `j`-th coordinates and use injectivity of the natural-number cast into `K`.
  have hj := congrArg (fun c : ι →₀ K ↦ c j) hnK
  by_cases hij : j = i
  · subst hij
    apply Nat.cast_injective (R := K)
    simpa [nK] using hj
  · apply Nat.cast_injective (R := K)
    simpa [nK, Finsupp.single_apply, hij] using hj

/-- Helper for Exercise 18-18.3-3: a local copy of the attached-root sum transport lemma
(`attached_sum_eq_of_eq` is `private` in `Proposition_18_18_1_2`). -/
private theorem attached_sum_eq_of_eq_iso_local
    {B : Type*} [AddCommMonoid B]
    {m₁ m₂ : Multiset k} (hm : m₁ = m₂)
    (f₁ : {x // x ∈ m₁} → B) (f₂ : {x // x ∈ m₂} → B)
    (hfun : ∀ μ : {x // x ∈ m₁}, f₁ μ = f₂ ⟨μ.1, hm ▸ μ.2⟩) :
    (Multiset.map f₁ m₁.attach).sum = (Multiset.map f₂ m₂.attach).sum := by
  subst hm
  refine congrArg Multiset.sum ?_
  apply Multiset.map_congr rfl
  intro μ _
  exact hfun μ

/-- Helper for Exercise 18-18.3-3: an isomorphism of modular representations preserves the
descended Brauer character on `PRegularConjClass G p`. -/
private theorem modularCharacterOnPRegularConjClass_eq_of_iso
    (lift : PrimeToPRoot p k →* Kˣ)
    {E₁ E₂ : FDRep k G}
    (e : E₁ ≅ E₂) :
    modularCharacterOnPRegularConjClass E₁ (toFieldLift lift) =
      modularCharacterOnPRegularConjClass E₂ (toFieldLift lift) := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s]
  -- Evaluate both descended characters on the same `p`-regular representative.
  rw [← hs, FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  -- The underlying modular characters agree because an isomorphism conjugates the action.
  simpa using
    congrFun
      (by
        haveI : Module.Finite k ((forget₂ (FDRep k G) (Rep k G)).obj E₁) :=
          inferInstanceAs (Module.Finite k E₁.V)
        haveI : Module.Finite k ((forget₂ (FDRep k G) (Rep k G)).obj E₂) :=
          inferInstanceAs (Module.Finite k E₂.V)
        let eρ := Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)
        funext t
        have hchar : (E₂.ρ t.1).charpoly = (E₁.ρ t.1).charpoly := by
          rw [← Representation.Equiv.conj_apply_self (ρ := E₁.ρ) (σ := E₂.ρ) t.1 eρ]
          exact LinearEquiv.charpoly_conj eρ.toLinearEquiv (E₁.ρ t.1)
        have hroots : (E₂.ρ t.1).charpoly.roots = (E₁.ρ t.1).charpoly.roots := by
          simpa using congrArg Polynomial.roots hchar
        change
          (Multiset.map
            (fun μ : { x // x ∈ (E₁.ρ t.1).charpoly.roots } ↦
              PrimeToPRoot.toFieldLift lift
                (charpolyRoot_primeToPRoot (p := p) E₁.ρ t.2 μ.2))
            (E₁.ρ t.1).charpoly.roots.attach).sum =
          (Multiset.map
            (fun μ : { x // x ∈ (E₂.ρ t.1).charpoly.roots } ↦
              PrimeToPRoot.toFieldLift lift
                (charpolyRoot_primeToPRoot (p := p) E₂.ρ t.2 μ.2))
            (E₂.ρ t.1).charpoly.roots.attach).sum
        symm
        exact attached_sum_eq_of_eq_iso_local hroots
          (fun μ ↦
            PrimeToPRoot.toFieldLift lift
              (charpolyRoot_primeToPRoot (p := p) E₂.ρ t.2 μ.2))
          (fun μ ↦
            PrimeToPRoot.toFieldLift lift
              (charpolyRoot_primeToPRoot (p := p) E₁.ρ t.2 μ.2))
          (fun μ ↦ by
            apply congrArg (PrimeToPRoot.toFieldLift lift)
            ext
            simp [charpolyRoot_primeToPRoot_coe]))
      s

-- Proof sketch: once part `(1)` identifies the Brauer character of `S` with one restricted
-- ordinary character, expand that ordinary character in the complete simple family `F` and apply
-- `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions` to the simple modular
-- characters to conclude that any nonnegative integral expansion of that class function in the
-- family must be a single basis vector.
/-- Helper for Exercise 18-18.3-3: if the Brauer character of a simple `k[G]`-module is viewed
through a chosen injective multiplicative lift of the prime-to-`p` roots of unity into `Kˣ`, then
every nonnegative integral expansion of that class function in the restricted ordinary characters
attached to `F` is a single summand. -/
theorem simple_modularCharacter_unique_nonnegative_expansion
    (lift : PrimeToPRoot p k →* Kˣ) (F : ι → FDRep K G) (S : FDRep k G)
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (hlift : Function.Injective lift)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (hF_pairwise : PairwiseNonisomorphic F)
    (hF_complete : IsCompleteIrreducibleFamily F) (hS : Simple S)
    (n : ι →₀ ℕ)
    (hn :
      modularCharacterOnPRegularConjClass S (toFieldLift lift) =
        n.sum fun i m ↦ (m : K) • ordinaryCharacterOnPRegularConjClass p (F i)) :
    ∃ i, n = Finsupp.single i 1 := by
  classical
  obtain ⟨κ, E, hE_pairwise, hE_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_explicit_local (F := k) (H := G)
  obtain ⟨jS, hjS⟩ := hE_complete.exists_iso S hS
  choose m hm using
    fun i ↦ by
      letI : Simple (F i) := hF_complete.isSimple i
      exact
        restricted_ordinary_character_eq_nonnegative_modular_sum_of_simple
          (p := p) (K := K) (G := G)
          lift hred hω E hE_pairwise hE_complete hp (F i)
  let c : κ →₀ ℕ := n.sum fun i a ↦ a • m i
  have hm_nonzero : ∀ i, n i ≠ 0 → m i ≠ 0 := by
    intro i hi hmi
    have hzero_char :
        ordinaryCharacterOnPRegularConjClass p (F i) = 0 := by
      -- If the inner column were zero, its ordinary character expansion would vanish.
      simp only [← hm i, hmi, Finsupp.sum_zero_index]
    have hdim_zero :
        (Module.finrank K (F i) : K) = 0 := by
      let c1 : PRegularConjClass G p := PRegularConjClass.ofSubtype p ⟨1, isPRegular_one p⟩
      have hEval := congrFun hzero_char c1
      simpa [c1, FDRep.char_one] using hEval
    letI : Simple (F i) := hF_complete.isSimple i
    have hdim_pos : 0 < Module.finrank K (F i) :=
      simple_fdRep_finrank_pos (K := K) (G := G) (V := F i)
    exact
      (Nat.cast_ne_zero.2 (Nat.ne_of_gt hdim_pos)) hdim_zero
  have hsingle_basis :
      c = Finsupp.single jS 1 := by
    -- Rewrite the outer sum through the inner nonnegative columns and compare with the fixed
    -- Brauer basis vector representing `S`.
    apply
      modular_basis_singleton_of_eq_sum
        (p := p) (K := K) (G := G)
        lift hlift E hE_pairwise hE_complete hp jS c
    calc
      modularCharacterOnPRegularConjClass (E jS) (toFieldLift lift) =
          modularCharacterOnPRegularConjClass S (toFieldLift lift) := by
            rcases hjS with ⟨e⟩
            symm
            exact modularCharacterOnPRegularConjClass_eq_of_iso
              (p := p) (K := K) (G := G) lift e
      _ =
          n.sum fun i a ↦ (a : K) • ordinaryCharacterOnPRegularConjClass p (F i) := hn
      _ =
          n.sum fun i a ↦
            (a : K) •
              (m i).sum fun j m_ij ↦
                (m_ij : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift) := by
            simp_rw [hm]
      _ =
          c.sum fun j a ↦
            (a : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift) := by
            -- Flatten the two-stage nonnegative expansion into one coefficient family through the
            -- additive-hom flattening lemma.
            simpa [c] using
              (finsupp_sum_natCast_smul_sum_eq_sum_sum
                (R := K) (n := n) (m := m)
                (v := fun j ↦
                  modularCharacterOnPRegularConjClass (E j) (toFieldLift lift)))
  obtain ⟨i, hi, _⟩ :=
    nonnegative_column_sum_eq_singleton (n := n) (m := m) (j := jS) hm_nonzero <| by
      simpa [c] using hsingle_basis
  exact ⟨i, hi⟩

/-- Helper for Exercise 18-18.3-3: the restricted ordinary character on `PRegularConjClass G p` is
invariant under isomorphism of `K[G]`-modules. -/
private theorem ordinaryCharacterOnPRegularConjClass_eq_of_iso
    {X Y : FDRep K G} (e : X ≅ Y) :
    ordinaryCharacterOnPRegularConjClass p X = ordinaryCharacterOnPRegularConjClass p Y := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s]
  rw [← hs, FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype,
    FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype, FDRep.char_iso e]

-- Proof sketch: express `χ_X|_{G_reg}` as a nonnegative integral combination of the Brauer basis
-- of `E` (decomposition numbers, helper above).  For `p`-solvable `G`, part `(1)` (Fong–Swan)
-- lifts each `E i` to a simple ordinary module, isomorphic to some `F j`; rewriting through these
-- turns the Brauer expansion into a nonnegative ordinary expansion in `F`.  Serre's condition `(b)`
-- then forces that ordinary expansion to be a single summand, and the column-singleton lemma pushes
-- the singleton back to the Brauer side, giving `χ_X|_{G_reg} = φ_{E i}` for a single `i`.
/-- Exercise 18-18.3-3 (3) — the converse direction of the Fong–Swan characterization.

⚠️ FAITHFULNESS NOTE: the naive converse "a simple `K[G]`-module `X` whose restricted ordinary
character expands in the Brauer basis has that character equal to a *single* Brauer character" is
**FALSE** (`G = 𝔖₄`, `p = 2`: `χ₄ = φ₁ + φ₂` on `G_reg`, with `χ₄` simple — Serre §18.5).  The
correct converse is Serre's condition `(b)`: if every nonnegative integral expansion of
`χ_X|_{G_reg}` in the *restricted ordinary characters* of a complete simple `K[G]`-family `F` is a
single summand `(hb)`, then `χ_X|_{G_reg}` is a single Brauer character of the complete simple
modular family `E`. -/
theorem simple_restricted_ordinary_character_eq_modularCharacter
    [HenselianLocalRing A]
    (lift : PrimeToPRoot p k →* Kˣ) (E : ι → FDRep k G) {κ : Type x} (F : κ → FDRep K G)
    (X : FDRep K G)
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (hlift : Function.Injective lift)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hF_pairwise : PairwiseNonisomorphic F)
    (hF_complete : IsCompleteIrreducibleFamily F) (hX : Simple X)
    (hb : ∀ m : κ →₀ ℕ,
        ordinaryCharacterOnPRegularConjClass p X =
            m.sum (fun j a ↦ (a : K) • ordinaryCharacterOnPRegularConjClass p (F j)) →
          ∃ j, m = Finsupp.single j 1) :
    ∃ i,
      ordinaryCharacterOnPRegularConjClass p X =
        modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Simple X := hX
  -- (a) `χ_X|reg` expands nonnegatively in the Brauer basis (decomposition numbers).
  obtain ⟨c, hc⟩ :=
    restricted_ordinary_character_eq_nonnegative_modular_sum_of_simple
      (p := p) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete hp X
  -- (1) Fong–Swan: each `E i` is the reduction of a simple ordinary module, matched in `F`.
  have hlift_i : ∀ i, ∃ j : κ,
      modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) =
        ordinaryCharacterOnPRegularConjClass p (F j) := by
    intro i
    obtain ⟨Xi, hXi_simple, hXi_char⟩ :=
      simple_modularCharacter_exists_restricted_ordinary_character
        (A := A) (K := K) (G := G) lift (E i) hp hG hlift hred hω (hE_complete.isSimple i)
    obtain ⟨j, hj⟩ := hF_complete.exists_iso Xi hXi_simple
    rcases hj with ⟨e⟩
    exact ⟨j, by rw [hXi_char, ordinaryCharacterOnPRegularConjClass_eq_of_iso e]⟩
  choose jcol hjcol using hlift_i
  set col : ι → (κ →₀ ℕ) := fun i ↦ Finsupp.single (jcol i) 1 with hcol
  set M : κ →₀ ℕ := c.sum (fun i a ↦ a • col i) with hM
  -- Turn the Brauer expansion into a nonnegative ordinary expansion in the family `F`.
  have hM_eq :
      ordinaryCharacterOnPRegularConjClass p X =
        M.sum (fun j a ↦ (a : K) • ordinaryCharacterOnPRegularConjClass p (F j)) := by
    rw [← hc]
    have hcol_eval : ∀ i,
        (col i).sum (fun j a ↦ (a : K) • ordinaryCharacterOnPRegularConjClass p (F j)) =
          modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) := by
      intro i
      change (Finsupp.single (jcol i) (1 : ℕ)).sum
          (fun j a ↦ (a : K) • ordinaryCharacterOnPRegularConjClass p (F j)) =
          modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)
      rw [Finsupp.sum_single_index (by simp), Nat.cast_one, one_smul]
      exact (hjcol i).symm
    -- Replace each Brauer column by its chosen ordinary singleton column, then flatten the
    -- two-stage coefficient family into the ordinary expansion `M`.
    calc
      c.sum
          (fun i a ↦
            (a : K) • modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)) =
          c.sum
            (fun i a ↦
              (a : K) •
                (col i).sum
                  (fun j b ↦ (b : K) • ordinaryCharacterOnPRegularConjClass p (F j))) := by
            refine Finsupp.sum_congr fun i _ ↦ ?_
            rw [hcol_eval i]
      _ =
          (c.sum fun i a ↦ a • col i).sum
            (fun j b ↦ (b : K) • ordinaryCharacterOnPRegularConjClass p (F j)) := by
            exact
              finsupp_sum_natCast_smul_sum_eq_sum_sum
                (R := K) (n := c) (m := col)
                (v := fun j ↦ ordinaryCharacterOnPRegularConjClass p (F j))
      _ = M.sum (fun j b ↦ (b : K) • ordinaryCharacterOnPRegularConjClass p (F j)) := by
            rw [hM]
  -- (b) Condition `(b)` forces the ordinary expansion to be a single summand.
  obtain ⟨j₀, hj₀⟩ := hb M hM_eq
  -- The column-singleton lemma pushes the singleton back to the Brauer coefficient family `c`.
  obtain ⟨i₀, hci₀, _⟩ :=
    nonnegative_column_sum_eq_singleton (n := c) (m := col) (j := j₀)
      (fun i _ ↦ by simp only [hcol]; exact Finsupp.single_ne_zero.mpr one_ne_zero)
      (by rw [← hM]; exact hj₀)
  refine ⟨i₀, ?_⟩
  rw [← hc, hci₀, Finsupp.sum_single_index (by simp), Nat.cast_one, one_smul]

end

end Representation
