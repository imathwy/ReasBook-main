import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_3_3.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

/- Domain-style sampling for Proposition 16-16.3-3:
* primary domain: Grothendieck groups in modular representation theory, with actual
  finite-dimensional and finite-projective representation classes tracked through scalar extension
  and reduction;
* relevant owner declarations inspected in this domain:
  `finiteRepGrothendieckClass`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`,
  `decompositionHom`;
* best owner abstraction: the canonical additive homomorphisms on Grothendieck groups, with this
  file owning only the source-facing actual subset `R⁺[K](G)` and condition `(R)`;
* primitive data: actual finite-dimensional `K[G]`-representations through
  `finiteRepGrothendieckClass`;
* derived API: the bridge theorem identifying the source-facing image `e '' P⁺[k](G)` with the
  canonical range owner `e.range` intersected with `R⁺[K](G)`.

Source/core/bridge triage:
* source-facing: `R⁺[K](G)` and `SatisfiesConditionR`;
* core/canonical: `projectiveGrothendieckScalarExtensionHom` and `decompositionHom`;
* bridge/view: Proposition `16-16.3-3`, which compares the source-facing positive projective image
  with the canonical scalar-extension range inside `R₀[K](G)`.
-/


variable [Finite G]
variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))

/-- Helper for Proposition 16-16.3-3: the restriction of the decomposition of a generic simple
class is computed by restricting the chosen stable-lattice reduction class. -/
private theorem restrictScalars_decomposition_basis_coord_eq
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ j, StableLattice A' (πK j).ρ)
    (l : ι) (j : κ) :
    (((Finsupp.lapply l).comp
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete).repr.toLinearMap).comp
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G).toIntLinearMap)
      ((decompositionHom A' K' G).toIntLinearMap
        ((simple_finiteRep_classes_basis_of_complete_family
          πK hπK_pairwise hπK_complete) j)) =
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete).repr
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G
          [FDRep.of (L j).reductionRepresentation]₀) l := by
  classical
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  -- First unfold the two homomorphism layers and compute `decompositionHom` using the chosen
  -- stable lattice for the generic simple module.
  calc
    (((Finsupp.lapply l).comp bk.repr.toLinearMap).comp
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G).toIntLinearMap)
      ((decompositionHom A' K' G).toIntLinearMap (bK j)) =
        bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G (bK j))) l := by
          simp [bk]
    _ =
        bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G [πK j]₀)) l := by
          simp [bK, simple_finiteRep_classes_basis_of_complete_family_apply]
    _ =
        bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            [FDRep.of (L j).reductionRepresentation]₀) l := by
          rw [decompositionHom_finiteRepClass_eq
            (A := A') (K := K') (G := G) (πK j) (L j)]

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: the residue-side coordinate of a restricted reduction class
is the fixed-simple multiplicity at the corresponding `k`-simple. -/
private theorem restrictScalars_coord_eq_fixedMultiplicity
    {A' : Type u} [CommRing A'] [IsLocalRing A']
    [Algebra k (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (l : ι)
    (V : FDRep (IsLocalRing.ResidueField A') G) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
        (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G [V]₀) l =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
        (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G [V]₀) := by
  -- Read the coordinate through the fixed-simple multiplicity functional, avoiding finite-index
  -- bookkeeping for the complete simple family.
  exact
    simple_basis_coord_eq_fixed_simple_multiplicity_noFinite
      (A := A) (G := G) (S := π l) π hπ_pairwise hπ_complete l ⟨Iso.refl _⟩
      (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G [V]₀)

/-- Helper for Proposition 16-16.3-3: after decomposition and residue-field restriction, a
generic simple basis vector has coordinate equal to the fixed-simple multiplicity of the chosen
stable-lattice reduction. -/
private theorem restrictScalars_decomposition_entry_eq_fixedMultiplicity
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ j, StableLattice A' (πK j).ρ)
    (l : ι) (j : κ) :
      (((Finsupp.lapply l).comp
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete).repr.toLinearMap).comp
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G).toIntLinearMap)
        ((decompositionHom A' K' G).toIntLinearMap
          ((simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete) j)) =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
        (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            [FDRep.of (L j).reductionRepresentation]₀) := by
  -- First compute the decomposition column with the stable lattice, then read the residue
  -- coordinate as the fixed-simple multiplicity functional.
  calc
    (((Finsupp.lapply l).comp
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr.toLinearMap).comp
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G).toIntLinearMap)
      ((decompositionHom A' K' G).toIntLinearMap
        ((simple_finiteRep_classes_basis_of_complete_family
          πK hπK_pairwise hπK_complete) j)) =
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            [FDRep.of (L j).reductionRepresentation]₀) l := by
          exact
            restrictScalars_decomposition_basis_coord_eq
              (A := A) (G := G) (A' := A') (K' := K')
              π hπ_pairwise hπ_complete πK hπK_pairwise hπK_complete L l j
    _ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            [FDRep.of (L j).reductionRepresentation]₀) := by
          exact
            restrictScalars_coord_eq_fixedMultiplicity
              (A := A) (G := G) (A' := A')
              π hπ_pairwise hπ_complete l
              (FDRep.of (L j).reductionRepresentation)

omit [Finite G] in
/-- Helper for Proposition 16-16.3-3: a simple representation has a positive-dimensional
endomorphism intertwiner space. -/
private theorem intertwiningEnd_finrank_pos_of_simple
    {L : Type u} [Field L] {V : FDRep L G} [Simple V] :
    0 < (Module.finrank L (Representation.IntertwiningMap V.ρ V.ρ) : ℤ) := by
  let ρ : Representation L G V := V.ρ
  letI : Module (MonoidAlgebra L G) V := by
    simpa using (inferInstance : Module (MonoidAlgebra L G) ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple V)
  letI : IsSimpleModule (MonoidAlgebra L G) V := by
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial (R := MonoidAlgebra L G) (M := V)
  have hnontr : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
    -- The identity intertwiner is nonzero because the simple module is nonzero.
    refine ⟨⟨1, 0, ?_⟩⟩
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hlin := congrArg Representation.IntertwiningMap.toLinearMap h
    have hfun := LinearMap.congr_fun hlin x
    exact hx (by simpa using hfun)
  have hfin : 0 < Module.finrank L (Representation.IntertwiningMap V.ρ V.ρ) := by
    letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := hnontr
    exact Module.finrank_pos
  exact_mod_cast hfin

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: the projective-envelope Hom dimension over the residue
field is the Schur-weighted fixed-simple multiplicity of the target class. -/
private theorem projectiveEnvelopeHomFinrank_eq_schurWeight_mul_fixedMultiplicity
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (l : ι)
    (M : FDRep k G) :
      (Module.finrank k (Representation.IntertwiningMap (P l).toRep.ρ M.ρ) : ℤ) =
        (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
            [M]₀ := by
  -- This is the residue-side Schur readback isolated from the later stable-lattice transport.
  exact
    projectiveEnvelope_hom_finrank_eq_schurWeight_mul_multiplicity_commonOwner
      (A := A) (G := G) π hπ_pairwise hπ_complete P hP_envelope l M

/-- Helper for Proposition 16-16.3-3: a Schur-weighted pairing identity checked on the
projective basis extends linearly to every projective Grothendieck class. -/
private theorem weightedPairingOfProjectiveBasisValues
    {ι κ P RK : Type*} [AddCommGroup P] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ P) (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK) (z : RK) (wK : κ → ℤ) (wP : ι → ℤ) (n : ℕ)
    {i : ι}
    (hbasis : ∀ l,
      weightedSimpleBasisPairing bK wK z (f (bP l)) =
        wP i * bP.repr (n • bP l) i) :
    ∀ y,
      weightedSimpleBasisPairing bK wK z (f y) =
        wP i * bP.repr (n • y) i := by
  intro y
  let lhs : P →ₗ[ℤ] ℤ := (weightedSimpleBasisPairing bK wK z).comp f
  let coord : P →ₗ[ℤ] ℤ := (Finsupp.lapply i).comp bP.repr.toLinearMap
  let rhs : P →ₗ[ℤ] ℤ := (wP i * (n : ℤ)) • coord
  have hmaps : lhs = rhs := by
    -- Both sides are linear in the projective class, so compare them on the basis.
    apply bP.ext
    intro l
    have hcoord_nsmul : bP.repr (n • bP l) i = (n : ℤ) * bP.repr (bP l) i := by
      rw [map_nsmul]
      exact Finsupp.smul_apply (n : ℤ) (bP.repr (bP l)) i
    calc
      lhs (bP l) = weightedSimpleBasisPairing bK wK z (f (bP l)) := by
        simp [lhs]
      _ = wP i * bP.repr (n • bP l) i := hbasis l
      _ = rhs (bP l) := by
        rw [hcoord_nsmul]
        simp [rhs, coord, mul_assoc]
  have hy := congrArg (fun g : P →ₗ[ℤ] ℤ ↦ g y) hmaps
  have htarget : rhs y = wP i * bP.repr (n • y) i := by
    -- Unfold the right-hand functional back into the `n`-multiple coordinate.
    have hcoord_nsmul : bP.repr (n • y) i = (n : ℤ) * bP.repr y i := by
      rw [map_nsmul]
      exact Finsupp.smul_apply (n : ℤ) (bP.repr y) i
    rw [hcoord_nsmul]
    simp [rhs, coord, mul_assoc]
  calc
    weightedSimpleBasisPairing bK wK z (f y) = lhs y := by
      rfl
    _ = rhs y := hy
    _ = wP i * bP.repr (n • y) i := htarget

/-- Helper for Proposition 16-16.3-3: scaled Schur-weighted column identities on a source basis
extend to the weighted dual-coordinate formula for every source class. -/
private theorem weightedDualCoordinateIdentity_of_basisColumnAdjunction
    {ι κ P RK : Type*} [AddCommGroup P] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ P) (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK) (wP : ι → ℤ) (wK : κ → ℤ) (n : ℕ)
    (z : ι → RK)
    (hbasis : ∀ i l,
      wP l * bP.repr (n • bP i) l =
        (n : ℤ) *
          ((bK.repr (f (bP l))).sum fun j a ↦
            a * (wK j * bK.repr (z i) j))) :
    ∀ i y,
      wP i * bP.repr (n • y) i =
        (n : ℤ) *
          ((bK.repr (f y)).sum fun j a ↦
            a * (wK j * bK.repr (z i) j)) := by
  intro i
  let lhs : P →ₗ[ℤ] ℤ :=
    (wP i) • ((n : ℤ) • ((Finsupp.lapply i).comp bP.repr.toLinearMap))
  let rhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((bK.constr ℤ fun j ↦ wK j * bK.repr (z i) j).comp f)
  have hmaps : lhs = rhs := by
    -- Compare the two weighted coordinate functionals on the source basis.
    apply bP.ext
    intro l
    have hleft :
        lhs (bP l) = wP i * bP.repr (n • bP l) i := by
      have hcoord :
          bP.repr (n • bP l) i = (n : ℤ) * bP.repr (bP l) i := by
        rw [map_nsmul]
        exact Finsupp.smul_apply (n : ℤ) (bP.repr (bP l)) i
      rw [hcoord]
      simp [lhs]
    have htranspose :
        wP i * bP.repr (n • bP l) i =
          wP l * bP.repr (n • bP i) l := by
      -- The two diagonal coordinates agree after transposing the source-basis indices.
      by_cases hli : l = i
      · subst l
        rfl
      · have hil : i ≠ l := fun h ↦ hli h.symm
        rw [map_nsmul, map_nsmul]
        simp [bP.repr_self l, bP.repr_self i, hli, hil]
    calc
      lhs (bP l) = wP i * bP.repr (n • bP l) i := hleft
      _ = wP l * bP.repr (n • bP i) l := htranspose
      _ =
          (n : ℤ) *
            ((bK.repr (f (bP l))).sum fun j a ↦
              a * (wK j * bK.repr (z i) j)) := hbasis i l
      _ = rhs (bP l) := by
            simp [rhs, Module.Basis.constr_apply]
  intro y
  -- Evaluate the linear-map identity and unfold the two functionals.
  have hy := congrArg (fun g : P →ₗ[ℤ] ℤ ↦ g y) hmaps
  simpa [lhs, rhs, Module.Basis.constr_apply] using hy

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: a condition-`(R)` column restricts to the residue-degree
multiple of the matching source simple coordinate. -/
private theorem conditionRColumnRestrictScalarsCoord
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i l : ι) (z : R₀[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l =
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope).repr
        ((Module.finrank k (IsLocalRing.ResidueField A')) •
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) i) l := by
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hrestrict :
      finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z) =
        n • ([π i]₀ : R₀[k](G)) := by
    -- Rewrite the column by condition `(R)`, then apply the scalar-extension/restriction formula.
    rw [hzd]
    exact
      finiteRepGrothendieckRestrictScalarsHom_scalarExtension_class_eq_finrank_nsmul
        (K := k) (K' := IsLocalRing.ResidueField A') (G := G) (π i)
  have hbk_self : bk.repr ([π i]₀ : R₀[k](G)) = Finsupp.single i (1 : ℤ) := by
    simpa [bk, simple_finiteRep_classes_basis_of_complete_family_apply] using bk.repr_self i
  have hbP_self : bP.repr (bP i) = Finsupp.single i (1 : ℤ) := by
    exact bP.repr_self i
  have hbase_coord : bk.repr ([π i]₀ : R₀[k](G)) l = bP.repr (bP i) l := by
    rw [hbk_self, hbP_self]
  -- Compare the two sides after both are reduced to the same Kronecker coordinate.
  calc
    bk.repr
        (finiteRepGrothendieckRestrictScalarsHom
          k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l =
        bk.repr (n • ([π i]₀ : R₀[k](G))) l := by
          rw [hrestrict]
    _ = (n : ℤ) * bk.repr ([π i]₀ : R₀[k](G)) l := by
          rw [map_nsmul]
          exact Finsupp.smul_apply (n : ℤ) (bk.repr ([π i]₀ : R₀[k](G))) l
    _ = (n : ℤ) * bP.repr (bP i) l := by
          rw [hbase_coord]
    _ = bP.repr (n • bP i) l := by
          rw [map_nsmul]
          exact (Finsupp.smul_apply (n : ℤ) (bP.repr (bP i)) l).symm

/-- Helper for Proposition 16-16.3-3: after applying condition `(R)`, the Schur-weighted
restricted residue coordinate is the residue-degree multiple of the diagonal projective-basis
coordinate. -/
private theorem conditionRColumnRestrictedWeightedCoord
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i l : ι) (z : R₀[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G z)) l =
      (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
        ((Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope).repr
            ((projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope) l) i) := by
  classical
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let wP : ι → ℤ :=
    fun j ↦ (Module.finrank k (Representation.IntertwiningMap (π j).ρ (π j).ρ) : ℤ)
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hcoord :
      bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l =
        bP.repr (n • bP i) l := by
    -- Condition `(R)` converts the column into the residue-degree multiple of the matching
    -- projective-envelope basis vector.
    simpa [bk, bP, n] using
      conditionRColumnRestrictScalarsCoord
        (A := A) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope i l z hzd
  have hscale :
      wP l * bP.repr (n • bP i) l =
        (n : ℤ) * (wP i * bP.repr (bP l) i) := by
    -- The scaled projective-basis column is diagonal; off the diagonal both sides are zero.
    by_cases hli : l = i
    · subst l
      have hcoord_self :
          bP.repr (n • bP i) i = (n : ℤ) * bP.repr (bP i) i := by
        rw [map_nsmul]
        exact Finsupp.smul_apply (n : ℤ) (bP.repr (bP i)) i
      rw [hcoord_self]
      ring
    · have hil : i ≠ l := fun h ↦ hli h.symm
      rw [map_nsmul]
      simp [bP.repr_self i, bP.repr_self l, hli, hil]
  -- Substitute the restricted coordinate and collapse the diagonal arithmetic.
  calc
    (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G z)) l =
        wP l * bP.repr (n • bP i) l := by
          rw [hcoord]
    _ = (n : ℤ) * (wP i * bP.repr (bP l) i) := hscale
    _ =
      (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
        ((Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
          bP.repr (bP l) i) := by
          rfl

-- From here on Serre's hypothesis `char K = 0` is in force (Prop. 45 is part of the modular
-- representation theory of §16.3, where `K` has characteristic zero so that `K[G]` and every
-- `K'[G]` are semisimple; this is exactly what makes the Schur-weighted pairing compute a `Hom`
-- dimension, i.e. what lets `e` and `d` be adjoint).  It is genuinely needed: in characteristic
-- `p` the basis identity below is false (e.g. `G = ℤ/p`, `K' = 𝔽_p((t))` gives `1 ≠ p`).
variable [CharZero K]

/-- Helper for Proposition 16-16.3-3: the characteristic-zero Brauer reciprocity identity at one
projective-envelope basis column and one generic simple.  Both sides are computed by the single
residue-field `Hom` dimension `Hom_k((P l).toRep, restrict(reduction(L j)))`: the generic
`K'`-side via the Schur readback (`finrank_intertwining_eq_simpleBasisCoord_mul_schur`), the
base-change `Hom`-fiber equality (`brauer_homFiber_baseChange_finrank_eq`) and the residue base
change (`finrank_intertwining_restrictScalars_eq_finrank_smul`); the residue side via the
projective-envelope multiplicity readback. -/
private theorem brauerReciprocity_basisColumn_entry
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ j, StableLattice A' (πK j).ρ)
    (l : ι) (j : κ) :
    (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
        ((Module.finrank K'
            (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) *
          (simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete).repr
            (projectiveGrothendieckScalarExtensionHom A K'
              ((projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope) l)) j) =
      (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G
              ((simple_finiteRep_classes_basis_of_complete_family
                πK hπK_pairwise hπK_complete) j))) l := by
  classical
  -- Characteristic zero is inherited by the larger field `K'`, making `K'[G]` semisimple.
  letI : CharZero K' := (RingHom.charZero_iff (algebraMap K K').injective).1 inferInstance
  -- Choose a projective `A[G]`-lift of the projective envelope `P l`.
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) (P l)
  set σ : FDRep (IsLocalRing.ResidueField A') G :=
    FDRep.of (L j).reductionRepresentation with hσ
  -- View the residue reduction as a `k`-space (the same restriction of scalars used by
  -- `FDRep.restrictScalars`), so that the bare `Representation.restrictScalars` elaborates.
  letI : Module k σ.V := Module.compHom σ.V (algebraMap k (IsLocalRing.ResidueField A'))
  letI : IsScalarTower k (IsLocalRing.ResidueField A') σ.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite k σ.V := Module.Finite.trans (IsLocalRing.ResidueField A') σ.V
  -- Schur readback over `K'`: the Schur-weighted generic coordinate is a `Hom` dimension.
  have hL1 :
      (Module.finrank K'
          (Representation.IntertwiningMap (Q.scalarExtension K').ρ (πK j).ρ) : ℤ) =
        (simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete).repr
            (finiteRepGrothendieckClass K' G (Q.scalarExtension K')) j *
          (Module.finrank K'
            (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) :=
    finrank_intertwining_eq_simpleBasisCoord_mul_schur
      (L := K') πK hπK_pairwise hπK_complete j (Q.scalarExtension K')
  -- Base-change Brauer `Hom`-fiber: the generic `K'`-fiber equals the residue `k'`-fiber.
  have hL2 :
      Module.finrank K'
          (Representation.IntertwiningMap (Q.scalarExtension K').ρ (πK j).ρ) =
        Module.finrank (IsLocalRing.ResidueField A')
          (Representation.IntertwiningMap
            ((P l).scalarExtension (IsLocalRing.ResidueField A')).ρ σ.ρ) :=
    brauer_homFiber_baseChange_finrank_eq
      (A := A) (A' := A') (K' := K') Q (P l) hQ (L j)
  -- Residue base change: the `k`-dimension is `[k':k]` times the `k'`-dimension.  Stated with the
  -- projective scalar-extension owner (definitionally the scalar extension of `(P l).toRep`).
  have hL3 :
      Module.finrank k
          (Representation.IntertwiningMap (P l).toRep.ρ
            (Representation.restrictScalars k σ.ρ)) =
        Module.finrank k (IsLocalRing.ResidueField A') *
          Module.finrank (IsLocalRing.ResidueField A')
            (Representation.IntertwiningMap
              ((P l).scalarExtension (IsLocalRing.ResidueField A')).ρ σ.ρ) :=
    finrank_intertwining_restrictScalars_eq_finrank_smul (P l).toRep.ρ σ.ρ
  -- Chain the base-change fiber with the residue base change: the residue `Hom` dimension is
  -- `[k':k]` times the generic `K'`-fiber dimension.
  have hC :
      Module.finrank k
          (Representation.IntertwiningMap (P l).toRep.ρ
            (Representation.restrictScalars k σ.ρ)) =
        Module.finrank k (IsLocalRing.ResidueField A') *
          Module.finrank K'
            (Representation.IntertwiningMap (Q.scalarExtension K').ρ (πK j).ρ) := by
    rw [hL3, ← hL2]
  -- The residue-field multiplicity readback for the projective envelope.
  have hMult :
      (Module.finrank k
          (Representation.IntertwiningMap (P l).toRep.ρ
            (FDRep.restrictScalars
              (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ).ρ) : ℤ) =
        (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
            [FDRep.restrictScalars
              (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ]₀ :=
    projectiveEnvelopeHomFinrank_eq_schurWeight_mul_fixedMultiplicity
      (A := A) (G := G) π hπ_pairwise hπ_complete P hP_envelope l
      (FDRep.restrictScalars (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ)
  -- The residue coordinate of the restricted decomposition is the fixed-simple multiplicity.
  have hEntry :=
    restrictScalars_decomposition_entry_eq_fixedMultiplicity
      (A := A) (G := G) (A' := A') (K' := K')
      π hπ_pairwise hπ_complete πK hπK_pairwise hπK_complete L l j
  have hcoord :
      (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G
              ((simple_finiteRep_classes_basis_of_complete_family
                πK hπK_pairwise hπK_complete) j))) l =
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
          [FDRep.restrictScalars
            (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ]₀ := by
    simpa [hσ, finiteRepGrothendieckRestrictScalarsHom_class_eq] using hEntry
  -- The lifted projective class is the scalar extension of the chosen `A[G]`-lift.
  have hlift :
      projectiveGrothendieckScalarExtensionHom A K'
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) l) =
        [Q.scalarExtension K']₀ := by
    rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
    exact projectiveScalarExtension_liftClass_eq (A := A) (G := G) (K' := K') (P l) Q hQ
  -- Assemble: both sides equal the residue-field `Hom` dimension of the projective envelope
  -- against the restricted reduction.
  rw [hlift]
  calc
    (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
        ((Module.finrank K'
            (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) *
          (simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete).repr
            (finiteRepGrothendieckClass K' G (Q.scalarExtension K')) j) =
        (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
          (Module.finrank K'
            (Representation.IntertwiningMap (Q.scalarExtension K').ρ (πK j).ρ) : ℤ) := by
          rw [hL1]; ring
    _ = (Module.finrank k
          (Representation.IntertwiningMap (P l).toRep.ρ
            (Representation.restrictScalars k σ.ρ)) : ℤ) := by
          rw [hC]; push_cast; ring
    _ = (Module.finrank k
          (Representation.IntertwiningMap (P l).toRep.ρ
            (FDRep.restrictScalars
              (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ).ρ) : ℤ) := rfl
    _ = (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π l)
            [FDRep.restrictScalars
              (K := k) (K' := IsLocalRing.ResidueField A') (G := G) σ]₀ := hMult
    _ = (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete).repr
            (finiteRepGrothendieckRestrictScalarsHom
              k (IsLocalRing.ResidueField A') G
              (decompositionHom A' K' G
                ((simple_finiteRep_classes_basis_of_complete_family
                  πK hπK_pairwise hπK_complete) j))) l := by
          rw [hcoord]

/-- Helper for Proposition 16-16.3-3: the condition-`(R)` column gives the scaled weighted
dual-basis identity needed before extending from basis classes to arbitrary projective classes. -/
private theorem conditionRColumnWeightedDualBasis
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (i l : ι) (z : R₀[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope).repr
          ((Module.finrank k (IsLocalRing.ResidueField A')) •
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope) i) l =
      (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
        (((simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete).repr
          (projectiveGrothendieckScalarExtensionHom A K'
            ((projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope) l))).sum
          fun j a ↦
            a *
              ((Module.finrank K'
                (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) *
                (simple_finiteRep_classes_basis_of_complete_family
                  πK hπK_pairwise hπK_complete).repr z j)) := by
  classical
  -- A complete simple `A'`-lattice family for the generic simples, feeding the basis-column entry.
  let L : ∀ j, StableLattice A' (πK j).ρ :=
    fun j ↦ (Representation.exists_stableLattice (A := A') (πK j).ρ).some
  set bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete with hbK
  set bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete with hbk
  set bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
      with hbP
  set wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) with hwK
  set n : ℕ := Module.finrank k (IsLocalRing.ResidueField A') with hn
  -- The restricted residue coordinate, as a `ℤ`-linear functional of the generic class.
  let Φ : R₀[K'](G) →ₗ[ℤ] ℤ :=
    (Finsupp.lapply l).comp (bk.repr.toLinearMap.comp
      ((finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G).toIntLinearMap.comp
        (decompositionHom A' K' G).toIntLinearMap))
  -- The Schur-weighted pairing against the projective basis column, as a `ℤ`-linear functional.
  let Pair : R₀[K'](G) →ₗ[ℤ] ℤ :=
    weightedSimpleBasisPairing bK wK
      (projectiveGrothendieckScalarExtensionHom A K' (bP l))
  have hΦ_apply : ∀ x, Φ x =
      bk.repr (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G
        (decompositionHom A' K' G x)) l := fun x ↦ rfl
  -- Brauer adjunction in functional form: on the generic simple basis the two functionals agree
  -- (this is the basis-column Brauer reciprocity entry), hence everywhere.
  have hmaps :
      (n : ℤ) • Pair =
        (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) • Φ := by
    apply bK.ext
    intro j
    have hPair : Pair (bK j) = wK j * bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l)) j := by
      simp only [Pair, weightedSimpleBasisPairing, Module.Basis.constr_basis]
    simp only [LinearMap.smul_apply, smul_eq_mul, hPair, hΦ_apply]
    exact
      brauerReciprocity_basisColumn_entry
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope πK hπK_pairwise hπK_complete L l j
  -- Evaluate the functional identity at the condition-`(R)` column `z`.
  have hStepA :
      (n : ℤ) * Pair z =
        (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          bk.repr (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G z)) l := by
    have hz := congrArg (fun f : R₀[K'](G) →ₗ[ℤ] ℤ ↦ f z) hmaps
    simpa [LinearMap.smul_apply, smul_eq_mul, hΦ_apply] using hz
  -- Condition `(R)` normalizes the restricted residue coordinate to the projective basis column.
  have hB :
      bk.repr (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G
          (decompositionHom A' K' G z)) l =
        bP.repr (n • bP i) l := by
    simpa [hbk, hbP, hn] using
      conditionRColumnRestrictScalarsCoord
        (A := A) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope i l z hzd
  -- The pairing is the same finite dot product as the target sum, after commuting the factors.
  have hsum :
      ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l))).sum
          fun j a ↦ a * (wK j * bK.repr z j)) = Pair z := by
    rw [show Pair z =
        weightedSimpleBasisPairing bK wK
          (projectiveGrothendieckScalarExtensionHom A K' (bP l)) z from rfl,
      weightedSimpleBasisPairing, Module.Basis.constr_apply,
      finsupp_weighted_intDot_comm]
    refine Finsupp.sum_congr ?_
    intro j _
    ring
  -- Assemble the adjunction with the column normalization.
  calc
    (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        bP.repr (n • bP i) l =
        (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
          bk.repr (finiteRepGrothendieckRestrictScalarsHom k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G z)) l := by
          rw [hB]
    _ = (n : ℤ) * Pair z := hStepA.symm
    _ = (n : ℤ) *
        ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l))).sum
          fun j a ↦ a * (wK j * bK.repr z j)) := by
          rw [hsum]

/-- Helper for Proposition 16-16.3-3: the condition-`(R)` column form of the
residue-degree-scaled Brauer adjunction identity. -/
private theorem conditionRColumnScaledAdjunction
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (i l : ι) (z : R₀[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
      weightedSimpleBasisPairing
        (simple_finiteRep_classes_basis_of_complete_family
          πK hπK_pairwise hπK_complete)
        (fun j ↦
          (Module.finrank K'
            (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ))
        z
        (projectiveGrothendieckScalarExtensionHom A K'
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) l)) =
    (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ) *
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G
            (decompositionHom A' K' G z)) l := by
  classical
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let wP : ι → ℤ :=
    fun j ↦ (Module.finrank k (Representation.IntertwiningMap (π j).ρ (π j).ρ) : ℤ)
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hdualBasis :
      wP l * bP.repr (n • bP i) l =
        (n : ℤ) *
          ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l))).sum
            fun j a ↦ a * (wK j * bK.repr z j)) := by
    -- Consume the new scaled basis-column bridge; no cancellation is performed here.
    simpa [bK, bP, wK, wP, n] using
      conditionRColumnWeightedDualBasis
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope
        πK hπK_pairwise hπK_complete i l z hzd
  have hcoord :
      bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l =
        bP.repr (n • bP i) l := by
    -- Condition `(R)` normalizes the residue coordinate to the matching scaled projective
    -- basis column.
    simpa [bk, bP, n] using
      conditionRColumnRestrictScalarsCoord
        (A := A) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope i l z hzd
  calc
    (n : ℤ) *
        weightedSimpleBasisPairing bK wK z
          (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
        (n : ℤ) *
          ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l))).sum
            fun j a ↦ a * (wK j * bK.repr z j)) := by
          simp [weightedSimpleBasisPairing, Module.Basis.constr_apply]
    _ = wP l * bP.repr (n • bP i) l := hdualBasis.symm
    _ = wP l *
        bk.repr
          (finiteRepGrothendieckRestrictScalarsHom
            k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l := by
          rw [hcoord]

/-- Helper for Proposition 16-16.3-3: condition-`(R)` columns give the scaled weighted
dual-coordinate identity for arbitrary projective residue-field classes. -/
private theorem conditionR_weightedDualCoordinateIdentity
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (z : ι → R₀[K'](G))
    (hzd :
      ∀ i, decompositionHom A' K' G (z i) =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    ∀ i y,
      (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope).repr
          ((Module.finrank k (IsLocalRing.ResidueField A')) • y) i =
        (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) *
          (((simple_finiteRep_classes_basis_of_complete_family
              πK hπK_pairwise hπK_complete).repr
            (projectiveGrothendieckScalarExtensionHom A K' y)).sum
            fun j a ↦
              a *
                ((Module.finrank K'
                  (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) *
                  (simple_finiteRep_classes_basis_of_complete_family
                    πK hπK_pairwise hπK_complete).repr (z i) j)) := by
  classical
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let wP : ι → ℤ :=
    fun i ↦ (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ)
  let wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hbasis :
      ∀ i l,
        wP l * bP.repr (n • bP i) l =
          (n : ℤ) *
            ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' (bP l))).sum
              fun j a ↦ a * (wK j * bK.repr (z i) j)) := by
    intro i l
    -- Consume the basis-column Brauer bridge once, then the pure linear helper extends it.
    simpa [bP, bK, wP, wK, n] using
      conditionRColumnWeightedDualBasis
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope
        πK hπK_pairwise hπK_complete i l (z i) (hzd i)
  simpa [bP, bK, wP, wK, n] using
    weightedDualCoordinateIdentity_of_basisColumnAdjunction
      bP bK (projectiveGrothendieckScalarExtensionHom A K').toIntLinearMap
      wP wK n z hbasis

/-- Helper for Proposition 16-16.3-3: condition `(R)` directly puts the residue-degree multiple
of a projective class in the projective positive cone. -/
private theorem conditionR_positiveMultipleCone_direct
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (z : ι → R₀[K'](G))
    (hzpositive : ∀ i, z i ∈ R⁺[K'](G))
    (hzd :
      ∀ i, decompositionHom A' K' G (z i) =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀)
    {y : P₀[k](G)}
    (hy : projectiveGrothendieckScalarExtensionHom A K' y ∈ R⁺[K'](G)) :
    (Module.finrank k (IsLocalRing.ResidueField A')) • y ∈
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope).positiveCone := by
  classical
  obtain ⟨κ, πK, hπK_pairwise, hπK_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField
      (L := K') (G := G)
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      πK hπK_pairwise hπK_complete
  let wP : ι → ℤ :=
    fun i ↦ (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ)
  let wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hwP_pos : ∀ i, 0 < wP i := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    exact intertwiningEnd_finrank_pos_of_simple (G := G) (V := π i)
  have hwK_nonneg : ∀ j, 0 ≤ wK j := by
    intro j
    letI : Simple (πK j) := hπK_complete.isSimple j
    exact le_of_lt (intertwiningEnd_finrank_pos_of_simple (G := G) (V := πK j))
  have hyCone :
      projectiveGrothendieckScalarExtensionHom A K' y ∈ bK.positiveCone :=
    finiteRepPositiveSubset_subset_simpleBasis_positiveCone
      (K := K') (G := G) πK hπK_pairwise hπK_complete hy
  have hzCone : ∀ i, z i ∈ bK.positiveCone := by
    intro i
    exact
      finiteRepPositiveSubset_subset_simpleBasis_positiveCone
        (K := K') (G := G) πK hπK_pairwise hπK_complete (hzpositive i)
  have hdual :
      ∀ i y,
        wP i * bP.repr (n • y) i =
          (n : ℤ) *
            ((bK.repr (projectiveGrothendieckScalarExtensionHom A K' y)).sum
              fun j a ↦ a * (wK j * bK.repr (z i) j)) := by
    simpa [bP, bK, wP, wK, n] using
      conditionR_weightedDualCoordinateIdentity
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope
        πK hπK_pairwise hπK_complete z hzd
  exact
    positiveCone_of_weightedScaledDualCoordinateWitnesses bP bK
      (projectiveGrothendieckScalarExtensionHom A K').toIntLinearMap
      wP wK z hdual hwP_pos hwK_nonneg (Int.natCast_nonneg n) hyCone hzCone

/-- Helper for Proposition 16-16.3-3: the condition-`(R)` column pairing formula holds on every
projective basis vector. -/
private theorem conditionRColumnWeightedPairingBasis
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (πK : κ → FDRep K' G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (i l : ι) (z : R₀[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀) :
    weightedSimpleBasisPairing
        (simple_finiteRep_classes_basis_of_complete_family
          πK hπK_pairwise hπK_complete)
        (fun j ↦
          (Module.finrank K'
            (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ))
        z
        (projectiveGrothendieckScalarExtensionHom A K'
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) l)) =
      (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope).repr
          ((projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope) l) i := by
  classical
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let wP : ι → ℤ :=
    fun j ↦ (Module.finrank k (Representation.IntertwiningMap (π j).ρ (π j).ρ) : ℤ)
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hbridge :
      (n : ℤ) *
        weightedSimpleBasisPairing bK wK z
          (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
        wP l *
          bk.repr
            (finiteRepGrothendieckRestrictScalarsHom
              k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l := by
    -- Use the source-facing Brauer bridge only on the condition-`(R)` column supplied by `hzd`.
    simpa [bK, bk, bP, wK, wP] using
      conditionRColumnScaledAdjunction
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope
        πK hπK_pairwise hπK_complete i l z hzd
  have hn_ne : (n : ℤ) ≠ 0 := by
    have hn_pos : (0 : ℤ) < (n : ℤ) := by
      exact_mod_cast
        (Module.finrank_pos (R := k) (M := IsLocalRing.ResidueField A'))
    exact ne_of_gt hn_pos
  have hrestricted :
      wP l *
          bk.repr
            (finiteRepGrothendieckRestrictScalarsHom
              k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l =
        (n : ℤ) * (wP i * bP.repr (bP l) i) := by
    -- All residue-coordinate arithmetic is now isolated in the condition-column normalization
    -- helper; the remaining proof only cancels the generic residue degree.
    simpa [bk, bP, wP, n] using
      conditionRColumnRestrictedWeightedCoord
        (A := A) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope i l z hzd
  have hscaled :
      (n : ℤ) *
          weightedSimpleBasisPairing bK wK z
            (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
        (n : ℤ) * (wP i * bP.repr (bP l) i) := by
    calc
      (n : ℤ) *
          weightedSimpleBasisPairing bK wK z
            (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
          wP l *
            bk.repr
              (finiteRepGrothendieckRestrictScalarsHom
                k (IsLocalRing.ResidueField A') G (decompositionHom A' K' G z)) l := hbridge
      _ = (n : ℤ) * (wP i * bP.repr (bP l) i) := hrestricted
  have hbasis :
      weightedSimpleBasisPairing bK wK z
          (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
        wP i * bP.repr (bP l) i :=
    mul_left_cancel₀ hn_ne hscaled
  simpa [bK, bP, wK, wP, n] using hbasis

/-- Helper for Proposition 16-16.3-3: if a Schur-weighted source coordinate is nonnegative, then
the residue-degree multiple has the divisibility witness required by the positive-cone argument. -/
private theorem weightedNsmulCoordinateWitness_of_nonneg
    {ι P : Type*} [AddCommGroup P]
    (b : Module.Basis ι ℤ P) (n : ℕ) (w : ι → ℤ)
    {x : P} (i : ι)
    (hcoord_nonneg : 0 ≤ w i * b.repr x i) :
    ∃ c : ℤ, 0 ≤ c ∧
      w i * b.repr (n • x) i = (n : ℤ) * c := by
  -- Choose the weighted coordinate itself; linearity of the basis coordinates supplies the
  -- residue-degree factor on the left.
  refine ⟨w i * b.repr x i, hcoord_nonneg, ?_⟩
  have hsmul :
      b.repr (n • x) i = (n : ℤ) * b.repr x i := by
    simp
  rw [hsmul]
  ring

/-- Helper for Proposition 16-16.3-3: the source-proof Brauer pairing step gives
nonnegativity of one Schur-weighted source coordinate. -/
private theorem conditionR_weightedSourceCoordinate_nonneg
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i : ι)
    {y : P₀[k](G)}
    (z : R₀[K'](G))
    (hzpositive : z ∈ R⁺[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀)
    (hy : projectiveGrothendieckScalarExtensionHom A K' y ∈ R⁺[K'](G)) :
    0 ≤
      (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope).repr y i := by
  -- Route correction: instead of asking directly for a nonnegative source coordinate, build the
  -- generic weighted pairing from two positive `K'`-classes and isolate the missing Brauer
  -- adjunction as one equality of that pairing with the source coordinate.
  classical
  obtain ⟨κ, πK, hπK_pairwise, hπK_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField
      (L := K') (G := G)
  let bK : Module.Basis κ ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      πK hπK_pairwise hπK_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let wK : κ → ℤ :=
    fun j ↦ (Module.finrank K' (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let wP : ι → ℤ :=
    fun l ↦ (Module.finrank k (Representation.IntertwiningMap (π l).ρ (π l).ρ) : ℤ)
  have hwK_nonneg : ∀ j, 0 ≤ wK j := by
    intro j
    letI : Simple (πK j) := hπK_complete.isSimple j
    exact le_of_lt (intertwiningEnd_finrank_pos_of_simple (G := G) (V := πK j))
  have hyCone :
      projectiveGrothendieckScalarExtensionHom A K' y ∈ bK.positiveCone :=
    finiteRepPositiveSubset_subset_simpleBasis_positiveCone
      (K := K') (G := G) πK hπK_pairwise hπK_complete hy
  have hzCone : z ∈ bK.positiveCone :=
    finiteRepPositiveSubset_subset_simpleBasis_positiveCone
      (K := K') (G := G) πK hπK_pairwise hπK_complete hzpositive
  have hpair_nonneg :
      0 ≤
        weightedSimpleBasisPairing bK wK z
          (projectiveGrothendieckScalarExtensionHom A K' y) :=
    weightedSimpleBasisPairing_nonneg_of_positive bK hwK_nonneg hyCone hzCone
  have hpair_eq :
      weightedSimpleBasisPairing bK wK z
          (projectiveGrothendieckScalarExtensionHom A K' y) =
        wP i * bP.repr y i := by
    have hbasis :
        ∀ l,
          weightedSimpleBasisPairing bK wK z
              (projectiveGrothendieckScalarExtensionHom A K' (bP l)) =
            wP i * bP.repr ((1 : ℕ) • bP l) i := by
      intro l
      -- The condition column formula is now checked only on projective basis vectors, after
      -- cancelling the residue-degree factor in the repaired Brauer bridge.
      simpa [bK, bP, wK, wP] using
        conditionRColumnWeightedPairingBasis
          (A := A) (K := K) (G := G) (A' := A') (K' := K')
          π hπ_pairwise hπ_complete P hP_envelope
          πK hπK_pairwise hπK_complete i l z hzd
    have hy_pair :
        weightedSimpleBasisPairing bK wK z
            (projectiveGrothendieckScalarExtensionHom A K' y) =
          wP i * bP.repr ((1 : ℕ) • y) i :=
      weightedPairingOfProjectiveBasisValues
        bP bK (projectiveGrothendieckScalarExtensionHom A K').toIntLinearMap
        z wK wP 1 hbasis y
    -- With `n = 1`, the linear extension gives exactly the unscaled source coordinate.
    simpa using hy_pair
  -- The pairing is nonnegative by positivity of both generic classes, and the adjunction
  -- identifies it with the required source coordinate.
  have hweighted : 0 ≤ wP i * bP.repr y i := by
    simpa [hpair_eq] using hpair_nonneg
  simpa [bP, wP] using hweighted

/-- Helper for Proposition 16-16.3-3: the source-proof pairing step gives a nonnegative weighted
coordinate witness for one original residue-field simple. -/
private theorem conditionR_pairingCoordinateWitness
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [IsLocalHom (algebraMap A A')]
    [Algebra k (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional k (IsLocalRing.ResidueField A')]
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ι : Type*}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[MonoidAlgebra k G] Representation.asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (i : ι)
    {y : P₀[k](G)}
    (z : R₀[K'](G))
    (hzpositive : z ∈ R⁺[K'](G))
    (hzd :
      decompositionHom A' K' G z =
        finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [π i]₀)
    (hy : projectiveGrothendieckScalarExtensionHom A K' y ∈ R⁺[K'](G)) :
    ∃ c : ℤ, 0 ≤ c ∧
      (Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) : ℤ) *
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope).repr
            ((Module.finrank k (IsLocalRing.ResidueField A')) • y) i =
        (Module.finrank k (IsLocalRing.ResidueField A') : ℤ) * c := by
  -- Route correction: the K'-simple-coordinate route required semisimplicity/splitting
  -- hypotheses not present here.  The remaining source-facing step is the Brauer-pairing
  -- nonnegativity lemma above; the residue-degree divisibility is only basis linearity.
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  let w : ι → ℤ :=
    fun j ↦ (Module.finrank k (Representation.IntertwiningMap (π j).ρ (π j).ρ) : ℤ)
  have hcoord_nonneg : 0 ≤ w i * bP.repr y i := by
    simpa [w, bP] using
      conditionR_weightedSourceCoordinate_nonneg
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope i
        z hzpositive hzd hy
  simpa [bP, n, w] using
    weightedNsmulCoordinateWitness_of_nonneg bP n w i hcoord_nonneg

/-- Helper for Proposition 16-16.3-3: the source-proof coefficient argument descends positivity
of the scalar extension of a projective residue-field class back to `P_k^+(G)`. -/
private theorem projectivePositive_of_scalarExtensionPositive_conditionR
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hdecomp :
      decompositionHom A' K' G '' R⁺[K'](G) =
        R⁺[IsLocalRing.ResidueField A'](G))
    {y : P₀[k](G)}
    (hy : projectiveGrothendieckScalarExtensionHom A K' y ∈ R⁺[K'](G)) :
    y ∈ P⁺[k](G) := by
  -- Route correction: the older proof route indexed the condition-`(R)` columns by simple
  -- `k'`-modules and then needed a missing projective positivity reflection across `k → k'`.
  -- We now follow the source proof: index the columns by original simple `k`-modules and leave
  -- only the Brauer-reciprocity coordinate identity as the remaining bridge.
  classical
  have hAK : Function.Injective (algebraMap A K) := by
    simpa [faithfulSMul_iff_algebraMap_injective] using
      (inferInstance : FaithfulSMul A K)
  have hKK' : Function.Injective (algebraMap K K') := RingHom.injective _
  have hAK' : Function.Injective (algebraMap A K') := by
    simpa [IsScalarTower.algebraMap_eq A K K'] using hKK'.comp hAK
  have hcomp : Function.Injective ((algebraMap A' K') ∘ (algebraMap A A')) := by
    simpa [IsScalarTower.algebraMap_eq A A' K'] using hAK'
  have hAA' : Function.Injective (algebraMap A A') :=
    Function.Injective.of_comp hcomp
  letI : FaithfulSMul A A' :=
    (faithfulSMul_iff_algebraMap_injective A A').2 hAA'
  letI : IsLocalHom (algebraMap A A') := by
    infer_instance
  let _ : Module.Finite k (IsLocalRing.ResidueField A') :=
    IsLocalRing.ResidueField.finite_of_module_finite (R := A) (S := A')
  letI : FiniteDimensional k (IsLocalRing.ResidueField A') :=
    inferInstance
  let n : ℕ := Module.finrank k (IsLocalRing.ResidueField A')
  have hn : 1 ≤ n := by
    exact Nat.succ_le_iff.mpr
      (Module.finrank_pos (R := k) (M := IsLocalRing.ResidueField A'))
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField
      (L := k) (G := G)
  choose P hP_envelope using
    fun i : ι ↦ existsFiniteProjectiveEnvelopeOfSimple (G := G) (τ := π i)
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  have hcolumnsSource :
      ∀ i, ∃ z : R₀[K'](G),
        z ∈ R⁺[K'](G) ∧
          decompositionHom A' K' G z =
            finiteRepGrothendieckScalarExtensionHom
              k (IsLocalRing.ResidueField A') G [π i]₀ := by
    intro i
    exact conditionR_positivePreimage_of_residueScalarExtensionClass
      (G := G) (A := A) (A' := A') (K' := K') hdecomp (π i)
  choose z hzpositive hzd using hcolumnsSource
  suffices hmultiple : n • y ∈ P⁺[k](G) by
    -- Once condition `(R)` supplies a positive multiple, Lemma `16-16.3-1` saturates the cone.
    exact mem_projectivePositiveSubset_of_nsmul_mem (A := k) (G := G) hn hmultiple
  have hmultipleCone : n • y ∈ bP.positiveCone := by
    -- The scaled dual-coordinate argument produces positivity of the whole residue-degree
    -- multiple at once, avoiding the old cancellation-based coordinate witness.
    simpa [bP, n] using
      conditionR_positiveMultipleCone_direct
        (A := A) (K := K) (G := G) (A' := A') (K' := K')
        π hπ_pairwise hπ_complete P hP_envelope z hzpositive hzd hy
  have hcone :
      P⁺[k](G) = bP.positiveCone :=
    projectivePositiveSubset_eq_positiveCone_of_complete_simple_family
      π hπ_pairwise hπ_complete P hP_envelope
  simpa [hcone] using hmultipleCone

/-- Helper for Proposition 16-16.3-3: condition `(R)` and actual positivity of `e y` force the
source projective class `y` to be actual-positive. -/
private theorem mem_projectivePositiveSubset_of_conditionR_positive
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hR : SatisfiesConditionR (R⁺[K](G)) A)
    {y : P₀[k](G)} (hy : e y ∈ R⁺[K](G)) :
    y ∈ P⁺[k](G) := by
  rcases hR with
    ⟨A', instCommA', instLocalA', instDomainA', instDVRA', instAlgAA',
      instFiniteAA', K', instFieldK', instAlgA'K', instAlgAK', instFracA'K',
      instAlgKK', instTowerAA'K', instTowerAKK', instFiniteDimKK', hpre, hdecomp⟩
  letI : CommRing A' := instCommA'
  letI : IsLocalRing A' := instLocalA'
  letI : IsDomain A' := instDomainA'
  letI : IsDiscreteValuationRing A' := instDVRA'
  letI : Algebra A A' := instAlgAA'
  letI : Module.Finite A A' := instFiniteAA'
  letI : Field K' := instFieldK'
  letI : Algebra A' K' := instAlgA'K'
  letI : Algebra A K' := instAlgAK'
  letI : IsFractionRing A' K' := instFracA'K'
  letI : Algebra K K' := instAlgKK'
  letI : IsScalarTower A A' K' := instTowerAA'K'
  letI : IsScalarTower A K K' := instTowerAKK'
  letI : FiniteDimensional K K' := instFiniteDimKK'
  have hscalar :
      finiteRepGrothendieckScalarExtensionHom K K' G (e y) ∈ R⁺[K'](G) :=
    conditionR_scalarExtension_mem_finiteRepPositive
      (K := K) (K' := K') (G := G) hpre hy
  have hprojective :
      projectiveGrothendieckScalarExtensionHom A K' y ∈ R⁺[K'](G) := by
    -- Normalize the finite scalar extension of `e y` to direct scalar extension over `K'`.
    rwa [finiteScalarExtension_projectiveScalarExtensionHom_apply
      (A := A) (K := K) (K' := K') (G := G) (y := y)] at hscalar
  exact
    projectivePositive_of_scalarExtensionPositive_conditionR
      (A := A) (K := K) (G := G) (A' := A') (K' := K') hdecomp hprojective

-- Proof sketch: use Proposition `16-16.3-2` to descend positive projective classes from a finite
-- extension satisfying condition `(R)`. Through the canonical reduction equivalence
-- `P_A(G) ≃ P_k(G)`, this identifies the image of the source-facing positive subset `P_k^+(G)`
-- under Serre's scalar-extension owner `e` with the intersection of the full scalar-extension
-- range of `e` and the actual positive subset `R⁺[K](G)`.
/-- Proposition 16-16.3-3: if condition `(R)` holds for the positive subset `R_K^+(G)`, then the
image of the source-facing positive subset `P_k^+(G)`, under Serre's canonical scalar-extension
homomorphism `e : P_k(G) → R_K(G)`, is exactly the intersection of the range of `e` with
`R_K^+(G)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem SatisfiesConditionR.image_eq_range_inter_positive
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hR : SatisfiesConditionR (R⁺[K](G)) A) :
    e '' P⁺[k](G) =
      ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := by
  apply Set.Subset.antisymm
  · -- The forward inclusion is actual lifting of projective residue-field modules.
    exact projectivePositiveImage_subset_range_inter_finiteRepPositive
      (A := A) (K := K) (G := G)
  · rintro x ⟨hxrange, hxpositive⟩
    rcases hxrange with ⟨y, rfl⟩
    -- The reverse inclusion is exactly positivity descent under condition `(R)`.
    exact
      ⟨y, mem_projectivePositiveSubset_of_conditionR_positive
        (A := A) (K := K) (G := G) hR hxpositive, rfl⟩

end

end Representation
