import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_77_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxAway[" f "]" => CochainComplex (ModuleCat (Localization.Away f)) ℤ
local notation "FiniteFreeClassAway[" f "]" =>
  (fun M : ModuleCat (Localization.Away f) ↦
    Module.Free (Localization.Away f) M ∧ Module.Finite (Localization.Away f) M)
local notation "BoundedFiniteFreeCpxAway[" f "]" =>
  CochainComplex.MinusWithTermsIn FiniteFreeClassAway[f]
/-- Helper for Lemma 15.78.1: the degree-`i` homology of the derived fiber
`K \otimes_R^{\mathbf L} \kappa(\mathfrak p)`. -/
abbrev primeResidueFieldDerivedHomology (p : PrimeSpectrum R) (K : DModR) (i : ℤ) :
    ModuleCat p.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat p.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[p.asIdeal.ResidueField])

/- Domain-style sampling for Lemma 15.78.1:
- primary domain: pseudo-coherent bounded-below objects of `D(R)`, residue-field derived homology,
  and localized finite-free / perfect representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfect` from `Definition_15_75_1`,
  `primeResidueFieldDerivedHomology`,
  `exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPerfect` from
    `Lemma_15_76_7`,
  `exists_localizationAway_gapSplit_of_residueField_homology_isZero` from `Lemma_15_77_4`;
- best owner abstraction: this file is `source-facing` for the bounded-below pseudo-coherent
  criterion, but the bounded-above finite-free representative is already owned upstream by
  `CochainComplex.MinusWithTermsIn`, so the public representative statement here should reuse that
  owner instead of a parallel raw `CochainComplex` witness;
- primitive vs. derived:
  primitive data are `p`, `K`, the lower bound `a`, the pseudo-coherence / bounded-below
  hypotheses, and the vanishing below `a` of the internally defined residue-field dimensions
  `dim_{κ(𝔭)} H^i(K ⊗^L κ(𝔭))`;
  derived API is the away-localized bounded finite-free representative with terms of rank
  `Module.finrank` of those residue-field homology groups, and the resulting localized
  perfectness;
- source/core/bridge triage:
  `source-facing`: the two existence theorems below;
  `core/canonical`: `K.IsPerfect` and `CochainComplex.MinusWithTermsIn`;
  `bridge/view`: `primeResidueFieldDerivedHomology` and the gap-splitting localization theorem
    from `15.77.4`, which feed the perfectness bridge from `15.76.7`.
-/

variable
    (p : PrimeSpectrum R) (K : DModR) (a : ℤ)
    (hK : K.IsPseudoCoherent)
    (hboundedBelow : ∃ n : ℤ, K.IsGE n)
    (hda :
      ∀ i : ℤ,
        i < a →
          Module.rank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = 0)

include p K a hK hboundedBelow hda

/-- Helper for Lemma 15.78.1: over the residue field `κ(𝔭)`, rank `0` forces the derived
homology object to be zero. -/
lemma primeResidueFieldDerivedHomology_isZero_of_rank_zero
    (i : ℤ)
    (hi :
      Module.rank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = 0) :
    IsZero (primeResidueFieldDerivedHomology p K i) := by
  let b := Module.Free.chooseBasis p.asIdeal.ResidueField
    (primeResidueFieldDerivedHomology p K i)
  have hb :
      Cardinal.mk
          (Module.Free.ChooseBasisIndex p.asIdeal.ResidueField
            (primeResidueFieldDerivedHomology p K i)) = 0 := by
    -- Proof comment: the chosen basis computes the module rank, so the rank-zero hypothesis
    -- forces the basis index type to be empty.
    calc
      Cardinal.mk
          (Module.Free.ChooseBasisIndex p.asIdeal.ResidueField
            (primeResidueFieldDerivedHomology p K i)) =
          Module.rank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) := by
        simpa [b] using Module.Basis.mk_eq_rank'' b
      _ = 0 := hi
  have hindex :
      IsEmpty
        (Module.Free.ChooseBasisIndex p.asIdeal.ResidueField
          (primeResidueFieldDerivedHomology p K i)) :=
    Cardinal.mk_eq_zero_iff.mp hb
  rw [ModuleCat.isZero_iff_subsingleton]
  let _ :
      IsEmpty
        (Module.Free.ChooseBasisIndex p.asIdeal.ResidueField
          (primeResidueFieldDerivedHomology p K i)) := hindex
  -- Proof comment: with empty basis index, the basis representation identifies the module with a
  -- finitely supported function type on the empty set, hence with a subsingleton.
  exact b.repr.injective.subsingleton

/-- Helper for Lemma 15.78.1: a complex whose terms are linearly equivalent to the zero free
module in all degrees `< a` is strictly supported in degrees `≥ a`. -/
lemma isStrictlyGE_of_linearEquiv_zero_below
    {f : R} (P : CpxAway[f])
    (hzero :
      ∀ i : ℤ,
        i < a →
          Nonempty (P.X i ≃ₗ[Localization.Away f] (Fin 0 → Localization.Away f))) :
    P.IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rcases hzero i hi with ⟨e⟩
  rw [ModuleCat.isZero_iff_subsingleton]
  -- Proof comment: a linear equivalence with the zero free module forces the source term to be
  -- subsingleton, hence zero in `ModuleCat`.
  exact e.injective.subsingleton

/-- Helper for Lemma 15.78.1: a bounded-above finite-free away-local complex that also vanishes
below some degree is a perfect object of the localized derived category. -/
lemma q_obj_isPerfect_of_boundedFiniteFreeAway
    {f : R} (P : BoundedFiniteFreeCpxAway[f])
    (hPge : (P : CpxAway[f]).IsStrictlyGE a) :
    (DerivedCategory.Q.obj (P : CpxAway[f])).IsPerfect := by
  obtain ⟨b, hPle⟩ :=
    CochainComplex.MinusWithTermsIn.exists_isStrictlyLE (P := FiniteFreeClassAway[f]) P
  let hBoundedFiniteProjective :
      CochainComplex.IsBoundedFiniteProjective (P : CpxAway[f]) :=
    { bounded := ⟨a, b, hPge, hPle⟩
      finite := fun i ↦ (P.term_mem i).2
      projective := fun i ↦ by
        let _ : Module.Free (Localization.Away f) ((P : CpxAway[f]).X i) := (P.term_mem i).1
        -- Proof comment: free modules are projective, so every term of `P` is finite
        -- projective.
        exact Module.Projective.of_free }
  -- Proof comment: the bounded finite-projective witness is already in the exact shape required
  -- by the definition of `DerivedCategory.IsPerfect`.
  exact ⟨(P : CpxAway[f]), Iso.refl _, hBoundedFiniteProjective⟩

/-- Helper for Lemma 15.78.1: flat scalar extension preserves the same lower cohomological
bound. -/
lemma isGE_derivedTensorWithAlgebra_of_isGE
    {R' : Type u} [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (L : DerivedCategory (ModuleCat.{u} R)) {n : ℤ} (hL : L.IsGE n) :
    ((derivedTensorWithAlgebra (algebraMap R R')).obj L).IsGE n := by
  -- Route correction: transport the vanishing range through the public flat homology comparison
  -- and the public identification of exact scalar extension with the derived tensor owner.
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars.{u, u, u} (algebraMap R R')
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R R')).left_adjoint_additive
  letI : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R R' from inferInstance))
  rw [DerivedCategory.isGE_iff] at hL ⊢
  intro i hi
  have hzero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L) :=
    hL i hi
  have hzeroExtended :
      IsZero (F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L)) :=
    F.map_isZero hzero
  have hzeroMapDerived :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj (F.mapDerivedCategory.obj L)) :=
    (extendScalars_homology_iso_of_flat.{u} (R := R) (R' := R') L i).isZero_iff.1
      hzeroExtended
  -- Proof comment: after identifying exact flat scalar extension with the derived tensor owner,
  -- the same homology vanishing statement becomes the desired `IsGE` bound.
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).mapIso
      ((extendScalars_mapDerivedCategory_iso_of_flat.{u} (R := R) (R' := R')).app L)).isZero_iff.1
      hzeroMapDerived

/-- Helper for Lemma 15.78.1: if the left summand is zero, then the projection onto the right
summand is an isomorphism. -/
lemma biprod_snd_isIso_of_isZero_left
    {X Y : DModR} [HasBinaryBiproduct X Y] (hX : IsZero X) :
    IsIso (biprod.snd : X ⊞ Y ⟶ Y) := by
  letI : IsZero X := hX
  have hfst_zero : (biprod.fst : X ⊞ Y ⟶ X) = 0 := by
    exact hX.eq_of_tgt _ _
  -- Proof comment: `biprod.inr` is a two-sided inverse once the left summand vanishes.
  refine ⟨⟨biprod.inr, ?_, ?_⟩⟩
  · apply biprod.hom_ext
    · simpa [Category.assoc, hfst_zero]
    · simp [Category.assoc]
  · simp

/-- Helper for Lemma 15.78.1: source-faithful gap splitting after killing one residue-field
homology group. -/
lemma exists_localizationAway_gapSplit_of_residueField_homology_isZero_local
    (i : ℤ)
    (hHi : IsZero (primeResidueFieldDerivedHomology p K i)) :
    ∃ f : R, f ∉ p.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι (i - 1)).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := by
  -- Proof comment: this is exactly the canonical gap-splitting theorem from `Lemma 15.77.4`,
  -- rewritten through the local abbreviation for the prime residue-field homology object.
  simpa [primeResidueFieldDerivedHomology] using
    exists_localizationAway_gapSplit_of_residueField_homology_isZero
      (𝔭 := p) K i hK hHi

-- Proof sketch: use the bounded-below hypothesis to lower the vanishing index to the chosen
-- bound `a`, so `H^i(K) = 0` for `i < a`. The condition that the internally defined residue-field
-- dimension is zero for `i < a` turns the residue-field homology in those degrees into zero
-- objects, and Lemma `15.77.4` then yields, after inverting some `f ∉ 𝔭`, a splitting with
-- perfect upper truncation `τ_{\ge a}`. The lower truncation vanishes because `K` is bounded
-- below, so the localization is perfect; then Lemma `15.76.7 (1)` gives finite-dimensionality of
-- the residue-field homology, and Lemma `15.76.7 (2)` yields the finite-interval free
-- representative with the corresponding termwise ranks.
/-- Lemma 15.78.1: let `R` be a commutative ring, let `𝔭 ⊂ R` be a prime, and let `K` be a
pseudo-coherent bounded-below object of `D(R)`. Set
`d i = dim_{κ(𝔭)} H^i(K \otimes_R^{\mathbf L} κ(𝔭))`. If `d i = 0` for all `i < a`, then after
inverting some `f ∉ 𝔭`, the localized derived object `K \otimes_R^{\mathbf L} R_f` is
represented by a bounded-above finite-free cochain complex whose degree-`i` term is free of rank
`dim_{κ(𝔭)} H^i(K \otimes_R^{\mathbf L} κ(𝔭))` and which vanishes in degrees `< a`. -/
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE
    :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (Module.finrank p.asIdeal.ResidueField
              (primeResidueFieldDerivedHomology p K i)) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) :=
  by
    -- Proof comment: the source-faithful route is to obtain localized perfectness from the gap
    -- splitting theorem `15.77.4`, then apply `15.76.7` over the localized ring, and finally use
    -- the zero-rank hypothesis below `a` to upgrade the lower support bound to exactly `a`.
    have hboundedBelow_saved : ∃ n : ℤ, K.IsGE n := hboundedBelow
    rcases hboundedBelow with ⟨n, hKn⟩
    let n₀ : ℤ := min n a
    have hKn₀ : K.IsGE n₀ := by
      -- Proof comment: lower bounds can be weakened, so we move the bounded-below cutoff down to
      -- the chosen source-proof index `n₀ ≤ a`.
      let _ : K.IsGE n := hKn
      let _ : K.IsGE n₀ :=
        DerivedCategory.TStructure.t.isGE_of_ge
          (C := DerivedCategory (ModuleCat R))
          (X := K) (p := n₀) (q := n) (hpq := by
            dsimp [n₀]
            exact min_le_left _ _)
      infer_instance
    have hzeroFiber :
        IsZero (primeResidueFieldDerivedHomology p K (n₀ - 1)) := by
      exact
        primeResidueFieldDerivedHomology_isZero_of_rank_zero
          (p := p) (K := K) (a := a) (hK := hK) (hboundedBelow := hboundedBelow_saved)
          (hda := hda) (i := n₀ - 1)
          (hda (n₀ - 1) (by
            dsimp [n₀]
            omega))
    rcases
        exists_localizationAway_gapSplit_of_residueField_homology_isZero_local
          (p := p) (K := K) (a := a) (hK := hK) (hboundedBelow := hboundedBelow_saved)
          (hda := hda) (n₀ - 1) hzeroFiber with
      ⟨f₀, hf₀, hperfTop, _hAmpTop, hsplit⟩
    have hKf₀_ge_n₀ :
        (K ⊗[R]^L[Localization.Away f₀]).IsGE n₀ := by
      -- Proof comment: localization is flat, so the lower cohomological bound survives after
      -- tensoring with `R_{f₀}`.
      exact isGE_derivedTensorWithAlgebra_of_isGE (R := R) (R' := Localization.Away f₀) K hKn₀
    have hKf₀_ge_prev :
        (K ⊗[R]^L[Localization.Away f₀]).IsGE (n₀ - 1) := by
      let _ : (K ⊗[R]^L[Localization.Away f₀]).IsGE n₀ := hKf₀_ge_n₀
      -- Proof comment: we lower the bound once more so that the left truncation
      -- `τ_{\le n₀ - 2}` is canonically zero.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact DerivedCategory.isZero_of_isGE
        (K ⊗[R]^L[Localization.Away f₀]) n₀ i (by omega)
    have hlowZero :
        IsZero ((t.truncLE (n₀ - 2)).obj (K ⊗[R]^L[Localization.Away f₀])) := by
      let _ : (K ⊗[R]^L[Localization.Away f₀]).IsGE (n₀ - 1) := hKf₀_ge_prev
      -- Proof comment: a lower-bounded object has zero left truncation strictly below that
      -- bound.
      simpa using
        t.isZero_truncLE_obj_of_isGE (n₀ - 2) (n₀ - 1) rfl
          (K ⊗[R]^L[Localization.Away f₀])
    rcases hsplit.exists with ⟨eGap, _heGapLeft, _heGapRight⟩
    have hsplitPerfect :
        (((t.truncLE (n₀ - 2)).obj (K ⊗[R]^L[Localization.Away f₀])) ⊞
          ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀]))).IsPerfect := by
      let _ :
          IsIso
            (biprod.snd :
              ((t.truncLE (n₀ - 2)).obj (K ⊗[R]^L[Localization.Away f₀])) ⊞
                  ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀])) ⟶
                ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀]))) :=
        biprod_snd_isIso_of_isZero_left (R := R) hlowZero
      let eSplit :
          (((t.truncLE (n₀ - 2)).obj (K ⊗[R]^L[Localization.Away f₀])) ⊞
            ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀]))) ≅
              ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀])) :=
        asIso
          (biprod.snd :
            ((t.truncLE (n₀ - 2)).obj (K ⊗[R]^L[Localization.Away f₀])) ⊞
                ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀])) ⟶
              ((t.truncGE n₀).obj (K ⊗[R]^L[Localization.Away f₀])))
      -- Proof comment: once the left summand vanishes, the gap-split object is isomorphic to the
      -- perfect upper truncation.
      exact DerivedCategory.IsPerfect.prop_of_iso eSplit hperfTop
    have hperf₀ :
        (K ⊗[R]^L[Localization.Away f₀]).IsPerfect := by
      -- Proof comment: the source proof concludes localized perfectness by identifying the whole
      -- localized object with the perfect upper truncation once the lower truncation vanishes.
      exact DerivedCategory.IsPerfect.prop_of_iso eGap hsplitPerfect
    -- Route correction: the initial failed route tried to jump directly from `hperf₀` to the
    -- final explicit away model over `R`. The remaining source-faithful blocker is the perfect
    -- case bridge that descends a representative built after localizing at the prime over `p`
    -- back to a single further principal localization of `R`.
    -- TODO: instantiate the perfect-case representative theorem over `Localization.Away f₀`,
    -- compare the corresponding prime residue-field homology with the original one at `p`, and
    -- normalize the resulting away-of-away localization to a single `Localization.Away g` of `R`.
    sorry

-- Proof sketch: apply the representative theorem above and then use the fact that a bounded
-- complex of finite free modules is perfect in the derived category.
/-- If the residue-field homology of `K` has dimension `0` in all degrees `< a`, then after
inverting some element away from `𝔭`, the localized derived complex is perfect. -/
theorem exists_away_isPerfect_of_primeResidueFieldDerivedHomology_vanishing_below
    :
    ∃ f : R, f ∉ p.asIdeal ∧
      (K ⊗[R]^L[Localization.Away f]).IsPerfect := by
  rcases
      exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE
        (p := p) (K := K) (a := a) (hK := hK) (hboundedBelow := hboundedBelow) (hda := hda) with
    ⟨f, hf, P, hPge, _hterms, ⟨e⟩⟩
  have hPperfect :
      (DerivedCategory.Q.obj (P : CpxAway[f])).IsPerfect :=
    q_obj_isPerfect_of_boundedFiniteFreeAway (a := a) P hPge
  -- Proof comment: the representative theorem gives an isomorphism from the localized object to
  -- the explicit bounded finite-free model, so perfectness transfers across that isomorphism.
  exact ⟨f, hf, DerivedCategory.IsPerfect.prop_of_iso e hPperfect⟩

end

end CategoryTheory
