import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent
import StacksProject_2024.Chap10.Lemma_10_71_4
import StacksProject_2024.Chap10.Lemma_10_75_7
import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_102_2
import StacksProject_2024.Chap10.Lemma_10_108_6.ExteriorPowerBaseChange
import StacksProject_2024.Chap10.Lemma_10_109_7
import StacksProject_2024.Chap10.Situation_10_102_1
import Mathlib.Tactic.StacksAttribute

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: the residue-field module is nonzero in `ModuleCat R`. -/
lemma residueField_module_not_isZero :
    ¬ Limits.IsZero (ModuleCat.of R (ResidueField R)) := by
  -- A field is nontrivial, so its image in `ModuleCat` cannot be a zero object.
  intro hzero
  have hsub :
      Subsingleton (ResidueField R) :=
    (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R (ResidueField R))).1 hzero
  have hnontrivial : Nontrivial (ResidueField R) := inferInstance
  exact (not_subsingleton_iff_nontrivial.mpr hnontrivial) hsub

/-- Helper for Lemma 10.110.3: a successor projective-dimension bound on the residue field
produces a bounded finite free resolution of the preceding length. -/
lemma residueField_hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLT_succ
    {d : ℕ}
    (hpd : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (d + 1)) :
    HasFiniteFreeResolutionLengthLE R (ResidueField R) d := by
  -- Rewrite `< d + 1` as `≤ d`, then invoke the finite-free-resolution bridge from
  -- Lemma `10.109.7`.
  have hle : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d := by
    simpa [CategoryTheory.HasProjectiveDimensionLE] using hpd
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := R) (M := ResidueField R) d).1 hle

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: unpack a bounded finite free resolution of the residue field into a
chosen augmented chain complex with termwise free and finite modules. -/
lemma exists_residueField_finiteFreeResolution_data
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution π ∧
        ChainComplex.IsTermwiseFree F ∧
        ChainComplex.IsTermwiseFinite F ∧
        ∀ n : ℕ, d < n → Limits.IsZero (F.X n) := by
  rcases hres with ⟨F, π, hπ, hbound⟩
  refine ⟨F, π, hπ, ?_, ?_, hbound⟩
  · -- Forget the finiteness decoration and read termwise freeness from the resolution owner.
    intro n
    exact ChainComplex.IsFreeResolution.free (R := R) (M := ResidueField R) π n
  · -- The finite-free-resolution owner also records finiteness of every term.
    intro n
    exact ChainComplex.IsFiniteFreeResolution.finite π n

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a bounded finite free resolution of the residue field already
vanishes in the first degree strictly above its length bound. -/
lemma residueField_finiteFreeResolution_succ_isZero
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution π ∧
        ChainComplex.IsTermwiseFree F ∧
        ChainComplex.IsTermwiseFinite F ∧
        Limits.IsZero (F.X (d + 1)) := by
  obtain ⟨F, π, hπ, hFfree, hFfinite, hbound⟩ :=
    exists_residueField_finiteFreeResolution_data (R := R) hres
  refine ⟨F, π, hπ, hFfree, hFfinite, ?_⟩
  -- Apply the stored bound in the first degree above the allowed resolution length.
  exact hbound (d + 1) (Nat.lt_succ_self d)

/-- Helper for Lemma 10.110.3: once the cotangent space has dimension `d + 1`, we can choose a
`Fin (d + 1)`-indexed basis and lift it to generators of the maximal ideal. -/
lemma cotangent_basis_lift_generates_maximalIdeal
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    ∃ b : Module.Basis (Fin (d + 1)) (ResidueField R) (CotangentSpace R),
      ∃ x : Fin (d + 1) → maximalIdeal R,
        (∀ i, (maximalIdeal R).toCotangent (x i) = b i) ∧
          Submodule.span R (Set.range x) = ⊤ := by
  let _ : Module.Finite (ResidueField R) (CotangentSpace R) :=
    Module.finite_of_finrank_eq_succ hfinrank
  let b : Module.Basis (Fin (d + 1)) (ResidueField R) (CotangentSpace R) :=
    Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hfinrank
  choose x hx using fun i : Fin (d + 1) ↦ (maximalIdeal R).toCotangent_surjective (b i)
  have himage :
      (maximalIdeal R).toCotangent '' Set.range x =
        Set.range fun i : Fin (d + 1) ↦ (maximalIdeal R).toCotangent (x i) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  have hspan_image :
      Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' Set.range x) = ⊤ := by
    -- The chosen lifts hit each basis vector, so their images already span the cotangent space.
    rw [himage]
    simpa [hx] using b.span_eq
  have hspan :
      Submodule.span R (Set.range x) = ⊤ := by
    -- In a Noetherian local ring, generating the cotangent space is equivalent to generating `𝔪`.
    exact
      (CotangentSpace.span_image_eq_top_iff (R := R) (s := Set.range x)).1 hspan_image
  exact ⟨b, x, hx, hspan⟩

/-- Helper for Lemma 10.110.3: the top exterior power of a `(d + 1)`-dimensional cotangent space
is nontrivial. -/
lemma top_exterior_cotangentSpace_nontrivial
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    Nontrivial (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) := by
  let _ : Module.Finite (ResidueField R) (CotangentSpace R) :=
    Module.finite_of_finrank_eq_succ hfinrank
  let _ : Module.Free (ResidueField R) (CotangentSpace R) := inferInstance
  let _ : Module.Free (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) :=
    inferInstance
  let _ : Module.Finite (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) :=
    inferInstance
  have htop :
      Module.finrank (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) = 1 := by
    -- The top exterior power has basis indexed by the singleton subsets of the chosen basis.
    rw [exteriorPower.finrank_eq]
    simp [hfinrank]
  exact Module.nontrivial_of_finrank_eq_succ (R := ResidueField R) htop

omit [CommRing R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top exterior power of standard `n`-space over a field
is nontrivial. -/
lemma topExteriorFinFun_nontrivial (k : Type u) [Field k] (n : ℕ) :
    Nontrivial (⋀[k]^n (Fin n → k)) := by
  -- The exterior-power finrank formula gives dimension one in top degree.
  let _ : Module.Free k (⋀[k]^n (Fin n → k)) := inferInstance
  let _ : Module.Finite k (⋀[k]^n (Fin n → k)) := inferInstance
  have htop : Module.finrank k (⋀[k]^n (Fin n → k)) = 1 := by
    rw [exteriorPower.finrank_eq]
    simp
  exact Module.nontrivial_of_finrank_eq_succ (R := k) htop

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a finite free module admits standard coordinates `R^n` for some
natural number `n`. -/
lemma exists_fin_standard_coordinates
    (M : ModuleCat R) [Module.Free R M] [Module.Finite R M] :
    ∃ n : ℕ, Nonempty (M ≅ ModuleCat.of R (Fin n → R)) := by
  classical
  let b₀ : Module.Basis (Module.Free.ChooseBasisIndex R M) R M := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  letI : Finite ι := Module.Finite.finite_basis b₀
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis (Fin (Fintype.card ι)) R M := b₀.reindex (Fintype.equivFin ι)
  -- Reindex the chosen basis by `Fin` so the module matches the coordinate owner
  -- used in `FiniteFreeComplex`.
  exact ⟨Fintype.card ι, ⟨b.equivFun.toModuleIso⟩⟩

/-- Helper for Lemma 10.110.3: in degree `i`, a bounded termwise finite free complex has a chosen
coordinate rank compatible with `FiniteFreeComplex`. -/
noncomputable def bounded_resolution_rank
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (i : Fin (e + 1)) : ℕ :=
  letI := hFfree i
  letI := hFfinite i
  Classical.choose (exists_fin_standard_coordinates (R := R) (M := F.X i))

/-- Helper for Lemma 10.110.3: in degree `i`, a bounded termwise finite free complex has chosen
`Fin`-coordinates for its term. -/
noncomputable def bounded_resolution_termIso
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (i : Fin (e + 1)) :
    F.X i ≅ ModuleCat.of R (Fin (bounded_resolution_rank (R := R) F hFfree hFfinite i) → R) :=
  letI := hFfree i
  letI := hFfinite i
  Classical.choice
    (Classical.choose_spec (exists_fin_standard_coordinates (R := R) (M := F.X i)))

/-- Helper for Lemma 10.110.3: a bounded termwise finite free complex can be repackaged as a
`FiniteFreeComplex` without changing its underlying chain complex. -/
noncomputable def finiteFreeComplex_of_bounded_resolution
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (hbound : ∀ n : ℕ, e < n → Limits.IsZero (F.X n)) :
    FiniteFreeComplex R e :=
  { toChainComplex := F
    isZero_toChainComplex_X := hbound
    rank := bounded_resolution_rank (R := R) F hFfree hFfinite
    termIso := bounded_resolution_termIso (R := R) F hFfree hFfinite }

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: the packaged bounded resolution has the original chain complex as
its underlying owner. -/
@[simp] lemma finiteFreeComplex_of_bounded_resolution_toChainComplex
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (hbound : ∀ n : ℕ, e < n → Limits.IsZero (F.X n)) :
    (finiteFreeComplex_of_bounded_resolution (R := R) F hFfree hFfinite hbound).toChainComplex = F :=
  rfl

end
