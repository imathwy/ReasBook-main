import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import StacksProject_2024.stacks_project.Chap10.Lemma_10_109_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open TrivSqZeroExt
open scoped DualNumber

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε
local notation "dε" => LinearMap.mulLeft Rε (ε : Rε)

/- Domain-style sampling:
- primary domain: dual numbers as a trivial square-zero extension, together with the explicit
  `ε`-periodic cochain complex in `ModuleCat Rε`;
- inspected owner declarations:
  `TrivSqZeroExt.kerIdeal`,
  `Ideal.Quotient.mkₐ`,
  `Ideal.Quotient.mkₐ_eq_mk`,
  `DualNumber.eps_mul_eps`,
  `CochainComplex.of`;
- best owner abstraction:
  `source-facing`: the residue module `R / (ε)` and the explicit periodic complex
    `R --ε→ R --ε→ ⋯`;
  `core/canonical`: `TrivSqZeroExt.kerIdeal` for the ideal `(ε)` and `CochainComplex.of` for the
    complex, with `Ideal.Quotient.mkₐ` for the quotient algebra map;
  `bridge/view`: the quotient presentation of `R / (ε)` by the kernel ideal of
    `TrivSqZeroExt.fstHom`;
- primitive data: the dual-number ring `Rε` and multiplication by `ε`;
- derived API: the residue module, quotient map, periodic complex, augmentation, and the
  projective-dimension statements below. -/

/-- The residue module `R / (ε)` for the dual numbers `R`, realized via the canonical kernel ideal
of `TrivSqZeroExt.fstHom`. -/
abbrev dualNumbersResidueModule : ModRε :=
  ModuleCat.of Rε (Rε ⧸ kerIdeal k k)

/-- Multiplication by `ε` on the dual numbers, viewed as an endomorphism of the free rank-one
module `R`. -/
def dualNumbersPeriodicDifferential : ModuleCat.of Rε Rε ⟶ ModuleCat.of Rε Rε :=
  ModuleCat.ofHom (LinearMap.mulLeft Rε (ε : Rε))

/-- Helper for Example 15.69.3: multiplying a dual number by `ε` keeps only its scalar part in the
square-zero direction. -/
theorem dualNumbersPeriodicDifferential_apply (x : Rε) :
    (dualNumbersPeriodicDifferential k).hom x = TrivSqZeroExt.inr x.fst := by
  -- Normalize multiplication by `ε` to the explicit trivial-square-zero-extension formula.
  ext <;> simp [dualNumbersPeriodicDifferential, LinearMap.mulLeft_apply]

-- Proof sketch: `ε` is square-zero in the trivial square-zero extension, so composing left
-- multiplication by `ε` with itself is left multiplication by `ε^2 = 0`.
/-- Left multiplication by `ε` squares to zero on the dual numbers. -/
theorem dualNumbersPeriodicDifferential_sq :
    dualNumbersPeriodicDifferential k ≫ dualNumbersPeriodicDifferential k = 0 := by
  -- Route correction: prove the square-zero relation at the level of endomorphisms before using
  -- it to build exact short complexes.
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun x ↦ by
    change (ε : Rε) * ((ε : Rε) * x) = 0
    rw [← mul_assoc, DualNumber.eps_mul_eps, zero_mul]

/-- The infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` over the dual numbers. -/
def dualNumbersPeriodicComplex : CochainComplex ModRε ℕ :=
  CochainComplex.of
    (fun _ ↦ ModuleCat.of Rε Rε)
    (fun _ ↦ dualNumbersPeriodicDifferential k)
    (fun _ ↦ dualNumbersPeriodicDifferential_sq k)

/-- The canonical augmentation from the periodic `ε`-complex to the module `R / (ε)` concentrated
in degree `0`. -/
def dualNumbersPeriodicAugmentation :
    dualNumbersPeriodicComplex k ⟶
      (CochainComplex.single₀ ModRε).obj (dualNumbersResidueModule k) :=
  (CochainComplex.toSingle₀Equiv
      (dualNumbersPeriodicComplex k)
      (dualNumbersResidueModule k)).symm
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)

/-- Helper for Example 15.69.3: the degree-zero component of the periodic augmentation is exactly
the quotient map `R → R/(ε)`. -/
theorem dualNumbersPeriodicAugmentation_f_zero :
    (dualNumbersPeriodicAugmentation k).f 0 =
      ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap := by
  -- The `toSingle₀` equivalence is definitionally the quotient map in degree `0`.
  rfl

/-- Helper for Example 15.69.3: the kernel of multiplication by `ε` is the square-zero ideal
`(ε)`. -/
theorem dualNumbers_mul_eps_ker_eq_kerIdeal :
    LinearMap.ker dε = kerIdeal k k := by
  -- Identify kernel elements by reading off the scalar part of `ε * x`.
  ext x
  constructor
  · intro hx
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
    have hfst : x.fst = 0 := by
      have hsnd := congrArg TrivSqZeroExt.snd hx
      simpa [dualNumbersPeriodicDifferential_apply] using hsnd
    ext <;> simp [hfst]
  · intro hx
    rw [LinearMap.mem_ker]
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at hx
    rw [hx]
    ext <;> simp [LinearMap.mulLeft_apply]

/-- Helper for Example 15.69.3: the image of multiplication by `ε` is the square-zero ideal
`(ε)`. -/
theorem dualNumbers_mul_eps_range_eq_kerIdeal :
    LinearMap.range dε = kerIdeal k k := by
  -- The image consists exactly of elements of the form `inr r`, which generate `(ε)`.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
    ext <;> simp [LinearMap.mulLeft_apply]
  · intro hx
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [hx]
    ext <;> simp [LinearMap.mulLeft_apply]

/-- Helper for Example 15.69.3: the quotient map to `R / (ε)` has kernel `(ε)` as a linear map. -/
theorem dualNumbersResidueModule_quotient_ker :
    LinearMap.ker ((Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap) = kerIdeal k k := by
  -- The linear kernel is the usual quotient kernel expressed in module language.
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Helper for Example 15.69.3: multiplication by `ε` has equal image and kernel. -/
theorem dualNumbers_mul_eps_range_eq_ker :
    LinearMap.range dε = LinearMap.ker dε := by
  -- Both source-side invariants identify with the ideal `(ε)`.
  rw [dualNumbers_mul_eps_range_eq_kerIdeal, dualNumbers_mul_eps_ker_eq_kerIdeal]

/-- Helper for Example 15.69.3: the quotient map `R → R/(ε)` is exact after multiplication by
`ε`. -/
theorem dualNumbersResidueModule_exact :
    (ShortComplex.mk
      (dualNumbersPeriodicDifferential k)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
      (by
        -- Elements in the image of `ε` lie in the quotient kernel.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x ↦ by
          change Ideal.Quotient.mk (kerIdeal k k) ((dualNumbersPeriodicDifferential k).hom x) = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
            rw [← dualNumbers_mul_eps_range_eq_kerIdeal]
            exact ⟨x, rfl⟩)).Exact := by
  -- Exactness is the statement that the image of multiplication by `ε` equals the quotient kernel.
  let S : ShortComplex ModRε :=
    ShortComplex.mk
      (dualNumbersPeriodicDifferential k)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
      (by
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x ↦ by
          change Ideal.Quotient.mk (kerIdeal k k) ((dualNumbersPeriodicDifferential k).hom x) = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
            rw [← dualNumbers_mul_eps_range_eq_kerIdeal]
            exact ⟨x, rfl⟩)
  change S.Exact
  rw [S.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((dualNumbersPeriodicDifferential k).hom) =
    LinearMap.ker ((Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
  rw [dualNumbersResidueModule_quotient_ker]
  simpa [S, dualNumbersPeriodicDifferential] using dualNumbers_mul_eps_range_eq_kerIdeal k

/-- Helper for Example 15.69.3: quotienting by `(ε)` identifies the residue module with the image
of multiplication by `ε`. -/
noncomputable def dualNumbersResidueModuleEquivRange :
    dualNumbersResidueModule k ≃ₗ[Rε] LinearMap.range dε :=
  (Submodule.quotEquivOfEq
      (kerIdeal k k)
      (LinearMap.ker dε)
      (dualNumbers_mul_eps_ker_eq_kerIdeal k).symm).trans
    ((LinearMap.mulLeft Rε (ε : Rε)).quotKerEquivRange)

-- Proof sketch: every term of `dualNumbersPeriodicComplex` is the free rank-one module `R`, hence
-- projective in `ModuleCat R`.
/-- Each term of the periodic dual-numbers complex is projective. -/
theorem dualNumbersPeriodicComplex_projective (n : ℕ) :
    Projective ((dualNumbersPeriodicComplex k).X n) := by
  -- Every term is definitionally the free rank-one module `Rε`.
  change Projective (ModuleCat.of Rε Rε)
  infer_instance

-- Proof sketch: identify the degree-zero homology of the periodic `ε`-complex with `R / (ε)` and
-- check that the higher homology vanishes because consecutive differentials are both multiplication
-- by the square-zero element `ε`.
/-- Example 15.69.3: for the dual numbers `R = k[ε]/(ε^2)` over a commutative ring `k` and
`M = R / (ε)`, the canonical
augmentation from the infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` to the
degree-zero complex `M[0]` is a quasi-isomorphism. Lean uses the canonical owner
`DualNumber k` for `R`, definitionally `TrivSqZeroExt k k`. -/
theorem dualNumbersResidueModule_quasiIso_periodicComplex :
    QuasiIso (dualNumbersPeriodicAugmentation k) := by
  -- Route correction: the degree-zero component is definitionally the quotient map `R → R/(ε)`,
  -- so the current augmentation kills the degree-zero cycles `(ε)` instead of identifying them
  -- with `R/(ε)`.
  -- TODO: the current statement appears mathematically inconsistent as written. A source-faithful
  -- repair likely needs either a shifted complex or a different augmentation map at degree `0`.
  sorry

end

section

variable (k : Type u) [CommRing k] [Nontrivial k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε
local notation "dε" => LinearMap.mulLeft Rε (ε : Rε)

/-- Helper for Example 15.69.3: the range of multiplication by `ε` gives the canonical short exact
sequence `0 → range(·ε) → R → R/(ε) → 0`. -/
theorem dualNumbersResidueModule_range_shortExact :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.range dε).subtype)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
      (by
        -- The quotient kills the range because the range is exactly `(ε)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x ↦ by
          change Ideal.Quotient.mk (kerIdeal k k) x.1 = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
            rw [← dualNumbers_mul_eps_range_eq_kerIdeal]
            exact x.2)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Exactness reduces to `range = ker` for the inclusion and quotient maps.
    let S : ShortComplex ModRε :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.range dε).subtype)
        (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
        (by
          apply ModuleCat.hom_ext
          exact LinearMap.ext fun x ↦ by
            change Ideal.Quotient.mk (kerIdeal k k) x.1 = 0
            exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
              rw [← dualNumbers_mul_eps_range_eq_kerIdeal]
              exact x.2)
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range ((ModuleCat.ofHom (LinearMap.range dε).subtype : _).hom) =
      LinearMap.ker ((Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)
    rw [dualNumbersResidueModule_quotient_ker]
    simpa [S, Submodule.range_subtype] using dualNumbers_mul_eps_range_eq_kerIdeal k
  · exact (ModuleCat.mono_iff_injective _).2 fun x y h => Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).2 (Ideal.Quotient.mkₐ_surjective Rε (kerIdeal k k))

/-- Helper for Example 15.69.3: the residue module over the dual numbers is not projective over a
nontrivial base ring. -/
theorem dualNumbersResidueModule_not_projective :
    ¬ Projective (dualNumbersResidueModule k) := by
  intro hproj
  letI : Module.Projective Rε (Rε ⧸ kerIdeal k k) :=
    (IsProjective.iff_projective (R := Rε) (P := Rε ⧸ kerIdeal k k)).2 hproj
  let π : Rε →ₗ[Rε] (Rε ⧸ kerIdeal k k) :=
    (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap
  let s : (Rε ⧸ kerIdeal k k) →ₗ[Rε] Rε :=
    Classical.choose
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective Rε (kerIdeal k k)))
  have hs : π.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective Rε (kerIdeal k k)))
  let a : Rε := s 1
  have hπa : π a = 1 := by
    -- The chosen lift is a section of the quotient map on the class of `1`.
    change (π.comp s) 1 = 1
    simpa [a, hs]
  have hεa : (ε : Rε) * a = 0 := by
    -- The class of `ε` vanishes in `R/(ε)`, so `ε` annihilates the lifted generator.
    have hεquot : ((Ideal.Quotient.mk (kerIdeal k k) (ε : Rε)) : Rε ⧸ kerIdeal k k) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, TrivSqZeroExt.mem_kerIdeal_iff_inr]
      change (ε : Rε) = TrivSqZeroExt.inr (1 : k)
      rfl
    calc
      (ε : Rε) * a = (ε : Rε) • a := by simp [smul_eq_mul]
      _ = s ((ε : Rε) • (1 : Rε ⧸ kerIdeal k k)) := by
        simpa [a, smul_eq_mul] using (s.map_smul (ε : Rε) (1 : Rε ⧸ kerIdeal k k)).symm
      _ = s 0 := by
        congr 1
        calc
          (ε : Rε) • (1 : Rε ⧸ kerIdeal k k) =
              ((Ideal.Quotient.mk (kerIdeal k k) (ε : Rε)) : Rε ⧸ kerIdeal k k) * 1 := by
                rfl
          _ = 0 := by
            rw [hεquot]
            simp
      _ = 0 := by simp
  let e : Rε := 1 - a
  have hπa' : ((Ideal.Quotient.mk (kerIdeal k k) a) : Rε ⧸ kerIdeal k k) = 1 := by
    -- Rewrite the section equation in the quotient-ring presentation.
    simpa [π, Ideal.Quotient.mkₐ_eq_mk Rε (kerIdeal k k)] using hπa
  have he_mem : e ∈ kerIdeal k k := by
    -- The complementary element `e = 1 - a` lies in the kernel ideal.
    have hπe' : ((Ideal.Quotient.mk (kerIdeal k k) e) : Rε ⧸ kerIdeal k k) = 0 := by
      dsimp [e]
      change (1 : Rε ⧸ kerIdeal k k) - Ideal.Quotient.mk (kerIdeal k k) a = 0
      simpa using sub_eq_zero.mpr hπa'.symm
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hπe'
  have hε_mem : (ε : Rε) ∈ kerIdeal k k := by
    -- The dual-number generator `ε` is itself a generator of the square-zero ideal.
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
    change (ε : Rε) = TrivSqZeroExt.inr (1 : k)
    rfl
  have hε_square : (ε : Rε) ∈ (kerIdeal k k) ^ 2 := by
    -- Since `ε a = 0` and `e = 1 - a ∈ (ε)`, we obtain `ε = ε e ∈ (ε)^2`.
    rw [pow_two]
    rw [show (ε : Rε) = (ε : Rε) * e by
      simpa [e, sub_eq_add_neg, mul_add, hεa] using (mul_one (ε : Rε)).symm]
    exact Ideal.mul_mem_mul hε_mem he_mem
  have hε_zero : (ε : Rε) = 0 := by
    -- But the square-zero ideal has square zero, so membership in `(ε)^2` forces `ε = 0`.
    have hbot : (ε : Rε) ∈ (⊥ : Ideal Rε) := by
      simpa [TrivSqZeroExt.kerIdeal_sq k k] using hε_square
    simpa using hbot
  have hsnd := congrArg TrivSqZeroExt.snd hε_zero
  change (1 : k) = 0 at hsnd
  exact one_ne_zero hsnd

/-- Helper for Example 15.69.3: any finite projective-dimension bound for the residue module
descends along the periodic self-syzygy short exact sequence to projectivity. -/
theorem dualNumbersResidueModule_projective_of_hasProjectiveDimensionLE :
    ∀ n : ℕ, HasProjectiveDimensionLE (dualNumbersResidueModule k) n →
      Projective (dualNumbersResidueModule k)
  | 0, hpd => (projective_iff_hasProjectiveDimensionLE_zero _).2 hpd
  | n + 1, hpd => by
      -- Descend the projective-dimension bound across `0 → range(·ε) → R → R/(ε) → 0`.
      have hR : HasProjectiveDimensionLE (ModuleCat.of Rε Rε) n := by
        letI : Projective (ModuleCat.of Rε Rε) := dualNumbersPeriodicComplex_projective k 0
        infer_instance
      have hrange : HasProjectiveDimensionLE
          (ModuleCat.of Rε (LinearMap.range dε)) n := by
        exact CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₁
          (dualNumbersResidueModule_range_shortExact k)
          n
          hR
          hpd
      have hresidue : HasProjectiveDimensionLE (dualNumbersResidueModule k) n := by
        letI : HasProjectiveDimensionLE (ModuleCat.of Rε (LinearMap.range dε)) n := hrange
        exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
          (M := ModuleCat.of Rε (LinearMap.range dε))
          (N := dualNumbersResidueModule k)
          ((dualNumbersResidueModuleEquivRange k).symm)
          n
      exact dualNumbersResidueModule_projective_of_hasProjectiveDimensionLE n hresidue

-- Proof sketch: if `R / (ε)` had finite projective dimension, some finite truncation of the
-- periodic projective resolution would force a projective syzygy. For the dual numbers this never
-- happens, because every syzygy is again isomorphic to `R / (ε)`.
/-- Over a nontrivial commutative ring, the residue module over the dual numbers does not have
finite projective dimension. -/
theorem dualNumbersResidueModule_projectiveDimension_eq_top :
    projectiveDimension (dualNumbersResidueModule k) = ⊤ := by
  -- A finite bound would descend inductively to projectivity, contradicting the splitting
  -- obstruction for the quotient by `(ε)`.
  by_contra htop
  rcases (projectiveDimension_ne_top_iff (dualNumbersResidueModule k)).1 htop with ⟨n, hn⟩
  have hproj : Projective (dualNumbersResidueModule k) :=
    dualNumbersResidueModule_projective_of_hasProjectiveDimensionLE k n hn
  exact dualNumbersResidueModule_not_projective k hproj

end
