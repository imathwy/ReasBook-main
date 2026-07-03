import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.HopkinsLevitzki

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_55_1 (from Chap10) -/
noncomputable section

universe u

section FiniteGrothendieckGroup

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

variable (R : Type u) [Ring R]

/- Domain-style sampling for Lemma 10.55.1:
- primary domain: additive invariants of `K'_0(R)` for finitely generated `R`-modules, with the
  invariant given by module length over an Artinian ring;
- sampled owner declarations:
  `ModulePropertyK0.lift`,
  `ModulePropertyK0.lift_of`,
  `finiteGrothendieckGroup`,
  `Module.length_eq_add_of_exact`;
- best owner abstraction:
  the public map `finiteGrothendieckGroup_lengthMap` should be presented as the canonical Chapter
  10 quotient lift of the generator-level length functional, not as a parallel wrapper around the
  same quotient construction;
- primitive vs. derived:
  primitive data is only the value on a finite module,
  `M ↦ ((Module.length R M.obj).toNat : ℤ)`;
  the kernel statement, descended homomorphism, and evaluation-on-generators theorem are derived
  from that owner abstraction;
- source/core/bridge triage:
  `source-facing`: `finiteGrothendieckGroup_lengthMap`;
  `core/canonical`: `ModulePropertyK0.lift`;
  `bridge/view`: the Artinian-length realization given by `Module.length`.

This file should therefore keep the length functional private at the generator level and expose
only the descended map together with its generator evaluation formula.
-/

-- Proof sketch: over an Artinian ring every finite module has finite length, and module length is
-- additive on short exact sequences by `Module.length_eq_add_of_exact`, so every Grothendieck
-- relation is sent to zero.
/-- Helper for Lemma 10.55.1: the generator-level length functional vanishes on the defining
Grothendieck relations coming from short exact sequences of finitely generated modules. -/
private theorem relations_le_ker_length [IsArtinianRing R] :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  let T : ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  let _ : Module.Finite R S.X₁.obj := S.X₁.property
  let _ : Module.Finite R S.X₂.obj := S.X₂.property
  let _ : Module.Finite R S.X₃.obj := S.X₃.property
  have hT : T.ShortExact := by
    simpa [T] using hS
  have hExact : Function.Exact T.f.hom T.g.hom := by
    simpa using (moduleCat_exact_iff_function_exact T).mp hT.exact
  have hlength :
      Module.length R S.X₂.obj =
        Module.length R S.X₁.obj + Module.length R S.X₃.obj := by
    simpa [T] using Module.length_eq_add_of_exact
      T.f.hom
      T.g.hom
      hT.moduleCat_injective_f
      hT.moduleCat_surjective_g
      hExact
  have hlen₁ : Module.length R S.X₁.obj ≠ ⊤ := Module.length_ne_top
  have hlen₃ : Module.length R S.X₃.obj ≠ ⊤ := Module.length_ne_top
  have hlengthNat :
      (Module.length R S.X₂.obj).toNat =
        (Module.length R S.X₁.obj).toNat + (Module.length R S.X₃.obj).toNat := by
    simpa [ENat.toNat_add hlen₁ hlen₃] using congrArg ENat.toNat hlength
  have hlength' :
      ((Module.length R S.X₂.obj).toNat : ℤ) =
        ((Module.length R S.X₁.obj).toNat : ℤ) + ((Module.length R S.X₃.obj).toNat : ℤ) := by
    simpa [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : ℤ)) hlengthNat
  linarith

/-- Lemma 10.55.1: if `R` is an Artinian local ring, then the length function defines a natural
abelian group homomorphism `K'_0(R) → ℤ`. Canonically, the same construction works for any
Artinian ring. -/
def finiteGrothendieckGroup_lengthMap [IsArtinianRing R] :
    finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R
    (fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ))
    (relations_le_ker_length R)

-- Proof sketch: `finiteGrothendieckGroup_lengthMap` is the quotient lift of the module-length
-- functional on `FGModuleCat R`, so on a generator class it returns the length of that finite
-- module.
/-- The length map sends the class of a finite module to its length. -/
@[simp]
theorem finiteGrothendieckGroup_lengthMap_apply_of
    [IsArtinianRing R] (M : FGModuleCat R) :
    finiteGrothendieckGroup_lengthMap R
        (finiteGrothendieckGroupOf R M) =
      ((Module.length R M.obj).toNat : ℤ) := by
  simpa using ModulePropertyK0.lift_of R
    (fun N : FGModuleCat R ↦ ((Module.length R N.obj).toNat : ℤ))
    (relations_le_ker_length R)
    M

end FiniteGrothendieckGroup

/-! ### Example_10_55_2 (from Chap10) -/
noncomputable section

universe u

variable (k : Type u) [Field k]

/- Domain-style sampling for Example 10.55.2:
- primary domain: the comparison between `K₀(k)` of finite projective `k`-modules and `K'_0(k)`
  of finite `k`-modules, identified with `ℤ` by rank/length;
- sampled owner declarations:
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length`,
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply`,
  `finiteGrothendieckGroup_lengthEquiv`,
  `finiteGrothendieckGroup_lengthEquiv_apply`,
  `projectiveGrothendieckGroup_rankMap`;
- best owner abstraction:
  the canonical owner data is the comparison square from Lemma 10.55.9 together with the chapter's
  length equivalence `finiteGrothendieckGroup_lengthEquiv`; this file is a field-specific
  `bridge/view`, not a new owner;
- primitive vs. derived:
  primitive data remains the comparison map `K₀(k) → K'_0(k)` and the rank/length homomorphisms;
  the field statement is the derived specialization where `length_k(k) = 1`;
- source/core/bridge triage:
  `source-facing`: Example 10.55.2 identifying the canonical comparison with the dimension map;
  `core/canonical`: Lemma 10.55.9 and `finiteGrothendieckGroup_lengthEquiv`;
  `bridge/view`: the field specialization below.
-/
/-- Helper for Example 10.55.2: over a field, the free rank-one module `k` has length `1`. -/
private theorem field_self_length_toNat_int_eq_one :
    ((Module.length k k).toNat : ℤ) = 1 := by
  -- Convert the module length of `k` into its finite dimension over itself.
  simpa [Module.finrank_self] using
    congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_eq_finrank k k)

/-- Over a field `k`, the canonical comparison map `K₀(k) → K'_0(k)` commutes with the rank and
length identifications with `ℤ`. -/
theorem field_projectiveGrothendieckGroup_comparison_commutes_with_rank :
    (finiteGrothendieckGroup_lengthEquiv k).toAddMonoidHom.comp
        (ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k)) =
      projectiveGrothendieckGroup_rankMap k := by
  apply AddMonoidHom.ext
  intro x
  -- Evaluate Lemma 10.55.9 on `x` and identify the length equivalence with the length map.
  -- Over a field, the ring-length factor from the local Artinian comparison square is `1`.
  simpa [finiteGrothendieckGroup_lengthEquiv_apply, field_self_length_toNat_int_eq_one, one_mul] using
    projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply k x

/-- Example 10.55.2: if `R = k` is a field, then the canonical map `K₀(k) → K'_0(k)` is the
identification obtained by the dimension function, which over a field is also the length function.
Equivalently, the comparison map is the canonical passage through `ℤ`. -/
theorem field_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k) =
      (finiteGrothendieckGroup_lengthEquiv k).symm.toAddMonoidHom.comp
        (projectiveGrothendieckGroup_rankMap k) := by
  apply AddMonoidHom.ext
  intro x
  -- Apply the length equivalence to reduce the comparison map to the commutative square above.
  apply (finiteGrothendieckGroup_lengthEquiv k).injective
  -- After composing with the equivalence, both sides are exactly the rank map.
  simpa [AddMonoidHom.comp_apply] using
    DFunLike.congr_fun (field_projectiveGrothendieckGroup_comparison_commutes_with_rank k) x

/-! ### Example_10_55_3 (from Chap10) -/
noncomputable section

open scoped TensorProduct

universe u

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

private theorem finiteProjectiveModuleCat_genericRank_eq_rank
    (M : FiniteProjectiveModuleCat R) :
    (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ) =
      Module.finrank R M.obj := by
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  let _ : Module.IsTorsionFree R M.obj := by
    obtain ⟨n, _, g, _, hg, _⟩ := Module.Finite.exists_comp_eq_id_of_projective R M.obj
    exact hg.moduleIsTorsionFree g fun r m ↦ by simp
  let _ : Module.Free R M.obj := Module.free_of_finite_type_torsion_free'
  norm_num [Module.finrank_tensorProduct]

-- The generic-rank functional on finitely generated `R`-modules, computed after base change to
-- the fraction field.
private noncomputable def finiteGrothendieckGroup_pidRank (M : FGModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

-- Proof sketch: the structure theorem for finitely generated modules over a principal ideal domain
-- reduces a Grothendieck relation to free and torsion summands; the generic rank vanishes on the
-- torsion part and is additive on short exact sequences, so every relation maps to zero.
private theorem finiteGrothendieckGroup_relations_le_ker_pidRank :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift (finiteGrothendieckGroup_pidRank R)).ker := by
  sorry

/-- Example 10.55.3: for a principal ideal domain `R`, the generic-rank functional on finite
`R`-modules descends to the canonical homomorphism `K'_0(R) → ℤ`. -/
def finiteGrothendieckGroup_pidRankMap : finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (finiteGrothendieckGroup_pidRank R)
    (finiteGrothendieckGroup_relations_le_ker_pidRank R)

/-- The PID generic-rank map sends the class of a finite module to its generic rank. -/
theorem finiteGrothendieckGroup_pidRankMap_apply_of
    (M : FGModuleCat R) :
    finiteGrothendieckGroup_pidRankMap R
        (finiteGrothendieckGroupOf R M) =
      (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ) := by
  simpa using ModulePropertyK0.lift_of R
    (finiteGrothendieckGroup_pidRank R)
    (finiteGrothendieckGroup_relations_le_ker_pidRank R)
    M

/-- For a principal ideal domain `R`, the generic-rank map on `K'_0(R)` is bijective. -/
-- Proof sketch: surjectivity is realized by the class of a free rank-one module. Injectivity
-- follows from the structure theorem for finitely generated modules over a principal ideal domain,
-- which shows that the Grothendieck class is determined by generic rank.
theorem finiteGrothendieckGroup_pidRankMap_bijective :
    Function.Bijective (finiteGrothendieckGroup_pidRankMap R) := by
  sorry

/-- For a principal ideal domain `R`, the rank functional on finitely generated projective
`R`-modules is obtained by composing the canonical comparison map `K₀(R) → K'_0(R)` with the
generic-rank homomorphism `K'_0(R) → ℤ`. -/
def projectiveGrothendieckGroup_pidRankMap : projectiveGrothendieckGroup R →+ ℤ :=
  (finiteGrothendieckGroup_pidRankMap R).comp
    (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R))

/-- The PID rank map sends the class of a finite projective module to its rank. -/
theorem projectiveGrothendieckGroup_pidRankMap_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_pidRankMap R
        (projectiveGrothendieckGroupOf R M) =
      (Module.finrank R M.obj : ℤ) := by
  rw [projectiveGrothendieckGroup_pidRankMap, AddMonoidHom.comp_apply, ModulePropertyK0.map_of,
    finiteGrothendieckGroup_pidRankMap_apply_of]
  exact finiteProjectiveModuleCat_genericRank_eq_rank R M

/-- For a principal ideal domain `R`, the rank map on `K₀(R)` is bijective. -/
-- Proof sketch: finite projective modules over a principal ideal domain are free, so the
-- Grothendieck class of a finite projective module is determined by its rank, and every integer is
-- realized by the difference of free-module classes.
theorem projectiveGrothendieckGroup_pidRankMap_bijective :
    Function.Bijective (projectiveGrothendieckGroup_pidRankMap R) := by
  sorry

/-- For a principal ideal domain `R`, the rank map identifies the Grothendieck group `K₀(R)` of
finitely generated projective `R`-modules with `ℤ`. -/
noncomputable def projectiveGrothendieckGroup_pidEquiv : projectiveGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (projectiveGrothendieckGroup_pidRankMap R)
    (projectiveGrothendieckGroup_pidRankMap_bijective R)

/-- The additive equivalence `K₀(R) ≃+ ℤ` acts by the PID rank map. -/
theorem projectiveGrothendieckGroup_pidEquiv_apply
    (x : projectiveGrothendieckGroup R) :
    projectiveGrothendieckGroup_pidEquiv R x =
      projectiveGrothendieckGroup_pidRankMap R x := rfl

/-- For a principal ideal domain `R`, the structure theorem for finitely generated modules
identifies `K'_0(R)` with `ℤ`; in this Noetherian setting `K'_0(R)` is modeled canonically here by
finite `R`-modules. -/
noncomputable def finiteGrothendieckGroup_pidEquiv : finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (finiteGrothendieckGroup_pidRankMap R)
    (finiteGrothendieckGroup_pidRankMap_bijective R)

/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the PID generic-rank map. -/
theorem finiteGrothendieckGroup_pidEquiv_apply
    (x : finiteGrothendieckGroup R) :
    finiteGrothendieckGroup_pidEquiv R x =
      finiteGrothendieckGroup_pidRankMap R x := rfl

/-- On a principal ideal domain, the canonical comparison map `K₀(R) → K'_0(R)` commutes with the
rank and generic-rank homomorphisms to `ℤ`. -/
theorem projectiveGrothendieckGroup_comparison_commutes_with_pidRank :
    (finiteGrothendieckGroup_pidRankMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)) =
      projectiveGrothendieckGroup_pidRankMap R := by
  rfl

/-- On an element of `K₀(R)`, the generic rank after comparison to `K'_0(R)` agrees with the
rank in `K₀(R)`. -/
@[simp] theorem projectiveGrothendieckGroup_comparison_commutes_with_pidRank_apply
    (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_pidRankMap R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      projectiveGrothendieckGroup_pidRankMap R x := by
  simpa using DFunLike.congr_fun
    (projectiveGrothendieckGroup_comparison_commutes_with_pidRank R) x

/-- Under the PID identifications `K₀(R) ≃+ ℤ` and `K'_0(R) ≃+ ℤ`, the canonical comparison map
`K₀(R) → K'_0(R)` acts as the identity on `ℤ`. -/
@[simp] theorem pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_apply
    (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_pidEquiv R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      projectiveGrothendieckGroup_pidEquiv R x := by
  change finiteGrothendieckGroup_pidRankMap R
      (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
    projectiveGrothendieckGroup_pidRankMap R x
  exact projectiveGrothendieckGroup_comparison_commutes_with_pidRank_apply R x

/-- For a principal ideal domain `R`, the canonical comparison map `K₀(R) → K'_0(R)` is the
identification obtained by passing through `ℤ`. In particular, `K₀(R) ≃+ K'_0(R) ≃+ ℤ`. -/
theorem pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) =
      (finiteGrothendieckGroup_pidEquiv R).symm.toAddMonoidHom.comp
        (projectiveGrothendieckGroup_pidEquiv R).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  apply (finiteGrothendieckGroup_pidEquiv R).injective
  simp [pid_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_apply]

end

/-! ### Example_10_55_4 (from Chap10) -/
variable (k : Type*) [Field k]

/- Example 10.55.4: for a field `k`, the polynomial ring `k[X]` is a principal ideal domain, so
Example 10.55.3 specializes to the canonical equivalence identifying `K₀(k[X])` with `ℤ`. -/
#check (projectiveGrothendieckGroup_pidEquiv (Polynomial k) :
  projectiveGrothendieckGroup (Polynomial k) ≃+ ℤ)

/- Example 10.55.4: the same specialization identifies `K'_0(k[X])`, modeled here by finitely
generated `k[X]`-modules, with `ℤ`. -/
#check (finiteGrothendieckGroup_pidEquiv (Polynomial k) :
  finiteGrothendieckGroup (Polynomial k) ≃+ ℤ)

/-! ### Example_10_55_5 (from Chap10) -/
noncomputable section

open scoped TensorProduct

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k
local notation "K0→K0'" =>
  ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)

-- Proof sketch: classify finitely generated projective modules over
-- `R = {f ∈ k[x] | f(0) = f(1)}` by rank together with a unit parameter, and identify `K'_0(R)`
-- with `ℤ` via the finite-module Grothendieck group used canonically in this chapter.
/-- Helper for Example 10.55.5: a constant polynomial belongs to the equal-endpoint subring. -/
private theorem equal_endpoint_constant_mem (a : k) : Polynomial.C a ∈ R := by
  -- Constant polynomials take the same value at both endpoints.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Example 10.55.5: the constant polynomial `C a`, viewed in the equal-endpoint
subring. -/
private noncomputable def equal_endpoint_constant (a : k) : R :=
  ⟨Polynomial.C a, equal_endpoint_constant_mem (k := k) a⟩

/-- Helper for Example 10.55.5: subtracting the endpoint difference times `X` puts a polynomial
into the equal-endpoint subring. -/
private theorem equal_endpoint_subtract_difference_mul_X_mem (f : Polynomial k) :
    f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X ∈ R := by
  -- The correction term changes the value at `1` by exactly `f(1) - f(0)` and vanishes at `0`.
  rw [mem_equal_endpoint_poly_subring_iff]
  calc
    (f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X).eval 0 = f.eval 0 := by
      simp
    _ = f.eval 1 - (f.eval 1 - f.eval 0) := by ring
    _ = (f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X).eval 1 := by
      simp

/-- Helper for Example 10.55.5: every polynomial splits as an equal-endpoint polynomial plus a
scalar multiple of `X`. -/
private theorem equal_endpoint_polynomial_decomposition (f : Polynomial k) :
    ∃ r : R, f = r.1 + Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X := by
  let r : R :=
    ⟨f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X,
      equal_endpoint_subtract_difference_mul_X_mem (k := k) f⟩
  refine ⟨r, ?_⟩
  -- Re-expanding the chosen equal-endpoint summand recovers the original polynomial.
  dsimp [r]
  ring

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path from
`Submodule.smul_mem`, multiplying the generator `1` by `r` recovers the underlying polynomial. -/
private theorem equal_endpoint_distrib_smul_one_eq (r : R) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (r • (1 : Polynomial k) : Polynomial k) = r.1 := by
  -- The exact restricted scalar action still reduces to multiplication in the ambient polynomial
  -- ring, and multiplying by `1` does nothing.
  rw [Subring.smul_def]
  simp [smul_eq_mul]

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path from
`Submodule.smul_mem`, the constant witness acts on `X` by ordinary multiplication. -/
private theorem equal_endpoint_distrib_smul_X_eq (a : k) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (equal_endpoint_constant (k := k) a • Polynomial.X : Polynomial k) =
      Polynomial.C a * Polynomial.X := by
  -- Rewriting through the subring action identifies the witness scalar with `C a`.
  rw [Subring.smul_def]
  simp [smul_eq_mul, equal_endpoint_constant]

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path used by the generator
map, scalar multiplication on `k[X]` is ordinary multiplication by the corresponding polynomial. -/
private theorem equal_endpoint_distrib_smul_eq_mul (r : R) (f : Polynomial k) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (r • f : Polynomial k) = (r : Polynomial k) * f := by
  -- This is the canonical `DistribMulAction` coming from the ambient polynomial ring.
  rfl

/-- Helper for Example 10.55.5: the `R`-action on `k[X]` is multiplication by the underlying
polynomial. -/
private theorem equal_endpoint_polynomial_smul (r : R) (f : Polynomial k) :
    (r • f : Polynomial k) = r.1 * f := by
  -- Restriction of scalars along the subring inclusion acts by ordinary polynomial multiplication.
  rfl

/-- Helper for Example 10.55.5: the algebra map from the equal-endpoint subring to `k[X]` is the
underlying polynomial coercion. -/
private theorem equal_endpoint_polynomial_algebraMap_eq_coe (r : R) :
    algebraMap R (Polynomial k) r = (r : Polynomial k) := by
  rfl

/-- Helper for Example 10.55.5: the source decomposition is packaged as a single `R`-linear map
from two copies of `R` onto `k[X]`. -/
private noncomputable def equal_endpoint_polynomial_generator_map :
    (R × R) →ₗ[R] Polynomial k :=
  LinearMap.coprod
    (LinearMap.toSpanSingleton R (Polynomial k) (1 : Polynomial k))
    (LinearMap.toSpanSingleton R (Polynomial k) Polynomial.X)

/-- Helper for Example 10.55.5: the source-faithful generator map sends `(r, s)` to `r + sX`. -/
private theorem equal_endpoint_polynomial_generator_map_apply (x : R × R) :
    equal_endpoint_polynomial_generator_map (k := k) x =
      (x.1 : Polynomial k) + (x.2 : Polynomial k) * Polynomial.X := by
  -- Expand the coprod map and normalize each coordinate to ambient polynomial multiplication.
  simp [equal_endpoint_polynomial_generator_map, equal_endpoint_polynomial_smul]

/-- Helper for Example 10.55.5: the generator map is surjective by the textbook decomposition
`f = r + C(f(1)-f(0)) X`. -/
private theorem equal_endpoint_polynomial_generator_map_surjective :
    Function.Surjective (equal_endpoint_polynomial_generator_map (k := k)) := by
  intro f
  rcases equal_endpoint_polynomial_decomposition (k := k) f with ⟨r, hr⟩
  refine ⟨(r, equal_endpoint_constant (k := k) (f.eval 1 - f.eval 0)), ?_⟩
  -- Evaluate the generator map on the textbook witness from the polynomial decomposition.
  rw [equal_endpoint_polynomial_generator_map_apply]
  simpa [equal_endpoint_constant] using hr.symm

/-- Helper for Example 10.55.5: `k[X]` is generated over `R` by `1` and `X`. -/
private theorem equal_endpoint_polynomial_finite : Module.Finite R (Polynomial k) := by
  -- The source decomposition makes `k[X]` a quotient of the finite module `R × R`.
  let _ : Module.Finite R (R × R) := inferInstance
  exact Module.Finite.of_surjective
    (equal_endpoint_polynomial_generator_map (k := k))
    (equal_endpoint_polynomial_generator_map_surjective (k := k))

/-- Helper for Example 10.55.5: register the normalization `k[X]` as a finite `R`-module. -/
private noncomputable instance equal_endpoint_polynomial_module_finite :
    Module.Finite R (Polynomial k) :=
  equal_endpoint_polynomial_finite (k := k)

/-- Helper for Example 10.55.5: evaluation at the common endpoint defines a ring map `R → k`. -/
private noncomputable def equal_endpoint_eval : R →+* k :=
  (Polynomial.eval₂RingHom (RingHom.id k) (0 : k)).comp (equal_endpoint_poly_subring k).subtype

/-- Helper for Example 10.55.5: the endpoint-evaluation map equips `k` with its natural
`R`-algebra structure. -/
private noncomputable instance equal_endpoint_eval_algebra : Algebra R k :=
  (equal_endpoint_eval k).toAlgebra

/-- Helper for Example 10.55.5: the `R`-action on the endpoint field is multiplication by the
endpoint value. -/
private theorem equal_endpoint_eval_smul (r : R) (a : k) :
    (r • a : k) = equal_endpoint_eval k r * a := by
  -- The endpoint field module structure comes from the algebra map `R → k`.
  rfl

/-- Helper for Example 10.55.5: the endpoint field is a cyclic `R`-module via evaluation. -/
private theorem equal_endpoint_eval_finite : Module.Finite R k := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : k)}, Set.finite_singleton _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro a
  refine ⟨equal_endpoint_constant (k := k) a, ?_⟩
  -- The constant polynomial `C a` acts on the generator `1` by the scalar `a`.
  rw [equal_endpoint_eval_smul]
  simp [equal_endpoint_eval, equal_endpoint_constant]

/-- Helper for Example 10.55.5: register the endpoint field as a finite `R`-module. -/
private noncomputable instance equal_endpoint_eval_module_finite : Module.Finite R k :=
  equal_endpoint_eval_finite (k := k)

/-- Helper for Example 10.55.5: evaluation at `0` makes `k` into a `k[X]`-algebra. -/
private noncomputable def polynomial_eval_zero : Polynomial k →+* k :=
  Polynomial.eval₂RingHom (RingHom.id k) (0 : k)

/-- Helper for Example 10.55.5: the evaluation-at-`0` ring map supplies the ambient
`k[X]`-module structure on `k`. -/
private noncomputable instance polynomial_eval_zero_algebra : Algebra (Polynomial k) k :=
  (polynomial_eval_zero (k := k)).toAlgebra

/-- Helper for Example 10.55.5: the evaluation-at-`0` module `k` over `k[X]` is cyclic. -/
private theorem polynomial_eval_zero_finite : Module.Finite (Polynomial k) k := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : k)}, Set.finite_singleton _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro a
  refine ⟨Polynomial.C a, ?_⟩
  -- The constant polynomial `C a` sends the generator `1` to the scalar `a`.
  change polynomial_eval_zero (k := k) (Polynomial.C a) * 1 = a
  simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: register `k` as a finite `k[X]`-module via evaluation at `0`. -/
private noncomputable instance polynomial_eval_zero_module_finite :
    Module.Finite (Polynomial k) k :=
  polynomial_eval_zero_finite (k := k)

/-- Helper for Example 10.55.5: the standard pair
`k[X] --(· X)→ k[X] --ev₀→ k` is exact. -/
private theorem polynomial_mul_X_eval_zero_exact :
    Function.Exact
      (fun q : Polynomial k ↦ q * Polynomial.X)
      (fun p : Polynomial k ↦ polynomial_eval_zero (k := k) p) := by
  intro p
  constructor
  · intro hp
    -- Vanishing at `0` is the same as divisibility by `X`.
    change polynomial_eval_zero (k := k) p = 0 at hp
    have hp' : p.coeff 0 = 0 := by
      simpa [polynomial_eval_zero] using hp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hp'
    refine ⟨q, ?_⟩
    simpa [mul_comm] using hq.symm
  · rintro ⟨q, rfl⟩
    -- Multiples of `X` vanish under evaluation at `0`.
    simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: multiplication by `X` on `k[X]` is injective. -/
private theorem polynomial_mul_X_injective :
    Function.Injective (fun q : Polynomial k ↦ q * Polynomial.X) := by
  intro p q hp
  -- `k[X]` is a domain, so right multiplication by the nonzero polynomial `X` cancels.
  exact mul_right_cancel₀ Polynomial.X_ne_zero hp

/-- Helper for Example 10.55.5: evaluation at `0` on `k[X]` is surjective. -/
private theorem polynomial_eval_zero_surjective :
    Function.Surjective (fun p : Polynomial k ↦ polynomial_eval_zero (k := k) p) := by
  intro a
  refine ⟨Polynomial.C a, ?_⟩
  -- Constant polynomials realize every scalar in the target field.
  simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: endpoint evaluation is the restriction of `ev₀ : k[X] → k` to the
equal-endpoint subring. -/
private theorem equal_endpoint_eval_eq_polynomial_eval_zero (r : R) :
    equal_endpoint_eval k r =
      polynomial_eval_zero (k := k) (algebraMap R (Polynomial k) r) := by
  -- Both ring maps are `eval₀` composed with the inclusion `R ↪ k[X]`.
  rfl

/-- Helper for Example 10.55.5: the `R`-module on `k` obtained by restricting scalars from
`k[X]` acts by endpoint evaluation. -/
private theorem equal_endpoint_restrictScalars_eval_zero_smul (r : R) (a : k) :
    let _ : Module R k := Module.restrictScalars R (Polynomial k) k
    let _ : IsScalarTower R (Polynomial k) k := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    (r • a : k) = equal_endpoint_eval k r * a := by
  -- The restricted action uses `ev₀` on the image of `r` inside `k[X]`.
  rw [show (r • a : k) =
      polynomial_eval_zero (k := k) (algebraMap R (Polynomial k) r) * a by rfl]
  rw [equal_endpoint_eval_eq_polynomial_eval_zero]

/-- Helper for Example 10.55.5: the `k[X]`-module `k = k[X]/(X)` is torsion, with `X` killing every
element. -/
private theorem polynomial_eval_zero_isTorsion :
    Module.IsTorsion (Polynomial k) k := by
  intro a
  by_cases ha : a = 0
  · refine ⟨⟨1, mem_nonZeroDivisors_iff_ne_zero.2 one_ne_zero⟩, ?_⟩
    simpa [ha]
  · refine ⟨⟨Polynomial.X, mem_nonZeroDivisors_iff_ne_zero.2 Polynomial.X_ne_zero⟩, ?_⟩
    -- The distinguished polynomial `X` acts by `0` under evaluation at `0`.
    change polynomial_eval_zero (k := k) Polynomial.X * a = 0
    simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: the generic rank of `k[X]/(X)` over `k[X]` is zero. -/
private theorem equal_endpoint_polynomial_torsion_tensor_finrank_zero :
    (Module.finrank (FractionRing (Polynomial k))
      ((FractionRing (Polynomial k)) ⊗[Polynomial k] k) : ℤ) = 0 := by
  let K := FractionRing (Polynomial k)
  let T : Type u := K ⊗[Polynomial k] k
  have hrank : Module.rank K T = 0 := by
    -- Base change to the fraction field preserves rank, and the source module is torsion.
    calc
      Module.rank K T = Module.rank (Polynomial k) k := by
        simpa [K, T] using (TensorProduct.isBaseChange (Polynomial k) k K).rank_eq
      _ = 0 := by
        have htors : Module.IsTorsion (Polynomial k) k :=
          polynomial_eval_zero_isTorsion (k := k)
        exact (rank_eq_zero_iff_isTorsion).2 htors
  have hfinrank :
      Module.finrank K T = 0 :=
    let _ : Module.Free K T := Module.Free.of_divisionRing K T
    Module.finrank_eq_zero_of_rank_eq_zero hrank
  rw [hfinrank]
  norm_num

/-- Helper for Example 10.55.5: the class of `k[X]/(X)` vanishes in `K'_0(k[X])`. -/
private theorem equal_endpoint_polynomial_field_class_eq_zero :
    finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k) = 0 := by
  -- The earlier PID computation identifies `K'_0(k[X])` with generic rank.
  apply (finiteGrothendieckGroup_pidEquiv (Polynomial k)).injective
  change finiteGrothendieckGroup_pidRankMap (Polynomial k)
      (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) = 0
  rw [finiteGrothendieckGroup_pidRankMap_apply_of]
  exact equal_endpoint_polynomial_torsion_tensor_finrank_zero (k := k)

/-- Helper for Example 10.55.5: the zero `R`-module represents the zero object in
`FGModuleCat R`. -/
private theorem equal_endpoint_isFG_zero :
    ModuleCat.isFG R (ModuleCat.of R PUnit) := by
  -- The zero module is finitely generated over every ring.
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Example 10.55.5: the identity map on `k` is `R`-linear from the restricted
evaluation-at-`0` action to the endpoint-evaluation action. -/
private theorem equal_endpoint_restrictScalars_eval_zero_linear_map_smul
    (r : R)
    (a : (ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj
      (ModuleCat.of (Polynomial k) k)) :
    (AddEquiv.refl k) (r • a) = (r • (AddEquiv.refl k a) : k) := by
  -- The restricted action is exactly endpoint evaluation, so the identity map is linear.
  simpa using equal_endpoint_restrictScalars_eval_zero_smul (k := k) r a

/-- Helper for Example 10.55.5: the restricted evaluation-at-`0` module on `k` is canonically the
same `R`-module as the endpoint-evaluation module. -/
private noncomputable def equal_endpoint_restrictScalars_eval_zero_moduleIso :
    (ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj (ModuleCat.of (Polynomial k) k) ≅
      ModuleCat.of R k :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj
      (ModuleCat.of (Polynomial k) k)) ≃ₗ[R] k from
    { __ := AddEquiv.refl k
      map_smul' := equal_endpoint_restrictScalars_eval_zero_linear_map_smul (k := k) }).toModuleIso

/-- Helper for Example 10.55.5: the packaged restricted object of a finite `k[X]`-module is still
finitely generated over `R`. -/
private theorem equal_endpoint_restrictScalars_isFG
    (M : FGModuleCat (Polynomial k)) :
    ModuleCat.isFG R (ModuleCat.of R ((ModuleCat.restrictScalars
      (algebraMap R (Polynomial k))).obj M.obj)) := by
  -- TODO: install an elaboration-stable `IsScalarTower R (Polynomial k)` instance on the
  -- restricted owner `(ModuleCat.restrictScalars ...).obj M.obj`, then apply
  -- `Module.Finite.trans` with `equal_endpoint_polynomial_finite`.
  sorry

/-- Helper for Example 10.55.5: after restricting scalars along `R ↪ k[X]`, a finite
`k[X]`-module is still finite over `R`. -/
private theorem equal_endpoint_restrictScalars_module_finite
    (M : FGModuleCat (Polynomial k)) : Module.Finite R ↑M := by
  -- TODO: once the restricted-owner `IsScalarTower` bridge is stabilized, forget the owner
  -- packaging to recover a carrier-level `Module.Finite R ↑M` instance.
  sorry

/-- Helper for Example 10.55.5: a finite `k[X]`-module defines a canonical finite `R`-module by
restriction of scalars along `R ↪ k[X]`. -/
private noncomputable abbrev equal_endpoint_restrictScalars_object
    (M : FGModuleCat (Polynomial k)) : FGModuleCat R :=
  -- Package the restricted module at the category level so later lemmas reuse a fixed owner.
  ⟨(ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj M.obj,
    equal_endpoint_restrictScalars_isFG (k := k) M⟩

/-- Helper for Example 10.55.5: the restricted `k[X]`-module `k = k[X]/(X)` is the same finite
`R`-module as the endpoint-evaluation module. -/
private noncomputable def equal_endpoint_restrictScalars_eval_zero_fgModuleIso :
    equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k) ≅
      FGModuleCat.of R k :=
  -- Reuse the canonical restricted-scalars identity-on-vectors isomorphism at the `FGModuleCat`
  -- level, so later `K'_0` computations do not unfold the owner packaging again.
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    (equal_endpoint_restrictScalars_eval_zero_moduleIso (k := k))

/-- Helper for Example 10.55.5: restricting scalars along `R ↪ k[X]` sends the Grothendieck
relations for finite `k[X]`-modules to zero in `K'_0(R)`. -/
private theorem equal_endpoint_relations_le_ker_restrictScalars :
    modulePropertyK0Relations (Polynomial k) (ModuleCat.isFG (Polynomial k)) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat (Polynomial k) ↦
        finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift
        (fun M : FGModuleCat (Polynomial k) ↦
          finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M))
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  let U : CategoryTheory.ShortComplex (ModuleCat (Polynomial k)) :=
    S.map (ModuleCat.isFG (Polynomial k)).ι
  have hU : U.ShortExact := by
    -- Forgetting the finiteness predicate gives the ambient short exact sequence.
    simpa [U] using hS
  have hExact :
      Function.Exact (S.f.hom.hom.restrictScalars R) (S.g.hom.hom.restrictScalars R) := by
    -- Restriction of scalars does not change the underlying exact pair.
    simpa [U] using
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  have hf_injective : Function.Injective (S.f.hom.hom.restrictScalars R) := by
    -- Injectivity of the first map survives scalar restriction.
    simpa [U] using hU.moduleCat_injective_f
  have hg_surjective : Function.Surjective (S.g.hom.hom.restrictScalars R) := by
    -- Surjectivity of the second map survives scalar restriction.
    simpa [U] using hU.moduleCat_surjective_g
  let _ : Module R S.X₁.obj := Module.restrictScalars R (Polynomial k) S.X₁.obj
  let _ : Module R S.X₂.obj := Module.restrictScalars R (Polynomial k) S.X₂.obj
  let _ : Module R S.X₃.obj := Module.restrictScalars R (Polynomial k) S.X₃.obj
  let _ : IsScalarTower R (Polynomial k) S.X₁.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (Polynomial k) S.X₂.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (Polynomial k) S.X₃.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite R S.X₁.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₁
  let _ : Module.Finite R S.X₂.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₂
  let _ : Module.Finite R S.X₃.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₃
  let T : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := FGModuleCat.of R S.X₁.obj
      X₂ := FGModuleCat.of R S.X₂.obj
      X₃ := FGModuleCat.of R S.X₃.obj
      f := FGModuleCat.ofHom (S.f.hom.hom.restrictScalars R)
      g := FGModuleCat.ofHom (S.g.hom.hom.restrictScalars R)
      zero := by
        ext x
        change S.g.hom.hom (S.f.hom.hom x) = 0
        simpa using congrFun hExact.comp_eq_zero x }
  have hT : (T.map (ModuleCat.isFG R).ι).ShortExact := by
    -- Repackage the restricted row as a short exact sequence in `FGModuleCat R`.
    refine ModuleCat.shortComplex_shortExact _ hExact hf_injective hg_surjective
  have hrel :
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) S.X₂) =
        finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) S.X₁) +
          finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) S.X₃) := by
    -- The defining Grothendieck relation now applies over `R`.
    simpa [equal_endpoint_restrictScalars_object, finiteGrothendieckGroupOf, T] using
      ModulePropertyK0.of_shortExact (equal_endpoint_poly_subring k) T hT
  -- Rewrite the short exact relation into the subgroup-generator form.
  rw [hrel]
  abel_nf

/-- Helper for Example 10.55.5: restriction of scalars along `R ↪ k[X]` induces the canonical map
`K'_0(k[X]) → K'_0(R)`. -/
private noncomputable def equal_endpoint_finiteGrothendieckGroup_restrictScalars :
    finiteGrothendieckGroup (Polynomial k) →+ finiteGrothendieckGroup R :=
  ModulePropertyK0.lift (Polynomial k)
    (fun M : FGModuleCat (Polynomial k) ↦
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M))
    (equal_endpoint_relations_le_ker_restrictScalars (k := k))

/-- Helper for Example 10.55.5: the restriction-of-scalars map sends a generator class to the class
of the restricted module. -/
private theorem equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of
    (M : FGModuleCat (Polynomial k)) :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) M) =
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M) := by
  -- The quotient lift agrees with its defining generator formula.
  simpa using ModulePropertyK0.lift_of (Polynomial k)
    (fun N : FGModuleCat (Polynomial k) ↦
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N))
    (equal_endpoint_relations_le_ker_restrictScalars (k := k))
    M

/-- Helper for Example 10.55.5: evaluating the restriction-of-scalars map on the polynomial field
class lands in the class of the restricted `ev₀` module before any endpoint rewrite. -/
private theorem equal_endpoint_restrictScalars_eval_zero_source_class :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R
        (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) := by
  -- This is the generator formula for the restriction-of-scalars homomorphism at the specific
  -- module `k[X]/(X)`.
  simpa using
    equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of (k := k)
      (FGModuleCat.of (Polynomial k) k)

/-- Helper for Example 10.55.5: restricting the polynomial-side class of `k[X]/(X)` gives the
endpoint field class over `R`. -/
private theorem equal_endpoint_restrictScalars_eval_zero_class :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
  -- First evaluate the restriction map on the generator class, then rewrite by the canonical
  -- identity-on-vectors `R`-linear isomorphism from the restricted `ev₀` action to endpoint
  -- evaluation.
  calc
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R
        (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) := by
          exact equal_endpoint_restrictScalars_eval_zero_source_class (k := k)
    _ = finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
      -- Rewrite the restricted `ev₀` module to the endpoint-evaluation module by the canonical
      -- identity-on-vectors `R`-linear isomorphism.
      have hIso :
          ModulePropertyK0.of R (ModuleCat.isFG R)
              (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R k) := by
        exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R)
          (equal_endpoint_isFG_zero (k := k))
          _ _
          (equal_endpoint_restrictScalars_eval_zero_fgModuleIso (k := k)) :
            ModulePropertyK0.of R (ModuleCat.isFG R)
                (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) =
              ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R k))
      simpa [finiteGrothendieckGroupOf] using hIso

/-- Helper for Example 10.55.5: the endpoint field class vanishes in `K'_0(R)`. -/
private theorem equal_endpoint_field_class_eq_zero :
    finiteGrothendieckGroupOf R (FGModuleCat.of R k) = 0 := by
  -- Apply the stabilized restriction-of-scalars map to the polynomial-side vanishing class and then
  -- rewrite the restricted generator by the canonical endpoint-evaluation module isomorphism.
  calc
    finiteGrothendieckGroupOf R (FGModuleCat.of R k) =
      equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) := by
          symm
          exact equal_endpoint_restrictScalars_eval_zero_class (k := k)
    _ = equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k) 0 := by
          rw [equal_endpoint_polynomial_field_class_eq_zero (k := k)]
    _ = 0 := by
          simp [equal_endpoint_finiteGrothendieckGroup_restrictScalars]

/-- Helper for Example 10.55.5: if an `R`-module factors through the endpoint field, finite
generation over `R` already implies finite generation over `k`. -/
private theorem equal_endpoint_moduleFinite_over_field
    (V : Type u) [AddCommGroup V] [Module k V] [Module R V]
    [IsScalarTower R k V] [SMulCommClass R k V] [Module.Finite R V] :
    Module.Finite k V := by
  classical
  have hR : Module.Finite R V := inferInstance
  rw [Module.finite_def, Submodule.fg_def] at hR ⊢
  rcases hR with ⟨s, hsFinite, hsTop⟩
  refine ⟨s, hsFinite, ?_⟩
  -- The same generators span over `k`, because the `R`-action already factors through `k`.
  have hspan :
      Submodule.span R s ≤ (Submodule.span k s).restrictScalars R := by
    refine Submodule.span_le.2 ?_
    intro x hx
    exact Submodule.subset_span hx
  rw [Submodule.eq_top_iff']
  intro v
  have hvTop : v ∈ (⊤ : Submodule R V) := by
    simp
  have hv :
      v ∈ (Submodule.span k s).restrictScalars R := by
    have htop :
        (⊤ : Submodule R V) ≤ (Submodule.span k s).restrictScalars R := by
      simpa [hsTop] using hspan
    exact htop hvTop
  exact hv

/-- Helper for Example 10.55.5: the Grothendieck class of a product of finite `R`-modules is the
sum of the two classes. -/
private theorem equal_endpoint_finiteGrothendieckGroupOf_prod
    (M N : FGModuleCat R) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (M.obj × N.obj)) =
      finiteGrothendieckGroupOf R M + finiteGrothendieckGroupOf R N := by
  let S : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := M
      X₂ := FGModuleCat.of R (M.obj × N.obj)
      X₃ := N
      f := FGModuleCat.ofHom (LinearMap.inl R M.obj N.obj)
      g := FGModuleCat.ofHom (LinearMap.snd R M.obj N.obj)
      zero := by
        -- The split product row has zero composite on the nose.
        ext x
        rfl }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
    -- This is the standard split exact sequence `0 → M → M × N → N → 0`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        exact Prod.ext rfl (by simpa using hx.symm)
      · rintro ⟨m, rfl⟩
        rfl
    · intro x y hxy
      exact congrArg Prod.fst hxy
    · intro y
      refine ⟨(0, y), ?_⟩
      rfl
  -- Apply the defining Grothendieck relation to the split row.
  simpa [S, finiteGrothendieckGroupOf] using
    ModulePropertyK0.of_shortExact R S hS

/-- Helper for Example 10.55.5: the endpoint-supported free module `k^(n+1)` splits as
`k × k^n`. -/
private noncomputable def equal_endpoint_field_power_succ_linearEquiv (n : ℕ) :
    (Fin (n + 1) → k) ≃ₗ[R] k × (Fin n → k) :=
  (LinearEquiv.piCongrLeft R (fun _ ↦ k) (finSuccEquiv n)) ≪≫ₗ
    LinearEquiv.piOptionEquivProd R

/-- Helper for Example 10.55.5: the split form of `k^(n+1)` yields a canonical isomorphism in
`FGModuleCat R`. -/
private noncomputable def equal_endpoint_field_power_succ_fgModuleIso (n : ℕ) :
    FGModuleCat.of R (Fin (n + 1) → k) ≅ FGModuleCat.of R (k × (Fin n → k)) :=
  -- Package the explicit head-tail decomposition as an isomorphism in the finite-module category.
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    ((equal_endpoint_field_power_succ_linearEquiv (k := k) n).toModuleIso)

/-- Helper for Example 10.55.5: the endpoint-supported free `k`-vector space `k^n` contributes
`n [k]` in `K'_0(R)`. -/
private theorem equal_endpoint_field_power_class_eq_zsmul_field_class
    (n : ℕ) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin n → k)) =
      n • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
  -- TODO: induct on `n` using the split `R`-linear equivalence
  -- `Fin (n + 1) → k ≃ₗ[R] k × (Fin n → k)` and the product relation in `K'_0(R)`.
  sorry

/-- Helper for Example 10.55.5: any finite `R`-module whose action factors through
`equal_endpoint_eval k : R → k` has zero class in `K'_0(R)`. -/
private theorem equal_endpoint_endpoint_supported_class_eq_zero
    (V : Type u) [AddCommGroup V] [Module k V] [Module R V]
    [IsScalarTower R k V] [SMulCommClass R k V] [Module.Finite R V] :
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) = 0 := by
  -- TODO: upgrade finite generation from `R` to `k`, identify `V` with `k^n` over `R`, and then
  -- use the previous `k^n` class computation together with `[k] = 0`.
  sorry

/-- Helper for Example 10.55.5: the conductor polynomial `X^2 - X` vanishes at both endpoints, so
every one of its multiples lies in the equal-endpoint ring. -/
private theorem equal_endpoint_conductor_mul_mem (q : Polynomial k) :
    ((Polynomial.X ^ 2 - Polynomial.X) * q : Polynomial k) ∈ R := by
  -- The conductor factor evaluates to `0` at both `0` and `1`, so the product has equal endpoint
  -- values.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Example 10.55.5: the conductor polynomial factors as `X (X - 1)`. -/
private theorem equal_endpoint_conductor_factor :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) =
      Polynomial.X * (Polynomial.X - Polynomial.C (1 : k)) := by
  calc
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) =
        Polynomial.X * Polynomial.X - Polynomial.X * Polynomial.C (1 : k) := by
      simp [pow_two]
    _ = Polynomial.X * (Polynomial.X - Polynomial.C (1 : k)) := by
      ring

/-- Helper for Example 10.55.5: the conductor polynomial is nonzero. -/
private theorem equal_endpoint_conductor_ne_zero :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ≠ 0 := by
  rw [equal_endpoint_conductor_factor (k := k)]
  exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (1 : k))

/-- Helper for Example 10.55.5: an equal-endpoint polynomial vanishing at `0` is divisible by the
conductor `X^2 - X`. -/
private theorem equal_endpoint_conductor_dvd_of_endpoint_zero (r : R)
    (h0 : (r : Polynomial k).eval 0 = 0) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ∣ (r : Polynomial k) := by
  have h1 : (r : Polynomial k).eval 1 = 0 := by
    have hr_eq :
        (r : Polynomial k).eval 0 = (r : Polynomial k).eval 1 :=
      (mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2
    calc
      (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 := hr_eq.symm
      _ = 0 := h0
  have hX : Polynomial.X ∣ (r : Polynomial k) := by
    apply Polynomial.X_dvd_iff.mpr
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
  have hX1 : Polynomial.X - Polynomial.C (1 : k) ∣ (r : Polynomial k) := by
    simpa [h1] using
      (Polynomial.X_sub_C_dvd_sub_C_eval (p := (r : Polynomial k)) (a := (1 : k)))
  have hcoprime : IsCoprime (Polynomial.X : Polynomial k) (Polynomial.X - Polynomial.C (1 : k)) := by
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : k)) (b := (1 : k))
        (show IsUnit ((0 : k) - 1) by
          exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr zero_ne_one)))
  rcases hcoprime.mul_dvd hX hX1 with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    (r : Polynomial k) = (Polynomial.X * (Polynomial.X - Polynomial.C (1 : k))) * q := by
      simpa [mul_assoc] using hq
    _ = (Polynomial.X ^ 2 - Polynomial.X) * q := by
      rw [equal_endpoint_conductor_factor (k := k)]

/-- Helper for Example 10.55.5: endpoint evaluation zero is exactly the conductor-divisibility
condition needed for the source-faithful exact row. -/
private theorem equal_endpoint_conductor_dvd_of_eval_zero (r : R)
    (hr : equal_endpoint_eval k r = 0) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ∣ (r : Polynomial k) := by
  -- Reinterpret the endpoint-evaluation kernel as vanishing at `0`, then apply the coprime-factor
  -- divisibility argument from the source proof.
  have h0 : (r : Polynomial k).eval 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, equal_endpoint_eval] using hr
  exact equal_endpoint_conductor_dvd_of_endpoint_zero (k := k) r h0

/-- Helper for Example 10.55.5: the normalization `k[X]`, viewed as its regular module over
itself, packaged as an object of `FGModuleCat (Polynomial k)`. -/
private noncomputable def equal_endpoint_polynomial_regular_fgModule :
    FGModuleCat (Polynomial k) :=
  letI : Module (Polynomial k) (Polynomial k) := Semiring.toModule
  letI : Module.Finite (Polynomial k) (Polynomial k) := Module.Finite.self (Polynomial k)
  FGModuleCat.of (Polynomial k) (Polynomial k)

/-- Helper for Example 10.55.5: multiplication by the conductor `X^2 - X` defines the left map in
the source short exact row `0 → k[X] → R → k → 0`. -/
private noncomputable def equal_endpoint_conductor_linearMap :
    Polynomial k →ₗ[R] R :=
  -- TODO: package conductor multiplication as an `R`-linear map on the restricted carrier
  -- `k[X]|_R`, avoiding the remaining owner/coercion mismatch.
  sorry

/-- Helper for Example 10.55.5: endpoint evaluation is the right map in the source short exact row
`0 → k[X] → R → k → 0`. -/
private noncomputable def equal_endpoint_eval_linearMap : R →ₗ[R] k where
  toFun := equal_endpoint_eval k
  map_add' r s := by
    -- Endpoint evaluation is already additive as a ring homomorphism.
    exact (equal_endpoint_eval k).map_add r s
  map_smul' r s := by
    -- The codomain scalar action is defined through the same endpoint-evaluation homomorphism.
    change equal_endpoint_eval k (r * s) = r • equal_endpoint_eval k s
    rw [equal_endpoint_eval_smul]
    simpa using (equal_endpoint_eval k).map_mul r s

/-- Helper for Example 10.55.5: the conductor row
`0 → k[X]|_R --(X^2-X)--> R --ev--> k → 0` packaged in `FGModuleCat R`. -/
private noncomputable def equal_endpoint_conductor_shortComplex :
    CategoryTheory.ShortComplex (FGModuleCat R) :=
  -- TODO: once the carrier-level conductor map is stabilized, package the concrete row
  -- `0 → k[X]|_R → R → k → 0` in `FGModuleCat R`.
  sorry

/-- Helper for Example 10.55.5: the conductor row
`0 → k[X]|_R --(X^2-X)--> R --ev--> k → 0` is short exact. -/
private theorem equal_endpoint_conductor_shortExact :
    ((equal_endpoint_conductor_shortComplex (k := k)).map (ModuleCat.isFG R).ι).ShortExact := by
  -- TODO: prove exactness, injectivity, and surjectivity for the stabilized carrier-level
  -- conductor row.
  sorry

/-- The generic-rank invariant on finite `R`-modules, computed after base change to the fraction
field of `R`. -/
private noncomputable def equalEndpointRank (M : FGModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

/-- Helper for Example 10.55.5: the tensorized short complex over `FractionRing R`. -/
private noncomputable def equal_endpoint_fractionRing_tensor_shortComplex
    (S : CategoryTheory.ShortComplex (FGModuleCat R)) :
    CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  { X₁ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₁)
    X₂ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₂)
    X₃ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₃)
    f := ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.f.hom)
    g := ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.g.hom)
    zero := by
      -- The tensorized maps still compose to zero because `lTensor` respects composition.
      apply ModuleCat.hom_ext
      let hzero : U.g.hom.comp U.f.hom = 0 := by
        ext x
        simpa [LinearMap.comp_apply] using U.moduleCat_zero_apply x
      ext x
      simpa [LinearMap.comp_apply, LinearMap.lTensor_comp] using
        LinearMap.congr_fun (congrArg (LinearMap.lTensor (FractionRing R)) hzero) x }

/-- Helper for Example 10.55.5: tensoring a short exact sequence of finite `R`-modules with the
fraction field produces a short exact sequence of `FractionRing R`-modules. -/
private theorem equal_endpoint_fractionRing_tensor_shortExact
    (S : CategoryTheory.ShortComplex (FGModuleCat R))
    (hS : (S.map (ModuleCat.isFG R).ι).ShortExact) :
    (equal_endpoint_fractionRing_tensor_shortComplex (k := k) S).ShortExact := by
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  -- Repackage the tensorized row in `ModuleCat` so the exactness and mono/epi bridges apply
  -- directly to the underlying linear maps.
  refine ModuleCat.shortComplex_shortExact
      (equal_endpoint_fractionRing_tensor_shortComplex (k := k) S) ?_ ?_ ?_
  · have hExactBase : Function.Exact U.f.hom U.g.hom := by
      exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).1 hS.exact
    -- Flat base change to the fraction field preserves exactness of the middle row.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_exact (FractionRing R) hExactBase)
  · have hf : Function.Injective U.f.hom := by
      simpa [U] using hS.moduleCat_injective_f
    -- Flatness also preserves injectivity of the first map after tensoring.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := FractionRing R) U.f.hom hf)
  · have hg : Function.Surjective U.g.hom := by
      simpa [U] using hS.moduleCat_surjective_g
    -- Right exactness of tensor product gives surjectivity of the last map.
    simpa [equal_endpoint_fractionRing_tensor_shortComplex, U] using
      (LinearMap.lTensor_surjective (FractionRing R) hg)

/-- Helper for Example 10.55.5: generic rank is additive on short exact sequences of finite
`R`-modules after tensoring with the fraction field. -/
private theorem equalEndpointRank_respects_shortExact
    (S : CategoryTheory.ShortComplex (FGModuleCat R))
    (hS : (S.map (ModuleCat.isFG R).ι).ShortExact) :
    equalEndpointRank k S.X₂ =
      equalEndpointRank k S.X₁ + equalEndpointRank k S.X₃ := by
  let T : CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
    equal_endpoint_fractionRing_tensor_shortComplex (k := k) S
  have hT : T.ShortExact := by
    simpa [T] using equal_endpoint_fractionRing_tensor_shortExact (k := k) S hS
  -- The tensor factors are finite-dimensional vector spaces over the fraction field, so the
  -- standard short-exact finrank additivity theorem applies to the tensorized row.
  let _ : Module.Finite (FractionRing R) T.X₁ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₁ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₁.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₁))
  let _ : Module.Finite (FractionRing R) T.X₃ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₃ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₃.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₃))
  let _ : Module.Finite (FractionRing R) T.X₂ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
    let _ : Module.Finite R U.X₂ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₂.obj)
    simpa [T, U, equal_endpoint_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₂))
  let _ : Module.Free (FractionRing R) T.X₁ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₁
  let _ : Module.Free (FractionRing R) T.X₃ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₃
  let _ : Module.Free (FractionRing R) T.X₂ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₂
  have hfinrank :
      Module.finrank (FractionRing R) T.X₂ =
        Module.finrank (FractionRing R) T.X₁ + Module.finrank (FractionRing R) T.X₃ := by
    simpa [T] using
      (ModuleCat.free_shortExact_finrank_add (S := T) hT rfl rfl)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj)
  -- Cast the finite-dimensional equality from `ℕ` to `ℤ` to match `equalEndpointRank`.
  simpa [equalEndpointRank, T, Nat.cast_add] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfinrank

/-- The Grothendieck relations for finite `R`-modules lie in the kernel of the generic-rank
functional. -/
private theorem equalEndpointRelations_le_ker_rank :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift (equalEndpointRank k)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (equalEndpointRank k)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  have hrank :
      equalEndpointRank k S.X₂ =
        equalEndpointRank k S.X₁ + equalEndpointRank k S.X₃ :=
    equalEndpointRank_respects_shortExact (k := k) S hS
  -- Each defining Grothendieck relation maps to the additive rank identity from the short exact
  -- sequence.
  rw [hrank]
  abel

/-- The generic-rank map `K'_0(R) → ℤ` for the equal-endpoint ring. -/
private noncomputable def equalEndpointRankMap :
    finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (equalEndpointRank k)
    (equalEndpointRelations_le_ker_rank k)

/-- Helper for Example 10.55.5: the descended generic-rank map evaluates on a generator class by
the original generic rank. -/
private theorem equalEndpointRankMap_apply_of
    (M : FGModuleCat R) :
    equalEndpointRankMap k (finiteGrothendieckGroupOf R M) = equalEndpointRank k M := by
  -- The quotient lift defining `equalEndpointRankMap` agrees with the generator-level invariant.
  simpa using ModulePropertyK0.lift_of R
    (equalEndpointRank k)
    (equalEndpointRelations_le_ker_rank k)
    M

/-- Helper for Example 10.55.5: the Grothendieck class of the free rank-one module over the
equal-endpoint ring. -/
private noncomputable def equal_endpoint_free_class : finiteGrothendieckGroup R :=
  finiteGrothendieckGroupOf R (FGModuleCat.of R R)

/-- Helper for Example 10.55.5: the free rank-one class has generic rank `1`. -/
private theorem equal_endpoint_free_class_rank :
    equalEndpointRankMap k (equal_endpoint_free_class k) = 1 := by
  -- Evaluate the descended rank map on the free generator class.
  simpa [equal_endpoint_free_class, equalEndpointRank, Module.finrank_tensorProduct,
    Module.finrank_self] using
    (equalEndpointRankMap_apply_of (k := k) (FGModuleCat.of R R))

/-- Helper for Example 10.55.5: the conductor short exact row identifies the normalization class
`[k[X]]` over `R` with the free rank-one class `[R]` in `K'_0(R)`. -/
private theorem equal_endpoint_polynomial_class_eq_free_class :
    finiteGrothendieckGroupOf R
        (equal_endpoint_restrictScalars_object (k := k)
          (equal_endpoint_polynomial_regular_fgModule (k := k))) =
      equal_endpoint_free_class k := by
  -- TODO: deduce `[k[X]|_R] = [R]` from the conductor short exact row once that row is
  -- stabilized on the carrier-level restricted object.
  sorry

/-- Helper for Example 10.55.5: once the free rank-one class maps to `1`, integer multiples of
that class already show that the generic-rank map is surjective. -/
private theorem equalEndpointRankMap_surjective_of_free_class_rank
    (hfree : equalEndpointRankMap k (equal_endpoint_free_class k) = 1) :
    Function.Surjective
      ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
  intro z
  -- The class `z • [R]` maps to the integer `z`.
  refine ⟨(z • equal_endpoint_free_class k : finiteGrothendieckGroup.{u, u} R), ?_⟩
  rw [map_zsmul, hfree]
  simp

/-- The generic-rank map on `K'_0(R)` is bijective for the equal-endpoint ring. -/
-- Proof sketch: surjectivity is realized by the class of a free rank-one module. Injectivity is
-- the equal-endpoint analogue of the PID generic-rank computation, using the classification of
-- finite modules over this ring to show that the `K'_0`-class is determined by generic rank.
private theorem equalEndpointRankMap_bijective :
    Function.Bijective
      ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
  have hsurj :
      Function.Surjective
        ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
    exact equalEndpointRankMap_surjective_of_free_class_rank (k := k)
      (equal_endpoint_free_class_rank (k := k))
  have hinj :
      Function.Injective
        ((equalEndpointRankMap k) : finiteGrothendieckGroup.{u, u} R →+ ℤ) := by
    -- Route correction: the next source-faithful step is not a naive splitting argument but the
    -- conductor comparison `R ⊂ k[X]` together with the restricted quotient bridge
    -- `(k[X]/(X))|_R ≃ k`.
    -- The conductor row is now packaged in `equal_endpoint_conductor_shortExact`, and the first
    -- class consequence `[k[X]|_R] = [R]` is available as
    -- `equal_endpoint_polynomial_class_eq_free_class`; the remaining work is the tensor/Tor
    -- descent showing every `K'_0(R)`-class comes from the polynomial side.
    -- TODO: finish injectivity by constructing the restriction-of-scalars map
    -- `K'_0(k[X]) → K'_0(R)`, tensoring the conductor row with an arbitrary finite module, and
    -- then killing the resulting `k`-supported error terms.
    sorry
  exact ⟨hinj, hsurj⟩

/-- Example 10.55.5 (1): for `R = {f ∈ k[x] | f(0) = f(1)}`, the finite-module Grothendieck group
`K'_0(R)` is canonically identified with `ℤ` by the generic-rank map. -/
noncomputable def equal_endpoint_ring_finiteGrothendieckGroup :
    finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (equalEndpointRankMap k) (equalEndpointRankMap_bijective k)

/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the generic-rank map. -/
theorem equal_endpoint_ring_finiteGrothendieckGroup_apply (x : finiteGrothendieckGroup R) :
    equal_endpoint_ring_finiteGrothendieckGroup k x =
      equalEndpointRankMap k x := rfl

/-- Example 10.55.5 (2): for `R = {f ∈ k[x] | f(0) = f(1)}`, the Grothendieck group `K₀(R)` of finite
projective `R`-modules is identified with `Additive kˣ × ℤ`. -/
-- Proof sketch: combine the classification of finite projective modules over the equal-endpoint
-- ring with the generic-rank identification of `K'_0(R)` with `ℤ`, and choose an additive
-- equivalence whose second component matches the canonical comparison map to `K'_0(R)`.
theorem equal_endpoint_ring_projectiveGrothendieckGroup :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
      (equal_endpoint_ring_finiteGrothendieckGroup k).toAddMonoidHom.comp K0→K0' := by
  -- TODO: after the source-faithful `K'_0(R) ≃ ℤ` injectivity step is restored, finish this
  -- theorem by the original twist/pullback stable-classification route for projective modules.
  sorry

/-- On an element of `K₀(R)`, some additive equivalence
`K₀(R) ≃+ Additive kˣ × ℤ` has `ℤ`-component given by the canonical comparison to `K'_0(R)`
followed by the generic-rank identification of `K'_0(R)` with `ℤ`. -/
theorem equal_endpoint_ring_projectiveGrothendieckGroup_snd_apply
    (x : projectiveGrothendieckGroup R) :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (e x).2 =
        equal_endpoint_ring_finiteGrothendieckGroup k (K0→K0' x) := by
  rcases equal_endpoint_ring_projectiveGrothendieckGroup k with ⟨e, he⟩
  refine ⟨e, ?_⟩
  simpa using DFunLike.congr_fun he x

end
