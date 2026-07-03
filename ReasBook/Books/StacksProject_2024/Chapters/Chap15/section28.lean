import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.CategoryTheory.Distributive.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_28_1 (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory ModuleCat ExteriorAlgebra

variable {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]

/- Definition 15.28.1, source-facing layer: the Koszul complex is built on the canonical graded
commutative algebra structure on `ExteriorAlgebra R E`. -/
recall ExteriorAlgebra.gradedAlgebra

/- The source-facing Koszul differential on `ExteriorAlgebra R E` is the canonical contraction
operator `CliffordAlgebra.contractLeft φ`. -/
recall CliffordAlgebra.contractLeft

/- On generators, the source-facing Koszul differential extends the linear form `φ`. -/
recall CliffordAlgebra.contractLeft_ι

/- The source-facing Koszul differential satisfies the graded Leibniz rule. -/
recall CliffordAlgebra.contractLeft_ι_mul

private theorem contractLeft_ιMulti_mem_exteriorPower (φ : E →ₗ[R] R) :
    ∀ n (v : Fin (n + 1) → E),
      CliffordAlgebra.contractLeft φ (ιMulti R (n + 1) v) ∈ ⋀[R]^n E
  | 0, v => by
      simp [ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one, ExteriorAlgebra.exteriorPower]
  | n + 1, v => by
      rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ <| ιMulti_range R (n + 1) ⟨Matrix.vecTail v, rfl⟩
      · have htail : CliffordAlgebra.contractLeft φ (ιMulti R (n + 1) (Matrix.vecTail v)) ∈ ⋀[R]^n E := by
          simpa using contractLeft_ιMulti_mem_exteriorPower φ n (Matrix.vecTail v)
        have hι : ι R (v 0) ∈ ⋀[R]^1 E := by
          simp [ExteriorAlgebra.exteriorPower]
        simpa [ExteriorAlgebra.exteriorPower, add_comm] using SetLike.mul_mem_graded hι htail

/-- The canonical Koszul differential on `ExteriorAlgebra R E` lowers exterior degree by one. -/
theorem contractLeft_mem_exteriorPower (φ : E →ₗ[R] R) (n : ℕ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ⋀[R]^(n + 1) E) :
    CliffordAlgebra.contractLeft φ x ∈ ⋀[R]^n E := by
  rw [← ιMulti_span_fixedDegree R (n + 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨v, rfl⟩
      exact contractLeft_ιMulti_mem_exteriorPower φ n v
  | zero =>
      simp
  | add a b _ _ ha hb =>
      simpa [map_add] using Submodule.add_mem (⋀[R]^n E) ha hb
  | smul a y _ hy =>
      simpa [map_smul] using Submodule.smul_mem (⋀[R]^n E) a hy

/-- The degree `n + 1` Koszul differential is the restriction of `CliffordAlgebra.contractLeft φ`
to the `(n + 1)`st exterior power. -/
noncomputable def koszulDifferentialLinearMap (φ : E →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^n E :=
  (CliffordAlgebra.contractLeft φ).restrict fun _ hx ↦ contractLeft_mem_exteriorPower φ n hx

/-- On each graded piece, `koszulDifferentialLinearMap` is literally the restriction of
`CliffordAlgebra.contractLeft φ`. -/
@[simp] theorem koszulDifferentialLinearMap_apply (φ : E →ₗ[R] R) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    (koszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) = CliffordAlgebra.contractLeft φ x :=
  rfl

/-- The degree `n + 1` differential in the Koszul complex attached to `φ`, viewed in
`ModuleCat R`. -/
noncomputable def koszulDifferential (φ : E →ₗ[R] R) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower (n + 1) ⟶ (ModuleCat.of R E).exteriorPower n :=
  ModuleCat.ofHom (koszulDifferentialLinearMap φ n)

/-- Consecutive differentials in the Koszul complex of `φ` compose to zero. -/
theorem koszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n = 0 := by
  change ModuleCat.ofHom ((koszulDifferentialLinearMap φ n).comp (koszulDifferentialLinearMap φ (n + 1))) = 0
  ext x
  simp [koszulDifferentialLinearMap, CliffordAlgebra.contractLeft_contractLeft]

/-- Definition 15.28.1: the Koszul complex associated to an `R`-linear map `φ : E →ₗ[R] R` is
the chain-complex bridge/view of `CliffordAlgebra.contractLeft φ` on the graded algebra
`ExteriorAlgebra R E`. -/
noncomputable abbrev koszulComplex (φ : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (koszulDifferential_sq φ)

/-- The degree `n` object of the Koszul complex of `φ` is the `n`th exterior power of `E`. -/
theorem koszulComplex_X (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex φ).X n = (ModuleCat.of R E).exteriorPower n :=
  rfl

/-! ### Definition_15_28_2 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open ModuleCat

section

variable {R : Type u} [CommRing R]

/-- The linear form `(f₁, …, fᵣ) : R^r → R` attached to a finite family `f : Fin r → R`. -/
noncomputable abbrev koszulFamilyLinearMap {r : ℕ} (f : Fin r → R) : (Fin r → R) →ₗ[R] R :=
  Module.piEquiv (Fin r) R R f

-- Proof sketch: `Module.piEquiv` is defined from the standard basis of `Fin r → R`, so evaluating
-- on the `i`th basis vector returns the prescribed coefficient `f i`.
/-- The linear form attached to `f` sends the `i`th standard basis vector of `R^r` to `f i`. -/
theorem koszulFamilyLinearMap_basis {r : ℕ} (f : Fin r → R) (i : Fin r) :
    koszulFamilyLinearMap f (Pi.basisFun R (Fin r) i) = f i := sorry

/-- Definition 15.28.2: the Koszul complex on a finite family `f : Fin r → R` is the Koszul
complex associated to the linear form `(f₁, …, fᵣ) : R^r → R`. -/
noncomputable abbrev koszulComplexOn {r : ℕ} (f : Fin r → R) : ChainComplex (ModuleCat R) ℕ :=
  koszulComplex (koszulFamilyLinearMap f)

/-- The `n`th powered Koszul complex on `(f₁^(n+1), \ldots, fᵣ^(n+1))`, indexed so that stage
`0` is the ordinary Koszul complex on `f`. -/
noncomputable abbrev koszulPowerStage {r : ℕ} (f : Fin r → R) (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulComplexOn (fun i ↦ f i ^ (n + 1))

/-- The degree `n` object of the Koszul complex on `f` is the `n`th exterior power of `R^r`. -/
theorem koszulComplexOn_X {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (koszulComplexOn f).X n = (ModuleCat.of R (Fin r → R)).exteriorPower n :=
  rfl

end

/-! ### Lemma_15_28_3 (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory ModuleCat ExteriorAlgebra
open ModuleCat.exteriorPower

section

variable {R : Type u} {E : Type v} {E' : Type v}
variable [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
variable {φ : E →ₗ[R] R} {φ' : E' →ₗ[R] R} {ψ : E →ₗ[R] E'}

/- Domain-style sampling:
- primary domain: Koszul differentials as derivations on exterior algebras, with chain-complex
  realization on the graded pieces;
- sampled owner declarations:
  `ExteriorAlgebra.map`,
  `CliffordAlgebra.contractLeft`,
  `koszulComplex`,
  `ModuleCat.exteriorPower.map`;
- best owner abstraction: the source-facing DGA map is the canonical algebra morphism
  `ExteriorAlgebra.map ψ`, and the induced chain map on `koszulComplex` is the derived bridge
  `KoszulComplex.map` on graded pieces;
- primitive data: a linear map `ψ : E →ₗ[R] E'` together with the compatibility
  `φ'.comp ψ = φ`;
- derived API: the differential-compatibility theorem for `ExteriorAlgebra.map ψ` and the
  induced chain map, with the degreewise commutative square kept as private bridge data;
- layer triage: the owner-level theorem on `ExteriorAlgebra.map ψ` is `source-facing`, while
  `KoszulComplex.map` is the derived `bridge/view` on the canonical chain complexes.
-/

namespace ExteriorAlgebra

/-- Lemma 15.28.3: the algebra map on exterior algebras induced by a compatible linear map
`ψ : E →ₗ[R] E'` commutes with the Koszul differential `CliffordAlgebra.contractLeft`. This is
the source-facing differential graded algebra morphism; `KoszulComplex.map` below is its
chain-map realization on the graded pieces. -/
theorem map_contractLeft (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) :
    (CliffordAlgebra.contractLeft φ').comp (ExteriorAlgebra.map ψ).toLinearMap =
      (ExteriorAlgebra.map ψ).toLinearMap.comp (CliffordAlgebra.contractLeft φ) := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [LinearMap.comp_apply]
  | add x y hx hy =>
      simpa [LinearMap.comp_apply] using congrArg₂ (fun a b ↦ a + b) hx hy
  | ι_mul x e hx =>
      have hψe : φ' (ψ e) = φ e := by
        simpa using LinearMap.congr_fun hψ e
      simpa [LinearMap.comp_apply, CliffordAlgebra.contractLeft_ι_mul, hψe] using
        congrArg (fun z ↦ ι R (ψ e) * z) hx

end ExteriorAlgebra

private theorem koszulDifferential_comm (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) (n : ℕ) :
    CommSq (ModuleCat.exteriorPower.map (ofHom ψ) (n + 1)) (koszulDifferential φ n)
      (koszulDifferential φ' n) (ModuleCat.exteriorPower.map (ofHom ψ) n) := sorry

namespace KoszulComplex

/-- Lemma 15.28.3: an `R`-linear map `ψ : E →ₗ[R] E'` satisfying `φ' ∘ ψ = φ` induces the
underlying chain map of the source-facing differential graded algebra morphism
`ExteriorAlgebra.map ψ`. -/
noncomputable abbrev map (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (fun n ↦ by
      simpa [koszulComplex, koszulDifferential, ChainComplex.of_d, Nat.add_assoc] using
        HomologicalComplex.d_comp_d (koszulComplex φ) ((n + 1) + 1) (n + 1) n)
    ((ModuleCat.of R E').exteriorPower)
    (koszulDifferential φ')
    (fun n ↦ by
      simpa [koszulComplex, koszulDifferential, ChainComplex.of_d, Nat.add_assoc] using
        HomologicalComplex.d_comp_d (koszulComplex φ') ((n + 1) + 1) (n + 1) n)
    (fun n ↦ ModuleCat.exteriorPower.map (ofHom ψ) n)
    (fun n ↦ by
      simpa using (koszulDifferential_comm ψ hψ n).w)

end KoszulComplex

end

/-! ### Lemma_15_28_4 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open ModuleCat
open Module
open scoped Matrix
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]

private theorem koszulLinearForm_matrix_transpose_toLin' {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) (f : Fin r → R) :
    koszulLinearForm (x.toLin' f) = (koszulLinearForm f).comp (xᵀ).toLin' := sorry

private theorem koszulLinearForm_matrix_transpose_toLin'_comp_inv {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    (koszulLinearForm (x.toLin' f)).comp (⅟ (xᵀ)).toLin' = koszulLinearForm f := sorry

/-- Lemma 15.28.4: an invertible linear change of generators
`g i = ∑ j, x i j * f j` induces an isomorphism between the Koszul complex on `f` and the Koszul
complex on the transformed family `g`. -/
noncomputable def koszul_complex_on_matrix_linear_combination_iso {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    K^•(f) ≅ K^•(x.toLin' f) where
  hom :=
    KoszulComplex.map (⅟ (xᵀ)).toLin' (koszulLinearForm_matrix_transpose_toLin'_comp_inv x f)
  inv :=
    KoszulComplex.map (xᵀ).toLin' (koszulLinearForm_matrix_transpose_toLin' x f).symm
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-- The degree `n` component of the forward map in
`koszul_complex_on_matrix_linear_combination_iso x f` is induced by the inverse transpose of
`x`. -/
theorem koszul_complex_on_matrix_linear_combination_iso_hom_f {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) (n : ℕ) :
    (koszul_complex_on_matrix_linear_combination_iso x f).hom.f n =
      ModuleCat.exteriorPower.map (ofHom (⅟ (xᵀ)).toLin') n := by
  simp [koszul_complex_on_matrix_linear_combination_iso]

end

/-! ### Lemma_15_28_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open ModuleCat

universe u v

section Lemma_15_28_5

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]
variable (φ : E →ₗ[R] R) (e : E)

/- Domain triage:
* primary domain: Koszul chain complexes, their degreewise differentials, and chain homotopies;
* sampled owner declarations:
  - `koszulDifferentialLinearMap`, `koszulComplex`, `koszulLeftWedge`, and
    `koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential`
    from `Definition_15_28_1`,
  - `Homotopy`,
  - `Homotopy.nullHomotopicMap'`,
  - `Homotopy.nullHomotopy'`,
  - `CliffordAlgebra.contractLeft_ι_mul`.
* source-facing: left wedge by `e` and the resulting null-homotopy statement;
* core/canonical: `koszulComplex φ` and `Homotopy`;
* bridge/view: the canonical null-homotopic map `Homotopy.nullHomotopicMap'` built from the
  degreewise left-wedge maps, together with its identification with `(φ e) • 𝟙`;
* primitive data: the canonical left-wedge homotopy components
  `koszulLeftWedgeHomotopyHom φ e`;
* derived API: the chain-homotopy on `koszulComplex φ`. -/

private noncomputable abbrev koszulLeftWedgeHomotopyHom (φ : E →ₗ[R] R) (e : E) :
    ∀ i j, (ComplexShape.down ℕ).Rel j i → ((koszulComplex φ).X i ⟶ (koszulComplex φ).X j)
  | i, j, hij => by
      cases hij
      simpa using ModuleCat.ofHom (koszulLeftWedge e i)

@[simp] private theorem koszulLeftWedgeHomotopyHom_apply
    (n : ℕ) :
    koszulLeftWedgeHomotopyHom φ e n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
      ModuleCat.ofHom (koszulLeftWedge e n) := by
  rfl

private noncomputable abbrev koszulLeftWedgeNullHomotopy :
    Homotopy (Homotopy.nullHomotopicMap' (koszulLeftWedgeHomotopyHom φ e)) 0 :=
  Homotopy.nullHomotopy' (koszulLeftWedgeHomotopyHom φ e)

private theorem koszulScalarEndomorphism_eq_nullHomotopicMap :
    (φ e) • 𝟙 (koszulComplex φ) =
      Homotopy.nullHomotopicMap' (koszulLeftWedgeHomotopyHom φ e) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (ComplexShape.down_mk 1 0 rfl)
        (by
          intro l
          simpa only [ComplexShape.down_Rel] using Nat.succ_ne_zero l)
        (koszulLeftWedgeHomotopyHom φ e)]
      simpa [koszulComplex, koszulDifferential] using
        congrArg ModuleCat.ofHom
          (koszulDifferentialLinearMap_comp_koszulLeftWedge_zero φ e).symm
  | succ n =>
      rw [Homotopy.nullHomotopicMap'_f
        (ComplexShape.down_mk (n + 2) (n + 1) rfl)
        (ComplexShape.down_mk (n + 1) n rfl)
        (koszulLeftWedgeHomotopyHom φ e)]
      have hs :
          (φ e • 𝟙 (koszulComplex φ)).f (n + 1) =
            ModuleCat.ofHom
              ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) :=
        rfl
      have hd₁ :
          (koszulComplex φ).d (n + 1) n =
            ModuleCat.ofHom (koszulDifferentialLinearMap φ n) := by
        simpa [koszulComplex, koszulDifferential] using
          (ChainComplex.of_d ((ModuleCat.of R E).exteriorPower)
            (koszulDifferential φ) _ n)
      have hd₂ :
          (koszulComplex φ).d (n + 2) (n + 1) =
            ModuleCat.ofHom (koszulDifferentialLinearMap φ (n + 1)) := by
        simpa [koszulComplex, koszulDifferential] using
          (ChainComplex.of_d ((ModuleCat.of R E).exteriorPower)
            (koszulDifferential φ) _ (n + 1))
      have hw₁ :
          koszulLeftWedgeHomotopyHom φ e n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
            ModuleCat.ofHom (koszulLeftWedge e n) :=
        by
          simpa using koszulLeftWedgeHomotopyHom_apply φ e n
      have hw₂ :
          koszulLeftWedgeHomotopyHom φ e (n + 1) (n + 2)
              (ComplexShape.down_mk (n + 2) (n + 1) rfl) =
            ModuleCat.ofHom (koszulLeftWedge e (n + 1)) :=
        by
          simpa using koszulLeftWedgeHomotopyHom_apply φ e (n + 1)
      rw [hs, hd₁, hd₂, hw₁, hw₂]
      rw [ModuleCat.ofHom_comp, ModuleCat.ofHom_comp]
      change
        ModuleCat.ofHom ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) =
          ModuleCat.ofHom
            ((koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n) +
              (koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)))
      have hcomp :
          ModuleCat.ofHom
              ((koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)) +
                (koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n)) =
            ModuleCat.ofHom
              ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) :=
        congrArg ModuleCat.ofHom
          (koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential
            φ e n)
      rw [← hcomp]
      congr 1
      exact add_comm _ _

/-- Lemma 15.28.5: multiplication by `φ e` on the Koszul complex of `φ` is null-homotopic via
left wedge by `e`. -/
noncomputable def koszul_scalar_endomorphism_homotopy_zero
    (φ : E →ₗ[R] R) (e : E) :
    Homotopy ((φ e) • 𝟙 (koszulComplex φ)) 0 :=
  (Homotopy.ofEq (koszulScalarEndomorphism_eq_nullHomotopicMap φ e)).trans
    (koszulLeftWedgeNullHomotopy φ e)

end Lemma_15_28_5

/-! ### Lemma_15_28_6 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open scoped KoszulComplex

universe u

section Lemma_15_28_6

variable {R : Type u} [CommRing R]
variable {r : ℕ}

-- Proof sketch: specialize Lemma 15.28.5 to `E = Fin r → R`, take the linear form attached to the
-- sequence `f`, and use the `i`th standard basis vector as the contracting homotopy.
/-- Lemma 15.28.6: multiplication by `f i` on the Koszul complex on `f` is homotopic to zero via
left wedge by the `i`th standard basis vector. -/
  noncomputable def koszul_generator_scalar_endomorphism_homotopy_zero
    (f : Fin r → R) (i : Fin r) :
    Homotopy ((f i) • 𝟙 (K^•(f))) 0 := by
  have h_eval : koszulLinearForm f (Pi.single i 1) = f i := by
    have hsum : (∑ j, Pi.single j (f j) : Fin r → R) i = f i := by
      simpa using congrArg (fun g : Fin r → R ↦ g i) (Pi.sum_single_apply f)
    rw [koszulLinearForm, Module.piEquiv_apply_apply]
    simpa [Pi.single_apply, mul_comm] using hsum
  simpa [Pi.basisFun_apply, h_eval] using
    koszul_scalar_endomorphism_homotopy_zero (koszulLinearForm f)
      (Pi.basisFun R (Fin r) i)

private theorem homologyMap_smul
    {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (a : R) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n] :
    homologyMap (a • φ) n = a • homologyMap φ n := by
  change
    ShortComplex.homologyMap
        (a • (shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map φ) =
      a • ShortComplex.homologyMap
        ((shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map φ)
  rw [ShortComplex.homologyMap_smul]
  rfl

private theorem homologyMap_smul_id
    {K : ChainComplex (ModuleCat R) ℕ} (a : R) (n : ℕ) [K.HasHomology n] :
    homologyMap (a • 𝟙 K) n = a • 𝟙 (K.homology n) := by
  rw [homologyMap_smul, homologyMap_id]

-- Proof sketch: apply `Homotopy.homologyMap_eq` to the given homotopy between `a • 𝟙 K` and `0`,
-- then rewrite the homology map of the zero morphism.
/-- A null-homotopic scalar endomorphism induces the zero map on homology. -/
theorem homologyMap_smul_id_eq_zero_of_homotopy_zero
    {K : ChainComplex (ModuleCat R) ℕ} (a : R) (n : ℕ) [K.HasHomology n]
    (h : Homotopy (a • 𝟙 K) 0) :
    homologyMap (a • 𝟙 K) n = 0 := by
  have hz : homologyMap (0 : K ⟶ K) n = 0 := by simp
  exact (h.homologyMap_eq n).trans hz

-- Proof sketch: the previous theorem shows that every generator `f i` acts by zero on homology;
-- then identify these endomorphisms with scalar multiplication on `K.homology n` and pass from the
-- generators to their ideal span.
/-- If every generator acts null-homotopically on a chain complex, then the ideal they generate
annihilates each homology module. -/
theorem ideal_span_le_annihilator_of_homotopic_zero_generators
    {K : ChainComplex (ModuleCat R) ℕ} (f : Fin r → R) (n : ℕ) [K.HasHomology n]
    (hhom : ∀ i, Homotopy (f i • 𝟙 K) 0) :
    Ideal.span (Set.range f) ≤ Module.annihilator R (K.homology n) := by
  rw [Ideal.span_le]
  intro a ha
  rcases ha with ⟨i, rfl⟩
  change f i ∈ Module.annihilator R (↑(K.homology n))
  rw [Module.mem_annihilator]
  intro x
  change ((f i) • 𝟙 (K.homology n)).hom x = 0
  have hzero : homologyMap (f i • 𝟙 K) n = 0 :=
    homologyMap_smul_id_eq_zero_of_homotopy_zero (f i) n (hhom i)
  have hsmul : homologyMap (f i • 𝟙 K) n = (f i) • 𝟙 (K.homology n) :=
    homologyMap_smul_id (f i) n
  rw [← hsmul, hzero]
  rfl

-- Proof sketch: apply the generic annihilator theorem to the source-facing null-homotopies from
-- `koszul_generator_scalar_endomorphism_homotopy_zero`.
/-- Lemma 15.28.6: the ideal generated by the entries of `f` annihilates each homology module of
the Koszul complex `K^•(f)`. -/
theorem ideal_span_le_annihilator_koszulComplex_homology
    (f : Fin r → R) (n : ℕ) [(K^•(f)).HasHomology n] :
    Ideal.span (Set.range f) ≤ Module.annihilator R ((K^•(f)).homology n) := by
  exact ideal_span_le_annihilator_of_homotopic_zero_generators f n
    (fun i ↦ koszul_generator_scalar_endomorphism_homotopy_zero f i)

end Lemma_15_28_6

/-! ### Lemma_15_28_7 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex ModuleCat exteriorPower
open HomologicalComplex.homotopyCofiber

variable {R : Type u} [CommRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

private instance exteriorPower_hasBinaryBiproduct (n : ℕ) :
    HasBinaryBiproduct ((ModuleCat.of R E).exteriorPower n)
      ((ModuleCat.of R E).exteriorPower (n + 1)) :=
  HasBinaryBiproduct.of_hasBinaryProduct _ _

private instance smul_id_koszulComplex_hasHomotopyCofiber
    (φ : E →ₗ[R] R) (f : R) :
    HasHomotopyCofiber (f • 𝟙 (koszulComplex φ)) where
  hasBinaryBiproduct i j hij := by
    rcases i with _ | i
    · cases hij
    · obtain rfl : j = i := by
        simpa [ComplexShape.down] using hij
      infer_instance

/- Domain-style sampling:
- primary domain: chain-complex mapping-cone comparisons for Koszul complexes;
- owner declarations inspected: `HomologicalComplex.homotopyCofiber`,
  `HomologicalComplex.homotopyCofiber.XIsoBiprod`,
  `HomologicalComplex.Hom.isoOfComponents`, `ModuleCat.exteriorPower.map`,
  `LinearEquiv.toModuleIso`, and `koszulLeftWedge`;
- best owner abstraction: the canonical cone object `HomologicalComplex.homotopyCofiber` for the
  scalar endomorphism `f • 𝟙 (koszulComplex φ)`;
- primitive data: the degreewise decomposition of `⋀[R]^n (E × R)` into the `E`-part and the
  summand generated by wedging with `(0, 1)`;
- derived API: the comparison isomorphism between the augmented Koszul complex and the canonical
  homotopy cofiber;
- layer triage: this item is a `bridge/view` comparison between a source-facing Koszul-complex
  presentation and the core/canonical homotopy-cofiber owner.
- universe note: unlike `Definition_15_28_1`, this bridge must remain in one module-object
  universe because its canonical ingredients `ModuleCat.ofHom` and `ModuleCat.exteriorPower.iso₀`
  compare `E`, `E × R`, and `R` inside a single `ModuleCat R`; the restriction is therefore a
  concrete owner-side constraint of the comparison, not a duplicate local abstraction.
-/

private noncomputable def koszulCoprodScalarSuccBiprodIso (n : ℕ) :
    (ModuleCat.of R (E × R)).exteriorPower (n + 1) ≅
      (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) :=
  let hom :
      (ModuleCat.of R (E × R)).exteriorPower (n + 1) ⟶
        (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) :=
    biprod.lift
      (ModuleCat.ofHom (koszulDifferentialLinearMap (LinearMap.snd R E R) n) ≫
        ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.fst R E R)) n)
      (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.fst R E R)) (n + 1))
  let inv :
      (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) ⟶
        (ModuleCat.of R (E × R)).exteriorPower (n + 1) :=
    biprod.desc
      (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.inl R E R)) n ≫
        ModuleCat.ofHom (koszulLeftWedge ((0 : E), (1 : R)) n))
      (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.inl R E R)) (n + 1))
  (LinearEquiv.ofLinear hom.hom inv.hom
    (by
      sorry)
    (by
      sorry)).toModuleIso

private noncomputable def koszulCoprodScalarComponentIso
    (φ : E →ₗ[R] R) (f : R) (n : ℕ) :
    (koszulComplex (koszulCoprodScalarLinearMap φ f)).X n ≅
      (homotopyCofiber (f • 𝟙 (koszulComplex φ))).X n :=
  let α := f • 𝟙 (koszulComplex φ)
  match n with
  | 0 =>
      ModuleCat.exteriorPower.iso₀ (ModuleCat.of R (E × R)) ≪≫
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of R E)).symm ≪≫
        (XIso α 0
          (by simp [ComplexShape.down])).symm
  | n + 1 =>
      koszulCoprodScalarSuccBiprodIso n ≪≫
        (XIsoBiprod α (n + 1) n
          (ComplexShape.down_mk (n + 1) n rfl)).symm

private theorem koszulCoprodScalarComponentIso_commSq
    (φ : E →ₗ[R] R) (f : R) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    CommSq
      (koszulCoprodScalarComponentIso φ f i).hom
      ((koszulComplex (koszulCoprodScalarLinearMap φ f)).d i j)
      ((homotopyCofiber (f • 𝟙 (koszulComplex φ))).d i j)
      (koszulCoprodScalarComponentIso φ f j).hom := by
  rcases i with _ | i
  · cases hij
  · obtain rfl : j = i := by
      simpa [ComplexShape.down] using hij
    exact ⟨by sorry⟩

/-- Lemma 15.28.7: if `φ' : E × R →ₗ[R] R` is given by `φ` on `E` and by multiplication by `f` on
the `R`-summand, then the Koszul complex of `φ'` is canonically isomorphic to the cone of
multiplication by `f` on the Koszul complex of `φ`, expressed in mathlib as the homotopy cofiber
of the canonical scalar endomorphism `f • 𝟙 (koszulComplex φ)`. -/
noncomputable def koszulComplex_coprod_scalar_iso_homotopyCofiber
    (φ : E →ₗ[R] R) (f : R) :
    koszulComplex (koszulCoprodScalarLinearMap φ f) ≅
      homotopyCofiber (f • 𝟙 (koszulComplex φ)) :=
  Hom.isoOfComponents
    (koszulCoprodScalarComponentIso φ f)
    (fun i j hij ↦ (koszulCoprodScalarComponentIso_commSq φ f i j hij).w)

/-! ### Lemma_15_28_8 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory HomologicalComplex Module
open scoped KoszulComplex

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: family-level Koszul complexes and their comparison with the canonical
  homotopy cofiber of scalar multiplication;
- sampled owner declarations: `koszulComplex`, `KoszulComplex.map`,
  `koszulComplex_coprod_scalar_iso_homotopyCofiber`, `Fin.finSuccEquivLast`,
  `LinearEquiv.piOptionEquivProd`, `LinearEquiv.prodComm`;
- best owner abstraction: the core/canonical owner remains the linear-form Koszul complex
  `koszulComplex` together with the canonical cone object `homotopyCofiber`;
- primitive data: the tuple `f : Fin (r + 1) → R`, split into its truncated family
  `Fin.init f` and last coefficient `f (Fin.last r)`;
- derived API: the private transport from the canonical `Option`-indexed Pi equivalence to the
  coproduct linear form, and the public family-level bridge
  `koszulComplex_iso_homotopyCofiber_truncate_last`;
- layer triage: this file is entirely `bridge/view`; the local linearization of
  the last-coordinate split stays private because it only repackages the canonical owners above
  and carries no extra source-level mathematics.
-/ 

private def finSnocLinearEquiv (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) :=
  { toFun := fun x ↦ Fin.snoc x.1 x.2
    invFun := fun x ↦ (Fin.init x, x (Fin.last r))
    map_add' := by
      intro x y
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp
    map_smul' := by
      intro a x
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp
    left_inv := by
      intro x
      ext i <;> simp
    right_inv := by
      intro x
      ext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · simp [Fin.init_def] }

@[simp] private theorem finSnocLinearEquiv_apply {r : ℕ} (x : (Fin r → R) × R) :
    finSnocLinearEquiv r x = Fin.snoc x.1 x.2 :=
  rfl

@[simp] private theorem finSnocLinearEquiv_symm_apply {r : ℕ} (x : Fin (r + 1) → R) :
    (finSnocLinearEquiv r).symm x = (Fin.init x, x (Fin.last r)) :=
  rfl

private theorem koszulLinearForm_snoc_comp_symm {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (koszulCoprodScalarLinearMap (koszulLinearForm fs) a).comp
        (finSnocLinearEquiv r).symm.toLinearMap =
      koszulLinearForm (Fin.snoc fs a) := by
  apply LinearMap.ext
  intro x
  simp [LinearMap.comp_apply, finSnocLinearEquiv_symm_apply,
    koszulLinearForm, piEquiv_apply_apply, Fin.sum_univ_castSucc, Fin.init_def]

private theorem koszulLinearForm_snoc_comp {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (koszulLinearForm (Fin.snoc fs a)).comp (finSnocLinearEquiv r).toLinearMap =
      koszulCoprodScalarLinearMap (koszulLinearForm fs) a := by
  apply LinearMap.ext
  intro x
  simp [LinearMap.comp_apply, finSnocLinearEquiv_apply, koszulCoprodScalarLinearMap,
    koszulLinearForm, piEquiv_apply_apply, Fin.sum_univ_castSucc]

private def koszulComplex_snoc_iso_coprodScalar {r : ℕ}
    (fs : Fin r → R) (a : R) :
    K^•(Fin.snoc fs a) ≅
      koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) where
  hom := KoszulComplex.map (finSnocLinearEquiv r).symm.toLinearMap
    (koszulLinearForm_snoc_comp_symm fs a)
  inv := KoszulComplex.map (finSnocLinearEquiv r).toLinearMap
    (koszulLinearForm_snoc_comp fs a)
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

-- Proof sketch: apply `koszulComplex_coprod_scalar_iso_homotopyCofiber` to the linear
-- form attached to the truncated family `Fin.init f` and the last coefficient
-- `f (Fin.last r)`, then transport the linear-map Koszul complex of
-- `koszulCoprodScalarLinearMap` back to the family-level complex through the canonical
-- `Fin.snoc` linear equivalence.

/-- Lemma 15.28.8: for a finite family `f : Fin (r + 1) → R`, the Koszul complex on `f` is
canonically isomorphic to the cone of multiplication by the last entry on the Koszul complex of
the truncated family, written in mathlib as the homotopy cofiber of the canonical scalar
endomorphism `f (Fin.last r) • 𝟙`. -/
def koszulComplex_iso_homotopyCofiber_truncate_last
    {r : ℕ} (f : Fin (r + 1) → R) :
    K^•(f) ≅
      homotopyCofiber
        ((f (Fin.last r)) • 𝟙 (K^•(Fin.init f))) := by
  simpa using
    koszulComplex_snoc_iso_coprodScalar (Fin.init f) (f (Fin.last r)) ≪≫
      koszulComplex_coprod_scalar_iso_homotopyCofiber
        (koszulLinearForm (Fin.init f)) (f (Fin.last r))

/-! ### Lemma_15_28_9 (from Chap15) -/
noncomputable section

universe v u

open CategoryTheory HomologicalComplex

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: mapping-cone / homotopy-cofiber constructions in the homotopy category of chain
  complexes;
- owner declarations inspected: `HomologicalComplex.homotopyCofiber`,
  `HomotopyEquiv`, `HomologicalComplex.homotopyEquivalences`, and the chapter recall
  `Definition_12_13_2`;
- best owner abstraction: the canonical cone object `homotopyCofiber` together with the canonical
  homotopy-equivalence owner/bridge pair `HomotopyEquiv` and `homotopyEquivalences`.

Primitive data are only the chain complex `A` and the scalar endomorphisms `f • 𝟙 A`,
`g • 𝟙 A`, and `(f * g) • 𝟙 A`. The morphism
`(homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A)` is source-facing bridge data,
and the resulting morphism from `homotopyCofiber ((f * g) • 𝟙 A)` to the cone of that morphism
being a homotopy equivalence is derived API, not primitive owner data.

Layer triage:
- `core/canonical`: `homotopyCofiber` and `HomotopyEquiv`;
- `bridge/view`: the source-facing assertion that there exists some comparison morphism whose cone
  is homotopy equivalent to the cone of multiplication by `f * g`.
-/

-- Proof sketch: first treat the two-term complex `R ⟶ R`, where there is an explicit morphism
-- from the shifted cone of multiplication by `f` to the cone of multiplication by `g` whose cone
-- is homotopy equivalent to the cone of multiplication by `f * g`. Then tensor that explicit
-- two-term construction with `A` and pass to the total complex, using compatibility of
-- totalization with cones and homotopies.
/-- Lemma 15.28.9: for a chain complex `A_•` of `R`-modules and scalars `f, g : R`, the cone of
multiplication by `f * g` on `A_•` is homotopy equivalent to the cone of some morphism from the
degree-one shift of the cone of multiplication by `f` to the cone of multiplication by `g`. -/
theorem homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    ∃ α : (homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A),
      Nonempty (HomotopyEquiv (homotopyCofiber ((f * g) • 𝟙 A)) (homotopyCofiber α)) := sorry

/-! ### Lemma_15_28_10 (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex

/- Domain-style sampling:
- primary domain: degree shifts of `ℕ`-indexed chain complexes, expressed canonically through the
  cochain-complex shift on `ℤ` together with complex-shape embeddings;
- sampled owner declarations:
  `HomologicalComplex.extend`,
  `HomologicalComplex.restriction`,
  `ComplexShape.embeddingDownNat`,
  `CategoryTheory.shiftFunctor` on `CochainComplex C ℤ`;
- best owner abstraction: for an `ℕ`-indexed chain complex `K`, the source-facing degree-one
  shifted complex is the bridge/view
  `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`;
- primitive data: the chain complex `K` and the canonical embedding `embeddingDownNat`;
- derived API: any `ℕ`-indexed reformulation of that shifted complex.

Source/core/bridge triage:
- `source-facing`: the existence statement for the Koszul complexes in Lemma 15.28.10;
- `core/canonical`: `extend`, `restriction`, `embeddingDownNat`, and the canonical cochain shift;
- `bridge/view`: the `ℕ`-indexed shifted-chain source object obtained by extending to `ℤ`,
  shifting by `-1`, and restricting back. This file should therefore use that owner expression
  directly rather than keep a parallel local shift definition. -/

section

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

-- Proof sketch: identify the three Koszul complexes attached to
-- `koszulCoprodScalarLinearMap φ f`, `koszulCoprodScalarLinearMap φ g`, and
-- `koszulCoprodScalarLinearMap φ (f * g)` with the corresponding homotopy cofibers from
-- Lemma 15.28.7; interpret the degree-one shift of the first complex via the canonical bridge
-- `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`; then apply
-- `homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber` to the scalar endomorphisms
-- of `koszulComplex φ`.
/-- Lemma 15.28.10: if `φ'_f`, `φ'_g`, and `φ'_{fg}` are the linear forms on `E ⊕ R`, realized in
Lean as `E × R`, obtained from `φ` by adjoining multiplication by `f`, `g`, and `f * g` on the
`R`-summand, then the Koszul complex of `φ'_{fg}` is homotopy equivalent to the cone of a map
from the canonical degree-one shift
`((K(φ'_f).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
to `K(φ'_g)`. -/
theorem koszulComplex_coprod_scalar_mul_exists_homotopyEquiv_homotopyCofiber
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ α :
        (((koszulComplex (koszulCoprodScalarLinearMap φ f)).extend embeddingDownNat)⟦
          (-1 : ℤ)⟧).restriction embeddingDownNat ⟶
          koszulComplex (koszulCoprodScalarLinearMap φ g),
      Nonempty
        (HomotopyEquiv
          (koszulComplex (koszulCoprodScalarLinearMap φ (f * g)))
          (homotopyCofiber α)) := sorry

end

/-! ### Lemma_15_28_11 (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]

-- Proof sketch: specialize Lemma `15.28.10` to the family linear form `koszulLinearForm fs`,
-- then transport the three linear-map-level Koszul complexes to the family-level complexes on
-- `Fin.snoc fs f`, `Fin.snoc fs g`, and `Fin.snoc fs (f * g)`.
/-- Lemma 15.28.11: for a finite family `fs : Fin r → R`, the Koszul complex on
`Fin.snoc fs (f * g)` is homotopy equivalent to the cone of a map from the canonical degree-one
shift `(((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
of the Koszul complex on `Fin.snoc fs f` to the Koszul complex on `Fin.snoc fs g`. -/
theorem koszulComplexOn_snoc_mul_exists_homotopyEquiv_homotopyCofiber
    {r : ℕ} (fs : Fin r → R) (f g : R) :
    ∃ α :
        (((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction
            embeddingDownNat ⟶
        K^•(Fin.snoc fs g),
      Nonempty (HomotopyEquiv (K^•(Fin.snoc fs (f * g))) (homotopyCofiber α)) := sorry

/-! ### Lemma_15_28_12 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]
variable {E E' : Type u} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/- Domain-style sampling:
- primary domain: tensor-product comparisons for Koszul chain complexes;
- owner declarations inspected: `koszulComplex`, `koszulLinearForm`, `KoszulComplex.map`,
  `LinearEquiv.sumArrowLequivProdArrow`, `LinearEquiv.piCongrLeft`,
  `AlternatingMap.domCoprod`, and
  `HomologicalComplex.Hom.isoOfComponents`;
- best owner abstraction: the linear-map-level Koszul complex `koszulComplex`, with the
  finite-family bridge owned upstream by `koszulLinearForm`, `K^•(-)`, and the canonical
  function-space linear equivalences;
- primitive data: linear forms `φ : E →ₗ[R] R` and `ψ : E' →ₗ[R] R`;
- derived API: the `Fin.append` comparison for `K^•(-)`, obtained from the owner-level direct-sum
  comparison after transporting along the canonical tuple owner `koszulLinearForm` and the
  canonical tuple-index owner `finSumFinEquiv`;
- layer triage: `koszulComplex_coprod_iso_tensorObj` is the public `core/canonical` bridge, while
  `koszulComplexOn_append_iso_tensorObj` is the public `bridge/view` specialization matching the
  source family notation.
-/

-- Thin private linear bridge expressing `Fin.append` and its canonical splitting directly.
private noncomputable def finAppendLinearEquiv (r s : ℕ) :
    ((Fin r → R) × (Fin s → R)) ≃ₗ[R] (Fin (r + s) → R) :=
  { toFun := fun x ↦ Fin.append x.1 x.2
    invFun := fun x ↦ (fun i ↦ x (Fin.castAdd s i), fun i ↦ x (Fin.natAdd r i))
    map_add' := by
      intro x y
      ext i
      cases i using Fin.addCases <;> simp [Fin.append]
    map_smul' := by
      intro a x
      ext i
      cases i using Fin.addCases <;> simp [Fin.append]
    left_inv := by
      intro x
      ext i <;> simp [Fin.append_left, Fin.append_right]
    right_inv := by
      intro x
      ext i
      cases i using Fin.addCases <;> simp [Fin.append_left, Fin.append_right] }

@[simp] private theorem finAppendLinearEquiv_apply {r s : ℕ} (x : (Fin r → R) × (Fin s → R)) :
    finAppendLinearEquiv r s x = Fin.append x.1 x.2 :=
  rfl

@[simp] private theorem finAppendLinearEquiv_symm_apply {r s : ℕ} (x : Fin (r + s) → R) :
    (finAppendLinearEquiv r s).symm x = (fun i ↦ x (Fin.castAdd s i), fun i ↦ x (Fin.natAdd r i)) :=
  rfl

-- Proof sketch: the canonical linear equivalence from `((Fin r → R) × (Fin s → R))` to
-- `(Fin (r + s) → R)` identifies a pair of coefficient functions with the function on
-- `Fin (r + s)` obtained by `Fin.append`; evaluating `Module.piEquiv` on the concatenated family
-- then splits into the two summands defining `LinearMap.coprod`.
private theorem koszulLinearForm_append_comp_symm {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    ((koszulLinearForm f).coprod (koszulLinearForm g)).comp
        (finAppendLinearEquiv r s).symm.toLinearMap =
      koszulLinearForm (Fin.append f g) := by
  sorry

-- Proof sketch: compose the previous compatibility with the canonical linear equivalence from
-- `((Fin r → R) × (Fin s → R))` to `(Fin (r + s) → R)` and use that it is inverse to its own
-- inverse.
private theorem koszulLinearForm_append_comp {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    (koszulLinearForm (Fin.append f g)).comp (finAppendLinearEquiv r s).toLinearMap =
      (koszulLinearForm f).coprod (koszulLinearForm g) := by
  sorry

-- Proof sketch: identify the Koszul complex on the direct-sum linear form `φ.coprod ψ` with the
-- tensor product differential graded algebra generated by the two factors. On exterior powers,
-- this yields the standard totalized tensor-product differential, which is exactly `tensorObj` on
-- chain complexes in mathlib.
private noncomputable def koszulComplex_coprod_to_tensorObjSummand
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) (p : Fin (n + 1)) :
    _root_.AlternatingMap R (ModuleCat.of R (E × E'))
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n) (Fin n) :=
  let q : ℕ := n - p
  let hpq : (p : ℕ) + q = n := Nat.add_sub_of_le p.is_le
  let left : (E × E') [⋀^Fin p]→ₗ[R] ⋀[R]^p E :=
    (exteriorPower.ιMulti R p).compLinearMap (LinearMap.fst R E E')
  let right : (E × E') [⋀^Fin q]→ₗ[R] ⋀[R]^q E' :=
    (exteriorPower.ιMulti R q).compLinearMap (LinearMap.snd R E E')
  let alternating :
      _root_.AlternatingMap R (ModuleCat.of R (E × E'))
        ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) (Fin n) :=
    (left.domCoprod right).domDomCongr (finSumFinEquiv.trans (finCongr hpq))
  let ι :
      ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) ⟶
        (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n hpq
  ι.hom.compAlternatingMap alternating

private noncomputable def koszulComplex_coprod_to_tensorObjComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ⟶
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  ModuleCat.ofHom <|
    exteriorPower.alternatingMapLinearEquiv
      (∑ p : Fin (n + 1), koszulComplex_coprod_to_tensorObjSummand φ ψ n p)

private theorem koszulComplex_coprod_to_tensorObjComponent_commSq
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    CommSq
      (koszulComplex_coprod_to_tensorObjComponent φ ψ i)
      ((koszulComplex (φ.coprod ψ)).d i j)
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).d i j)
      (koszulComplex_coprod_to_tensorObjComponent φ ψ j) := by
  rcases i with _ | i
  · cases hij
  · obtain rfl : j = i := by
      simpa [ComplexShape.down] using hij
    exact ⟨by sorry⟩

private theorem isIso_koszulComplex_coprod_to_tensorObjComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    IsIso (koszulComplex_coprod_to_tensorObjComponent φ ψ n) := by
  sorry

private noncomputable def koszulComplex_coprod_tensorObjComponentIso
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ≅
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  let _ := isIso_koszulComplex_coprod_to_tensorObjComponent φ ψ n
  asIso (koszulComplex_coprod_to_tensorObjComponent φ ψ n)

/-- The Koszul complex of the coproduct linear form `φ.coprod ψ` is canonically isomorphic to the
tensor product of the Koszul complexes of `φ` and `ψ`. This is the owner-level comparison from
which tuple-indexed `Fin.append` specializations are obtained by transport along
`koszulLinearForm`. -/
noncomputable def koszulComplex_coprod_iso_tensorObj
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) :
    koszulComplex (φ.coprod ψ) ≅ koszulComplex φ ⊗ koszulComplex ψ :=
  Hom.isoOfComponents
    (koszulComplex_coprod_tensorObjComponentIso φ ψ)
    (fun i j hij ↦ (koszulComplex_coprod_to_tensorObjComponent_commSq φ ψ i j hij).w)

private def koszulComplexOn_append_iso_coprod {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    K^•(Fin.append f g) ≅
      koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g)) where
  hom := KoszulComplex.map (finAppendLinearEquiv r s).symm.toLinearMap
    (koszulLinearForm_append_comp_symm f g)
  inv := KoszulComplex.map (finAppendLinearEquiv r s).toLinearMap
    (koszulLinearForm_append_comp f g)
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-- Lemma 15.28.12: for finite families `f : Fin r → R` and `g : Fin s → R`, the Koszul complex
on the concatenated family `Fin.append f g` is isomorphic to the tensor product of the Koszul
complexes on `f` and `g`, written in Lean as `K^•(f) ⊗ K^•(g)`. -/
noncomputable def koszulComplexOn_append_iso_tensorObj {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    K^•(Fin.append f g) ≅ K^•(f) ⊗ K^•(g) :=
  by
    simpa using
      koszulComplexOn_append_iso_coprod f g ≪≫
        koszulComplex_coprod_iso_tensorObj (koszulLinearForm f) (koszulLinearForm g)

end
