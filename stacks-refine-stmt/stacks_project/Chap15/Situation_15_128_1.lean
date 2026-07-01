import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.JacobsonSpace

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: commutative algebra of fibres of modules at closed points of `Spec R`;
- inspected owner-style declarations:
  `Ideal.Fiber`,
  `closedPoints`,
  `PrimeSpectrum.isClosed_singleton_iff_isMaximal`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `Ideal.bijective_algebraMap_quotient_residueField`,
  `Lemma_10_39_15.nontrivial_tensor_residueField_iff_nontrivial_quotSMul`;
- owner abstraction: for modules, the canonical owner is the left-tensor fibre
  `κ(x) ⊗[R] M`, which is the mathlib-native base-change module carrying the residue-field scalar
  structure directly; the ring owner `Ideal.Fiber` itself was inspected and rejected here because
  it lives at the ring fibre level rather than the module fibre level. The source-facing quotient
  fibre `M(x) = M / xM` is retained as the textbook surface;
- layer: `source-facing` for `M(x)` and the image map `s ↦ s(x)`, `core/canonical` for the tensor
  model `κ(x) ⊗[R] M`, `bridge/view` for the tensor/quotient identification
  `κ(x) ⊗[R] M ≃ M(x)`;
- primitive data: only the closed point `x`;
- derived API: maximality of `x.1.asIdeal`, the residue-field scalar structure on `M(x)`, and the
  internal tensor/quotient bridge used to prove finite-dimensionality.
-/

local notation "Ω" => closedPoints (PrimeSpectrum R)

set_option quotPrecheck false in
scoped[ClosedPointFiber] notation:max "κ(" x:max ")" =>
  Ideal.ResidueField ((x).1.asIdeal)

/-- Situation 15.128.1: for a closed point `x ∈ Ω = closedPoints (PrimeSpectrum R)`, the fibre
`M(x)` of an `R`-module `M` is the quotient `M / xM`. -/
abbrev closedPointFiber (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) : Type v :=
  N ⧸ x.1.asIdeal • (⊤ : Submodule R N)

scoped[ClosedPointFiber] notation:max N:max "﹙" x:max "﹚" =>
  closedPointFiber N x

open scoped ClosedPointFiber

instance (x : Ω) : x.1.asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.1).1 x.2

/-- For a closed point `x`, the quotient ring `R / x` is canonically the residue field `κ(x)`. -/
noncomputable abbrev closedPointFiberResidueFieldAlgEquiv (x : Ω) :
    (R ⧸ x.1.asIdeal) ≃ₐ[R] κ(x) :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ x.1.asIdeal) κ(x))
    (Ideal.bijective_algebraMap_quotient_residueField x.1.asIdeal)

/-- The quotient fibre `N(x)`, written in Lean as `N﹙x﹚`, is canonically a `κ(x)`-vector
space. -/
noncomputable instance closedPointFiber.module
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) :
    Module κ(x) (N﹙x﹚) :=
  let _ : Module (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
    inferInstanceAs (Module (R ⧸ x.1.asIdeal) (N ⧸ x.1.asIdeal • (⊤ : Submodule R N)))
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  Module.compHom _ eκ.symm.toRingHom

noncomputable instance closedPointFiber.isScalarTower
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) :
    IsScalarTower R κ(x) (N﹙x﹚) :=
  let _ : Module (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
    inferInstanceAs (Module (R ⧸ x.1.asIdeal) (N ⧸ x.1.asIdeal • (⊤ : Submodule R N)))
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  let _ : Module κ(x) (N﹙x﹚) :=
    Module.compHom _ eκ.symm.toRingHom
  IsScalarTower.of_algebraMap_smul fun r y ↦ by
    change eκ.symm (algebraMap R κ(x) r) • y = r • y
    rw [← eκ.commutes r]
    simpa using (show (algebraMap R (R ⧸ x.1.asIdeal) r) • y = r • y by rfl)

/-- Internal bridge from the source-facing quotient fibre to the canonical left-tensor fibre
model. -/
private noncomputable def closedPointFiberTensorEquiv
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) :
    κ(x) ⊗[R] N ≃ₗ[κ(x)] N﹙x﹚ :=
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  ((TensorProduct.congr eκ.symm.toLinearEquiv (LinearEquiv.refl R N)) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul N x.1.asIdeal).extendScalarsOfSurjective
    x.1.asIdeal.algebraMap_residueField_surjective

/-- The image of a section in the quotient fibre over a closed point. -/
private abbrev closedPointFiberMk (x : Ω) (s : M) : M﹙x﹚ :=
  Submodule.Quotient.mk s

/-- The image `s(x)` of a section `s : M` in the quotient fibre `M(x) = M / xM`. -/
scoped[ClosedPointFiber] notation:max s:max "⟮" x:max "⟯" =>
  closedPointFiberMk x s

open scoped ClosedPointFiber

private noncomputable def closedPointFiberLinearFormQuotient
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) (φ : Module.Dual R N) :
    Module.Dual (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
  let f : N﹙x﹚ →ₗ[R] (R ⧸ x.1.asIdeal) :=
    ((x.1.asIdeal) • (⊤ : Submodule R N)).liftQ
      (((Ideal.Quotient.mkₐ R x.1.asIdeal).toLinearMap).comp φ) <| by
        intro m hm
        change (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ m) = 0
        refine Submodule.smul_induction_on hm ?_ ?_
        · intro r hr n hn
          simpa [Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul] using
            (Ideal.Quotient.eq_zero_iff_mem.2 <| x.1.asIdeal.mul_mem_right (φ n) hr :
              Ideal.Quotient.mk x.1.asIdeal (r * φ n) = 0)
        · intro a b ha hb
          calc
            (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ (a + b)) =
                (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ a) +
                  (Ideal.Quotient.mkₐ R x.1.asIdeal) (φ b) := by
                  rw [map_add, map_add]
            _ = 0 := by rw [ha, hb, add_zero]
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro c q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine Quotient.inductionOn' q ?_
      intro m
      have hmk :
          Ideal.Quotient.mk x.1.asIdeal r •
              (Submodule.Quotient.mk m : N﹙x﹚) =
            (Submodule.Quotient.mk (r • m) : N﹙x﹚) :=
        (Module.Quotient.mk_smul_mk N x.1.asIdeal r m :
          Ideal.Quotient.mk x.1.asIdeal r •
              (Submodule.Quotient.mk m : N ⧸ x.1.asIdeal • (⊤ : Submodule R N)) =
            (Submodule.Quotient.mk (r • m) : N ⧸ x.1.asIdeal • (⊤ : Submodule R N)))
      simpa [f, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using congrArg f hmk }

private noncomputable def closedPointFiberLinearForm
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) (φ : Module.Dual R N) :
    Module.Dual (κ(x)) (N﹙x﹚) :=
  let eκ := closedPointFiberResidueFieldAlgEquiv (R := R) x
  let ψ := closedPointFiberLinearFormQuotient N x φ
  { toFun := fun m ↦ eκ (ψ m)
    map_add' := by
      intro a b
      simp
    map_smul' := by
      intro c m
      change eκ (ψ ((eκ.symm c) • m)) = c • eκ (ψ m)
      rw [ψ.map_smul]
      change eκ (eκ.symm c * ψ m) = c • eκ (ψ m)
      rw [map_mul, eκ.apply_symm_apply]
      simp }

/-- The invisible part `B(x)` of the fibre `N(x)`, defined as the common kernel of the linear
forms on `N(x)` induced by `Hom_R(N, R)`. -/
noncomputable abbrev closedPointFiberInvisibleSubspace
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) :
    Submodule (κ(x)) (N﹙x﹚) :=
  (Submodule.span (κ(x)) (Set.range (closedPointFiberLinearForm N x))).dualCoannihilator

scoped[ClosedPointFiber] notation:max "B(" x:max ")" =>
  closedPointFiberInvisibleSubspace _ x

/-- The visible quotient `V(x) = N(x) / B(x)`. -/
noncomputable abbrev closedPointFiberVisibleQuotient
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) : Type v :=
  N﹙x﹚ ⧸ closedPointFiberInvisibleSubspace N x

scoped[ClosedPointFiber] notation:max "V(" x:max ")" =>
  closedPointFiberVisibleQuotient _ x

/-- The class in `V(x)` of the fibre image `s(x) ∈ N(x)`. -/
noncomputable abbrev closedPointFiberVisibleClass
    {N : Type v} [AddCommGroup N] [Module R N] (x : Ω) (s : N) :
    closedPointFiberVisibleQuotient N x :=
  (closedPointFiberInvisibleSubspace N x).mkQ (s⟮x⟯)

/-- Every visible class at a closed point is represented by a global section. -/
theorem closedPointFiberVisibleClass_surjective
    (N : Type v) [AddCommGroup N] [Module R N] (x : Ω) :
    Function.Surjective
      (closedPointFiberVisibleClass x : N → closedPointFiberVisibleQuotient N x) := by
  intro v
  obtain ⟨mbar, hmbar⟩ := (B(x)).mkQ_surjective v
  obtain ⟨m, rfl⟩ :=
    Submodule.mkQ_surjective (x.1.asIdeal • (⊤ : Submodule R N)) mbar
  exact ⟨m, hmbar⟩

section

variable [Module.Finite R M]

/-- The fibre `M(x)` at a closed point is finite-dimensional over its residue field `κ(x)`. -/
-- Proof sketch: a finite `R`-module stays finite after tensoring with the residue field, and the
-- quotient-residue-field identification with `R / x`
-- identifies `M(x)` with the canonical tensor model `κ(x) ⊗[R] M`, which is finite-dimensional
-- over `κ(x)`.
theorem closedPointFiber_finiteDimensional (x : Ω) :
    FiniteDimensional κ(x) (M﹙x﹚) := by
  let _ : FiniteDimensional κ(x) (κ(x) ⊗[R] M) :=
    inferInstance
  exact (closedPointFiberTensorEquiv M x).finiteDimensional

end

end
