import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR
local notation "singleComplex₀" => CochainComplex.singleFunctor ModR (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.12:
- primary domain: two-term cochain complexes in `ModuleCat R`, presented as mapping cones of
  matrices and, more canonically, of endomorphisms of finite free modules, and their derived
  images;
- sampled owner declarations of the same kind:
  `Matrix.toLin'`,
  `LinearMap.det_toLin'`,
  `CochainComplex.mappingCone`,
  `CochainComplex.singleFunctor`,
  `LinearMap.det`;
- best owner abstraction: the canonical owner for the two-term complex attached to an
  endomorphism `f` of a finite free module is
  `CochainComplex.mappingCone ((CochainComplex.singleFunctor ModR 0).map (ModuleCat.ofHom f))`,
  while the source-facing statement remains the matrix presentation `R^n \xrightarrow{A} R^n`;
- primitive data: for the source-facing lemma, a matrix `A : Matrix (Fin n) (Fin n) R` and a
  chosen representation isomorphism from the derived image of the corresponding two-term complex
  to `K`;
- derived API: the supporting finite-free endomorphism bridge theorem over the canonical
  mapping-cone owner.

Source/core/bridge triage:
- `source-facing`: the textbook matrix statement that an arbitrary `K` represented by
  `R^n \xrightarrow{A} R^n` is annihilated by `det A`;
- `core/canonical`: `CochainComplex.mappingCone` of the map induced by `f` on the degree-zero
  single complex;
- `bridge/view`: the finite-free endomorphism version together with the matrix comparison
  `A.toLin'` and `LinearMap.det_toLin'`.

Accordingly, this file keeps the matrix formulation as the main numbered source-facing theorem,
and exposes the finite-free endomorphism statement only as a supporting bridge over the canonical
mapping-cone owner. -/

/-- Matrix specialization of Lemma 15.85.12: if `K` is represented by the two-term complex
`R^n \xrightarrow{A} R^n`, then multiplication by `det A` acts by zero on `K` in `D(R)`. -/
theorem matrixTwoTermDerived_det_endomorphism_eq_zero {n : ℕ}
    (K : DModR) (A : Matrix (Fin n) (Fin n) R)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom A.toLin')))) K) :
    Matrix.det A • 𝟙 K = 0 := sorry

-- Proof sketch: choose a basis of the finite free module `M`, represent `f` by a matrix `A`, and
-- apply the source-facing matrix lemma above to that presentation. The determinant comparison
-- `LinearMap.det_toLin'` identifies the resulting scalar action with multiplication by
-- `LinearMap.det f`.
/-- Supporting bridge: if `K` is represented by the two-term complex `M \xrightarrow{f} M` in
degrees `-1` and `0`, where `M` is finite free over `R`, then multiplication by `det(f)` acts by
zero on `K` in `D(R)`. -/
theorem endomorphismTwoTermDerived_det_endomorphism_eq_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (K : DModR) (f : M →ₗ[R] M)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom f)))) K) :
    LinearMap.det f • 𝟙 K = 0 := sorry

end

end CategoryTheory
