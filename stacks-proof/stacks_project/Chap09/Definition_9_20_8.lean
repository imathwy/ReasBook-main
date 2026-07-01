import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Discriminant

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Module

/- Domain-style sampling for Definition 9.20.8:
- primary domain: discriminants of finite field extensions, represented by basis discriminants of
  the trace pairing and then reduced modulo squares;
- sampled owner declarations:
  `Algebra.discr`,
  `Algebra.discr_reindex`,
  `Algebra.discr_of_matrix_vecMul`,
  `Algebra.traceForm`,
  `MulAction.orbitRel.Quotient`;
- best owner abstraction:
  - `source-facing`: the discriminant class of the finite extension `L/K` in `K / (Kˣ)^2`;
  - `core/canonical`: `Algebra.discr K b` as the basis discriminant of the extension, together
    with the quotient `MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K`;
  - `bridge/view`: the basis-independence theorem for the square class of `Algebra.discr K b`,
    yielding `fieldExtensionDiscriminant_eq`;
- primitive data: the canonical square-class quotient and the basis discriminant
  `Algebra.discr K b`;
- derived API: the basis-independence theorem `fieldExtensionDiscriminant_eq`.

Source/core/bridge triage:
- `source-facing`: `fieldExtensionDiscriminant`, the discriminant class of the finite extension
  `L/K`;
- `core/canonical`: `Algebra.discr` for basis representatives and
  `MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K` for square classes;
- `bridge/view`: `fieldExtensionDiscriminant_eq`, identifying the source-facing class with any
  basis representative `Algebra.discr K b`.
-/

variable (K : Type u) [Field K]

/-- Field elements modulo multiplication by a square of a unit. -/
abbrev SquareClass := MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K

namespace SquareClass

/-- The square class of a field element. -/
abbrev mk (a : K) : SquareClass K := Quotient.mk'' a

theorem mk_eq_mk_iff {a b : K} :
    mk K a = mk K b ↔ ∃ u : Kˣ, a = ↑(u ^ (2 : ℕ)) * b :=
    by
  change (Quotient.mk'' a : Quotient (MulAction.orbitRel (Subgroup.square Kˣ) K)) =
      Quotient.mk'' b ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rcases (Subgroup.mem_square.mp u.2) with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      a = u • b := hu.symm
      _ = ((u : Subgroup.square Kˣ) : Kˣ) • b := by rw [MulAction.subgroup_smul_def]
      _ = (((u : Subgroup.square Kˣ) : Kˣ) : K) * b := by simp [Units.smul_def]
      _ = ↑(v ^ (2 : ℕ)) * b := by rw [hv, pow_two]
  · rintro ⟨u, hu⟩
    refine ⟨⟨u ^ (2 : ℕ), Subgroup.mem_square.mpr ⟨u, by simp [pow_two]⟩⟩, ?_⟩
    simpa [MulAction.subgroup_smul_def, Units.smul_def] using hu.symm

end SquareClass

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

private theorem squareClass_eq_of_basis_discr {ι : Type w} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (b : Basis ι K L) (b' : Basis ι' K L) :
    SquareClass.mk K (Algebra.discr K b) = SquareClass.mk K (Algebra.discr K b') := by
  let e : ι ≃ ι' := b.indexEquiv b'
  let b₀ : Basis ι K L := b'.reindex e.symm
  have hdet : IsUnit (b₀.toMatrix b).det := by
    letI := Basis.invertibleToMatrix b₀ b
    exact Matrix.isUnit_det_of_invertible (b₀.toMatrix b)
  rw [SquareClass.mk_eq_mk_iff]
  refine ⟨hdet.unit, ?_⟩
  calc
    Algebra.discr K b = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
      calc
        Algebra.discr K b =
            Algebra.discr K (Matrix.vecMul b₀ ((b₀.toMatrix b).map (algebraMap K L))) := by
              rw [b₀.toMatrix_map_vecMul b]
        _ = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
              simpa using Algebra.discr_of_matrix_vecMul b₀ (b₀.toMatrix b)
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b₀ := by simp
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b' := by
      congr 1
      simpa [b₀, Basis.coe_reindex] using
        (@Algebra.discr_reindex K L ι' _ _ _ _ ι _ _ _ b' e.symm)

section FiniteDimensional

variable [FiniteDimensional K L]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Definition 9.20.8: the discriminant of the finite field extension `L/K` is the square class of
the discriminant of the trace pairing `Q_{L/K}`, i.e. the class of any basis representative
`Algebra.discr K b` in `K / (Kˣ)^2`. -/
noncomputable def fieldExtensionDiscriminant (K : Type u) [Field K] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] : SquareClass K :=
  SquareClass.mk K (Algebra.discr K (Module.finBasis K L))

/-- Any basis representative computes the discriminant class of `L/K`. -/
theorem fieldExtensionDiscriminant_eq (b : Basis ι K L) :
    fieldExtensionDiscriminant K L = SquareClass.mk K (Algebra.discr K b) := by
  simpa [fieldExtensionDiscriminant] using
    squareClass_eq_of_basis_discr (Module.finBasis K L) b

end FiniteDimensional
