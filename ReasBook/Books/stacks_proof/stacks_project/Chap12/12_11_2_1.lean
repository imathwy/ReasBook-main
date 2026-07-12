import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {M : C} {φ ψ : M ⟶ M}

private theorem cyclicCochainComplex_sq
    (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) (i : ZMod 2) :
    (if i = 0 then φ else ψ) ≫ (if i + 1 = 0 then φ else ψ) = 0 := by
  fin_cases i
  · simpa using hφψ
  · simpa using hψφ

/- Domain-style sampling for 12.11.2.1:
- primary domain: `ZMod 2`-indexed cochain complexes in a category with zero morphisms;
- inspected owner declarations:
  `CochainComplex.of`,
  `CochainComplex.of_d`,
  `CochainComplex.ofHom`,
  `HomologicalComplex.d_comp_d`.
- owner abstraction: `CochainComplex.of`;
- primitive data: the object `M`, the two endomorphisms `φ, ψ`, and the square-zero relations
  `φ ≫ ψ = 0`, `ψ ≫ φ = 0`;
- derived API: the resulting `ZMod 2`-indexed cochain complex, its constant degree object, and
  the explicit degree-`0` / degree-`1` differential formulas coming from `CochainComplex.of`.

Source/core/bridge triage:
- `source-facing`: the cyclic cochain complex with constant object `M` and alternating
  differentials `φ, ψ`;
- `core/canonical`: `CochainComplex.of`;
- `bridge/view`: the specialization of `CochainComplex.of` to the constant object family
  `fun _ ↦ M` and the differential family `fun i ↦ if i = 0 then φ else ψ`.
-/

/-- 12.11.2.1: the `ZMod 2`-indexed cyclic cochain complex with constant object `M` and
alternating differentials `φ, ψ`. -/
@[stacks 02MW]
abbrev cyclicCochainComplex (φ ψ : M ⟶ M)
    (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    CochainComplex C (ZMod 2) :=
  CochainComplex.of
    (fun _ ↦ M)
    (fun i ↦ if i = 0 then φ else ψ)
    (cyclicCochainComplex_sq hφψ hψφ)

@[simp] theorem cyclicCochainComplex_X
    (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) (i : ZMod 2) :
    (cyclicCochainComplex φ ψ hφψ hψφ).X i = M :=
  rfl

@[simp] theorem cyclicCochainComplex_d_zero
    (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    (cyclicCochainComplex φ ψ hφψ hψφ).d 0 1 = φ := by
  simpa only [zero_add, if_pos rfl, cyclicCochainComplex] using
    (CochainComplex.of_d
      (fun _ : ZMod 2 ↦ M)
      (fun i ↦ if i = 0 then φ else ψ)
      (cyclicCochainComplex_sq hφψ hψφ)
      (0 : ZMod 2))

@[simp] theorem cyclicCochainComplex_d_one
    (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    (cyclicCochainComplex φ ψ hφψ hψφ).d 1 0 = ψ := by
  simpa only [show ((1 : ZMod 2) + 1) = 0 by decide, if_neg (by decide : (1 : ZMod 2) ≠ 0),
    if_pos rfl, cyclicCochainComplex] using
    (CochainComplex.of_d
      (fun _ : ZMod 2 ↦ M)
      (fun i ↦ if i = 0 then φ else ψ)
      (cyclicCochainComplex_sq hφψ hψφ)
      (1 : ZMod 2))

end

end CategoryTheory
