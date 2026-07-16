import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import stacks_proof.stacks_project.Chap15.Lemma_15_59_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

section

variable {R : Type u} [CommRing R]

local notation "KHom" => HomotopyCategory (ModuleCat R) (up ℤ)

/-
Domain-style sampling for Lemma 15.60.5:
- primary domain: K-flat objects in the homotopy category `K(R)` of cochain complexes of
  `R`-modules and their behavior in distinguished triangles;
- sampled owner declarations:
  `HomotopyCategory.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the owner layer is already the object property `K ↦ K.IsKFlat` on
  `K(R)`, with the three two-out-of-three distinguished-triangle consequences packaged by the
  canonical theorems above;
- primitive vs. derived:
  primitive data are only a distinguished triangle `T` in `K(R)` and K-flatness hypotheses on two
  of its vertices;
  the three closure implications are derived API from the existing owner theorems, so this file
  should specialize those directly instead of keeping a parallel local theorem family.

Source/core/bridge triage:
- `source-facing`: the three K-flat two-out-of-three implications for distinguished triangles in
  `K(R)`;
- `core/canonical`: `HomotopyCategory.IsKFlat` and the owner theorems
  `isKFlat_obj₃_of_distinguished_triangle`, `isKFlat_obj₂_of_distinguished_triangle`,
  `isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: the `ModuleCat R` specialization of those canonical `K(C)` owner theorems to the
  source-local homotopy category `K(R)`.
-/

/- Lemma 15.60.5 (1): if `T` is a distinguished triangle in `K(R)` and the first two terms are
K-flat, then the third term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₃_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₁.IsKFlat → T.obj₂.IsKFlat →
      T.obj₃.IsKFlat)

/- Lemma 15.60.5 (2): if `T` is a distinguished triangle in `K(R)` and the first and third terms
are K-flat, then the second term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₂_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₁.IsKFlat → T.obj₃.IsKFlat →
      T.obj₂.IsKFlat)

/- Lemma 15.60.5 (3): if `T` is a distinguished triangle in `K(R)` and the second and third terms
are K-flat, then the first term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₁_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₂.IsKFlat → T.obj₃.IsKFlat →
      T.obj₁.IsKFlat)

end

end CochainComplex
