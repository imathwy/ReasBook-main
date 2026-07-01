import Mathlib
import stacks_project.Chap17.Definition_17_4_1
import stacks_project.Chap17.Definition_17_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.17.11:
- primary domain: local factorization of two-step complexes of sheaves of modules on a ringed
  space with flat target, together with the matrix description of maps between finite free
  restrictions;
- sampled owner declarations:
  `SheafOfModules.flat_at`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMapLE`,
  `SheafOfModules.freeHomEquiv`;
- best owner abstraction: the core theorem should use the pointwise flatness owner
  `SheafOfModules.flat_at ℱ x` and the restriction-map owners, while the matrix theorem remains a
  source-facing bridge obtained by unwinding `SheafOfModules.freeHomEquiv`;
- primitive data: an open `U`, a point `x ∈ U`, morphisms `α` and `β` with `α ≫ β = 0`, and the
  flat stalk `ℱ_x`;
- derived API: the restricted complex on a neighbourhood `V` and the matrix-family reformulation.

Source/core/bridge triage:
- `source-facing`: the local finite-free factorization statement and its matrix form;
- `core/canonical`: `SheafOfModules.flat_at`, the restriction-map owners, and `freeHomEquiv`;
- `bridge/view`: the matrix-family translation of the factorization statement. -/

variable {X : RingedSpace.{u}} {ℱ : SheafOfModules (RingedSpace.ringCatSheaf X)}

-- Proof sketch: let `I ⊂ \mathcal O_U` be the image of the map
-- `\mathcal O_U \to \mathcal O_U^{\oplus n}`. The relation `\alpha ≫ \beta = 0` says exactly that
-- the induced map `I ⊗_{\mathcal O_U} \mathcal F|_U \to \mathcal F|_U` kills the corresponding
-- finite family of generators. Flatness of `\mathcal F_x` over `\mathcal O_{X, x}` lets one
-- shrink around `x` so that this tensor relation already vanishes on some neighbourhood `V`. Since
-- the source is finite free, this vanishing can be rewritten as a factorization of the restricted
-- map `\beta|_V` through another finite free module with zero composite from `\alpha|_V`.
/-- Lemma 17.17.11: if a two-step complex
`\mathcal O_U \xrightarrow{\alpha} \mathcal O_U^{\oplus n} \xrightarrow{\beta} \mathcal F|_U`
has stalkwise flat target at `x`, then near `x` the restricted map `\beta` factors through a
finite free module in such a way that the restricted `\alpha` maps to zero. -/
theorem exists_local_finite_free_factorization_of_complex_of_flat
    {U : Opens X} {I : Type u} [Finite I]
    (α : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} I : SheafOfModules _))
    (β : (SheafOfModules.free.{u} I : SheafOfModules _) ⟶ ℱ.over U)
    (hcomplex : α ≫ β = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (J : Type u) (_ : Finite J)
      (A :
        ((SheafOfModules.free.{u} I : SheafOfModules _).over
            (Over.mk (homOfLE hVU))) ⟶
          (SheafOfModules.free.{u} J : SheafOfModules _))
      (γ :
        (SheafOfModules.free.{u} J : SheafOfModules _) ⟶
          (ℱ.over U).over (Over.mk (homOfLE hVU))),
        moduleRestrictionMapLE hVU α ≫ A = 0 ∧
          A ≫ γ = moduleRestrictionMapLE hVU β := sorry

-- Proof sketch: apply the owner theorem to the morphisms corresponding under
-- `SheafOfModules.freeHomEquiv` to the families `(f_i)` and `(s_i)`. Unwinding those morphisms on
-- a shrunken neighbourhood gives the matrix coefficients `a_{ij}` and local sections `t_j`.
/-- Source-facing matrix form of Lemma 17.17.11: if families `f_i` and `s_i` define a complex
`\mathcal O_U \to \mathcal O_U^{\oplus n} \to \mathcal F|_U` with `\mathcal F_x` flat, then near
`x` the restricted family `s_i` factors through finitely many local sections `t_j` with matrix
coefficients annihilating the restricted `f_i`. -/
theorem exists_local_matrix_factorization_of_complex_of_flat
    {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (m : ℕ)
      (A : Fin n → Fin m → X.presheaf.obj (op V))
      (t : Fin m → ℱ.val.obj (op V)),
        (∀ i, ℱ.val.map (homOfLE hVU).op (s i) = ∑ j, A i j • t j) ∧
          ∀ j, ∑ i, X.presheaf.map (homOfLE hVU).op (f i) * A i j = 0 := sorry

end AlgebraicGeometry.RingedSpace
