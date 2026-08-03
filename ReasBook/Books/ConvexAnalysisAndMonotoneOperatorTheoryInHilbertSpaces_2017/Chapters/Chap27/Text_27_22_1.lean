import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

noncomputable section

-- The later Chapter 27 results use the canonical objective
-- `f + ε • g` directly, so this item stays recall-only rather than
-- introducing an extra wrapper name.

section Regularization

variable {H : Type u}

/- Source/core/bridge triage:
- `source-facing`: Text 27.22.1 is a setup sentence. Under the standing assumptions
  `f, g ∈ Γ₀(H)` and `(Argmin f.asEReal).Nonempty`, each positive parameter `ε` gives the
  regularized problem with objective `f + ε g`.
- `core/canonical`: the project already uses the canonical pointwise owner
  `Argmin (f + ε • g).asEReal` directly.
- `bridge/view`: this file is therefore recall-only; the later existence/uniqueness and
  convergence clauses are formalized in `Theorem_27_23`.

Primitive data: the recalled owner only depends on `f`, `g`, and the positive parameter `ε`.
Derived Chapter 27 context: the hypotheses `f ∈ Γ₀(H)`, `g ∈ Γ₀(H)`,
`(Argmin f.asEReal).Nonempty`, and the Hilbert-space assumptions used later in
`Theorem_27_23` do not belong to the owner surface of the regularized argmin object itself.
The textbook side condition `ε < 1` is likewise deferred to the later convergence statements,
where it is mathematically used. -/

-- Semantic recall note: `lean_leansearch` only surfaced generic minimization APIs here.
-- The verified local owner for this setup is `Argmin` applied to the canonical pointwise sum
-- `f + ε • g`.

section

variable {f g : H → Set.Ioi (⊥ : EReal)}
variable (ε : PosReal)

/- Text 27.22.1: let `f ∈ Γ₀(H)` with `(Argmin f.asEReal).Nonempty`, let `g ∈ Γ₀(H)`, and let
`ε > 0`. The regularized problem is to minimize `(f + ε • g).asEReal`. The later Chapter 27
convergence statements impose the additional restriction `ε < 1` where needed. -/
#check Argmin (f + ε • g).asEReal

end

end Regularization

end

end ERealFunction
