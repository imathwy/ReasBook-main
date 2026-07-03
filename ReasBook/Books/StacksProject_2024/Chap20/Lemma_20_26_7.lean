import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap18.Lemma_18_28_9
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.RingedSpace

noncomputable section

/- Domain-style sampling for Lemma 20.26.7:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules in a short exact sequence of
  complexes on a ringed space;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃`;
- best owner abstraction: the primitive owner data are a short complex
  `S : ShortComplex (CochainComplex (RingedSpace.Modules X) ℤ)` together with `hS : S.ShortExact`;
  the three K-flatness conclusions are derived API attached to that owner, not separate ringed
  space wrapper data;
- primitive vs derived: primitive data are only `S`, `hS`, and the termwise flatness hypothesis on
  `S.X₃`; the conclusions that `S.X₁`, `S.X₂`, or `S.X₃` are K-flat are derived theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the short-exact two-out-of-three K-flatness
  statements from the Stacks Project;
- `core/canonical`: `CochainComplex.IsKFlat` and the short-exact owner
  `CategoryTheory.ShortComplex.ShortExact`;
- `bridge/view`: the earlier tensor-exactness theorem
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`, which supplies the
  short-exact tensor sequence used in the proof sketch. -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable {S : ShortComplex (CochainComplex (RingedSpace.Modules X) ℤ)}

-- Proof sketch: tensor the given short exact sequence with an arbitrary acyclic complex. Since the
-- terms of `S.X₃` are flat, the canonical tensor-right owner theorem
-- `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient` preserves short exactness
-- after tensoring termwise. If
-- `S.X₁` and `S.X₂` are K-flat, the first two tensor complexes are acyclic, so the third is
-- acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 20.26.7 (1): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_2^\bullet` are K-flat, then `\mathcal K_3^\bullet` is K-flat. -/
theorem isKFlat_X₃_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: after tensoring with an arbitrary acyclic complex, the canonical tensor-right
-- owner theorem `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient` again gives
-- a short exact sequence of tensor complexes because the terms of `S.X₃` are flat. If `S.X₁` and
-- `S.X₃` are K-flat, the outer tensor complexes are acyclic, so the middle one is acyclic by the
-- associated long exact sequence on cohomology sheaves.
/-- Lemma 20.26.7 (2): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_2^\bullet` is K-flat. -/
theorem isKFlat_X₂_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence with an arbitrary acyclic complex and use the
-- flatness of the terms of `S.X₃` to keep the tensor sequence short exact by
-- `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`. If
-- `S.X₂` and `S.X₃` are K-flat, then the last two tensor complexes are acyclic, and the first is
-- acyclic by the resulting long exact sequence of cohomology sheaves.
/-- Lemma 20.26.7 (3): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_2^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_1^\bullet` is K-flat. -/
theorem isKFlat_X₁_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact
