import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.3 states that when the linear transformation `A` is nonsingular, the
  textbook image operation `Ah` reduces to ordinary composition with the inverse map.
- `core/canonical`: the owner theorem is the chapter declaration
  `Function.linearImage_eq_comp_symm`, attached directly to `Function.linearImage`.
- `bridge/view`: nonsingularity is represented canonically by a `LinearEquiv`, and the textbook
  term `hA^{-1}` is the composite `h ∘ A.symm`.
- Primitive data vs derived API: the primitive objects are the invertible linear map `A` and the
  function `h`; the displayed equality is derived owner-level API and should be reused directly
  rather than reproved in coordinates.

Domain-style sampling used here:
- `Function.linearImage`;
- `Function.linearImage_eq_sInf_image`;
- `Function.linearImage_eq_comp_symm`;
- `LinearEquiv.apply_eq_iff_eq_symm_apply`.
- Ambient minimization: the owner theorem already lives on arbitrary modules through the
  `LinearEquiv` interface and works for any conditionally complete lattice codomain of `h`.
- Abstraction checks:
  - codomain/ambient layer: already at the canonical conditionally-complete-lattice layer;
  - scalar/space structure: no extra concrete structure beyond module data;
  - owner choice: direct reuse of `Function.linearImage_eq_comp_symm` as the canonical owner;
  - topology language: not applicable for this algebraic item;
  - notation surface: reuse the existing chapter notation/owner layer without local wrappers.
- Layer target: `core/canonical`; Text 5.7.3 is an exact owner-level identity already provided by
  the chapter theorem `Function.linearImage_eq_comp_symm`, so the main entry should stay a direct
  `recall` rather than a duplicate local theorem.
-/

/- Text 5.7.3: for an invertible linear map `A`, the textbook image operation `Ah` coincides
with composition by the inverse map, i.e. `Ah = hA^{-1}`; the owner theorem is already codomain-
generic at the conditionally-complete-lattice level. -/
recall Function.linearImage_eq_comp_symm
