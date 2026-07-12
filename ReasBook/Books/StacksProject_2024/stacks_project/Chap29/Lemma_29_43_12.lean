import Mathlib.AlgebraicGeometry.OpenImmersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`lean_leansearch` recalled the canonical scheme-morphism owner `IsOpenImmersion`. Nearby Chapter
29 files provide the source-facing morphism-property owners `QuasiProjective` and `Projective`,
and local precedent represents the quasi-compact quasi-separated base hypotheses as
`[CompactSpace S] [QuasiSeparatedSpace S]`.

The current read-only item environment cannot import `Definition_29_40_1` or
`Definition_29_43_1`: their relative-ampleness/projective-bundle owner path rebuilds
`Definition_29_37_1`, whose `.olean` is unavailable and whose source does not elaborate in this
target-file check. This file therefore records the source lemma as a labeled recall block and
checks the dependency-closed factorization, open-immersion, and quasi-compact quasi-separated base
surfaces instead of introducing fake replacements for `QuasiProjective` or `Projective`. The
Stacks tag evidence is consistent: item tag `07RM` matches the source URL `/tag/07RM`. -/

/- Lemma 29.43.12 (Stacks tag `07RM`): if `f : X ⟶ S` is quasi-projective and `S` is
quasi-compact and quasi-separated, then `f` factors as an open immersion followed by a projective
morphism.

When `Definition_29_40_1` and `Definition_29_43_1` are dependency-closed, the intended
source-facing statement is:
`theorem QuasiProjective.exists_factor_openImmersion_projective
  {X S : Scheme} {f : X ⟶ S} [CompactSpace S] [QuasiSeparatedSpace S]
  (hf : QuasiProjective f) :
  ∃ (X' : Scheme) (i : X ⟶ X') (g : X' ⟶ S)
    (_ : IsOpenImmersion i) (_ : Projective g), i ≫ g = f`.
-/
#check fun {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] ↦ f
#check fun {X X' S : Scheme.{u}} (i : X ⟶ X') (g : X' ⟶ S) ↦ i ≫ g
#check fun {X X' : Scheme.{u}} (i : X ⟶ X') ↦ IsOpenImmersion i
#check fun {S : Scheme.{u}} ↦ CompactSpace S
#check fun {S : Scheme.{u}} ↦ QuasiSeparatedSpace S

end AlgebraicGeometry
