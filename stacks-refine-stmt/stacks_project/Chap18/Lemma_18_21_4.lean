import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ)

/- Domain-style sampling for Lemma 18.21.4:
- primary domain: relocalization of localizations of a ringed topos, with the canonical slice-topos
  comparison on the underlying topoi and the induced comparison on localized structure sheaves;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.star`,
  `Over.pullback`,
  `Over.starPullbackIsoStar`,
  `sheafCompose`;
- best owner abstraction: the underlying relocalization comparison is already owned by the
  canonical slice base-change isomorphism `Over.starPullbackIsoStar`, and the ringed refinement is
  the specialization of that same owner to the forgotten structure sheaf;
- primitive data: a morphism of sheaves `s : 𝒢 ⟶ ℱ`;
- derived API: the localization inverse-image functors `Over.star ℱ`, `Over.star 𝒢`, the
  pullback functor `Over.pullback s`, and the induced comparison on localized structure sheaves
  after forgetting ring structure.

Source/core/bridge triage:
- `source-facing`: the commutative triangle of localization morphisms of ringed topoi attached to
  `s`, including compatibility of the structure-sheaf maps;
- `core/canonical`: `Over.starPullbackIsoStar`;
- `bridge/view`: the explicit source and target functors `Over.star ℱ ⋙ Over.pullback s` and
  `Over.star 𝒢`, and the specialization of their comparison to the forgotten structure sheaf.

Primitive data and derived API separate cleanly here: the owner only needs the sheaf map `s`,
while the ringed statement is obtained by applying that owner to the underlying structure sheaf.
This file should therefore reuse `Over.starPullbackIsoStar` directly as the main entry and expose
the structure-sheaf compatibility only as its thin derived companion.
-/
/- Lemma 18.21.4: for a morphism of sheaves `s : 𝒢 ⟶ ℱ` on a ringed topos
`(\mathit{Sh}(\mathcal C), \mathcal O)`, the natural commutative triangle of localization
morphisms of the underlying topoi is the canonical relocalization comparison
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. This is the topos-level part of the ringed-topos
diagram, and the ringed refinement is obtained by transporting the structure sheaf along this
localization square. -/
recall Over.starPullbackIsoStar

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type (max u v))} (s : 𝒢 ⟶ ℱ)
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Companion bridge: applying the canonical relocalization isomorphism to the forgotten
structure sheaf gives the comparison on localized structure sheaves. This is the underlying
sheaf-level content of the statement that `j_𝒢^♯` is obtained from `j_ℱ^♯` by relocalization. -/
#check
  ((Over.starPullbackIsoStar s).app
    ((sheafCompose J (forget RingCat.{max u v})).obj 𝒪))

/- Companion view: the morphism on the underlying sheaves of sets is the map appearing in the
commutative ringed-topos triangle. -/
#check
  (((Over.starPullbackIsoStar s).app
      ((sheafCompose J (forget RingCat.{max u v})).obj 𝒪)).hom.left)

end

end
