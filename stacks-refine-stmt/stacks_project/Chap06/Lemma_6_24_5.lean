import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat

universe w v u

/- Domain-style sampling for Lemma 6.24.5:
- primary domain: direct image of sheaves of modules along a continuous map of topological spaces;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardId`,
  `TopCat.Sheaf.pushforward`,
  `PresheafOfModules.pushforward`;
- owner abstraction: the canonical owner is `SheafOfModules.pushforward`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `X`, and a sheaf of
  `𝒪`-modules `ℱ`;
- derived API: the specialized object `f_* ℱ` over the direct-image ring sheaf `f_* 𝒪`.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that direct image carries an `𝒪`-module sheaf on `X`
  to an `f_* 𝒪`-module sheaf on `Y`;
- `core/canonical`: `SheafOfModules.pushforward`;
- `bridge/view`: the identity-morphism specialization over the direct-image ring sheaf
  `(Sheaf.pushforward RingCat f).obj 𝒪`.

This item is only the object-level specialization of the canonical owner, so the refined file
should keep a direct `#check` of that specialization rather than introduce a local alias. -/

section

variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} X)
variable (ℱ : SheafOfModules.{v} 𝒪)

/- Lemma 6.24.5: for a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `X`, and a sheaf
of `𝒪`-modules `ℱ`, the direct image `f_* ℱ` is canonically a sheaf of modules over the direct
image ring sheaf `f_* 𝒪`. In mathlib this is the specialization of
`SheafOfModules.pushforward` to the identity morphism on `(Sheaf.pushforward RingCat f).obj 𝒪`. -/
recall SheafOfModules.pushforward

#check (SheafOfModules.pushforward (𝟙 ((Sheaf.pushforward RingCat f).obj 𝒪))).obj ℱ

end
