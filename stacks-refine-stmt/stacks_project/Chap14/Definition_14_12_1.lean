import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Definition 14.12.1:
- primary domain: truncated simplicial objects as presheaves on the truncated simplex category;
- sampled same-kind owner API:
  `SimplexCategory.Truncated`,
  `SimplicialObject.Truncated`,
  `SimplicialObject.Truncated.trunc`,
  `SSet.Truncated`;
- best owner abstraction:
  - `source-facing`: an `n`-truncated simplicial object of `C`;
  - `core/canonical`: the functor category `SimplicialObject.Truncated C n`;
  - `bridge/view`: derived specializations such as `SSet.Truncated n` and further truncation
    along `SimplicialObject.Truncated.trunc`;
- primitive data: none are introduced locally, because the source notion is already the canonical
  functor category `(SimplexCategory.Truncated n)ᵒᵖ ⥤ C`;
- derived API: morphisms as natural transformations, specialization to simplicial sets, and
  further truncation functors.

Source/core/bridge triage:
- `source-facing`: the textbook notion of an `n`-truncated simplicial object;
- `core/canonical`: mathlib's owner `SimplicialObject.Truncated`;
- `bridge/view`: downstream specializations and truncation functors built from that owner.

This numbered definition is therefore a direct canonical recall, not a place for a local wrapper
or duplicate abbreviation. -/

/- Definition 14.12.1: an `n`-truncated simplicial object of a category `𝒞` is a contravariant
functor from `Δ_{≤ n}` to `𝒞`; morphisms are natural transformations. This is the canonical
functor category `SimplicialObject.Truncated C n`. -/
recall SimplicialObject.Truncated
