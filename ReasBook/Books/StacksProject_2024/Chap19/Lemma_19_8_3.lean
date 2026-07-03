import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 19.8.3:
- primary domain: functorial injective embeddings in categories of sheaves of modules;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings`,
  `HasFunctorialInjectiveEmbeddings.under`,
  `HasFunctorialInjectiveEmbeddings.under_injective`,
  the bridge instance `EnoughInjectives` induced from functorial injective embeddings;
- best owner abstraction: `HasFunctorialInjectiveEmbeddings` is the source-facing owner, and
  `under_injective` is already its canonical derived API for the chosen injective target.

This item is therefore a `bridge/view` recall of an existing owner-level declaration, not a new
source-facing theorem. -/

/- Lemma 19.8.3: for every `\mathcal O`-module sheaf `\mathcal F`, the chosen object
`J(\mathcal F)` in a functorial injective embedding of `\operatorname{Mod}(\mathcal O)` is
injective. This is exactly the owner-level instance
`HasFunctorialInjectiveEmbeddings.under_injective` specialized to `SheafOfModules 𝒪`. -/
recall HasFunctorialInjectiveEmbeddings.under_injective
