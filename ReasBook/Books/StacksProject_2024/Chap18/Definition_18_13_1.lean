import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 18.13.1 (1): for a morphism of ringed topoi or ringed sites, the direct image of a
sheaf of modules is the canonical functor `SheafOfModules.pushforward`, whose underlying sheaf of
abelian groups is the usual pushforward and whose module structure is obtained by restricting
scalars along the structure-sheaf map `f^\sharp : \mathcal O_{\mathcal D} \to f_* \mathcal
O_{\mathcal C}`. -/
recall SheafOfModules.pushforward

/- Definition 18.13.1 (2): for a morphism of ringed topoi or ringed sites, the inverse image of a
sheaf of modules is the canonical functor `SheafOfModules.pullback`, i.e. the sheaf
`\mathcal O_{\mathcal C} \otimes_{f^{-1}\mathcal O_{\mathcal D}} f^{-1}\mathcal G` with its
canonical `\mathcal O_{\mathcal C}`-module structure. -/
recall SheafOfModules.pullback
