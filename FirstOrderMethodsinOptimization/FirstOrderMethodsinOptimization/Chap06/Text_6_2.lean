import FirstOrderMethodsinOptimization.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

variable {E : Type*} [NormedAddCommGroup E]

/- Text 6.2 is `bridge/view` in the proximal/projection domain. Domain sampling in the minimal
semantic closure shows that the relevant owner-level declarations are:
1. Chapter 2's `extendedIndicator`,
2. Chapter 6's `prox` / `prox[...]`,
3. Chapter 6's source-facing projection owner `projection_mapping`,
4. the bridge theorem `prox_extendedIndicator_eq_projection_mapping`.
The target file therefore reuses the existing chapter owner `P[C]` rather than keeping a parallel
squared-distance wrapper. -/
recall projection_mapping

/- Text 6.2: for a nonempty set `C`, the proximal mapping of the indicator function `δ_C`
coincides with the set-valued projection mapping `P_C`; in the Euclidean textbook setting, this
is the orthogonal projection operator. -/
recall prox_extendedIndicator_eq_projection_mapping
