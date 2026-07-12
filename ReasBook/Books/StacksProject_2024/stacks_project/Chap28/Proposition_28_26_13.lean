import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Semantic recall:
- `lean_leansearch` found `List.TFAE` as the canonical mathlib owner for listwise equivalent
  conditions; local Chapter 28 context identifies the project-local owners
  `AlgebraicGeometry.ProjectiveSpectrum`,
  `Scheme.Modules.IsAmple`, `TopologicalSpace.Opens.IsBasis`,
  `SheafOfModules.GeneratingSections`, and the generic section-ring morphism API around
  `Proj.fromOfGlobalSections`;
- local Chapter 28 files record the exact specialized morphism
  `X → Proj(Γ_*(X, L))` as not yet dependency-closed;
- importing the current Chapter 17 section-ring/twisted-power owner, or even the local Chapter 28
  ampleness owner that depends on it, makes this item time out before target elaboration in item
  mode, so Proposition 28.26.13 is kept as a source-facing `List.TFAE` recall block rather than a
  theorem over a noncanonical replacement for `Γ_*(X, L)`;
- the Stacks tag evidence is consistent: item tag `01Q3` and source URL tag `01Q3`.
-/

/- Proposition 28.26.13: for a quasi-compact scheme `X` and an invertible sheaf `L`, ampleness
is equivalent to the eight standard section-ring, nonvanishing-basis, twisted-generation, eventual
high-twist global-generation, and negative-tensor-power quotient conditions. -/
#check List.TFAE
