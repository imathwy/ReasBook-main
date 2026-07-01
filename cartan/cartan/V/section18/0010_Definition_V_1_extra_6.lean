import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file is in the set-restricted injectivity domain. The relevant owner
-- declarations inspected before refinement were `Set.InjOn`,
-- `Set.injOn_univ`, and `Function.Injective.injOn`. The source-facing notion "simple on `Γ`"
-- is injectivity of the restriction to `Γ`, so `Set.InjOn` is the right main owner; plain
-- `Function.Injective` is the unrestricted `Γ = Set.univ` special case.

/- Definition V.1-extra-6. A function is simple on `Γ` exactly when its restriction to `Γ` is
injective, i.e. when distinct points of `Γ` have distinct images. In mathlib this owner is
`Set.InjOn`; the unrestricted case is recovered by `Set.injOn_univ`. -/
#check Set.InjOn
