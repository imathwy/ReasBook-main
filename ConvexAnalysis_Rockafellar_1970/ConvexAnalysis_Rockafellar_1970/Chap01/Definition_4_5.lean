import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Definition 4.5 names the dimension of a function as the dimension of its
  effective domain; concrete coordinate statements are downstream specializations.
- `core/canonical`: the owner abstractions are `effectiveDomain` from Definition 4.4 and the
  chapter declaration `Set.affineDim` from Definition 2.4.10.
- `bridge/view`: the effective domain is expressed directly by the canonical notation `dom(f)`, so
  the source reading belongs on the composite owner expression `dim[𝕜](dom(f))`; no
  separate function-side owner is needed.
- Domain-style sampling: the relevant declarations in this domain are the owner
  `AffineSubspace.affineDim` from Theorem 1.3, the chapter bridge `Set.affineDim` from
  Definition 2.4.10, and the primitive set-valued bridge `effectiveDomain` from Definition 4.4.
- Primitive data vs derived API: the effective domain formula is the primitive set-valued bridge;
  the function dimension is the derived owner-side reading `Set.affineDim (dom(f))`, not a new
  packaged owner.
- Layer target: `bridge/view`, by direct recall/use of the intrinsic affine-space owner level
  instead of a parallel function wrapper.
-/

/- Definition 4.5 is a direct composite of existing owners:
`effectiveDomain` (`dom(f)`) and `Set.affineDim` (`dim[𝕜](·)`).
No function-side alias theorem is introduced. -/
recall effectiveDomain
recall Set.affineDim
