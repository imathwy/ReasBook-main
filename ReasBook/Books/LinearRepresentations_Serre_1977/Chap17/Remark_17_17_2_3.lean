import Serre.Chap17.Corollary_17_17_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for this item:
* primary domain: subgroup induction on Grothendieck groups of finite-dimensional and finite
  projective modular representations.
* relevant owner declarations inspected in the same domain:
  `Representation.FDRep.subgroupInduction`,
  `Representation.Subgroup.finiteRepGrothendieckGroupInduction`,
  `Representation.FiniteProjectiveGroupAlgebraModule.subgroupInduction`,
  `Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction`.

Primitive data vs derived API:
* the primitive construction is subgroup induction on representations/modules;
* the Grothendieck-group induction maps are the derived owner-level API already defined upstream in
  `Corollary_17_17_2_2`;
* this remark contributes no new source-facing object, map, or proposition beyond that existing
  owner API.

Source/core/bridge triage:
* source-facing: Remark `17-17.2-3` is explanatory prose about the reach of the modular
  Brauer-induction argument;
* core/canonical: the chapter owner declarations are the two subgroup-induction homomorphisms in
  `Representation.Subgroup`;
* bridge/view: this file should therefore stay a direct recall of those owners rather than
  introducing a parallel local wrapper or alias. -/
/- Remark 17-17.2-3: the argument used in the proof of Theorem `39` applies in many other
situations and, in particular, leads to the modular analogue of Artin's theorem developed next.
For the chapter/project API, the relevant source-facing owner already is the subgroup-induction
homomorphism on finite-dimensional modular Grothendieck groups; this remark adds no new local
declaration beyond recalling that canonical map. -/
recall Representation.Subgroup.finiteRepGrothendieckGroupInduction

/- The projective induction map is likewise already owned upstream in
`Representation.Subgroup`; the following modular Artin-induction theorem uses its rationalized
direct-sum form, not a remark-specific duplicate. -/
recall Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction
