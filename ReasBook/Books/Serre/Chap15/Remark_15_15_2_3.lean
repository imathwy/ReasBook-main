import Serre.Chap15.Theorem_15_15_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Representation

/- Domain-style sampling for this item:
- primary domain: stable-lattice reduction and the decomposition map in the Grothendieck groups
  of finite-dimensional representations over a local ring and its residue field.
- relevant owner declarations inspected before refining:
  `StableLattice`,
  `stableLatticeReduction_grothendieckClass_eq`,
  `decompositionHom`, and
  `decompositionHom_finiteRepClass_eq`.

Primitive data vs derived API:
- the primitive owner data live in `StableLattice` and its reduction construction;
- the remark itself contributes no new data, only the observation that the canonical reduction
  class theorem and decomposition-map owner already carry the intended hypothesis profile.

Source/core/bridge triage:
- source-facing: Remark `15-15.2-3` is a proof note saying that Theorem `15-15.2-2` and the
  associated decomposition homomorphism do not require any completeness hypothesis on `K`;
- core/canonical: the chapter owners are already
  `stableLatticeReduction_grothendieckClass_eq` and `decompositionHom`;
- bridge/view: the remark should therefore stay a direct recall of those owners rather than a new
  wrapper theorem restating the same conclusion with altered hypotheses. -/

/- Remark 15-15.2-3 is a proof note, not a new mathematical owner. In the chapter API, the two
relevant owner declarations are `stableLatticeReduction_grothendieckClass_eq` for Theorem
`15-15.2-2` and `decompositionHom` for the decomposition homomorphism
`d : R_K(G) → R_k(G)`. Their canonical interfaces already express the remark's point: neither
declaration assumes any completeness hypothesis on `K`. -/
recall stableLatticeReduction_grothendieckClass_eq

/- The decomposition homomorphism itself is likewise owned upstream, with no completeness
assumption in its declaration. -/
recall decompositionHom
