import StacksProject_2024.stacks_project.Chap09.Definition_9_21_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.21.4:
- primary domain: Galois theory for towers of field extensions;
- sampled owner declarations:
  `IsGalois`,
  `isGalois_iff`,
  `IsGalois.tower_top_of_isGalois`,
  `IsGalois.tower_top_intermediateField`;
- best owner abstraction: the extension-level owner remains `IsGalois`;
- primitive data: a tower of fields together with the canonical compatibility data
  `[IsScalarTower F E K]`;
- derived API: upward inheritance of Galoisness along the tower is already owned by
  `IsGalois.tower_top_of_isGalois`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that in a tower `K/E/F`, Galoisness over `F` implies
  Galoisness over `E`;
- `core/canonical`: `IsGalois`;
- `bridge/view`: the tower inheritance theorem `IsGalois.tower_top_of_isGalois`.

So this file should remain a direct recall of the canonical tower theorem rather than a local
wrapper. The source's separate algebraicity hypothesis is redundant here, since the canonical
owner `IsGalois` already packages separability and normality. -/
/- Lemma 9.21.4: in a tower of field extensions `K/E/F`, if `K` is Galois over `F`, then `K` is
Galois over `E`. -/
recall IsGalois.tower_top_of_isGalois
