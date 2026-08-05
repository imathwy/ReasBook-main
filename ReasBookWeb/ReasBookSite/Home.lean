import VersoBlog
open Verso Genre Blog

#doc (Page) "ReasBook" =>

This site publishes the Lean formalization of Amir Beck's
*First-Order Methods in Optimization*.

Use the top navigation to browse:

- `Home`: project overview (this page)
- `Documentation`: Lean API docs
- the book `Home` page: overview and links to all chapter source directories

After the book layout changes, regenerate `ReasBookSite/Sections.lean`,
`ReasBookSite/RouteTable.lean`, and the book home page with:

`python3 scripts/gen_sections.py`
