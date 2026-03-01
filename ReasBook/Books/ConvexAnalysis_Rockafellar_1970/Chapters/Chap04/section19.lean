/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part14

/-!
Overview page for 4.19 Polyhedral Convex Sets and Functions.

This aggregation module imports all currently available part files for this section.
Use this page to jump to each part page quickly.

Verso links:
- [Section overview](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19/)
- [Chapter overview](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/)
- [Book overview](/ReasBook-main/books/convexanalysis_rockafellar_1970/book/)

Directory:

- [Part 1 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part1.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part1/))
- [Part 2 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part2.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part2/))
- [Part 3 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part3.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part3/))
- [Part 4 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part4.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part4/))
- [Part 5 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part5.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part5/))
- [Part 6 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part6.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part6/))
- [Part 7 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part7.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part7/))
- [Part 8 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part8.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part8/))
- [Part 9 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part9.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part9/))
- [Part 10 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part10.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part10/))
- [Part 11 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part11.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part11/))
- [Part 12 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part12.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part12/))
- [Part 13 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part13.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part13/))
- [Part 14 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap04/section19_part14.lean) ([Verso](/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap04/section19_part14/))

-/
