/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part17
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part18
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part19
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part21
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part22
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part23

/-!
Overview page for `3.15 Polars of Convex Functions`.

This aggregation module imports all currently available part files for this section.

Verso links:
- [Section overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15/)
- [Chapter overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/)
- [Book overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/book/)

Directory:

- [Part 1 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part1.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part1/))
- [Part 2 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part2.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part2/))
- [Part 3 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part3.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part3/))
- [Part 4 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part4.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part4/))
- [Part 5 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part5.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part5/))
- [Part 6 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part6.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part6/))
- [Part 7 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part7.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part7/))
- [Part 8 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part8.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part8/))
- [Part 9 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part9.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part9/))
- [Part 10 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part10.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part10/))
- [Part 11 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part11.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part11/))
- [Part 12 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part12.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part12/))
- [Part 13 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part13.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part13/))
- [Part 14 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part14.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part14/))
- [Part 15 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part15.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part15/))
- [Part 16 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part16.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part16/))
- [Part 17 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part17.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part17/))
- [Part 18 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part18.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part18/))
- [Part 19 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part19.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part19/))
- [Part 20 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part20.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part20/))
- [Part 21 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part21.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part21/))
- [Part 22 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part22.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part22/))
- [Part 23 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap03/section15_part23.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part23/))

-/
