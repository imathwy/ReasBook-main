import Mathlib

import cartan.Chapters.Chap01
import cartan.Chapters.Chap02
import cartan.Chapters.Chap03
import cartan.Chapters.Chap04
import cartan.Chapters.Chap05
import cartan.Chapters.Chap06
import cartan.Chapters.Chap07

/-!
Overview page for Cartan.

This aggregation module imports the currently formalized sections in this book.
Use the links below to jump directly into chapter and section overview pages.

Verso links:
- [Book home](/ReasBook-private/books/cartan/)
- [Book overview](/ReasBook-private/books/cartan/book/)

Directory:

Chapter 01

- Section 1.1 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap01/section01.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap01/section01/))
- Section 1.2 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap01/section02.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap01/section02/))
- Section 1.3 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap01/section03.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap01/section03/))
- Section 1.4 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap01/section04.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap01/section04/))

Chapter 02

- Section 2.5 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap02/section05.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap02/section05/))
- Section 2.6 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap02/section06.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap02/section06/))

Chapter 03

- Section 3.7 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section07.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section07/))
- Section 3.8 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section08.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section08/))
- Section 3.9 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section09.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section09/))
- Section 3.10 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section10.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section10/))
- Section 3.11 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section11.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section11/))
- Section 3.12 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap03/section12.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap03/section12/))

Chapter 04

- Section 4.13 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap04/section13.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap04/section13/))
- Section 4.14 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap04/section14.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap04/section14/))
- Section 4.15 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap04/section15.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap04/section15/))
- Section 4.16 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap04/section16.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap04/section16/))
- Section 4.17 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap04/section17.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap04/section17/))

Chapter 05

- Section 5.18 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap05/section18.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap05/section18/))
- Section 5.19 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap05/section19.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap05/section19/))
- Section 5.20 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap05/section20.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap05/section20/))
- Section 5.21 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap05/section21.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap05/section21/))

Chapter 06

- Section 6.22 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap06/section22.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap06/section22/))
- Section 6.23 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap06/section23.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap06/section23/))
- Section 6.24 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap06/section24.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap06/section24/))
- Section 6.25 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap06/section25.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap06/section25/))
- Section 6.26 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap06/section26.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap06/section26/))

Chapter 07

- Section 7.27 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap07/section27.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap07/section27/))
- Section 7.28 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap07/section28.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap07/section28/))
- Section 7.29 ([Documentation](/ReasBook-private/docs/Books/cartan/Chapters/Chap07/section29.html)) ([Verso](/ReasBook-private/books/cartan/chapters/chap07/section29/))

-/

/-!
# cartan.Book

Auto-managed aggregation root for lifted prerequisite modules. Keep project
mathematics in the chapter subtrees and let the orchestrator manage the import
block above.
-/
