package libref.proof

import libref.collection.ListOps._
import libref.collection._
import libref.proof.DistinctOps._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

@library
object ListLemmas {
  def snocIndex[T] (l: List[T], t: T, i: BigInt): Boolean = {
    require(0 <= i && i < l.size + 1)
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t)) because
      (l match {
        case Nil()       => true
        case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
      })
  }.holds

  def reverseIndex[T] (l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil()       => true
      case Cons(x, xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
      (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def snocLast[T] (l: List[T], x: T): Boolean = {
    ((l :+ x).last == x) because {
      l match {
        case Nil()       => true
        case Cons(y, ys) => {
          ((y :: ys) :+ x).last ==| trivial |
            (y :: (ys :+ x)).last ==| trivial |
            (ys :+ x).last ==| snocLast(ys, x) |
            x
        }.qed
      }
    }
  }.holds

  def headReverseLast[T] (l: List[T]): Boolean = {
    require(!l.isEmpty)
    (l.head == l.reverse.last) because {
      (l: @unchecked) match {
        case Cons(x, xs) => {
          (x :: xs).head ==| trivial |
            x ==| snocLast(xs.reverse, x) |
            (xs.reverse :+ x).last ==| trivial |
            (x :: xs).reverse.last
        }.qed
      }
    }
  }.holds

  def appendIndex[T] (l1: List[T], l2: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size))) because {
      l1 match {
        case Nil()       => true
        case Cons(x, xs) =>
          (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
      }
    }
  }.holds

  @induct
  def appendAssoc[T] (l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  @induct
  def rightUnitAppend[T] (l1: List[T]): Boolean = {
    l1 ++ Nil() == l1
  }.holds

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  def leftUnitAppend[T] (l1: List[T]): Boolean = {
    Nil() ++ l1 == l1
  }.holds

  def consIsAppend[T] (l: List[T], t: T): Boolean = {
    (t :: l) == Cons[T](t, Nil[T]()) ++ l
  } holds

  def snocIsAppend[T] (l: List[T], t: T): Boolean = {
    ((l :+ t) == l ++ Cons[T](t, Nil())) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => snocIsAppend(xs, t)
      }
    }
  }.holds

  def snocAfterAppend[T] (l1: List[T], l2: List[T], t: T): Boolean = {
    ((l1 ++ l2) :+ t == l1 ++ (l2 :+ t)) because {
      l1 match {
        case Nil()       => true
        case Cons(x, xs) => snocAfterAppend(xs, l2, t)
      }
    }
  }.holds

  def snocReverse[T] (l: List[T], t: T): Boolean = {
    ((l :+ t).reverse == Cons(t, l.reverse)) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => snocReverse(xs, t)
      }
    }
  }.holds

  def reverseReverse[T] (l: List[T]): Boolean = {
    l.reverse.reverse == l because {
      l match {
        case Nil()       => trivial
        case Cons(x, xs) => {
          (xs.reverse :+ x).reverse ==| snocReverse[T](xs.reverse, x) |
            x :: xs.reverse.reverse ==| reverseReverse[T](xs) |
            (x :: xs)
        }.qed
      }
    }
  }.holds

  def reverseAppend[T] (l1: List[T], l2: List[T]): Boolean = {
    ((l1 ++ l2).reverse == l2.reverse ++ l1.reverse) because {
      l1 match {
        case Nil()       => {
          (Nil() ++ l2).reverse ==| trivial |
            l2.reverse ==| rightUnitAppend(l2.reverse) |
            l2.reverse ++ Nil() ==| trivial |
            l2.reverse ++ Nil().reverse
        }.qed
        case Cons(x, xs) => {
          ((x :: xs) ++ l2).reverse ==| trivial |
            (x :: (xs ++ l2)).reverse ==| trivial |
            (xs ++ l2).reverse :+ x ==| reverseAppend(xs, l2) |
            (l2.reverse ++ xs.reverse) :+ x ==|
              snocAfterAppend(l2.reverse, xs.reverse, x) |
            l2.reverse ++ (xs.reverse :+ x) ==| trivial |
            l2.reverse ++ (x :: xs).reverse
        }.qed
      }
    }
  }.holds

  def snocFoldRight[A, B] (xs: List[A], y: A, z: B, f: (A, B) => B): Boolean = {
    ((xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f)) because {
      xs match {
        case Nil()       => true
        case Cons(x, xs) => snocFoldRight(xs, y, z, f)
      }
    }
  }.holds

  def folds[A, B] (xs: List[A], z: B, f: (B, A) => B): Boolean = {
    val f2 = (x: A, z: B) => f(z, x)
    (xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2)) because {
      xs match {
        case Nil()       => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(f) ==| trivial |
            xs.foldLeft(f(z, x))(f) ==| folds(xs, f(z, x), f) |
            xs.reverse.foldRight(f(z, x))(f2) ==| trivial |
            xs.reverse.foldRight(f2(x, z))(f2) ==|
              snocFoldRight(xs.reverse, x, z, f2) |
            (xs.reverse :+ x).foldRight(z)(f2) ==| trivial |
            (x :: xs).reverse.foldRight(z)(f2)
        }.qed
      }
    }
  }.holds

  def scanVsFoldLeft[A, B] (l: List[A], z: B, f: (B, A) => B): Boolean = {
    (l.scanLeft(z)(f).last == l.foldLeft(z)(f)) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
      }
    }
  }.holds

  //// my hand calculation shows this should work, but it does not seem to be found
  def associative[T, U] (l1: List[T], l2: List[T], f: List[T] => U, op: (U, U) => U) = {
    f(l1 ++ l2) == op(f(l1), f(l2))
  }

  @induct
  def existsAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
    associative[T, Boolean](l1, l2, _.exists(p), _ || _ )
  }.holds

  @induct
  def forallAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
    associative[T, Boolean](l1, l2, _.forall(p), _ && _ )
  }.holds

  @induct
  def countAssoc[T] (l1 : List[T], l2 : List[T], p : T => Boolean) = {
    associative[T, BigInt](l1, l2, _.count(p), _ + _ )
  } holds

  @induct
  def scanVsFoldRight[A, B] (l: List[A], z: B, f: (A, B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A] (l1: List[A], l2: List[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T] (ls: List[List[T]]): Boolean = {
    val f: (List[T], Set[T]) => Set[T] = _.content ++ _
    (flatten(ls).content == ls.foldRight(Set[T]())(f)) because {
      ls match {
        case Nil()      => true
        case Cons(h, t) => {
          flatten(h :: t).content ==| trivial |
            (h ++ flatten(t)).content ==| appendContent(h, flatten(t)) |
            h.content ++ flatten(t).content ==| flattenPreservesContent(t) |
            h.content ++ t.foldRight(Set[T]())(f) ==| trivial |
            f(h, Set[T]()) ++ t.foldRight(Set[T]())(f) ==| trivial |
            (h :: t).foldRight(Set[T]())(f)
        }.qed
      }
    }
  }.holds

  // A lemma about `append` and `updated`
  def appendUpdate[T] (l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    // induction scheme
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).updated(i, y) == (
        if (i < l1.size)
          l1.updated(i, y) ++ l2
        else
          l1 ++ l2.updated(i - l1.size, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T] (l1: List[T], l2: List[T], n: BigInt): Boolean = {
    //induction scheme
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }) &&
      // lemma
      ((l1 ++ l2).take(n) == (
        if (n < l1.size) l1.take(n)
        else if (n > l1.size) l1 ++ l2.take(n - l1.size)
        else l1)) &&
      ((l1 ++ l2).drop(n) == (
        if (n < l1.size) l1.drop(n) ++ l2
        else if (n > l1.size) l2.drop(n - l1.size)
        else l2))
  }.holds

  // A lemma about `append` and `insertAt`
  def appendInsert[T] (l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).insertAt(i, y) == (
        if (i < l1.size) l1.insertAt(i, y) ++ l2
        else l1 ++ l2.insertAt((i - l1.size), y)))
  }.holds

  def acc_updated_eq[A] (l : List[A], i : BigInt, x : A, j : BigInt) : Boolean = {
    require(i >= 0 && i < l.size && i == j)
    l.updated(i, x)(j) == x because {
      l match {
        case Cons(hd, tl) if i == 0 => trivial
        case Cons(hd, tl) => acc_updated_eq(tl, i - 1, x, j - 1)
      }
    }
  } holds

  def acc_updated_neq[A] (l : List[A], i : BigInt, x : A, j : BigInt) : Boolean = {
    require(i >= 0 && i < l.size && j >= 0 && j < l.size && i != j)
    l.updated(i, x)(j) == l(j) because {
      l match {
        case Cons(hd, tl) if i == 0 => trivial
        case Cons(hd, tl) if j == 0 => trivial
        case Cons(hd, tl) => acc_updated_neq(tl, i - 1, x, j - 1)
      }
    }
  } holds

  @induct
  def acc_drop[A] (l : List[A], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && i >= 0 && i + n < l.size)
    l.drop(n)(i) == l(i + n) because {
      (l, n) match {
        case (Nil(), _) => trivial
        case (Cons(hd, tl), m) =>
          if (m <= BigInt(0)) trivial
          else acc_drop(tl, n - 1, i)
      }
    }
  } holds

  def acc_take[A] (l : List[A], n : BigInt, i : BigInt) : Boolean = {
    require(i >= 0 && i < l.size && i < n)
    l.take(n)(i) == l(i) because {
      if (i == 0)
        trivial
      else {
        l match {
          case Nil() => trivial
          case Cons(hd, tl) => acc_take(tl, n - 1, i - 1)
        }
      }
    }
  } holds

  def acc_slice[A] (l : List[A], from : BigInt, until : BigInt, i : BigInt) : Boolean = {
    require(0 <= from && from <= until && until <= l.size && i >= 0 && i + from < until)
    l.slice(from, until)(i) == l(from + i) because {
      acc_drop(l, from, i) && acc_take(l.drop(from), until - from, i)
    }
  } holds

  @induct
  def slice_all[A] (l : List[A]) : Boolean = {
    l.slice(0, l.size) == l
  } holds

  @induct
  def append_forall[A] (l : List[A], e : A, p : A => Boolean) : Boolean = {
    require(l.forall(p) && p(e))
    (l :+ e).forall(p)
  } holds

  @induct
  def append_forall[A] (l1 : List[A], l2 : List[A], p : A => Boolean) : Boolean = {
    require(l1.forall(p) && l2.forall(p))
    (l1 ++ l2).forall(p)
  } holds

  def drop_forall[A] (l : List[A], n : BigInt, p : A => Boolean) : Boolean = {
    require(l.forall(p) && n <= l.size)
    l.drop(n).forall(p) because {
      l match {
        case Nil() => trivial
        case Cons(hd, tl) => drop_forall(tl, n - 1, p)
      }
    }
  } holds

  @induct
  def apply_forall[A] (l : List[A], p : A => Boolean, e : A) : Boolean = {
    require(l.forall(p) && l.contains(e))
    p(e)
  } holds

  def prefix_tran[A] (l1 : List[A], l2 : List[A], l3 : List[A]) : Boolean = {
    require(l1.isPrefixOf(l2) && l2.isPrefixOf(l3))
    l1.isPrefixOf(l3) because {
      (l1, l2, l3) match {
        case (Nil(), _, _) => trivial
        case (Cons(hd1, tl1), Cons(hd2, tl2), Cons(hd3, tl3)) => prefix_tran(tl1, tl2, tl3)
        case (_, _, _) => trivial
      }
    }
  } holds

  def suffix_tran[A] (l1 : List[A], l2 : List[A], l3 : List[A]) : Boolean = {
    require(l1.isSuffixOf(l2) && l2.isSuffixOf(l3))
    l1.isSuffixOf(l3) because { prefix_tran(l1.reverse, l2.reverse, l3.reverse) }
  } holds

  def reverse_prefix[A] (l1 : List[A], l2 : List[A]) : Boolean = {
    require(l1.isPrefixOf(l2))
    l1.reverse.isSuffixOf(l2.reverse) because { reverseReverse(l1) && reverseReverse(l2) }
  } holds // Failed to prove because an unexpected error from smt-z3 solver

  @induct
  def count_contains[A] (l : List[A], e : A) : Boolean = {
    if (l.count(e) == 0)
      !l.contains(e)
    else
      l.contains(e)
  } holds

  @induct
  def contains_count[A] (l : List[A], e : A) : Boolean = {
    if (l.contains(e))
      l.count(e) > 0
    else
      l.count(e) == 0
  } holds

  def distinct_count[A] (l : List[A]) : Boolean = {
    require(distinct(l))

    // The proof will fail if we prove l1.forall(x => Cons(e, l3).count(x) == 1) or use l3.head and l3.tail instead of e and l2.
    @induct
    def forall_count_one_cons[A] (l1 : List[A], e : A, l2 : List[A], l3 : List[A]) : Boolean = {
      require(l3 == Cons(e, l2) && l1.forall(x => l2.count(x) == 1) && !l1.contains(e))
      l1.forall(x => l3.count(x) == 1)
    } holds

    val p = (x : A) => l.count(x) == 1
    l.forall(p) because {
      l match {
        case Nil() => trivial
        case Cons(hd, tl) => l.count(hd) == 1 && tl.forall(p) because {
          distinct_count(tl) && forall_count_one_cons(tl, hd, tl, l)
        }
      }
    }
  } holds

  def take_all[A] (l : List[A], n : BigInt) : Boolean = {
    require(n >= l.size)
    l.take(n) == l because {
      l match {
        case Nil() => trivial
        case Cons(hd, tl) => take_all(tl, n - 1)
      }
    }
  } holds

  def cut_as_take_drop[A] (l : List[A], n : BigInt) : Boolean = {
    l.take(n) ++ l.drop(n) == l because {
      if (n <= 0) trivial
      else {
        l match {
          case Nil() => trivial
          case Cons(hd, tl) => cut_as_take_drop(tl, n - 1)
        }
      }
    }
  } holds

  @induct
  def concat_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    (l1 ++ l2).contains(e) == l1.contains(e) || l2.contains(e)
  } holds

  @induct
  def forall_exists[T] (l : List[T], p : T => Boolean) : Boolean = {
    require(l.forall(p))
    !l.exists(!p(_))
  } holds

  @induct
  def exists_forall[T] (l : List[T], p : T => Boolean) : Boolean = {
    require(l.exists(p))
    !l.forall(!p(_))
  } holds

}

