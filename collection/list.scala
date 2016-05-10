package libref.collection

import libref.proof.DistinctOps
import libref.proof.PermutationOps.permutation
import leon.lang._
import leon.annotation._
import scala.language.implicitConversions

case class Cons[T] (h : T, t : List[T]) extends List[T]

case class Nil[T] () extends List[T]

@library
sealed abstract class List[T] {

  def ++ (that : List[T]) : List[T] = {
    this match {
      case Nil()       => that
      case Cons(x, xs) => Cons(x, xs ++ that)
    }
  } ensuring { res =>
    (res.content == this.content ++ that.content) &&
      (res.size == this.size + that.size) &&
      (that != Nil[T]() || res == this)
  }

  def +: (e : T) : List[T] = e :: this

  def /:[B] (z : B)(op : (B, T) => B) : B = foldLeft(z)(op)

  def :+ (t : T) : List[T] = {
    this match {
      case Nil()       => Cons(t, this)
      case Cons(x, xs) => Cons(x, xs :+ (t))
    }
  } ensuring (res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def :: (t : T) : List[T] = Cons(t, this)

  def ::: (prefix : List[T]) : List[T] = prefix ++ this

  def :\[B] (z : B)(op : (T, B) => B) : B = foldRight(z)(op)
  // not in Scala List
  def - (e : T) : List[T] = {
    this match {
      case Cons(h, t) =>
        if (e == h) {
          t - e
        } else {
          Cons(h, t - e)
        }
      case Nil()      =>
        Nil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == this.content -- Set(e)
  }

  // not in Scala List
  def -- (that : List[T]) : List[T] = {
    this match {
      case Cons(h, t) =>
        if (that.contains(h)) {
          t -- that
        } else {
          Cons(h, t -- that)
        }
      case Nil()      =>
        Nil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == this.content -- that.content
  }

  // not in Scala List, note that this is different from intersect
  def & (that : List[T]) : List[T] = {
    this match {
      case Cons(h, t) =>
        if (that.contains(h)) {
          Cons(h, t & that)
        } else {
          t & that
        }
      case Nil()      =>
        Nil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == (this.content & that.content)
  }

  def apply (index : BigInt) : T = {
    require(0 <= index && index < size)
    if (index == BigInt(0)) head
    else tail(index - 1)
  } ensuring { res =>
    contains(res) && indexOf(res) <= index
  }

  // not in Scala List
  private def chunk0 (s : BigInt, l : List[T], acc : List[T], res : List[List[T]], s0 : BigInt) : List[List[T]] = {
    require(s > 0 && s0 >= 0)
    l match {
      case Nil()      =>
        if (acc.size > 0) {
          res :+ acc
        } else {
          res
        }
      case Cons(h, t) =>
        if (s0 == BigInt(0)) {
          chunk0(s, t, Cons(h, Nil()), res :+ acc, s - 1)
        } else {
          chunk0(s, t, acc :+ h, res, s0 - 1)
        }
    }
  }

  // not in Scala List
  def chunks (s : BigInt) : List[List[T]] = {
    require(s > 0)

    chunk0(s, this, Nil(), Nil(), s)
  }

  def contains (v : T) : Boolean = {
    this match {
      case Cons(h, t) if h == v => true
      case Cons(_, t)           => t.contains(v)
      case Nil()                => false
    }
  } ensuring { res =>
    res == content.contains(v)
  }

  // not in Scala List
  def content : Set[T] = this match {
    case Nil()      => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  def count (p : T => Boolean) : BigInt = {
    this match {
      case Nil()      => BigInt(0)
      case Cons(h, t) =>
        (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
    }
  } ensuring { res =>
    res == filter(p).size
  }

  // not in Scala List
  def count (e : T) : BigInt = {
    count(x => x == e)
  }

  def diff (that : List[T]) : List[T] = {
    this match {
      case Nil()                             => Nil[T]()
      case Cons(hd, tl) if that.contains(hd) => tl.diff(that.removeFirst(hd))
      case Cons(hd, tl)                      => Cons(hd, tl.diff(that))
    }
  } ensuring { res =>
    res.size <= size && res.content.subsetOf(content)
  }

  def distinct : List[T] = {
    this match {
      case Nil()                                    => Nil[T]()
      case Cons(hd, tl) if tl.distinct.contains(hd) => tl.distinct
      case Cons(hd, tl)                             => Cons(hd, tl.distinct)
    }
  } ensuring { res =>
    res.size <= size && res.content == content && DistinctOps.distinct(res)
  }

  def drop (i : BigInt) : List[T] = {
    this match {
      case Nil()      => Nil[T]()
      case Cons(h, t) =>
        if (i <= BigInt(0)) Cons[T](h, t)
        else t.drop(i - 1)
    }
  } ensuring { res =>
    res.content.subsetOf(content) && (res.size == (
      if (i <= 0) size
      else if (i >= size) BigInt(0)
      else size - i
      ))
  }

  def dropRight (n : BigInt) : List[T] = {
    reverse.drop(n).reverse
  } ensuring {
    res =>
      res.content.subsetOf(content) && (res.size == (
        if (n <= 0) size
        else if (n >= size) BigInt(0)
        else size - n
        ))
  }

  def dropWhile (p : T => Boolean) : List[T] = {
    this match {
      case Cons(h, t) if p(h) => t.dropWhile(p)
      case _                  => this
    }
  } ensuring { res =>
    (res.size <= size) &&
      res.content.subsetOf(content) &&
      (res.isEmpty || !p(res.head))
  }

  // not in Scala List
  def evenSplit : (List[T], List[T]) = {
    val c = size / 2
    (take(c), drop(c))
  }

  def exists (p : T => Boolean) : Boolean = {
    this match {
      case Nil()      => false
      case Cons(h, t) => p(h) || t.exists(p)
    }
  }

  def filter (p : T => Boolean) : List[T] = {
    this match {
      case Nil()              => Nil[T]()
      case Cons(h, t) if p(h) => Cons(h, t.filter(p))
      case Cons(_, t)         => t.filter(p)
    }
  } ensuring { res =>
    res.size <= size &&
      res.content.subsetOf(content) &&
      res.forall(p)
  }

  def filterNot (p : T => Boolean) : List[T] = {
    filter(!p(_))
  } ensuring { res =>
    res.size <= size &&
      res.content.subsetOf(content) &&
      res.forall(!p(_))
  }

  def find (p : T => Boolean) : Option[T] = {
    this match {
      case Nil()              => None[T]()
      case Cons(h, t) if p(h) => Some(h)
      case Cons(_, t)         => t.find(p)
    }
  } ensuring { res =>
    res.isDefined ==> (content.contains(res.get) && p(res.get))
  }

  // not in Scala List
  def find (e : T) : Option[BigInt] = {
    this match {
      case Nil()      => None[BigInt]()
      case Cons(h, t) =>
        if (h == e) {
          Some[BigInt](0)
        } else {
          t.find(e) match {
            case None()  => None[BigInt]()
            case Some(i) => Some(i + 1)
          }
        }
    }
  } ensuring { res => !res.isDefined || content.contains(e) }

  def flatMap[R] (f : T => List[R]) : List[R] = ListOps.flatten(this map f)

  def foldLeft[R] (z : R)(f : (R, T) => R) : R = this match {
    case Nil()      => z
    case Cons(h, t) => t.foldLeft(f(z, h))(f)
  }

  def foldRight[R] (z : R)(f : (T, R) => R) : R = this match {
    case Nil()      => z
    case Cons(h, t) => f(h, t.foldRight(z)(f))
  }

  def forall (p : T => Boolean) : Boolean = {
    this match {
      case Nil()      => true
      case Cons(h, t) => p(h) && t.forall(p)
    }
  }

  def groupBy[R] (f : T => R) : Map[R, List[T]] = this match {
    case Nil()      => Map.empty[R, List[T]]
    case Cons(h, t) =>
      val key : R = f(h)
      val rest : Map[R, List[T]] = t.groupBy(f)
      val prev : List[T] = if (rest isDefinedAt key) rest(key) else Nil[T]()
      (rest ++ Map((key, h :: prev))) : Map[R, List[T]]
  }

  def head : T = {
    require(this != Nil[T]())
    val Cons(h, _) = this
    h
  }

  def headOption : Option[T] = {
    this match {
      case Cons(h, t) => Some(h)
      case Nil()      => None[T]()
    }
  } ensuring { res =>
    res.isDefined != isEmpty
  }

  def indexOf (elem : T, from : BigInt) : BigInt = {
    val i = drop(from).indexOf(elem)
    if (i == -1) BigInt(-1)
    else from + i
  } ensuring { res =>
    (res == -1 || res >= from && res < size) /*&& (
      (res != -1) ==> (apply(res) == elem && slice(from, res).forall(x => x != elem))
    )*/
    // unknown
  }

  def indexOf (elem : T) : BigInt = {
    this match {
      case Nil()                                          => BigInt(-1)
      case Cons(hd, tl) if hd == elem                     => BigInt(0)
      case Cons(hd, tl) if tl.indexOf(elem) == BigInt(-1) => BigInt(-1)
      case Cons(hd, tl)                                   => tl.indexOf(elem) + BigInt(1)
    }
  } ensuring { res =>
    (res == -1 || res >= 0 && res < size) && (
      (res != -1) ==> (apply(res) == elem && take(res).forall(x => x != elem))
      )
  }

  def indexWhere (p : T => Boolean, from : BigInt) : BigInt = {
    val i = drop(from).indexWhere(p)
    if (i == -1) BigInt(-1)
    else from + i
  } ensuring { res =>
    (res == -1 || res >= from && res < size) /*&& (
      (res != -1) ==> (p(apply(res)) && slice(from, res).forall(x => !p(x)))
    )*/
    // unknown
  }

  def indexWhere (p : T => Boolean) : BigInt = {
    this match {
      case Nil()                                          => BigInt(-1)
      case Cons(hd, tl) if p(hd)                          => BigInt(0)
      case Cons(hd, tl) if tl.indexWhere(p) == BigInt(-1) => BigInt(-1)
      case Cons(hd, tl)                                   => tl.indexWhere(p) + BigInt(1)
    }
  } ensuring { res =>
    (res == -1 || res >= 0 && res < size) && (
      (res != -1) ==> (p(apply(res)) && take(res).forall(x => !p(x)))
      )
  }

  def init : List[T] = {
    require(!isEmpty)
    ((this : @unchecked) match {
      case Cons(h, Nil()) => Nil[T]()
      case Cons(h, t)     => Cons[T](h, t.init)
    })
  } ensuring { res =>
    res.size == size - 1 &&
      res.content.subsetOf(content)
  }


  // not in Scala List
  private def insertAtImpl (pos : BigInt, l : List[T]) : List[T] = {
    require(0 <= pos && pos <= size)
    if (pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.insertAtImpl(pos - 1, l))
        case Nil()      =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
      res.content == this.content ++ l.content
  }

  // not in Scala List
  def insertAt (pos : BigInt, l : List[T]) : List[T] = {
    require(-pos <= size && pos <= size)
    if (pos < 0) {
      insertAtImpl(size + pos, l)
    } else {
      insertAtImpl(pos, l)
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
      res.content == this.content ++ l.content
  }

  // not in Scala List
  def insertAt (pos : BigInt, e : T) : List[T] = {
    require(-pos <= size && pos <= size)
    insertAt(pos, Cons[T](e, Nil()))
  } ensuring { res =>
    res.size == this.size + 1 &&
      res.content == this.content ++ Set(e)
  }

  def intersect (that : List[T]) : List[T] = {
    this match {
      case Nil()                             => Nil[T]()
      case Cons(hd, tl) if that.contains(hd) => Cons(hd, tl.intersect(that.removeFirst(hd)))
      case Cons(hd, tl)                      => tl.intersect(that)
    }
  } ensuring { res =>
    res.size <= size /*&& res.size <= that.size &&
    res.content == (content & that.content)*/
    //unknown
  }

  def isDefinedAt (i : BigInt) = i >= 0 && i < size

  def isEmpty = this != Nil()

  // not in Scala List
  def isPrefixOf (l : List[T]) : Boolean = {
    (this, l) match {
      case (Nil(), _)                       => true
      case (Cons(hd1, tl1), Cons(hd2, tl2)) => hd1 == hd2 && tl1.isPrefixOf(tl2)
      case (_, _)                           => false
    }
  } ensuring { res =>
    res ==> (size <= l.size)
  }

  // not in Scala List
  def isSuffixOf (l : List[T]) : Boolean = {
    reverse.isPrefixOf(l.reverse)
  } ensuring { res =>
    res ==> (size <= l.size)
  }

  def last : T = {
    require(!isEmpty)
    (this : @unchecked) match {
      case Cons(h, Nil()) => h
      case Cons(_, t)     => t.last
    }
  } ensuring { res =>
    contains(res)
  }

  def lastIndexOf (elem : T, end : BigInt) : BigInt = {
    val i = take(end).reverse.indexOf(elem)
    if (i == -1) BigInt(-1)
    else end - i - 1
  } ensuring { res =>
    res == -1 || res >= 0 && res <= end
  }

  def lastIndexOf (elem : T) : BigInt = {
    val i = reverse.indexOf(elem)
    if (i == -1) BigInt(-1)
    else size - i - 1
  } ensuring { res =>
    res == -1 || res >= 0 && res < size
  }

  def lastIndexWhere (p : T => Boolean, end : BigInt) : BigInt = {
    val i = take(end).reverse.indexWhere(p)
    if (i == -1) BigInt(-1)
    else end - i - 1
  } ensuring { res =>
    res == -1 || res >= 0 && res <= end
  }

  def lastIndexWhere (p : T => Boolean) : BigInt = {
    val i = reverse.indexWhere(p)
    if (i == -1) BigInt(-1)
    else size - i - 1
  } ensuring { res =>
    res == -1 || res >= 0 && res < size
  }

  def lastOption : Option[T] = {
    this match {
      case Cons(h, t) =>
        t.lastOption.orElse(Some(h))
      case Nil()      =>
        None[T]()
    }
  } ensuring { res =>
    res.isDefined != isEmpty
  }

  def length = size

  def lengthCompare (len : BigInt) : BigInt = {
    if (length < len) BigInt(-1)
    else if (length == len) BigInt(0)
    else BigInt(1)
  }

  def map[R] (f : T => R) : List[R] = {
    this match {
      case Nil()      => Nil[R]()
      case Cons(h, t) => f(h) :: t.map(f)
    }
  } ensuring { res =>
    res.size == size
  }

  def nonEmpty : Boolean = !isEmpty

  def padTo (s : BigInt, e : T) : List[T] = {
    (this, s) match {
      case (_, s) if s <= 0 =>
        this
      case (Nil(), s)       =>
        Cons(e, Nil().padTo(s - 1, e))
      case (Cons(h, t), s)  =>
        Cons(h, t.padTo(s - 1, e))
    }
  } ensuring { res =>
    if (s <= size)
      res == this
    else
      res.size == s &&
        res.content == content ++ Set(e)
  }

  def partition (p : T => Boolean) : (List[T], List[T]) = {
    this match {
      case Nil()      => (Nil[T](), Nil[T]())
      case Cons(h, t) =>
        val (l1, l2) = t.partition(p)
        if (p(h)) (h :: l1, l2)
        else (l1, h :: l2)
    }
  } ensuring { res =>
    res._1 == filter(p) &&
      res._2 == filterNot(p)
  }

  def prefixLength (p : T => Boolean) : BigInt = {
    this match {
      case Nil()                 => BigInt(0)
      case Cons(hd, tl) if p(hd) => BigInt(1) + tl.prefixLength(p)
      case Cons(hd, tl)          => BigInt(0)
    }
  } ensuring { res =>
    res <= size && take(res).forall(p) /*&& (res == size || !p(apply(res + 1)))*/
    // unknown
  }

  // not in Scala List
  def removeFirst (e : T) : List[T] = {
    this match {
      case Nil()        => Nil[T]()
      case Cons(hd, tl) => if (hd == e) tl else Cons(hd, tl.removeFirst(e))
    }
  } ensuring {
    res => this.contains(e) ==> (res.length == this.length - 1)
  }

  // not in Scala List
  def replace (from : T, to : T) : List[T] = {
    this match {
      case Nil()      => Nil[T]()
      case Cons(h, t) =>
        val r = t.replace(from, to)
        if (h == from) Cons(to, r)
        else Cons(h, r)
    }
  } ensuring { res =>
    res.size == size &&
      res.content == (
        (content -- Set(from)) ++
          (if (content.contains(from)) Set(to) else Set[T]())
        )
  }

  // not in Scala List
  def replaceAt (pos : BigInt, l : List[T]) : List[T] = {
    require(-pos <= size && pos <= size)
    if (pos < 0) {
      replaceAtImpl(size + pos, l)
    } else {
      replaceAtImpl(pos, l)
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  // not in Scala List
  private def replaceAtImpl (pos : BigInt, l : List[T]) : List[T] = {
    require(0 <= pos && pos <= size)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.replaceAtImpl(pos - 1, l))
        case Nil()      =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def reverse : List[T] = {
    this match {
      case Nil()       => this
      case Cons(x, xs) => xs.reverse :+ x
    }
  } ensuring { res =>
    res.size == size &&
      res.content == content /*&&
    headOption == res.lastOption &&
    lastOption == res.headOption*/
    // unknown
  }

  // not in Scala List
  def rotate (s : BigInt) : List[T] = {
    if (isEmpty) Nil[T]()
    else drop(s mod size) ++ take(s mod size)
  } ensuring { res =>
    res.size == size /*&& res.content == content*/
    // unknown
  }

  def scanLeft[R] (z : R)(f : (R, T) => R) : List[R] = {
    this match {
      case Nil()      => z :: Nil()
      case Cons(h, t) => z :: t.scanLeft(f(z, h))(f)
    }
  } ensuring { !_.isEmpty }

  def scanRight[R] (z : R)(f : (T, R) => R) : List[R] = {
    this match {
      case Nil()      => z :: Nil[R]()
      case Cons(h, t) =>
        val rest@Cons(h1, _) = t.scanRight(z)(f)
        f(h, h1) :: rest
    }
  } ensuring { !_.isEmpty }

  def size : BigInt = {
    this match {
      case Nil()      => BigInt(0)
      case Cons(h, t) => 1 + t.size
    }
  } ensuring (_ >= 0)

  def slice (from : BigInt, until : BigInt) : List[T] = {
    require(from >= 0 && until <= size)
    drop(from).take(until - from)
  } ensuring { res =>
    res.content.subsetOf(content) && res.size == (
      if (until >= from) (until - from)
      else BigInt(0)
      )
  }

  def span (p : T => Boolean) : (List[T], List[T]) = {
    this match {
      case Nil()                 => (Nil[T](), Nil[T]())
      case Cons(hd, tl) if p(hd) => (Cons(hd, tl.span(p)._1), tl.span(p)._2)
      case Cons(hd, tl)          => (Nil[T](), this)
    }
  } ensuring { res =>
    res._1 == takeWhile(p) && res._2 == dropWhile(p)
  }

  def splitAt (n : BigInt) : (List[T], List[T]) = {
    this match {
      case Nil()                  => (Nil[T](), Nil[T]())
      case Cons(hd, tl) if n <= 0 => (Nil[T](), this)
      case Cons(hd, tl)           => (Cons(hd, tl.splitAt(n - 1)._1), tl.splitAt(n - 1)._2)
    }
  } ensuring { res =>
    res._1 == take(n) && res._2 == drop(n)
  }

  // not in Scala List
  def splitAt (e : T) : List[List[T]] = split(Cons(e, Nil()))

  // not in Scala List
  def split (seps : List[T]) : List[List[T]] = this match {
    case Cons(h, t) =>
      if (seps.contains(h)) {
        Cons(Nil(), t.split(seps))
      } else {
        val r = t.split(seps)
        Cons(Cons(h, r.head), r.tail)
      }
    case Nil()      =>
      Cons(Nil(), Nil())
  }

  def tail : List[T] = {
    require(this != Nil[T]())
    val Cons(_, t) = this
    t
  }

  def take (i : BigInt) : List[T] = {
    this match {
      case Nil()      => Nil[T]()
      case Cons(h, t) =>
        if (i <= BigInt(0)) Nil[T]()
        else Cons(h, t.take(i - 1))
    }
  } ensuring { res =>
    res.content.subsetOf(content) && (res.size == (
      if (i <= 0) BigInt(0)
      else if (i >= size) size
      else i
      ))
  }

  def takeRight (n : BigInt) : List[T] = {
    reverse.take(n).reverse
  } ensuring { res =>
    res.content.subsetOf(content) && (res.size == (
      if (n <= 0) BigInt(0)
      else if (n >= size) size
      else n
      ))
  }

  def takeWhile (p : T => Boolean) : List[T] = {
    this match {
      case Cons(h, t) if p(h) => Cons(h, t.takeWhile(p))
      case _                  => Nil[T]()
    }
  } ensuring { res =>
    res.forall(p) &&
      res.size <= size &&
      res.content.subsetOf(content)
  }

  def union (that : List[T]) : List[T] = this ++ that

  // not in Scala List
  def unique : List[T] = this match {
    case Nil()      => Nil()
    case Cons(h, t) => Cons(h, t.unique - h)
  }

  def updated (i : BigInt, y : T) : List[T] = {
    require(0 <= i && i < size && size > 0)
    if (i == 0)
      Cons(y, tail)
    else
      Cons(head, tail.updated(i - 1, y))
  } ensuring {
    res => res.size == size
  }

  // In case we implement for-comprehensions
  def withFilter (p : T => Boolean) = filter(p)

  def zip[B] (that : List[B]) : List[(T, B)] = {
    (this, that) match {
      case (Cons(h1, t1), Cons(h2, t2)) =>
        Cons((h1, h2), t1.zip(t2))
      case _                            =>
        Nil[(T, B)]()
    }
  } ensuring { res =>
    res.size == (
      if (size <= that.size) size else that.size
      )
  }

}

@library
object ListOps {

  def flatten[T] (ls : List[List[T]]) : List[T] = ls match {
    case Cons(h, t) => h ++ flatten(t)
    case Nil()      => Nil()
  }

}

object List {

  @ignore
  def apply[T] (elems : T*) : List[T] = {
    var l : List[T] = Nil[T]()
    for (e <- elems) {
      l = Cons(e, l)
    }
    l.reverse
  }

  @library
  def fill[T] (n : BigInt)(x : T) : List[T] = {
    if (n <= 0) Nil[T]
    else Cons[T](x, fill[T](n - 1)(x))
  } ensuring { res =>
    (res.content == (if (n <= BigInt(0)) Set.empty[T] else Set(x))) &&
      res.size == (if (n <= BigInt(0)) BigInt(0) else n)
  }

  def unzip[A1, A2] (l : List[(A1, A2)]) : (List[A1], List[A2]) = {
    l match {
      case Nil()                => (Nil[A1](), Nil[A2]())
      case Cons((hd1, hd2), tl) => (Cons[A1](hd1, unzip(tl)._1), Cons[A2](hd2, unzip(tl)._2))
    }
  } ensuring { res =>
    res._1.size == l.size && res._2.size == l.size
  }

  def unzip3[A1, A2, A3] (l : List[(A1, A2, A3)]) : (List[A1], List[A2], List[A3]) = {
    l match {
      case Nil()                     => (Nil[A1](), Nil[A2](), Nil[A3]())
      case Cons((hd1, hd2, hd3), tl) => (Cons[A1](hd1, unzip3(tl)._1), Cons[A2](hd2, unzip3(tl)._2), Cons[A3](hd3, unzip3(tl)._3))
    }
  } ensuring { res =>
    res._1.size == l.size && res._2.size == l.size && res._3.size == l.size
  }

  case class Bisimulation[T] (l1 : List[T]) {
    def ~ (l2 : List[T]) : Boolean = permutation(l1, l2)

    def ~~ (l2 : List[T]) : Boolean = l1.content == l2.content
  }

  implicit def bisimulate[T] (l : List[T]) = Bisimulation(l)
}

// 'Cons' Extractor
@library
object :: {
  def unapply[A] (l : List[A]) : Option[(A, List[A])] = l match {
    case Nil()       => None()
    case Cons(x, xs) => Some((x, xs))
  }
}
