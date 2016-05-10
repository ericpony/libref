package libref.collection

import libref.proof.PairListLemmas._
import leon.proof._
import leon.lang._
import leon.annotation._

/**
  * PList
  * List of key-value pairs with integer keys
  */
package object PairList {

  case class Pair[K, V] (key : K, value : V)

  case class PCons[K, V] (h : Pair[K, V], t : PList[K, V]) extends PList[K, V]

  case class PNil[K, V] () extends PList[K, V]

  @library
  sealed abstract class PList[K, V] {

    def size : BigInt = (this match {
      case PNil()      => BigInt(0)
      case PCons(h, t) => 1 + t.size
    }) ensuring (_ >= 0)

    def content : Set[Pair[K, V]] = this match {
      case PNil()      => Set[Pair[K, V]]()
      case PCons(h, t) => Set(h) ++ t.content
    }

    def contains (v : Pair[K, V]) : Boolean = (this match {
      case PCons(h, t) if h == v => true
      case PCons(_, t)           => t.contains(v)
      case PNil()                => false
    }) ensuring { res =>
      res == (content contains v) && (res ==> hasKey(v.key))
    }

    def ++ (that : PList[K, V]) : PList[K, V] = (this match {
      case PNil()       => that
      case PCons(x, xs) => PCons[K, V](x, xs ++ that)
    }) ensuring { res =>
      (res.content == this.content ++ that.content) &&
        (res.size == this.size + that.size) &&
        (that != PNil[K, V]() || res == this)
    }

    def head : Pair[K, V] = {
      require(this != PNil[K, V]())
      val PCons(h, _) = this
      h
    }

    def tail : PList[K, V] = {
      require(this != PNil[K, V]())
      val PCons(_, t) = this
      t
    }

    def :: (t : Pair[K, V]) : PList[K, V] = PCons(t, this)

    def :+ (t : Pair[K, V]) : PList[K, V] = {
      this match {
        case PNil()       => PCons(t, this)
        case PCons(x, xs) => PCons(x, xs :+ (t))
      }
    } ensuring (res => (res.size == size + 1) && (res.content == content ++ Set(t)))

    def reverse : PList[K, V] = {
      this match {
        case PNil()       => this
        case PCons(x, xs) => xs.reverse :+ x
      }
    } ensuring (res => (res.size == size) && (res.content == content))

    def keys : List[K] = mapList(item => item.key)

    def values : List[V] = mapList(item => item.value)

    def take (i : BigInt) : PList[K, V] = {
      (this, i) match {
        case (PNil(), _)      => PNil[K, V]()
        case (PCons(h, t), i) => if (i <= BigInt(0)) PNil[K, V]() else PCons(h, t.take(i - 1))
      }
    } ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if (i <= 0) BigInt(0)
        else if (i >= this.size) this.size
        else i
        ))
    }

    def drop (i : BigInt) : PList[K, V] = {
      (this, i) match {
        case (PNil(), _)      => PNil[K, V]()
        case (PCons(h, t), i) => if (i <= BigInt(0)) PCons[K, V](h, t) else t.drop(i - 1)
      }
    } ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if (i <= 0) this.size
        else if (i >= this.size) BigInt(0)
        else this.size - i
        ))
    }

    def slice (from : BigInt, to : BigInt) : PList[K, V] = {
      require(0 <= from && from <= to && to <= size)
      drop(from).take(to - from)
    }

    def replace (from : Pair[K, V], to : Pair[K, V]) : PList[K, V] = {
      this match {
        case PNil()      => PNil[K, V]()
        case PCons(h, t) =>
          val r = t.replace(from, to)
          if (h == from) PCons(to, r) else PCons(h, r)
      }
    } ensuring { (res : PList[K, V]) =>
      res.size == this.size &&
        res.content == (
          (this.content -- Set(from)) ++
            (if (this.content contains from) Set(to) else Set[Pair[K, V]]())
          )
    }

    /**
      * Delete ALL occurrences of e from the list
      */
    def - (e : Pair[K, V]) : PList[K, V] = {
      this match {
        case PCons(h, t) => if (e == h) t - e else PCons(h, t - e)
        case PNil()      => PNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == this.content -- Set(e)
    }

    def -- (that : PList[K, V]) : PList[K, V] = {
      this match {
        case PCons(h, t) => if (that.contains(h)) t -- that else PCons(h, t -- that)
        case PNil()      => PNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == this.content -- that.content
    }

    def & (that : PList[K, V]) : PList[K, V] = {
      this match {
        case PCons(h, t) => if (that.contains(h)) PCons(h, t & that) else t & that
        case PNil()      => PNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == (this.content & that.content)
    }

    def ~ (that : PList[K, V]) = permutation(this, that)

    def ~~ (that : PList[K, V]) = this.content == that.content

    def update (data : Pair[K, V]) : PList[K, V] = {
      if (!hasKey(data.key))
        data :: this
      else {
        this match {
          case PNil()               => data :: PNil[K, V]()
          case PCons(Pair(k, v), t) =>
            if (k == data.key) Pair(k, data.value) :: t
            else Pair(k, v) :: t.update(data)
        }
      }
    } ensuring {
      res => res.size > 0 && res.hasKey(data.key)
      //res.forall(p => p.key != data.key || p.value == data.value)
    }

    def hasKey (key : K) : Boolean = {
      this match {
        case PNil()               => false
        case PCons(Pair(k, v), t) => k == key || t.hasKey(key)
      }
    } ensuring { res =>
      (res ==> (
        get(key).isDefined &&
          // Adding the following line will lead to unsoundness
          // contains(get(key).get) &&
          getAll(key) != PNil[K, V]()
        )) &&
        ((!res) ==> (
          !get(key).isDefined &&
            getAll(key) == PNil[K, V]()
          ))
    }

    /**
      * Get the first element in this list with the provided key.
      */
    def getFirst (key : K) : Option[Pair[K, V]] = {
      this match {
        case PNil()      => None[Pair[K, V]]()
        case PCons(h, t) => if (h.key == key) Some[Pair[K, V]](h) else t.getFirst(key)
      }
    } ensuring { res =>
      res.isDefined ==>
        (res.get.key == key &&
          res.get == getAll(key).head)
    }

    /**
      * Get the last element in this list with the provided key.
      */
    def getLast (key : K) = this.reverse.getFirst(key)

    /**
      * Get all elements in this list with the provided key.
      * The order in which the elements are stored in the returned list
      * is consistent with the order they are stored in the original list.
      * Note: This version of getAll is easier to verify for Leon than
      * the concise version
      * def getAll (key: K) = this.filter(item => item.key == key).
      */
    def getAll (key : K) : PList[K, V] = {
      this match {
        case PNil()      => PNil[K, V]()
        case PCons(h, t) => if (h.key == key) PCons(h, t.getAll(key)) else t.getAll(key)
      }
    } ensuring { res =>
      res.size <= size &&
        res.content.subsetOf(content) &&
        res.forall(item => item.key == key) &&
        (res != PNil[K, V]() ==> hasKey(key))
    }

    /**
      * Get an element from the list with the provided key.
      */
    def get = getFirst _

    /**
      * Obtain a new list by removing the first occurrence of e
      * from this list.
      */
    def deleteFirst (e : Pair[K, V]) : PList[K, V] = {
      if (this == PNil[K, V]()) this
      else if (head == e) tail
      else PCons(head, tail.deleteFirst(e))
    } ensuring { res =>
      if (contains(e)) {
        res.size == size - 1 &&
          res.content == content -- Set(e) because delete_content(this, e)
      } else {
        res.size == size &&
          res.content == content
      }
    }

    /**
      * Obtain a new list by removing the first element with
      * the provided key from this list.
      */
    def deleteFirst (key : K) : PList[K, V] = {
      this match {
        case PNil()      => this
        case PCons(h, t) => if (h.key == key) t else PCons(h, t.deleteFirst(key))
      }
    } ensuring { res =>
      if (hasKey(key)) {
        val e = getFirst(key).get
        res.size == size - 1 &&
          res.content == content -- Set(e) because delete_content(this, e)
      } else {
        res.size == size &&
          res.content == content
      }
    }

    /**
      * Obtain a new list by removing the last element with
      * the provided key from this list.
      */
    def deleteLast (key : K) = this.reverse.deleteFirst(key)

    /**
      * Obtain a new list by removing all element with the
      * provided key from this list.
      */
    def deleteAll (key : K) : PList[K, V] = {
      this match {
        case PNil()      => this
        case PCons(h, t) => if (h.key == key) t.deleteAll(key) else PCons(h, t.deleteAll(key))
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content.subsetOf(this.content) &&
        res.forall(item => item.key != key)
    }

    def deleteAll (e : Pair[K, V]) = this - e

    def delete (key : K) = deleteFirst(key)

    def delete (e : Pair[K, V]) = deleteFirst(e)

    def init : PList[K, V] = {
      require(!isEmpty)
      ((this : @unchecked) match {
        case PCons(h, PNil()) =>
          PNil[K, V]()
        case PCons(h, t)      =>
          PCons[K, V](h, t.init)
      })
    } ensuring { (r : PList[K, V]) =>
      r.size == this.size - 1 &&
        r.content.subsetOf(this.content)
    }

    def last : Pair[K, V] = {
      require(!isEmpty)
      (this : @unchecked) match {
        case PCons(h, PNil()) => h
        case PCons(_, t)      => t.last
      }
    } ensuring { this.contains _ }

    def lastOption : Option[Pair[K, V]] = {
      this match {
        case PCons(h, t) => t.lastOption.orElse(Some(h))
        case PNil()      => None[Pair[K, V]]()
      }
    } ensuring { _.isDefined != this.isEmpty }

    def headOption : Option[Pair[K, V]] = {
      this match {
        case PCons(h, t) => Some(h)
        case PNil()      => None[Pair[K, V]]()
      }
    } ensuring { _.isDefined != this.isEmpty }

    def unique : PList[K, V] = this match {
      case PNil()      => PNil()
      case PCons(h, t) => PCons(h, t.unique - h)
    }

    def rotate (s : BigInt) : PList[K, V] = {
      if (isEmpty) PNil[K, V]()
      else drop(s mod size) ++ take(s mod size)
    } ensuring {
      res => res.size == this.size
    }

    def isEmpty = this match {
      case PNil() => true
      case _      => false
    }

    // Higher-order API
    def map[K2, V2] (f : Pair[K, V] => Pair[K2, V2]) : PList[K2, V2] = {
      this match {
        case PNil()      => PNil[K2, V2]()
        case PCons(h, t) => f(h) :: t.map(f)
      }
    } ensuring { _.size == this.size }

    def mapList[V2] (f : Pair[K, V] => V2) : List[V2] = {
      this match {
        case PNil()      => Nil[V2]()
        case PCons(h, t) => f(h) :: t.mapList(f)
      }
    } ensuring { _.size == this.size }

    def foldLeft[V2] (z : V2)(f : (V2, Pair[K, V]) => V2) : V2 = this match {
      case PNil()      => z
      case PCons(h, t) => t.foldLeft(f(z, h))(f)
    }

    def foldRight[V2] (z : V2)(f : (Pair[K, V], V2) => V2) : V2 = this match {
      case PNil()      => z
      case PCons(h, t) => f(h, t.foldRight(z)(f))
    }

    def scanLeft[K2, V2] (z : Pair[K2, V2])(f : (Pair[K2, V2], Pair[K, V]) => Pair[K2, V2]) : PList[K2, V2] = {
      this match {
        case PNil()      => z :: PNil[K2, V2]()
        case PCons(h, t) => z :: t.scanLeft(f(z, h))(f)
      }
    } ensuring { !_.isEmpty }

    def scanRight[K2, V2] (z : Pair[K2, V2])(f : (Pair[K, V], Pair[K2, V2]) => Pair[K2, V2]) : PList[K2, V2] = {
      this match {
        case PNil()      => z :: PNil[K2, V2]()
        case PCons(h, t) =>
          val rest@PCons(h1, _) = t.scanRight(z)(f)
          f(h, h1) :: rest
      }
    } ensuring { !_.isEmpty }

    def filter (p : Pair[K, V] => Boolean) : PList[K, V] = {
      this match {
        case PNil()              => PNil[K, V]()
        case PCons(h, t) if p(h) => PCons(h, t.filter(p))
        case PCons(_, t)         => t.filter(p)
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content.subsetOf(this.content) &&
        res.forall(p)
    }

    def filterNot (p : Pair[K, V] => Boolean) : PList[K, V] =
      filter(!p(_)) ensuring { res =>
        res.size <= this.size &&
          res.content.subsetOf(this.content) &&
          res.forall(!p(_))
      }

    def partition (p : Pair[K, V] => Boolean) : (PList[K, V], PList[K, V]) = {
      this match {
        case PNil()      => (PNil[K, V](), PNil[K, V]())
        case PCons(h, t) =>
          val (l1, l2) = t.partition(p)
          if (p(h)) (h :: l1, l2)
          else (l1, h :: l2)
      }
    } ensuring { res =>
      res._1 == filter(p) &&
        res._2 == filterNot(p)
    }

    // In case we implement for-comprehensions
    def withFilter (p : Pair[K, V] => Boolean) = filter(p)

    def forall (p : Pair[K, V] => Boolean) : Boolean = this match {
      case PNil()      => true
      case PCons(h, t) => p(h) && t.forall(p)
    }

    def exists (p : Pair[K, V] => Boolean) = !forall(!p(_))

    def find (p : Pair[K, V] => Boolean) : Option[Pair[K, V]] = {
      this match {
        case PNil()              => None[Pair[K, V]]()
        case PCons(h, t) if p(h) => Some(h)
        case PCons(_, t)         => t.find(p)
      }
    } ensuring { res =>
      res match {
        case Some(r) => (content contains r) && p(r)
        case None()  => true
      }
    }

    def groupBy[K2] (f : Pair[K, V] => K2) : Map[K2, PList[K, V]] = this match {
      case PNil()      => Map.empty[K2, PList[K, V]]
      case PCons(h, t) =>
        val key : K2 = f(h)
        val rest : Map[K2, PList[K, V]] = t.groupBy(f)
        val prev : PList[K, V] = if (rest isDefinedAt key) rest(key) else PNil[K, V]()
        (rest ++ Map((key, h :: prev))) : Map[K2, PList[K, V]]
    }

    def takeWhile (p : Pair[K, V] => Boolean) : PList[K, V] = {
      this match {
        case PCons(h, t) if p(h) => PCons(h, t.takeWhile(p))
        case _                   => PNil[K, V]()
      }
    } ensuring { res =>
      (res forall p) &&
        (res.size <= this.size) &&
        (res.content subsetOf this.content)
    }

    def dropWhile (p : Pair[K, V] => Boolean) : PList[K, V] = {
      this match {
        case PCons(h, t) if p(h) => t.dropWhile(p)
        case _                   => this
      }
    } ensuring { res =>
      (res.size <= this.size) &&
        (res.content subsetOf this.content) &&
        (res.isEmpty || !p(res.head))
    }

    def count (p : Pair[K, V] => Boolean) : BigInt = {
      this match {
        case PNil()      => BigInt(0)
        case PCons(h, t) =>
          (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
      }
    } ensuring {
      _ == this.filter(p).size
    }
  }

  /* Obtain a new list by removing the the FIRST occurrence of e from list. */
  @library
  def delete[K, V] (list : PList[K, V], e : Pair[K, V]) : PList[K, V] = list.delete(e)

  @library
  def permutation[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    if (l1 == PNil[K, V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res =>
    res ==>
      (l1.size == l2.size &&
        l1.content == l2.content)
  }

  def distinct[K, V] (list : PList[K, V]) : Boolean = {
    list match {
      case PNil()        => true
      case PCons(hd, tl) => !tl.contains(hd) && distinct(tl)
    }
  }

  @ignore
  def apply[K, V] (elems : (K, V)*) : PList[K, V] = {
    var l : PList[K, V] = PNil[K, V]()
    for (e <- elems) {
      l = PCons(Pair(e._1, e._2), l)
    }
    l.reverse
  }

  // 'PCons' Extractor
  //  object :: {
  //    @library
  //    def unapply[K, V] (l: PList[K, V]): Option[(Item[K, V], PList[K, V])] = l match {
  //      case PNil()       => None()
  //      case PCons(x, xs) => Some((x, xs))
  //    }
  //  }

}
