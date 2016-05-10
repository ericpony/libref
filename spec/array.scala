package libref.spec

import libref.collection._
import libref.proof.ListLemmas
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import leon.lang._
import leon.proof._
import leon.annotation._
import scala.language.postfixOps
import scala.language.implicitConversions

case class EmptyArray[K, V] () extends FunctionalArray[K, V]

case class UpdatedArray[K, V] (a : FunctionalArray[K, V], i : K, e : V) extends FunctionalArray[K, V]

sealed abstract class FunctionalArray[K, V] {

  def acc (i : K) : Option[V] = {
    this match {
      case EmptyArray() => None()
      case UpdatedArray(a, j, e) if i == j => Some(e)
      case UpdatedArray(a, _, _) => a.acc(i)
    }
  }

  def upd (i : K, e : V) : FunctionalArray[K, V] = {
    UpdatedArray(this, i, e)
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def domain : Set[K] = {
    this match {
      case EmptyArray() => Set.empty
      case UpdatedArray(a, i, e) => Set(i) ++ a.domain
    }
  }

}

object FunctionalArray {

  def empty[K, V] : FunctionalArray[K, V] = EmptyArray()

}

object FunctionalArrayLemmas {

  def acc_upd_eq[K, V] (a : FunctionalArray[K, V], i : K, e : V, j : K) = {
    require(i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[K, V] (a : FunctionalArray[K, V], i : K, e : V, j : K) = {
    require(i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  @induct
  def acc_in_domain[K, V] (a : FunctionalArray[K, V], i : K) = {
    require(a.domain.contains(i))
    a.acc(i) match {
      case None() => false
      case Some(e) => true
    }
  } holds

  @induct
  def acc_out_domain[K, V] (a : FunctionalArray[K, V], i : K) = {
    require(!a.domain.contains(i))
    a.acc(i) == None[V]()
  } holds

}


sealed case class BoundedArray[T] (array : FunctionalArray[BigInt, T], size : BigInt) {

  def acc (i : BigInt) : Option[T] = {
    require(inv && vi(i))
    array.acc(i)
  }

  def upd (i : BigInt, e : T) : BoundedArray[T] = {
    require(inv && vi(i))
    BoundedArray(array.upd(i, e), size)
  } ensuring {
    res => res.inv && res.acc(i) == Some(e)
  }

  def srl (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), size + n)
      case UpdatedArray(a, i, e) => BoundedArray(UpdatedArray(BoundedArray(a, size).srl(n).array, i + n, e), size + n)
    }
  } ensuring {
    res => res.inv && res.size == size + n
  }

  def sll (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0 && n <= size)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), size - n)
      case UpdatedArray(a, i, e) if i < n => BoundedArray(a, size).sll(n)
      case UpdatedArray(a, i, e) => BoundedArray(UpdatedArray(BoundedArray(a, size).sll(n).array, i - n, e), size - n)
    }
  } ensuring {
    res => res.inv && res.size == size - n
  }

  def resize (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), n)
      case UpdatedArray(a, i, e) if i < n => BoundedArray(UpdatedArray(BoundedArray(a, size).resize(n).array, i, e), n)
      case UpdatedArray(a, i, e) => BoundedArray(a, size).resize(n)
    }
  } ensuring {
    res => res.inv && res.size == n
  }

  def vi (i : BigInt) : Boolean = {
    i >= 0 && i < size
  }

  def inv : Boolean = {
    size >= 0 && BoundedArray.domain_in_range(array, 0, size - 1)
  }

}

object BoundedArray {

  def empty[T] : BoundedArray[T] = BoundedArray(EmptyArray(), 0)

  def alloc[T] (size : BigInt) : BoundedArray[T] = BoundedArray(EmptyArray(), size)

  def domain_in_range[T] (array : FunctionalArray[BigInt, T], min : BigInt, max : BigInt) : Boolean = {
    array match {
      case EmptyArray() => true
      case UpdatedArray(a, i, e) => i >= min && i <= max && domain_in_range(a, min, max)
    }
  }

}

object BoundedArrayLemmas {

  def acc_upd_eq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && a.vi(j) && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  def acc_srl[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.inv && i >= 0 && j >= 0 && j < a.size)
    a.srl(i).acc(i + j) == a.acc(j) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, k, e) if k == j => trivial
        case UpdatedArray(b, k, e) => acc_srl(BoundedArray(b, a.size), i, j)
      }
    }
  } holds

  def acc_sll[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.inv && i >= 0 && j >= 0 && j < a.size - i)
    a.sll(i).acc(j) == a.acc(i + j) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, k, e) if k == i + j => trivial
        case UpdatedArray(b, k, e) => acc_sll(BoundedArray(b, a.size), i, j)
      }
    }
  } holds

  def acc_resize[T] (a : BoundedArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && n >= 0 && i < n)
    a.resize(n).acc(i) == a.acc(i) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, j, e) if j == i => trivial
        case UpdatedArray(b, j, e) => acc_resize(BoundedArray(b, a.size), n, i)
      }
    }
  } holds

}

sealed case class ListArray[T] (array : List[Option[T]]) {

  def apply (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    acc(i)
  }

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    array(i)
  }

  def upd (i : BigInt, e : T) : ListArray[T] = {
    require(i >= 0 && i < size)
    ListArray(array.updated(i, Some(e)))
  } ensuring {
    res => res.size == size && res.acc(i) == Some(e) because {
      ListLemmas.acc_updated_eq(array, i, Some(e), i)
    }
  }

  def size : BigInt = array.size

  def :+ (e : T) : ListArray[T] = {
    ListArray(array :+ Some(e))
  } ensuring {
    res => res.size == size + 1
  }

  def ++ (that : ListArray[T]) : ListArray[T] = {
    ListArray(array ++ that.array)
  } ensuring {
    res => res.size == size + that.size
  }

  def append (e : T) : ListArray[T] = {
    this :+ e
  } ensuring {
    res => res.size == size + 1
  }

  def append (that : ListArray[T]) : ListArray[T] = {
    this ++ that
  } ensuring {
    res => res.size == size + that.size
  }

  def shift (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    if (n == 0)
      this
    else
      ListArray(Cons(None[T](), shift(n - 1).array))
  } ensuring {
    res => res.size == size + n
  }

  def drop (n : BigInt) : ListArray[T] = {
    ListArray(array.drop(n))
  } ensuring {
    res => res.size == (
      if (n <= 0) size
      else if (n >= size) BigInt(0)
      else size - n
      )
  }

  def take (n : BigInt) : ListArray[T] = {
    ListArray(array.take(n))
  } ensuring {
    res => res.size == (
      if (n <= 0) BigInt(0)
      else if (n >= size) size
      else n
      )
  }

  def slice (from : BigInt, until : BigInt) : ListArray[T] = {
    require(from >= 0 && until >= from && until <= size)
    ListArray(array.slice(from, until))
  }

  def forall (p : Option[T] => Boolean) : Boolean = {
    array.forall(p)
  }

  def exists (p : Option[T] => Boolean) : Boolean = {
    array.exists(p)
  }

  def toList : List[T] = {
    array match {
      case Nil() => Nil[T]()
      case Cons(None(), tl) => ListArray(tl).toList
      case Cons(Some(hd), tl) => Cons(hd, ListArray(tl).toList)
    }
  }

}

object ListArray {

  @ignore
  def apply[T] (elems : T*) : ListArray[T] = {
    var l : ListArray[T] = ListArray.alloc[T](elems.size)
    var i = 0
    for (e <- elems) {
      l = l.upd(i, e)
      i = i + 1
    }
    l
  }

  def empty[T] : ListArray[T] = {
    ListArray[T](Nil[Option[T]]())
  } ensuring {
    res => res.size == 0
  }

  def alloc[T] (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    if (n == 0)
      ListArray(Nil[Option[T]]())
    else
      ListArray(Cons(None[T](), ListArray.alloc[T](n - 1).array))
  } ensuring {
    res => res.size == n && res.array.forall(e => !e.isDefined)
  }

}

object ListArrayLemmas {

  def acc_upd_eq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && j >= 0 && j < a.size && i != j)
    a.upd(i, e).acc(j) == a.acc(j) because ListLemmas.acc_updated_neq(a.array, i, Some(e), j)
  } holds

  def acc_append1[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a1.size)
    (a1 ++ a2).acc(i) == a1.acc(i) because {
      a1.array match {
        case Nil() => i == 0
        case Cons(hd, tl) if i == 0 => trivial
        case Cons(hd, tl) => acc_append1(ListArray(tl), a2, i - 1)
      }
    }
  } holds

  def acc_append1[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i >= 0 && i < a.size)
    (a :+ e).acc(i) == a.acc(i) because {
      a.array match {
        case Nil() => i == 0
        case Cons(hd, tl) if i == 0 => trivial
        case Cons(hd, tl) => acc_append1(ListArray(tl), e, i - 1)
      }
    }
  } holds

  def acc_append2[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a2.size)
    (a1 ++ a2).acc(a1.size + i) == a2.acc(i) because {
      a1.array match {
        case Nil() => trivial
        case Cons(hd, tl) => acc_append2(ListArray(tl), a2, i)
      }
    }
  } holds

  def acc_append2[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i == a.size)
    (a :+ e).acc(i) == Some(e) because {
      a.array match {
        case Nil() => trivial
        case Cons(hd, tl) => acc_append2(ListArray(tl), e, i - 1)
      }
    }
  } holds

  def acc_append[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a1.size + a2.size)
    if (i < a1.size)
      (a1 ++ a2).acc(i) == a1.acc(i) because acc_append1(a1, a2, i)
    else
      (a1 ++ a2).acc(i) == a2.acc(i - a1.size) because acc_append2(a1, a2, i - a1.size)
  } holds

  def acc_append[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i >= 0 && i <= a.size)
    if (i < a.size)
      (a :+ e).acc(i) == a.acc(i) because acc_append1(a, e, i)
    else
      (a :+ e).acc(i) == Some(e) because acc_append2(a, e, i)
  } holds

  def acc_shift[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && i >= 0 && i < a.size)
    a.shift(n).acc(i + n) == a.acc(i) because {
      if (n == 0) {
        trivial
      } else {
        acc_shift(a, n - 1, i)
      }
    }
  } holds

  def acc_drop[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && n <= a.size && i >= 0 && i < a.size - n)
    a.drop(n).acc(i) == a.acc(i + n) because ListLemmas.acc_drop(a.array, n, i)
  } holds

  def acc_take[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && i < n)
    a.take(n).acc(i) == a.acc(i) because ListLemmas.acc_take(a.array, n, i)
  } holds

  def shift_append_eq[T] (a : ListArray[T], n : BigInt) : Boolean = {
    require(n >= 0)
    a.shift(n) == ListArray.alloc(n) ++ a because {
      if (n == 0)
        trivial
      else
        shift_append_eq(a, n - 1)
    }
  } holds

  def append_drop_eq[T] (a1 : ListArray[T], a2 : ListArray[T]) : Boolean = {
    (a1 ++ a2).drop(a1.size) == a2 because ListLemmas.appendTakeDrop(a1.array, a2.array, a1.size)
  } holds

  def shift_drop_eq[T] (a : ListArray[T], n : BigInt) : Boolean = {
    require(n >= 0)
    a.shift(n).drop(n) == a because {
      shift_append_eq(a, n) && append_drop_eq(ListArray.alloc(n), a)
    }
  } holds

  def append_forall[T] (a : ListArray[T], e : T, p : Option[T] => Boolean) : Boolean = {
    require(a.array.forall(p) && p(Some(e)))
    (a :+ e).forall(p) because ListLemmas.append_forall(a.array, Some(e), p)
  } holds

  def append_forall[T] (a1 : ListArray[T], a2 : ListArray[T], p : Option[T] => Boolean) : Boolean = {
    require(a1.array.forall(p) && a2.array.forall(p))
    (a1 ++ a2).forall(p) because ListLemmas.append_forall(a1.array, a2.array, p)
  } holds

}

object IMap {

  def empty[T] = Map.empty[BigInt, T]

  def isDefinedBetween[T] (m : Map[BigInt, T], from : BigInt, until : BigInt) : Boolean = {
    if (from >= until)
      true
    else
      m.isDefinedAt(from) && isDefinedBetween(m, from + 1, until)
  }

  def defined_between_shrink[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, left : BigInt, right : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && left >= from && right <= until)
    isDefinedBetween(m, left, right) because {
      if (left >= right) trivial
      else if (left == from) defined_between_shrink(m, from + 1, until, left + 1, right)
      else defined_between_shrink(m, from + 1, until, left, right)
    }
  } holds

  def defined_between_tran[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    ((isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k)) ==> (isDefinedBetween(m, i, k) because {
      if (i >= j) defined_between_shrink(m, j, k, i, k)
      else defined_between_tran(m, i + 1, j, k)
    })) &&
      ((isDefinedBetween(m, i, k) && j >= i && j <= k) ==> (isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k) because {
        defined_between_shrink(m, i, k, i, j) && defined_between_shrink(m, i, k, j, k)
      }))
  } holds

  def defined_between_at[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, i : BigInt) : Boolean = {
    require(i >= from && i < until && isDefinedBetween(m, from, until))
    m.isDefinedAt(i) because {
      if (from >= until) trivial
      else if (i == from) trivial
      else defined_between_at(m, from + 1, until, i)
    }
  } holds

  def updated_defined_at[T] (m : Map[BigInt, T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.isDefinedAt(j))
    m.updated(i, e).isDefinedAt(j)
  } holds

  def updated_defined_between[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until))
    isDefinedBetween(m.updated(i, e), from, until) because {
      if (from >= until) trivial
      else updated_defined_between(m, i, e, from + 1, until)
    } &&
      ((i == from - 1) ==> isDefinedBetween(m.updated(i, e), from - 1, until) because {
        updated_defined_between(m, i, e, from, until)
      }) &&
      ((i == until) ==> isDefinedBetween(m.updated(i, e), from, until + 1)) because {
      updated_defined_between(m, i, e, from, until) && defined_between_tran(m.updated(i, e), from, until, until + 1)
    }
  } holds

  /* Assign */

  def assign_op[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Map[BigInt, T] = {
    if (from >= until) m
    else assign_op(m.updated(from, e), from + 1, until, e)
  }

  def assign_defined_between[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j))
    isDefinedBetween(assign_op(m, from, until, e), i, j) because {
      if (from >= until) trivial
      else {
        updated_defined_between(m, from, e, i, j) &&
          assign_defined_between(m.updated(from, e), from + 1, until, e, i, j)
      }
    }
  } holds

  def assign_defined_at[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt) : Boolean = {
    (i >= from && i < until || m.isDefinedAt(i)) ==> (assign_op(m, from, until, e).isDefinedAt(i) because {
      if (i >= from && i < until) assign_defined_at(m.updated(from, e), from + 1, until, e, i)
      else assign_defined_between(m, from, until, e, i, i + 1)
    })
  } holds

  private def assign_defined_between[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Boolean = {
    isDefinedBetween(assign_op(m, from, until, e), from, until) because {
      if (from >= until) trivial
      else {
        assign_defined_at(m.updated(from, e), from + 1, until, e, from) &&
          assign_defined_between(m.updated(from, e), from + 1, until, e)
      }
    }
  } holds

  def assign[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Map[BigInt, T] = {
    assign_op(m, from, until, e)
  } ensuring { res =>
    isDefinedBetween(res, from, until) because assign_defined_between(m, from, until, e)
  }

  def acc_assign[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt) : Boolean = {
    require(assign_defined_at(m, from, until, e, i))
    if (i >= from && i < until) assign(m, from, until, e)(i) == e because {
      acc_assign(m.updated(from, e), from + 1, until, e, i)
    } else if (m.isDefinedAt(i)) assign(m, from, until, e)(i) == m(i) because {
      if (from >= until) assign(m, from, until, e)(i) == m(i)
      else updated_defined_at(m, from, e, i) && acc_assign(m.updated(from, e), from + 1, until, e, i)
    } else trivial
  } holds

  /* Copy */

  /**
    * Copy a segment of elements in m1 to m2 with an absolute offset, that is,
    * m2[offset] := m1[from], m2[offset + 1] := m1[from + 1], ..., m2[offset + until - from - 1] := m1[until - 1]
    */
  private def copy_op[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt) : Map[BigInt, T] = {
    require(isDefinedBetween(m1, from, until))
    if (from >= until) m2
    else copy_op(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1)
  }

  def copy_defined_between[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && isDefinedBetween(m2, i, j))
    isDefinedBetween(copy_op(m1, m2, from, until, offset), i, j) because {
      if (from >= until) trivial
      else {
        updated_defined_between(m2, offset, m1(from), i, j) &&
          copy_defined_between(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i, j)
      }
    }
  } holds

  def copy_defined_at[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until))
    if (i >= offset && i < offset + until - from) copy_op(m1, m2, from, until, offset).isDefinedAt(i) because {
      copy_defined_at(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i)
    } else if (m2.isDefinedAt(i)) copy_op(m1, m2, from, until, offset).isDefinedAt(i) because {
      copy_defined_between(m1, m2, from, until, offset, i, i + 1)
    } else trivial
  } holds

  private def copy_defined_between[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until))
    isDefinedBetween(copy_op(m1, m2, from, until, offset), offset, offset + until - from) because {
      if (from >= until) trivial
      else {
        copy_defined_between(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1) &&
          copy_defined_at(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, offset)
      }
    }
  } holds

  def copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt) : Map[BigInt, T] = {
    require(isDefinedBetween(m1, from, until))
    copy_op(m1, m2, from, until, offset)
  } ensuring { res =>
    isDefinedBetween(res, offset, offset + until - from) because {
      copy_defined_between(m1, m2, from, until, offset)
    }
  }

  private def acc_copy_out[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && m2.isDefinedAt(i) && (i < offset || i >= offset + until - from) && copy_defined_at(m1, m2, from, until, offset, i))
    copy(m1, m2, from, until, offset)(i) == m2(i) because {
      if (from >= until) trivial
      else acc_copy_out(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i)
    }
  } holds

  private def acc_copy_in[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && i >= offset && i < offset + until - from &&
      copy_defined_at(m1, m2, from, until, offset, i) && defined_between_at(m1, from, until, i - offset + from))
    copy(m1, m2, from, until, offset)(i) == m1(i - offset + from) because {
      if (i == offset) acc_copy_out(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i)
      else acc_copy_in(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i)
    }
  } holds

  def acc_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until))
    if (i >= offset && i < offset + until - from) acc_copy_in(m1, m2, from, until, offset, i)
    else if (m2.isDefinedAt(i)) acc_copy_out(m1, m2, from, until, offset, i)
    else trivial
  } holds

  /* To List */

  def toList[T] (m : Map[BigInt, T], from : BigInt, until : BigInt) : List[T] = {
    require(isDefinedBetween(m, from, until))
    if (from >= until) Nil[T]()
    else Cons(m(from), toList(m, from + 1, until))
  } ensuring { res =>
    res.size == (
      if (from <= until) until - from
      else BigInt(0)
      )
  }

  def acc_toList[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && i >= 0 && i < until - from && defined_between_at(m, from, until, i + from))
    toList(m, from, until)(i) == m(i + from) because {
      if (i == 0) trivial
      else acc_toList(m, from + 1, until, i - 1)
    }
  } holds

  def updated_toList[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && (i < from || i >= until) && updated_defined_between(m, i, e, from, until))
    toList(m.updated(i, e), from, until) == toList(m, from, until) because {
      updated_toList(m, i, e, from + 1, until)
    }
  } holds

  def toList_cons[T] (m : Map[BigInt, T], i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i < j)
    Cons(m(i), toList(m, i + 1, j)) == toList(m, i, j)
  } holds

  def toList_snoc[T] (m : Map[BigInt, T], i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i < j && defined_between_shrink(m, i, j, i, j - 1) && defined_between_at(m, i, j, j - 1))
    toList(m, i, j - 1) :+ m(j - 1) == toList(m, i, j) because {
      if (i == j - 1) trivial
      else toList_snoc(m, i + 1, j)
    }
  } holds

  def toList_snoc[T] (m : Map[BigInt, T], e : T, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i <= j && updated_defined_between(m, j, e, i, j))
    toList(m.updated(j, e), i, j + 1) == toList(m, i, j) :+ e because {
      if (i == j) trivial
      else toList_snoc(m, e, i + 1, j)
    }
  } holds

  def toList_append[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, k) && i <= j && j <= k && defined_between_tran(m, i, j, k))
    toList(m, i, j) ++ toList(m, j, k) == toList(m, i, k) because {
      if (i == j) trivial
      else toList_append(m, i + 1, j, k)
    }
  } holds

  def toList_contains[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && k >= i && k < j && defined_between_at(m, i, j, k))
    toList(m, i, j).contains(m(k)) because {
      if (i == k) trivial
      else toList_contains(m, i + 1, j, k)
    }
  } holds

  def toList_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until))
    toList(copy(m1, m2, from, until, offset), offset, offset + until - from) == toList(m1, from, until) because {
      if (from >= until) trivial
      else {
        toList_copy(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1) &&
          acc_copy(m1, m2, from, until, offset, offset)
      }
    }
  } holds

  def toList_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && isDefinedBetween(m2, i, j) &&
      (i < offset && j <= offset || i >= offset + until - from && j >= offset + until - from || i >= j) &&
      copy_defined_between(m1, m2, from, until, offset, i, j)
    )
    toList(copy(m1, m2, from, until, offset), i, j) == toList(m2, i, j) because {
      if (from >= until || i >= j) trivial
      else {
        acc_copy(m1, m2, from, until, offset, i) &&
          toList_copy(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, i, j) &&
          updated_toList(m2, offset, m1(from), i, j)
      }
    }
  } holds

  def toList_drop[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && n >= 0 && defined_between_shrink(m, from, until, from + n, until))
    toList(m, from, until).drop(n) == toList(m, from + n, until) because {
      if (from >= until || from + n >= until || n == 0) trivial
      else {
        defined_between_shrink(m, from, until, from + 1, until) &&
          toList_drop(m, from + 1, until, n - 1)
      }
    }
  } holds

  def toList_take[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until))
    if (n <= 0) toList(m, from, until).take(n) == Nil[T]()
    else if (n >= until - from) {
      if (from >= until) trivial
      else toList_take(m, from + 1, until, n - 1)
    } else defined_between_shrink(m, from, until, from, from + n) && toList(m, from, until).take(n) == toList(m, from, from + n) because {
      if (from >= until) trivial
      else if (n == 1) trivial
      else toList_take(m, from + 1, until, n - 1)
    }
  } holds

  /* Swap */

  def swap[T] (m : Map[BigInt, T], i : BigInt, j : BigInt) : Map[BigInt, T] = {
    require(m.isDefinedAt(i) && m.isDefinedAt(j))
    m.updated(i, m(j)).updated(j, m(i))
  } ensuring { res =>
    res(i) == m(j) && res(j) == m(i)
  }

  def acc_swap[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(m.isDefinedAt(i) && m.isDefinedAt(j) && m.isDefinedAt(k))
    swap(m, i, j)(k) == (
      if (k == i) m(j)
      else if (k == j) m(i)
      else m(k)
      )
  } holds

  def swap_defined_between[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && m.isDefinedAt(n1) && m.isDefinedAt(n2))
    isDefinedBetween(swap(m, n1, n2), i, j) because { swap_defined_between(m, i + 1, j, n1, n2) }
  } holds

  def swap_toList_comm[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && m.isDefinedAt(n1) && m.isDefinedAt(n2) && swap_defined_between(m, i, j, n1, n2))
    toList(swap(m, n1, n2), i, j) == toList(swap(m, n2, n1), i, j) because {
      if (i >= j) trivial
      else swap_toList_comm(m, i + 1, j, n1, n2)
    }
  } holds

  def swap_toList_eq[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && m.isDefinedAt(n1) && m.isDefinedAt(n2) && swap_defined_between(m, i, j, n1, n2))
    ((n1 == n2) ==> (toList(swap(m, n1, n2), i, j) == toList(m, i, j))) &&
      (((n1 < i || n1 >= j) && (n2 < i || n2 >= j)) ==> (toList(swap(m, n1, n2), i, j) == toList(m, i, j) because {
        if (i >= j) trivial
        else swap_toList_eq(m, i + 1, j, n1, n2)
      }))
  } holds

  def swap_toList_contains_strict[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt, k : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && m.isDefinedAt(n1) && m.isDefinedAt(n2) &&
      ((k >= i && k < j) ==> defined_between_at(m, i, j, k)) && swap_defined_between(m, i, j, n1, n2))
    (
      ((n1 < i || n1 >= j) && (n2 < i || n2 >= j) && (k >= i && k < j)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        swap_toList_eq(m, i, j, n1, n2) && toList_contains(m, i, j, k)
      })
      ) && (
      ((n1 < i || n1 >= j) && (n2 >= i && n2 < j) && (k >= i && k < j && k != n2 || k == n1)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        if (i == k) trivial
        else if (i == n2) {
          if (k >= i && k < j && k != n2) swap_toList_contains_strict(m, i + 1, j, n1, n2, k)
          else trivial
        } else
          swap_toList_contains_strict(m, i + 1, j, n1, n2, k)
      })
      ) && (
      ((n1 >= i && n1 < j) && (n2 >= i && n2 < j) && (k >= i && k < j) && (n1 <= n2)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        if (i == n1 && k == n2 || i == n2 && k == n1) trivial
        else if (i == k) {
          if (k == n1) swap_toList_contains_strict(m, i + 1, j, n1, n2, k)
          else swap_toList_contains_strict(m, i + 1, j, n1, n2, k)
        } else swap_toList_contains_strict(m, i + 1, j, n1, n2, k)
      })
      )
  } holds

  def swap_toList_contains[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt, k : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && m.isDefinedAt(n1) && m.isDefinedAt(n2) &&
      ((k >= i && k < j) ==> defined_between_at(m, i, j, k)) && swap_defined_between(m, i, j, n1, n2))
    (
      ((n1 < i || n1 >= j) && (n2 < i || n2 >= j) && (k >= i && k < j)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        swap_toList_contains_strict(m, i, j, n1, n2, k)
      })
      ) && (
      ((n1 < i || n1 >= j) && (n2 >= i && n2 < j) && (k >= i && k < j && k != n2 || k == n1)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        swap_toList_contains_strict(m, i, j, n1, n2, k)
      })
      ) && (
      ((n1 >= i && n1 < j) && (n2 < i || n2 >= j) && (k >= i && k < j && k != n1 || k == n2)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        swap_toList_comm(m, i, j, n1, n2) && swap_toList_contains_strict(m, i, j, n2, n1, k)
      })
      ) && (
      ((n1 >= i && n1 < j) && (n2 >= i && n2 < j) && (k >= i && k < j)) ==> (toList(swap(m, n1, n2), i, j).contains(m(k)) because {
        if (n1 <= n2) swap_toList_contains_strict(m, i, j, n1, n2, k)
        else swap_toList_comm(m, i, j, n1, n2) && swap_toList_contains_strict(m, i, j, n2, n1, k)
      })
      )
  } holds

  /* Used to prove swap_toList_perm */
  def swap_toList_append[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i <= n1 && n1 < n2 && n2 < j &&
      defined_between_at(m, i, j, n1) && defined_between_at(m, i, j, n2) &&
      defined_between_shrink(m, i, j, i, n1) && defined_between_shrink(m, i, j, n1 + 1, n2) &&
      defined_between_shrink(m, i, j, n2 + 1, j) &&
      swap_defined_between(m, i, j, n1, n2))
    toList(swap(m, n1, n2), i, j) == toList(m, i, n1) ++ Cons(m(n2), Nil[T]()) ++ toList(m, n1 + 1, n2) ++ Cons(m(n1), Nil[T]()) ++ toList(m, n2 + 1, j) because {
      swap_toList_eq(m, i, n1, n1, n2) && swap_toList_eq(m, n1 + 1, n2, n1, n2) && swap_toList_eq(m, n2 + 1, j, n1, n2) &&
        toList_append(swap(m, n1, n2), i, n2 + 1, j) &&
        toList_append(swap(m, n1, n2), i, n2, n2 + 1) &&
        toList_append(swap(m, n1, n2), i, n1 + 1, n2) &&
        toList_append(swap(m, n1, n2), i, n1, n1 + 1)
    }
  } holds

  def swap_toList_perm[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, n1 : BigInt, n2 : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i <= n1 && n1 < j && i <= n2 && n2 < j &&
      defined_between_at(m, i, j, n1) && defined_between_at(m, i, j, n2) && swap_defined_between(m, i, j, n1, n2))
    permutation(toList(swap(m, n1, n2), i, j), toList(m, i, j)) because {
      if (n1 == n2) swap_toList_eq(m, i, j, n1, n2) && permutation_refl(toList(m, i, j))
      else if (n1 <= n2) {
        swap_toList_append(m, i, j, n1, n2) &&
          toList_append(m, i, n2 + 1, j) &&
          toList_append(m, i, n2, n2 + 1) &&
          toList_append(m, i, n1 + 1, n2) &&
          toList_append(m, i, n1, n1 + 1) &&
          append5_swap2_perm(toList(m, i, n1), Cons(m(n2), Nil[T]()), toList(m, n1 + 1, n2), Cons(m(n1), Nil[T]()), toList(m, n2 + 1, j))
      } else {
        swap_toList_comm(m, i, j, n1, n2) && swap_toList_perm(m, i, j, n2, n1)
      }
    }
  } holds

  /* Forall && Exists */

  def forall[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, p : T => Boolean) : Boolean = {
    require(isDefinedBetween(m, from, until))
    if (from >= until) true
    else p(m(from)) && forall(m, from + 1, until, p)
  } ensuring { res =>
    res ==> !exists(m, from, until, (x : T) => !p(x))
  }

  def exists[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, p : T => Boolean) : Boolean = {
    require(isDefinedBetween(m, from, until))
    if (from >= until) false
    else p(m(from)) || exists(m, from + 1, until, p)
  } ensuring { res =>
    res ==> !forall(m, from, until, (x : T) => !p(x))
  }

  def forall_shrink[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, p : T => Boolean, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && forall(m, from, until, p) && i >= from && j <= until && defined_between_shrink(m, from, until, i, j))
    forall(m, i, j, p) because {
      if (i >= j) trivial
      else if (i == from) forall_shrink(m, from + 1, until, p, i + 1, j)
      else forall_shrink(m, from + 1, until, p, i, j)
    }
  } holds

  def forall_tran[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt, p : T => Boolean) : Boolean = {
    require(isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k) && defined_between_tran(m, i, j, k))
    if (forall(m, i, j, p) && forall(m, j, k, p)) forall(m, i, k, p) because {
      if (i >= j) forall_shrink(m, j, k, p, i, k)
      else forall_tran(m, i + 1, j, k, p)
    } else if (forall(m, i, k, p) && j >= i && j <= k) forall(m, i, j, p) && forall(m, j, k, p) because {
      forall_shrink(m, i, k, p, i, j) && forall_shrink(m, i, k, p, j, k)
    } else
      trivial
  } holds

  def updated_forall[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt, p : T => Boolean) : Boolean = {
    require(isDefinedBetween(m, from, until) && updated_defined_between(m, i, e, from, until))
    ((forall(m, from, until, p) && (i < from || i >= until)) ==> forall(m.updated(i, e), from, until, p) because {
      if (from >= until) trivial
      else updated_forall(m, i, e, from + 1, until, p)
    }) &&
      ((forall(m, from, until, p) && i == from - 1 && p(e)) ==> forall(m.updated(i, e), from - 1, until, p) because {
        if (from >= until) trivial
        else updated_forall(m, i, e, from + 1, until, p)
      }) &&
      ((forall(m, from, until, p) && i == until && p(e)) ==> forall(m.updated(i, e), from, until + 1, p) because {
        if (from >= until) trivial
        else updated_forall(m, i, e, from + 1, until, p)
      }) &&
      ((forall(m.updated(i, e), from, until, p) && (i < from || i >= until)) ==> forall(m, from, until, p))
  } holds

  def copy_forall[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, p : T => Boolean) : Boolean = {
    require(isDefinedBetween(m1, from, until))
    (
      (forall(m1, from, until, p) ==> forall(copy(m1, m2, from, until, offset), offset, offset + until - from, p)) &&
        (forall(copy(m1, m2, from, until, offset), offset, offset + until - from, p) ==> forall(m1, from, until, p))
      ) because {
      if (forall(m1, from, until, p) || forall(copy(m1, m2, from, until, offset), offset, offset + until - from, p)) {
        if (from >= until) trivial
        else {
          acc_copy(m1, m2, from, until, offset, offset) &&
            copy_forall(m1, m2.updated(offset, m1(from)), from + 1, until, offset + 1, p)
        }
      } else trivial
    }
  } holds

  def copy_forall[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, offset : BigInt, p : T => Boolean,
                      i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && isDefinedBetween(m2, i, j) && (j <= offset || i >= offset + until - from) &&
      copy_defined_between(m1, m2, from, until, offset, i, j))
    (
      (forall(m2, i, j, p) ==> forall(copy(m1, m2, from, until, offset), i, j, p)) &&
        (forall(copy(m1, m2, from, until, offset), i, j, p) ==> forall(m2, i, j, p))
      ) because {
      if (from >= until || i >= j) trivial
      else {
        acc_copy(m1, m2, from, until, offset, i) &&
          copy_forall(m1, m2, from, until, offset, p, i + 1, j)
      }
    }
  } holds

}

sealed case class MapArray[T] (map : Map[BigInt, T], from : BigInt, until : BigInt) {

  def :+ (e : T) : MapArray[T] = {
    require(inv)
    snoc(e)
  } ensuring { res =>
    res.size == size + 1 && res.inv
  }

  def ++ (m : MapArray[T]) : MapArray[T] = {
    require(inv && m.inv)
    append(m)
  } ensuring { res =>
    res.size == size + m.size && res.inv
  }

  def append (m : MapArray[T]) : MapArray[T] = {
    require(inv && m.inv)
    MapArray(IMap.copy(m.map, map, m.from, m.until, until), from, until + m.size)
  } ensuring { res =>
    res.size == size + m.size && res.inv because {
      IMap.copy_defined_between(m.map, map, m.from, m.until, until, from, until) &&
        IMap.defined_between_tran(res.map, from, until, res.until)
    }
  }

  def apply (i : BigInt) : T = {
    require(inv && i >= 0 && i < size && IMap.defined_between_at(map, from, until, from + i))
    map.apply(from + i)
  }

  def drop (n : BigInt) : MapArray[T] = {
    require(inv)
    if (n <= 0) this
    else if (n >= size) MapArray.empty[T]
    else MapArray(map, from + n, until)
  } ensuring { res =>
    res.size == (
      if (n <= 0) size
      else if (n >= size) BigInt(0)
      else size - n
      ) && res.inv because {
      if (n <= 0 || n >= size) trivial
      else IMap.defined_between_shrink(map, from, until, from + n, until)
    }
  }

  def exists (p : T => Boolean) : Boolean = {
    require(inv)
    IMap.exists(map, from, until, p)
  } ensuring { res =>
    res ==> !forall(!p(_))
  }

  def forall (p : T => Boolean) : Boolean = {
    require(inv)
    IMap.forall(map, from, until, p)
  } ensuring { res =>
    res ==> !exists(!p(_))
  }

  def isEmpty : Boolean = {
    require(inv)
    size == 0
  }

  def prepend (e : T) : MapArray[T] = {
    require(inv)
    MapArray(map.updated(from - 1, e), from - 1, until)
  } ensuring { res =>
    res.size == size + 1 && res.inv because IMap.updated_defined_between(map, from - 1, e, from, until)
  }

  def rotate (n : BigInt) : MapArray[T] = {
    require(inv)
    if (isEmpty) MapArray.empty[T]
    else drop(n mod size) ++ take(n mod size)
  } ensuring { res =>
    res.size == size && res.inv
  }

  def size : BigInt = until - from

  def snoc (e : T) : MapArray[T] = {
    require(inv)
    MapArray(map.updated(until, e), from, until + 1)
  } ensuring { res =>
    res.size == size + 1 && res.inv because IMap.updated_defined_between(map, until, e, from, until)
  }

  def swap (i : BigInt, j : BigInt) : MapArray[T] = {
    require(inv && i >= 0 && i < size && j >= 0 && j < size &&
      IMap.defined_between_at(map, from, until, from + i) && IMap.defined_between_at(map, from, until, from + j))
    updated(i, this (j)).updated(j, this (i))
  } ensuring { res =>
    res.size == size && res.inv because {
      IMap.updated_defined_between(map, i, this (j), from, until) && IMap.updated_defined_between(updated(i, this (j)).map, j, this (i), from, until)
    } && res(i) == this (j) && res(j) == this (i)
  }

  def take (n : BigInt) : MapArray[T] = {
    require(inv)
    if (n <= 0) MapArray.empty[T]
    else if (n >= size) this
    else MapArray(map, from, from + n)
  } ensuring { res =>
    res.size == (
      if (n <= 0) BigInt(0)
      else if (n >= size) size
      else n
      ) && res.inv because {
      if (n <= 0 || n >= size) trivial
      else IMap.defined_between_shrink(map, from, until, from, from + n)
    }
  }

  def toList : List[T] = {
    require(inv)
    IMap.toList(map, from, until)
  } ensuring { res =>
    res.size == size
  }

  def updated (i : BigInt, e : T) : MapArray[T] = {
    require(inv && i >= 0 && i < size)
    MapArray(map.updated(from + i, e), from, until)
  } ensuring { res =>
    res.size == size && res.inv because {
      IMap.updated_defined_between(map, from + i, e, from, until)
    }
  }

  def inv : Boolean = {
    size >= 0 && IMap.isDefinedBetween(map, from, until)
  }

}

object MapArray {

  def empty[T] : MapArray[T] = {
    MapArray(IMap.empty[T], 0, 0)
  } ensuring { res =>
    res.size == 0 && res.inv
  }

  def create[T] (n : BigInt, e : T) : MapArray[T] = {
    require(n >= 0)
    MapArray(IMap.assign(IMap.empty[T], 0, n, e), 0, n)
  } ensuring { res =>
    res.size == n && res.inv
  }

}

object MapArrayLemmas {

  implicit def to_imap[T] (m : MapArray[T]) : Map[BigInt, T] = m.map

  def index_defined[T] (m : MapArray[T], i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size)
    IMap.defined_between_at(m, m.from, m.until, m.from + i)
  }

  def acc_updated_eq[T] (m : MapArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && i == j)
    m.updated(i, e)(j) == e
  } holds

  def acc_updated_neq[T] (m : MapArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && j >= 0 && j < m.size && i != j && index_defined(m, j))
    m.updated(i, e)(j) == m(j)
  } holds

  def acc_snoc[T] (m : MapArray[T], e : T, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i <= m.size)
    (m :+ e) (i) == (
      if (i >= 0 && i < m.size) m(i)
      else e
      )
  } holds

  def acc_append[T] (m1 : MapArray[T], m2 : MapArray[T], i : BigInt) : Boolean = {
    require(m1.inv && m2.inv && i >= 0 && i < m1.size + m2.size)
    (m1 ++ m2) (i) == (
      if (i >= 0 && i < m1.size) m1(i)
      else m2(i - m1.size)
      ) because {
      IMap.acc_copy(m2, m1, m2.from, m2.until, m1.until, m1.from + i)
    }
  } holds

  def acc_drop[T] (m : MapArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(m.inv)
    if (n <= 0 && i >= 0 && i < m.size) m.drop(n)(i) == m(i) because { index_defined(m, i) }
    else if (n > 0 && i >= 0 && i < m.size - n) m.drop(n)(i) == m(i + n) because { index_defined(m.drop(n), i) }
    else trivial
  } holds

  def acc_prepend[T] (m : MapArray[T], e : T, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i <= m.size)
    if (i == 0) m.prepend(e)(i) == e
    else m.prepend(e)(i) == m(i - 1)
  } holds

  def acc_rotate[T] (m : MapArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size)
    (if (i < m.size - (n mod m.size)) m.rotate(n)(i) == m(i + (n mod m.size))
    else m.rotate(n)(i) == m(i - m.size + (n mod m.size))) because {
      acc_append(m.drop(n mod m.size), m.take(n mod m.size), i) && (
        if (i < m.size - (n mod m.size)) acc_drop(m, n mod m.size, i)
        else acc_take(m, n mod m.size, i - m.size + (n mod m.size))
        )
    }
  } holds

  def acc_swap[T] (m : MapArray[T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && j >= 0 && j < m.size && k >= 0 && k < m.size &&
      index_defined(m, i) && index_defined(m, j) && index_defined(m, k))
    m.swap(i, j)(k) == (
      if (k == i) m(j)
      else if (k == j) m(i)
      else m(k)
      )
  } holds

  def acc_take[T] (m : MapArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < n && i < m.size && index_defined(m, i) && index_defined(m.take(n), i))
    m.take(n)(i) == m(i)
  } holds

  def acc_toList[T] (m : MapArray[T], i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && index_defined(m, i))
    m.toList(i) == m(i) because { IMap.acc_toList(m, m.from, m.until, i) }
  } holds

  def snoc_toList[T] (m : MapArray[T], e : T) : Boolean = {
    require(m.inv)
    (m :+ e).toList == m.toList :+ e because {
      IMap.toList_snoc(m :+ e, m.from, m.until + 1) &&
        IMap.updated_toList(m, m.until, e, m.from, m.until)
    }
  } holds

  def append_toList[T] (m1 : MapArray[T], m2 : MapArray[T]) : Boolean = {
    require(m1.inv && m2.inv)
    (m1 ++ m2).toList == m1.toList ++ m2.toList because {
      if (m1.size == 0) IMap.toList_copy(m2, m1, m2.from, m2.until, m1.until)
      else {
        IMap.toList_append(m1 ++ m2, m1.from, m1.until, m1.until + m2.size) &&
          IMap.toList_copy(m2, m1, m2.from, m2.until, m1.until, m1.from, m1.until) &&
          IMap.toList_copy(m2, m1, m2.from, m2.until, m1.until)
      }
    }
  } holds

  def drop_toList[T] (m : MapArray[T], n : BigInt) : Boolean = {
    require(m.inv)
    m.drop(n).toList == m.toList.drop(n) because {
      if (n <= 0) trivial
      else IMap.toList_drop(m, m.from, m.until, n)
    }
  } holds

  def prepend_toList[T] (m : MapArray[T], e : T) : Boolean = {
    require(m.inv)
    m.prepend(e).toList == Cons(e, m.toList) because { IMap.updated_toList(m, m.from - 1, e, m.from, m.until) }
  } holds

  def rotate_toList[T] (m : MapArray[T], n : BigInt) : Boolean = {
    require(m.inv)
    m.rotate(n).toList == m.toList.rotate(n) because {
      if (m.isEmpty) trivial
      else {
        append_toList(m.drop(n mod m.size), m.take(n mod m.size)) &&
          drop_toList(m, n mod m.size) && take_toList(m, n mod m.size)
      }
    }
  } holds

  def take_toList[T] (m : MapArray[T], n : BigInt) : Boolean = {
    require(m.inv)
    m.take(n).toList == m.toList.take(n) because {
      if (n <= 0) trivial
      else if (n >= m.size) ListLemmas.take_all(m.toList, n)
      else IMap.toList_take(m, m.from, m.until, n)
    }
  } holds

  def swap_toList_perm[T] (m : MapArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && j >= 0 && j < m.size)
    permutation(m.swap(i, j).toList, m.toList) because {
      IMap.swap_toList_perm(m, m.from, m.until, m.from + i, m.from + j)
    }
  } holds

  def acc_forall[T] (m : MapArray[T], p : T => Boolean, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && m.forall(p))
    p(m(i)) because {
      if (i == 0) trivial
      else acc_forall(MapArray(m.map, m.from + 1, m.until), p, i - 1)
    }
  } holds

  def take_forall[T] (m : MapArray[T], n : BigInt, p : T => Boolean) : Boolean = {
    require(m.inv && m.forall(p))
    m.take(n).forall(p) because {
      if (n <= 0) trivial
      else if (n >= m.size) trivial
      else IMap.forall_shrink(m, m.from, m.until, p, m.from, m.from + n)
    }
  } holds

  def append_forall[T] (m1 : MapArray[T], m2 : MapArray[T], p : T => Boolean) : Boolean = {
    require(m1.inv && m2.inv)
    (
      ((m1 ++ m2).forall(p) ==> (m1.forall(p) && m2.forall(p))) &&
        ((m1.forall(p) && m2.forall(p)) ==> (m1 ++ m2).forall(p))
      ) because {
      if ((m1 ++ m2).forall(p)) {
        IMap.forall_shrink(m1 ++ m2, m1.from, m1.until + m2.size, p, m1.from, m1.until) &&
          IMap.copy_forall(m2, m1, m2.from, m2.until, m1.until, p, m1.from, m1.until) &&
          IMap.forall_shrink(m1 ++ m2, m1.from, m1.until + m2.size, p, m1.until, m1.until + m2.size) &&
          IMap.copy_forall(m2, m1, m2.from, m2.until, m1.until, p)
      } else if (m1.forall(p) && m2.forall(p)) {
        IMap.copy_forall(m2, m1, m2.from, m2.until, m1.until, p, m1.from, m1.until) &&
          IMap.copy_forall(m2, m1, m2.from, m2.until, m1.until, p) &&
          IMap.forall_tran(m1 ++ m2, m1.from, m1.until, m1.until + m2.size, p)
      } else trivial
    }
  } holds

  def snoc_forall[T] (m : MapArray[T], e : T, p : T => Boolean) : Boolean = {
    require(m.inv)
    ((m :+ e).forall(p) ==> (m.forall(p) && p(e) because {
      IMap.forall_shrink(m :+ e, m.from, m.until + 1, p, m.from, m.until) &&
        IMap.forall_shrink(m :+ e, m.from, m.until + 1, p, m.until, m.until + 1) &&
        IMap.updated_forall(m, m.until, e, m.from, m.until, p)
    })) &&
      ((m.forall(p) && p(e)) ==> (m :+ e).forall(p) because {
        IMap.updated_forall(m, m.until, e, m.from, m.until, p)
      })
  } holds

}
