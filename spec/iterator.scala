package libref.spec

import leon.lang._
import leon.annotation._
import libref.collection._

abstract class Iterator[T] {
  /** Returns true if the next element is available. */
  def hasNext : Boolean

  /** Returns the next element. */
  def head : Option[T]

  /** Returns the next iteraotr with the head removed. */
  def next : Iterator[T]

  /** Returns the number of elements left to be enumerated. */
  def size : BigInt

  def toList: List[T]
}

case class ListIterator[T] (list : List[T]) extends Iterator[T] {
  def hasNext : Boolean = !list.isEmpty

  def head : Option[T] = list.headOption

  def next : ListIterator[T] = {
    require(!list.isEmpty)
    val Cons(_, tl) = list
    ListIterator(tl)
  }

  def size : BigInt = list.size

  def toList : List[T] = list
}

abstract class Iterable[T] {
  def iterator : Iterator[T]
}

abstract class Collection[T] extends Iterable[T]

case class CollectionImpl[T] () extends Collection[T] {
  def iterator : ListIterator[T] = ListIterator(Nil())
}
