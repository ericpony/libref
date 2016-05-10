package libref.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import libref.collection._
import libref.spec.ListArray._
import libref.spec.ListIterator._
import libref.proof.ListLemmas._

abstract class ListADT[T] extends Collection[T] {
  def append (e : T) : ListADT[T]
  def head : T
  def isEmpty : Boolean = size != 0
  def prepend (e : T) : ListADT[T]
  def size : BigInt
  def tail : ListADT[T]
}

case class LinkedList[T] (list : List[T]) extends ListADT[T] {

  def append (e : T) : LinkedList[T] = LinkedList(list :+ e)

  def head : T = {
    require(!list.isEmpty)
    list.head
  }

  def iterator : Iterator[T] = ListIterator(list)

  def prepend (e : T) : LinkedList[T] = LinkedList(e :: list)

  def size : BigInt = list.size

  def tail : LinkedList[T] = {
    require(!list.isEmpty)
    LinkedList(list.tail)
  }

}

case class ArrayList[T] (array : ListArray[T]) /*extends ListADT[T]*/ {

  def append (e : T) : ArrayList[T] = {
    require(inv)
    ArrayList(array :+ e)
  } ensuring {
    res => res.inv because ListArrayLemmas.append_forall(array, e, (e : Option[T]) => e.isDefined)
  }

  def head : T = {
    require(inv && size > 0)
    val Some(v) = array.acc(0)
    v
  }

  def iterator : Iterator[T] = {
    require(inv)
    ListIterator(array.toList)
  }

  def prepend (e : T) : ArrayList[T] = {
    require(inv)
    ArrayList(array.shift(1).upd(0, e))
  } ensuring {
    res =>
    res.inv &&
    res.head == e &&
    res.array.toList == Cons(e, array.toList) &&
    res.size == size + 1
  }

  def size : BigInt = array.size

  def tail : ArrayList[T] = {
    require(inv && size > 0)
    ArrayList(array.drop(1))
  } ensuring {
    res => res.inv
  }

  def inv : Boolean = {
    array.array.forall(e => e.isDefined)
  }

}

object ArrayListLemmas {

  def prepend_head[T] (a : ArrayList[T], e : T) : Boolean = {
    require(a.inv)
    a.prepend(e).head == e
  } holds

  def to_list_size_eq[T] (a : ArrayList[T]) : Boolean = {
    require(a.inv)
    a.size == a.array.toList.size because {
      a.array.array match {
        case Nil() => trivial
        case Cons(None(), tl) => trivial
        case Cons(Some(hd), tl) => to_list_size_eq(ArrayList(ListArray(tl)))
      }
    }
  } holds
}

object LinkedListArrayListBisimulation {

  def bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T]) : Boolean = {
    a2.inv && a1.list == a2.array.toList
  }

  def append_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T], e : T) : Boolean = {
    require(bisim(a1, a2))
    val a3 : LinkedList[T] = a1.append(e)
    val a4 : ArrayList[T] = a2.append(e)
    bisim(a3, a4) because {
      (a1.list, a2.array.array) match {
        case (Nil(), Nil()) => trivial
        case (Nil(), Cons(hd2, tl2)) => trivial
        case (Cons(hd1, tl1), Nil()) => trivial
        case (Cons(hd1, tl1), Cons(None(), tl2)) => trivial
        case (Cons(hd1, tl1), Cons(Some(hd2), tl2)) => hd1 == hd2 && append_bisim(LinkedList(tl1), ArrayList(ListArray(tl2)), e)
      }
    }
  } holds

  def head_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T]) : Boolean = {
    require(bisim(a1, a2) && a1.size > 0 && a2.size > 0)
    val h1 : T = a1.head
    val h2 : T = a2.head
    h1 == h2
  } holds

  def iterator_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T]) : Boolean = {
    require(bisim(a1, a2))
    a1.iterator.toList == a2.iterator.toList
  } holds

  def prepend_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T], e : T) : Boolean = {
    require(bisim(a1, a2))
    val a3 = a1.prepend(e) : LinkedList[T]
    val a4 = a2.prepend(e) : ArrayList[T]
    bisim(a3, a4)
  } holds

  def size_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T]) : Boolean = {
    require(bisim(a1, a2))
    a1.size == a2.size because ArrayListLemmas.to_list_size_eq(a2)
  } holds

  def tail_bisim[T] (a1 : LinkedList[T], a2 : ArrayList[T]) : Boolean = {
    require(bisim(a1, a2) && a1.size > 0 && a2.size > 0)
    val a3 = a1.tail
    val a4 = a2.tail
    bisim(a3, a4)
  } holds

}



case class MapArrayList[T] (array : MapArray[T]) /*extends ListADT[T]*/ {

  def append (e : T) : MapArrayList[T] = {
    require(inv)
    MapArrayList(array :+ e)
  } ensuring { res =>
    res.size == size + 1 && res.inv
  }

  def head : T = {
    require(inv && size > 0)
    array(0)
  }

  def iterator : Iterator[T] = {
    require(inv)
    ListIterator(array.toList)
  }

  def prepend (e : T) : MapArrayList[T] = {
    require(inv)
    MapArrayList(array.prepend(e))
  } ensuring {
    res =>
    res.inv &&
    res.head == e because { MapArrayLemmas.acc_prepend(array, e, 0) } &&
    res.array.toList == Cons(e, array.toList) because {MapArrayLemmas.prepend_toList(array, e) } &&
    res.size == size + 1
  }

  def size : BigInt = array.size

  def tail : MapArrayList[T] = {
    require(inv)
    MapArrayList(array.drop(1))
  } ensuring {
    res => res.inv
  }

  def inv : Boolean = {
    array.inv
  }

}

object LinkedListMapArrayListBisimulation {

  def bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T]) : Boolean = {
    a2.inv && a1.list == a2.array.toList
  }

  def append_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T], e : T) : Boolean = {
    require(bisim(a1, a2))
    val a3 : LinkedList[T] = a1.append(e)
    val a4 : MapArrayList[T] = a2.append(e)
    bisim(a3, a4) because {
      MapArrayLemmas.snoc_toList(a2.array, e)
    }
  } holds

  def head_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T]) : Boolean = {
    require(bisim(a1, a2) && a1.size > 0 && a2.size > 0)
    val h1 : T = a1.head
    val h2 : T = a2.head
    h1 == h2
  } holds

  def iterator_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T]) : Boolean = {
    require(bisim(a1, a2))
    a1.iterator.toList == a2.iterator.toList
  } holds

  def prepend_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T], e : T) : Boolean = {
    require(bisim(a1, a2))
    val a3 = a1.prepend(e) : LinkedList[T]
    val a4 = a2.prepend(e) : MapArrayList[T]
    bisim(a3, a4) because { MapArrayLemmas.prepend_toList(a2.array, e) }
  } holds

  def size_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T]) : Boolean = {
    require(bisim(a1, a2))
    a1.size == a2.size
  } holds

  def tail_bisim[T] (a1 : LinkedList[T], a2 : MapArrayList[T]) : Boolean = {
    require(bisim(a1, a2) && a1.size > 0 && a2.size > 0)
    val a3 = a1.tail
    val a4 = a2.tail
    bisim(a3, a4) because { MapArrayLemmas.drop_toList(a2.array, 1) }
  } holds

}
