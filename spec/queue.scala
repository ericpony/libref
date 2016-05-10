package libref.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import libref.collection._
import libref.spec.ListArray._

/*
abstract class Queue[T] {
  def dequeue : Queue[T]
  def enqueue (e : T) : Queue[T]
  def first : T
  def isEmpty : Boolean = size == 0
  def size : BigInt
}
*/

sealed case class ListQueue[T] (list : List[T]) /*extends Queue[T]*/ {

  def dequeue : ListQueue[T] = {
    require(size > 0)
    ListQueue(list.tail)
  } ensuring {
    res => res.size == size - 1
  }

  def enqueue (e : T) : ListQueue[T] = {
    ListQueue(list :+ e)
  } ensuring {
    res => res.size == size + 1
  }

  def first : T = {
    require(size > 0)
    list.head
  }

  def size : BigInt = list.size

}

object ListQueue {

  def empty[T] : ListQueue[T] = {
    ListQueue(Nil[T]())
  } ensuring {
    res => res.size == 0
  }

  def dequeue[T] (q : ListQueue[T], n : BigInt) : ListQueue[T] = {
    require(n >= 0 && n <= q.size)
    if (n == 0)
      q
    else {
      val dq : ListQueue[T] = q.dequeue
      dequeue(dq, n - 1)
    }
  } ensuring {
    res => res.size == q.size - n
  }

}

object ListQueueLemmas {

  def enqueue_dequeue[T] (q : ListQueue[T], e : T) : Boolean = {
    val eq : ListQueue[T] = q.enqueue(e)
    ListQueue.dequeue(eq, q.size).first == e because {
      q.list match {
        case Nil()        => trivial
        case Cons(hd, tl) =>
          enqueue_dequeue(ListQueue(tl), e)
      }
    }
  } holds

}

sealed case class ArrayQueue[T] (array : ListArray[T]) /*extends Queue[T]*/ {

  def dequeue : ArrayQueue[T] = {
    require(inv && size > 0)
    ArrayQueue(array.drop(1))
  } ensuring {
    res => res.inv && res.size == size - 1
  }

  def enqueue (e : T) : ArrayQueue[T] = {
    require(inv)
    ArrayQueue(array :+ e)
  } ensuring {
    res => res.inv && res.size == size + 1 because ListArrayLemmas.append_forall(array, e, (e : Option[T]) => e.isDefined)
  }

  def first : T = {
    require(inv && size > 0)
    array.acc(0).get
  }

  def size : BigInt = {
    require(inv)
    array.size
  }

  def inv : Boolean = {
    array.forall(e => e.isDefined)
  }

}

object ArrayQueue {

  def empty[T] : ArrayQueue[T] = {
    ArrayQueue(ListArray.empty[T])
  } ensuring {
    res => res.size == 0
  }

  def dequeue[T] (q : ArrayQueue[T], n : BigInt) : ArrayQueue[T] = {
    require(q.inv && n >= 0 && n <= q.size)
    if (n == 0)
      q
    else {
      val dq : ArrayQueue[T] = q.dequeue
      dequeue(dq, n - 1)
    }
  } ensuring {
    res => res.inv && res.size == q.size - n
  }

}

object ArrayQueueLemmas {

  def enqueue_dequeue[T] (q : ArrayQueue[T], e : T) : Boolean = {
    require(q.inv)
    ArrayQueue.dequeue(q.enqueue(e), q.size).first == e because {
      (if (q.size == 0)
        trivial
      else
        enqueue_dequeue(ArrayQueue(q.array.drop(1)), e)
        )
    }
  } holds

}
