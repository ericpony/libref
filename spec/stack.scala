package libref.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import libref.collection._
import libref.spec.ListArray._

/*
abstract class Stack[T] {
  def isEmpty : Boolean = { size == 0 }
  def pop : Stack[T]
  def push (e : T) : Stack[T]
  def size : BigInt
  def top : T
}
*/

case class ListStack[T] (list : List[T]) /*extends Stack[T]*/ {

  def pop : ListStack[T] = {
    require(size > 0)
    ListStack(list.tail)
  } ensuring {
    res => res.size == size - 1
  }

  def push (e : T) : ListStack[T] = {
    ListStack(e::list)
  } ensuring {
    res => res.top == e && res.pop == this
  }

  def size : BigInt = list.size

  def top : T = {
    require(size > 0)
    list.head
  }

}

object ListStack {

  def empty[T] : ListStack[T] = ListStack(Nil())

}

case class ArrayStack[T] (array : ListArray[T]) /*extends Stack[T]*/ {

  def pop : ArrayStack[T] = {
    require(inv && size > 0)
    ArrayStack(array.drop(1))
  } ensuring {
    res => res.inv && res.size == size - 1
  }

  def push (e : T) : ArrayStack[T] = {
    require(inv)
    ArrayStack(array.shift(1).upd(0, e))
  } ensuring {
    res => res.inv && res.top == e && res.pop == this
  }

  def size : BigInt = {
    require(inv)
    array.size
  }

  def top : T = {
    require(inv && size > 0)
    val Some(e) = array.acc(0)
    e
  }

  def inv : Boolean = {
    array.forall(e => e.isDefined)
  }

}
