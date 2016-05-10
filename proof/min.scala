package libref.proof

import libref.collection._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import libref.proof.DeleteOps._
import libref.proof.ListLemmas._

import leon.annotation._
import leon.lang._
import leon.proof._

import MinOps._
import MinLemmas._


import scala.language.postfixOps

@library
object MinOps {
  /**
    * Obtain the minimal element of the input list.
    * @param list a list
    * @return the minimal element of the input list
    */
  def min (list : List[BigInt]) : BigInt = {
    require(list != Nil[BigInt]())
    if (list.tail == Nil[BigInt]()) list.head
    else min(list.head, min(list.tail))
  } ensuring { res =>
    (list contains res) &&
      list.forall(res <= _) because min_lemma(list, res)
  }

  def min (x : BigInt, y : BigInt) = if (x < y) x else y

  def max (x : BigInt, y : BigInt) = if (x > y) x else y
}

@library
object MinLemmas {

  @induct
  def min_contains (list : List[BigInt], m : BigInt) : Boolean = {
    require(list contains m)
    min(list) <= m
  } holds

  @induct
  def min_not_contains (list : List[BigInt], e : BigInt) : Boolean = {
    require(e < min(list))
    !(list contains e)
  } holds

  def min_content (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(l1.content == l2.content && l1 != Nil[BigInt]())
    min(l1) == min(l2) because {
      min_contains(l1, min(l2)) &&
        min_contains(l2, min(l1))
    }
  } holds

  /**
    * Assert that a number is either > min(list) or <= all elements of list.
    */
  @induct
  def min_lemma (list : List[BigInt], m : BigInt) : Boolean = {
    require(list != Nil[BigInt]())
    m > min(list) || list.forall(m <= _)
  } holds

  /**
    * Assert that min(list) is indeed the minimal element of list.
    */
  def min_lemma2 (list : List[BigInt]) : Boolean = {
    require(list != Nil[BigInt]())
    val m = min(list)
    list.contains(m) && list.forall(m <= _) because
      min_lemma(list, m)
  } holds

  /**
    * Assert that min(l1 ++ l2) == min(l2 ++ l1)
    */
  def min_concat_comm (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(l1 != Nil[BigInt]() || l2 != Nil[BigInt]())
    min(l1 ++ l2) == min(l2 ++ l1) because {
      min_concat_lemma(l1, l2) && min_concat_lemma(l2, l1)
    }
  } holds

  /**
    * Assert that min(l1 ++ l2) == min(min(l1), min(l2))
    */
  @induct
  def min_concat_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(l1 != Nil[BigInt]() || l2 != Nil[BigInt]())
    if (l1 == Nil[BigInt]()) trivial
    else if (l2 == Nil[BigInt]()) trivial
    else min(l1 ++ l2) == min(min(l1), min(l2))
  } holds

  def is_min (l : List[BigInt], n : BigInt) : Boolean = {
    require(l.contains(n) && l.forall(n <= _))
    min(l) == n because {
      l match {
        case Nil()                   => trivial
        case Cons(hd, Nil())         => trivial
        case Cons(hd, tl) if hd == n => min_lemma2(tl) && apply_forall(tl, n <= (_ : BigInt), min(tl))
        case Cons(hd, tl)            => is_min(tl, n)
      }
    }
  } holds

  def min_permutation (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(permutation(l1, l2) && l2 != Nil[BigInt]())
    min(l1) == min(l2) because {
      if (l1.size == BigInt(1))
        trivial
      else {
        val l11 = delete(l1, min(l1))
        val l21 = delete(l2, min(l1))
        //min(l11) == min(l21) because {
        permutation_delete(l1, l2, min(l1)) &&
          min_permutation(l11, l21) && // }
          // min(l1) <= min(l21) because
          // min(l1) <= min(l11) because
          min_contains(l1, min(l11)) &&
          // l2.contains(min(l1)) &&
          min_delete(l2, min(l1))
      }
    }
  } holds /* verified by Leon */

  @induct
  def min_delete (l : List[BigInt], m : BigInt) : Boolean = {
    require(l.contains(m) &&
      (l.size == BigInt(1) || m <= min(delete(l, m))))
    m == min(l)
  } holds /* verified by Leon */
}