package libref.spec

import libref.collection._
import libref.spec.LeftistHeap._
import libref.proof.SortedListOps._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import libref.proof.MinOps._
import libref.proof.MinLemmas._
import libref.proof.DeleteOps._

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

/**
  * Bisimulation between LeftistHeap and ListHeap
  */
object Heap_List_BisimulationSpec {
  implicit def toList (h : ListHeap) = h.toList

  implicit def toHeap (l : List[BigInt]) = ListHeap(l)

  /**
    * h ~ l implies h.insert(e) ~ l.insert(e)
    */
  def bisim_insert (h : HeapNode, l : ListHeap, e : BigInt) : Boolean = {
    require(h.isHeap && h ~ l)
    h.insert(e) ~ l.insert(e) because {
      val L1 = h.insert(e)
      val L2 = l.insert(e)
      permutation_cons(h, l, e) &&
        permutation_eq(e :: l, L2) &&
        permutation_tran(L1, e :: h, e :: l) &&
        permutation_tran(L1, e :: l, L2)
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ l1 and h2 ~ l2 implies h1.merge(h2) ~ l1.merge(l2)
    */
  def bisim_merge (h1 : HeapNode, h2 : HeapNode, l1 : ListHeap, l2 : ListHeap) : Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ l1 && h2 ~ l2)
    h1.merge(h2) ~ l1.merge(l2) because {
      val L1 = h1.merge(h2)
      val L2 = l1.merge(l2)
      permutation_append(h1, l1, h2) &&
        permutation_prepend(l1, l2, h2) &&
        permutation_tran(h1 ++ h2, l1 ++ h2, l1 ++ l2) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, l1.merge(l2))
    }
  } holds /* verified by Leon */

  /**
    * h ~ l implies h.findMin == l.findMin
    */
  def bisim_findMin (h : HeapNode, l : ListHeap) : Boolean = {
    require(h.isHeap && h ~ l)
    h.findMin == l.findMin because {
      if (h.isEmpty) trivial
      else min_permutation(h, l)
    }
  } holds /* verified by Leon */

  /**
    * h ~ l implies h.deleteMin ~ l.deleteMin
    */
  def bisim_deleteMin (h : HeapNode, l : ListHeap) : Boolean = {
    require(h.isHeap && h ~ l)
    h.deleteMin ~ l.deleteMin because {
      if (h.isEmpty) trivial
      else {
        bisim_findMin(h, l) &&
          permutation_delete(h, l, h.findMin.get) &&
          permutation_tran(h.deleteMin, delete(h, h.findMin.get), delete(l, l.findMin.get))
      }
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ h2 implies h1.size == h2.size
    */
  def bisim_size (h : HeapNode, l : ListHeap) : Boolean = {
    require(h.isHeap && h ~ l)
    h.size == l.size
  } holds /* verified by Leon */

  @induct
  def list_insert_comm (l : List[BigInt], e1 : BigInt, e2 : BigInt) = {
    l.insert(e1).insert(e2) ~ l.insert(e2).insert(e1)
  } holds /* verified by Leon */

  def insert_comm_prop (l : ListHeap, e1 : BigInt, e2 : BigInt) = {
    l.insert(e1).insert(e2) ~ l.insert(e2).insert(e1) because
      list_insert_comm(l, e1, e2)
  } holds /* verified by Leon */

  def merge_comm_prop (l1 : ListHeap, l2 : ListHeap) : Boolean = {
    l1.merge(l2) ~ l2.merge(l1) because
      permutation_concat_comm(l1, l2)
  } holds /* verified by Leon */

  def merge_assoc_prop (l1 : ListHeap, l2 : ListHeap, l3 : ListHeap) : Boolean = {
    l1.merge(l2).merge(l3) ~ l1.merge(l2.merge(l3)) because
      permutation_concat_assoc(l1, l2, l3)
  } holds /* verified by Leon */

  //  /**
  //   * h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1)
  //   */
  //  def heap_insert_comm_prop (h: ListHeap, e1: BigInt, e2: BigInt): Boolean = {
  //    require(h.isHeap)
  //    h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1) because {
  //      bisim_insert(h, h, e1) &&
  //        bisim_insert(h.insert(e1), e1 :: h, e2) &&
  //        list_insert_comm_prop(h, e1, e2) &&
  //        permutation_tran(
  //          h.insert(e1).insert(e2),
  //          e2 :: e1 :: h,
  //          e1 :: e2 :: h
  //        ) &&
  //        heap_insert_lemma(h, e2) &&
  //        permutation_cons(h.insert(e2), e2 :: h, e1) &&
  //        heap_insert_lemma(h.insert(e2), e1) &&
  //        permutation_tran(
  //          h.insert(e2).insert(e1),
  //          e1 :: h.insert(e2),
  //          e1 :: e2 :: h
  //        ) &&
  //        permutation_tran(
  //          h.insert(e1).insert(e2),
  //          e1 :: e2 :: h,
  //          h.insert(e2).insert(e1)
  //        )
  //    }
  //  } holds /* verified by Leon */
  //
  //  /**
  //   * h1.merge(h2) ~ h2.merge(h1)
  //   */
  //  def heap_merge_comm_prop (h1: ListHeap, h2: ListHeap): Boolean = {
  //    require(h1.isHeap && h2.isHeap)
  //    h1.merge(h2) ~ h2.merge(h1) because {
  //      bisim_merge(h1, h2, h1, h2) &&
  //        bisim_merge(h2, h1, h2, h1) &&
  //        permutation_concat_comm(h1, h2) &&
  //        permutation_tran(h1.merge(h2), h1 ++ h2, h2 ++ h1) &&
  //        // The following line is weird. It is not needed in logic,
  //        // but Leon cannot prove this lemma without it.
  //        permutation(h2 ++ h1, h2.merge(h1)) && // WEIRD!!
  //        permutation_tran(h1.merge(h2), h2 ++ h1, h2.merge(h1))
  //    }
  //  } holds /* verified by Leon */
}

//case class ListHeap (list: List[BigInt]) extends HeapADT {
case class ListHeap (list : List[BigInt]) {

  implicit def toList (h : ListHeap) : List[BigInt] = h.toList

  def ~ (l : List[BigInt]) = permutation(list, l)

  def findMin : Option[BigInt] = {
    if (list == Nil[BigInt]())
      None[BigInt]()
    else
      Some(min(list))
  }

  def deleteMin : ListHeap = {
    if (list == Nil[BigInt]())
      ListHeap(list)
    else
      ListHeap(delete(list, findMin.get))
  }

  def merge (l : ListHeap) : ListHeap = ListHeap(list ++ l)

  def insert (e : BigInt) : ListHeap = ListHeap(e :: list)

  def toSortedList : List[BigInt] = sort(list)

  def content = list.content

  def toList : List[BigInt] = list

  def isHeap : Boolean = true

  def size : BigInt = list.size
}
