package libref.spec

import libref.proof.MinLemmas._
import libref.proof.DeleteOps._
import libref.proof.DistinctOps._
import libref.proof.DistinctLemmas._
import libref.proof.PermutationOps._
import libref.proof.SortedListOps._
import libref.proof.SortedListSpec._
import libref.collection._

import leon.annotation._
import leon.lang._
import leon.proof._

import DistinctSortedListOps._
import DistinctSortedListLemmas._

import scala.language.postfixOps

@library
object DistinctSortedListSpec {
  def merge_comm (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(distinct_sorted(l1) && distinct_sorted(l2))
    merge(l1, l2) == merge(l2, l1) because
      merge_comm_lemma(l1, l2)
  } holds

  def merge_assoc (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) : Boolean = {
    require(distinct_sorted(l1) && distinct_sorted(l2) && distinct_sorted(l3))
    merge(merge(l1, l2), l3) == merge(l1, merge(l2, l3)) because
      merge_assoc_lemma(l1, l2, l3)
  } holds
}

@library
object DistinctSortedListOps {
  def distinct_sorted (list : List[BigInt]) : Boolean = {
    distinct(list) && isSorted(list)
  }

  def add (list : List[BigInt], e : BigInt) : List[BigInt] = {
    require(distinct_sorted(list))
    list match {
      case Nil()        => Cons(e, Nil())
      case Cons(hd, tl) =>
        if (e < hd) e :: list
        else {
          if (e > hd) hd :: add(tl, e)
          else list
        }
    }
  } ensuring {
    res => res.content == list.content ++ Set(e) &&
      distinct_sorted(res) because
      add_distinct(list, e)
  }

  def merge (l1 : List[BigInt], l2 : List[BigInt]) : List[BigInt] = {
    require(distinct_sorted(l1) && distinct_sorted(l2))
    l1 match {
      case Nil()        => l2
      case Cons(h1, t1) =>
        l2 match {
          case Nil()        => l1
          case Cons(h2, t2) =>
            if (h1 < h2)
              Cons(h1, merge(t1, l2))
            else if (h2 < h1)
              Cons(h2, merge(l1, t2))
            else
              Cons(h1, merge(t1, t2))
        }
    }
  } ensuring {
    res => res.content == l1.content ++ l2.content &&
      res.size <= l1.size + l2.size &&
      distinct(merge(l1, l2)) &&
      distinct_sorted(res)
  }
}

@library
object DistinctSortedListLemmas {
  @induct
  def add_distinct (list : List[BigInt], e : BigInt) : Boolean = {
    require(distinct_sorted(list))
    distinct(add(list, e))
  } holds

  @induct
  def merge_not_contains (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require(distinct_sorted(l1) && !l1.contains(e) &&
      distinct_sorted(l2) && !l2.contains(e))
    !merge(l1, l2).contains(e)
  } holds

  def merge_comm_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(distinct_sorted(l1) && distinct_sorted(l2))
    if (l1 == Nil[BigInt]() || l2 == Nil[BigInt]) {
      merge(l1, l2) == merge(l2, l1)
    } else {
      val h1 = l1.head
      val h2 = l2.head
      if (h1 < h2) {
        merge(l1, l2) == merge(l2, l1) because
          merge_comm_lemma(l1.tail, l2)
      } else {
        if (h2 < h1) {
          merge(l1, l2) == merge(l2, l1) because
            merge_comm_lemma(l1, l2.tail)
        } else {
          merge(l1, l2) == merge(l2, l1) because
            merge_comm_lemma(l1.tail, l2.tail)
        }
      }
    }
  } holds

  @induct
  def distinct_content_permutation (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(distinct(l1) && distinct(l2) && l1.content == l2.content)
    if (l1 == Nil[BigInt]()) {
      permutation(l1, l2)
    } else {
      val h1 = l1.head
      permutation(l1, l2) because {
        distinct_delete(l2, h1) &&
          distinct_delete_content(l1, l2, h1) &&
          distinct_content_permutation(l1.tail, delete(l2, h1))
      }
    }
  } holds

  @induct
  def distinct_sorted_content (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(distinct_sorted(l1) && distinct_sorted(l2) && l1.content == l2.content)
    if (l1 == Nil[BigInt]()) {
      l1 == l2
    } else {
      l1 == l2 because {
        min_content(l1, l2) &&
          sort_head_min(l1) && sort_head_min(l2) &&
          distinct_delete_content(l1, l2, l1.head) &&
          distinct_sorted_content(l1.tail, l2.tail)
      }
    }
  } holds

  @induct
  def merge_assoc_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) : Boolean = {
    require(distinct_sorted(l1) && distinct_sorted(l2) && distinct_sorted(l3))
    val L1 = merge(merge(l1, l2), l3)
    val L2 = merge(l1, merge(l2, l3))
    L1 == L2 because {
      distinct_sorted(L1) && distinct_sorted(L2) &&
        L1.content == L2.content &&
        distinct_sorted_content(L1, L2)
    }
  } holds

  @induct
  def deterministic_lemma (list : List[BigInt], e : BigInt) : Boolean = {
    require(distinct_sorted(list))
    val L1 = add(list, e)
    val L2 = merge(list, add(Nil(), e))
    L1 == L2 because {
      distinct_sorted(L1) && distinct_sorted(L2) &&
        L1.content == L2.content &&
        distinct_sorted_content(L1, L2)
    }
  } holds
}
