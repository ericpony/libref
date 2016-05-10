package libref.proof

import libref.collection._
import libref.proof.DeleteOps._
import libref.proof.MinOps._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import libref.proof.SortedListLemmas._
import libref.proof.SortedListOps._
import libref.proof.sugar._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

@library
object SortedListSpec {
  /* Insert operations are commutative. */
  @induct
  def insert_commutative_prop (list : List[BigInt], e1 : BigInt, e2 : BigInt) = {
    require(isSorted(list))
    insert(insert(list, e1), e2) == insert(insert(list, e2), e1)
  } holds

  @induct
  def sort_head_min (list : List[BigInt]) : Boolean = {
    require(list != Nil[BigInt]() && isSorted(list))
    list.head == min(list)
  } holds

  /* Merge operations are associative. */
  def sort_associative_prop (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) = {
    sort(sort(l1 ++ l2) ++ l3) == sort(l1 ++ sort(l2 ++ l3)) because
      sort_assoc_lemma(l1, l2, l3)
  } holds

  /* Merge operations are commutative. */
  def sort_commutative_prop (l1 : List[BigInt], l2 : List[BigInt]) = {
    sort(l1 ++ l2) == sort(l2 ++ l1) because
      permutation_concat_comm(l1, l2) &&
        permutation_sort(l1 ++ l2, l2 ++ l1)
  } holds

  /* Sort operations are idempotent. */
  def sort_idempotent_prop (list : List[BigInt]) = {
    sort(list) == sort(sort(list)) because
      sort_permutation(list) &&
        permutation_sort(list, sort(list))
  } holds

  /* Sort any permutation of a list give the same result */
  def sort_permutation_prop (l1 : List[BigInt], l2 : List[BigInt]) = {
    require(permutation(l1, l2))
    sort(l1) == sort(l2) because permutation_sort(l1, l2)
  } holds

  /* Sort is permutation */
  def permutation_sort_prop (list : List[BigInt]) = {
    permutation(list, sort(list)) because sort_permutation(list)
  } holds
}

@library
object SortedListOps {
  /**
    * Insert an element into a sorted list.
    * @param list a sorted list
    * @param e an element
    * @return a sorted list containning e
    */
  def insert (list : List[BigInt], e : BigInt) : List[BigInt] = {
    require(isSorted(list))
    list match {
      case Nil()       => Cons(e, Nil())
      case Cons(x, xs) => if (x >= e) Cons(e, list) else Cons(x, insert(xs, e))
    }
  } ensuring { res =>
    res.content == list.content ++ Set[BigInt](e) and
      res.size == list.size + 1 and
      isSorted(res)
  }

  /**
    * Merge two sorted lists to obtain one sorted list.
    * @param l1 a sorted list
    * @param l2 a sorted list
    * @return a sorted list
    */
  @induct
  def mergeSortedList (l1 : List[BigInt], l2 : List[BigInt]) : List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    l2 match {
      case Nil()       => l1
      case Cons(x, xs) => insert(mergeSortedList(l1, xs), x)
    }
  } ensuring { res =>
    isSorted(res) and
      res.content == l1.content ++ l2.content
  }

  /**
    * Obtain a sorted version of the provided list (in ascending order).
    * @param list a list
    * @return a sorted list
    */
  def sort (list : List[BigInt]) : List[BigInt] = {
    list match {
      case Nil()       => list
      case Cons(x, xs) => insert(sort(xs), x)
    }
  } ensuring { res =>
    res.content == list.content &&
      isSorted(res) &&
      res.size == list.size &&
      (isSorted(list) implies res == list)
  }

  /**
    * Tell whether a list is sorted in ascending order.
    * @param list a list
    * @return whether the input list is sorted in ascending order
    */
  def isSorted (list : List[BigInt]) : Boolean = {
    list match {
      case Nil()                  => trivial
      case Cons(_, Nil())         => trivial
      case Cons(x1, Cons(x2, xs)) => x1 <= x2 && isSorted(list.tail)
    }
  } ensuring { res =>
    list.size > 0 && res implies list.head == min(list)
  }
}

@library
object SortedListLemmas {
  @induct
  def min_head_lemma (list : List[BigInt]) = {
    require(list != Nil[BigInt]())
    sort(list).head == min(list)
  } holds

  @induct
  def min_sort_lemma (list : List[BigInt]) = {
    require(list != Nil[BigInt]())
    min(sort(list)) == min(list)
  } holds

  @induct
  def sort_delete_lemma (list : List[BigInt], m : BigInt) : Boolean = {
    require(list != Nil[BigInt]() && m == sort(list).head)
    sort(delete(list, m)) == delete(sort(list), m)
  } holds

  @induct
  def sort_not_contains_lemma (list : List[BigInt], e : BigInt) : Boolean = {
    require(!list.contains(e))
    !sort(list).contains(e)
  } holds

  @induct
  def insert_comm (list : List[BigInt], a : BigInt, b : BigInt) : Boolean = {
    require(isSorted(list))
    insert(insert(list, a), b) == insert(insert(list, b), a)
  } holds

  @induct
  def insert_delete (list : List[BigInt], e : BigInt) : Boolean = {
    require(isSorted(list))
    list == delete(insert(list, e), e)
  } holds

  def sort_cons_delete (list : List[BigInt], e : BigInt) : Boolean = {
    sort(list) == delete(sort(Cons(e, list)), e) because
      check { insert_delete(sort(list), e) }
  } holds

  @induct
  def insert_sort_delete (list : List[BigInt], e : BigInt) : Boolean = {
    require(list.contains(e))
    if (list.size == 1) {
      sort(list) == insert(sort(delete(list, e)), e)
    } else {
      val h = list.head
      if (h == e) {
        sort(list) == insert(sort(delete(list, e)), e)
      } else {
        sort(list) == insert(sort(delete(list, e)), e) because
          insert_sort_delete(list.tail, e) &&
            insert_comm(sort(delete(list.tail, e)), e, h)
      }
    }
  } holds

  @induct
  def permutation_sort (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require(permutation(l1, l2))
    sort(l1) == sort(l2) because {
      if (l1 == Nil[BigInt]()) trivial
      else {
        val h1 = l1.head
        sort(l1) == sort(l2) because
          permutation_sort(l1.tail, delete(l2, h1)) &&
            insert_sort_delete(l2, h1)
      }
    }
  } holds

  @induct
  def sort_permutation (list : List[BigInt]) : Boolean = {
    permutation(list, sort(list)) because {
      if (list == Nil[BigInt]) trivial
      else {
        //permutation(list, sort(list)) because
        sort_permutation(list.tail) &&
          sort_cons_delete(list.tail, list.head)
      }
    }
  } holds

  def sort_assoc_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) = {
    sort(sort(l1 ++ l2) ++ l3) == sort(l1 ++ sort(l2 ++ l3)) because
      // permutation (l1 ++ l2, sort (l1 ++ l2))
      sort_permutation(l1 ++ l2) &&
        // permutation (sort (l1 ++ l2), l1 ++ l2)
        permutation_comm(l1 ++ l2, sort(l1 ++ l2)) &&
        // permutation (sort (l1 ++ l2) ++ l3, l1 ++ l2 ++ l3)
        permutation_append(sort(l1 ++ l2), l1 ++ l2, l3) &&
        // permutation (l2 ++ l3, sort (l2 ++ l3))
        sort_permutation(l2 ++ l3) &&
        // permutation (l1 ++ (l2 ++ l3), l1 ++ sort (l2 ++ l3)
        permutation_prepend(l1, l2 ++ l3, sort(l2 ++ l3)) &&
        // permutation (l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3))
        permutation_concat_assoc(l1, l2, l3) &&
        permutation_tran(sort(l1 ++ l2) ++ l3, l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) &&
        permutation_tran(sort(l1 ++ l2) ++ l3, l1 ++ (l2 ++ l3), l1 ++ sort(l2 ++ l3)) &&
        permutation_sort(sort(l1 ++ l2) ++ l3, l1 ++ sort(l2 ++ l3))
  }

  @induct
  def sort_sorted (l : List[BigInt]) : Boolean = {
    require(isSorted(l))
    sort(l) == l
  } holds

}
