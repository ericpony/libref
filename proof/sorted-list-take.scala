package libref.proof

import libref.collection._
import libref.proof.DeleteLemmas._
import libref.proof.DeleteOps._
import libref.proof.ListLemmas._
import libref.proof.MinLemmas._
import libref.proof.MinOps._
import libref.proof.PermutationLemmas._
import libref.proof.PermutationOps._
import libref.proof.SortedListTakeLemmas._
import libref.proof.SortedListTakeOps._
import libref.proof.SortedListLemmas._
import libref.proof.SortedListOps.{isSorted, sort}
import libref.proof.SortedListSpec._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

object SortedListTakeSpec {

  def insert_commutative_prop (list : List[BigInt], e1 : BigInt, e2 : BigInt, n : BigInt) = {
    require(isSorted(list))
    insert(insert(list, e1, n), e2, n) == insert(insert(list, e2, n), e1, n) because
      insert_comm_lemma(list, e1, e2, n)
  } holds /* verified by Leon */

  def merge_commutative_prop (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    merge(l1, l2, n) == merge(l2, l1, n) because
      merge_comm_lemma(l1, l2, n)
  } holds /* verified by Leon */

  def merge_associative_prop (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt], n : BigInt) = {
    merge(merge(l1, l2, n), l3, n) == merge(l1, merge(l2, l3, n), n) because
      merge_assoc_lemma(l1, l2, l3, n)
  } holds /* verified by Leon */

  def composition_prop (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) : Boolean = {
    val z = Nil[BigInt]()
    val L = foldl_insert(z, l1 ++ l2, n)
    val L1 = foldl_insert(z, l1, n)
    val L2 = foldl_insert(z, l2, n)
    L == merge(L1, L2, n) because {
      // L == sort_take(l1 ++ l2, n)
      foldl_insert_lemma(z, l1 ++ l2, n) &&
        // L1 == sort_take(l1, n)
        foldl_insert_lemma(z, l1, n) &&
        // L2 == sort_take(l2, n)
        foldl_insert_lemma(z, l2, n) &&
        sort_take_concat_sort_take(l1, l2, n, n, n)
    }
  } holds /* verified by Leon */
}

object SortedListTakeOps {

  def sorted_take (list : List[BigInt], n : BigInt) : List[BigInt] = {
    require(isSorted(list))
    //list.take(n)
    (list, n) match {
      case (Nil(), _)      => Nil[BigInt]()
      case (Cons(h, t), i) =>
        if (i <= BigInt(0)) {
          Nil[BigInt]()
        } else {
          Cons(h, sorted_take(t, i - 1))
        }
    }
  } ensuring {
    res => res == list.take(n) && isSorted(res)
  }

  def sort_take (list : List[BigInt], n : BigInt) : List[BigInt] = {
    sorted_take(sort(list), n)
  } ensuring { res =>
    res == sort(list).take(n) &&
      res.content.subsetOf(list.content) &&
      isSorted(res) && res.size == (
      if (n <= 0) BigInt(0)
      else if (n > list.size) list.size
      else n
      )
  }

  def insert (list : List[BigInt], e : BigInt, n : BigInt) = {
    sort_take(e :: list, n)
  }

  def merge (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    sort_take(l1 ++ l2, n)
  }

  def foldl_insert (list0 : List[BigInt], list : List[BigInt], n : BigInt) : List[BigInt] = {
    require(isSorted(list0))
    if (list == Nil[BigInt]()) sort_take(list0, n)
    else foldl_insert(insert(list0, list.head, n), list.tail, n)
  } ensuring { isSorted(_) }

  def L (e : BigInt) = Cons(e, Nil[BigInt]())
}

object SortedListTakeLemmas {

  def take_all (l : List[BigInt], n : BigInt) : Boolean = {
    require(n >= l.size)
    l.take(n) == l because {
      l match {
        case Nil()      => trivial
        case Cons(h, t) =>
          if (n <= BigInt(0)) {
            trivial
          } else {
            take_all(t, n - 1)
          }
      }
    }
  } holds

  def take_n_m (l : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    l.take(n).take(m) == l.take(min(n, m)) because {
      l match {
        case Nil()      => trivial
        case Cons(h, t) =>
          if (n <= 0 || m <= 0)
            trivial
          else if (n < m) {
            take_all(l.take(n), m)
          } else {
            take_n_m(t, n - 1, m - 1)
          }
      }
    }
  } holds

  def take_idempotent (l : List[BigInt], n : BigInt) : Boolean = {
    l.take(n).take(n) == l.take(n) because { take_n_m(l, n, n) }
  } holds

  def sort_take_idempotent (l : List[BigInt], n : BigInt) : Boolean = {
    sort_take(sort_take(l, n), n) == sort_take(l, n) because {
      sort_sorted(sorted_take(sort(l), n)) && take_idempotent(sort(l), n)
    }
  } holds

  def sort_tail (l : List[BigInt]) : Boolean = {
    require(!l.isEmpty)
    sort(l).tail == sort(delete(l, min(l))) because {
      min_head_lemma(l) && sort_delete_lemma(l, min(l))
    }
  } holds

  def sort_take_decomp (l : List[BigInt], n : BigInt) : Boolean = {
    require(!l.isEmpty && n > 0)
    sort(l).take(n) == min(l) :: sort(delete(l, min(l))).take(n - 1) because {
      sort_tail(l)
    }
  } holds

  def sort_take_sorted (l : List[BigInt], n : BigInt) : Boolean = {
    isSorted(sort(l).take(n)) because { sort(l).take(n) == sort_take(l, n) }
  } holds

  @induct
  def min_delete (l : List[BigInt]) : Boolean = {
    require(l.size > 1)
    min(l) <= min(delete(l, min(l)))
  } holds

  def take_delete (l : List[BigInt], n : BigInt, x : BigInt) : Boolean = {
    require(l.take(n).contains(x))
    delete(l.take(n), x) == delete(l, x).take(n - 1) because {
      l match {
        case Nil()                => trivial
        case Cons(h, t) if h == x => trivial
        case Cons(h, t)           => t.take(n - 1).contains(x) && take_delete(t, n - 1, x)
      }
    }
  } holds

  def sort_take_min (l : List[BigInt], n : BigInt) : Boolean = {
    require(!l.isEmpty && n > 0)
    min(sort(l).take(n)) == min(l) because {
      l match {
        case Nil()                => trivial
        case Cons(h, Nil())       => trivial
        case Cons(h, t) if n == 1 => sort_take_decomp(l, n)
        case Cons(h, t)           =>
          // min(sort(l).take(n))
          // == min(min(l)::sort(delete(l, min(l))).take(n - 1))
          sort_take_decomp(l, n) &&
            // == min(min(l), min(delete(l, min(l))))
            sort_take_min(delete(l, min(l)), n - 1) &&
            // == min(l)
            min_delete(l)
      }
    }
  } holds

  def sort_take_concat_decomp_l (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require(!l1.isEmpty && n >= m && m > 0 && (l2.isEmpty || min(l1) <= min(l2)))
    sort(sort(l1).take(n) ++ l2).take(m) == min(l1) :: sort(sort(delete(l1, min(l1))).take(n - 1) ++ l2).take(m - 1) because {
      val min12 = min(sort(l1).take(n) ++ l2)
      // sort_take(sort(l1).take(n) ++ l2, m)
      sort_take_decomp(sort(l1).take(n) ++ l2, m) &&
        // == min12::sort(delete(sort(l1).take(n) ++ l2, min12)).take(m - 1)
        (if (l2.isEmpty)
          rightUnitAppend(sort(l1).take(n)) && sort_take_min(l1, n)
        else
          min_concat_lemma(sort(l1).take(n), l2) && sort_take_min(l1, n)) &&
        // == min(l1)::sort(delete(sort(l1).take(n) ++ l2, min(l1))).take(m - 1)
        min_lemma2(sort(l1).take(n)) && delete_concat(sort(l1).take(n), l2, min(sort(l1).take(n))) &&
        // == min(l1)::sort(delete(sort(l1).take(n), min(l1)) ++ l2).take(m - 1)
        take_delete(sort(l1), n, min(l1))
      // == min(l1)::sort(delete(sort(l1), min(l1)).take(n - 1) ++ l2).take(m - 1)
    }
  } holds

  def sort_take_concat_decomp_r (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require(!l2.isEmpty && m > 0 && (l1.isEmpty || n <= 0 || min(l2) < min(l1)))
    sort(sort(l1).take(n) ++ l2).take(m) == min(l2) :: sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1) because {
      val min12 = min(sort(l1).take(n) ++ l2)
      // sort_take(sort(l1).take(n) ++ l2, m)
      sort_take_decomp(sort(l1).take(n) ++ l2, m) &&
        // == min12::sort(delete(sort(l1).take(n) ++ l2, min12)).take(m - 1)
        (if (l1.isEmpty || n <= 0) leftUnitAppend(l2) else min_concat_lemma(sort(l1).take(n), l2) && sort_take_min(l1, n)) &&
        // == min(l2)::sort(delete(sort(l1).take(n) ++ l2, min(l2))).take(m - 1)
        (
          if (l1.isEmpty || n <= 0)
            leftUnitAppend(l2) && leftUnitAppend(delete(l2, min(l2)))
          else
            min_not_contains(sort(l1).take(n), min(l2)) && delete_concat_right(sort(l1).take(n), l2, min(l2))
          )
      // == min(l2)::sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1)
    }
  } holds

  def sort_take_concat_more (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(n >= r && m >= r && i >= 0 && j >= 0)
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r) because {
      sort_take_concat_sort_take(l1, l2, n, m, r) && sort_take_concat_sort_take(l1, l2, n + i, m + j, r)
    }
  } holds

  def sort_take_concat_norm (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require(n >= r && m >= r)
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == sort(sort(l1).take(r) ++ sort(l2).take(r)).take(r) because {
      sort_take_concat_more(l1, l2, r, r, r, n - r, m - r)
    }
  } holds

  def sort_take_perm_eq (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) : Boolean = {
    require(permutation(l1, l2))
    sort_take(l1, n) == sort_take(l2, n) because { sort_permutation_prop(l1, l2) }
  } holds

  def sort_take_concat (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require(n >= m)
    sort_take(sort_take(l1, n) ++ l2, m) == sort_take(l1 ++ l2, m) because {
      if (n <= 0 || m <= 0 || l1.isEmpty) {
        trivial
      } else if (l2.isEmpty) {
        rightUnitAppend(sort_take(l1, n)) && sort_sorted(sort_take(l1, n)) && take_n_m(sort(l1), n, m) &&
          rightUnitAppend(l1)
      } else if (min(l1) <= min(l2)) {
        // sort_take(sort_take(l1, n) ++ l2, m)
        sort_take_concat_decomp_l(l1, l2, n, m) &&
          // == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ l2).take(m - 1)
          sort_take_concat(delete(l1, min(l1)), l2, n - 1, m - 1) &&
          // == min(l1)::sort(delete(l1, min(l1)) ++ l2).take(m - 1)
          delete_concat(l1, l2, min(l1)) && min_lemma2(l1) &&
          // == min(l1)::sort(delete(l1 ++ l2, min(l1))).take(m - 1)
          min_concat_lemma(l1, l2) && sort_take_decomp(l1 ++ l2, m)
        // == sort_take(l1 ++ l2, n)
      } else {
        // sort_take(sort_take(l1, n) ++ l2, m)
        sort_take_concat_decomp_r(l1, l2, n, m) &&
          // == min(l2)::sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1)
          sort_take_concat(l1, delete(l2, min(l2)), n, m - 1) &&
          // == min(l2)::sort(l1 ++ delete(l2, min(l2))).take(m - 1)
          min_not_contains(l1, min(l2)) && !l1.contains(min(l2)) && delete_concat_right(l1, l2, min(l2)) &&
          // == min(l2)::sort(delete(l1 ++ l2, min(l2))).take(m - 1)
          min_concat_lemma(l1, l2) && min(l1 ++ l2) == min(l2) && sort_take_decomp(l1 ++ l2, m)
        // == sort_take(l1 ++ l2, m)
      }
    }
  } holds

  def sort_take_concat_sort_take (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require(n >= r && m >= r)
    sort_take(sort_take(l1, n) ++ sort_take(l2, m), r) == sort_take(l1 ++ l2, r) because {
      // sort_take(sort_take(l1, n) ++ sort_take(l2, m), r)
      sort_take_concat(l1, sort_take(l2, m), n, r) &&
        // == sort_take(l1 ++ sort_take(l2, m), r)
        merge_comm_lemma(l1, sort_take(l2, m), r) &&
        // == sort_take(sort_take(l2, m) ++ l1, r)
        sort_take_concat(l2, l1, m, r) &&
        // == sort_take(l2 ++ l1, r)
        merge_comm_lemma(l2, l1, r)
      // == sort_take(l1 ++ l2, r)
    }
  } holds

  def merge_comm_lemma (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    merge(l1, l2, n) == merge(l2, l1, n) because {
      sort_commutative_prop(l1, l2)
    }
  } holds

  def merge_assoc_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt], n : BigInt) = {
    merge(merge(l1, l2, n), l3, n) == merge(l1, merge(l2, l3, n), n) because {
      // sort_take(sort_take(l1 ++ l2, n) ++ l3, n)
      sort_take_concat_sort_take(sort_take(l1 ++ l2, n), l3, n, n, n) &&
        // == sort_take(sort_take(sort_take(l1 ++ l2, n), n) ++ sort_take(l3, n), n)
        sort_take_idempotent(l1 ++ l2, n) &&
        // == sort_take(sort_take(l1 ++ l2, n) ++ sort_take(l3, n), n)
        sort_take_concat_sort_take(l1 ++ l2, l3, n, n, n) &&
        // == sort_take((l1 ++ l2) ++ l3, n)
        // sort_take(l1 ++ sort_take(l2 ++ l3, n), n)
        sort_take_concat_sort_take(l1, sort_take(l2 ++ l3, n), n, n, n) &&
        // == sort_take(sort_take(l1, n) ++ sort_take(sort_take(l2 ++ l3, n), n), n)
        sort_take_idempotent(l2 ++ l3, n) &&
        // == sort_take(sort_take(l1, n) ++ sort_take(l2 ++ l3, n), n)
        sort_take_concat_sort_take(l1, l2 ++ l3, n, n, n) &&
        // == sort_take(l1 ++ (l2 ++ l3), n)
        appendAssoc(l1, l2, l3)
      // == sort_take(l1 ++ l2 ++ l3, n)
    }
  } holds

  def insert_merge (list : List[BigInt], e : BigInt, n : BigInt) = {
    insert(list, e, n) == merge(list, L(e), n) because
      insert_merge_perm(list, e) &&
        sort_take_perm_eq(e :: list, list ++ L(e), n)
  } holds

  @induct
  def insert_merge_perm (list : List[BigInt], e : BigInt) = {
    permutation(e :: list, list ++ L(e))
  } holds

  def insert_comm_lemma (list : List[BigInt], e1 : BigInt, e2 : BigInt, n : BigInt) = {
    require(isSorted(list))
    insert(insert(list, e1, n), e2, n) == insert(insert(list, e2, n), e1, n) because {
      // insert(list, e1, n) == merge(list, L(e1), n)
      insert_merge(list, e1, n) &&
        // insert(list, e2, n) == merge(list, L(e2), n)
        insert_merge(list, e2, n) &&
        // insert(insert(list, e1, n), e2, n) == merge(insert(list, e1, n), L(e2), n)
        insert_merge(insert(list, e1, n), e2, n) &&
        // insert(insert(list, e2, n), e1, n) == merge(insert(list, e2, n), L(e1), n)
        insert_merge(insert(list, e2, n), e1, n) &&
        merge(merge(list, L(e1), n), L(e2), n) == merge(merge(list, L(e2), n), L(e1), n) because {
        // merge(merge(list, L(e1), n), L(e2), n) == merge(list, merge(L(e1), L(e2), n), n)
        merge_assoc_lemma(list, L(e1), L(e2), n) &&
          // merge(merge(list, L(e2), n), L(e1), n) == merge(list, merge(L(e2), L(e1), n), n)
          merge_assoc_lemma(list, L(e2), L(e1), n) &&
          // merge(L(e2), L(e1), n) == merge(L(e1), L(e2), n) because
          merge_comm_lemma(L(e1), L(e2), n)
      }
    }
  }

  def foldl_insert_lemma (list0 : List[BigInt], list : List[BigInt], n : BigInt) : Boolean = {
    require(isSorted(list0))
    foldl_insert(list0, list, n) == sort_take(list0 ++ list, n) because {
      if (list == Nil[BigInt]()) trivial
      else {
        val e = list.head
        foldl_insert(sort(list0 ++ L(e)), list.tail, n) == sort_take(list0 ++ list, n) because {
          // foldl_insert(sort(list0 ++ L(e)), list.tail, n) == sort_take(sort(list0 ++ L(e)) ++ list.tail, n)
          foldl_insert_lemma(sort(list0 ++ L(e)), list.tail, n) &&
            // sort_take(sort(list0 ++ L(e)) ++ list.tail, n) == sort_take(list0 ++ list, n)
            foldl_insert_2(list0, list) &&
            sort_take_perm_eq(sort(list0 ++ L(e)) ++ list.tail, list0 ++ list, n)
        } &&
          // foldl_insert(sort(list0 ++ L(e)), list.tail, n) == foldl_insert(list0, list, n) because
          foldl_insert_3(list0, list, n)
      }
    }
  } holds /* verified by Leon */

  def foldl_insert_2 (list0 : List[BigInt], list : List[BigInt]) : Boolean = {
    require(list != Nil[BigInt]())
    permutation(sort(list0 ++ L(list.head)) ++ list.tail, list0 ++ list) because {
      val l1 = list0 ++ L(list.head)
      val l2 = list.tail
      list_decomp(list0, list) &&
        //permutation(sort(l1) ++ l2, l1 ++ l2) because
        permutation(sort(l1), l1) because {
        sort_permutation(l1)
      } && permutation_append(sort(l1), l1, l2)
    }
  } holds /* verified by Leon */

  /**
    * WARNING: Leon takes 10+ seconds to verify this lemma on my desktop.
    */
  def foldl_insert_3 (list0 : List[BigInt], list : List[BigInt], n : BigInt) : Boolean = {
    require(isSorted(list0))
    if (list == Nil[BigInt]()) true /* never happens in the context of application */
    else {
      foldl_insert(sort(list0 ++ L(list.head)), list.tail, n) == foldl_insert(list0, list, n) because {
        // foldl_insert(sort(list0 ++ L(list.head)), list.tail, n) == foldl_insert(sort(list.head :: list0), list.tail, n) because
        //sort(list0 ++ L(list.head)) == sort(list.head :: list0) because
        permutation_first_last_swap(list0, list.head) &&
          permutation_sort(list0 ++ L(list.head), list.head :: list0)
      } && {
        // foldl_insert(sort(list.head :: list0), list.tail, n) == foldl_insert(sort_take(list.head :: list0, n), list.tail, n) because
        if (list.tail == Nil[BigInt]()) {
          // foldl_insert(sort_take(list.head :: list0, n), list.tail, n) == sort_take(list.head :: list0, n)
          sort_take_idempotent(list.head :: list0, n) //&&
          // foldl_insert(sort(list.head :: list0), list.tail, n) == sort_take(list.head :: list0, n)
          //sorted_sort_take(sort(list.head :: list0), n)
        } else {
          val Cons(h, t) = list.tail
          // foldl_insert(sort(list.head :: list0), list.tail, n) == foldl_insert(sort_take(h :: sort(list.head :: list0), n), t, n)
          // foldl_insert(sort_take(list.head :: list0, n), list.tail, n) == foldl_insert(sort_take(h :: sort_take(list.head :: list0, n), n), t, n)
          sort_take_cons_sort_take(list.head :: list0, h, n) &&
            foldl_insert_3(sort_take(h :: sort(list.head :: list0), n), t, n)
        }
      }
    }
  } holds /* verified by Leon */

  def sort_take_cons_sort_take (list : List[BigInt], e : BigInt, n : BigInt) = {
    sort_take(e :: sort(list), n) == sort_take(e :: sort_take(list, n), n) because {
      if (n <= 0) trivial
      else {
        sort_take(e :: sort(list), n) == sort_take(sort(e :: list), n) because {
          // sort(e :: sort(list)).take(n) == sort(e :: list).take(n) because
          sort_cons_sort(list, e) &&
            // sort_take(e :: sort(list), n) == sort_take(sort(e :: sort(list)), n) because
            sort_idempotent_prop(e :: sort(list)) &&
            // sort_take(sort(e :: sort(list)), n) == sort(e :: sort(list)).take(n) because
            sort_idempotent_prop(e :: sort(list))
        } &&
          sort_take(e :: sort_take(list, n), n) == sort_take(sort(e :: list), n) because {
          // sort_take(sort(e :: list), n) == sort_take(e :: list, n) because
          sort_idempotent_prop(e :: list) &&
            // e :: sort_take(list, n) == L(e) ++ sort_take(list, n) &&
            L(e) == sort_take(L(e), n) &&
            // sort_take(sort_take(L(e), n) ++ sort_take(list, n), n) == sort_take(e :: list, n) because
            sort_take_concat_sort_take(L(e), list, n, n, n)
        }
      }
    }
  } holds /* verified by Leon */

  @induct
  def permutation_first_last_swap (list : List[BigInt], e : BigInt) = {
    permutation(list ++ L(e), e :: list)
  } holds /* verified by Leon */

  def sort_cons_sort (list : List[BigInt], e : BigInt) = {
    sort(e :: sort(list)) == sort(e :: list) because {
      sort_permutation(list) &&
        permutation_cons(sort(list), list, e) &&
        permutation_sort(e :: sort(list), e :: list)
    }
  } holds /* verified by Leon */

  @induct
  def list_decomp (list0 : List[BigInt], list : List[BigInt]) : Boolean = {
    require(list != Nil[BigInt]())
    list0 ++ list == (list0 ++ L(list.head)) ++ list.tail
  } holds /* verified by Leon */

}
