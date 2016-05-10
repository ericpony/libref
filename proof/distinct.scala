package libref.proof

import libref.collection._
import libref.proof.DeleteLemmas._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import libref.proof.ListLemmas._
import leon.annotation._
import leon.lang._
import leon.proof._
import DeleteOps._
import DistinctOps._

import scala.language.postfixOps

case class DistinctList[V] (list : List[V]) {

  def insert (e : V) : List[V] = {
    require(distinct(list))
    DistinctListOps.insert(list, e)
  } ensuring { distinct(_) }

  def insertAll (other : List[V]) = {
    require(distinct(list) && distinct(other))
    DistinctListOps.union(list, other)
  } ensuring { distinct(_) }

  def remove (e : V) : List[V] = {
    require(distinct(list))
    DistinctListOps.remove(list, e)
  } ensuring { distinct(_) }
}

object DistinctListOps {

  def insert[V] (set : List[V], e : V) : List[V] = {
    if (set.contains(e))
      set
    else
      e :: set
  } ensuring {
    res => res.content == set.content ++ Set(e) &&
      (if (set.contains(e))
        res.size == set.size
      else
        res.size == set.size + 1) &&
      (distinct(set) ==> distinct(res))
  }

  @induct // we need this form of remove to do reduction
  def remove[V] (list : List[V], e : V) : List[V] = {
    delete(list, e)
  } ensuring { distinct(list) ==> distinct(_) }

  def union[T] (l1 : List[T], l2 : List[T]) : List[T] = {
    (l1 ++ l2).distinct
  } ensuring { distinct(_) }
}

@library
object DistinctOps {

  def distinct[T] (list : List[T]) : Boolean =
    list match {
      case Nil()        => true
      case Cons(hd, tl) => !tl.contains(hd) && distinct(tl)
    }
}

@library
object DistinctLemmas {

  @induct
  def distinct_delete[V] (list : List[V], m : V) : Boolean = {
    distinct(list) ==> distinct(delete(list, m))
  } holds /* verified by Leon */

  @induct
  def distinct_sublist[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1) && distinct(l2)
  } holds /* verified by Leon */

  @induct
  def distinct_exclusive[V] (l1 : List[V], l2 : List[V], m : V) : Boolean = {
    require(distinct(l1 ++ l2) && l2.contains(m))
    !l1.contains(m)
  } holds /* verified by Leon */

  @induct
  def distinct_sublist_delete_l[V] (l1 : List[V], l2 : List[V], m : V) : Boolean = {
    require(distinct(l1 ++ l2))
    distinct(delete(l1, m) ++ l2) because distinct_delete(l1, m)
  } holds /* verified by Leon */

  @induct
  def distinct_sublist_delete_r[V] (l1 : List[V], l2 : List[V], m : V) : Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1 ++ delete(l2, m)) because distinct_delete(l2, m)
  } holds /* verified by Leon */

  @induct
  def distinct_cons_not_contains[V] (list : List[V], e : V) : Boolean = {
    require(distinct(list) && !list.contains(e))
    distinct(e :: list)
  } holds

  def distinct_delete_content[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(distinct(l1) && distinct(l2) && l1.content == l2.content)
    delete(l1, e).content == delete(l2, e).content because
      distinct_delete_content_lemma(l1, l2, e)
  } holds

  @induct
  def distinct_contains[T] (list : List[T], e : T) : Boolean = {
    (list.contains(e) ==> list.distinct.contains(e)) &&
      (list.distinct.contains(e) ==> list.contains(e))
  } holds

  @induct
  def distinct_not_contains[T] (list : List[T], e : T) : Boolean = {
    ((!list.contains(e)) ==> (!list.distinct.contains(e))) &&
      ((!list.distinct.contains(e)) ==> (!list.contains(e)))
  } holds

  @induct
  def distinct_is_distinct[T] (list : List[T]) : Boolean = {
    distinct(list.distinct)
  } holds

  @induct
  def delete_neq_contains[T] (list : List[T], x : T, y : T) : Boolean = {
    require(list.contains(x) && x != y)
    delete(list, y).contains(x)
  } holds

  @induct
  def delete_neq_not_contains[T] (list : List[T], x : T, y : T) : Boolean = {
    require(!list.contains(x) && x != y)
    !delete(list, y).contains(x)
  } holds

  def delete_distinct_assoc[T] (list : List[T], e : T) : Boolean = {
    require(!delete(list, e).contains(e))
    delete(list, e).distinct == delete(list.distinct, e) because {
      list match {
        case Nil()        => trivial
        case Cons(hd, tl) =>
          if (hd == e) {
            distinct_not_contains(tl, hd)
          } else if (tl.distinct.contains(hd)) {
            distinct_contains(tl, hd) &&
              delete_neq_contains(tl, hd, e) &&
              distinct_contains(delete(tl, e), hd) &&
              delete_distinct_assoc(tl, e)
          } else {
            distinct_not_contains(tl, hd) &&
              delete_neq_not_contains(tl, hd, e) &&
              delete_distinct_assoc(tl, e)
          }
      }
    }
  } holds

  def delete_contains_distinct[T] (list : List[T], e : T) : Boolean = {
    require(delete(list, e).contains(e))
    list.distinct == delete(list, e).distinct because {
      list match {
        case Nil()        => trivial
        case Cons(hd, tl) =>
          if (hd == e) distinct_contains(tl, hd)
          else delete_contains_distinct(tl, e)
      }
    }
  } holds

  def cons_distinct_assoc[T] (list : List[T], e : T) : Boolean = {
    require(!list.contains(e))
    Cons(e, list.distinct) == Cons(e, list).distinct
  } holds

  def permutation_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && l1.contains(e))
    l2.contains(e)
  } holds //tbd

  def permutation_not_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && !l1.contains(e))
    !l2.contains(e)
  } holds //tbd

  def perm_delete_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && delete(l1, e).contains(e))
    delete(l2, e).contains(e) because {
      permutation_delete(l1, l2, e)
    }
  } holds //tbd

  def distinct_cons[T] (l : List[T], e : T) : Boolean = {
    require(l.contains(e))
    l.distinct == Cons(e, l).distinct because {
      delete_contains_distinct(Cons(e, l), e)
    }
  } holds

  def distinct_perm[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l1.distinct, l2.distinct) because {
      l1 match {
        case Nil()        => trivial
        case Cons(hd, tl) =>
          if (tl.contains(hd)) {
            permutation_delete(l1, l2, hd) &&
              distinct_perm(tl, delete(l2, hd)) &&
              delete_contains_distinct(l2, hd) &&
              permutation_refl(l2.distinct) &&
              distinct_cons(tl, hd) &&
              permutation_tran(tl.distinct, delete(l2, hd).distinct, l2.distinct)
          } else {
            // !tl.contains(hd) &&
            cons_distinct_assoc(tl, hd) &&
              permutation_delete(l1, l2, hd) &&
              distinct_perm(tl, delete(l2, hd)) &&
              delete_distinct_assoc(l2, hd) &&
              distinct_contains(l2, hd) &&
              permutation_cons_delete(l2.distinct, hd)
          }
      }
    }
  } holds

  @induct
  def distinct_idempotent[T] (l : List[T]) : Boolean = {
    l.distinct.distinct == l.distinct
  } holds

  def distinct_concat_comm_perm[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    permutation((l1 ++ l2).distinct, (l2 ++ l1).distinct) because {
      permutation_concat_comm(l1, l2) && distinct_perm(l1 ++ l2, l2 ++ l1)
    }
  } holds

  def distinct_concat_perm_r[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    permutation((l1 ++ l2.distinct).distinct, (l1 ++ l2).distinct) because {
      l1 match {
        case Nil()        => distinct_idempotent(l2) && permutation_refl(l2.distinct)
        case Cons(hd, tl) =>
          concat_contains(tl, l2.distinct, hd) && (
            if ((tl ++ l2.distinct).contains(hd)) {
              distinct_contains(l2, hd) && distinct_concat_perm_r(tl, l2)
            } else {
              distinct_not_contains(l2, hd) && distinct_concat_perm_r(tl, l2) &&
                permutation_cons((tl ++ l2.distinct).distinct, (tl ++ l2).distinct, hd)
            }
            )
      }
    }
  } holds

  def distinct_concat_perm_l[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    permutation((l1.distinct ++ l2).distinct, (l1 ++ l2).distinct) because {
      distinct_concat_comm_perm(l1.distinct, l2) &&
        distinct_concat_perm_r(l2, l1) &&
        permutation_tran((l1.distinct ++ l2).distinct, (l2 ++ l1.distinct).distinct, (l2 ++ l1).distinct) &&
        distinct_concat_comm_perm(l2, l1) &&
        permutation_tran((l1.distinct ++ l2).distinct, (l2 ++ l1).distinct, (l1 ++ l2).distinct)
    }
  } holds

  def distinct_concat_assoc_perm[T] (l1 : List[T], l2 : List[T], l3 : List[T]) : Boolean = {
    permutation(((l1 ++ l2).distinct ++ l3).distinct, (l1 ++ (l2 ++ l3).distinct).distinct) because {
      distinct_concat_perm_l(l1 ++ l2, l3) && // permutation(((l1 ++ l2).distinct ++ l3).distinct, ((l1 ++ l2) ++ l3).distinct)}
        permutation_concat_assoc(l1, l2, l3) && distinct_perm((l1 ++ l2) ++ l3, l1 ++ (l2 ++ l3)) && // permutation(((l1 ++ l2) ++ l3).distinct, (l1 ++ (l2 ++ l3)).distinct)
        permutation_tran(((l1 ++ l2).distinct ++ l3).distinct, ((l1 ++ l2) ++ l3).distinct, (l1 ++ (l2 ++ l3)).distinct) &&
        //
        distinct_concat_perm_r(l1, l2 ++ l3) && // permutation((l1 ++ (l2 ++ l3).distinct).distinct, (l1 ++ (l2 ++ l3)).distinct)
        permutation_comm((l1 ++ (l2 ++ l3).distinct).distinct, (l1 ++ (l2 ++ l3)).distinct) &&
        permutation_tran(((l1 ++ l2).distinct ++ l3).distinct, (l1 ++ (l2 ++ l3)).distinct, (l1 ++ (l2 ++ l3).distinct).distinct)
    }
  } holds

  @induct
  def distinct_delete_content0[V] (list : List[V], e : V) : Boolean = {
    require(distinct(list) && (list contains e))
    val L = delete(list, e)
    L.content == list.content -- Set(e) && distinct(L)
  } holds

  @induct
  def distinct_delete_content_lemma[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(distinct(l1) && distinct(l2) && l1.content == l2.content)
    val L1 = delete(l1, e)
    val L2 = delete(l2, e)
    if (l1 contains e) {
      L1.content == L2.content && distinct(L1) && distinct(L2) because
        distinct_delete_content0(l1, e) && distinct_delete_content0(l2, e)
    } else {
      L1.content == L2.content && distinct(L1) && distinct(L2) because
        delete_not_contains(l1, e) && delete_not_contains(l2, e)
    }
  } holds
}
