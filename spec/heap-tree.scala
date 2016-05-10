package libref.spec

import libref.collection._
import libref.proof.SortedListOps._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import libref.proof.MinOps._
import libref.proof.MinLemmas._
import libref.proof.DeleteOps._

import leon.lang._
import leon.proof._
import leon.annotation._
import scala.language.postfixOps
import scala.language.implicitConversions

import LeftistHeap._

/**
  * LeftistHeap as List
  */
object LeftistHeapSpec {

  /**
    * h1 ~ h2 implies h1.insert(e) ~ h2.insert(e)
    */
  def insert_invariant (h1 : HeapNode, h2 : HeapNode, e : BigInt) : Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ h2)
    h1.insert(e) ~ h2.insert(e) because {
      permutation_cons(h1, h2, e) &&
        permutation_tran(h1.insert(e), e :: h1, e :: h2) &&
        permutation_comm(h2.insert(e), e :: h2) &&
        permutation_tran(h1.insert(e), e :: h2, h2.insert(e))
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ h3 && h1 ~ h4 implies h1.merge(h2) ~ h3.merge(h4)
    */
  def merge_invariant (h1 : HeapNode, h2 : HeapNode, h3 : HeapNode, h4 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h3.isHeap && h4.isHeap && h1 ~ h3 && h2 ~ h4)
    h1.merge(h2) ~ h3.merge(h4) because {
      permutation_concat(h1, h2, h3, h4) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, h3 ++ h4) &&
        permutation_comm(h3.merge(h4), h3 ++ h4) &&
        permutation_tran(h1.merge(h2), h3 ++ h4, h3.merge(h4))
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ h2 implies h1.findMin == h2.findMin
    */
  def findMin_invariant (h1 : HeapNode, h2 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ h2)
    h1.findMin == h2.findMin because {
      if (h1.isEmpty || h2.isEmpty) trivial
      else min_permutation(h1, h2)
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ h2 implies h1.deleteMin ~ h2.deleteMin
    */
  def deleteMin_invariant (h1 : HeapNode, h2 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ h2)
    h1.deleteMin ~ h2.deleteMin because {
      if (h1.isEmpty || h2.isEmpty) trivial
      else {
        findMin_invariant(h1, h2) &&
          permutation_delete(h1, h2, h1.findMin.get) && // permutation(delete(h1, h1.findMin.get), delete(h2, h2.findMin.get))
          permutation_tran(h1.deleteMin, delete(h1, h1.findMin.get), delete(h2, h2.findMin.get)) &&
          permutation_comm(h2.deleteMin, delete(h2, h2.findMin.get)) &&
          permutation_tran(h1.deleteMin, delete(h2, h2.findMin.get), h2.deleteMin)
      }
    }
  } holds /* verified by Leon */

  /**
    * h1 ~ h2 implies h1.size == h2.size
    */
  def size_invariant (h1 : HeapNode, h2 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ h2)
    h1.size == h2.size
  } holds /* verified by Leon */

  /**
    * h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1)
    */
  def insert_comm_prop (h : HeapNode, e1 : BigInt, e2 : BigInt) : Boolean = {
    require(h.isHeap)
    h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1) because {
      permutation_cons(h.insert(e1), e1 :: h, e2) &&
        permutation_cons(h.insert(e2), e2 :: h, e1) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: h.insert(e1), e2 :: e1 :: h) &&
        permutation_tran(h.insert(e2).insert(e1), e1 :: h.insert(e2), e1 :: e2 :: h) &&
        permutation_car_swap(h, e1, e2) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: e1 :: h, e1 :: e2 :: h) &&
        permutation_tran(h.insert(e1).insert(e2), e1 :: e2 :: h, h.insert(e2).insert(e1))
    }
  } holds /* verified by Leon */

  /**
    * h1.merge(h2) ~ h2.merge(h1)
    */
  def merge_comm_prop (h1 : HeapNode, h2 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap)
    h1.merge(h2) ~ h2.merge(h1) because {
      permutation_concat_comm(h1, h2) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, h2 ++ h1) &&
        permutation_tran(h1.merge(h2), h2 ++ h1, h2.merge(h1))
    }
  } holds /* verified by Leon */

  /**
    * (h1.merge(h2)).merge(h3) ~ h1.merge(h2.merge(h3))
    */
  def merge_assoc_prop (h1 : HeapNode, h2 : HeapNode, h3 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h3.isHeap)
    h1.merge(h2).merge(h3) ~ h1.merge(h2.merge(h3)) because {
      permutation_append(h1.merge(h2), h1 ++ h2, h3) &&
        permutation_tran(h1.merge(h2).merge(h3), h1.merge(h2) ++ h3, h1 ++ h2 ++ h3) &&
        permutation_prepend(h1, h2.merge(h3), h2 ++ h3) &&
        permutation_tran(h1.merge(h2.merge(h3)), h1 ++ h2.merge(h3), h1 ++ (h2 ++ h3)) &&
        permutation_concat_assoc(h1, h2, h3) &&
        permutation_tran(h1.merge(h2).merge(h3), h1 ++ h2 ++ h3, h1 ++ (h2 ++ h3)) &&
        permutation_tran(h1.merge(h2).merge(h3), h1 ++ (h2 ++ h3), h1.merge(h2.merge(h3)))
    }
  } holds /* verified by Leon */

  /**
    * foldl(Empty(), insert, l1 ++ l2) ==
    * foldl(Empty(), insert, l1).merge(foldl(Empty(), insert, l2))
    */
  def composition_prop (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L ~ L1.merge(L2) because {
      permutation_append(L1, l1, l2) &&
        permutation_prepend(L1, L2, l2) &&
        permutation_tran(L1 ++ L2, L1 ++ l2, l1 ++ l2) &&
        permutation(l1 ++ l2, L) && // STRANGE: shouldn't need this line
        permutation_tran(L1 ++ L2, l1 ++ l2, L) &&
        permutation_tran(L, L1 ++ L2, L1.merge(L2))
    }
  } holds /* verified by Leon */

}

/**
  * LeftistHeap as Set
  */
object LeftistHeapSpec0 {

  implicit def toHeap (h : HeapNode) = LeftistHeapOps(h)

  def insert_comm_prop (h : HeapNode, e1 : BigInt, e2 : BigInt) : Boolean = {
    require(h.isHeap)
    h.insert(e1).insert(e2) ~~ h.insert(e2).insert(e1)
  } holds /* verified by Leon */

  def merge_comm_prop (h1 : HeapNode, h2 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap)
    h1.merge(h2) ~~ h2.merge(h1)
  } holds /* verified by Leon */

  def merge_assoc_prop (h1 : HeapNode, h2 : HeapNode, h3 : HeapNode) : Boolean = {
    require(h1.isHeap && h2.isHeap && h3.isHeap)
    h1.merge(h2).merge(h3) ~~ h1.merge(h2.merge(h3))
  } holds /* verified by Leon */

  def composition_prop (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L ~~ L1.merge(L2)
  } holds /* verified by Leon */

}

object LeftistHeap {

  sealed abstract class HeapNode {
    def isEmpty = this == Empty()

    def size : BigInt = {
      this match {
        case Empty()          => BigInt(0)
        case Node(_, v, l, r) => l.size + 1 + r.size
      }
    } ensuring (_ >= 0)
  }

  case object HeapNode {
    implicit def toList (h : HeapNode) : List[BigInt] = LeftistHeapOps(h).toList

    implicit def toLeftistHeap (h : HeapNode) : LeftistHeapOps = LeftistHeapOps(h)
  }

  case class Empty () extends HeapNode

  case class Node (rk : BigInt, value : BigInt, left : HeapNode, right : HeapNode) extends HeapNode

  /**
    * A leftist heap.
    * Each node maintains a "rank", which records the length of the path between
    * the node and the right most leaf.
    * Invariants:
    * 1. For each node, the height of its right subtree <= that of its left subtree.
    * 2. For each node, the rank of its right child <= the rank of its left child.
    */
  case class LeftistHeapOps (heap : HeapNode) {

    def findMin : Option[BigInt] = {
      require(heap.isHeap)
      heap match {
        case Empty()          => None[BigInt]()
        case Node(_, v, _, _) => Some(v)
      }
    } ensuring { res =>
      (!heap.isEmpty) ==> (res.isDefined && res.get == min(heap) because {
        val Node(_, v, l, r) = heap
        if (l == Empty() && r == Empty()) trivial
        else {
          ((!l.isEmpty) ==> (l.findMin.get == min(l))) &&
            ((!r.isEmpty) ==> (r.findMin.get == min(r))) &&
            min_concat_lemma(l, r)
        }
      })
    } /* verified by Leon */

    def deleteMin : HeapNode = {
      require(heap.isHeap)
      heap match {
        case Empty()          => heap
        case Node(_, _, l, r) => l.merge(r)
      }
    } ensuring { res =>
      res.isHeap &&
        res.size == max(0, heap.size - 1) &&
        ((!heap.isEmpty) ==> (permutation(res.toList, heap.toList.tail))) &&
        ((!heap.isEmpty) ==> (permutation(res, delete(heap, heap.findMin.get)))) &&
        res.content.subsetOf(heap.content) &&
        ((!heap.isEmpty) ==> (heap.content == res.content ++ Set(heap.findMin.get))) &&
        ((!heap.isEmpty && !res.isEmpty) ==> (heap.findMin.get <= res.findMin.get))
    } /* verified by Leon */

    def merge (h : HeapNode) : HeapNode = {
      require(heap.isHeap && h.isHeap)
      LeftistHeap.merge(heap, h)
    } ensuring { res =>
      res.isHeap &&
        res.size == heap.size + h.size &&
        res.content == heap.content ++ h.content &&
        permutation(res, heap ++ h) because { LeftistHeap.merge_perm(heap, h) } &&
        ((!res.isEmpty) ==> (res.findMin.get == min(heap.findMin.getOrElse(res.findMin.get), h.findMin.getOrElse(res.findMin.get))))
    } /* verified by Leon */

    def insert (element : BigInt) : HeapNode = {
      require(heap.isHeap)
      merge(Node(1, element, Empty(), Empty()))
    } ensuring { res =>
      res.isHeap &&
        res.size == heap.size + 1 &&
        res.content == heap.content ++ Set(element) &&
        permutation(res, element :: heap) because {
        permutation_prepend(heap, Node(1, element, Empty(), Empty()), Cons(element, Nil())) &&
          permutation_tran(res, heap ++ Node(1, element, Empty(), Empty()), heap ++ Cons(element, Nil())) &&
          permutation_concat_comm(heap, Cons(element, Nil())) &&
          permutation_tran(res, heap ++ Cons(element, Nil()), element :: heap)
      }
    } /* verified by Leon */

    def isHeap : Boolean = heap match {
      case Empty()                 => true
      case Node(_, v, left, right) =>
        left.isHeap && right.isHeap &&
          rightHeight(left) >= rightHeight(right) &&
          isPartiallyOrdered(v, left, right)
    }

    def toList : List[BigInt] = {
      heap match {
        case Empty()          => Nil[BigInt]()
        case Node(_, v, l, r) => v :: (l.toList ++ r.toList)
      }
    } ensuring { res =>
      res.size == heap.size &&
        res.content == heap.content &&
        (heap match {
          case Empty()          => true
          case Node(_, v, l, r) =>
            permutation(res, v :: (l.toList ++ r.toList)) because
              permutation_refl(res)
        })
    }

    def toSortedList : List[BigInt] = {
      require(heap.isHeap)
      heap match {
        case Empty() => Nil[BigInt]()
        case _       => findMin.get :: deleteMin.toSortedList
      }
    } ensuring { res =>
      res.size == heap.size &&
        res.content == heap.content &&
        isSorted(res)
    }

    def ~ (l : List[BigInt]) : Boolean = permutation(heap, l)

    def ~~ (l : List[BigInt]) : Boolean = heap.content == l.content
  }

  //////////////////////////////////////////////////////////

  def rightHeight (h : HeapNode) : BigInt = {
    h match {
      case Empty()          => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (_ >= 0)

  def build (v : BigInt, l : HeapNode, r : HeapNode) : HeapNode = {
    require(l.isHeap && r.isHeap && isPartiallyOrdered(v, l, r))
    if (rightHeight(l) >= rightHeight(r)) Node(rightHeight(r) + 1, v, l, r)
    else Node(rightHeight(l) + 1, v, r, l)
  } ensuring { res =>
    res.isHeap &&
      permutation(res, v :: (l ++ r)) because {
      if (rightHeight(l) >= rightHeight(r)) true
      else {
        permutation(res, v :: (r ++ l)) &&
          permutation_concat_comm(l, r) &&
          permutation_cons(r ++ l, l ++ r, v) &&
          permutation_tran(res, v :: (r ++ l), v :: (l ++ r))
      }
    }
  } /* verified by Leon */

  def isPartiallyOrdered (value : BigInt, h1 : HeapNode, h2 : HeapNode) = {
    require(h1.isHeap && h2.isHeap)
    (h1, h2) match {
      case (Empty(), Empty())                     => true
      case (Node(_, v1, _, _), Empty())           => value <= v1
      case (Empty(), Node(_, v2, _, _))           => value <= v2
      case (Node(_, v1, _, _), Node(_, v2, _, _)) => value <= v1 && value <= v2
    }
  }

  def merge (h1 : HeapNode, h2 : HeapNode) : HeapNode = {
    require(h1.isHeap && h2.isHeap)
    (h1, h2) match {
      case (Empty(), _)                               => h2
      case (_, Empty())                               => h1
      case (Node(_, v1, l1, r1), Node(_, v2, l2, r2)) =>
        if (v1 <= v2) build(v1, l1, merge(r1, h2))
        else build(v2, l2, merge(h1, r2))
    }
  } ensuring { res =>
    res.isHeap &&
      res.size == h1.size + h2.size &&
      res.content == h1.content ++ h2.content &&
      (
        res match {
          case Empty()          => true
          case Node(_, v, _, _) =>
            (h1, h2) match {
              case (Empty(), Empty())                     => true // impossible case
              case (Empty(), Node(_, v2, _, _))           => v == v2
              case (Node(_, v1, _, _), Empty())           => v == v1
              case (Node(_, v1, _, _), Node(_, v2, _, _)) => v == min(v1, v2)
            }
        }
        )
  } /* verified by Leon */

  /** One verification condition of this lemma may need more than 5 seconds to verify. */
  def merge_perm[T] (heap : HeapNode, h : HeapNode) : Boolean = {
    require(heap.isHeap && h.isHeap)
    permutation(merge(heap, h), heap ++ h) because {
      (heap, h.heap) match {
        case (Empty(), _)                               => permutation_refl(h)
        case (_, Empty())                               => permutation_refl(heap)
        case (Node(_, v1, l1, r1), Node(_, v2, l2, r2)) =>
          if (v1 <= v2) {
            merge_perm(r1, h) && // permutation(merge(r1, h), r1 ++ h)
              concat_permutation(l1, merge(r1, h), r1 ++ h) && // permutation(l1 ++ (merge(r1, h)), l1 ++ (r1 ++ h))
              permutation_cons(l1 ++ (merge(r1, h)), l1 ++ (r1 ++ h), v1) && // permutation(v1 :: (l1 ++ (merge(r1, h))), v1 :: (l1 ++ (r1 ++ h)))
              permutation_tran(build(v1, l1, merge(r1, h)), v1 :: (l1 ++ (merge(r1, h))), v1 :: (l1 ++ (r1 ++ h))) &&
              //
              permutation_concat_assoc(l1, r1, h) && // permutation(l1 ++ r1 ++ h, l1 ++ (r1 ++ h))
              permutation_cons(l1 ++ r1 ++ h, l1 ++ (r1 ++ h), v1) && // permutation(v1 :: (l1 ++ r1 ++ h), v1 :: (l1 ++ (r1 ++ h)))
              permutation_comm(v1 :: (l1 ++ r1 ++ h), v1 :: (l1 ++ (r1 ++ h))) && // permutation(v1 :: (l1 ++ (r1 ++ h)), v1 :: (l1 ++ r1 ++ h))
              permutation_tran(build(v1, l1, merge(r1, h)), v1 :: (l1 ++ (r1 ++ h)), v1 :: (l1 ++ r1 ++ h))
          } else {
            merge_perm(heap, r2) && // permutation(merge(heap, r2), heap ++ r2)
              concat_permutation(l2, merge(heap, r2), heap ++ r2) && // permutation(l2 ++ (merge(heap, r2)), l2 ++ (heap ++ r2))
              permutation_cons(l2 ++ (merge(heap, r2)), l2 ++ (heap ++ r2), v2) && // permutation(v2 :: (l2 ++ (merge(heap, r2))), v2 :: (l2 ++ (heap ++ r2)))
              permutation_tran(build(v2, l2, merge(heap, r2)), v2 :: (l2 ++ (merge(heap, r2))), v2 :: (l2 ++ (heap ++ r2))) &&
              //
              permutation_concat_assoc(l2, heap, r2) && // permutation(l2 ++ heap ++ r2, l2 ++ (heap ++ r2))
              permutation_comm(l2 ++ heap ++ r2, l2 ++ (heap ++ r2)) && // permutation(l2 ++ (heap ++ r2), l2 ++ heap ++ r2)
              permutation3(l2, heap, r2) && // permutation(l2 ++ heap ++ r2, heap ++ l2 ++ r2)
              permutation_concat_assoc(heap, l2, r2) && // permutation(heap ++ l2 ++ r2, heap ++ (l2 ++ r2))
              permutation_tran(l2 ++ heap ++ r2, heap ++ l2 ++ r2, heap ++ (l2 ++ r2)) &&
              permutation_tran(l2 ++ (heap ++ r2), l2 ++ heap ++ r2, heap ++ (l2 ++ r2)) &&
              //
              permutation_cons(l2 ++ (heap ++ r2), heap ++ (l2 ++ r2), v2) && // permutation(v2 :: (l2 ++ (heap ++ r2)), v2 :: (heap ++ (l2 ++ r2)))
              cons_concat_perm2(heap, l2 ++ r2, v2) && // permutation(v2 :: (heap ++ (l2 ++ r2)), heap ++ (v2 :: (l2 ++ r2)))
              permutation_tran(v2 :: (l2 ++ (heap ++ r2)), v2 :: (heap ++ (l2 ++ r2)), heap ++ (v2 :: (l2 ++ r2))) &&
              //
              permutation_tran(build(v2, l2, merge(heap, r2)), v2 :: (l2 ++ (heap ++ r2)), heap ++ (v2 :: (l2 ++ r2)))
          }
      }
    }
  } holds

  def foldl_insert (heap : HeapNode, list : List[BigInt]) : HeapNode = {
    require(heap.isHeap)
    list match {
      case Nil()        => heap
      case Cons(hd, tl) => foldl_insert(heap.insert(hd), tl)
    }
  } ensuring { res =>
    res.isHeap &&
      res.content == (heap.content ++ list.content) &&
      permutation(res, heap ++ list) because {
      list match {
        case Nil()        => permutation_refl(res)
        case Cons(hd, tl) =>
          permutation_append(heap.insert(hd), hd :: heap, tl) && // permutation(heap.insert(hd) ++ tl, (hd :: heap) ++ tl)
            permutation_cons_tail(heap, tl, hd) && // permutation(heap ++ (hd :: tl), (hd :: heap) ++ tl)
            permutation_comm(heap ++ (hd :: tl), (hd :: heap) ++ tl) && // permutation((hd :: heap) ++ tl, heap ++ (hd :: tl))
            permutation_tran(heap.insert(hd) ++ tl, (hd :: heap) ++ tl, heap ++ (hd :: tl)) &&
            permutation_tran(res, heap.insert(hd) ++ tl, heap ++ (hd :: tl))
      }
    }
  } /* verified by Leon */

}
