package libref.proof

import libref.collection.PairList._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

@library
object PairListLemmas {

  @induct
  def permutation_refl[K, V] (list : PList[K, V]) : Boolean = {
    permutation(list, list)
  } holds

  def permutation_comm[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l2, l1) because permutation_comm_lemma(l1, l2)
  } holds

  def permutation_tran[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    permutation(l1, l3) because permutation_tran_lemma(l1, l2, l3)
  } holds

  def permutation_content[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    l1.content == l2.content because permutation_content_lemma(l1, l2)
  } holds

  def permutation_concat_comm[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    permutation(l1 ++ l2, l2 ++ l1) because
      permutation_concat_comm_lemma(l1, l2)
  } holds

  def permutation_concat_assoc[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V]) = {
    permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
      permutation_concat_assoc_lemma(l1, l2, l3)
  } holds

  @induct
  def permutation_car_swap[K, V] (list : PList[K, V], a : Pair[K, V], b : Pair[K, V]) : Boolean = {
    permutation(a :: b :: list, b :: a :: list)
  } holds

  @induct
  def permutation_cons_tail[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    if (l1 == PNil[K, V]()) {
      permutation(l1 ++ (e :: l2), (e :: l1) ++ l2) because
        permutation_refl(e :: l2)
    } else {
      val h1 = l1.head
      permutation(l1 ++ (e :: l2), (e :: l1) ++ l2) because
        check {
          // permutation (l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2)
          permutation_cons_tail(l1.tail, l2, e) &&
            // permutation (h1 :: (l1.tail ++ (e :: l2)), h1 :: (e :: l1.tail) ++ l2)
            permutation_cons(l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2, h1) &&
            // permutation (h1 :: e :: l1.tail ++ l2, e :: h1 :: l1.tail ++ l2)
            permutation_car_swap(l1.tail ++ l2, h1, e) &&
            permutation_tran_lemma(l1 ++ (e :: l2),
                                    h1 :: e :: l1.tail ++ l2,
                                    (e :: l1) ++ l2)
        }
    }
  } holds

  def permutation_eq[K, V] (s : PList[K, V], t : PList[K, V]) : Boolean = {
    require(s == t)
    permutation(s, t) because {
      s.isEmpty || permutation_eq(s.tail, t.tail)
    }
  } holds

  def permutation_delete_cons[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(l2 != PNil[K, V]())
    val h2 = l2.head
    permutation((l1 ++ l2).delete(h2), l1 ++ (l2.tail)) because {
      if (l1 == PNil[K, V]) {
        permutation_refl(l2.tail)
      } else {
        val h1 = l1.head
        if (h1 == h2) {
          permutation_cons_tail(l1.tail, l2.tail, h1)
        } else {
          permutation_delete_cons(l1.tail, l2) &&
            permutation_cons((l1.tail ++ l2).delete(h2), l1.tail ++ (l2.tail), h1)
        }
      }
    }
  } holds

  @induct
  private def permutation_concat_comm_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    if (l1 == PNil[K, V]()) {
      permutation(l1 ++ l2, l2 ++ l1) because
        permutation_refl(l2)
    } else {
      val h1 = l1.head
      permutation(l1 ++ l2, l2 ++ l1) because
        check {
          (l2 ++ l1 contains h1) &&
            // permutation (l1.tail ++ l2, l2 ++ l1.tail)
            permutation_concat_comm(l1.tail, l2) &&
            (l1 ++ l2).tail == l1.tail ++ l2 &&
            // permutation (delete (l2 ++ l1, h1), l2 ++ l1.tail)
            permutation_delete_cons(l2, l1) &&
            // permutation (l2 ++ l1.tail, delete (l2 ++ l1, h1))
            permutation_comm_lemma((l2 ++ l1).delete(h1), l2 ++ l1.tail) &&
            permutation_tran_lemma(l1.tail ++ l2, l2 ++ l1.tail, (l2 ++ l1).delete(h1))
        }
    }
  } holds

  @induct
  def permutation_delete_head[K, V] (t1 : PList[K, V], l2 : PList[K, V], h1 : Pair[K, V]) : Boolean = {
    require(permutation(h1 :: t1, l2))
    permutation(t1, delete(l2, h1))
  } holds

  @induct
  def permutation_delete[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l1.delete(e), l2.delete(e)) because {
      if (l1 == PNil[K, V]())
        trivial
      else {
        val h1 = l1.head
        if (e == h1)
          permutation_delete_head(l1.tail, l2, h1)
        else {
          delete_contains(l2, h1, e) &&
            permutation_delete(l1.tail, l2.delete(h1), e) &&
            delete_comm(l2, e, h1)
        }
      }
    }
  } holds

  def permutation_delete_cons[K, V] (l1 : PList[K, V], h2 : Pair[K, V], t2 : PList[K, V]) : Boolean = {
    require(permutation(l1.delete(h2), t2) && l1.contains(h2))
    permutation(l1, PCons(h2, t2)) because {
      if (l1 == PNil[K, V]()) {
        trivial
      } else {
        val h1 = l1.head
        if (h1 == h2) {
          trivial
        } else {
          (PCons(h2, t2) contains h1) &&
            delete_comm(l1, h1, h2) &&
            permutation_delete_cons(l1.tail, h2, t2 delete h1)
        }
      }
    }
  } holds

  @induct
  def permutation_comm_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    if (l1 == PNil[K, V]()) {
      permutation(l2, l1)
    } else {
      permutation(l2, l1) because
        check {
          permutation_content(l1, l2) &&
            l1.contains(l2.head) &&
            permutation_comm(l1.tail, l2 delete l1.head) &&
            permutation_delete_cons(l2, l1.head, l1.tail) &&
            permutation_delete(l2, l1, l2.head)
        }
    }
  } holds

  @induct
  def permutation_tran_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    if (l1 == PNil[K, V]()) {
      permutation(l1, l3)
    } else {
      val h1 = l1.head
      permutation(l1, l3) because
        // l3 contains h1
        permutation_contains_lemma(l2, l3, h1) &&
          // permutation (delete (l2, h1), delete (l3, h1))
          permutation_delete(l2, l3, h1) &&
          // permutation (l1.tail, delete (l3, h1))
          permutation_tran_lemma(l1.tail, l2 delete h1, l3 delete h1)
    }
  } holds

  def permutation_tran_lemma2[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V], l4 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3) && permutation(l3, l4))
    permutation(l1, l4) because
      permutation_tran_lemma(l1, l2, l3) &&
        permutation_tran_lemma(l1, l3, l4)
  } holds

  @induct
  def permutation_cons[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(PCons(e, l1), PCons(e, l2))
  } holds

  @induct
  def permutation_content_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    if (l1 == PNil[K, V]()) {
      l1.content == l2.content
    } else {
      val h1 = l1.head
      l1.content == l2.content because
        l1.content == l1.tail.content ++ Set(h1) &&
          l2.content == l2.delete(h1).content ++ Set(h1) &&
          check { delete_content(l2, h1) } &&
          check { permutation_content_lemma(l1.tail, l2.delete(h1)) }
    }
  } holds

  def permutation_contains_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(permutation(l1, l2) && l1.contains(e))
    val h = l1.head
    if (h == e) {
      l2.contains(e)
    } else {
      /* induction */
      l2.contains(e) because {
        check { permutation_contains_lemma(l1.tail, l2 delete h, e) }
      }
    }
  } holds

  @induct
  def permutation_prefix[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(PCons(e, l1), PCons(e, l2))
  } holds

  @induct
  def permutation_append[K, V] (l1 : PList[K, V], l2 : PList[K, V], ll : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    if (l1 == PNil[K, V]()) {
      permutation(l1 ++ ll, l2 ++ ll) because
        check { permutation_refl(ll) }
    } else {
      val h1 = l1.head
      permutation(l1 ++ ll, l2 ++ ll) because
        check {
          permutation_append(l1.tail, l2.delete(h1), ll) &&
            l1.tail ++ ll == (l1 ++ ll).tail &&
            l2.delete(h1) ++ ll == (l2 ++ ll).delete(h1) &&
            delete_concat(l2, ll, h1)
        }
    }
  } holds

  @induct
  private def permutation_concat_assoc_lemma[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V]) : Boolean = {
    if (l1 == PNil[K, V]()) {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_refl(l2 ++ l3)
    } else {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_concat_assoc_lemma(l1.tail, l2, l3) &&
          permutation_cons(l1.tail ++ l2 ++ l3, l1.tail ++ (l2 ++ l3), l1.head)
    }
  } holds

  def hasKey_contains[K, V] (map : PList[K, V], key : K) : Boolean = {
    require(map.hasKey(key))
    map.contains(map.get(key).get)
  } holds

  def permutation_hasKey_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    require(permutation(map1, map2))
    (map1.hasKey(key) ==> (map2.hasKey(key) because { map2.contains(map1.get(key).get) })) &&
      (map2.hasKey(key) ==> (map1.hasKey(key) because { map1.contains(map2.get(key).get) }))
  } holds /* verified by Leon */

  /**
    * WARNING: Leon may take 2~30 seconds to verify this lemma.
    **/
  def permutation_getAll_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    require(permutation(map1, map2))
    val l1 = map1.getAll(key)
    val l2 = map2.getAll(key)

    permutation(l1, l2) because {
      if (l1 == PNil[K, V]())
        permutation(l1, l2) because
          (l1 == PNil[K, V]()) == !l1.hasKey(key) &&
            (l2 == PNil[K, V]()) == !l2.hasKey(key) &&
            permutation_hasKey_lemma(map1, map2, key)
      else {
        val h1 = map1.get(key).get
        val m1 = map1.delete(h1)
        val m2 = map2.delete(h1)
        l1.head == h1 &&
          check {
            l2.contains(h1) because
              getAll_contain_lemma(map2, h1)
          } &&
          check {
            permutation(m1, m2) because
              permutation_delete(map1, map2, h1)
          } &&
          check {
            permutation(m1.getAll(key), m2.getAll(key)) because
              permutation_getAll_lemma(m1, m2, key)
          } &&
          check { m1.getAll(key) == l1.tail because getAll_delete_lemma(map1, h1, key) } &&
          check { m2.getAll(key) == l2.delete(h1) because getAll_delete_lemma(map2, h1, key) } &&
          permutation(l2.delete(h1), l1.tail) &&
          permutation_delete_cons(l2, h1, l1.tail)
      }
    }
  } holds /* verified by Leon */

  @induct
  def getAll_delete_lemma[K, V] (map : PList[K, V], e : Pair[K, V], key : K) : Boolean = {
    require(map.contains(e) && e.key == key)
    map.delete(e).getAll(key) == map.getAll(key).delete(e)
  } holds /* verified by Leon */

  @induct
  def getAll_contain_lemma[K, V] (map : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(map contains e)
    map.getAll(e.key) contains e
  } holds /* verified by Leon */

  def concat_permutation[K, V] (ll : PList[K, V], l1 : PList[K, V], l2 : PList[K, V]) = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      concat_permutation_lemma(ll, l1, l2)
  } holds

  def concat_permutation_lemma[K, V] (ll : PList[K, V], l1 : PList[K, V], l2 : PList[K, V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      // permutation (l1 ++ ll, l2 ++ ll)
      permutation_append(l1, l2, ll) &&
        // permutation (ll ++ l1, l1 ++ ll)
        permutation_concat_comm_lemma(ll, l1) &&
        // permutation (l2 ++ ll, ll ++ l2)
        permutation_concat_comm_lemma(l2, ll) &&
        permutation_tran_lemma(ll ++ l1, l1 ++ ll, l2 ++ ll) &&
        permutation_tran_lemma(ll ++ l1, l2 ++ ll, ll ++ l2)
  } holds

  def permutation_delete_cons[K, V] (list : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(list contains e)
    val h = list.head
    permutation(PCons(e, list delete e), list) because {
      permutation_refl(list.delete(e))
    }
  } holds

  @induct
  def delete_contains[K, V] (list : PList[K, V], a : Pair[K, V], b : Pair[K, V]) = {
    require(list.contains(a) && a != b)
    list.delete(b).contains(a)
  } holds

  @induct
  def delete_content[K, V] (list : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(list.contains(e))
    list.content == list.delete(e).content ++ Set(e)
  } holds

  @induct
  def delete_concat[K, V] (l1 : PList[K, V], l2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(l1 contains e)
    (l1).delete(e) ++ l2 == (l1 ++ l2).delete(e)
  } holds

  @induct
  def delete_comm[K, V] (list : PList[K, V], a : Pair[K, V], b : Pair[K, V]) : Boolean = {
    list.delete(a).delete(b) == list.delete(b).delete(a)
  } holds

  /* Apply this to prove permutation(l1, l3) by transitivity. */
  def permutation_by_tran[K, V] (l1 : PList[K, V], l2 : PList[K, V], l3 : PList[K, V]) : Boolean = {
    permutation(l1, l2) && permutation(l2, l3) && permutation_tran(l1, l2, l3)
  } ensuring {
    res => !res || permutation(l1, l3)
  }

  def cons_merge_assoc[K, V] (e : Pair[K, V], list1 : PList[K, V], list2 : PList[K, V]) : Boolean = {
    e :: (list1 ++ list2) == (e :: list1) ++ list2
  } holds /* proven by Leon */

  def cons_delete_perm[K, V] (list : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(list.contains(e))
    permutation(e :: list.delete(e), list) because {
      permutation_refl(list.delete(e)) &&
        permutation_delete_cons(list, e, list.delete(e))
    }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm1[K, V] (h : Pair[K, V], t : PList[K, V], pos : PList[K, V], neg : PList[K, V]) : Boolean = {
    require(permutation(pos.delete(h) ++ neg, t) && pos.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (pos.delete(h) ++ neg), h :: t) because {
        /* for permutation(pos ++ neg, h::(pos.delete(h))) */
        cons_merge_assoc(h, pos.delete(h), neg) &&
          permutation(pos ++ neg, (h :: pos.delete(h)) ++ neg) because {
          permutation(pos, h :: pos.delete(h)) because {
            cons_delete_perm(pos, h) && permutation_comm(h :: pos.delete(h), pos)
          } && permutation_append(pos, h :: pos.delete(h), neg)
        } &&
          /* for permutation(h::(pos.delete(h)), h::t) */
          permutation_cons(pos.delete(h) ++ neg, t, h)
      }
    }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm2[K, V] (h : Pair[K, V], t : PList[K, V], pos : PList[K, V], neg : PList[K, V]) : Boolean = {
    require(permutation(pos ++ neg.delete(h), t) && neg.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (pos ++ neg.delete(h)), h :: t) because {
        /* for permutation(pos ++ neg, h::(pos ++ neg.delete(h))) */
        cons_merge_assoc(h, pos, neg.delete(h)) &&
          permutation(pos ++ neg, (h :: pos) ++ neg.delete(h)) because {
          permutation_by_tran(pos ++ neg, pos ++ (h :: neg.delete(h)), (h :: pos) ++ neg.delete(h)) because {
            /* for permutation(pos ++ neg, pos ++ (h::neg.delete(h))) */
            permutation_by_tran(pos ++ neg, neg ++ pos, pos ++ (h :: neg.delete(h))) because {
              /* for permutation(pos ++ neg, neg ++ pos) */
              permutation_concat_comm(pos, neg) &&
                /* for permutation(neg ++ pos, pos ++ (h::neg.delete(h))) */
                permutation_by_tran(neg ++ pos, (h :: neg.delete(h)) ++ pos, pos ++ (h :: neg.delete(h))) because {
                cons_delete_perm(neg, h) && permutation_comm(h :: neg.delete(h), neg) &&
                  permutation_append(neg, h :: neg.delete(h), pos) &&
                  permutation_concat_comm(h :: neg.delete(h), pos)
              }
            } &&
              /* for permutation(pos ++ (h::neg.delete(h)), (h::pos) ++ neg.delete(h)) */
              permutation_cons_tail(pos, neg.delete(h), h)
          }
        } &&
          /* for permutation(h::(pos ++ neg.delete(h)), h::t) */
          permutation_cons(pos ++ neg.delete(h), t, h)
      }
    }
  } holds /* proven by Leon */

  def filter_union_perm[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean) : Boolean = {
    permutation(list.filter(p) ++ list.filterNot(p), list) because {
      list match {
        case PNil()              => trivial
        case PCons(h, t) if p(h) => filter_union_perm(t, p) && filter_union_perm1(h, t, list.filter(p), list.filterNot(p))
        case PCons(h, t)         => filter_union_perm(t, p) && filter_union_perm2(h, t, list.filter(p), list.filterNot(p))
      }
    }
  } holds /* proven by Leon */

  def filter_union_size[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean) : Boolean = {
    (list.filter(p) ++ list.filterNot(p)).size == list.size because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  def filter_union_content[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean) : Boolean = {
    (list.filter(p) ++ list.filterNot(p)).content == list.content because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  @induct
  def forall_p_not_in[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean, e : Pair[K, V]) : Boolean = {
    require(list.forall(p) && !p(e))
    !list.contains(e)
  } holds /* proven by Leon */

  @induct
  def filter_sound[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean, e : Pair[K, V]) : Boolean = {
    require(list.filter(p).contains(e))
    list.contains(e) && p(e)
  } holds /* proven by Leon */

  @induct
  def filter_complete[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean, e : Pair[K, V]) : Boolean = {
    require(list.contains(e) && p(e))
    list.filter(p).contains(e)
  } holds /* proven by Leon */

  def disjoint_by_pred[K, V] (pos : PList[K, V], neg : PList[K, V], p : Pair[K, V] => Boolean) : Boolean = {
    require(pos.forall(p) && neg.forall(!p(_)))
    (pos & neg) == PNil[K, V]() because {
      pos match {
        case PNil()      => trivial
        case PCons(h, t) => check {
          !neg.contains(h) because forall_p_not_in(neg, (x : Pair[K, V]) => !p(x), h)
        } && disjoint_by_pred(t, neg, p)
      }
    }
  } holds /* proven by Leon */

  def filter_disjoint[K, V] (list : PList[K, V], p : Pair[K, V] => Boolean) : Boolean = {
    (list.filter(p) & list.filterNot(p)) == PNil[K, V]() because
      disjoint_by_pred(list.filter(p), list.filterNot(p), p)
  } holds /* proven by Leon */

  def permutation_filter_contains[K, V] (list1 : PList[K, V], list2 : PList[K, V], p : Pair[K, V] => Boolean, x : Pair[K, V]) : Boolean = {
    require(permutation(list1, list2) && list1.filter(p).contains(x))
    list2.filter(p).contains(x) because {
      filter_sound(list1, p, x) && permutation_contains_lemma(list1, list2, x) && filter_complete(list2, p, x)
    }
  } holds /* proven by Leon */

}
