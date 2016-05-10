package libref.proof

import libref.collection._
import libref.proof.ListLemmas._
import libref.proof.DeleteLemmas._
import libref.proof.DeleteOps._
import libref.proof.PermutationOps._

import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

@library
object PermutationOps {
  /**
    * Tell whether a list is a permutation of the other
    * @param l1, l2 are lists
    * @return whether l1 is a permutation of l2
    */
  def permutation[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    if (l1 == Nil[V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res => res ==> (
    l1.size == l2.size &&
      permutation(l2, l1) && // REMOVE this line!
      l1.content == l2.content
    )
  }
}

@library
object PermutationLemmas {

  @induct
  def permutation_refl[V] (list : List[V]) : Boolean = {
    permutation(list, list)
  } holds

  /* @induct doesn't work for this simple lemma */
  def permutation_eq[V] (s : List[V], t : List[V]) : Boolean = {
    require(s == t)
    permutation(s, t) because {
      s.isEmpty || permutation_eq(s.tail, t.tail)
    }
  } holds

  def permutation_append[V] (l1 : List[V], l2 : List[V], ll : List[V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l1 ++ ll, l2 ++ ll) because {
      if (l1 == Nil[V]()) {
        check { permutation_refl(ll) }
      } else {
        val h1 = l1.head
        // permutation(l1 ++ ll, l2 ++ ll) because
        permutation_append(l1.tail, delete(l2, h1), ll) &&
          l1.tail ++ ll == (l1 ++ ll).tail &&
          delete(l2, h1) ++ ll == delete(l2 ++ ll, h1) &&
          delete_concat(l2, ll, h1)
      }
    }
  } holds

  def permutation_prepend[V] (ll : List[V], l1 : List[V], l2 : List[V]) = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      concat_permutation(ll, l1, l2)
  } holds

  @induct
  def permutation_car_swap[V] (list : List[V], a : V, b : V) : Boolean = {
    permutation(a :: b :: list, b :: a :: list)
  } holds

  def permutation_cons_tail[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    permutation(l1 ++ (e :: l2), (e :: l1) ++ l2) because {
      if (l1 == Nil[V]()) {
        check { permutation_refl(e :: l2) }
      } else {
        val h1 = l1.head
        // permutation (l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2)
        permutation_cons_tail(l1.tail, l2, e) &&
          // permutation (h1 :: (l1.tail ++ (e :: l2)), h1 :: (e :: l1.tail) ++ l2)
          permutation_cons(l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2, h1) &&
          // permutation (h1 :: e :: l1.tail ++ l2, e :: h1 :: l1.tail ++ l2)
          permutation_car_swap(l1.tail ++ l2, h1, e) &&
          permutation_tran(l1 ++ (e :: l2),
                            h1 :: e :: l1.tail ++ l2,
                            (e :: l1) ++ l2)
      }
    }
  } holds

  def permutation_delete_cons[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    require(l2 != Nil[V]())
    val h2 = l2.head
    permutation(delete(l1 ++ l2, h2), l1 ++ (l2.tail)) because {
      if (l1 == Nil[V])
        permutation_refl(l2.tail)
      else {
        val h1 = l1.head
        if (h1 == h2)
          permutation_cons_tail(l1.tail, l2.tail, h1)
        else
          permutation_delete_cons(l1.tail, l2)
      }
    }
  } holds

  def permutation_concat_comm[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    permutation(l1 ++ l2, l2 ++ l1) because {
      if (l1 == Nil[V]())
        permutation_refl(l2)
      else {
        val h1 = l1.head
        (l2 ++ l1 contains h1) &&
          // permutation (l1.tail ++ l2, l2 ++ l1.tail)
          permutation_concat_comm(l1.tail, l2) &&
          (l1 ++ l2).tail == l1.tail ++ l2 &&
          // permutation (delete (l2 ++ l1, h1), l2 ++ l1.tail)
          permutation_delete_cons(l2, l1) &&
          // permutation (l2 ++ l1.tail, delete (l2 ++ l1, h1))
          permutation_comm(delete(l2 ++ l1, h1), l2 ++ l1.tail) &&
          permutation_tran(l1.tail ++ l2, l2 ++ l1.tail, delete(l2 ++ l1, h1))
      }
    }
  } holds

  def permutation_tail_delete[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    require(l1 != Nil[V]() && permutation(l1, l2))
    permutation(l1.tail, delete(l2, l1.head))
  } holds

  def permutation_delete[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(permutation(l1, l2))
    permutation(delete(l1, e), delete(l2, e)) because {
      if (l1 == Nil[V]())
        trivial
      else {
        val h1 = l1.head
        if (e == h1) {
          // permutation(delete(l1, h1), delete(l2, h1)) because
          permutation_tail_delete(l1, l2)
        } else {
          delete_contains(l2, h1, e) &&
            permutation_delete(l1.tail, delete(l2, h1), e) &&
            delete_comm(l2, e, h1)
        }
      }
    }
  } holds

  def permutation_delete_cons[V] (l1 : List[V], h2 : V, t2 : List[V]) : Boolean = {
    require(permutation(delete(l1, h2), t2) && l1.contains(h2))
    permutation(l1, Cons(h2, t2)) because {
      if (l1 == Nil[V]())
        trivial
      else {
        val h1 = l1.head
        if (h1 == h2)
          trivial
        else {
          (Cons(h2, t2) contains h1) &&
            delete_comm(l1, h1, h2) &&
            permutation_delete_cons(l1.tail, h2, delete(t2, h1))
        }
      }
    }
  } holds

  def permutation_cons_delete[V] (l : List[V], e : V) : Boolean = {
    require(l contains e)
    permutation(Cons(e, delete(l, e)), l) because { permutation_refl(delete(l, e)) }
  } holds

  def permutation_comm[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l2, l1) because {
      if (l1 == Nil[V]())
        trivial
      else {
        permutation_content(l1, l2) &&
          l1.contains(l2.head) &&
          permutation_comm(l1.tail, delete(l2, l1.head)) &&
          permutation_delete_cons(l2, l1.head, l1.tail) &&
          permutation_delete(l2, l1, l2.head)
      }
    }
  } holds

  def permutation_tran[V] (l1 : List[V], l2 : List[V], l3 : List[V]) : Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    permutation(l1, l3) because {
      if (l1 == Nil[V]())
        trivial
      else {
        val h1 = l1.head
        // permutation (delete (l2, h1), delete (l3, h1))
        permutation_delete(l2, l3, h1) &&
          // permutation (l1.tail, delete (l3, h1))
          permutation_tran(l1.tail, delete(l2, h1), delete(l3, h1))
      }
    }
  } holds

  def permutation_tran_lemma2[V] (l1 : List[V], l2 : List[V], l3 : List[V], l4 : List[V]) : Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3) && permutation(l3, l4))
    permutation(l1, l4) because
      permutation_tran(l1, l2, l3) &&
        permutation_tran(l1, l3, l4)
  } holds

  def permutation_cons[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(permutation(l1, l2))
    permutation(e :: l1, e :: l2)
  } holds

  def permutation_content[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    require(permutation(l1, l2))
    l1.content == l2.content because {
      if (l1 == Nil[V]())
        trivial
      else {
        val h1 = l1.head
        l1.content == l1.tail.content ++ Set(h1) &&
          l2.content == delete(l2, h1).content ++ Set(h1) &&
          delete_content(l2, h1) &&
          permutation_content(l1.tail, delete(l2, h1))
      }
    }
  } holds

  def permutation_concat[V] (l1 : List[V], l2 : List[V], t1 : List[V], t2 : List[V]) : Boolean = {
    require(permutation(l1, t1) && permutation(l2, t2))
    permutation(l1 ++ l2, t1 ++ t2) because {
      if (l1 == Nil[V]())
        trivial
      else {
        val h1 = l1.head
        // permutation(l1.tail, delete(t1, h1)) because
        permutation_tail_delete(l1, t1) &&
          // permutation(l1, h1 :: delete(t1, h1)) because
          permutation_cons(l1.tail, delete(t1, h1), h1) &&
          // permutation(l1.tail ++ l2, delete(t1, h1) ++ t2) because
          permutation_concat(l1.tail, l2, delete(t1, h1), t2) &&
          // permutation(l1 ++ l2, h1 :: delete(t1, h1) ++ t2) because
          permutation_cons(l1.tail ++ l2, delete(t1, h1) ++ t2, h1) &&
          // permutation(l1 ++ t2, h1 :: delete(t1, h1) ++ t2) because
          permutation_append(l1, h1 :: delete(t1, h1), t2) &&
          permutation_tran(l1 ++ l2, h1 :: delete(t1, h1) ++ t2, l1 ++ t2) &&
          permutation_append(l1, t1, t2) &&
          permutation_tran(l1 ++ l2, l1 ++ t2, t1 ++ t2)
      }
    }
  } holds

  def concat_permutation[V] (ll : List[V], l1 : List[V], l2 : List[V]) : Boolean = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because {
      // permutation (l1 ++ ll, l2 ++ ll)
      permutation_append(l1, l2, ll) &&
        // permutation (ll ++ l1, l1 ++ ll)
        permutation_concat_comm(ll, l1) &&
        // permutation (l2 ++ ll, ll ++ l2)
        permutation_concat_comm(l2, ll) &&
        permutation_tran(ll ++ l1, l1 ++ ll, l2 ++ ll) &&
        permutation_tran(ll ++ l1, l2 ++ ll, ll ++ l2)
    }
  } holds

  @induct
  def delete_permutation[V] (list : List[V], e : V) : Boolean = {
    require(list contains e)
    permutation(list, Cons(e, delete(list, e))) because {
      val h = list.head
      if (h == e) {
        permutation_refl(list)
      } else {
        // permutation(list, Cons(e, delete(list, e))) because
        delete(list, e) == Cons(h, delete(list.tail, e))
      }
    }
  } holds

  def permutation_concat_assoc[V] (l1 : List[V], l2 : List[V], l3 : List[V]) : Boolean = {
    permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because {
      if (l1 == Nil[V]()) {
        permutation_refl(l2 ++ l3)
      } else {
        permutation_concat_assoc(l1.tail, l2, l3) &&
          permutation_cons(l1.tail ++ l2 ++ l3, l1.tail ++ (l2 ++ l3), l1.head)
      }
    }
  } holds

  @induct
  def cons_snoc_perm[V] (l : List[V], e : V) : Boolean = {
    permutation(e :: l, l :+ e)
  } holds

  def rotate_perm[V] (l : List[V], n : BigInt) : Boolean = {
    require(!l.isEmpty)
    permutation(l.rotate(n), l) because {
      cut_as_take_drop(l, n mod l.size) &&
        permutation_concat_comm(l.take(n mod l.size), l.drop(n mod l.size))
    }
  } holds

  def permutation_replace[V] (x : List[V], y : List[V], a : List[V], b : List[V]) : Boolean = {
    require(permutation(x, y))
    ((permutation(x, a) && permutation(y, b)) ==> (permutation(a, b) because {
      permutation_comm(x, a) && permutation_tran(a, x, y) && permutation_tran(a, y, b)
    })) &&
      ((permutation(a, x) && permutation(y, b)) ==> (permutation(a, b) because {
        permutation_tran(a, x, y) && permutation_tran(a, y, b)
      })) &&
      ((permutation(x, a) && permutation(b, y)) ==> (permutation(a, b) because {
        permutation_comm(x, a) && permutation_tran(a, x, y) && permutation_comm(b, y) && permutation_tran(a, y, b)
      })) &&
      ((permutation(a, x) && permutation(b, y)) ==> (permutation(a, b) because {
        permutation_tran(a, x, y) && permutation_comm(b, y) && permutation_tran(a, y, b)
      })) &&
      ((permutation(y, a) && permutation(x, b)) ==> (permutation(a, b) because {
        permutation_comm(x, y) && permutation_comm(y, a) && permutation_tran(a, y, x) && permutation_tran(a, x, b)
      })) &&
      ((permutation(a, y) && permutation(x, b)) ==> (permutation(a, b) because {
        permutation_comm(x, y) && permutation_tran(a, y, x) && permutation_tran(a, x, b)
      })) &&
      ((permutation(y, a) && permutation(b, x)) ==> (permutation(a, b) because {
        permutation_comm(x, y) && permutation_comm(y, a) && permutation_tran(a, y, x) && permutation_comm(b, x) && permutation_tran(a, x, b)
      })) &&
      ((permutation(a, y) && permutation(b, x)) ==> (permutation(a, b) because {
        permutation_comm(x, y) && permutation_tran(a, y, x) && permutation_comm(b, x) && permutation_tran(a, x, b)
      }))
  } holds

  /* Used to prove permutation3 */
  def permutation3_swap2[V] (x : List[V], y : List[V], z : List[V]) : Boolean = {
    permutation(x ++ y ++ z, x ++ z ++ y) because {
      permutation_concat_assoc(x, y, z) &&
        permutation_concat_comm(y, z) && permutation_prepend(x, y ++ z, z ++ y) &&
        permutation_tran(x ++ y ++ z, x ++ (y ++ z), x ++ (z ++ y)) &&
        permutation_concat_assoc(x, z, y) && permutation_comm(x ++ z ++ y, x ++ (z ++ y)) &&
        permutation_tran(x ++ y ++ z, x ++ (z ++ y), x ++ z ++ y)
    } && permutation(x ++ y ++ z, y ++ x ++ z) because {
      permutation_concat_comm(x, y) && permutation_append(x ++ y, y ++ x, z)
    } && permutation(x ++ y ++ z, z ++ y ++ x) because {
      permutation_concat_comm(x, y) && permutation_append(x ++ y, y ++ x, z) &&
        permutation_concat_comm(y ++ x, z) &&
        permutation_concat_assoc(z, y, x) &&
        permutation_comm(z ++ y ++ x, z ++ (y ++ x)) &&
        permutation_tran(x ++ y ++ z, y ++ x ++ z, z ++ (y ++ x)) &&
        permutation_tran(x ++ y ++ z, z ++ (y ++ x), z ++ y ++ x)
    }
  } holds

  /* Used to prove permutation3 */
  def permutation3_swap_noassoc[V] (x : List[V], y : List[V], z : List[V]) : Boolean = {
    permutation(x ++ y ++ z, x ++ y ++ z) because { permutation_refl(x ++ y ++ z) } &&
      permutation(x ++ y ++ z, x ++ z ++ y) because { permutation3_swap2(x, y, z) } &&
      permutation(x ++ y ++ z, y ++ x ++ z) because { permutation3_swap2(x, y, z) } &&
      permutation(x ++ y ++ z, y ++ z ++ x) because { permutation3_swap2(x, y, z) && permutation3_swap2(y, x, z) && permutation_tran(x ++ y ++ z, y ++ x ++ z, y ++ z ++ x) } &&
      permutation(x ++ y ++ z, z ++ x ++ y) because { permutation3_swap2(x, y, z) && permutation3_swap2(x, z, y) && permutation_tran(x ++ y ++ z, x ++ z ++ y, z ++ x ++ y) } &&
      permutation(x ++ y ++ z, z ++ y ++ x) because { permutation3_swap2(x, y, z) }
  } holds

  def permutation3[V] (x : List[V], y : List[V], z : List[V]) : Boolean = {
    permutation(x ++ y ++ z, x ++ y ++ z) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, x ++ z ++ y) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, y ++ x ++ z) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, y ++ z ++ x) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, z ++ x ++ y) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, z ++ y ++ x) because { permutation3_swap_noassoc(x, y, z) } &&
      permutation(x ++ y ++ z, x ++ (y ++ z)) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(x, y, z) && permutation_tran(x ++ y ++ z, x ++ y ++ z, x ++ (y ++ z))
    } &&
      permutation(x ++ y ++ z, x ++ z ++ y) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(x, y, z) && permutation_tran(x ++ y ++ z, x ++ y ++ z, x ++ (y ++ z))
    } &&
      permutation(x ++ y ++ z, y ++ x ++ z) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(y, x, z) && permutation_tran(x ++ y ++ z, y ++ x ++ z, y ++ (x ++ z))
    } &&
      permutation(x ++ y ++ z, y ++ z ++ x) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(y, z, x) && permutation_tran(x ++ y ++ z, y ++ z ++ x, y ++ (z ++ x))
    } &&
      permutation(x ++ y ++ z, z ++ x ++ y) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(z, x, y) && permutation_tran(x ++ y ++ z, z ++ x ++ y, z ++ (x ++ y))
    } &&
      permutation(x ++ y ++ z, z ++ y ++ x) because {
      permutation3_swap_noassoc(x, y, z) && permutation_concat_assoc(z, y, x) && permutation_tran(x ++ y ++ z, z ++ y ++ x, z ++ (y ++ x))
    }
  } holds

  def append5_swap2_perm[T] (a : List[T], b : List[T], c : List[T], d : List[T], e : List[T]) : Boolean = {
    permutation(a ++ b ++ c ++ d ++ e, a ++ d ++ c ++ b ++ e) because {
      permutation_concat_comm(b, d) &&
        permutation_append(b ++ d, d ++ b, c) &&
        permutation3(b, c, d) && permutation_tran(b ++ c ++ d, b ++ d ++ c, d ++ b ++ c) &&
        permutation3(d, b, c) && permutation_tran(b ++ c ++ d, d ++ b ++ c, d ++ c ++ b) &&
        permutation_prepend(a, b ++ c ++ d, d ++ c ++ b) &&
        permutation_concat_assoc(a, b ++ c, d) && permutation_concat_assoc(a, d ++ c, b) &&
        permutation_replace(a ++ (b ++ c ++ d), a ++ (d ++ c ++ b), a ++ (b ++ c) ++ d, a ++ (d ++ c) ++ b) &&
        permutation_concat_assoc(a, b, c) && permutation_comm(a ++ b ++ c, a ++ (b ++ c)) && permutation_append(a ++ (b ++ c), a ++ b ++ c, d) &&
        permutation_concat_assoc(a, d, c) && permutation_comm(a ++ d ++ c, a ++ (d ++ c)) && permutation_append(a ++ (d ++ c), a ++ d ++ c, b) &&
        permutation_replace(a ++ (b ++ c) ++ d, a ++ (d ++ c) ++ b, a ++ b ++ c ++ d, a ++ d ++ c ++ b) &&
        permutation_append(a ++ b ++ c ++ d, a ++ d ++ c ++ b, e)
    }
  } holds

  def cons_concat_perm1[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    permutation(e :: (l1 ++ l2), (e :: l1) ++ l2) because { permutation_refl(e :: (l1 ++ l2)) }
  } holds

  def cons_concat_perm2[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    permutation(e :: (l1 ++ l2), l1 ++ (e :: l2)) because {
      permutation_cons_tail(l1, l2, e) && permutation_comm(l1 ++ (e :: l2), e :: (l1 ++ l2))
    }
  } holds

  def delete_concat_perm1[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(l1.contains(e))
    permutation(delete(l1 ++ l2, e), delete(l1, e) ++ l2) because {
      delete_concat(l1, l2, e) && permutation_eq(delete(l1 ++ l2, e), delete(l1, e) ++ l2)
    }
  } holds

  def delete_concat_perm2[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(l2.contains(e))
    permutation(delete(l1 ++ l2, e), l1 ++ delete(l2, e)) because {
      l1 match {
        case Nil()                   => permutation_refl(delete(l2, e))
        case Cons(hd, tl) if hd == e => delete_concat_perm2(tl, l2, e)
        case Cons(hd, tl)            => delete_concat_perm2(tl, l2, e)
      }
    }
  } holds

  def permutation_concat_move[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(l2.contains(e))
    permutation((e :: l1) ++ delete(l2, e), l1 ++ l2) because {
      delete_concat_perm2(e :: l1, l2, e) &&
        permutation_comm(delete((e :: l1) ++ l2, e), (e :: l1) ++ delete(l2, e))
    }
  } holds

}
