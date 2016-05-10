package libref.spec

import libref.collection.PairList._
import libref.proof.PairListLemmas._
import leon.annotation._
import leon.lang._
import leon.proof._

import SetMapLemmas._

import scala.language.postfixOps

/**
  * Set Map
  * A key-value-set map. Each key corresponds to a set of values.
  * Upon each insertion, the value is add to the set associated with the given key.
  */
object SetMapSpec {
  @induct
  def insert_commu_lemma[K, V] (map : PList[K, V], p1 : Pair[K, V], p2 : Pair[K, V], key : K) : Boolean = {
    (p2 :: p1 :: map).getAll(key) ~~ (p1 :: p2 :: map).getAll(key)
  } holds /* verified by Leon */

  def merge_commu_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    (map1 ++ map2).getAll(key) ~~ (map2 ++ map1).getAll(key) because
      merge_perm_lemma(map1, map2, key)
  } holds /* verified by Leon */

  @induct
  def merge_assoc_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], map3 : PList[K, V], key : K) : Boolean = {
    (map1 ++ (map2 ++ map3)).getAll(key) ~~ ((map1 ++ map2) ++ map3).getAll(key)
  } holds /* verified by Leon */
}

object SetMapLemmas {
  def merge_perm_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    val l1 = map1 ++ map2
    val l2 = map2 ++ map1
    permutation(l1.getAll(key), l2.getAll(key)) because
      permutation_concat_comm(map1, map2) &&
        permutation_getAll_lemma(l1, l2, key)
  } holds /* verified by Leon */
}
