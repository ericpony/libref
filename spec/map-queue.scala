package libref.spec

import libref.collection._
import libref.collection.PairList._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

/**
  * FIFO Map
  * A key-value-queue map. Each key corresponds to a queue of values.
  * Upon each insertion, the value is append to the queue associated with the given key.
  */
object FIFOMapSpec {

  @induct
  def insert_commu_lemma[K, V] (map : PList[K, V], p1 : Pair[K, V], p2 : Pair[K, V], key : K) = {
    require(p1.key != p2.key)
    (p2 :: p1 :: map).getAll(key) == (p1 :: p2 :: map).getAll(key)
  } holds /* verified by Leon */

  def merge_commu_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    require(!map1.hasKey(key) || !map2.hasKey(key))
    (map1 ++ map2).getAll(key) == (map2 ++ map1).getAll(key)
  } holds /* verified by Leon */

  @induct
  def merge_assoc_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], map3 : PList[K, V], key : K) = {
    require((map1.keys & map2.keys) == Nil[K]() &&
      (map2.keys & map3.keys) == Nil[K]() &&
      (map3.keys & map1.keys) == Nil[K]())
    (map1 ++ (map2 ++ map3)).getAll(key) == ((map1 ++ map2) ++ map3).getAll(key)
  } holds /* verified by Leon */
}

@library
object FIFOMapLemmas {
  @induct
  def get_swap_lemma[K, V] (map : PList[K, V], p1 : Pair[K, V], p2 : Pair[K, V], key : K) = {
    require(p1.key != p2.key)
    (p2 :: p1 :: map).get(key) == (p1 :: p2 :: map).get(key)
  } holds /* verified by Leon */

  @induct
  def getAll_delete_lemma[K, V] (map : PList[K, V], e : Pair[K, V], key : K) : Boolean = {
    require(map.contains(e) && e.key == key)
    map.delete(e).getAll(key) == map.getAll(key).delete(e)
  } holds

  @induct
  def get_commu_lemma[K, V] (map1 : PList[K, V], map2 : PList[K, V], key : K) : Boolean = {
    require(!map1.hasKey(key))
    (map2 ++ map1).get(key) == (map1 ++ map2).get(key) because {
      if (map2 == PNil[K, V]()) trivial
      else {
        val PCons(h, t) = map2
        if (h.key == key) trivial
        else
          (map2 ++ map1).get(key) == (t ++ map1).get(key) &&
            (map1 ++ map2).get(key) == (t ++ map1).get(key) because
            get_commu_lemma(map1, map2.deleteFirst(h), key)
      }
    }
  } holds
}
