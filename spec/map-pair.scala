package libref.spec

import libref.collection.PairList._
import libref.collection._
import libref.proof.DistinctOps._
import leon.lang._
import leon.proof._
import leon.annotation._

import scala.language.postfixOps

/**
  * Pair Map
  * A key-value-pair map. Each key corresponds to at most one value in the map.
  * Upon each insertion, the value with the same key, if any, is overwritten
  * by the new value.
  */
object PairMapSpec {

  // def ~[K, V] (m1 : PList[K, V], m2 : PList[K, V]) = permutation(m1, m2)

  @ignore
  def update_invariant[K, V] (m1 : PList[K, V], m2 : PList[K, V], e : Pair[K, V]) : Boolean = {
    require(m1 ~ m2 && libref.proof.DistinctOps.distinct(m1.keys) && libref.proof.DistinctOps.distinct(m2.keys))
    m1.update(e) ~ m2.update(e) because {
      if (!m1.hasKey(e.key) || !m2.hasKey(e.key))
        trivial
      else
        update_invariant(m1.delete(e.key), m2.delete(e.key), e)
    }
  } holds /* verified by Leon */

  def merge_invariant[K, V] (m1 : PList[K, V], m2 : PList[K, V], m3 : PList[K, V], m4 : PList[K, V]) = {
    require(m1 ~ m2 && m3 ~ m4)
    (m1 ++ m3) ~ (m2 ++ m4)
  } holds /* verified by Leon */

  @induct
  def insert_commu_lemma[K, V] (m : PList[K, V], p1 : Pair[K, V], p2 : Pair[K, V]) = {
    require(p1.key != p2.key)
    m.update(p1).update(p2) ~ m.update(p2).update(p1)
  } holds /* verified by Leon */

  def merge_commu_lemma[K, V] (m1 : PList[K, V], m2 : PList[K, V]) = {
    require((m1.keys & m2.keys) == Nil[K]())
    (m2 ++ m1) ~ (m1 ++ m2)
  } holds /* verified by Leon */

  @ignore
  def merge_commu_lemma2[K, V] (m1 : PList[K, V], m2 : PList[K, V]) = {
    require((m1.keys & m2.keys) == Nil[K]() && libref.proof.DistinctOps.distinct(m1.keys) && libref.proof.DistinctOps.distinct(m2.keys))
    merge(m1, m2) ~ merge(m2, m1)
  } holds /* timeout */

  def merge_assoc_lemma[K, V] (m1 : PList[K, V], m2 : PList[K, V], m3 : PList[K, V]) = {
    require((m1.keys & m2.keys) == Nil[K]() &&
      (m2.keys & m3.keys) == Nil[K]() &&
      (m3.keys & m1.keys) == Nil[K]())
    (m1 ++ (m2 ++ m3)) ~ ((m1 ++ m2) ++ m3)
  } holds /* verified by Leon */

  @induct
  def merge[K, V] (m1 : PList[K, V], m2 : PList[K, V]) : PList[K, V] = {
    m1 match {
      case PNil()        => m2
      case PCons(hd, tl) => merge(tl, m2.update(hd))
    }
  }
  //  ensuring {
  //    res => (distinct(m1.keys) &&
  //      distinct(m2.keys) &&
  //      (m1.keys & m2.keys) == Nil[K]()) ==> (res.size == m1.size + m2.size)
  //  }

}

object PairMapLemmas {}
