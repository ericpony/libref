package libref.proof

import libref.collection._
import libref.proof.MinOps._
import libref.proof.SortedListOps._
import leon.lang._


import scala.language.postfixOps
import scala.language.implicitConversions

object SetLemmas {
  //  implicit def setAsList[A] (set: Set[A]): List[A] = choose {
  //    (x: List[A]) => set == x.content
  //  }

  def set_min (set1 : Set[BigInt], set2 : Set[BigInt]) : Boolean = {
    require(set1 == set2 && !set1.isEmpty)
    min(set1.toList) == min(set2.toList)
  } holds

  def set_forall[A] (set1 : Set[A], set2 : Set[A], p : A => Boolean) : Boolean = {
    require(set1 == set2)
    set1.forall(p) == set2.forall(p)
  } holds


  def set_exists[A] (set1 : Set[A], set2 : Set[A], p : A => Boolean) : Boolean = {
    require(set1 == set2)
    set1.exists(p) == set2.exists(p)
  } holds

  def set_filter[A] (set1 : Set[A], set2 : Set[A], p : A => Boolean) : Boolean = {
    require(set1 == set2 && !set1.isEmpty)
    set1.filter(p) == set2.filter(p)
  } holds

  def set_sort (set1 : Set[BigInt], set2 : Set[BigInt]) : Boolean = {
    require(set1 == set2 && set1.size == set2.size)
    sort(set1.toList) == sort(set2.toList)
  } holds
}

