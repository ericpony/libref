package libref

import leon.lang._
import leon.lang.synthesis.choose
import scala.language.postfixOps
import scala.language.implicitConversions

package object collection {

  //  implicit def setAsList[A] (set: Set[A]): List[A] = choose {
  //    (x: List[A]) => set == x.content
  //  }

  case class SetOps[A] (set: Set[A]) {

    def toList: List[A] = choose {
      (x: List[A]) => set == x.content
    }

    def size = toList.size

    def filter (p: A => Boolean): Set[A] =
      toList.filter(p).content

    def forall (p: A => Boolean): Boolean =
      toList.forall(p)

    def exists (p: A => Boolean): Boolean =
      toList.exists(p)
  }

  implicit def extendedSet[A] (set: Set[A]) = SetOps(set)
}