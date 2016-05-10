package libref.proof

import scala.language.implicitConversions

package object sugar {

  case class LogicalOps (a: Boolean) {
    def and (b: => Boolean) = a && b

    def or (b: => Boolean) = a || b

    def implies (b: => Boolean) = !a || b

    def onlyif (b: => Boolean) = !b || a

    def iff (b: => Boolean) = a == b

    def ==> (b: => Boolean) = !a || b

    def <== (b: => Boolean) = !b || a

    def <==> (b: => Boolean) = a == b
  }

  implicit def extendedBoolean (a: Boolean) = LogicalOps(a)
}
