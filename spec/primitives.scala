package libref.spec

import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._
import scala.language.postfixOps

object PrimitiveDataTypeSpec {

  /**
   * Check that set union operations are commutative and associative.
   */
  def set_union_lemma[B] (a1: Set[B], a2: Set[B], a3: Set[B]): Boolean = {
    def op (a: Set[B], b: Set[B]) = a ++ b
    op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3)
  } holds /* verified by Leon */

  /**
   * Check that choosing maximum is commutative and associative.
   */
  def integer_max_lemma (a1: BigInt, a2: BigInt, a3: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = if (a > b) a else b
    op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3)
  } holds /* verified by Leon */

  /**
   * Check that mathematical integer additions are commutative and associative.
   */
  def integer_add_lemma (a1: BigInt, a2: BigInt, a3: BigInt): Boolean = {
    def op (a: BigInt, b: BigInt) = a + b
    op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3)
  } holds /* verified by Leon */

  /**
   * Check that 32-bit integer additions are commutative and associative.
   * (Note that Leon handles overflow by wrapping, e.g., 2^32 == -2^31.)
   */
  def int32_add_lemma (a1: Int, a2: Int, a3: Int): Boolean = {
    def op (a: Int, b: Int) = a + b
    op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3)
  } holds /* verified by Leon */

  /**
   * Check that 64-bit floating-point additions are commutative and associative.
   */
  @ignore
  def double_add_lemma (a1: Double, a2: Double, a3: Double): Boolean = {
    def op (a: Double, b: Double) = a + b
    op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3)
  } holds /* failed due to unsupported type Double */

  /**
   * Check that point-wise additions of mathematical integer vectors are commutative and associative.
   */
  def int_vector_add_lemma (a1: List[BigInt], a2: List[BigInt], a3: List[BigInt]): Boolean = {
    require(a1.size == a2.size && a2.size == a3.size)
    if (a1.size == 0) trivial
    else {
      def op (a: List[BigInt], b: List[BigInt]) = a.zip(b).map(t => t._1 + t._2)
      op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3) because {
        a1 match {
          case Nil() => trivial
          case _     => integer_add_lemma(a1.head, a2.head, a3.head) &&
            int_vector_add_lemma(a1.tail, a2.tail, a3.tail)
        }
      }
    }
  } holds /* verified by Leon */

  /**
   * Check that point-wise additions of Int32 vectors are commutative and associative.
   * Note: Leon may take up to 30 seconds to verify this lemma on my desktop.
   */
  def int32_vector_add_lemma (a1: List[Int], a2: List[Int], a3: List[Int]): Boolean = {
    require(a1.size == a2.size && a2.size == a3.size)
    def op (a: List[Int], b: List[Int]): List[Int] = {
      a.zip(b).map((t: (Int, Int)) => t._1 + t._2)
    } ensuring { res =>
      res.size == 0 ||
        (a.head + b.head) :: op(a.tail, b.tail) == op(a, b)
    }
    if (a1 != Nil[Int]()) {
      op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3) because {
        op(a1, a2).head == op(a2, a1).head &&
          op(a1, op(a2, a3)).head == op(op(a1, a2), a3).head && {
          op(a1, a2).tail == op(a2.tail, a1.tail) &&
            op(a1, op(a2, a3)).tail == op(a1.tail, op(a2.tail, a3.tail)) &&
            op(op(a1, a2), a3).tail == op(op(a1.tail, a2.tail), a3.tail) because
            int32_vector_add_lemma(a1.tail, a2.tail, a3.tail)
        }
      }
    } else trivial
  } holds /* verified by Leon */

  /**
   * Check that point-wise unions of set vectors are commutative and associative.
   */
  @ignore
  def set_vector_add_lemma[B] (a1: List[Set[B]], a2: List[Set[B]], a3: List[Set[B]]): Boolean = {
    require(a1.size == a2.size && a2.size == a3.size)
    if (a1.size == 0) trivial
    else {
      def op (a: List[Set[B]], b: List[Set[B]]) = a.zip(b).map(t => t._1 ++ t._2)
      op(a1, a2) == op(a2, a1) && op(a1, op(a2, a3)) == op(op(a1, a2), a3) because {
        a1 match {
          case Nil() => trivial
          case _     => set_union_lemma(a1.head, a2.head, a3.head) &&
            set_vector_add_lemma(a1.tail, a2.tail, a3.tail)
        }
      }
    }
  } holds /* failed due to Z3 runtime exception */
}

