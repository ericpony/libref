package libref.spec

import libref.collection._
import leon.lang._
import scala.language.postfixOps
import scala.language.implicitConversions

abstract class HeapADT {

  def findMin: Option[BigInt]

  def deleteMin: HeapADT

  def insert (e: BigInt): HeapADT

  def toSortedList: List[BigInt]

  def content: Set[BigInt]

  def isHeap: Boolean

  def size: BigInt
}
