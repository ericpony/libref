package libref.spec

import libref.collection._
import leon.lang._
import scala.language.postfixOps
import scala.language.implicitConversions

/**
  * This is the AVL Tree implementation formerly used by Scala's mutable TreeSet.
  * AVLTree and its related classes have been deleted from the Scala standard
  * library since version 2.11, because they are not different enough from
  * RedBlackTree to justify keeping them.
  *
  * Source:
  * https://github.com/scala/scala/blob/2.11.x/src/library/scala/collection/mutable/AVLTree.scala
  */
object AVLTree {

  sealed abstract class TreeNode {
    def balance : BigInt

    def depth : BigInt
  }

  case object Leaf extends TreeNode {
    val balance : BigInt = 0

    val depth : BigInt = -1
  }

  case class Node (value : BigInt, left : TreeNode, right : TreeNode) extends TreeNode {
    val balance : BigInt = right.depth - left.depth

    val depth : BigInt = (if (left.depth > right.depth) left.depth else right.depth) + 1

  }

  implicit def NodeToAVLTree (node : TreeNode) : AVLTreeOps = AVLTreeOps(node)

  sealed case class AVLTreeOps (tree : TreeNode) {

    def contains (value : BigInt) : Boolean = tree match {
      case Leaf => false
      case Node(data, left, right) =>
        if (value == data) true
        else if (value < data) left.contains(value)
        else right.contains(value)
    }

    /**
      * Returns a new tree containing the given element.
      * Ignore the new element if the same element is already present.
      */
    def insert (v : BigInt) : TreeNode = tree match {
      case Leaf => tree
      case Node(value, left, right) =>
        if (v == value)
          tree
        else if (v < value)
          Node(value, left.insert(v), right).rebalance
        else
          Node(value, left, right.insert(v)).rebalance
    }

    /**
      * Return a new tree which not contains given element.
      */
    def delete (v : BigInt) : TreeNode = tree match {
      case Leaf => tree
      case Node(value, left, right) =>
        if (v == value) {
          if (left == Leaf) {
            if (right == Leaf) {
              Leaf
            } else {
              val (min, newRight) = right.deleteMin
              Node(min, left, newRight).rebalance
            }
          } else {
            val (max, newLeft) = left.deleteMax
            Node(max, newLeft, right).rebalance
          }
        } else if (v < value) {
          Node(value, left.delete(v), right).rebalance
        } else {
          Node(value, left, right.delete(v)).rebalance
        }
    }

    def findMin : Option[BigInt] = tree match {
      case Leaf => None[BigInt]()
      case Node(value, Leaf, _) => Some(value)
      case Node(_, left, _) => left.findMin
    }

    def findMax : Option[BigInt] = tree match {
      case Leaf => None[BigInt]()
      case Node(value, _, Leaf) => Some(value)
      case Node(_, _, right) => right.findMin
    }

    /**
      * Return a tuple containing the smallest element of the provided tree
      * and a new tree from which this element has been extracted.
      */
    def deleteMin : (BigInt, TreeNode) = {
      require(tree != Leaf)
      val Node(data, left, right) = tree
      if (left == Leaf)
        (data, right)
      else {
        val (min, newLeft) = left.deleteMin
        (min, Node(data, newLeft, right).rebalance)
      }
    }

    /**
      * Return a tuple containing the biggest element of the provided tree
      * and a new tree from which this element has been extracted.
      */
    def deleteMax : (BigInt, TreeNode) = {
      require(tree != Leaf)
      val Node(value, left, right) = tree
      if (right == Leaf)
        (value, left)
      else {
        val (max, newRight) = right.deleteMax
        (max, Node(value, left, newRight).rebalance)
      }
    }

    def rebalance : TreeNode = tree match {
      case Leaf => Leaf
      case Node(value, left, right) =>
        if (tree.balance == BigInt(-2)) {
          if (left.balance == BigInt(1))
            tree.doubleRightRotation
          else
            tree.rightRotation
        } else if (tree.balance == BigInt(2)) {
          if (right.balance == BigInt(-1))
            tree.doubleLeftRotation
          else
            tree.leftRotation
        } else tree
    }

    def leftRotation : TreeNode = tree match {
      case Leaf => Leaf
      case Node(value, left, right) =>
        right match {
          case Leaf => tree // should not happen
          case r@Node(_, _, _) => Node(r.value, Node(value, left, r.left), r.right)
        }
    }

    def rightRotation : TreeNode = tree match {
      case Leaf => Leaf
      case Node(value, left, right) =>
        left match {
          case Leaf => tree // should not happen
          case l@Node(_, _, _) => Node(l.value, l.left, Node(value, l.right, right))
        }
    }

    def doubleLeftRotation : TreeNode = tree match {
      case Leaf => Leaf
      case Node(v, l, r) =>
        r match {
          case Leaf => tree // should not happen
          case r@Node(_, _, _) =>
            val Node(rv, rl, rr) = r.rightRotation
            Node(rv, Node(v, l, rl), rr)
        }
    }

    def doubleRightRotation : TreeNode = tree match {
      case Leaf => Leaf
      case Node(v, l, r) =>
        l match {
          case Leaf => tree // should not happen
          case l@Node(_, _, _) =>
            val Node(lv, ll, lr) = l.leftRotation
            Node(lv, ll, Node(v, lr, r))
        }
    }

    def toList : List[BigInt] = tree match {
      case Leaf => Nil[BigInt]()
      case Node(v, l, r) => v :: (l.toList ++ r.toList)
    }

    def toSortedList : List[BigInt] = tree match {
      case Leaf => Nil[BigInt]()
      case Node(v, l, r) => l.toList ++ (v :: r.toList)
    }

    def toSet : Set[BigInt] = toList.content
  }

}
