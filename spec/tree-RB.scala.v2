import leon.lang._
import leon.annotation._

/**
 * Okasaki's red-black tree with deletion
 *
 * Algorithm: http://matt.might.net/articles/red-black-delete/
 * Source:    http://goo.gl/GV6vsl
 */
object RedBlackTree {

  sealed abstract class Color

  case object Red extends Color

  case object Black extends Color

  case object DoubleBlack extends Color

  case object NegativeBlack extends Color

  sealed abstract class Tree

  case object Empty extends Tree

  case object DoubleBlackEmpty extends Tree

  case class Node (color: Color, left: Tree, value: BigInt, right: Tree) extends Tree

  def delete (node: Tree, key: BigInt): Tree = {
    require(redNodesHaveBlackChildren(node) && hasRedBlackNodes(node))
    node match {
      case Node(c, l, k, r) =>
        if (key < k) bubble(c, delete(l, key), k, r)
        else if (key == k) remove(node)
        else bubble(c, l, k, delete(r, key))
      case _                => node
    }
  } ensuring (res => redNodesHaveBlackChildren(res) && hasRedBlackNodes(res))

  def findMax (t: Tree): BigInt = {
    require(isNode(t))
    t match {
      case Node(c, l, k, r@Node(cr, lr, kr, rr)) => findMax(r)
      case Node(c, l, k, r)                      => k
      // case _ => throw new Exception("Searching for findMax in a leaf")
    }
  }

  def content (t: Tree): Set[BigInt] = t match {
    case Empty            => Set.empty
    case DoubleBlackEmpty => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size (t: Tree): BigInt = t match {
    case Empty            => 0
    case DoubleBlackEmpty => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  @induct
  def deleteMax (node: Tree): Tree = {
    require(isNode(node) && redNodesHaveBlackChildren(node) && hasRedBlackNodes(node))
    node match {
      case Node(_, l, _, Empty) => remove(node)
      case Node(c, l, k, r)     => bubble(c, l, k, deleteMax(r))
      // case _ => throw new Exception("Removing findMax from a leaf")
    }
  } ensuring (res => redNodesHaveBlackChildren(res))

  def hasRedBlackNodes (t: Tree): Boolean = t match {
    case Empty                => true
    case Node(Black, l, _, r) => hasRedBlackNodes(l) && hasRedBlackNodes(r)
    case Node(Red, l, _, r)   => hasRedBlackNodes(l) && hasRedBlackNodes(r)
    case _                    => false
  }

  def hasRedBlackDesc (t: Tree): Boolean = t match {
    case Node(_, l, _, r) => hasRedBlackNodes(l) && hasRedBlackNodes(r)
    case Empty            => true
    case DoubleBlackEmpty => true
  }

  /* We consider leaves to be black by definition */
  def isBlack (t: Tree): Boolean = t match {
    case Empty                => true
    case Node(Black, _, _, _) => true
    case _                    => false
  }

  def isNode (t: Tree): Boolean = t match {
    case Node(_, _, _, _) => true
    case _                => false
  }

  def redNodesHaveBlackChildren (t: Tree): Boolean = {
    require(hasRedBlackNodes(t))
    t match {
      case Empty                => true
      case Node(Black, l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
      case Node(Red, l, _, r)   => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    }
  }

  def redDescHaveBlackChildren (t: Tree): Boolean = {
    require(hasRedBlackNodes(t))
    t match {
      case Empty            => true
      case Node(_, l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    }
  }

  def ins (x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && hasRedBlackNodes(t))
    t match {
      case Empty            => Node(Red, Empty, x, Empty)
      case Node(c, a, y, b) =>
        if (x < y) balance(c, ins(x, a), y, b)
        else if (x == y) Node(c, a, y, b)
        else balance(c, a, y, ins(x, b))
    }
  } ensuring (res => content(res) == content(t) ++ Set(x)
    && size(t) <= size(res) && size(res) <= size(t) + 1
    && redDescHaveBlackChildren(res)
    && hasRedBlackNodes(res)
    )

  def makeBlack (n: Tree): Tree = {
    require(redDescHaveBlackChildren(n) && hasRedBlackNodes(n))
    n match {
      case Node(Red, l, v, r) => Node(Black, l, v, r)
      case _                  => n
    }
  } ensuring (res => redNodesHaveBlackChildren(res) && hasRedBlackNodes(res))

  def makeRed (n: Tree): Tree = {
    n match {
      case Node(_, l, v, r) => Node(Red, l, v, r)
      case _                => n
    }
  }

  def add (x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && hasRedBlackNodes(t))
    makeBlack(ins(x, t))
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && hasRedBlackNodes(res))

  def balance (c: Color, a: Tree, x: BigInt, b: Tree): Tree = {
    // require(
    //   Node(c,a,x,b) match {
    //     case Node(Black(),Node(Red(),Node(Red(),a,_,b),_,c),_,d) =>
    //       redNodesHaveBlackChildren(a) &&
    //       redNodesHaveBlackChildren(b) &&
    //       redNodesHaveBlackChildren(c) &&
    //       redNodesHaveBlackChildren(d)
    //     case Node(Black(),Node(Red(),a,_,Node(Red(),b,_,c)),_,d) =>
    //       redNodesHaveBlackChildren(a) &&
    //       redNodesHaveBlackChildren(b) &&
    //       redNodesHaveBlackChildren(c) &&
    //       redNodesHaveBlackChildren(d)
    //     case Node(Black(),a,_,Node(Red(),Node(Red(),b,_,c),_,d)) =>
    //       redNodesHaveBlackChildren(a) &&
    //       redNodesHaveBlackChildren(b) &&
    //       redNodesHaveBlackChildren(c) &&
    //       redNodesHaveBlackChildren(d)
    //     case Node(Black(),a,_,Node(Red(),b,_,Node(Red(),c,_,d))) =>
    //       redNodesHaveBlackChildren(a) &&
    //       redNodesHaveBlackChildren(b) &&
    //       redNodesHaveBlackChildren(c) &&
    //       redNodesHaveBlackChildren(d)
    //     case t => redDescHaveBlackChildren(t)
    //   }
    // )
    Node(c, a, x, b) match {
      case Node(Black, Node(Red, Node(Red, a, xV, b), yV, c), zV, d) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, Node(Red, a, xV, Node(Red, b, yV, c)), zV, d) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, a, xV, Node(Red, Node(Red, b, yV, c), zV, d)) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, a, xV, Node(Red, b, yV, Node(Red, c, zV, d))) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))

      case Node(DoubleBlack, Node(Red, Node(Red, a, xV, b), yV, c), zV, d) =>
        Node(Black, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(DoubleBlack, Node(Red, a, xV, Node(Red, b, yV, c)), zV, d) =>
        Node(Black, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(DoubleBlack, a, xV, Node(Red, Node(Red, b, yV, c), zV, d)) =>
        Node(Black, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(DoubleBlack, a, xV, Node(Red, b, yV, Node(Red, c, zV, d))) =>
        Node(Black, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))

      case Node(DoubleBlack, a, xV, Node(NegativeBlack, Node(Black, b, yV, c), zV, d)) =>
        Node(Black, Node(Black, a, xV, b), yV, balance(Black, c, zV, makeRed(d)))
      case Node(DoubleBlack, Node(NegativeBlack, a, xV, Node(Black, b, yV, c)), zV, d) =>
        Node(Black, balance(Black, makeRed(a), xV, b), yV, Node(Black, c, zV, d))

      case Node(c, a, xV, b) => Node(c, a, xV, b)
    }
  } ensuring (res => content(res) == content(Node(c, a, x, b)) /*&& redDescHaveBlackChildren(res)*/)

  def balance1 (c: Color, a: Tree, x: BigInt, b: Tree): Tree = {
    Node(c, a, x, b) match {
      case Node(Black, Node(Red, Node(Red, a, xV, b), yV, c), zV, d) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, Node(Red, a, xV, Node(Red, b, yV, c)), zV, d) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, a, xV, Node(Red, Node(Red, b, yV, c), zV, d)) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(Black, a, xV, Node(Red, b, yV, Node(Red, c, zV, d))) =>
        Node(Red, Node(Black, a, xV, b), yV, Node(Black, c, zV, d))
      case Node(c, a, xV, b)                                         =>
        Node(c, a, xV, b)
    }
  } ensuring (res => content(res) == content(Node(c, a, x, b)))

  /* Deletion */
  def incColor (c: Color): Color = {
    require(c != DoubleBlack)
    c match {
      case Black         => DoubleBlack
      case Red           => Black
      case NegativeBlack => Red
      // case DoubleBlack => throw new Exception("Incrementing double black color")
    }
  } ensuring (_ != NegativeBlack)

  def incColor (t: Tree): Tree = {
    require(!isDoubleBlack(t))
    t match {
      case Node(c, l, k, r) => Node(incColor(c), l, k, r)
      case Empty            => DoubleBlackEmpty
      // case _ => throw new Exception("Incrementing double black leaf")
    }
  } ensuring (!isNegativeBlack(_))

  def decColor (c: Color): Color = {
    require(c != NegativeBlack)
    c match {
      case DoubleBlack => Black
      case Black       => Red
      case Red         => NegativeBlack
      // case NegativeBlack => throw new Exception("Decrementing negative black color")
    }
  } ensuring (_ != DoubleBlack)

  def decColor (t: Tree): Tree = {
    require(!isNegativeBlack(t) && t != Empty)
    t match {
      case Node(c, l, k, r) => Node(decColor(c), l, k, r)
      case DoubleBlackEmpty => Empty
      // case _ => throw new Exception("Decrementing black leaf")
    }
  } ensuring (!isDoubleBlack(_))

  def remove (node: Tree): Tree = {
    require(node != Empty && redNodesHaveBlackChildren(node) && hasRedBlackNodes(node))
    node match {
      // Leaves are easy to kill:
      case Node(Red, Empty, k, Empty)   => Empty
      case Node(Black, Empty, k, Empty) => DoubleBlackEmpty

      // Killing a node with one child:
      case Node(Black, Node(Red, l, k, r), _, Empty) => Node(Black, l, k, r)
      case Node(Black, Empty, _, Node(Red, l, k, r)) => Node(Black, l, k, r)

      // Killing a node with two sub-trees:
      case Node(c, l@Node(_, _, _, _), _, r@Node(_, _, _, _)) =>
        val maxV = findMax(l)
        val newL = deleteMax(l)
        bubble(c, newL, maxV, r)
      case _                                                  =>
        error[Tree]("Removing an unexpected tree")
    }
  } ensuring (res => hasRedBlackDesc(res))

  def isDoubleBlack (t: Tree): Boolean = t match {
    case DoubleBlackEmpty           => true
    case Node(DoubleBlack, _, _, _) => true
    case _                          => false
  }

  def isNegativeBlack (t: Tree): Boolean = t match {
    case Node(NegativeBlack, _, _, _) => true
    case _                            => false
  }

  def bubble (c: Color, l: Tree, k: BigInt, r: Tree): Tree = {
    require(l != Empty && r != Empty && !isNegativeBlack(l) && !isNegativeBlack(r))
    if ((c != DoubleBlack) && (isDoubleBlack(l) || isDoubleBlack(r))) {
      balance(incColor(c), decColor(l), k, decColor(r))
    } else {
      Node(c, l, k, r)
    }
  }
}