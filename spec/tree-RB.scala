package libref.spec

import leon.lang._

/**
 * This is a simplified version of the Red-Black Tree implementation used for TreeMaps and TreeSets
 * in the Scala standard library, based on Stefan Kahrs' Haskell version of Okasaki's Red-Black Trees
 *
 * References:
 *
 * @see <a href="https://github.com/scala/scala/blob/2.12.x/src/library/scala/collection/immutable/RedBlackTree.scala">RBTree in the official Scala library</a>
 *
 */
object RedBlackTree {

  sealed abstract class Tree {
    val isRed: Boolean
    val isBlack: Boolean
    val left: Tree
    val right: Tree
    val count: BigInt
    val key: BigInt
    val value: BigInt
  }

  case object Leaf extends Tree {
    override val left = Leaf
    override val right = Leaf
    override val key = BigInt(0)
    override val value = BigInt(0)
    override val count = BigInt(0)
    override val isRed = false
    override val isBlack = false
  }

  case class RedTree (override val key: BigInt,
                      override val value: BigInt,
                      override val left: Tree,
                      override val right: Tree) extends Tree {
    override val count = 1 + left.count + right.count
    override val isRed = true
    override val isBlack = false
  }

  case class BlackTree (override val key: BigInt,
                        override val value: BigInt,
                        override val left: Tree,
                        override val right: Tree) extends Tree {
    override val count = 1 + left.count + right.count
    override val isRed = false
    override val isBlack = true
  }

  def contains (tree: Tree, x: BigInt): Boolean = lookup(tree, x) != Leaf

  def size (tree: Tree): BigInt = tree.count

  def update (tree: Tree, k: BigInt, v: BigInt, overwrite: Boolean): Tree = black(upd(tree, k, v, overwrite))

  def delete (tree: Tree, k: BigInt): Tree = black(del(tree, k))

  def find (tree: Tree, x: BigInt): Option[BigInt] = {
    val t = lookup(tree, x)
    if (t == Leaf)
      None[BigInt]()
    else
      Some(t.value)
  }

  def findMin (tree: Tree): BigInt = {
    require(tree != Leaf)
    if (tree.left == Leaf)
      tree.value
    else
      findMin(tree.left)
  }

  def findMax (tree: Tree): BigInt = {
    require(tree != Leaf)
    if (tree.right == Leaf)
      tree.value
    else
      findMax(tree.right)
  }

  def findNth (tree: Tree, n: BigInt): Option[BigInt] = {
    val count = tree.left.count
    if (n < count)
      findNth(tree.left, n)
    else if (n > count)
      findNth(tree.right, n - count - 1)
    else if (tree == Leaf)
      None[BigInt]()
    else
      Some[BigInt](tree.value)
  }

  private def lookup (tree: Tree, x: BigInt): Tree = {
    if (tree == Leaf) tree
    else {
      if (x < tree.key)
        lookup(tree.left, x)
      else if (x > tree.key)
        lookup(tree.right, x)
      else
        tree
    }
  }

  private def red (tree: Tree): Tree = {
    if (tree.isRed)
      tree
    else if (tree.isBlack)
      RedTree(tree.key, tree.value, tree.left, tree.right)
    else
      Leaf
  }

  private def black (tree: Tree): Tree = {
    if (tree.isBlack)
      tree
    else if (tree.isRed)
      BlackTree(tree.key, tree.value, tree.left, tree.right)
    else
      Leaf
  }

  private def mkTree (isBlack: Boolean, k: BigInt, v: BigInt, l: Tree, r: Tree): Tree =
    if (isBlack) BlackTree(k, v, l, r) else RedTree(k, v, l, r)

  private def balanceLeft (isBlack: Boolean, z: BigInt, zv: BigInt, l: Tree, d: Tree): Tree = if (l == Leaf) Leaf
  else {
    if (l.isRed && l.left.isRed) {
      RedTree(l.key, l.value, BlackTree(l.left.key, l.left.value, l.left.left, l.left.right), BlackTree(z, zv, l.right, d))
    } else if (l.isRed && l.right.isRed) {
      RedTree(l.right.key, l.right.value, BlackTree(l.key, l.value, l.left, l.right.left), BlackTree(z, zv, l.right.right, d))
    } else
      mkTree(isBlack, z, zv, l, d)
  }

  private def balanceRight (isBlack: Boolean, x: BigInt, xv: BigInt, a: Tree, r: Tree): Tree = if (r == Leaf) Leaf
  else {
    if (r.isRed && r.left.isRed)
      RedTree(r.left.key, r.left.value, BlackTree(x, xv, a, r.left.left), BlackTree(r.key, r.value, r.left.right, r.right))
    else if (r.isRed && r.right.isRed)
      RedTree(r.key, r.value, BlackTree(x, xv, a, r.left), BlackTree(r.right.key, r.right.value, r.right.left, r.right.right))
    else
      mkTree(isBlack, x, xv, a, r)
  }

  private def upd (tree: Tree, k: BigInt, v: BigInt, overwrite: Boolean): Tree = if (tree == Leaf) {
    RedTree(k, v, Leaf, Leaf)
  } else {
    if (k < tree.key)
      balanceLeft(tree.isBlack, tree.key, tree.value, upd(tree.left, k, v, overwrite), tree.right)
    else if (k > tree.key)
      balanceRight(tree.isBlack, tree.key, tree.value, tree.left, upd(tree.right, k, v, overwrite))
    else if (overwrite || k != tree.key)
      mkTree(tree.isBlack, k, v, tree.left, tree.right)
    else
      tree
  }

  private def updNth (tree: Tree, idx: BigInt, k: BigInt, v: BigInt, overwrite: Boolean): Tree = if (tree == Leaf) {
    RedTree(k, v, Leaf, Leaf)
  } else {
    val rank = tree.left.count + 1
    if (idx < rank)
      balanceLeft(tree.isBlack, tree.key, tree.value, updNth(tree.left, idx, k, v, overwrite), tree.right)
    else if (idx > rank)
      balanceRight(tree.isBlack, tree.key, tree.value, tree.left, updNth(tree.right, idx - rank, k, v, overwrite))
    else if (overwrite)
      mkTree(tree.isBlack, k, v, tree.left, tree.right)
    else
      tree
  }

  private def del (tree: Tree, k: BigInt): Tree = if (tree == Leaf) Leaf
  else {
    def balance (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = if (tl.isRed) {
      if (tr.isRed)
        RedTree(x, xv, black(tl), black(tr))
      else if (tl.left.isRed)
        RedTree(tl.key, tl.value, black(tl.left), BlackTree(x, xv, tl.right, tr))
      else if (tl.right.isRed)
        RedTree(tl.right.key, tl.right.value, BlackTree(tl.key, tl.value, tl.left, tl.right.left), BlackTree(x, xv, tl.right.right, tr))
      else
        BlackTree(x, xv, tl, tr)

    } else if (tr.isRed) {
      if (tr.right.isRed)
        RedTree(tr.key, tr.value, BlackTree(x, xv, tl, tr.left), black(tr.right))
      else if (tr.left.isRed)
        RedTree(tr.left.key, tr.left.value, BlackTree(x, xv, tl, tr.left.left), BlackTree(tr.key, tr.value, tr.left.right, tr.right))
      else
        BlackTree(x, xv, tl, tr)

    } else {
      BlackTree(x, xv, tl, tr)
    }
    def subl (t: Tree) = {
      // if(t.isBlack)
      //   sys.error("Defect: invariance violation; expected black, got " + t)
      red(t)
    }

    def balLeft (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = {
      if (tl.isRed) {
        RedTree(x, xv, black(tl), tr)
      } else if (tr.isBlack) {
        balance(x, xv, tl, red(tr))
      } else if (tr.isRed && tr.left.isBlack) {
        RedTree(tr.left.key, tr.left.value, BlackTree(x, xv, tl, tr.left.left), balance(tr.key, tr.value, tr.left.right, subl(tr.right)))
      } else {
        // sys.error("Defect: invariance violation")
        Leaf
      }
    }

    def balRight (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = {
      if (tr.isRed) {
        RedTree(x, xv, tl, black(tr))
      } else if (tl.isBlack) {
        balance(x, xv, red(tl), tr)
      } else if (tl.isRed && tl.right.isBlack) {
        RedTree(tl.right.key, tl.right.value, balance(tl.key, tl.value, subl(tl.left), tl.right.left), BlackTree(x, xv, tl.right.right, tr))
      } else {
        // sys.error("Defect: invariance violation")
        Leaf
      }
    }

    def delLeft = {
      if (tree.left.isBlack)
        balLeft(tree.key, tree.value, del(tree.left, k), tree.right)
      else
        RedTree(tree.key, tree.value, del(tree.left, k), tree.right)
    }

    def delRight = {
      if (tree.right.isBlack)
        balRight(tree.key, tree.value, tree.left, del(tree.right, k))
      else
        RedTree(tree.key, tree.value, tree.left, del(tree.right, k))
    }

    def append (tl: Tree, tr: Tree): Tree = if (tl == Leaf) {
      tr
    } else if (tr == Leaf) {
      tl
    } else if (tl.isRed && tr.isRed) {
      val bc = append(tl.right, tr.left)
      if (bc.isRed) {
        RedTree(bc.key, bc.value, RedTree(tl.key, tl.value, tl.left, bc.left), RedTree(tr.key, tr.value, bc.right, tr.right))
      } else {
        RedTree(tl.key, tl.value, tl.left, RedTree(tr.key, tr.value, bc, tr.right))
      }
    } else if (tl.isBlack && tr.isBlack) {
      val bc = append(tl.right, tr.left)
      if (bc.isRed) {
        RedTree(bc.key, bc.value, BlackTree(tl.key, tl.value, tl.left, bc.left), BlackTree(tr.key, tr.value, bc.right, tr.right))
      } else {
        balLeft(tl.key, tl.value, tl.left, BlackTree(tr.key, tr.value, bc, tr.right))
      }
    } else if (tr.isRed) {
      RedTree(tr.key, tr.value, append(tl, tr.left), tr.right)
    } else if (tl.isRed) {
      RedTree(tl.key, tl.value, tl.left, append(tl.right, tr))
    } else {
      // sys.error("unmatched tree on append: " + tl + ", " + tr)
      Leaf
    }
    if (k < tree.key) delLeft
    else if (k > tree.key) delRight
    else append(tree.left, tree.right)
  } // end of function del
}
