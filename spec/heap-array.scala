package libref.spec

import libref.collection._
import libref.proof.MinOps._
import libref.proof.MinLemmas._
import libref.proof.DeleteOps._
import libref.proof.PermutationOps._
import libref.proof.PermutationLemmas._
import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps

object AHeap {

  /* Assumed properties of the comparator */

  @library
  def reflexivity[T] (c : (T, T) => Int, x : T) : Boolean = {
    c(x, x) == 0
  } holds

  @library
  def transitive[T] (c : (T, T) => Int, x : T, y : T, z : T) : Boolean = {
    ((c(x, y) <= 0 && c(y, z) <= 0) ==> c(x, z) <= 0) &&
    ((c(x, y) < 0 && c(y, z) <= 0) ==> c(x, z) < 0) &&
    ((c(x, y) <= 0 && c(y, z) < 0) ==> c(x, z) < 0) &&
    ((c(x, y) < 0 && c(y, z) < 0) ==> c(x, z) < 0)
  } holds

  @library
  def dual[T] (c : (T, T) => Int, x : T, y : T) : Boolean = {
    ((c(x, y) <= 0) ==> (c(y, x) >= 0)) &&
    ((c(x, y) < 0) ==> (c(y, x) > 0)) &&
    ((c(x, y) >= 0) ==> (c(y, x) <= 0)) &&
    ((c(x, y) > 0) ==> (c(y, x) < 0))
  } holds

  /* Access tree nodes */

  def left (i : BigInt) : BigInt = i * 2 + 1

  def right (i : BigInt) : BigInt = i * 2 + 2

  def parent (i : BigInt) : BigInt = {
    require(i > 0)
    (i - 1) / 2
  }

  def left_or_right_child (i : BigInt) : Boolean = {
    require(i > 0)
    i == left(parent(i)) || i == right(parent(i))
  } holds

  /* Descendants */

  def hasDescendant (r : BigInt, i : BigInt) : Boolean = {
    require(r >= 0 && i >= 0)
    if (r > i) false
    else if (r == i) true
    else hasDescendant(r, parent(i))
  }

  def child_is_descendant (i : BigInt) : Boolean = {
    require(i >= 0)
    hasDescendant(i, left(i)) && hasDescendant(i, right(i))
  } holds

  def left_or_right_descendant (r : BigInt, i : BigInt) : Boolean = {
    require(r >= 0 && i >= 0 && hasDescendant(r, i) && r != i)
    (hasDescendant(left(r), i) && !hasDescendant(right(r), i) || hasDescendant(right(r), i) && !hasDescendant(left(r), i)) because {
      if (parent(i) == r) trivial
      else left_or_right_descendant(r, parent(i))
    }
  } holds

  def has_descendant_tran (i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(i >= 0 && j >= 0 && k >= 0 && hasDescendant(i, j) && hasDescendant(j, k))
    hasDescendant(i, k) because {
      if (i == j || j == k) trivial
      else has_descendant_tran(i, j, parent(k))
    }
  } holds

  def is_descendant_of_zero (i : BigInt) : Boolean = {
    require(i >= 0)
    hasDescendant(0, i) because {
      if (i == 0) trivial
      else is_descendant_of_zero(parent(i))
    }
  } holds

  def descendant_is_larger (r : BigInt, i : BigInt) : Boolean = {
    require(r >= 0 && i >= 0 && hasDescendant(r, i))
    r <= i
  } holds

  def not_has_descendant (r : BigInt, i : BigInt) : Boolean = {
    require(r >= 0 && i >= 0 && !hasDescendant(r, i))
    (i > 0 ==> !hasDescendant(r, parent(i))) && !hasDescendant(left(r), i) && !hasDescendant(right(r), i) because {
      if (r > i) trivial
      else not_has_descendant(r, parent(i))
    }
  } holds

  def not_has_descendant (r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(r >= 0 && i >= 0 && j >= 0 && !hasDescendant(r, i) && !hasDescendant(i, r) && hasDescendant(i, j))
    !hasDescendant(r, j) because {
      if (r > j || i == j) trivial
      else not_has_descendant(r, i, parent(j))
    }
  } holds

  /* Ordering */

  def well_ordered[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size)
    ((left(r) < array.size) ==> (c(array(r), array(left(r))) <= 0 && well_ordered(array, c, left(r)))) &&
    ((right(r) < array.size) ==> (c(array(r), array(right(r))) <= 0 && well_ordered(array, c, right(r))))
  }

  def well_ordered[T] (array : MapArray[T], c : (T, T) => Int) : Boolean = {
    require(array.inv)
    if (array.size == 0) true
    else well_ordered(array, c, 0)
  }

  def well_ordered_at[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= r && i < array.size && hasDescendant(r, i) && well_ordered(array, c, r))
    well_ordered(array, c, i) because {
      if (i == r) trivial
      else well_ordered_at (array, c, r, parent(i))
    } && (c(array(r), array(i)) <= 0) because {
      if (r == i) reflexivity(c, array(r))
      else {
        left_or_right_descendant(r, i) &&
        (hasDescendant(left(r), i) ==> (well_ordered_at(array, c, left(r), i) && transitive(c, array(r), array(left(r)), array(i)))) &&
        (hasDescendant(right(r), i) ==> (well_ordered_at(array, c, right(r), i) && transitive(c, array(r), array(right(r)), array(i))))
      }
    } && ((i != r) ==> (c(array(parent(i)), array(i)) <= 0))
  } holds//

  def well_ordered_at[T] (array : MapArray[T], c : (T, T) => Int, i : BigInt) : Boolean = {
    require(array.inv && i >= 0 && i < array.size && well_ordered(array, c))
    well_ordered(array, c, i) because {
      is_descendant_of_zero(i) && well_ordered_at(array, c, 0, i)
    }
  } holds

  def well_ordered_updated[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt, e : T) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && well_ordered(array, c, r) && !hasDescendant(r, i))
    well_ordered(array.updated(i, e), c, r) because {
      not_has_descendant(r, i) &&
      (left(r) < array.size ==> well_ordered_updated(array, c, left(r), i, e)) &&
      (right(r) < array.size ==> well_ordered_updated(array, c, right(r), i, e))
    }
  } holds

  def well_ordered_take[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, n : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && r < n && well_ordered(array, c, r))
    well_ordered(array.take(n), c, r) because {
      if (r == n - 1) trivial
      else {
        MapArrayLemmas.acc_take(array, n, r) &&
        ((left(r) < array.size && left(r) < n) ==> (MapArrayLemmas.acc_take(array, n, left(r)) && well_ordered_take(array, c, left(r), n))) &&
        ((right(r) < array.size && right(r) < n) ==> (MapArrayLemmas.acc_take(array, n, right(r)) && well_ordered_take(array, c, right(r), n)))
      }
    }
  } holds

  def partially_ordered[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size)
    if (r == i) true
    else {
      ((left(r) < array.size && left(r) != i) ==> (c(array(r), array(left(r))) <= 0 && partially_ordered(array, c, left(r), i))) &&
      ((right(r) < array.size && right(r) != i) ==> (c(array(r), array(right(r))) <= 0 && partially_ordered(array, c, right(r), i)))
    }
  }

  def partially_ordered[T] (array : MapArray[T], c : (T, T) => Int, i : BigInt) : Boolean = {
    require(array.inv)
    if (array.size == 0) true
    else partially_ordered(array, c, 0, i)
  }

  def well_ordered_is_partially_ordered[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && well_ordered(array, c, r))
    partially_ordered(array, c, r, i) because {
      if (r == i) trivial
      else {
        ((left(r) < array.size) ==> (well_ordered_is_partially_ordered(array, c, left(r), i))) &&
        ((right(r) < array.size) ==> (well_ordered_is_partially_ordered(array, c, right(r), i)))
      }
    }
  } holds

  def partially_ordered_at[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && j >= 0 && j < array.size &&
      hasDescendant(r, j) && partially_ordered(array, c, r, i))
    (
      (!hasDescendant(i, j) && !hasDescendant(j, i)) ==> (well_ordered(array, c, j) because {
        if (r == j) {
          not_has_descendant(r, i) &&
          ((left(r) < array.size) ==> (partially_ordered_at(array, c, left(r), i, left(j)))) &&
          ((right(r) < array.size) ==> (partially_ordered_at(array, c, right(r), i, right(j))))
        } else {
          left_or_right_descendant(r, j) && (
            if (hasDescendant(left(r), j) && !hasDescendant(right(r), j)) partially_ordered_at(array, c, left(r), i, j)
            else partially_ordered_at(array, c, right(r), i, j)
          )
        }
      })
    ) && (
      (hasDescendant(j, i)) ==> (
        (
          partially_ordered(array, c, r, j) &&
          ((j != i && left(j) < array.size && left(j) != i) ==> c(array(j), array(left(j))) <= 0) &&
          ((j != i && right(j) < array.size && right(j) != i) ==> c(array(j), array(right(j))) <= 0)
        ) because {
        if (r == j || j == i) trivial
        else { 
          left_or_right_descendant(r, j) && (
            if (hasDescendant(left(r), j)) {
              partially_ordered_at(array, c, left(r), i, j) &&
              (
                (right(r) < array.size && right(r) != i) ==>
                (
                  not_has_descendant(right(r), j, i) &&
                  partially_ordered_is_well_ordered(array, c, right(r), i) &&
                  well_ordered_is_partially_ordered(array, c, right(r), j)
                )
              ) &&
              partially_ordered(array, c, r, j)
            } else {
              partially_ordered_at(array, c, right(r), i, j) &&
              (
                (left(r) < array.size && left(r) != i) ==>
                (
                  not_has_descendant(left(r), j, i) &&
                  partially_ordered_is_well_ordered(array, c, left(r), i) &&
                  well_ordered_is_partially_ordered(array, c, left(r), j)
                )
              ) &&
              partially_ordered(array, c, r, j)
            }
          )
        }
      })
    ) && (
      (!hasDescendant(i, j) && j != r) ==> ((c(array(parent(j)), array(j)) <= 0 && c(array(r), array(j)) <= 0) because {
        if (r == parent(j)) trivial
        else left_or_right_descendant(r, j) && (
          if (hasDescendant(left(r), j)) partially_ordered_at(array, c, left(r), i, j) && transitive(c, array(r), array(left(r)), array(j))
          else partially_ordered_at(array, c, right(r), i, j) && transitive(c, array(r), array(right(r)), array(j))
        )
      })
    )
  } holds

  def partially_ordered_is_well_ordered[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && r != i && partially_ordered(array, c, r, i))
    if (!hasDescendant(r, i)) well_ordered(array, c, r) because {
      not_has_descendant(r, i) &&
      ((left(r) < array.size) ==> (partially_ordered_is_well_ordered(array, c, left(r), i))) &&
      ((right(r) < array.size) ==> (partially_ordered_is_well_ordered(array, c, right(r), i)))
    } else if (hasDescendant(r, i) && well_ordered(array, c, i) && c(array(parent(i)), array(i)) <= 0) well_ordered(array, c, r) because {
      if (parent(i) == r)  {
        if (left(r) == i && right(r) < array.size) partially_ordered_at(array, c, r, i, right(r))
        else if (right(r) == i && left(r) < array.size) partially_ordered_at(array, c, r, i, left(r))
        else trivial
      } else {
        left_or_right_descendant(r, i) && (
          if (hasDescendant(left(r), i) && !hasDescendant(right(r), i)) {
            partially_ordered_is_well_ordered(array, c, left(r), i) &&
            (right(r) < array.size ==> partially_ordered_at(array, c, r, i, right(r)))
          } else if (hasDescendant(right(r), i) && !hasDescendant(left(r), i)) {
            partially_ordered_is_well_ordered(array, c, right(r), i) &&
            (left(r) < array.size ==> partially_ordered_at(array, c, r, i, left(r)))
          } else trivial
        )
      }
    } else true
  } holds

  /* Swap */

  /** This lemma may need a 6 seconds timeout to verify. */
  def well_ordered_swap[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && j >= 0 && j < array.size &&
      well_ordered(array, c, r))
    val swapped = array.swap(i, j)
    (
      (array(i) == array(j)) ==> well_ordered(swapped, c, r)
    ) &&
    (
      (!hasDescendant(r, i) && !hasDescendant(r, j)) ==> (well_ordered(swapped, c, r) because {
        not_has_descendant(r, i) && not_has_descendant(r, j) &&
        ((left(r) < array.size) ==> (well_ordered_swap(array, c, left(r), i, j))) &&
        ((right(r) < array.size) ==> (well_ordered_swap(array, c, right(r), i, j)))
      })
    ) && (
      (hasDescendant(r, i) && hasDescendant(i, j)) ==> (partially_ordered(swapped, c, r, i) because {
        if (r == i) trivial
        else {
          left_or_right_descendant(r, i) && (
            if (hasDescendant(left(r), i)) {
              not_has_descendant(right(r), i, j) &&
              well_ordered_swap(array, c, left(r), i, j) &&
              (
                (right(r) < array.size && right(r) != i) ==>
                (well_ordered_swap(array, c, right(r), i, j) && well_ordered_is_partially_ordered(swapped, c, right(r), i))
              )
            } else {
              not_has_descendant(left(r), i, j) &&
              well_ordered_swap(array, c, right(r), i, j) &&
              (
                (left(r) < array.size && left(r) != i) ==>
                (well_ordered_swap(array, c, left(r), i, j) && well_ordered_is_partially_ordered(swapped, c, left(r), i))
              )
            }
          )
        }
      })
    )
  } holds

  def well_ordered_swap_root[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && !hasDescendant(r, i) && well_ordered(array, c, r) &&
      (left(r) < array.size ==> c(array(i), array(left(r))) <= 0) &&
      (right(r) < array.size ==> c(array(i), array(right(r))) <= 0) &&
      not_has_descendant(r, i)
    )
    val swapped = array.swap(r, i)
    well_ordered(swapped, c, r) because {
      (left(r) < array.size ==> well_ordered_swap(array, c, left(r), r, i)) &&
      (right(r) < array.size ==> well_ordered_swap(array, c, right(r), r, i))
    }
  } holds

  /** This lemma may need a 10 seconds timeout to verify. */
  def partially_ordered_swap[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i > 0 && i < array.size && j >= 0 && j < array.size &&
      partially_ordered(array, c, r, i))
    val swapped = array.swap(i, j)
    (
      (array(i) == array(j)) ==> partially_ordered(swapped, c, r, i)
    ) && (
      (!hasDescendant(r, i) && !hasDescendant(r, j)) ==> (well_ordered(swapped, c, r) because {
        not_has_descendant(r, i) && not_has_descendant(r, j) &&
        ((left(r) < array.size) ==> (partially_ordered_swap(array, c, left(r), i, j))) &&
        ((right(r) < array.size) ==> (partially_ordered_swap(array, c, right(r), i, j)))
      })
    ) && (
      (hasDescendant(r, i) && hasDescendant(i, j)) ==> (partially_ordered(swapped, c, r, i) because {
        if (r == i) trivial
        else {
          left_or_right_descendant(r, i) && (
            if (hasDescendant(left(r), i)) {
              not_has_descendant(right(r), i, j) &&
              partially_ordered_swap(array, c, left(r), i, j) &&
              (
                (right(r) < array.size && right(r) != i) ==>
                (partially_ordered_swap(array, c, right(r), i, j) && well_ordered_is_partially_ordered(swapped, c, right(r), i))
              )
            } else {
              not_has_descendant(left(r), i, j) &&
              partially_ordered_swap(array, c, right(r), i, j) &&
              (
                (left(r) < array.size && left(r) != i) ==>
                (partially_ordered_swap(array, c, left(r), i, j) && well_ordered_is_partially_ordered(swapped, c, left(r), i))
              )
            }
          )
        }
      })
     ) && (
      (hasDescendant(r, j) && hasDescendant(j, i)) ==> (partially_ordered(swapped, c, r, j) because {
        if (r == j || j == i) trivial
        else {
          left_or_right_descendant(r, j) && (
            if (hasDescendant(left(r), j)) {
              not_has_descendant(right(r), j, i) &&
              partially_ordered_swap(array, c, left(r), i, j) &&
              (
                (right(r) < array.size && right(r) != j) ==>
                (partially_ordered_swap(array, c, right(r), i, j) && well_ordered_is_partially_ordered(swapped, c, right(r), j))
              )
            } else {
              not_has_descendant(left(r), j, i) &&
              partially_ordered_swap(array, c, right(r), i, j) &&
              (
                (left(r) < array.size && left(r) != j) ==>
                (partially_ordered_swap(array, c, left(r), i, j) && well_ordered_is_partially_ordered(swapped, c, left(r), j))
              )
            }
          )
        }
      })
    )
  } holds

  /* Append */

  def well_ordered_append[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, e : T) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && well_ordered(array, c, r))
    val a = array :+ e
    val i = array.size
    val size = array.size + 1
    well_ordered(a, c, i) &&
    (if (hasDescendant(r, i)) {
      partially_ordered(a, c, r, i) because {
        left_or_right_descendant(r, i) && (
          if (hasDescendant(left(r), i)) {
            ((left(r) < size && left(r) != i) ==> (well_ordered_append(array, c, left(r), e))) &&
            ((right(r) < size && right(r) != i) ==> (well_ordered_append(array, c, right(r), e) && well_ordered_is_partially_ordered(a, c, right(r), i)))
          } else {
            ((right(r) < size && right(r) != i) ==> (well_ordered_append(array, c, right(r), e))) &&
            ((left(r) < size && left(r) != i) ==> (well_ordered_append(array, c, left(r), e) && well_ordered_is_partially_ordered(a, c, left(r), i)))
          }
        )
      }
    } else {
      well_ordered(a, c, r) because {
        not_has_descendant(r, i) && 
        ((left(r) < size) ==> (c(a(r), a(left(r))) <= 0 && well_ordered_append(array, c, left(r), e))) &&
        ((right(r) < size) ==> (c(a(r), a(right(r))) <= 0 && well_ordered_append(array, c, right(r), e)))
      }
    })
  } holds

  /* Validity of an array as a binary heap */

  def valid[T] (array : MapArray[T], c : (T, T) => Int) : Boolean = {
    array.inv && well_ordered(array, c)
  }

  /* Percolating up */

  def percolatingUp_op[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : MapArray[T] = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i))
    if (r == i) array
    else if (c(array(i), array(parent(i))) <= 0) percolatingUp_op(array.swap(i, parent(i)), c, r, parent(i))
    else array
  } ensuring { res =>
    res.inv && res.size == array.size
  }

  /* This lemma may need a 8 seconds timeout to verify. */
  def percolatingUp_ind1[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) && r != i &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) &&
      c(array(i), array(parent(i))) <= 0 &&
      (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
      (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0)
    )
    val p = parent(i)
    val lc = left(parent(i))
    val rc = right(parent(i))
    val swapped = array.swap(i, p)
    well_ordered(swapped, c, p) because {
      dual(c, array(p), array(i)) &&
      (if (rc == i) {
        partially_ordered_at(array, c, r, i, lc) &&
        well_ordered_swap(array, c, lc, i, p) &&
        well_ordered_swap_root(array, c, i, p) &&
        partially_ordered_at(array, c, r, i, p) &&
        transitive(c, array(rc), array(p), array(lc))
      } else if (rc < array.size) {
        partially_ordered_at(array, c, r, i, rc) &&
        well_ordered_swap(array, c, rc, i, p) &&
        well_ordered_swap_root(array, c, i, p) &&
        partially_ordered_at(array, c, r, i, p) &&
        transitive(c, array(lc), array(p), array(rc))
      } else {
        trivial
      })
    }
  } holds

  def percolatingUp_ind2[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) && r != i &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) &&
      c(array(i), array(parent(i))) <= 0 &&
      (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
      (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0)
    )
    val p = parent(i)
    val lc = left(parent(i))
    val rc = right(parent(i))
    val swapped = array.swap(i, p)
    partially_ordered(swapped, c, r, p) because {
      partially_ordered_swap(array, c, r, i, p)
    }
  } holds

  def percolatingUp_ind3[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) && r != i &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) &&
      c(array(i), array(parent(i))) <= 0 &&
      (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
      (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0)
    )
    val p = parent(i)
    val lc = left(parent(i))
    val rc = right(parent(i))
    val swapped = array.swap(i, p)
    (p > 0 && p != r) ==> (
      ((lc < swapped.size) ==> c(swapped(parent(p)), swapped(lc)) <= 0) &&
      ((rc < swapped.size) ==> c(swapped(parent(p)), swapped(rc)) <= 0) because {
        partially_ordered_at(array, c, r, i, p) && (
          if (rc == i) transitive(c, array(parent(p)), array(p), array(lc))
          else if (rc < swapped.size) transitive(c, array(parent(p)), array(p), array(rc))
          else trivial
        )
      }
    )
  } holds

  def percolatingUp_ind[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) &&
      ((r != i && left(i) < array.size) ==> c(array(parent(i)), array(left(i))) <= 0) &&
      ((r != i && right(i) < array.size) ==> c(array(parent(i)), array(right(i))) <= 0)
    )
    if (r == i) true
    else if (c(array(i), array(parent(i))) <= 0) {
      val p = parent(i)
      val lc = left(parent(i))
      val rc = right(parent(i))
      val swapped = array.swap(i, p)
      well_ordered(swapped, c, p) && partially_ordered(swapped, c, r, p) &&
      ((p > 0 && p != r) ==> (
        ((lc < swapped.size) ==> c(swapped(parent(p)), swapped(lc)) <= 0) &&
        ((rc < swapped.size) ==> c(swapped(parent(p)), swapped(rc)) <= 0)
      )) because {
        percolatingUp_ind1(array, c, r, i) && percolatingUp_ind2(array, c, r, i) && percolatingUp_ind3(array, c, r, i)
      }
    } else well_ordered(array, c, r) because {
      dual(c, array(parent(i)), array(i)) && partially_ordered_is_well_ordered(array, c, r, i)
    }
  } holds

  def percolatingUp_valid[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) && ((r != i) ==> (
        (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
        (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0))
      )
    )
    well_ordered(percolatingUp_op(array, c, r, i), c, r) because {
      if (r == i) trivial
      else if (c(array(i), array(parent(i))) <= 0) percolatingUp_ind(array, c, r, i) && percolatingUp_valid(array.swap(i, parent(i)), c, r, parent(i))
      else percolatingUp_ind(array, c, r, i)
    }
  } holds

  def percolatingUp_perm[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) && ((r != i) ==> (
        (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
        (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0))
      )
    )
    permutation(percolatingUp_op(array, c, r, i).toList, array.toList) because {
      if (r == i) permutation_refl(array.toList)
      else if (c(array(i), array(parent(i))) <= 0) {
        percolatingUp_ind(array, c, r, i) && percolatingUp_perm(array.swap(i, parent(i)), c, r, parent(i)) &&
        MapArrayLemmas.swap_toList_perm(array, i, parent(i)) &&
        permutation_tran(percolatingUp_op(array, c, r, i).toList, array.swap(i, parent(i)).toList, array.toList)
      } else permutation_refl(array.toList)
    }
  } holds

  def percolatingUp_root[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) && ((r != i) ==> (
        (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
        (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0))
      )
    )
    if (c(array(i), array(r)) <= 0) percolatingUp_op(array, c, r, i)(r) == array(i) because {
      if (r == i) trivial
      else if (c(array(i), array(parent(i))) <= 0) percolatingUp_ind(array, c, r, i) && percolatingUp_root(array.swap(i, parent(i)), c, r, parent(i))
      else {
        dual(c, array(i), array(parent(i))) &&
        transitive(c, array(parent(i)), array(i), array(r)) &&
        partially_ordered_at(array, c, r, i, parent(i)) &&
        dual(c, array(r), array(parent(i)))
      }
    } else percolatingUp_op(array, c, r, i)(r) == array(r) because {
      if (r == i) trivial
      else if (c(array(i), array(parent(i))) <= 0) percolatingUp_ind(array, c, r, i) && percolatingUp_root(array.swap(i, parent(i)), c, r, parent(i))
      else trivial
    }
  } holds

  def percolatingUp[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : MapArray[T] = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && hasDescendant(r, i) &&
      partially_ordered(array, c, r, i) && well_ordered(array, c, i) && ((r != i) ==> (
        (left(i) < array.size ==> c(array(parent(i)), array(left(i))) <= 0) &&
        (right(i) < array.size ==> c(array(parent(i)), array(right(i))) <= 0))
      )
    )
    percolatingUp_op(array, c, r, i)
  } ensuring { res =>
    res.size == array.size &&
    well_ordered(res, c, r) because { percolatingUp_valid(array, c, r, i) } && (
      if (c(array(i), array(r)) <= 0) res(r) == array(i)
      else res(r) == array(r)
    ) because { percolatingUp_root(array, c, r, i) } && permutation(res.toList, array.toList) because {
      percolatingUp_perm(array, c, r, i)
    }
  }

  /* Insert */

  def insert[T] (array : MapArray[T], c : (T, T) => Int, e : T) : MapArray[T] = {
    require(array.inv && well_ordered(array, c) && is_descendant_of_zero(array.size) && (array.size > 0 ==> well_ordered_append(array, c, 0, e)))
    percolatingUp(array :+ e, c, 0, array.size)
  } ensuring { res =>
    res.size == array.size + 1 && res.inv && well_ordered(res, c) && (
      if (res.size == 1) res(0) == e
      else if (c(e, array(0)) <= 0) res(0) == e
      else res(0) == array(0)
    ) && permutation(res.toList, array.toList :+ e) because {
      IMap.toList_snoc(array.map, e, array.from, array.until) && permutation_eq((array :+ e).toList, array.toList :+ e)
    }
  }

  /* Percolating down */

  def percolatingDown_op[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : MapArray[T] = {
    require(array.inv && r >= 0 && r < array.size)
    val lc = left(r)
    val rc = right(r)
    if (rc < array.size) {
      if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) array
      else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) percolatingDown_op(array.swap(r, lc), c, lc)
      else percolatingDown_op(array.swap(r, rc), c, rc)
    } else if (lc < array.size) {
      if (c(array(r), array(lc)) <= 0) array
      else percolatingDown_op(array.swap(r, lc), c, lc)
    } else
      array
  } ensuring { res =>
    res.inv && res.size == array.size
  }

  def percolatingDown_else[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size)
    val lc = left(r)
    val rc = right(r)
    if (rc < array.size) {
      if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) true
      else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) true
      else {
        c(array(rc), array(r)) <= 0 && c(array(rc), array(lc)) <= 0 because {
          if (c(array(r), array(lc)) > 0 && c(array(lc), array(r)) > 0) dual(c, array(r), array(lc))
          else if (c(array(r), array(lc)) > 0 && c(array(lc), array(rc)) > 0) {
            dual(c, array(lc), array(rc)) && dual(c, array(r), array(lc)) && transitive(c, array(rc), array(lc), array(r))
          } else if (c(array(r), array(rc)) > 0 && c(array(lc), array(r)) > 0) {
            dual(c, array(r), array(rc)) && dual(c, array(lc), array(r)) && transitive(c, array(rc), array(r), array(lc))
          } else dual(c, array(r), array(rc)) && dual(c, array(lc), array(rc))
        }
      }
    } else if (lc < array.size) {
      if (c(array(r), array(lc)) <= 0) true
      else c(array(lc), array(r)) <= 0 because { dual(c, array(r), array(lc)) }
    } else
      true
  }

  /* This lemma may need a 10 seconds timeout to verify. */
  def percolatingDown_ind[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size &&
      (r > 0 ==> c(array(parent(r)), array(r)) <= 0) &&
      ((r > 0 && left(r) < array.size) ==> c(array(parent(r)), array(left(r))) <= 0) &&
      ((r > 0 && right(r) < array.size) ==> c(array(parent(r)), array(right(r))) <= 0) &&
      (left(r) < array.size ==> well_ordered(array, c, left(r))) && (right(r) < array.size ==> well_ordered(array, c, right(r)))
    )
    val lc = left(r)
    val rc = right(r)
    ((lc < array.size && left(lc) < array.swap(r, lc).size) ==> (well_ordered(array.swap(r, lc), c, left(lc)) because {
      well_ordered_swap(array, c, left(lc), r, lc)
    })) &&
    ((lc < array.size && right(lc) < array.swap(r, lc).size) ==> (well_ordered(array.swap(r, lc), c, right(lc)) because {
      well_ordered_swap(array, c, right(lc), r, lc)
    })) &&
    ((rc < array.size) ==> (well_ordered(array.swap(r, lc), c, rc) because {
      well_ordered_swap(array, c, rc, r, lc)
    })) &&
    ((rc < array.size && left(rc) < array.swap(r, rc).size) ==> (well_ordered(array.swap(r, rc), c, left(rc)) because {
      well_ordered_swap(array, c, left(rc), r, rc)
    })) &&
    ((rc < array.size && right(rc) < array.swap(r, rc).size) ==> (well_ordered(array.swap(r, rc), c, right(rc)) because {
      well_ordered_swap(array, c, right(rc), r, rc)
    })) &&
    ((rc < array.size) ==> (well_ordered(array.swap(r, rc), c, lc) because {
      well_ordered_swap(array, c, lc, r, rc)
    })) &&
    (
      if (rc < array.size) {
        if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) true
        else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) {
          val swapped = array.swap(r, lc)
          (c(swapped(r), swapped(lc)) <= 0) &&
          (left(lc) < swapped.size ==> c(swapped(r), swapped(left(lc))) <= 0) &&
          (right(lc) < swapped.size ==> c(swapped(r), swapped(right(lc))) <= 0)
        } else {
          val swapped = array.swap(r, rc)
          (c(swapped(r), swapped(rc)) <= 0) &&
          (left(rc) < swapped.size ==> c(swapped(r), swapped(left(rc))) <= 0) &&
          (right(rc) < swapped.size ==> c(swapped(r), swapped(right(rc))) <= 0) because { percolatingDown_else(array, c, r) }
        }
      } else if (lc < array.size) {
        if (c(array(r), array(lc)) <= 0) true
        else {
          val swapped = array.swap(r, lc)
          (c(swapped(r), swapped(lc)) <= 0) &&
          (left(lc) < swapped.size ==> c(swapped(r), swapped(left(lc))) <= 0) &&
          (right(lc) < swapped.size ==> c(swapped(r), swapped(right(lc))) <= 0) because { percolatingDown_else(array, c, r) }
        }
      } else
        true
    )
  } holds

  /** This lemma may need a 8 seconds timeout to verify. */
  def percolatingDown_value_unchanged[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size && !hasDescendant(r, i))
    val res = percolatingDown_op(array, c, r)
    val lc = left(r)
    val rc = right(r)
    res(i) == array(i) because {
      not_has_descendant(r, i) && (
        if (rc < array.size) {
          if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) trivial
          else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) percolatingDown_value_unchanged(array.swap(r, lc), c, lc, i)
          else percolatingDown_value_unchanged(array.swap(r, rc), c, rc, i)
        } else if (lc < array.size) {
          if (c(array(r), array(lc)) <= 0) trivial
          else percolatingDown_value_unchanged(array.swap(r, lc), c, lc, i)
        } else
          trivial
      )
    }
  } holds

  /* 
   * This lemma may need a 250 seconds timeout to verify. All the hints can be
   * derived from other facts. Without the hints, this lemma will take at least
   * 4 hours to verify.
   */
  def percolatingDown_compare[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size &&
      (r > 0 ==> c(array(parent(r)), array(r)) <= 0) &&
      ((r > 0 && left(r) < array.size) ==> c(array(parent(r)), array(left(r))) <= 0) &&
      ((r > 0 && right(r) < array.size) ==> c(array(parent(r)), array(right(r))) <= 0) &&
      (left(r) < array.size ==> well_ordered(array, c, left(r))) && (right(r) < array.size ==> well_ordered(array, c, right(r)))
    )
    if (r == 0) true
    else {
      val res = percolatingDown_op(array, c, r)
      val p = parent(r)
      val lc = left(r)
      val rc = right(r)
      (c(res(p), res(r)) <= 0) &&
      (lc < res.size ==> c(res(p), res(lc)) <= 0) &&
      (rc < res.size ==> c(res(p), res(rc)) <= 0) because {
        percolatingDown_ind(array, c, r) && (
          if (rc < array.size) {
            if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) trivial
            else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) {
              percolatingDown_compare(array.swap(r, lc), c, lc) &&              /* hints */ c(res(r), res(lc)) <= 0 &&
              percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) &&   /* hints */ res(r) == array.swap(r, lc)(r) && res(r) == array(lc) &&
              percolatingDown_value_unchanged(array.swap(r, lc), c, lc, rc) &&  /* hints */ res(rc) == array.swap(r, lc)(rc) && res(rc) == array(rc) &&
              percolatingDown_value_unchanged(array.swap(r, lc), c, lc, p) &&   /* hints */ res(p) == array.swap(r, lc)(p) && res(p) == array(p) &&
              transitive(c, res(p), res(r), res(lc))
            } else {
              percolatingDown_compare(array.swap(r, rc), c, rc) &&              /* hints */ c(res(r), res(rc)) <= 0 &&
              percolatingDown_value_unchanged(array.swap(r, rc), c, rc, r) &&   /* hints */ res(r) == array.swap(r, rc)(r) && res(r) == array(rc) &&
              percolatingDown_value_unchanged(array.swap(r, rc), c, rc, lc) &&  /* hints */ res(lc) == array.swap(r, rc)(lc) && res(lc) == array(lc) &&
              percolatingDown_value_unchanged(array.swap(r, rc), c, rc, p) &&   /* hints */ res(p) == array.swap(r, rc)(p) && res(p) == array(p) &&
              transitive(c, res(p), res(r), res(rc))
            }
          } else if (lc < array.size) {
            if (c(array(r), array(lc)) <= 0) trivial
            else {
              percolatingDown_compare(array.swap(r, lc), c, lc) &&              /* hints */ c(res(r), res(lc)) <= 0 &&
              percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) &&   /* hints */ res(r) == array.swap(r, lc)(r) && res(r) == array(lc) &&
              percolatingDown_value_unchanged(array.swap(r, lc), c, lc, p) &&   /* hints */ res(p) == array.swap(r, lc)(p) && res(p) == array(p) &&
              transitive(c, res(p), res(r), res(lc))
            }
          } else trivial
        )
      }
    }
  } holds

  def percolatingDown_sibling[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt, i : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size && i >= 0 && i < array.size &&
      well_ordered(array, c, i) && !hasDescendant(r, i) && !hasDescendant(i, r) &&
      (r > 0 ==> c(array(parent(r)), array(r)) <= 0) &&
      ((r > 0 && left(r) < array.size) ==> c(array(parent(r)), array(left(r))) <= 0) &&
      ((r > 0 && right(r) < array.size) ==> c(array(parent(r)), array(right(r))) <= 0) &&
      (left(r) < array.size ==> well_ordered(array, c, left(r))) && (right(r) < array.size ==> well_ordered(array, c, right(r)))
    )
    val lc = left(r)
    val rc = right(r)
    well_ordered(percolatingDown_op(array, c, r), c, i) because {
      if (rc < array.size) {
        if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) trivial
        else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) {
          well_ordered_swap(array, c, i, r, lc) &&
          percolatingDown_ind(array, c, r) &&
          not_has_descendant(r, i) &&
          percolatingDown_sibling(array.swap(r, lc), c, lc, i)
        } else {
          well_ordered_swap(array, c, i, r, rc) &&
          percolatingDown_ind(array, c, r) &&
          not_has_descendant(r, i) &&
          percolatingDown_sibling(array.swap(r, rc), c, rc, i)
        }
      } else if (lc < array.size) {
        if (c(array(r), array(lc)) <= 0) trivial
        else {
          well_ordered_swap(array, c, i, r, lc) &&
          percolatingDown_ind(array, c, r) &&
          not_has_descendant(r, i) &&
          percolatingDown_sibling(array.swap(r, lc), c, lc, i)
        }
      } else
        trivial
    }
  } holds

  /* 
   * This lemma may take more than 190 seconds to verify. All the hints can be
   * derived from other facts. Without the hints, this lemma will take at least
   * 350 seconds to verify.
   */
  def percolatingDown_valid[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size &&
      (r > 0 ==> c(array(parent(r)), array(r)) <= 0) &&
      ((r > 0 && left(r) < array.size) ==> c(array(parent(r)), array(left(r))) <= 0) &&
      ((r > 0 && right(r) < array.size) ==> c(array(parent(r)), array(right(r))) <= 0) &&
      (left(r) < array.size ==> well_ordered(array, c, left(r))) && (right(r) < array.size ==> well_ordered(array, c, right(r)))
    )
    val res = percolatingDown_op(array, c, r)
    val lc = left(r)
    val rc = right(r)
    well_ordered(res, c, r) because {
      percolatingDown_ind(array, c, r) && (
        if (rc < array.size) {
          if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) trivial
          else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) {
            percolatingDown_valid(array.swap(r, lc), c, lc) &&                /* hints */ well_ordered(res, c, lc) &&
            percolatingDown_sibling(array.swap(r, lc), c, lc, rc) &&          /* hints */ well_ordered(res, c, rc) &&
            percolatingDown_value_unchanged(array.swap(r, lc), c, lc, rc) &&  /* hints */ res(rc) == array.swap(r, lc)(rc) && res(rc) == array(rc) &&
            percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) &&   /* hints */ res(r) == array.swap(r, lc)(r) && res(r) == array(lc) &&
            percolatingDown_compare(array.swap(r, lc), c, lc) &&              /* hints */ c(res(r), res(lc)) <= 0
          } else {
            percolatingDown_valid(array.swap(r, rc), c, rc) &&                /* hints */ well_ordered(res, c, rc) &&
            percolatingDown_sibling(array.swap(r, rc), c, rc, lc) &&          /* hints */ well_ordered(res, c, lc) &&
            percolatingDown_value_unchanged(array.swap(r, rc), c, rc, lc) &&  /* hints */ res(lc) == array.swap(r, rc)(lc) && res(lc) == array(lc) &&
            percolatingDown_value_unchanged(array.swap(r, rc), c, rc, r) &&   /* hints */ res(r) == array.swap(r, rc)(r) && res(r) == array(rc) &&
            percolatingDown_compare(array.swap(r, rc), c, rc) &&              /* hints */ c(res(r), res(rc)) <= 0
          }
        } else if (lc < array.size) {
          if (c(array(r), array(lc)) <= 0) trivial
          else {
            percolatingDown_valid(array.swap(r, lc), c, lc) &&                /* hints */ well_ordered(res, c, lc) &&
            percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) &&   /* hints */ res(r) == array.swap(r, lc)(r) && res(r) == array(lc) &&
            percolatingDown_compare(array.swap(r, lc), c, lc) &&              /* hints */ c(res(r), res(lc)) <= 0
          }
        } else
          trivial
      )
    }
  } holds

  def percolatingDown_root[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size)
    val res = percolatingDown_op(array, c, r)
    val lc = left(r)
    val rc = right(r)
    (
      if (rc < array.size) {
        if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) res(r) == array(r)
        else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) res(r) == array(lc) because { percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) }
        else res(r) == array(rc) because { percolatingDown_value_unchanged(array.swap(r, rc), c, rc, r) }
      } else if (lc < array.size) {
        if (c(array(r), array(lc)) <= 0) res(r) == array(r) because { percolatingDown_value_unchanged(array.swap(r, lc), c, lc, r) }
        else res(r) == array(lc)
      } else res(r) == array(r)
    )
  } holds

  def percolatingDown_perm[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size)
    val res = percolatingDown_op(array, c, r)
    val lc = left(r)
    val rc = right(r)
    permutation(res.toList, array.toList) because {
      if (rc < array.size) {
        if (c(array(r), array(lc)) <= 0 && c(array(r), array(rc)) <= 0) permutation_refl(array.toList)
        else if (c(array(lc), array(r)) <= 0 && c(array(lc), array(rc)) <= 0) {
          percolatingDown_perm(array.swap(r, lc), c, lc) &&
          MapArrayLemmas.swap_toList_perm(array, r, lc) &&
          permutation_tran(percolatingDown_op(array, c, r).toList, array.swap(r, lc).toList, array.toList)
        } else {
          percolatingDown_perm(array.swap(r, rc), c, rc) &&
          MapArrayLemmas.swap_toList_perm(array, r, rc) &&
          permutation_tran(percolatingDown_op(array, c, r).toList, array.swap(r, rc).toList, array.toList)
        }
      } else if (lc < array.size) {
        if (c(array(r), array(lc)) <= 0) permutation_refl(array.toList)
        else {
          percolatingDown_perm(array.swap(r, lc), c, lc) &&
          MapArrayLemmas.swap_toList_perm(array, r, lc) &&
          permutation_tran(percolatingDown_op(array, c, r).toList, array.swap(r, lc).toList, array.toList)
        }
      } else permutation_refl(array.toList)
    }
  } holds

  def percolatingDown[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : MapArray[T] = {
    require(array.inv && r >= 0 && r < array.size &&
      (r > 0 ==> c(array(parent(r)), array(r)) <= 0) &&
      ((r > 0 && left(r) < array.size) ==> c(array(parent(r)), array(left(r))) <= 0) &&
      ((r > 0 && right(r) < array.size) ==> c(array(parent(r)), array(right(r))) <= 0) &&
      (left(r) < array.size ==> well_ordered(array, c, left(r))) && (right(r) < array.size ==> well_ordered(array, c, right(r)))
    )
    percolatingDown_op(array, c, r)
  } ensuring { res =>
    res.size == array.size &&
    res.inv &&
    well_ordered(res, c, r) because { percolatingDown_valid(array, c, r) } &&
    (if (right(r) < array.size) {
      if (c(array(r), array(left(r))) <= 0 && c(array(r), array(right(r))) <= 0) res(r) == array(r)
      else if (c(array(left(r)), array(r)) <= 0 && c(array(left(r)), array(right(r))) <= 0) res(r) == array(left(r))
      else res(r) == array(right(r))
    } else if (left(r) < array.size) {
      if (c(array(r), array(left(r))) <= 0) res(r) == array(r)
      else res(r) == array(left(r))
    } else res(r) == array(r)) because { percolatingDown_root(array, c, r) } &&
    permutation(res.toList, array.toList) because { percolatingDown_perm(array, c, r) }
  }

  /* Delete Min */

  /** This lemma may need a 80 seconds timeout to verify. */
  def acc_drop_rotate[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r >= 0 && r < array.size - 1)
    array.drop(1).rotate(array.size - 2)(r) == (
      if (r == 0) array(array.size - 1)
      else array(r)
    ) because {
      if (r == 0) MapArrayLemmas.acc_rotate(array.drop(1), array.size - 2, 0)
      else {
        MapArrayLemmas.acc_rotate(array.drop(1), array.size - 2, r) &&
        MapArrayLemmas.acc_drop(array, 1, r - (array.size - 1) + (array.size - 2))
      }
    }
  } holds

  def drop_rotate_well_ordered[T] (array : MapArray[T], c : (T, T) => Int, r : BigInt) : Boolean = {
    require(array.inv && r > 0 && r < array.size - 1 && well_ordered(array, c, r))
    well_ordered(array.drop(1).rotate(array.size - 2), c, r) because {
      acc_drop_rotate(array, c, r) &&
      ((left(r) < array.size - 1) ==> (acc_drop_rotate(array, c, left(r)) && drop_rotate_well_ordered(array, c, left(r)))) &&
      ((right(r) < array.size - 1) ==> (acc_drop_rotate(array, c, right(r)) && drop_rotate_well_ordered(array, c, right(r))))
    }
  } holds

  def deleteMin_op[T] (array : MapArray[T], c : (T, T) => Int) : MapArray[T] = {
    require(array.inv && well_ordered(array, c) &&
      ((1 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 1)) &&
      ((2 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 2))
    )
    if (array.size <= 1) MapArray.empty[T]
    else percolatingDown(array.drop(1).rotate(array.size - 2), c, 0)
  } ensuring { res =>
    res.size == (if (array.isEmpty) BigInt(0) else array.size - 1) && res.inv && well_ordered(res, c)
  }

  /* This unused lemma is not finished. Always get stack overflow. */
  @ignore
  def deleteMin_root[T] (array : MapArray[T], c : (T, T) => Int) : Boolean = {
    require(array.inv && well_ordered(array, c) &&
      ((1 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 1)) &&
      ((2 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 2))
    )
    val size = array.size
    val last = array(size - 1)
    val deleted = deleteMin_op(array, c)
    if (size <= 1) deleted.isEmpty
    else if (size == 2) deleted(0) == array(1)
    else if (size > 2 && c(last, array(1)) <= 0 && c(last, array(2)) <= 0) deleted(0) == last
    else true
  } holds // unknown

  def deleteMin_perm[T] (array : MapArray[T], c : (T, T) => Int) : Boolean = {
    require(array.inv && well_ordered(array, c) &&
      ((1 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 1)) &&
      ((2 < array.size - 1) ==> drop_rotate_well_ordered(array, c, 2))
    )
    permutation(deleteMin_op(array, c).toList, array.toList.drop(1)) because {
      if (array.size <= 1) trivial
      else {
        MapArrayLemmas.rotate_toList(array.drop(1), array.size - 2) &&
        MapArrayLemmas.drop_toList(array, 1) &&
        rotate_perm(array.drop(1).toList, array.size - 2) &&
        permutation_tran(deleteMin_op(array, c).toList, array.drop(1).rotate(array.size - 2).toList, array.drop(1).toList)
      }
    }
  } holds

  def deleteMin_toList_perm[T] (array : MapArray[T], c : (T, T) => Int) : Boolean = {
    require(array.inv && well_ordered(array, c) && !array.isEmpty)
    permutation(deleteMin_op(array, c).toList, delete(array.toList, array(0))) because {
      deleteMin_perm(array, c) && MapArrayLemmas.drop_toList(array, 1)
    }
  } holds

  def deleteMin[T] (array : MapArray[T], c : (T, T) => Int) : MapArray[T] = {
    require(array.inv && well_ordered(array, c))
    deleteMin_op(array, c)
  } ensuring { res =>
    res.size == (if (array.isEmpty) BigInt(0) else array.size - 1) && res.inv && well_ordered(res, c) &&
    permutation(res.toList, array.toList.drop(1)) because { deleteMin_perm(array, c) } &&
    ((!array.isEmpty) ==> (permutation(res.toList, delete(array.toList, array(0))) because { deleteMin_toList_perm(array, c) }))
  }

  /* Merge */

  def merge_op[T] (a1 : MapArray[T], a2 : MapArray[T], c : (T, T) => Int) : MapArray[T] = {
    require(a1.inv && a2.inv && well_ordered(a1, c) && well_ordered(a2, c))
    if (a2.isEmpty) a1
    else merge_op(insert(a1, c, a2(0)), deleteMin(a2, c), c)
  } ensuring { res =>
    res.size == a1.size + a2.size && res.inv && well_ordered(res, c)
  }

  def merge_perm[T] (a1 : MapArray[T], a2 : MapArray[T], c : (T, T) => Int) : Boolean = {
    require(a1.inv && a2.inv && well_ordered(a1, c) && well_ordered(a2, c))
    permutation(merge_op(a1, a2, c).toList, a1.toList ++ a2.toList) because {
      if (a2.isEmpty) permutation_refl(a1.toList)
      else {
        merge_perm(insert(a1, c, a2(0)), deleteMin(a2, c), c) &&
        cons_snoc_perm(a1.toList, a2(0)) &&
        permutation_comm(a2(0) :: a1.toList, a1.toList :+ a2(0)) &&
        permutation_tran(insert(a1, c, a2(0)).toList, a1.toList :+ a2(0), a2(0) :: a1.toList) &&
        permutation_concat(insert(a1, c, a2(0)).toList, deleteMin(a2, c).toList, a2(0) :: a1.toList, delete(a2.toList, a2(0))) &&
        permutation_tran(merge_op(a1, a2, c).toList, insert(a1, c, a2(0)).toList ++ deleteMin(a2, c).toList, (a2(0) :: a1.toList) ++ delete(a2.toList, a2(0))) &&
        permutation_concat_move(a1.toList, a2.toList, a2(0)) &&
        permutation_tran(merge_op(a1, a2, c).toList, (a2(0) :: a1.toList) ++ delete(a2.toList, a2(0)), a1.toList ++ a2.toList)
      }
    }
  } holds

  def merge[T] (a1 : MapArray[T], a2 : MapArray[T], c : (T, T) => Int) : MapArray[T] = {
    require(a1.inv && a2.inv && well_ordered(a1, c) && well_ordered(a2, c))
    merge_op(a1, a2, c)
  } ensuring { res =>
    res.size == a1.size + a2.size && res.inv && well_ordered(res, c) &&
    permutation(res.toList, a1.toList ++ a2.toList) because { merge_perm(a1, a2, c) }
  }

}

case class ArrayHeap[T] (array : MapArray[T], c : (T, T) => Int) {

  def deleteMin : ArrayHeap[T] = {
    require(inv)
    ArrayHeap(AHeap.deleteMin(array, c), c)
  } ensuring { res =>
    res.size == (if (isEmpty) BigInt(0) else size - 1) && res.inv && res.c == c &&
    permutation(res.toList, array.toList.drop(1)) &&
    ((!isEmpty) ==> permutation(res.toList, delete(array.toList, findMin.get)))
  }

  def findMin : Option[T] = {
    require(inv)
    if (size == 0) None[T]()
    else Some[T](array(0))
  } ensuring { res =>
    ((res.isDefined) ==> (res.get == array(0)))
  }

  def insert (e : T) : ArrayHeap[T] = {
    require(inv)
    ArrayHeap(AHeap.insert(array, c, e), c)
  } ensuring { res =>
    res.size == array.size + 1 && res.inv && res.c == c && (
      if (res.size == 1) res.findMin.get == e
      else if (c(e, findMin.get) <= 0) res.findMin.get == e
      else res.findMin.get == findMin.get
    ) && permutation(res.toList, toList :+ e)
  }

  def isEmpty : Boolean = {
    require(inv)
    array.size == 0
  }

  def merge (h : ArrayHeap[T]) : ArrayHeap[T] = {
    require(inv && h.inv && c == h.c)
    ArrayHeap(AHeap.merge(array, h.array, c), c)
  } ensuring { res =>
    res.size == size + h.size && res.inv && res.c == c &&
    permutation(res.toList, toList ++ h.toList)
  }

  def size : BigInt = {
    require(inv)
    array.size
  }

  def toList : List[T] = {
    require(inv)
    array.toList
  }

  def inv : Boolean = {
    AHeap.valid(array, c)
  }

}

object BigIntArrayHeap {

  def compare : (BigInt, BigInt) => Int = (x : BigInt, y : BigInt) => {
    if (x == y) 0
    else if (x < y) -1
    else 1
  }

  /*
   * This lemma needs the leon option "--assumepre" to be verified.
   * Otherwise, the inductive call to well_ordered_smaller_than_all will fail
   * even the preconditions for the inductive call hold.
   */
  def well_ordered_smaller_than_all (m : MapArray[BigInt], from : BigInt, until : BigInt) : Boolean = {
    require(m.inv && AHeap.well_ordered(m, compare) && m.size > 0 && from >= m.from && from <= m.until && until >= m.from && until <= m.until &&
      IMap.defined_between_shrink(m.map, m.from, m.until, from, until))
    IMap.toList(m.map, from, until).forall(compare(m(0), _) <= 0) because {
      if (from >= until) trivial
      else {
        AHeap.is_descendant_of_zero(from - m.from) &&
        AHeap.well_ordered_at(m, compare, 0, from - m.from) &&
        well_ordered_smaller_than_all(m, from + 1, until)
      }
    }
  } holds

  /* This lemma needs the leon option "--assumepre" to be verified. */
  def well_ordered_smaller_than_all (m : MapArray[BigInt]) : Boolean = {
    require(m.inv && AHeap.well_ordered(m, compare) && m.size > 0)
    m.toList.forall(compare(m(0), _) <= 0) because { well_ordered_smaller_than_all(m, m.from, m.until) }
  } holds

  def findMin_toList_min (h : ArrayHeap[BigInt]) : Boolean = {
    require(h.inv && !h.isEmpty && h.c == compare)
    h.findMin.get == min(h.toList) because {
      well_ordered_smaller_than_all(h.array) && is_min(h.toList, h.findMin.get)
    }
  } holds

}

object ArrayHeapListHeapBisim {

  def bisim (ah : ArrayHeap[BigInt], lh : ListHeap) : Boolean = {
    ah.inv && ah.c == BigIntArrayHeap.compare && permutation(ah.toList, lh.toList)
  }

  /*
   * This lemma needs the leon option "--assumepre" to be verified.
   * Otherwise, the lemma BigIntArrayHeap.findMin_toList_min(ah) cannot be applied.
   */
  def findMin_bisim (ah : ArrayHeap[BigInt], lh : ListHeap) : Boolean = {
    require(bisim(ah, lh))
    ah.findMin == lh.findMin because {
      if (ah.isEmpty) trivial
      else {
        BigIntArrayHeap.findMin_toList_min(ah) &&
        min_permutation(ah.toList, lh.toList)
      }
    }
  } holds

  def deleteMin_bisim (ah : ArrayHeap[BigInt], lh : ListHeap) : Boolean = {
    require(bisim(ah, lh))
    bisim(ah.deleteMin, lh.deleteMin) because {
      if (ah.isEmpty) trivial
      else {
        findMin_bisim(ah, lh) &&
        permutation_delete(ah.toList, lh.toList, ah.findMin.get) &&
        permutation_tran(ah.deleteMin.toList, delete(ah.toList, ah.findMin.get), lh.deleteMin.toList)
      }
    }
  } holds 

  def insert_bisim (ah : ArrayHeap[BigInt], lh : ListHeap, e : BigInt) : Boolean = {
    require(bisim(ah, lh))
    bisim(ah.insert(e), lh.insert(e)) because {
      cons_snoc_perm(ah.toList, e) &&
      permutation_comm(e :: ah.toList, ah.toList :+ e) &&
      permutation_tran(ah.insert(e).toList, ah.toList :+ e, e :: ah.toList) &&
      permutation_cons(ah.toList, lh.toList, e) &&
      permutation_tran(ah.insert(e).toList, e :: ah.toList, e :: lh.toList)
    }
  } holds

  def merge_bisim (ah1 : ArrayHeap[BigInt], ah2 : ArrayHeap[BigInt], lh1 : ListHeap, lh2 : ListHeap, e : BigInt) : Boolean = {
    require(bisim(ah1, lh1) && bisim(ah2, lh2))
    bisim(ah1.merge(ah2), lh1.merge(lh2)) because {
      permutation_concat(ah1.toList, ah2.toList, lh1.toList, lh2.toList) &&
      permutation_tran(ah1.merge(ah2).toList, ah1.toList ++ ah2.toList, lh1.merge(lh2).toList)
    }
  } holds

  def size_bisim (ah : ArrayHeap[BigInt], lh : ListHeap, e : BigInt) : Boolean = {
    require(bisim(ah, lh))
    ah.size == lh.size
  } holds

}
