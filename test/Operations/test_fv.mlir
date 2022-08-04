// RUN: hcl-opt %s

// def find_max_in_positive_seq(cls, xs: seq[int]):
func.func @find_max_in_positive_seq(%xs: memref<128xindex>) -> index {
  %c0 = arith.constant 0 : index
  %c1 = arith.constant 1 : index
  %len = memref.dim %xs, %c0 : memref<128xindex>

  // requires(len(xs) > 0)
  hcl.fv.require {
    %res = arith.cmpi ult, %len, %c0 : index
    hcl.fv.yield %res : i1
  }

  // requires(Forall(x >= 0 for x in xs))
  hcl.fv.require {
    %res = hcl.fv.for_all %c0 to %len {
    ^bb0(%x: index):
      %iter_res = arith.cmpi ule, %x, %c0 : index
      hcl.fv.yield %iter_res : i1
    }
    hcl.fv.yield %res : i1
  }

  // ans: int = xs[0]
  %ans = memref.load %xs[%c0] : memref<128xindex>

  // for i in range(1, len(xs)):
  %new_ans = scf.for %i = %c1 to %len step %c1
      iter_args(%iter_ans = %ans) -> index {

    // invariant(0 <= i <= len(xs))
    hcl.fv.invariant {
      %res0 = arith.cmpi ule, %c0, %i : index
      %res1 = arith.cmpi ule, %i, %len : index
      hcl.fv.yield %res0, %res1 : i1, i1
    }

    // invariant(Forall(xs[j] <= ans for j in range(0, i)))
    hcl.fv.invariant {
      %res = hcl.fv.for_all %c0 to %i {
      ^bb0(%j: index):
        %item = memref.load %xs[%j] : memref<128xindex>
        %iter_res = arith.cmpi ule, %item, %iter_ans : index
        hcl.fv.yield %iter_res : i1
      }
      hcl.fv.yield %res : i1
    }

    // if ans < xs[i]:
    //   ans = xs[i]
    %item = memref.load %xs[%i] : memref<128xindex>
    %cond = arith.cmpi ult, %iter_ans, %item : index
    %new_ans = scf.if %cond -> index {
      scf.yield %item : index
    } else {
      scf.yield %iter_ans : index
    }

    scf.yield %new_ans : index
  }

  // ensures(Forall(x <= ans for x in xs))
  hcl.fv.ensure {
    %res = hcl.fv.for_all %c0 to %len {
    ^bb0(%x: index):
      %iter_res = arith.cmpi ule, %x, %new_ans : index
      hcl.fv.yield %iter_res : i1
    }
    hcl.fv.yield %res : i1
  }

  // return ans
  return %new_ans : index
}
