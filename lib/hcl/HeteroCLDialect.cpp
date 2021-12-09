//===- HeteroCLDialect.cpp - hcl dialect ---------------*- C++ -*-===//
//
// This file is licensed under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "hcl/HeteroCLDialect.h"
#include "hcl/HeteroCLOps.h"

using namespace mlir;
using namespace mlir::hcl;

#include "hcl/HeteroCLOpsDialect.cpp.inc"

//===----------------------------------------------------------------------===//
// hcl dialect.
//===----------------------------------------------------------------------===//

void HeteroCLDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "hcl/HeteroCLOps.cpp.inc"
      >();
}
