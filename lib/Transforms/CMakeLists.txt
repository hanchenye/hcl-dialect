add_mlir_library(MLIRHCLPasses
    LoopTransformations.cpp
    FixedPointToInteger.cpp
    AnyWidthInteger.cpp
    MoveReturnToInput.cpp
    LowerCompositeType.cpp
    LowerBitOps.cpp
    Passes.cpp
    LegalizeCast.cpp
    RemoveStrideMap.cpp

    ADDITIONAL_HEADER_DIRS
    ${PROJECT_SOURCE_DIR}/include/hcl

    DEPENDS
    MLIRHeteroCLOpsIncGen
    MLIRHeteroCLTypesIncGen
    MLIRHeteroCLPassesIncGen

    LINK_COMPONENTS
    Core

    LINK_LIBS PUBLIC
    MLIRIR
    MLIRPass
    MLIRHeteroCL
    MLIRHCLSupport
)