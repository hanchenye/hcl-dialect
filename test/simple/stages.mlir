module {
    func @matrix_multiply(%A: memref<?x?xf32>, %B: memref<?x?xf32>, %C: memref<?x?xf32>) -> memref<?x?xf32>
    {
        %l1 = hcl.create_loop_handle : !hcl.LoopHandle<"i">
        %l2 = hcl.create_loop_handle : !hcl.LoopHandle<"j">
        %l3 = hcl.create_loop_handle : !hcl.LoopHandle<"k">
        %l11 = hcl.create_loop_handle : !hcl.LoopHandle<"i1">
        %l21 = hcl.create_loop_handle : !hcl.LoopHandle<"j1">
        %l31 = hcl.create_loop_handle : !hcl.LoopHandle<"k1">
        affine.for %i = 0 to 1024 {
            affine.for %j = 0 to 1024 {
                affine.for %k = 0 to 1024 {
                    %a = affine.load %A[%i, %k] : memref<?x?xf32>
                    %b = affine.load %B[%k, %j] : memref<?x?xf32>
                    %c = affine.load %C[%i, %j] : memref<?x?xf32>
                    %prod = mulf %a, %b : f32
                    %sum = addf %prod, %c: f32
                    affine.store %sum, %C[%i, %j] : memref<?x?xf32>
                } { loop_name = "k" }
            } { loop_name = "j" }
        } { loop_name = "i" }
        affine.for %i = 0 to 1024 {
            affine.for %j = 0 to 1024 {
                affine.for %k = 0 to 1024 {
                    %a = affine.load %A[%i, %k] : memref<?x?xf32>
                    %b = affine.load %B[%k, %j] : memref<?x?xf32>
                    %c = affine.load %C[%i, %j] : memref<?x?xf32>
                    %prod = mulf %a, %b : f32
                    %sum = addf %prod, %c: f32
                    affine.store %sum, %C[%i, %j] : memref<?x?xf32>
                } { loop_name = "k1" }
            } { loop_name = "j1" }
        } { loop_name = "i1" }
        hcl.reorder (%l3, %l2: !hcl.LoopHandle<"k">, !hcl.LoopHandle<"j">)
        hcl.reorder (%l31, %l21, %l11: !hcl.LoopHandle<"k1">, !hcl.LoopHandle<"j1">, !hcl.LoopHandle<"i1">)
        return %C : memref<?x?xf32>
    }
}