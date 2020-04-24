#!/bin/bash
export CXXFLAGS='-Dcuda_alloc -Dautotune'
export HL_PERMIT_FAILED_UNROLL=1;
export HL_TARGET=host-cuda-cuda_capability_61
declare -i shared_cost
declare -i inl_cost
declare -i l2_cost
shared_cost=8
inl_cost=32
l2_cost=8
export HL_GPU_GLOBAL_COST=$inl_cost
for i in {0..1}
do
  shared_cost=8
  export HL_GPU_L2_cost=$l2_cost
  for i in {0..1}
 do
     export HL_GPU_SHARED_COST=$shared_cost
     echo "global cost $HL_GPU_GLOBAL_COST"
     echo  "l2 cost $HL_GPU_L2_cost"
     echo "shared cost $HL_GPU_SHARED_COST"
     make autotune
     make test
     shared_cost=$((shared_cost*2))
     done
  l2_cost=$((l2_cost*2))
done

  
  
  