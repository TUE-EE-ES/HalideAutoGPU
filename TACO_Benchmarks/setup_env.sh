#!/bin/bash

export HL_GPU_DEVICE=0
export HL_PERMIT_FAILED_UNROLL=1
export CXXFLAGS=
export CXXFLAGS+=-Dcuda_alloc
export HL_GPU_L2_COST=200
export HL_GPU_SHARED_COST=1
export HL_GPU_GLOBAL_COST=1
export HL_CUDA_JIT_MAX_REGISTERS=256
export HL_TARGET=host-cuda-cuda_capability_61

