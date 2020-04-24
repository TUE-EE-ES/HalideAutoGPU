#!/bin/bash
rm -f results_4ti.txt

touch results_4ti.txt
export HL_GPU_DEVICE=0
export HL_PERMIT_FAILED_UNROLL=1
export CXXFLAGS=
export CXXFLAGS+=-Dcuda_alloc
export HL_GPU_L2_COST=200
export HL_GPU_SHARED_COST=1
export HL_GPU_GLOBAL_COST=1
export HL_CUDA_JIT_MAX_REGISTERS=256
export HL_TARGET=host-cuda-cuda_capability_61
echo "BILATERAL"
echo "bilateral_grid:" >> results_4ti.txt
cd bilateral_grid
make clean
make  test | tail -5  >> ../results_4ti.txt
cd ..

echo "CAMERA"
echo "camera_pipe:" >> results_4ti.txt
cd camera_pipe
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "HARRIS"
echo "harris:" >> results_4ti.txt
cd harris
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "hist"
echo "hist:" >> results_4ti.txt
cd hist
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "iir"
echo "IIR:" >> results_4ti.txt
cd iir_blur_generator
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "INTERPOLATE"
echo "interpolate:" >> results_4ti.txt
cd interpolate_generator
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "LAPLACIAN"
echo "local_laplacian:" >> results_4ti.txt
cd local_laplacian
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "MAXFILTER"
echo "max_filter:" >> results_4ti.txt
cd max_filter
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "UNSHARP"
echo "unsharp:" >> results_4ti.txt
cd unsharp
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "NLMEANS"
echo "nlmeans:" >> results_4ti.txt
cd nl_means
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "stencil"
echo "stencil:" >> results_4ti.txt
cd stencil_chain
make clean
make test | tail -5  >> ../results_4ti.txt
cd ..

echo "matmul"
echo "matmul:" >> results_4ti.txt
cd mat_mul
make clean
make test | tail -5 >> ../results_4ti.txt
cd ..

echo "CONV"
echo "conv_layer:" >> results_4ti.txt
cd conv_layer
make clean
make test | tail -4  >> ../results_4ti.txt
cd ..

echo "LENSBLUR"
echo "lens_blur:" >> results_4ti.txt
cd lens_blur
make clean
make test | tail -4 >> ../results_4ti.txt
cd ..
#echo "VDSR"
#echo "VDSR:" >> results_4ti.txt
#cd VDSR
#make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test #| tail -2  >> ../results_4ti.txt
#cd ..

#echo "resnet50"
#echo "resnet50:" >> results_4ti.txt
#cd resnet_50
#make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test #| tail -2  >> ../results_4ti.txt
#cd ..
