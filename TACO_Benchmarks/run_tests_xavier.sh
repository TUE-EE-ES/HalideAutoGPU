#!/bin/bash
rm -f results_xavier.txt

touch results_xavier.txt
export HL_GPU_DEVICE=0
export HL_PERMIT_FAILED_UNROLL=1
export CXXFLAGS+=-Dcuda_alloc
export HL_GPU_L2_COST=200
export HL_GPU_SHARED_COST=1
export HL_GPU_GLOBAL_COST=160
export HL_TARGET=host-cuda-cuda_capability_61
echo "BILATERAL"
echo "bilateral_grid:" >> results_xavier.txt
cd bilateral_grid
make clean
make  test | tail -3  >> ../results_xavier.txt
cd ..

echo "CAMERA"
echo "camera_pipe:" >> results_xavier.txt
cd camera_pipe
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "HARRIS"
echo "harris:" >> results_xavier.txt
cd harris
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "hist"
echo "hist:" >> results_xavier.txt
cd hist
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "iir"
echo "IIR:" >> results_xavier.txt
cd iir_blur_generator
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "INTERPOLATE"
echo "interpolate:" >> results_xavier.txt
cd interpolate_generator
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "LAPLACIAN"
echo "local_laplacian:" >> results_xavier.txt
cd local_laplacian
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "MAXFILTER"
echo "max_filter:" >> results_xavier.txt
cd max_filter
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "UNSHARP"
echo "unsharp:" >> results_xavier.txt
cd unsharp
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "NLMEANS"
echo "nlmeans:" >> results_xavier.txt
cd nl_means
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "stencil"
echo "stencil:" >> results_xavier.txt
cd stencil_chain
make clean
make test | tail -3  >> ../results_xavier.txt
cd ..

echo "matmul"
echo "matmul:" >> results_xavier.txt
cd mat_mul
make clean
make test | tail -3 >> ../results_xavier.txt
cd ..

echo "CONV"
echo "conv_layer:" >> results_xavier.txt
cd conv_layer
make clean
make test | tail -2  >> ../results_xavier.txt
cd ..

echo "LENSBLUR"
echo "lens_blur:" >> results_xavier.txt
cd lens_blur
make clean
make test | tail -2 >> ../results_xavier.txt
cd ..
#echo "VDSR"
#echo "VDSR:" >> results_xavier.txt
#cd VDSR
#make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test #| tail -2  >> ../results_xavier.txt
#cd ..

#echo "resnet50"
#echo "resnet50:" >> results_xavier.txt
#cd resnet_50
#make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test #| tail -2  >> ../results_xavier.txt
#cd ..

