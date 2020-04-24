#!/bin/bash
rm -f results_ti.txt

touch results_ti.txt
export HL_GPU_DEVICE=0
echo "BILATERAL"
echo "bilateral_grid:" >> results_ti.txt
cd bilateral_grid
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | grep -e "Auto" -e "Manual"  >> ../results_ti.txt
cd ..

echo "CAMERA"
echo "camera pipe:" >> results_ti.txt
cd camera_pipe
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "CONV"
echo "conv layer:" >> results_ti.txt
cd conv_layer
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "HARRIS"
echo "harris:" >> results_ti.txt
cd harris
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "hist"
echo "hist:" >> results_ti.txt
cd hist
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

#echo "iir"
#echo "IIR:" >> results_ti.txt
#cd iir
#make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
#cd ..

echo "INTERPOLATE"
echo "interpolate:" >> results_ti.txt
cd interpolate_generator
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

cd nl_means
rm -rf *.png
make clean
cd ..

cd mat_mul
rm -rf *.png
make clean
cd ..

echo "LENSBLUR"
echo "lens blur:" >> results_ti.txt
cd lens_blur
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "LAPLACIAN"
echo "local laplacian:" >> results_ti.txt
cd local_laplacian
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "MAXFILTER"
echo "max filter:" >> results_ti.txt
cd max_filter
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

echo "UNSHARP"
echo "unsharp:" >> results_ti.txt
cd unsharp
rm -rf *.png
make clean
#make HL_TARGET=host-cuda-cuda_capability_35 test | tail -2  >> ../results_ti.txt
cd ..

cd iir_blur_generator
rm -rf *.png
make clean
cd ..

