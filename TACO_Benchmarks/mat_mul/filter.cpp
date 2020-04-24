#include <cstdio>

#include "mat_mul.h"
#include "mat_mul_auto_schedule_store.h"
#include "mat_mul_auto_schedule.h"
#include "mat_mul_simple_auto_schedule.h"
#include "mat_mul_auto_schedule_no_fus.h"
#include "benchmark_util.h"
#include "HalideBuffer.h"

int main(int argc, char **argv) {
    if (argc != 1) {
        printf("Usage: %s\n", argv[0]);
        return 1;
    }

    const int matrix_size = 1536;

    Halide::Runtime::Buffer<float> mat_A(matrix_size, matrix_size);
    Halide::Runtime::Buffer<float> mat_B(matrix_size, matrix_size);
    Halide::Runtime::Buffer<float> output(matrix_size, matrix_size);

    // init randomly
    for (int iy = 0; iy < matrix_size; iy++) {
        for (int ix = 0; ix < matrix_size; ix++) {
            mat_A(ix, iy) = (rand() % 256) / 256.0f;
            mat_B(ix, iy) = (rand() % 256) / 256.0f;
        }
    }
  #ifdef cuda_alloc
    halide_reuse_device_allocations(nullptr,true);
   #endif
mat_mul(mat_A,mat_B,output);
    multi_way_bench({
        {"Manual", [&]() { mat_mul(mat_A, mat_B, output); output.device_sync(); }},
        {"Nested auto-schedule", [&]() { mat_mul_auto_schedule_store(mat_A, mat_B, output); output.device_sync(); }},
             {"No-fusion auto-schedule", [&]() { mat_mul_auto_schedule_no_fus(mat_A, mat_B, output); output.device_sync(); }},
 
     	{"Auto-schedule", [&]() { mat_mul_auto_schedule(mat_A, mat_B, output); output.device_sync(); }},
        {"Simple auto-schedule", [&]() { mat_mul_simple_auto_schedule(mat_A, mat_B, output); output.device_sync(); }}
        });

    return 0;
}
