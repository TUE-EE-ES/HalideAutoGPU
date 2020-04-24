#include <cstdio>
#include <chrono>

#include "conv_layer.h"
#include "conv_layer_auto_schedule.h"
#include "conv_layer_auto_schedule_store.h"
#include "conv_layer_auto_schedule_no_fus.h"

//#include "halide_benchmark.h"
#include "benchmark_util.h"
#include "HalideBuffer.h"
#include "../../tutorial/clock.h"
using namespace Halide::Tools;
using namespace Halide::Runtime;
/*
  void test_performance(bool auto_sched,Buffer<float> input,Buffer<float> filter, Buffer<float> bias, Buffer<float> output) {
        // Test the performance of the scheduled MyPipeline.

        

        // Run the filter once to initialize any GPU runtime state.
        if(!auto_sched) conv_layer(input, filter, bias, output);
        else  conv_layer_auto_schedule(input, filter, bias, output);
        // Now take the best of 10 runs for timing.
        double best_time = 0.0;
        for (int i = 0; i < 10; i++) {

            double t1 = current_time();

            // Run the filter 100 times.
            if(!auto_sched){
            for (int j = 0; j < 100; j++) {
                conv_layer(input, filter, bias, output);
            }
            }
            else {
                        for (int j = 0; j < 100; j++) {
                conv_layer_auto_schedule(input, filter, bias, output);
            }
            }
            // Force any GPU code to finish by copying the buffer back to the CPU.
            output.copy_to_host();

            double t2 = current_time();

            double elapsed = (t2 - t1)/100;
            if (i == 0 || elapsed < best_time) {
                best_time = elapsed;
            }
        }

      if(!auto_sched)  printf("Manual: %1.4f ms\n", best_time);
      else  printf("Auto: %1.4f ms\n", best_time);
    }
*/
int main(int argc, char **argv) {
    Buffer<float> input(131, 131, 64, 4);
    Buffer<float> filter(3, 3, 64,64);
    Buffer<float> bias(64);

    for (int c = 0; c < input.dim(3).extent(); c++) {
        for (int z = 0; z < input.channels(); z++) {
            for (int y = 0; y < input.height(); y++) {
                for (int x = 0; x < input.width(); x++) {
                    input(x, y) = rand();
                }
            }
        }
    }

    for (int c = 0; c < filter.dim(3).extent(); c++) {
        for (int z = 0; z < filter.channels(); z++) {
            for (int y = 0; y < filter.height(); y++) {
                for (int x = 0; x < filter.width(); x++) {
                    filter(x, y) = rand();
                }
            }
        }
    }

    for (int x = 0; x < bias.width(); x++) {
        bias(x) = rand();
    }

    Buffer<float> output(128, 128, 64, 4);

   

    // Timing code

    // Manually-tuned version
  //  test_performance(false,input,filter,bias,output);
//test_performance(true,input,filter,bias,output);
//
#ifdef cuda_alloc
    halide_reuse_device_allocations(nullptr,true);
   #endif
    conv_layer_auto_schedule_store(input,filter,bias,output);
    output.device_sync();
    multi_way_bench({
        {"Manual", [&]() { conv_layer(input, filter, bias, output); output.device_sync(); }},
        {"Nested auto-scheduled", [&]() { conv_layer_auto_schedule_store(input,filter,bias, output); output.device_sync(); }},
              {"No-fusion auto-scheduled", [&]() { conv_layer_auto_schedule_no_fus(input,filter,bias, output); output.device_sync(); }},
 
      	{"Auto-scheduled", [&]() { conv_layer_auto_schedule(input, filter, bias, output); output.device_sync(); }},
   //     {"Simple auto-scheduled", [&]() { harris_simple_auto_schedule(input, output); output.device_sync(); }}
    });


    return 0;
}
