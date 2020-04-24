#include <cstdio>
#include <cstdlib>
#include <cassert>

#include "HalideRuntime.h"
#include "HalideBuffer.h"

#include "harris.h"
#include "harris_auto_schedule_store.h"
#include "harris_auto_schedule.h"
#include "harris_simple_auto_schedule.h"
#include "harris_auto_schedule_no_fus.h"
#include "benchmark_util.h"
#include "halide_image_io.h"

using namespace Halide::Tools;

int main(int argc, char **argv) {
    if (argc != 3) {
        printf("Usage: %s in out\n", argv[0]);
        return 1;
    }

    Halide::Runtime::Buffer<float> input = load_and_convert_image(argv[1]);
 //   Halide::Runtime::Buffer<float> input(2048,2048,3);
/*    for(int c=0;c<3;c++){
    for(int i=0;i<2048;i++){
	for(int j=0;j<2048;j++){
	input(i,j,c)=rand();
	}
    }	
    }*/
    Halide::Runtime::Buffer<float> output(input.width() - 6, input.height() - 6);
    input.set_host_dirty();
  //  output.set_host_dirty();
#ifdef cuda_alloc
 //   cout<<"assdasdasdasd AAAALLOCA"<<endl;
    halide_reuse_device_allocations(nullptr,true);
    harris(input,output);
    output.device_sync();
  #endif
    multi_way_bench({
    #ifndef autotune
        {"Manual", [&]() { harris(input, output); output.device_sync(); }},
         {"Simple auto-scheduled", [&]() { harris_simple_auto_schedule(input, output); output.device_sync(); }},
    #endif
	{"No-fusion auto-scheduled",[&]() {harris_auto_schedule_no_fus(input,output);output.device_sync();}},
       {"Nested auto-scheduled", [&]() { harris_auto_schedule_store(input, output); output.device_sync(); }},
       {"Auto-scheduled", [&]() { harris_auto_schedule(input, output); output.device_sync(); }}
    
    });
    output.copy_to_host();
    convert_and_save_image(output, argv[2]);

    return 0;
}
