#include <cstdio>
#include <chrono>

#include "nl_means.h"
#include "nl_means_auto_schedule_store.h"
#include "nl_means_auto_schedule.h"
#include "nl_means_simple_auto_schedule.h"
#include "nl_means_auto_schedule_no_fus.h"
#include "benchmark_util.h"
#include "HalideBuffer.h"
#include "halide_image_io.h"

using namespace Halide::Runtime;
using namespace Halide::Tools;

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("Usage: ./process input.png patch_size search_area sigma timing_iterations output.png\n"
               "e.g.: ./process input.png 7 7 0.12 10 output.png\n");
        return 0;
    }

    Buffer<float> input = load_and_convert_image(argv[1]);
    int patch_size = atoi(argv[2]);
    int search_area = atoi(argv[3]);
    float sigma = atof(argv[4]);
    Buffer<float> output(input.width(), input.height(), 3);

    printf("Input size: %d by %d, patch size: %d, search area: %d, sigma: %f\n",
            input.width(), input.height(), patch_size, search_area, sigma);
 #ifdef cuda_alloc
    halide_reuse_device_allocations(nullptr,true);
#endif
    nl_means_simple_auto_schedule(input,patch_size,search_area,sigma,output);
    output.device_sync();
    multi_way_bench({
       {"Manual", [&]() { nl_means(input, patch_size, search_area, sigma, output); output.device_sync(); }},
       {"Nested Auto-scheduled", [&]() { nl_means_auto_schedule_store(input, patch_size, search_area, sigma, output); output.device_sync(); }},
       {"No-fusion auto-scheduled", [&]() { nl_means_auto_schedule_no_fus(input, patch_size, search_area, sigma, output); output.device_sync(); }},
 
 {"Auto-scheduled", [&]() { nl_means_auto_schedule(input, patch_size, search_area, sigma, output); output.device_sync(); }},
        {"Simple auto-scheduled", [&]() { nl_means_simple_auto_schedule(input, patch_size, search_area, sigma, output); output.device_sync(); }}
        }
    );

    convert_and_save_image(output, argv[6]);

    return 0;
}
