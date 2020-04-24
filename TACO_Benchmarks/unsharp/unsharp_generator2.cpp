#include "Halide.h"
#include "../autoscheduler/SimpleAutoSchedule.h"

namespace {

class Unsharp : public Halide::Generator<Unsharp> {
public:
    GeneratorParam<float>   sigma_{"sigma", 1.5f};

    Input<Buffer<float>>    input_{"input", 3};
    Output<Buffer<float>>   output_{"output", 3};

    void generate() {
        Var x("x"), y("y"), c("c");

        const float sigma = sigma_;
        const float kPi = 3.14159265358979310000;

        Func kernel("kernel");
        kernel(x) = exp(-x*x/(2*sigma*sigma)) / (sqrtf(2*kPi)*sigma);

        Func input_bounded = Halide::BoundaryConditions::repeat_edge(input_);

        Func gray("gray");
        gray(x, y) = 0.299f * input_bounded(x, y, 0)
                     + 0.587f * input_bounded(x, y, 1)
                     + 0.114f * input_bounded(x, y, 2);

        Func blur_y("blur_y");
        blur_y(x, y) = (kernel(0) * gray(x, y) +
                        kernel(1) * (gray(x, y-1) +
                                     gray(x, y+1)) +
                        kernel(2) * (gray(x, y-2) +
                                     gray(x, y+2)) +
                        kernel(3) * (gray(x, y-3) +
                                     gray(x, y+3)));

        Func blur_x("blur_x");
        blur_x(x, y) = (kernel(0) * blur_y(x, y) +
                        kernel(1) * (blur_y(x-1, y) +
                                     blur_y(x+1, y)) +
                        kernel(2) * (blur_y(x-2, y) +
                                     blur_y(x+2, y)) +
                        kernel(3) * (blur_y(x-3, y) +
                                     blur_y(x+3, y)));

        Func sharpen("sharpen");
        sharpen(x, y) = 2 * gray(x, y) - blur_x(x, y);

        Func ratio("ratio");
        ratio(x, y) = sharpen(x, y) / gray(x, y);

        output_(x, y, c) = ratio(x, y) * input_(x, y, c);

        output_.bound(c, 0, 3);

        // Estimates (for autoscheduler; ignored otherwise)
        {
            input_.dim(0).set_bounds_estimate(0, 1536)
                  .dim(1).set_bounds_estimate(0, 2560)
                  .dim(2).set_bounds_estimate(0, 3);
            output_.dim(0).set_bounds_estimate(0, 1536)
                  .dim(1).set_bounds_estimate(0, 2560)
                  .dim(2).set_bounds_estimate(0, 3);
        }

        std::string use_simple_autoscheduler =
            Halide::Internal::get_env_variable("HL_USE_SIMPLE_AUTOSCHEDULER");

        // Schedule
        if (!auto_schedule) {
            if (use_simple_autoscheduler == "1") {
                    Halide::SimpleAutoscheduleOptions options;
                    options.gpu = get_target().has_gpu_feature();
                    options.gpu_tile_channel = 3;
                    Func output_func = output_;
                    Halide::simple_autoschedule(output_func,
                            {{"input.min.0", 0},
                             {"input.extent.0", 1536},
                             {"input.min.1", 0},
                             {"input.extent.1", 2560},
                             {"input.min.2", 0},
                             {"input.extent.2", 3}},
                            {{0, 1536},
                             {0, 2560},
                             {0, 3}},
                            options);
            } else if (get_target().has_gpu_feature()) {
                Var xi, yi;
                output_.compute_root()
                    .reorder(c, x, y)
                    .gpu_tile(x, y, xi, yi, 26, 10)
                    .unroll(c);
                ratio.compute_at(output_, xi);
                blur_y.compute_at(output_, x)
                    .gpu_threads(x, y);
                gray.compute_at(output_, x)
                    .gpu_threads(x, y);
            } else {
                blur_y.compute_at(output_, y).vectorize(x, 8);
                ratio.compute_at(output_, y).vectorize(x, 8);
                output_.vectorize(x, 8).parallel(y).reorder(x, c, y);
            }
        }
    }
};

}  // namespace

HALIDE_REGISTER_GENERATOR(Unsharp, unsharp)
