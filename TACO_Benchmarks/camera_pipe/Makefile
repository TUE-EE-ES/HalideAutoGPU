include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda-cuda_capability_35

all: $(BIN)/process

TIMING_ITERATIONS ?= 5

$(BIN)/camera_pipe.generator: camera_pipe_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/camera_pipe.a: $(BIN)/camera_pipe.generator
	@mkdir -p $(@D)
	$< -g camera_pipe -o $(BIN) -f camera_pipe target=$(HL_TARGET) auto_schedule=false -e static_library,h,assembly,stmt



$(BIN)/camera_pipe_auto_schedule.a: $(BIN)/camera_pipe.generator  $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g camera_pipe -o $(BIN) -f camera_pipe_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule

$(BIN)/camera_pipe_simple_auto_schedule.a: $(BIN)/camera_pipe.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g camera_pipe -o $(BIN) -f camera_pipe_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h

$(BIN)/camera_pipe_auto_schedule_store.a: $(BIN)/camera_pipe.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g camera_pipe -o $(BIN) -f camera_pipe_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 



$(BIN)/camera_pipe_auto_schedule_no_fus.a: $(BIN)/camera_pipe.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g camera_pipe -o $(BIN) -f camera_pipe_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/process: process.cpp $(BIN)/camera_pipe.a  $(BIN)/camera_pipe_auto_schedule.a $(BIN)/camera_pipe_simple_auto_schedule.a $(BIN)/camera_pipe_auto_schedule_store.a $(BIN)/camera_pipe_auto_schedule_no_fus.a
	$(CXX) $(CXXFLAGS) -Wall -O3 -I$(BIN) $^ -o $@ $(IMAGE_IO_FLAGS) $(LDFLAGS)


$(BIN)/out.png: $(BIN)/process
	$(BIN)/process $(IMAGES)/bayer_raw.png 3700 2.0 50 1.0 $(TIMING_ITERATIONS) $@ $(BIN)/h_auto.png


clean:
	rm -rf $(BIN)

test: $(BIN)/out.png
