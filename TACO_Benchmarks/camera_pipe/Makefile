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
#	HL_PERMIT_FAILED_UNROLL=1 \
#	HL_WEIGHTS_DIR=$(AUTOSCHED_SRC)/gpu_weights \
#	HL_DEBUG_CODEGEN=1 \
#	HL_SHARED_MEMORY_LIMIT=48 
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



$(BIN)/viz/camera_pipe.a: $(BIN)/camera_pipe.generator
	@mkdir -p $(@D)
	$^ -g camera_pipe -o $(BIN)/viz target=$(HL_TARGET)-trace_all

$(BIN)/process: process.cpp $(BIN)/camera_pipe.a  $(BIN)/camera_pipe_auto_schedule.a $(BIN)/camera_pipe_simple_auto_schedule.a $(BIN)/camera_pipe_auto_schedule_store.a $(BIN)/camera_pipe_auto_schedule_no_fus.a
	$(CXX) $(CXXFLAGS) -Wall -O3 -I$(BIN) $^ -o $@ $(IMAGE_IO_FLAGS) $(LDFLAGS)

$(BIN)/viz/process: process.cpp $(BIN)/viz/camera_pipe.a
	$(CXX) $(CXXFLAGS) -DNO_AUTO_SCHEDULE -Wall -O3 -I$(BIN)/viz $^ -o $@ $(IMAGE_IO_FLAGS) $(LDFLAGS)

$(BIN)/out.png: $(BIN)/process
	$(BIN)/process $(IMAGES)/bayer_raw.png 3700 2.0 50 1.0 $(TIMING_ITERATIONS) $@ $(BIN)/h_auto.png

../../bin/HalideTraceViz: ../../util/HalideTraceViz.cpp
	$(MAKE) -C ../../ bin/HalideTraceViz

$(BIN)/camera_pipe.mp4: $(BIN)/viz/process viz.sh $(HALIDE_TRACE_VIZ) ../../bin/HalideTraceViz
	HL_AVCONV=$(HL_AVCONV) bash viz.sh $(BIN)

clean:
	rm -rf $(BIN)

test: $(BIN)/out.png

viz: $(BIN)/camera_pipe.mp4
	$(HL_VIDEOPLAYER) $^

$(BIN)/viz_auto.mp4: $(BIN)/viz/process ../support/viz_auto.sh ../../bin/HalideTraceViz
	@mkdir -p $(@D)
	HL_AVCONV=$(HL_AVCONV) bash ../support/viz_auto.sh "$(BIN)/viz/process $(IMAGES)/bayer_small.png 3700 1.8 50 1 1 $(BIN)/out.png" ../../bin/HalideTraceViz $@

viz_auto: $(BIN)/viz_auto.mp4
	$(HL_VIDEOPLAYER) $^

autotune:  $(BIN)/camera_pipe.generator  $(BIN)/camera_pipe_auto_schedule.a  $(AUTOSCHED_BIN)/libauto_schedule.so 
	$(BIN)/camera_pipe.generator -g camera_pipe -f camera_pipe_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so

