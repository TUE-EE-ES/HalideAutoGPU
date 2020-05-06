include ../support/Makefile.inc
include ../support/autoscheduler.inc

BIN ?= bin

#HL_TARGET=host-cuda-cuda_capability_35

all: $(BIN)/process

$(BIN)/nl_means.generator: nl_means_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/DerivativeUtils.h ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h  ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@-mkdir -p $(BIN)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/nl_means.a: $(BIN)/nl_means.generator
	@-mkdir -p $(BIN)
	$^ -g nl_means -o $(BIN) -f nl_means target=$(HL_TARGET) auto_schedule=false

$(BIN)/nl_means_auto_schedule.a: $(BIN)/nl_means.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@-mkdir -p $(BIN)
	$< -g nl_means -o $(BIN) -f nl_means_auto_schedule target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 

$(BIN)/nl_means_auto_schedule_store.a: $(BIN)/nl_means.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g nl_means -o $(BIN) -f nl_means_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 

$(BIN)/nl_means_auto_schedule_no_fus.a: $(BIN)/nl_means.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g nl_means -o $(BIN) -f nl_means_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/nl_means_simple_auto_schedule.a: $(BIN)/nl_means.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g nl_means -o $(BIN) -f nl_means_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h

$(BIN)/process: process.cpp $(BIN)/nl_means.a  $(BIN)/nl_means_auto_schedule.a $(BIN)/nl_means_auto_schedule_store.a $(BIN)/nl_means_simple_auto_schedule.a $(BIN)/nl_means_auto_schedule_no_fus.a
	@-mkdir -p $(BIN)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

$(BIN)/out.png: $(BIN)/process
	@-mkdir -p $(BIN)
	$(BIN)/process $(IMAGES)/rgb.png 7 7 0.12 10 $(BIN)/out.png




clean:
	rm -rf $(BIN)

test: $(BIN)/out.png


