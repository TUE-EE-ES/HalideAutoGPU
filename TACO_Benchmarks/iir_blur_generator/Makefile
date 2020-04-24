include ../support/Makefile.inc
include ../support/autoscheduler.inc
#HL_TARGET=host-cuda-cuda_capability_35
BIN ?= bin

$(BIN)/iir_blur.generator: iir_blur_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/iir_blur.a: $(BIN)/iir_blur.generator
	@mkdir -p $(@D)
	$< -g iir_blur -f iir_blur -o $(BIN) target=$(HL_TARGET) auto_schedule=false

$(BIN)/iir_blur_auto_schedule.a: $(BIN)/iir_blur.generator  $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g iir_blur -f iir_blur_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so

$(BIN)/iir_blur_simple_auto_schedule.a: $(BIN)/iir_blur.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g iir_blur -o $(BIN) -f iir_blur_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h,html

$(BIN)/iir_blur_auto_schedule_store.a: $(BIN)/iir_blur.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g iir_blur -o $(BIN) -f iir_blur_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 

$(BIN)/iir_blur_auto_schedule_no_fus.a: $(BIN)/iir_blur.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g iir_blur -o $(BIN) -f iir_blur_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 




$(BIN)/process: process.cpp $(BIN)/iir_blur.a $(BIN)/iir_blur_auto_schedule.a  $(BIN)/iir_blur_simple_auto_schedule.a $(BIN)/iir_blur_auto_schedule_store.a $(BIN)/iir_blur_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

clean:
	rm -rf $(BIN)

test: $(BIN)/process
	$(BIN)/process

autotune: $(BIN)/iir_blur.generator $(AUTOSCHED_BIN)/augment_sample $(AUTOSCHED_BIN)/train_cost_model $(AUTOSCHED_BIN)/libauto_schedule.so $(AUTOSCHED_SRC)/autotune_loop.sh
	HL_PERMIT_FAILED_UNROLL=1 \
	HL_WEIGHTS_DIR=$(AUTOSCHED_SRC)/gpu_weights \
	HL_DEBUG_CODEGEN=1 \
	HL_SHARED_MEMORY_LIMIT=48 \
	bash $(AUTOSCHED_SRC)/autotune_loop.sh \
		$(BIN)/iir_blur.generator \
		iir_blur \
		$(HL_TARGET) \
		$(AUTOSCHED_SRC)/gpu_weights \
		$(AUTOSCHED_BIN)
