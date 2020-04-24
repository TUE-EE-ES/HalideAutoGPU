include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda-cuda_capability_35

all: $(BIN)/test

$(BIN)/mat_mul.generator: mat_mul_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/DerivativeUtils.h ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/mat_mul.a: $(BIN)/mat_mul.generator
	@mkdir -p $(@D)
	$< -g mat_mul -f mat_mul -o $(BIN) target=$(HL_TARGET) auto_schedule=false

$(BIN)/mat_mul_auto_schedule.a: $(BIN)/mat_mul.generator  $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g mat_mul -f mat_mul_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule

$(BIN)/mat_mul_simple_auto_schedule.a: $(BIN)/mat_mul.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g mat_mul -o $(BIN) -f mat_mul_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h,html

$(BIN)/mat_mul_auto_schedule_store.a: $(BIN)/mat_mul.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g mat_mul -o $(BIN) -f mat_mul_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/mat_mul_auto_schedule_no_fus.a: $(BIN)/mat_mul.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g mat_mul -o $(BIN) -f mat_mul_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 



$(BIN)/filter: filter.cpp $(BIN)/mat_mul.a $(BIN)/mat_mul_auto_schedule.a $(BIN)/mat_mul_simple_auto_schedule.a $(BIN)/mat_mul_auto_schedule_store.a $(BIN)/mat_mul_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

clean:
	rm -rf $(BIN)

test: $(BIN)/filter
	$(BIN)/filter

autotune: $(BIN)/mat_mul.generator $(AUTOSCHED_BIN)/augment_sample $(AUTOSCHED_BIN)/train_cost_model $(AUTOSCHED_BIN)/libauto_schedule.so $(AUTOSCHED_SRC)/autotune_loop.sh
	HL_PERMIT_FAILED_UNROLL=1 \
	HL_WEIGHTS_DIR=$(AUTOSCHED_SRC)/gpu_weights \
	HL_DEBUG_CODEGEN=1 \
	HL_SHARED_MEMORY_LIMIT=48 \
	bash $(AUTOSCHED_SRC)/autotune_loop.sh \
		$(BIN)/mat_mul.generator \
		mat_mul \
		$(HL_TARGET) \
		$(AUTOSCHED_SRC)/gpu_weights \
		$(AUTOSCHED_BIN)
