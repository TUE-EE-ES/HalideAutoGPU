include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda

all: $(BIN)/test

$(BIN)/interpolate.generator: interpolate_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/interpolate.a: $(BIN)/interpolate.generator
	@mkdir -p $(@D)
	$< -g interpolate -f interpolate -o $(BIN) target=$(HL_TARGET) auto_schedule=false


$(BIN)/interpolate_auto_schedule.a: $(BIN)/interpolate.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g interpolate -f interpolate_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so

$(BIN)/interpolate_simple_auto_schedule.a: $(BIN)/interpolate.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g interpolate -o $(BIN) -f interpolate_simple_auto_schedule target=$(HL_TARGET) auto_schedule=false -e static_library,h

$(BIN)/interpolate_auto_schedule_store.a: $(BIN)/interpolate.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g interpolate -o $(BIN) -f interpolate_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 

$(BIN)/interpolate_auto_schedule_no_fus.a: $(BIN)/interpolate.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g interpolate -o $(BIN) -f interpolate_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 




$(BIN)/filter: filter.cpp  $(BIN)/interpolate_simple_auto_schedule.a $(BIN)/interpolate.a $(BIN)/interpolate_auto_schedule.a $(BIN)/interpolate_auto_schedule_store.a $(BIN)/interpolate_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

clean:
	rm -rf $(BIN)

test: $(BIN)/filter
	$(BIN)/filter ../images/rgba.png $(BIN)/out.png

