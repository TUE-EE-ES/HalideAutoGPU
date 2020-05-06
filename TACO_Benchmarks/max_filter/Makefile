include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda-cuda_capability_35

all: $(BIN)/test

$(BIN)/max_filter.generator: max_filter_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/max_filter.a: $(BIN)/max_filter.generator
	@mkdir -p $(@D)
	$< -g max_filter -f max_filter -o $(BIN) target=$(HL_TARGET) auto_schedule=false


$(BIN)/max_filter_auto_schedule.a: $(BIN)/max_filter.generator  $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g max_filter -f max_filter_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 2> stderr.txt > stdout.txt

$(BIN)/max_filter_simple_auto_schedule.a: $(BIN)/max_filter.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g max_filter -o $(BIN) -f max_filter_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h

$(BIN)/max_filter_auto_schedule_store.a: $(BIN)/max_filter.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g max_filter -o $(BIN) -f max_filter_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/max_filter_auto_schedule_no_fus.a: $(BIN)/max_filter.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g max_filter -o $(BIN) -f max_filter_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 



$(BIN)/filter: filter.cpp $(BIN)/max_filter.a $(BIN)/max_filter_auto_schedule.a $(BIN)/max_filter_simple_auto_schedule.a $(BIN)/max_filter_auto_schedule_store.a $(BIN)/max_filter_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

clean:
	rm -rf $(BIN)

test: $(BIN)/filter
	$(BIN)/filter ../images/rgb.png $(BIN)/out.tiff


