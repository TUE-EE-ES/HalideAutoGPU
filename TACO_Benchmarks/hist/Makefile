include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda

all: $(BIN)/test

$(BIN)/hist.generator: hist_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/hist.a: $(BIN)/hist.generator
	@mkdir -p $(@D)
	$< -g hist -f hist -o $(BIN) target=$(HL_TARGET) auto_schedule=false



$(BIN)/hist_auto_schedule.a: $(BIN)/hist.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g hist -f hist_auto_schedule -o $(BIN) target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so  2> stderr.txt > stdout.txt

$(BIN)/hist_simple_auto_schedule.a: $(BIN)/hist.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g hist -o $(BIN) -f hist_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h

$(BIN)/hist_auto_schedule_store.a: $(BIN)/hist.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g hist -o $(BIN) -f hist_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 

$(BIN)/hist_auto_schedule_no_fus.a: $(BIN)/hist.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
		      $<  -g hist -o $(BIN) -f hist_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/filter: filter.cpp $(BIN)/hist.a $(BIN)/hist_auto_schedule.a  $(BIN)/hist_simple_auto_schedule.a $(BIN)/hist_auto_schedule_store.a $(BIN)/hist_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS) $(IMAGE_IO_FLAGS) $(CUDA_LDFLAGS) $(OPENCL_LDFLAGS) $(OPENGL_LDFLAGS)

clean:
	rm -rf $(BIN)

test: $(BIN)/filter
	$(BIN)/filter ../images/rgb.png $(BIN)/out.png



