include ../support/Makefile.inc
include ../support/autoscheduler.inc

#HL_TARGET=host-cuda

all: $(BIN)/filter

$(BIN)/bilateral_grid.generator: bilateral_grid_generator.cpp ../autoscheduler/SimpleAutoSchedule.h ../autoscheduler/SimpleAutoSchedule.cpp ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h ../autoscheduler/DerivativeUtils.h ../autoscheduler/DerivativeUtils.cpp $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(USE_EXPORT_DYNAMIC) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS)

$(BIN)/bilateral_grid.a: $(BIN)/bilateral_grid.generator
	@mkdir -p $(@D)
	$< -g bilateral_grid -o $(BIN) -f bilateral_grid target=$(HL_TARGET) auto_schedule=false


$(BIN)/bilateral_grid_auto_schedule.a: $(BIN)/bilateral_grid.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g bilateral_grid -o $(BIN) -f bilateral_grid_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so  -e static_library,h,schedule

$(BIN)/bilateral_grid_simple_auto_schedule.a: $(BIN)/bilateral_grid.generator
	@mkdir -p $(@D)
	HL_USE_SIMPLE_AUTOSCHEDULER=1 \
	$< -g bilateral_grid -o $(BIN) -f bilateral_grid_simple_auto_schedule target=$(HL_TARGET)-no_runtime auto_schedule=false -e static_library,h

$(BIN)/bilateral_grid_auto_schedule_store.a: $(BIN)/bilateral_grid.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$<  -g bilateral_grid -o $(BIN) -f bilateral_grid_auto_schedule_store target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 


$(BIN)/bilateral_grid_auto_schedule_no_fus.a: $(BIN)/bilateral_grid.generator $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$<  -g bilateral_grid -o $(BIN) -f bilateral_grid_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true  -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule 





$(BIN)/filter: filter.cpp $(BIN)/bilateral_grid.a  $(BIN)/bilateral_grid_auto_schedule.a $(BIN)/bilateral_grid_auto_schedule_store.a $(BIN)/bilateral_grid_simple_auto_schedule.a $(BIN)/bilateral_grid_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -O3 -ffast-math -Wall -Werror -I$(BIN) $^ -o $@ $(IMAGE_IO_FLAGS) $(LDFLAGS)




$(BIN)/out.png: $(BIN)/filter
	@mkdir -p $(@D)
	$(BIN)/filter $(IMAGES)/gray.png $(BIN)/out.png 0.1 10

$(BIN)/out.tiff: $(BIN)/filter
	@mkdir -p $(@D)
	$(BIN)/filter $(IMAGES)/gray.png $(BIN)/out.tiff 0.1 10

clean:
	rm -rf $(BIN)

test: $(BIN)/out.png 


