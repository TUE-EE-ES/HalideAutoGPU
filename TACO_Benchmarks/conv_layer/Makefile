include ../support/Makefile.inc
include ../support/autoscheduler.inc
BIN ?= bin
#HL_TARGET =host-cuda-cuda_capability_35

all: $(BIN)/test

$(BIN)/conv_layer.generator: conv_layer_generator.cpp  ../autoscheduler/AutoSchedule.cpp ../autoscheduler/AutoSchedule.h $(GENERATOR_DEPS)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -g $(filter-out %.h,$^) -o $@ $(LDFLAGS) $(HALIDE_SYSTEM_LIBS) $(USE_EXPORT_DYNAMIC)

$(BIN)/conv_layer.a: $(BIN)/conv_layer.generator
	@mkdir -p $(@D)
	$^ -g conv_layer -o $(BIN) -f conv_layer target=$(HL_TARGET) auto_schedule=false

$(BIN)/conv_layer_auto_schedule.a: $(BIN)/conv_layer.generator  $(AUTOSCHED_BIN)/libauto_schedule.so
	@mkdir -p $(@D)
	$< -g conv_layer -o $(BIN) -f conv_layer_auto_schedule target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule



$(BIN)/conv_layer_auto_schedule_store.a: $(BIN)/conv_layer.generator $(AUTOSCHED_BIN)/libauto_schedule.so 
	@mkdir -p $(@D)
	HL_AUTO_FOLDED_FUSION=1 \
	$< -g conv_layer -o $(BIN) -f conv_layer_auto_schedule_store target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule			    

$(BIN)/conv_layer_auto_schedule_no_fus.a: $(BIN)/conv_layer.generator $(AUTOSCHED_BIN)/libauto_schedule.so 
	@mkdir -p $(@D)
	HL_GPU_NO_FUS=1 \
	$< -g conv_layer -o $(BIN) -f conv_layer_auto_schedule_no_fus target=$(HL_TARGET) auto_schedule=true -p $(AUTOSCHED_BIN)/libauto_schedule.so -e static_library,h,schedule			    


$(BIN)/process: process.cpp $(BIN)/conv_layer.a $(BIN)/conv_layer_auto_schedule.a $(BIN)/conv_layer_auto_schedule_store.a $(BIN)/conv_layer_auto_schedule_no_fus.a
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -I$(BIN) -Wall -O3 $^ -o $@ $(LDFLAGS)

run: $(BIN)/process
	@mkdir -p $(@D)
	$(BIN)/process

clean:
	rm -rf $(BIN)

test: run
