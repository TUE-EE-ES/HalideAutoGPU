AUTOSCHED_SRC ?= ../autoscheduler
AUTOSCHED_BIN ?= $(AUTOSCHED_SRC)/bin

$(AUTOSCHED_BIN)/binary2cpp: ../../tools/binary2cpp.cpp
	@mkdir -p $(@D)
	$(CXX) $< -o $@


# It's important to use dynamic lookups for undefined symbols here: all of libHalide
# is expected to be present (in the loading binary), so we explicitly make the symbols
# undefined rather than dependent on libHalide.so.
$(AUTOSCHED_BIN)/libauto_schedule.so: $(AUTOSCHED_SRC)/AutoSchedule.cpp 
	@mkdir -p $(@D)
	$(CXX) -shared $(USE_EXPORT_DYNAMIC) -fPIC $(CXXFLAGS) -g -I $(AUTOSCHED_SRC)/AutoSchedule.cpp  -O3 -o $@ $(HALIDE_SYSTEM_LIBS)

$(AUTOSCHED_BIN)/libauto_schedule_store.so: $(AUTOSCHED_SRC)/Auto_Store.cpp 
	@mkdir -p $(@D)
	$(CXX) -shared $(USE_EXPORT_DYNAMIC) -fPIC $(CXXFLAGS) -g -I $(AUTOSCHED_SRC)/Auto_Store.cpp  -O3 -o $@ $(HALIDE_SYSTEM_LIBS)






