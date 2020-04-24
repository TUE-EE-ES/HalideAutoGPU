#!/bin/bash
export CXXFLAGS='-Dcuda_alloc -Dautotune'
export HL_PERMIT_FAILED_UNROLL=1;
export HL_TARGET=host-cuda-cuda_capability_61
declare -i shared_cost
declare -i inl_cost
declare -i l2_cost
shared_cost=8
inl_cost=32
l2_cost=8
best_cost_l2=l2_cost
best_cost_inl=inl_cost
best_cost_shared=shared_cost
export HL_GPU_GLOBAL_COST=$inl_cost
curr_time=0
best_time=1000
for i in {0..1}
do
  shared_cost=8
  export HL_GPU_L2_cost=$l2_cost
  for i in {0..1}
 do
     export HL_GPU_SHARED_COST=$shared_cost
     echo "global cost $HL_GPU_GLOBAL_COST"
     echo  "l2 cost $HL_GPU_L2_cost"
     echo "shared cost $HL_GPU_SHARED_COST"
     make autotune &> /dev/null
     curr_time=$(make test | sed -n -e 's/^\(.*\)\(Auto-scheduled time: \)\(.*\)\(ms\)$/\3/p')
     if (( $(echo "$curr_time < $best_time" |bc -l) )); then
     cd bin/
     cp *'.schedule' ../best_schedule.schedule
     cd ..
     best_time=$curr_time
     echo "new best time $best_time"
     fi
     echo "time $curr_time"
     #make HL_TARGET=host-cuda-cuda_capability_35 test | grep -e "Auto" -e "Manual"  >> ../results_ti.txt
     shared_cost=$((shared_cost*2))
     done
  l2_cost=$((l2_cost*2))
done

  
  
  