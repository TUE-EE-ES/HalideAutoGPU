"""
========
Barchart
========

A bar plot with errorbars and height labels on individual bars
"""
import numpy as np
import sys as sys
gld_trans=0
gst_trans=0
atomic_trans=0
local_load_trans=0
local_store_trans=0
shared_load_trans=0
shared_store_trans=0
l2_read=0
l2_write=0
dram_read=0
dram_write=0
sys_read=0
sys_write=0
sp_flops=0
f=open(sys.argv[1],"r")
'''
g=open(sys.argv[2],"r")
runtime =0
for line in g:
    words = line.split(",")
    if '"Duration"' in words:
        word = words[11]
        word = word[1:-2]
        runtime+=int(word)
'''
for line in f:
  words = line.split(",")#  l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum
  #print words
  if '"l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum"' in words:
      word = words[11]
      word = word[1:-2]
      gld_trans+=int(word)
  elif '"l1tex__t_sectors_pipe_lsu_mem_global_op_st.sum"' in words:
      word = words[11]
      word = word[1:-2]
      gst_trans+=int(word)
  elif '"lts__t_sectors_op_atom.sum"' in words:
      word = words[11]
      word = word[1:-2]
      atomic_trans+=2*int(word)
  elif '"lts__t_sectors_op_red.sum"' in words:
      word = words[11]
      word = word[1:-2]
      atomic_trans+=2*int(word)
  elif '"l1tex__t_sectors_pipe_lsu_mem_local_op_ld.sum"' in words:
      word = words[11]
      word = word[1:-2]
      local_load_trans+=int(word);
  elif '"l1tex__t_sectors_pipe_lsu_mem_local_op_st.sum"' in words:
      word = words[11]
      word = word[1:-2]
      local_store_trans+=int(word);
  elif '"l1tex__data_pipe_lsu_wavefronts_mem_shared_op_ld.sum"' in words:
      word = words[11]
      word = word[1:-2]
      shared_load_trans+=int(word);
  elif '"l1tex__data_pipe_lsu_wavefronts_mem_shared_op_st.sum"' in words:
      word = words[11]
      word = word[1:-2]
      shared_store_trans+=int(word);
  elif '"lts__t_sectors_op_read.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_read+=int(word);
  elif '"lts__t_sectors_op_atom.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_read+=int(word);
  elif '"lts__t_sectors_op_red.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_read+=int(word);
  elif '"lts__t_sectors_op_write.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_write+=int(word);
  elif '"lts__t_sectors_op_atom.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_write+=int(word);
  elif '"lts__t_sectors_op_red.sum"' in words:
      word = words[11]
      word = word[1:-2]
      l2_write+=int(word);
  elif '"dram__sectors_read.sum"' in words:
      word = words[11]
      word = word[1:-2]
      dram_read+=int(word);
  elif '"dram__sectors_write.sum"' in words:
      word = words[11]
      word = word[1:-2]
      dram_write+=int(word);
  elif '"lts__t_sectors_aperture_sysmem_op_read.sum"' in words:
      word = words[11]
      word = word[1:-2]
      sys_read+=int(word);
  elif '"lts__t_sectors_aperture_sysmem_op_write.sum"' in words:
      word = words[11]
      word = word[1:-2]
      sys_write+=int(word);
  elif '"smsp__sass_thread_inst_executed_op_fadd_pred_on.sum"' in words:
      word = words[11]
      word = word[1:-2]
      sp_flops+=int(word);
  elif '"smsp__sass_thread_inst_executed_op_fmul_pred_on.sum"' in words:
      word = words[11]
      word = word[1:-2]
      sp_flops+=int(word);
  elif '"smsp__sass_thread_inst_executed_op_ffma_pred_on.sum"' in words:
      word = words[11]
      word = word[1:-2]
      sp_flops+=2*int(word);
    
'''
gld_trans=0
gst_trans=0
atomic_trans=0
local_load_trans=0
local_store_trans=0
shared_load_trans=0
shared_store_trans=0
l2_read=0
l2_write=0
dram_read=0
dram_write=0
sys_read=0
sys_write=0
sp_flops=0
'''

  #elif words[0]=="Simple":
  #  simple.append(float(words[3][:-3]))
  #elif words[0]=="Nested":
  #  nested.append(float(words[3][:-3]))
  #elif words[0]=="No-fusion":
  #      nofus.append(float(words[3][:-3]))
  #else:
  #  auto.append(float(words[2][:-3]))
print 'gst_trans\n', gst_trans
print 'atomic_trans\n', atomic_trans
print 'global_trans\n', gld_trans
print 'local_load_trans\n',local_load_trans
print 'shared_loads\n',shared_load_trans
print 'shared_store\n',shared_store_trans
print 'local_store\n',local_store_trans
print 'l2_reads\n',l2_read
print 'l2_writes\n',l2_write
print 'dram_w\n',dram_write
print 'dram_r\n',dram_read
print 'sys_read\n',sys_read
print 'sys_write\n',sys_write
print 'flops\n',sp_flops
print 'drams\n',dram_write+dram_read

l1_bytes_transfered = (gld_trans+gst_trans+atomic_trans+local_load_trans+local_store_trans+shared_load_trans)*32
l2_bytes_transfered = (l2_read + l2_write) * 32
hbm_bytes_transfered = (dram_write+dram_read)*32
runtime = sys.argv[2]
runtime = float(runtime)
#print(runtime)
sp_flops = float(sp_flops)
l1_bytes_transfered = float(l1_bytes_transfered)
l2_bytes_transfered = float(l2_bytes_transfered)
hbm_bytes_transfered = float(hbm_bytes_transfered)
AI_l1 = (sp_flops / l1_bytes_transfered)
AI_l2 = (sp_flops / l2_bytes_transfered)
AI_hbm = (sp_flops / hbm_bytes_transfered)
#AI = (sp_flops / (l1_bytes_transfered + l2_bytes_transfered + hbm_bytes_transfered))
performance = (sp_flops/runtime)/1e9
f.close()
print '=====\n perf\n',performance
print 'arith intens l1 \n',AI_l1
print 'arith intens l2 \n',AI_l2
print 'arith intens hbm \n',AI_hbm
#print 'arith intens \n',AI




