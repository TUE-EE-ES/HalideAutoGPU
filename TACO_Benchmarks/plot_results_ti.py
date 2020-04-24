"""
========
Barchart
========

A bar plot with errorbars and height labels on individual bars
"""
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
print(mpl.__version__) 
mpl.rcParams['hatch.linewidth'] = 0.8

auto=[]
manual=[]
simple=[]
nested=[]
nofus=[]
f=open("results_4ti.txt","r")
for line in f:
  words = line.split(" ")
  if len(words)==1:
    continue
  print(words);
  if words[0]=="Manual":
    #manman=words[2][:-3];
    manual.append(float(words[2][:-3]))
  elif words[0]=="Simple":
    simple.append(float(words[3][:-3]))
  elif words[0]=="Nested":
    nested.append(float(words[3][:-3]))
  elif words[0]=="No-fusion":
        nofus.append(float(words[3][:-3]))
  else:
    auto.append(float(words[2][:-3]))

f.close()
print("auto")
for a in auto:
  print(a)
  
print("manual")
print(len(auto))
print(len(manual)) 
for a in manual:
  print(a)

ratio_m=np.array
np.array(auto)
np.array(manual)
np.array(simple)
np.array(nested)
nested = np.minimum(auto,nested)
ratio_m=np.minimum(auto,nested)/manual
print(np.mean(ratio_m))
ratio_s=np.minimum(auto[:11],nested[:11])/simple[:11]
print(np.mean(ratio_s))


"""
========
Barchart
========

A bar plot with errorbars and height labels on individual bars
"""


class ScalarFormatterForceFormat(ticker.ScalarFormatter):
    def _set_format(self,vmin,vmax):  # Override function that finds format to use.
        self.format = "$%.1f$"  # Give format here

N=2;

titles=('bilateral','camera','harris','histogram','IIR','interpolate','laplacian','maxfilter','unsharp','nlmeans','stencil','matmul','cvlayer','lensblur')
ind = 0.1  # the x locations for the groups
width = 0.2      # the width of the bars
x=1
y=2
f,ax2d = plt.subplots(3, 5, sharex='col',squeeze=True,figsize=(9,4))
f.text(0.008, 0.5, 'Average execution time (ms)', ha='center', va='center',fontsize='large', rotation='vertical')
#f.figsize=(2,2)
#plt.tight_layout()
#DefaultSize=f.get_size_inches()
#f.set_size_inches(DefaultSize[0]*0.5,DefaultSize[1])

axli=ax2d.flatten()
for i,ax1 in enumerate(axli):
	if(i<12):
		rects1 = ax1.bar(2*ind, auto[i], width, color='#e66101',edgecolor='black')#,hatch='//')
		rects2 = ax1.bar(2*ind + 0.15+width,nested[i],width,color='#fdb863',edgecolor='black')#,hatch='--')
                rects3 = ax1.bar(2*ind + 0.3+2*width,nofus[i],width,color='#FFFAF0',edgecolor='black')
		rects4 = ax1.bar(2*ind + 0.45+3*width,manual[i],width,color='#b2abd2',edgecolor='black')#,hatch='xx')
                rects5 = ax1.bar(2*ind + 0.6+4*width,simple[i],width,color='#5e3c99',edgecolor='black')#,hatch='\\\\')

		ax1.set_xlim(0,1.8)


		#	ax1.set_title('Sharing x per column, y per row')
		# Fine-tune figure; make subplots close to each other and hide x ticks for
		# all but bottom plot.
		# add some text for labels, title and axes ticks
		
		start, end = ax1.get_ylim()
		ax1.yaxis.set_ticks(np.arange(start, end*1.2, abs(start-end)/4))
		if(end>100):	
			print(end)
			yfmt = ScalarFormatterForceFormat()
			yfmt.set_powerlimits((0,0))
			ax1.yaxis.set_major_formatter(yfmt)
			ax1.set_title(titles[i],y=1.0,loc='right',fontsize='large')
		else:
			ax1.yaxis.set_major_formatter(ticker.FormatStrFormatter('$%.1f$'))
			ax1.set_title(titles[i],y=1.0,fontsize='large')
		ax1.yaxis.major.formatter._useMathText = True
		ax1.tick_params(labelsize='large')
		ax1.tick_params(
		    axis='x',          # changes apply to the x-axis
		    which='both',      # both major and minor ticks are affected
		    bottom='off',      # ticks along the bottom edge are off
		    top='off',         # ticks along the top edge are off
		    labelbottom='off')
		ax1.set_axisbelow(True)
		ax1.yaxis.grid(color='gray', linestyle=':')
        elif(i<14):
                rects1 = ax1.bar(2*ind, auto[i], width, color='#e66101',edgecolor='black')#,hatch='//')
                rects2 = ax1.bar(2*ind + 0.15+width,nested[i],width,color='#fdb863',edgecolor='black')#,hatch='--')
                rects3 = ax1.bar(2*ind + 0.3+2*width,nofus[i],width,color='#FFFAF0',edgecolor='black')
                rects4 = ax1.bar(2*ind + 0.45+3*width,manual[i],width,color='#b2abd2',edgecolor='black')#,hatch='xx')
                ax1.set_xlim(0,1.8)
                #       ax1.set_title('Sharing x per column, y per row')
                # Fine-tune figure; make subplots close to each other and hide x ticks for
 #                all but bottom plot.
                # add some text for labels, title and axes ticks
        	start, end = ax1.get_ylim()
		ax1.yaxis.set_ticks(np.arange(start, end*1.2, abs(start-end)/4))
		if(end>100):	
			print(end)
			yfmt = ScalarFormatterForceFormat()
			yfmt.set_powerlimits((0,0))
			ax1.yaxis.set_major_formatter(yfmt)
			ax1.set_title(titles[i],y=1.0,loc='right',fontsize='large')
		else:
			ax1.yaxis.set_major_formatter(ticker.FormatStrFormatter('$%.1f$'))
			ax1.set_title(titles[i],y=1.0,fontsize='large')
		ax1.yaxis.major.formatter._useMathText = True
		ax1.tick_params(labelsize='large')
		ax1.tick_params(
		    axis='x',          # changes apply to the x-axis
		    which='both',      # both major and minor ticks are affected
		    bottom='off',      # ticks along the bottom edge are off
		    top='off',         # ticks along the top edge are off
		    labelbottom='off')
		ax1.set_axisbelow(True)
		ax1.yaxis.grid(color='gray', linestyle=':')
	else:
		plt.delaxes(ax1) 
			#ax.set_xticklabels(('G1', 'G2', 'G3', 'G4', 'G5'))"""
                        #ax.set_xticklabels(('G1', 'G2', 'G3', 'G4', 'G5'))"""
plt.legend((rects1[0], rects2[0],rects3[0],rects4[0],rects5[0]), ('AutoGPU (Overlap)','AutoGPU (Nested)','AutoGPU (w/o Fus)','Manual','Gradient scheduler'),bbox_to_anchor=(2.75,1.35),fancybox=True,edgecolor='black',fontsize='medium',ncol=1)
        #plt.tight_layout()



plt.tight_layout();
#plt.subplots_adjust(bottom=0.5, wspace=0.5)
#plt.tight_layout(pad=3.5,w_pad=0.75,h_pad=0.75)
#f.savefig("results_ti.png")
plt.savefig("results4_ti_plt.pdf")
plt.show()

