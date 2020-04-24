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
#0.922441206848
#a0.451236286948
#
#0.958480658026
#0.521779483132#


propm = [1/0.890101732724 , 1/0.904644884007 , 1/1.05616342645,1/0.959983104732 ,1/0.974005139407 ,1/0.958480658026
 ]
props = [1/0.426059135889 , 1/0.448395411112 , 1/0.548040714548,1/0.511221374409,  1/0.59051728142, 1/0.521779483132
 ] 


titles=('RTX 2080 Ti','RTX 2070','GTX TITAN','GTX 570','Tegra K1','AGX Xavier')
ind = 0.15  # the x locations for the groups
width = 0.3      # the width of the bars
x=1
y=2
f,ax2d = plt.subplots(1, 6, sharex='col',squeeze=True,figsize=(9,2))
f.text(0.015, 0.5, 'Speedup', ha='center', va='center',fontsize='large', rotation='vertical')
#f.figsize=(2,2)
#plt.tight_layout()
#DefaultSize=f.get_size_inches()
#f.set_size_inches(DefaultSize[0]*0.5,DefaultSize[1])

axli=ax2d.flatten()
for i,ax1 in enumerate(axli):
	if(i<6):
		rects1 = ax1.bar(2*ind, propm[i], width, color='#f1a340',edgecolor='black')#,hatch='//')
		rects2 = ax1.bar(2*ind + 0.15+width,props[i],width,color='#998ec3',edgecolor='black')#,hatch='--')
		ax1.set_xlim(0,1.05)


		#	ax1.set_title('Sharing x per column, y per row')
		# Fine-tune figure; make subplots close to each other and hide x ticks for
		# all but bottom plot.
		# add some text for labels, title and axes ticks
		
		start, end = ax1.get_ylim()
                if(end > 2):
                    yticks=[0.5,1,2,2.5];
                elif(end > 1.5):
                    yticks=[0.5,1,1.5,2];
#		ax1.yaxis.set_ticks(np.arange(0, 2.6))
                ax1.yaxis.set_ticks(yticks);
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
  
plt.legend((rects1[0], rects2[0]), ('Manual/AutoGPU','Li et al/AutoGPU'),bbox_to_anchor=(-0.85,-0.003),fancybox=True,edgecolor='black',fontsize='large',ncol=2)
	#plt.tight_layout()

plt.tight_layout();
#plt.subplots_adjust(bottom=0.5, wspace=0.5)
plt.tight_layout(pad=2.5,w_pad=0.75,h_pad=0.75)
#f.savefig("results_ti.png")
plt.savefig("results_ratios.pdf")
plt.show()

