from __future__ import division
from collections import defaultdict
from pylab import *
from numpy import *
from mpl_toolkits.mplot3d import axes3d
import numpy as np
import matplotlib.pyplot as plt
import matplotlib as mpl
import pylab as py
import glob as g
import PIL.Image
import numpy

# Example of ploting bi-grams and tri-grams of hex values. A bad knock-off of a part of Cantor.Dust and research of Gregory Conti. :D

# Create hex files using something like xxd -c 1 $i | awk -F" " '{print $2}'

def dbscan(int_list):
    # Taken from http://scikit-learn.org/0.13/auto_examples/cluster/plot_dbscan.html 
    import numpy as np
    from scipy.spatial import distance
    from sklearn.cluster import DBSCAN
    from sklearn import metrics

    # Create a list of (x,y) points
    X = [[x,y] for x,y in int_list]

    ##############################################################################
    # Compute similarities
    D = distance.squareform(distance.pdist(X))
    S = 1 - (D / np.max(D))
    ##############################################################################
    # Compute DBSCAN this is the core "machine learning" part 
    db = DBSCAN().fit(S, eps=0.95, min_samples=10)
    core_samples = db.core_sample_indices_
    labels = db.labels_

    # Number of clusters in labels, ignoring noise if present.
    n_clusters_ = len(set(labels)) - (1 if -1 in labels else 0)

    print 'Estimated number of clusters: %d' % n_clusters_

    ##############################################################################
    # Plot result this is where most of the code belongs and where the "machine learning" ends
    import pylab as pl
    from itertools import cycle

    pl.close('all')
    pl.figure(1)
    pl.clf()

    # Black removed and is used for noise instead.
    colors = cycle('bgrcmybgrcmybgrcmybgrcmy')
    for k, col in zip(set(labels), colors):
        if k == -1:
            # Black used for noise.
            col = 'k'
            markersize = 6
        class_members = [index[0] for index in np.argwhere(labels == k)]
        cluster_core_samples = [index for index in core_samples
                                if labels[index] == k]
        for index in class_members:
            x = X[index]
            if index in core_samples and k != -1:
                markersize = 14
            else:
                markersize = 6
            pl.plot(x[0], x[1], 'o', markerfacecolor=col,
                    markeredgecolor='k', markersize=markersize)

    pl.title('Estimated number of clusters: %d' % n_clusters_)
    pl.show()

def bi_gram(inst_list):
    # A take list and pass a sliding window of length 2
    counter = defaultdict(int) 
    bigram_list = [] 
    for bigram in ngrams(inst_list,2,2):
        counter[tuple(bigram)] += 1
        bigram_list.append(bigram)
    return counter,bigram_list


def tri_gram(inst_list):
    # A take list and pass a sliding window of length 3
    counter = defaultdict(int) 
    trigram_list = [] 
    for trigram in ngrams(inst_list,3,3):
        counter[tuple(trigram)] += 1
        trigram_list.append(trigram)
    return counter,trigram_list

    
def ngrams(tokens, n_min, n_max):
    ''' General function for computing ngrams.'''
    ''' Input: a list of tokens, max gram length, min gram length'''
    n_tokens = len(tokens)
    for i in xrange(n_tokens):
        for j in xrange(i+n_min, min(n_tokens, i+n_max)+1):
            yield tokens[i:j]

def scale_to_unit_interval(ndar, eps=1e-8):
    """ Scales all values in the ndarray ndar to be between 0 and 1 """
    ndar = ndar.copy()
    ndar -= ndar.min()
    ndar *= 1.0 / (ndar.max() + eps)
    return ndar

def create_BW_mat(int_list,name,bi_gram_counts):
    print name
    total = sum(bi_gram_counts.values())
    print total 
    empty = np.zeros(shape=(256,256),dtype=numpy.uint8)
    x,y = zip(*int_list)
    for X,Y in zip(x,y): 
        pixel = bi_gram_counts[(X,Y)] / float(total)
        empty[X][Y] = np.absolute(np.log2(pixel))

        print empty[X][Y], bi_gram_counts[(X,Y)]
#    f = empty.flatten()
    image = PIL.Image.fromarray(empty)
    #              X=rbm.W.get_value(borrow=True).T,
    #              img_shape=(28, 28), tile_shape=(10, 10),
    #              tile_spacing=(1, 1)))
    pic_name = 'test_2D' + name + ".png"
    image.save(pic_name)
    

def plot_2D(int_list,title):
    # Take a list of 2D points and plot them 
    x,y = zip(*int_list)
    mpl.pyplot.clf()
    mpl.pyplot.scatter(x,y)
    mpl.pyplot.savefig(title+"_2D"+".png")
    #mpl.pyplot.show() 

def plot_3D(int_list,title):
    # Take a list of 3D points and plot them 
    fig = plt.figure()
    fig.clf() 
    x,y,z = zip(*int_list)
    ax = fig.gca(projection='3d')
    ax.plot(x,y,z,'o')
    plt.savefig(title+"_3D"+".png")
    #plt.show()

def plot_2D_heatmap(int_list):
    x,y = zip(*int_list)
    heatmap, xedges, yedges = np.histogram2d(x,y,10)
    extent = [xedges[0], xedges[-1], yedges[0], yedges[-1]]
    plt.clf()
    plt.imshow(heatmap, extent=extent)
    plt.show()


def count_filter(counter, thres):
    '''We can filter by byte count to get a better signal'''
    ''' Input: dictionaty of counts and counter threshold '''
    new_list = defaultdict(int)
    for key,value in counter.items():
        if value >= thres:
            new_list[key] = value
    return new_list
            

def read_byte_tokens(fileloc):
    ''' Create a list of hex values and the correspodning decimal representation'''
    ''' Input: hex bytes dilimeted by newline '''
    f = open(fileloc, "r")
    hex_list = [] 
    int_list = [] 
    for v in f:
        hex_list.append(v.strip("\n")) 
        int_list.append(int(v,16))
    return hex_list, int_list

def test_bigram_plot(test_file,name):
    hex_list, int_list = read_byte_tokens(test_file)
    bi_gram_counts,bi_grams = bi_gram(int_list) 
    filter_10_bi = count_filter(bi_gram_counts, 10)
    create_BW_mat(filter_10_bi,name,bi_gram_counts)
    #plot_2D(filter_10_bi,name)

def test_trigram_plot(test_file,name):
    hex_list, int_list = read_byte_tokens(test_file)
    tri_gram_counts,tri_grams = tri_gram(int_list) 
    filter_30_tri = count_filter(tri_gram_counts, 30)
    plot_3D(filter_30_tri.keys(),name)

def test_bigram_dbscan(test_file):
    hex_list, int_list = read_byte_tokens(test_file)
    bi_gram_counts,bi_grams = bi_gram(int_list) 
    filter_10_bi = count_filter(bi_gram_counts, 10)
    dbscan(filter_10_bi)

def test_bigram_heatmapn(test_file):
    hex_list, int_list = read_byte_tokens(test_file)
    bi_gram_counts,bi_grams = bi_gram(int_list) 
    filter_10_bi = count_filter(bi_gram_counts, 10)
    plot_2D_heatmap(filter_10_bi)


def return_files_in_dir(path):
    hex_files = g.glob(path + "*.hex")
    return hex_files

def main_test():
    test_files = {
    "ls":"ls.hex",
    "ssh":"ssh.hex",
    "rethinkdb":"rethinkdb.hex",
    "strings":"strings.hex" }
    hex_file = test_files["strings"]
    test_trigram_plot(hex_file)
    test_bigram_plot(hex_file)
    test_bigram_dbscan(hex_file)

def plot_hex_files(files):
    for f in files:
        tokenize = f.split("/")
        l = len(tokenize) 
        name = tokenize[l-1]
        print name
        #test_trigram_plot(f,name)
        test_bigram_plot(f,name)
    

path = "/var/tmp/"
h = return_files_in_dir(path)
plot_hex_files(h[0:1])
    
#main_test()



