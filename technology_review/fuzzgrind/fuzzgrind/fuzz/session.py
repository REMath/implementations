#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import cPickle
import os
import zlib


def load(target):
    '''
    Restore a session given it's filename
    
    @param progname: session name
    @type  progname: str
    '''
    
    session_filename = 'session/%s.session' % target
    
    if not os.path.exists(session_filename):
        return
        
    fp = open(session_filename, 'rb')
    data = cPickle.loads(zlib.decompress(fp.read()))
    fp.close()
    
    PARAM    = data['PARAM']
    ninput   = data['ninput']
    worklist = data['worklist']
    
    return PARAM, ninput, worklist
    
    
def save(target, PARAM, ninput, worklist):
    '''
    Save current session to a file
    
    @param worklist:
    @type  worklist: Input list
    '''
    
    session_filename = 'session/%s.session' % target

    data = {}
    data['PARAM']    = PARAM
    data['ninput']   = ninput
    data['worklist'] = worklist

    fp = open(session_filename, 'wb+')
    fp.write(zlib.compress(cPickle.dumps(data, protocol=2)))
    fp.close()
