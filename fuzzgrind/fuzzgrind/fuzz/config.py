#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import ConfigParser
import os
import sys
import fault_checker


def get_targets(filename):
    '''Return existing sections'''
    
    if not os.path.exists(filename):
        print '[-] configuration error: %s not found' % filename
        sys.exit(-1)
    
    config = ConfigParser.ConfigParser()
    config.read(filename)
    
    sections = config.sections()
    sections.remove('GENERAL')
    
    return sections


def get_option(config, section, option, default):
    '''Return a config option if present, default otherwise'''
    
    if config.has_option(section, option):
        return config.get(section, option)
    else:
        return default


def get_config(filename, configname):
    '''Read the configuration file and return a dictionary'''
    
    if not os.path.exists(filename):
        print '[-] configuration error: %s not found' % filename
        sys.exit(-1)
    
    config = ConfigParser.ConfigParser()
    config.read(filename)
    
    if not config.has_section(configname):
        print '[-] configuration error: %s section not found' % configname
        sys.exit(-1)
    
    if not config.has_section('GENERAL'):
        print '[-] configuration error: GENERAL section'
        sys.exit(-1)
    
    output_folder = config.get('GENERAL', 'output', '')
    input_folder = config.get('GENERAL', 'input', '')
    crash_folder = config.get('GENERAL', 'crash', '')
    
    prog = get_option(config, configname, 'prog', None)
    input = get_option(config, configname, 'input', None)
    ext = get_option(config, configname, 'ext', None)
    min_bound = int(get_option(config, configname, 'min_bound', '0'))
    max_bound = int(get_option(config, configname, 'max_bound', '-1'))
    stdin = (get_option(config, configname, 'stdin', 'false').lower() == 'true')
    checker = get_option(config, configname, 'checker', 'ptrace')
    progarg = get_option(config, configname, 'arg', '')
    
    if not prog:
        print '[-] configuration error: prog option not found'
        sys.exit(-1)
    elif not os.path.exists(prog):
        print '[-] prog %s not found' % prog
        sys.exit(-1)
        
    if not input:
        print '[-] configuration error: input option not found'
        sys.exit(-1)
    
    # fuzzgrind --file-filter option expects absolute path
    if not input_folder.startswith('/'):
        input_folder = os.path.join(os.getcwd(), input_folder)
    
    if not output_folder.startswith('/'):
        output_folder = os.path.join(os.getcwd(), output_folder)

    if not crash_folder.startswith('/'):
        crash_folder = os.path.join(os.getcwd(), crash_folder)
    
    if not input.startswith('/'):
        input = os.path.join(input_folder, input)
    
    if not ext:
        ext = os.path.splitext(os.path.basename(input))[1]
    else:
        ext = '.' + ext
    
    checkers = [ c[6:] for c in dir(fault_checker) if c.startswith('check_') ]
    if checker not in checkers:
        print '[-] configuration error: wrong fault checker "%s"' % checker
        print '    valid fault checkers are: %s' % ', '.join(checkers)
        sys.exit(-1)
    
    # XXX - erk. maybe use __import__ ?
    checker_callback = eval('fault_checker.check_%s' % checker)
        
    param = {
        'OUTPUT_FOLDER': output_folder,
        'INPUT_FOLDER':  input_folder,
        'CRASH_FOLDER':  crash_folder,
        'PROGNAME':      prog,
        'INPUT_FILE':    input,
        'EXTENSION':     ext,
        'MIN_BOUND':     min_bound,
        'MAX_BOUND':     max_bound,
        'TAINT_STDIN':   stdin,
        'FAULT_CHECKER': checker_callback,
        'PROGARG':       progarg,
    }
    
    return param
