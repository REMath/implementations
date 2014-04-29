def check_all():
    check_platform()    
    check_sage()
    check_z3()
    print 'All requirements met. Have fun with DIG !'


def check_platform(supported_platforms=['darwin','linux3']):
    """
    Check if the requirement for platform is met. 
    Either Mac OS or Linux is fine
    """
    p = sys.platform.lower()
    print 'System: {}'.format(p)
    assert p in supported_platforms, "Unsupported platform '{}'".format(p)
    if p == 'darwin':
        print ('Warning: Z3 SMT does not work well on Mac. Use with care !')

               
def check_sage(min_version=5.1):
    """
    Check if the requirement for Sage is met
    """
    try:
        
        from sage.env import SAGE_VERSION, SAGE_DATE, SAGE_SRC
        print 'SAGE version: {}, release date: {}, in "{}"'.format(SAGE_VERSION, SAGE_DATE, SAGE_SRC)
        v = float(SAGE_VERSION)
    
        assert v >= min_version
            
    except Exception:
        
        raise AssertionError("Needs to have SAGE version >= {}".format(min_version))
        


def check_z3():
    """
    Check if Z3 API can be loaded properly
    """

    try:
        import z3
        import z3util
        print 'Z3 version: {}'.format(z3util.get_z3_version(as_str=True))
        
    except Exception:
        msg = ("Try Adding z3py Api to SAGE_PATH\n" 
               "E.g. in ~/.bash_profile\n"
               "export SAGE=$DEVEL/SAGE/sage\n"
               "export PATH=$SAGE:$PATH\n"
               "export SAGE_PATH=$SAGE_PATH:$Z3/build:$DROPBOX/git/common-python-vu")
        
        raise AssertionError('Cannot import Z3 API.\n{}'.format(msg))



if __name__ == "__main__":

    #perform doctest
    print('Runs this script in Sage\n'
          'E.g.,\n'
          'sage: %attach check_requirements.py\n'
          'sage: check_all()\n')
    


