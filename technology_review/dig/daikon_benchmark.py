import common as CM

"""
Contain utilities to run Daikon on benchmark programs
Based on the old stuff in 
~/USB/SVN/DCBA/code/(inv.py,dk/)
"""


"""
EXAMPLE on how to run Daikon on the 'cohendiv" benchmark. 
Note: It's best to copy all these .sh files to a local dir because
all thes traces will take lots of space

$ cd /tmp_dir/contains/cohendiv.sh
$ ln -sf ~/Dropbox/git/invgen/Benchmarks/testsuites/arithmetics/inv .
$ ln -sf ~/Dropbox/git/invgen/daikon_benchmark.py .

$ sage
sage: attach daikon_benchmark.py 

#create the daikon testscript
sage: create_dk_run_script('cohendiv',write_to_file=True)
sage: mkdir cohendiv

#run the testscript to obtain traces (take a long time)
sage: !sh cohendiv_dk.sh

#get invariant from the traces and output results (take a long time)
sage: run_dk('cohendiv')

"""
def create_dk_run_script(pname, write_to_file=False):
    """
    Takes in the name of a program and 
    convert its script file (pname.sh) 
    to Daikon run script (pname_dk.sh)


    EXAMPLES:
    ./inv cohendiv 5 2  
    => 
    kvasir-dtrace -q --dtrace-file=cohendiv/19.dtrace --program-stdout=cohendiv/1.out --program-stderr=cohendiv/1.err ./inv cohendiv 5 2 &> cohendiv/1.dk_err
    """

    script_file = pname + '.sh'

    assert os.path.isfile(script_file) 
        

    lines = CM.vread(script_file,verbose=verbose).splitlines()
    lines = [cmd for cmd in lines if not cmd.startswith('#')]

    #disallow something like './inv cohendiv 5 2 #comment'
    assert all('#' not in cmd for cmd in lines)  

    kvasir = "kvasir-dtrace -q " +\
        "--dtrace-file={pn}/{i}.dtrace --program-stdout={pn}/{i}.out " +\
        "--program-stderr={pn}/{i}.err {cmd} &> {pn}/{i}.dk_err"
        
    dk_lines = [kvasir.format(pn=pname,i=i,cmd=cmd)
                for i,cmd in enumerate(lines)]

    dk_script = '\n'.join(dk_lines)


    if write_to_file:
        dk_script_file = '{}_dk.sh'.format(pname)
        if os.path.exists(dk_script_file):
            CM.pause('Overwrite {} ? (Ctr + c to abort)'.format(dk_script_file))

        CM.vwrite(dk_script_file,dk_script)
    else:
        print dk_script


def run_dk(pname,execute_cmd = False):
    """
    Takes in the name of a program and 

    (1) run daikon on its trace directory (pname/).
    The result will be output as 'pname.dk.bin'
    This assumes the file pname.dk.sh created by 
    'create_dk_run_script' function has been executed.

    (2) read the Daikon result binary file to text format
    This assumes the Daikon result file 'pname.dk.bin' has been generated 
    from (1)


    EXAMPLES:
    1) java -Xmx1024m daikon.Daikon cohendiv/*.dtrace -o cohendiv.dk_ --no_text_output --no_show_progress --noversion
    2)     EXAMPLES:
    java daikon.PrintInvariants --output_num_samples cohen.dk_

    """
    

    dk_cmd = "java -Xmx2048m "\
        "daikon.Daikon {fr} -o {pn}/{pn}.dk_ "\
        "--no_text_output --no_show_progress --noversion "\
        "> /dev/null"
    
    dk_cmd = dk_cmd.format(pn=pname,fr=os.path.join(pname,'*.dtrace'))

    if execute_cmd:
        CM.vcmd(dk_cmd,verbose=1)
    else:
        print dk_cmd


    dk_read = "java daikon.PrintInvariants "\
        "--output_num_samples "\
        "{pn}/{pn}.dk_ > {pn}/{pn}.dk".format(pn=pname)

    
    if execute_cmd:
        assert os.path.isfile("{pn}/{pn}.dk_".format(pn=pname))
        CM.vcmd(dk_read,verbose=1)
    else:
        print dk_read

