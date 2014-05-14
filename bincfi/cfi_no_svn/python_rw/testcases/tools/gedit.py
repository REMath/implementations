#!/usr/bin/python
'''
LDTP v2 gedit example

@author: Eitan Isaacson <eitan@ascender.com>
@copyright: Copyright (c) 2009 Eitan Isaacson
@license: LGPL

http://ldtp.freedesktop.org

This file may be distributed and/or modified under the terms of the GNU Lesser General
Public License version 2 as published by the Free Software Foundation. This file
is distributed without any warranty; without even the implied warranty of 
merchantability or fitness for a particular purpose.

See "COPYING" in the source distribution for more information.

Headers in this file shall remain intact.
'''

import ldtp, ooldtp
from time import sleep
ldtp.launchapp('/home/mingwei/myworks/cfi/python_rw/target_elf/gedit/gedit_final')
frm = ooldtp.context('*gedit')
frm.waittillguiexist()
txt_field = frm.getchild('txt1')
txt_field.enterstring('Hello world!<return>bye<return>')
ldtp.imagecapture('*gedit', '/tmp/foo.png')
mnu_quit = frm.getchild('mnuQuit')
mnu_quit.selectmenuitem()
alert = ooldtp.context('Question')
alert.waittillguiexist()
btn = alert.getchild('btnClosewithoutSaving')
btn.click()
frm.waittillguinotexist()
