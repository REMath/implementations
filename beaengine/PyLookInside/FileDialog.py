# -*- coding: utf8 -*-

"""

Copyright 2006-2009, BeatriX

This file is part of BeaEngine.
 
BeaEngine is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

BeaEngine is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with BeaEngine.  If not, see <http://www.gnu.org/licenses/>.

"""

# Import packages

import os
import wx                            # This module uses the new wx namespace

from WilcardList import *

#---------------------------------------------------------------------------

class My_FileDialog(wx.FileDialog):
    def __init__(self, parent,):
        wx.FileDialog.__init__(self, parent,
                               message=u"Choose a file",
                               defaultDir=os.getcwd(),
                               defaultFile=u"",
                               wildcard=wildcard,
                               pos=wx.DefaultPosition,
                               style=wx.OPEN | wx.MULTIPLE | wx.CHANGE_DIR)
        
        # Show the dialog and retrieve the user response. If it is the OK response, 
        # process the data.
        if self.ShowModal()== wx.ID_OK:
            # This returns a Python list of files that were selected.
            paths = self.GetPaths()
            
        # Destroy the dialog. Don't do this until you are done with it!
        # BAD things can happen otherwise!
        self.Destroy()
        
        
