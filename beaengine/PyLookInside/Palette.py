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

import wx                            # This module uses the new wx namespace

#---------------------------------------------------------------------------

class My_MiniFrame(wx.MiniFrame):
    def __init__(self, parent, title, pos=wx.DefaultPosition,
                 size=wx.DefaultSize, style=wx.MINIMIZE_BOX |
                 wx.SYSTEM_MENU | wx.CAPTION | wx.CLOSE_BOX |
                 wx.CLIP_CHILDREN | wx.STAY_ON_TOP):
        wx.MiniFrame.__init__(self, parent, -1, title, pos, size, style)
        
        # Bind the event close to an events handler
        self.Bind(wx.EVT_CLOSE, self.OnCloseWindow)
        
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #------------------------------------------------------------------
        
        self.SetMaxSize((180, 100))
        
        #------------------------------------------------------------------
        
        self.panel = wx.Panel(self, -1)
        self.panel.SetFocus()
        
        #------------------------------------------------------------------
        
        self.btn = wx.Button(self.panel, -1, u"&Close", pos = (20, 20))
        self.btn.SetDefault()
        
        # Bind the button event to an events handler
        self.Bind(wx.EVT_BUTTON, self.OnCloseMe, self.btn)
        
        self.CenterOnParent(wx.BOTH)
        self.Show(True)
        
    #-----------------------------------------------------------------------
        
    def OnCloseMe(self, event):
        self.Close(True)
        
        
    def OnCloseWindow(self, event):
        self.Destroy()
        
        

