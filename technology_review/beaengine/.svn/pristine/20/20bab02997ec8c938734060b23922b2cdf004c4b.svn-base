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
import Instructions
import ArgumentOne
import ArgumentTwo
import ArgumentThree
import ArgumentFour
import ArgumentFive
import Eflags

#---------------------------------------------------------------------------

class PageInfos(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        self.SetBackgroundColour("#f0f0f0")
        
        #-------------------------------------------------------------------
        
        self.stbx1 = Instructions.My_StaticBox(self)
        self.stbx2 = ArgumentOne.My_StaticBox(self)
        self.stbx3 = ArgumentTwo.My_StaticBox(self)
        self.stbx4 = ArgumentThree.My_StaticBox(self)
        self.stbx5 = ArgumentFour.My_StaticBox(self)
        self.stbx6 = ArgumentFive.My_StaticBox(self)
        self.stbx7 = Eflags.My_StaticBox(self)
        
        stbx1Sizer = wx.BoxSizer(wx.HORIZONTAL)
        stbx2Sizer = wx.BoxSizer(wx.HORIZONTAL)
        stbx3Sizer = wx.BoxSizer(wx.HORIZONTAL)
        stbx4Sizer = wx.BoxSizer(wx.HORIZONTAL)
        
        stbx1Sizer.Add(self.stbx1, 1, wx.EXPAND | wx.ALL, 0)
        stbx2Sizer.Add(self.stbx2, 1, wx.EXPAND | wx.ALL, 0)
        stbx2Sizer.Add(self.stbx3, 1, wx.EXPAND | wx.ALL, 0)
        stbx3Sizer.Add(self.stbx4, 1, wx.EXPAND | wx.ALL, 0)
        stbx3Sizer.Add(self.stbx5, 1, wx.EXPAND | wx.ALL, 0)
        stbx4Sizer.Add(self.stbx6, 1, wx.EXPAND | wx.ALL, 0)
        stbx4Sizer.Add(self.stbx7, 1, wx.EXPAND | wx.ALL, 0)
        
        #----------
        
        stbxSizer = wx.BoxSizer(wx.VERTICAL)
        
        stbxSizer.Add(stbx1Sizer, 1, wx.EXPAND | wx.ALL, 0)
        stbxSizer.Add(stbx2Sizer, 1, wx.EXPAND | wx.ALL, 0)
        stbxSizer.Add(stbx3Sizer, 1, wx.EXPAND | wx.ALL, 0)
        stbxSizer.Add(stbx4Sizer, 1, wx.EXPAND | wx.ALL, 0)
        
        #----------
      
        self.SetAutoLayout(True)
        self.SetSizer(stbxSizer)
        stbxSizer.Fit(self)
        
#---------------------------------------------------------------------------
        
class PageOptions(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        self.SetBackgroundColour("#f0f0f0")
        
        txt2 = wx.StaticText(self, -1, "Blah, blah, blah", (40, 40))
        
#---------------------------------------------------------------------------
        
class My_Notebook(wx.Notebook):
    def __init__(self, parent, id):
        wx.Notebook.__init__(self, parent, id, size=(21, 21),
                             style=wx.CLIP_CHILDREN)  # wx.BK_DEFAULT | 
        
        # Create some instance of class
        page1 = PageInfos(self)
        page2 = PageOptions(self)
        
        # Create the page windows as children of the notebook
        self.AddPage(page1, "Infos")
        self.AddPage(page2, "Options")
        
        # Add an image on the tab
        bmp = wx.Bitmap("Bitmaps/nb_Infos.png", wx.BITMAP_TYPE_PNG)
        il = wx.ImageList(16, 16)
        idx1 = il.Add(bmp)
        self.AssignImageList(il)
        
        self.SetPageImage(0, idx1)
       
        # Bind some events to an events handler
        self.Bind(wx.EVT_NOTEBOOK_PAGE_CHANGED, self.OnPageChanged)
        self.Bind(wx.EVT_NOTEBOOK_PAGE_CHANGING, self.OnPageChanging)
        
    #-----------------------------------------------------------------------
        
    def OnPageChanged(self, event):
        old = event.GetOldSelection()
        new = event.GetSelection()
        sel = self.GetSelection()
        event.Skip()
        
        
    def OnPageChanging(self, event):
        old = event.GetOldSelection()
        new = event.GetSelection()
        sel = self.GetSelection()
        event.Skip()
        
        
