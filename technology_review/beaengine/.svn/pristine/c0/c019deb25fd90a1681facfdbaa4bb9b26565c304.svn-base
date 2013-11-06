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

class My_SearchCtrl(wx.SearchCtrl):
    def __init__(self, parent, id=-1, value=u"",
                 pos=wx.DefaultPosition, size=(270, -1), style=0):
        wx.SearchCtrl.__init__(self, parent, id, value,
                               pos, size, style)
                               
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #-------------------------------------------------------------------
        
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        elif wx.Platform == "__WXGTK__":
            self.normalFont = wx.Font(fontSize+1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        else:
            self.normalFont = wx.Font(fontSize+1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        self.SetFont(self.normalFont)
        self.SetSize(self.GetBestSize())
        
        #-------------------------------------------------------------------
        
        self.ShowSearchButton(True)
        self.ShowCancelButton(True)
        
        #-------------------------------------------------------------------
        
        self.SetMenu(self.OnMenu())
        self.SetFocus()
        
        #-------------------------------------------------------------------
        
        # Bind some events to an events handler
        self.Bind(wx.EVT_SEARCHCTRL_SEARCH_BTN, self.OnSearchBtn, self)
        self.Bind(wx.EVT_SEARCHCTRL_CANCEL_BTN, self.OnCancelBtn, self)
        self.Bind(wx.EVT_TEXT_ENTER, self.OnDoSearch)
        self.Bind(wx.EVT_MENU, self.OnMenu)
        
    #-----------------------------------------------------------------------
    
    def OnDoSearch(self, event):
        pass
     
     
    def OnSearchBtn(self, event):
        pass
     
     
    def OnCancelBtn(self, event):
        self.Clear()
     
     
    def OnMenu(self):
        menu = wx.Menu()
        item = menu.Append(-1, text=u"Prefix :")
        item.Enable(False)
        for txt in [ u"Offset",
                     u"Value" ]:
            menu.Append(-1, txt)
     
        return menu
     
     
