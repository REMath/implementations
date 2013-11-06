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

import os.path
import wx                            # This module uses the new wx namespace

#---------------------------------------------------------------------------

class My_Memento(wx.Dialog):
    def __init__(self, parent):
        wx.Dialog.__init__(self, parent, -1,
                           title=u"Memento",
                           pos=(-1, -1), size=(352, 312),
                           style=wx.DEFAULT_FRAME_STYLE ^ (wx.MAXIMIZE_BOX |
                                                           wx.MINIMIZE_BOX))
        
        # Bind the event close to an events handler
        self.Bind(wx.EVT_CLOSE, self.OnCloseWindow)
        
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #-------------------------------------------------------------------
        
        self.filename = u"Memento.txt"
        self.dirname = u"."
        
        #-------------------------------------------------------------------
        
        self.SetMaxSize((700, 600))
        self.SetMinSize((352, 312))
        
        #-------------------------------------------------------------------
        
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":
            self.btnFont = wx.Font(fontSize-1,
                                   wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.normalFont = wx.Font(fontSize+0,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.boldFont = wx.Font(fontSize+2,
                                    wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            
        elif wx.Platform == "__WXGTK__":
            self.btnFont = wx.Font(fontSize+0,
                                   wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.boldFont = wx.Font(fontSize+0,
                                    wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            
        else:
            self.btnFont = wx.Font(fontSize+0,
                                   wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.normalFont = wx.Font(fontSize+2,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            self.boldFont = wx.Font(fontSize+5,
                                    wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            
        self.SetFont(self.btnFont)
        self.SetFont(self.boldFont)
        self.SetFont(self.normalFont)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/logo_Notes.png", wx.BITMAP_TYPE_PNG)
        self.logo = wx.StaticBitmap(self, -1)
        self.logo.SetBitmap(bmp)
        
        #-------------------------------------------------------------------
        
        self.label = wx.StaticText(self, -1, u"Little reminder...")
        self.label.SetFont(self.boldFont)
        self.label.SetSize(self.label.GetBestSize())
        
        #-------------------------------------------------------------------
        
        self.field = wx.TextCtrl(self, -1, value=u"", size=(100, 165),
                                 style=wx.TE_LEFT | wx.TE_MULTILINE |
                                 wx.BORDER_SIMPLE) # wx.BORDER_THEME
        
        self.field.SetFont(self.normalFont)
        self.field.SetSize(self.field.GetBestSize())
        
        filename = open(os.path.join(self.dirname, self.filename), "r")
        text_in = filename.read()
        filename.close()
        
        hello_in = text_in.decode("utf-8", "ignore")
        self.field.SetValue(hello_in)
        
        self.field.SetInsertionPoint(0)
        
        # Bind the focus event to an events handler
        self.field.Bind(wx.EVT_SET_FOCUS, self.OnClearSelection)
        
        #-------------------------------------------------------------------
        
        self.btnSave = wx.Button(self, -1, u"&Save")
        self.btnSave.SetFont(self.btnFont)
        self.btnSave.SetSize(self.btnSave.GetBestSize())
        self.btnSave.SetDefault()
        
        # Bind the button event to an events handler
        self.Bind(wx.EVT_BUTTON, self.OnSave, self.btnSave)
        
        self.btnClose = wx.Button(self, -1, u"&Close")
        self.btnClose.SetFont(self.btnFont)
        self.btnClose.SetSize(self.btnClose.GetBestSize())
        self.btnClose.SetFocus()
        
        # Bind the button event to an events handler
        self.Bind(wx.EVT_BUTTON, self.OnClose, self.btnClose)
        
        #-------------------------------------------------------------------
        
        txtLogoSizer = wx.BoxSizer(wx.HORIZONTAL)
        fieldSizer = wx.BoxSizer(wx.HORIZONTAL)
        btnSizer = wx.BoxSizer(wx.HORIZONTAL)
        
        txtLogoSizer.Add(self.logo, 0, wx.ALL, 10)
        txtLogoSizer.Add(self.label, 0, wx.TOP | wx.RIGHT, 25)
        fieldSizer.Add(self.field, 1, wx.LEFT | wx.RIGHT | wx.EXPAND, 10)
        btnSizer.Add(self.btnSave, 0, wx.ALL, 10)
        btnSizer.Add(self.btnClose, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, 10)
        
        #------------
        
        topSizer = wx.BoxSizer(wx.VERTICAL)
        
        topSizer.Add(txtLogoSizer, 0, wx.ALIGN_LEFT, 0)
        topSizer.Add(fieldSizer, 1, wx.EXPAND, 0)
        topSizer.Add(btnSizer, 0, wx.ALIGN_RIGHT)
        
        #------------
        
        self.SetAutoLayout(True)
        self.SetSizer(topSizer)
        topSizer.Fit(self)
        
        #-------------------------------------------------------------------
        
        self.Centre(wx.BOTH)
        
        self.btnClose = self.ShowModal()
        
    #-----------------------------------------------------------------------
        
    def OnClearSelection(self, event):
        ip = self.field.GetInsertionPoint()
        self.field.SetInsertionPoint(ip) 
        event.Skip()
        
        
    def OnSave(self, event):
        text_out = self.field.GetValue()
        hello_out = text_out.encode("utf-8", "ignore")
        filename = open(os.path.join(self.dirname, self.filename), "w")
        filename.write(hello_out)
        filename.close()
        
        
    def OnClose(self, event):
        self.Close(True)
        
        
    def OnCloseWindow(self, event):
        self.Destroy()
        
        
