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

class My_StaticBox(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent, -1)
        
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #-------------------------------------------------------------------
        
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":
            self.normalFont = wx.Font(fontSize-4,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        elif wx.Platform == "__WXGTK__":
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        else:
            self.normalFont = wx.Font(fontSize+0,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
         
        self.SetFont(self.normalFont)
        
       #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer1 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "OF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#404040")
        bsizer1.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "M",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")  #e2ceff 
        basicText.SetInsertionPoint(0)
        bsizer1.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer2 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "SF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#404040")
        bsizer2.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "O",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer2.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer3 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "ZF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer3.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "---",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer3.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer4 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "AF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#404040")
        bsizer4.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "1",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer4.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer5 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "PF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#404040")
        bsizer5.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "M",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer5.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer6 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "CF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer6.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "2",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer6.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer7 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "TF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer7.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "1",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer7.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer8 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "IF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer8.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "M",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer8.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer9 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "DF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer9.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "0",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer9.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer10 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "NT",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#404040")
        bsizer10.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "P",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer10.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "", style=wx.BORDER_NONE)
        bsizer11 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "RF",
                               style = wx.TE_CENTRE)
        texte1.SetFont(self.normalFont) 
        texte1.SetForegroundColour("#404040")
        bsizer11.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        basicText = wx.TextCtrl(self, -1, "2",
                                style = wx.TE_CENTRE)
        basicText.SetFont(self.normalFont)
        basicText.SetBackgroundColour("#e2ceff")
        basicText.SetInsertionPoint(0)
        bsizer11.Add(basicText, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        #-------------------------------------------------------------------
        
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(bsizer1, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer2, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer3, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer4, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer5, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer6, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer7, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer8, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer9, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer10, 1, wx.EXPAND | wx.ALL, 0)
        sizer.Add(bsizer11, 1, wx.EXPAND | wx.ALL, 0)
        
        #----------
        
        box = wx.StaticBox(self, -1, "Eflags :", style=wx.BORDER_NONE)
        box.SetForegroundColour("#0074ff")
        allSizer = wx.StaticBoxSizer(box, wx.VERTICAL)        
        allSizer.Add(sizer, 1, wx.EXPAND | wx.TOP, 3)
        
        #----------
        
        topSizer = wx.BoxSizer(wx.VERTICAL)
        topSizer.Add(allSizer, 1, wx.EXPAND | wx.TOP, 6)
        
        self.SetSizer(topSizer)
        topSizer.Fit(self)
        
        
