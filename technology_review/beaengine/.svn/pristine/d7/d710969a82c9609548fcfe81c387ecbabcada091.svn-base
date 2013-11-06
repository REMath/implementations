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
        
        box = wx.StaticBox(self, -1, "Instruction. Category :")
        box.SetForegroundColour("#0074ff")
        bsizer1 = wx.StaticBoxSizer(box, wx.VERTICAL)
       
        texte1 = wx.StaticText(self, -1,
                               "GENERAL_PURPOSE_INSTRUCTION + CONTROL_TRANSFER",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer1.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Instruction. Mnemonic :")
        box.SetForegroundColour("#0074ff")
        bsizer2 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "jean",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer2.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Instruction. Opcode :")
        box.SetForegroundColour("#0074ff")
        bsizer3 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "00000074",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer3.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Instruction. Branch Type :")
        box.SetForegroundColour("#0074ff")
        bsizer4 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "je",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer4.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Instruction. Prefixes :")
        box.SetForegroundColour("#0074ff")
        bsizer5 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "---",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer5.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Instruction. Immediat :")
        box.SetForegroundColour("#0074ff")
        bsizer6 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "---",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer6.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        
        box = wx.StaticBox(self, -1, "Implicit Modified Regs :")
        box.SetForegroundColour("#0074ff")
        bsizer7 = wx.StaticBoxSizer(box, wx.VERTICAL)
        
        texte1 = wx.StaticText(self, -1, "---",
                               style=wx.ALIGN_LEFT)
        texte1.SetFont(self.normalFont)
        texte1.SetForegroundColour("#892903")
        bsizer7.Add(texte1, 1, wx.ALL|wx.EXPAND, 0)
        
        #-------------------------------------------------------------------
        #-------------------------------------------------------------------
        
        sizer1 = wx.BoxSizer(wx.HORIZONTAL)
        sizer1.Add(bsizer1, 1, wx.EXPAND | wx.TOP, 3)
        
        #----------
        
        sizer2 = wx.BoxSizer(wx.HORIZONTAL)
        sizer2.Add(bsizer2, 1, wx.EXPAND | wx.TOP, 3)
        sizer2.Add(bsizer3, 1, wx.EXPAND | wx.TOP, 3)
        sizer2.Add(bsizer4, 1, wx.EXPAND | wx.TOP, 3)
        
        #----------
        
        sizer3 = wx.BoxSizer(wx.HORIZONTAL)
        sizer3.Add(bsizer5, 1, wx.EXPAND | wx.TOP, 3)
        sizer3.Add(bsizer6, 1, wx.EXPAND | wx.TOP, 3)
        sizer3.Add(bsizer7, 1, wx.EXPAND | wx.TOP, 3)
        
        #----------
        
        topSizer = wx.BoxSizer(wx.VERTICAL)
        topSizer.Add(sizer1, 1, wx.EXPAND | wx.TOP, 3)
        topSizer.Add(sizer2, 1, wx.EXPAND | wx.TOP, 3)
        topSizer.Add(sizer3, 1, wx.EXPAND | wx.TOP, 3)
        
        #----------
        
        self.SetSizer(topSizer)
        topSizer.Fit(self)
        
        
