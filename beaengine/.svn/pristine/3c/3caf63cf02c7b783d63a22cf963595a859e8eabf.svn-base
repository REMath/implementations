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

class My_Toolbar(wx.ToolBar):
    def __init__(self, parent):
        wx.ToolBar.__init__(self, parent, -1,
                            style=wx.TB_HORIZONTAL | wx.NO_BORDER |
                            wx.TB_FLAT | wx.TB_TEXT)
     
        toolSize = (24, 24)
        self.SetToolBitmapSize(toolSize)
        
        self.AddLabelTool(20, u" Open ",
                          wx.Bitmap("Bitmaps/tb_Open.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Display the open file dialog.")
        self.AddSeparator()
        self.AddLabelTool(21, u"Disassemble",
                          wx.Bitmap("Bitmaps/tb_Disassemble.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Launch the disassembling.")
        self.AddSeparator()
        self.AddLabelTool(22, u"Screen Shot",
                          wx.Bitmap("Bitmaps/tb_Print.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Frame screen shot.")
        self.AddSeparator()
        self.AddLabelTool(23, u"About",
                          wx.Bitmap("Bitmaps/tb_About.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"About this application.")
        self.AddSeparator()
        self.AddLabelTool(24, u"Memento",
                          wx.Bitmap("Bitmaps/tb_Note.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Little reminder.")
        self.AddSeparator()
        self.AddLabelTool(25, u"Online help",
                          wx.Bitmap("Bitmaps/tb_Help.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Online help.")
        self.AddSeparator()
        self.AddLabelTool(26, u"Quit",
                          wx.Bitmap("Bitmaps/tb_Quit.png", wx.BITMAP_TYPE_PNG),
                          shortHelp=u"",
                          longHelp=u"Quit the application.")
        self.AddSeparator()
        
        self.Realize()
        
        