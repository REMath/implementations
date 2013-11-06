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

class My_MenuBar(wx.MenuBar):
    def __init__(self, parent):
        wx.MenuBar.__init__(self)
        
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #-------------------------------------------------------------------
        #-------------------------------------------------------------------
        
        menuFile = wx.Menu(style=wx.MENU_TEAROFF)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Open.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuFile, 20,
                           text=u"&Open\tCtrl+O",
                           help=u"Display the open file dialog.")
        item.SetBitmap(bmp)
        menuFile.AppendItem(item)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Disassemble.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuFile, 21,
                           text=u"&Disassemble\tCtrl+D",
                           help=u"Launch the disassembling.")
        item.SetBitmap(bmp)
        menuFile.AppendItem(item)
        menuFile.AppendSeparator()
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Print.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuFile, 22,
                           text=u"&Screen Shot\tCtrl+P",
                           help=u"Frame screen shot.")
        item.SetBitmap(bmp)
        menuFile.AppendItem(item)
        menuFile.AppendSeparator()
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Exit.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuFile, 26,
                           text=u"&Quit\tCtrl+Q",
                           help=u"Quit the application.")
        item.SetBitmap(bmp)
        menuFile.AppendItem(item)
        wx.App.SetMacExitMenuItemId(item.GetId())
        
        #-------------------------------------------------------------------
        #-------------------------------------------------------------------
        
        menuView = wx.Menu(style=wx.MENU_TEAROFF)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_RollUp.png", wx.BITMAP_TYPE_PNG)
                        
        item = wx.MenuItem(menuView, 27,
                           text=u"&Roll\tF3",
                           help=u"Minimize the application to this titleBar.")
        item.SetBitmap(bmp)
        menuView.AppendItem(item)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Unroll.png", wx.BITMAP_TYPE_PNG)
                        
        item = wx.MenuItem(menuView, 28,
                           text=u"&UnRoll\tF4",
                           help=u"Restore the application to this initial size.")
        item.SetBitmap(bmp)
        menuView.AppendItem(item)
        
        #-------------------------------------------------------------------
        #-------------------------------------------------------------------
        
        menuWindow = wx.Menu(style=wx.MENU_TEAROFF)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Empty.png", wx.BITMAP_TYPE_PNG)
                        
        item = wx.MenuItem(menuWindow, 29,
                           text=u"Pale&tte\tF5",
                           help=u"Display a tools palette.")
        item.SetBitmap(bmp)
        menuWindow.AppendItem(item)
        
        #-------------------------------------------------------------------        
        #-------------------------------------------------------------------
        
        menuHelp = wx.Menu(style=wx.MENU_TEAROFF)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_About.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuHelp, 23,
                           text=u"&About...\tCtrl+A",
                           help=u"About this application.")
        item.SetBitmap(bmp)
        menuHelp.AppendItem(item)
        wx.App.SetMacAboutMenuItemId(item.GetId())
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Note.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuHelp, 24,
                           text=u"Me&mento\tCtrl+M",
                           help=u"Little reminder.")
        item.SetBitmap(bmp)
        menuHelp.AppendItem(item)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/item_Help.png", wx.BITMAP_TYPE_PNG)
        
        item = wx.MenuItem(menuHelp, 25,
                           text=u"Online &help\tCtrl+H",
                           help=u"Online help.")
        item.SetBitmap(bmp)
        menuHelp.AppendItem(item)
        
        #-------------------------------------------------------------------
        
        self.Append(menuFile, title=u"&File")
        self.Append(menuView, title=u"&View")
        self.Append(menuWindow, title=u"&Window")
        self.Append(menuHelp, title=u"&?")
        
        
