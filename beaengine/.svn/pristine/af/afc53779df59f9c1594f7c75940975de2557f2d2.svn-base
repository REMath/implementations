#!/usr/bin/env python
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


#############################################################################
# Name      :  PyLookInside.py                                              #
# Version   :  4.0                                                          #
# Authors   :  JCie & Beatrix                                               #
# Created   :  December 2009                                                #
# Copyright :  © Copyright 2009-2010  |  BeatriX                            #
# License   :  wxWindows License Version 3.1                                #
# About     :  PyLookInside was built using Python 2.6.4,                   #
#              wxPython 2.8.10.1 unicode, and wxWindows                     #
#############################################################################


# Import packages

import wxversion
wxversion.select("2.8-unicode")  # Launch the script only from wx.Python 2.8

try:
    import wx                        # This module uses the new wx namespace
except ImportError:
    raise ImportError, u"The wxPython unicode module is required to run this program."

import sys
import VersionInfos
import SplashScreen
import MenuBar
import ToolBar
import StatusBar
import TaskBarIcon
import wx.aui
import ListCtrlVirtual
import SearchCtrl
import Notebook
import FileDialog
import AboutNotebook
import MementoProvider
import webbrowser
import Palette

#---------------------------------------------------------------------------

class My_Frame(wx.Frame):
    isRolled = 0
    def __init__(self, parent, id):
        wx.Frame.__init__(self, parent, id,
                          title=u"PyLookInside %s"
                          % VersionInfos.VERSION_STRING,
                          pos=wx.DefaultPosition,
                          size=(920, 683),
                          style=wx.DEFAULT_FRAME_STYLE | wx.TAB_TRAVERSAL |
                          wx.NO_FULL_REPAINT_ON_RESIZE)
        
        # Bind the close event to an events handler
        self.Bind(wx.EVT_CLOSE, self.OnCloseWindow)
        
        #-------------------------------------------------------------------
        
        self.pnl = wx.Panel(self, 1)
#        self.SetBackgroundColour("#f0f0f0")
        
        #-------------------------------------------------------------------
        
        # Simplified init method
        self.createMenuBar()
        self.createToolBar()
        self.createStatusBar()
        self.createTaskBarIcon()
        self.createNotebook()
        self.createAuiManager()
        self.createSearchCtrl()
        self.createListCtrl()
        self.doLayout()
        
        #-------------------------------------------------------------------
        
        self.CenterOnScreen()
        
    #-----------------------------------------------------------------------
        
    def createMenuBar(self):
        self.menu = MenuBar.My_MenuBar(self)
        self.SetMenuBar(self.menu)
        
        # Bind some menus events to an events handler
        self.Bind(wx.EVT_MENU, self.OnFileOpen, id=20)
        self.Bind(wx.EVT_MENU, self.OnDisassemble, id=21)
        self.Bind(wx.EVT_MENU, self.OnScreenShot, id=22)
        self.Bind(wx.EVT_MENU, self.OnAbout, id=23)
        self.Bind(wx.EVT_MENU, self.OnMemento, id=24)
        self.Bind(wx.EVT_MENU, self.OnlineHelp, id=25)
        self.Bind(wx.EVT_MENU, self.OnClose, id=26)
        self.Bind(wx.EVT_MENU, self.OnRoll, id=27)
        self.Bind(wx.EVT_MENU, self.OnUnRoll, id=28)
        self.Bind(wx.EVT_MENU, self.OnToolsPalette, id=29)
        
    #-----------------------------------------------------------------------
        
    def createToolBar(self):
        self.tb = ToolBar.My_Toolbar(self)
        self.SetToolBar(self.tb)
        
        # Bind some tools events to an events handler
        self.Bind(wx.EVT_TOOL, self.OnFileOpen, id=20)
        self.Bind(wx.EVT_TOOL, self.OnDisassemble, id=21)
        self.Bind(wx.EVT_TOOL, self.OnScreenShot, id=22)
        self.Bind(wx.EVT_TOOL, self.OnAbout, id=23)
        self.Bind(wx.EVT_TOOL, self.OnMemento, id=24)
        self.Bind(wx.EVT_TOOL, self.OnlineHelp, id=25)
        self.Bind(wx.EVT_TOOL, self.OnClose, id=26)
        
    #-----------------------------------------------------------------------
        
    def createStatusBar(self):
        self.sb = StatusBar.My_CustomStatusBar(self)
        self.SetStatusBar(self.sb)
        self.SetStatusText(u"Welcome to PyLookInside !", 0)
        
    #-----------------------------------------------------------------------
        
    def createTaskBarIcon(self):
        self.tskic = TaskBarIcon.My_TaskBarIcon(self)
        
    #-----------------------------------------------------------------------
        
    def createNotebook(self):
        self.nb = Notebook.My_Notebook(self.pnl, -1)
        # Select initial items
        self.nb.SetSelection(0)
        
    #-----------------------------------------------------------------------
        
    def createAuiManager(self):
        self.mgr = wx.aui.AuiManager()
        self.mgr.SetManagedWindow(self.pnl)
        
        self.leftPanel = wx.Panel(self.pnl, style=wx.TAB_TRAVERSAL | wx.CLIP_CHILDREN)
    
        self.mgr.AddPane(self.nb, wx.aui.AuiPaneInfo().CenterPane().Name("Notebook"))
        
        self.mgr.AddPane(self.leftPanel,
                         wx.aui.AuiPaneInfo().
                         Left().Layer(0).BestSize((300, -1)).
                         MinSize((295, -1)).
                         FloatingSize((300, 160)).
                         Caption("Search").
                         CloseButton(False).
                         Name("ListCtrl"))
        
        self.mgr.Update()
        
        # self.mgr.SetFlags(self.mgr.GetFlags() ^ wx.aui.AUI_MGR_TRANSPARENT_DRAG)
        
    #-----------------------------------------------------------------------

    def createSearchCtrl(self):
        self.search = SearchCtrl.My_SearchCtrl(self.leftPanel)  # style=wx.TE_PROCESS_ENTER
        
#    def createSearchCtrl(self):
#        self.search = SearchCtrl.My_SearchCtrl(self.leftPanel, )leftPanel
#        self.search.SetFocus()

    #-----------------------------------------------------------------------
       
    def createListCtrl(self):
        self.list = ListCtrlVirtual.My_ListCtrl(self.leftPanel)
        
    #-----------------------------------------------------------------------
        
    def doLayout(self):
        listSizer = wx.BoxSizer(wx.VERTICAL)
        
        listSizer.Add(self.search, 0, wx.EXPAND | wx.ALL, 3)
        listSizer.Add(self.list, 1, wx.EXPAND | wx.ALL, 0)
        
        #----------
        
        self.leftPanel.SetAutoLayout(True)
        self.leftPanel.SetSizer(listSizer)
        listSizer.Fit(self.leftPanel)
        
        #----------
        
        self.pnl.SetAutoLayout(True)
        self.pnl.Fit()
        
    #-----------------------------------------------------------------------
        
    def OnFileOpen(self, event):
        self.fileOpen = FileDialog.My_FileDialog(self)
        
    #-----------------------------------------------------------------------
        
    def OnDisassemble(self, event):
        pass
     
    #-----------------------------------------------------------------------
    
    def OnAbout(self, event):
        self.notebook = AboutNotebook.My_AboutNotebook(self)
        
    #-----------------------------------------------------------------------   
        
    def OnMemento(self, event):
        self.memento = MementoProvider.My_Memento(self)
        
    #-----------------------------------------------------------------------
        
    def OnlineHelp(self, event):
        webbrowser.open_new("http://www.beaengine.org")
        
    #-----------------------------------------------------------------------
        
    def OnScreenShot(self, event):     
        """ Takes a screenshot of the screen at give pos & size (rect). """
        
        if wx.Platform == "__WXMAC__":
            # Created by John Torres and modify by Sigma
            # Works on Mac OSX ---------- To check

            rect = self.GetRect()
            if sys.platform == "linux2":
                # On mac, GetRect() returns size of client, not size of window.
                # Compensate for this
                client_x, client_y = self.ClientToScreen((0, 0))
                border_width = client_x - rect.x
                title_bar_height = client_y - rect.y
                # If the window has a menu bar, remove it from the title bar height.
                if self.GetMenuBar():
                    title_bar_height /= 2
                rect.width += (border_width * 2)
                rect.height += title_bar_height + border_width
            self.Raise()
            viewer_dc = wx.ScreenDC()
            bitmap = wx.EmptyBitmap(rect.width, rect.height-29)
            memory_dc = wx.MemoryDC()
            memory_dc.SelectObject(bitmap)
            memory_dc.Blit(0, 0, rect.width, rect.height-29, viewer_dc, rect.x, rect.y)
            memory_dc.SelectObject(wx.NullBitmap)
            image = bitmap.ConvertToImage()
            image.SaveFile("ScreenShots/Capture.png", wx.BITMAP_TYPE_PNG)
           
        elif wx.Platform == "__WXGTK__":
            # Created by John Torres and modify by Sigma
            # Works fine on Linux Ubuntu

            rect = self.GetRect()
            if sys.platform == "linux2":
                # On linux, GetRect() returns size of client, not size of window.
                # Compensate for this
                client_x, client_y = self.ClientToScreen((0, 0))
                border_width = client_x - rect.x
                title_bar_height = client_y - rect.y
                # If the window has a menu bar, remove it from the title bar height.
                if self.GetMenuBar():
                    title_bar_height /= 2
                rect.width += (border_width * 2)
                rect.height += title_bar_height + border_width
            self.Raise()
            viewer_dc = wx.ScreenDC()
            bitmap = wx.EmptyBitmap(rect.width, rect.height-29)
            memory_dc = wx.MemoryDC()
            memory_dc.SelectObject(bitmap)
            memory_dc.Blit(0, 0, rect.width, rect.height-29, viewer_dc, rect.x, rect.y)
            memory_dc.SelectObject(wx.NullBitmap)
            image = bitmap.ConvertToImage()
            image.SaveFile("ScreenShots/Capture.png", wx.BITMAP_TYPE_PNG)
            
        else:
            # Created by Andrea Gavana
            # Works fine on Windows XP, Vista and Seven
            # See http://aspn.activestate.com/ASPN/Mail/Message/wxpython-users/3575899

            rect = self.GetRect()
            
            # Create a DC for the whole screen area
            dcScreen = wx.ScreenDC()
            
            # Create a Bitmap that will hold the screenshot image later on
            # Note that the Bitmap must have a size big enough to hold the screenshot
            # -1 means using the current default colour depth
            bmp = wx.EmptyBitmap(rect.width, rect.height)
            
            # Create a memory DC that will be used for actually taking the screenshot
            memDC = wx.MemoryDC()
            
            # Tell the memory DC to use our Bitmap
            # all drawing action on the memory DC will go to the Bitmap now
            memDC.SelectObject(bmp)
            
            # Blit (in this case copy) the actual screen on the memory DC
            # and thus the Bitmap
            memDC.Blit( 0, # Copy to this X coordinate
                        0, # Copy to this Y coordinate
                        rect.width, # Copy this width
                        rect.height, # Copy this height
                        dcScreen, # From where do we copy ?
                        rect.x, # What's the X offset in the original DC ?
                        rect.y  # What's the Y offset in the original DC ?
                        )
            
            # Select the Bitmap out of the memory DC by selecting a new
            # uninitialized Bitmap
            memDC.SelectObject(wx.NullBitmap)
            
            img = bmp.ConvertToImage()
            fileName = "ScreenShots/Capture.png"
            img.SaveFile(fileName, wx.BITMAP_TYPE_PNG)
            
            
    #-----------------------------------------------------------------------
        
    def OnPass(self, event):
        pass
     
    #-----------------------------------------------------------------------
    
    def OnRoll(self, event):
        if self.isRolled == 1:
            return
        self.isRolled = 1
        
        self.pos1 = self.GetPosition()
        self.size1 = self.GetSize()
        
        if wx.Platform == "__WXMAC__":
            self.SetSize((-1, 23))
           
        elif wx.Platform == "__WXGTK__":
            self.SetSize((-1, 1))
            
        else:
            self.SetSize((-1, 0))
     
     
    def OnUnRoll(self, event):
        self.isRolled = 0
        
        self.pos2 = self.GetPosition()
        self.size2 = self.GetSize()
        
        if wx.Platform == "__WXMAC__":
            self.SetSize(self.size1)
            
        elif wx.Platform == "__WXGTK__":
            self.SetSize(self.size1)
            
        else:
            self.SetSize(self.size1)
     
    #-----------------------------------------------------------------------
        
    def OnToolsPalette(self, event):
        self.palette = Palette.My_MiniFrame(self, title="Palette")
        
    #-----------------------------------------------------------------------
        
    def OnClose(self, event):
        self.Close(True)
        
        
    def OnCloseWindow(self, event):
        dlg = wx.MessageDialog(self,
                               message=u"Do you really want to close this application ?",
                               caption=u"Confirm Exit",
                               style=wx.YES_NO | wx.ICON_QUESTION)
        
        if dlg.ShowModal() == wx.ID_YES:
            if self.tskic is not None:
                self.tskic.Destroy()
                
            self.sb.timer.Stop()
            del self.sb.timer
            self.Destroy()
            
        dlg.Destroy()
        
#---------------------------------------------------------------------------
      
class My_App(wx.App):
    def OnInit(self):
        
        # Create and show the splash screen.  It will then create 
        # and show the main frame when it is time to do so
        wx.SystemOptions.SetOptionInt("mac.window-plain-transition", 1)
        
        self.splash = SplashScreen.My_SplashScreenCustom()
        self.splash.Show()
        
        return True   
        
#---------------------------------------------------------------------------
        
def main():
    app = My_App(redirect=False)
    app.MainLoop()
        
#----------------------------------------------------------------------------
        
if __name__ == '__main__':
    __name__ = 'Main'
    main()
        
        
