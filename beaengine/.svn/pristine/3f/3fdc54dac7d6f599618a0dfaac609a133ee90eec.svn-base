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
import os
import sys
import platform
import time
import PyLookInside
import VersionInfos

#import wx.animate as ani

#---------------------------------------------------------------------------

#class BoutonAnime(wx.Window):
#    def __init__(self, parent, image):
#        wx.Window.__init__(self, parent, -1, style=wx.BORDER_NONE)
        
#        self.image = image
#        animation = ani.Animation(self.image)
#        self.ctrl = ani.AnimationCtrl(self, -1, animation)
#        self.ctrl.Play()

#        # Bind the size event to an events handler
#        self.Bind(wx.EVT_SIZE, self.OnSize)
        
        
#    def OnSize(self, event):
#        w, h = self.ctrl.GetSizeTuple()
#        taille = wx.Size(w, h)
#        taille = wx.Size(w+1, h+1)
#        self.SetSize(taille)
#        self.SetPosition((436, 3))
#        self.ctrl.CentreOnParent()
        
#---------------------------------------------------------------------------

class My_SplashScreenCustom(wx.Frame):
    def __init__(self, tempo=2):
        self.tempo = tempo
        
        wx.Frame.__init__(self, None, -1,
                          style=wx.FRAME_SHAPED | wx.SIMPLE_BORDER |
                          wx.STAY_ON_TOP | wx.FRAME_NO_TASKBAR)
        
        self.hasShaped = False
        
        self.bmp = wx.Bitmap("Bitmaps/splashScreen.png", wx.BITMAP_TYPE_PNG)
#        self.btn = BoutonAnime(self, "Bitmaps/loading.ani")
        
        self.SetClientSize((self.bmp.GetWidth(), self.bmp.GetHeight()))
        
        dc = wx.ClientDC(self)
        dc.DrawBitmap(self.bmp, 0, 0, True)
        self.SetWindowsShape()
        
        self.SetTransparent(240)
        
        self.timer = wx.Timer(self)
        self.Bind(wx.EVT_TIMER, self.TimeOut)
        
        self.fc = wx.FutureCall(1500, self.ShowMain)
        
        # Bind some events to an events handler
        self.Bind(wx.EVT_PAINT, self.OnPaint)
        self.Bind(wx.EVT_WINDOW_CREATE, self.SetWindowsShape)
        self.Bind(wx.EVT_CLOSE, self.OnClose)
        
        self.CentreOnScreen(wx.BOTH)
        
    #-----------------------------------------------------------------------
        
    def OnClose(self, event):
        # Make sure the default handler runs too so
        # this window gets destroyed
        event.Skip()
        self.Hide()
        
        # If the timer is still running then go
        # ahead and show the main frame now
        if self.fc.IsRunning():
            self.fc.Stop()
            self.ShowMain()
            
    #-----------------------------------------------------------------------
            
    def TimeOut(self, event):
        self.Close()
        
    #-----------------------------------------------------------------------
        
    def SetWindowsShape(self, event=None):
        region = wx.RegionFromBitmap(self.bmp)
        self.hasShaped = self.SetShape(region)
        
    #-----------------------------------------------------------------------
        
    def OnPaint(self, event):
        dc = wx.PaintDC(self)
        dc.DrawBitmap(self.bmp, 0, 0, True)
        
        if self.tempo>0:
            self.timer.Start(self.tempo * 1000, True)
            
        #-------------------------------------------------------------------
            
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":
            self.normalBoldFont = wx.Font(fontSize-3,
                                          wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            self.normalFont = wx.Font(fontSize-3, wx.
                                      DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        elif wx.Platform == "__WXGTK__":
            self.normalBoldFont = wx.Font(fontSize-2,
                                          wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            self.normalFont = wx.Font(fontSize-2,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
              
        else:
            self.normalBoldFont = wx.Font(fontSize+0,
                                          wx.DEFAULT, wx.NORMAL, wx.BOLD, False, "")
            self.normalFont = wx.Font(fontSize+0,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
       
        dc.SetFont(self.normalBoldFont)
        dc.SetFont(self.normalFont)
        
        #-------------------------------------------------------------------
        
        dc.SetTextForeground(wx.BLACK)
        dc.SetFont(self.normalBoldFont)
        
        dc.DrawText(u"%s" % VersionInfos.LICENSE1_STRING, 50, 160)

        dc.SetFont(self.normalFont)
        dc.DrawText(u"%s" % VersionInfos.LICENSE2_STRING, 50, 190)
        dc.DrawText(u"%s" % VersionInfos.LICENSE3_STRING, 50, 205)
        dc.DrawText(u"%s" % VersionInfos.LICENSE4_STRING, 50, 220)
        dc.DrawText(u"%s" % VersionInfos.COPYRIGHT_STRING, 50, 235)


        dc.DrawText(u"PyLookInside was built using Python "
                    + sys.version.split()[0] + ",", 50, 260)
        dc.DrawText(u"wxPython "
                    + wx.VERSION_STRING + u" unicode" +
                    u" and wxWindows.", 50, 275)
        dc.DrawText(u"%s" % VersionInfos.OS_STRING
                    + platform.system() + u" "
                    + platform.win32_ver()[1], 50, 300)
        # dc.DrawText(u"Python %s" % sys.version.split()[:6], 50, 285)
        # dc.DrawText(u"Python %s" % sys.version.split()[6:], 50, 300)
        
    #-----------------------------------------------------------------------
        
    def ShowMain(self):
        self.frame = PyLookInside.My_Frame(None, -1)
        
        frameicon = wx.Icon("Icons/icon_App.ico", wx.BITMAP_TYPE_ICO)
        self.frame.SetIcon(frameicon)
       
        self.frame.Show(True)
        
        if self.fc.IsRunning():
            self.Raise()
        
        
