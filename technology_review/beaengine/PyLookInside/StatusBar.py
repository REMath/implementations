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
import time
import locale

#---------------------------------------------------------------------------

class My_CustomStatusBar(wx.StatusBar):
    def __init__(self, parent):
        wx.StatusBar.__init__(self, parent, -1)
        
        #-------------------------------------------------------------------
        
        self.parent = parent
        
        #-------------------------------------------------------------------
        
        self.SetFieldsCount(2)
        self.SetStatusWidths([-7, -3])
        
        #-------------------------------------------------------------------
        
        self.sizeChanged = False
        
        # Bind some events to an events handler
        self.Bind(wx.EVT_SIZE, self.OnSize)
        self.Bind(wx.EVT_IDLE, self.OnIdle)
        
        #-------------------------------------------------------------------
        
        self.timer = wx.PyTimer(self.Notify)
        # Update every 1000 milliseconds
        self.timer.Start(1000)
        self.Notify()
        
    #-----------------------------------------------------------------------
        
    # Handles events from the timer we started in __init__().
    # We're using it to drive a 'clock' in field 2.
    def Notify(self):
        """ Timer event. """
        
        locale.setlocale(locale.LC_ALL,"")
        tm = time.strftime("%a %d %b %Y - %Hh%M")
        
        self.SetStatusText(tm, 1)
        
        
    def OnSize(self, evt):
        self.Reposition()  # For normal size events
        
        # Set a flag so the idle time handler will also do the repositioning.
        # It is done this way to get around a buglet where GetFieldRect is not
        # accurate during the EVT_SIZE resulting from a frame maximize.
        self.sizeChanged = True
        
        
    def OnIdle(self, evt):
        if self.sizeChanged:
            self.Reposition()
            
            
    def Reposition(self):
        self.sizeChanged = False
        
        
