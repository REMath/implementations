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
import wx.lib.mixins.listctrl  as  listmix

#---------------------------------------------------------------------------

class My_ListCtrl(wx.ListCtrl,
                  listmix.ListCtrlAutoWidthMixin,
                  listmix.ColumnSorterMixin):
     
    def __init__(self, parent):
        wx.ListCtrl.__init__(self, parent, -1,
                             style=wx.LC_REPORT | wx.LC_VIRTUAL |
                             wx.LC_SORT_ASCENDING | wx.LC_SINGLE_SEL |
                             wx.LC_VRULES | wx.BORDER_SUNKEN)
        
        listmix.ListCtrlAutoWidthMixin.__init__(self)
        listmix.ColumnSorterMixin.__init__(self, 2)
       
        #-------------------------------------------------------------------
        
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":
            self.normalFont = wx.Font(fontSize-2,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        elif wx.Platform == "__WXGTK__":
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        else:
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
            
        self.SetFont(self.normalFont)
        
        #-------------------------------------------------------------------
        
        self.il = wx.ImageList(16, 16)
        
        bmp = wx.Bitmap("Bitmaps/listCtrl_Icon.png", wx.BITMAP_TYPE_PNG)
        self.idx1 = self.il.Add(bmp)
        
        bmp1 = wx.Bitmap("Bitmaps/small_Up_Arrow.png", wx.BITMAP_TYPE_PNG)
        self.sm_up = self.il.Add(bmp1)
        
        bmp2 = wx.Bitmap("Bitmaps/small_Dn_Arrow.png", wx.BITMAP_TYPE_PNG)
        self.sm_dn = self.il.Add(bmp2)
        
        self.SetImageList(self.il, wx.IMAGE_LIST_SMALL)
        
        #-------------------------------------------------------------------
        
        self.InsertColumn(0, u"Offset", wx.LIST_FORMAT_LEFT, width=wx.LIST_AUTOSIZE)  # width=90
        self.InsertColumn(1, u"Value", wx.LIST_FORMAT_LEFT, width=100)  # width=wx.LIST_AUTOSIZE
        
        #-------------------------------------------------------------------
        
        self.SetItemCount(201)
        
        #-------------------------------------------------------------------
        
        self.SetForegroundColour("#6a6a66")
        
        self.attributeColor = wx.ListItemAttr()
        self.attributeColor.SetBackgroundColour(wx.WHITE)  # wx.Colour(220, 225, 228)

        #-------------------------------------------------------------------
        
        self.SortListItems(0, True)
        
        #-------------------------------------------------------------------
        
        self.SetItemState(0, wx.LIST_STATE_SELECTED, wx.LIST_STATE_SELECTED)
        
        #-------------------------------------------------------------------
        
        # Bind some events to an events handler
        self.Bind(wx.EVT_LIST_ITEM_SELECTED, self.OnItemSelected)
        self.Bind(wx.EVT_LIST_ITEM_ACTIVATED, self.OnItemActivated)
        self.Bind(wx.EVT_LIST_COL_CLICK, self.OnColClick)
        
    #-----------------------------------------------------------------------
        
    def OnColClick(self,event):
        event.Skip()
        
        
    def OnItemSelected(self, event):
        self.currentItem = event.m_itemIndex
        
        
    def OnItemActivated(self, event):
        self.currentItem = event.m_itemIndex
        
        
    def getColumnText(self, index, col):
        item = self.GetItem(index, col)
        return item.GetText()
     
    #---------------------------------------------------
    # These methods are callbacks for implementing the
    # "virtualness" of the list...  Normally you would
    # determine the text, attributes and/or image based
    # on values from some external data source, but for
    # this demo we'll just calculate them
    def OnGetItemText(self, item, col):
        return "Item %d, column %d" % (item, col)
        
     
    def OnGetItemImage(self, item):
        if item % 1 == 0:
            return self.idx1
        else:
            return -1
        
        
    def OnGetItemAttr(self, item):
        if item % 1 == 0:
            return self.attributeColor
        else:
            return None
        
        
    def GetListCtrl(self):
        return self
        
     
    def GetSortImages(self):
        return (self.sm_dn, self.sm_up)
    
#---------------------------------------------------------------------------
     
class VirtualListPanel1(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent, -1, style=wx.WANTS_CHARS)
        
        sizer = wx.BoxSizer(wx.VERTICAL)
        
        self.list = My_ListCtrl(self)
        sizer.Add(self.list, 1, wx.EXPAND)
        
        self.SetSizer(sizer)
        self.SetAutoLayout(True)
        
        
