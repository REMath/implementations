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
import wx.html
import VersionInfos

text = u"""<html><body><div align="center">
<br>
<br>
<h3><font color="#d52c00"><b>PyLookInside %(version)s</h3></font>
<p><i>wxPython GUI for disassembling library...</i>
<br>
<br>
<p><b>&copy; Copyright 2009-2010.</b></p>
<br>
<p><b>Sweet Home : </b>
<a href="http://www.beaengine.org">BeaEngine</a></p>
<br>
<p>License GNU-LGPL version 3.</div></body></html>"""

#---------------------------------------------------------------------------

class HtmlWindow(wx.html.HtmlWindow):
    def __init__(self, parent):
        wx.html.HtmlWindow.__init__(self, parent, style=wx.BORDER_THEME)
        
        if "gtk2" in wx.PlatformInfo:
            self.SetStandardFonts()
        
        
    def OnLinkClicked(self, link):
        wx.LaunchDefaultBrowser(link.GetHref())
        
#---------------------------------------------------------------------------
        
class PageCopyright(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        html = HtmlWindow(self)
        vers = {}
        vers["version"] = VersionInfos.VERSION_STRING
        html.SetPage(text % vers)
        
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(html, 1, wx.EXPAND, 0)
        
        self.SetSizer(sizer)
        sizer.Fit(self)
        
    def OnLinkClicked(self, link):
        wx.LaunchDefaultBrowser(link.GetHref())
        
#---------------------------------------------------------------------------
        
class PageLicence(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        #-------------------------------------------------------------------
        
        self.filename = u"License/lgpl.txt"
        self.dirname = u"."
        
        #-------------------------------------------------------------------
        
        fontSize = self.GetFont().GetPointSize()
        
        # wx.Font(pointSize, family, style, weight, underline, faceName)
        if wx.Platform == "__WXMAC__":   
            self.normalFont = wx.Font(fontSize+0,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
        
        elif wx.Platform == "__WXGTK__":
            self.normalFont = wx.Font(fontSize-1,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
        
        else:
            self.normalFont = wx.Font(fontSize+2,
                                      wx.DEFAULT, wx.NORMAL, wx.NORMAL, False, "")
        
        self.SetFont(self.normalFont)
        
        #-------------------------------------------------------------------
        
        self.field = wx.TextCtrl(self, -1, value=u"", size=(100, 165),
                                 style=wx.TE_LEFT | wx.TE_MULTILINE |
                                 wx.TE_READONLY | wx.BORDER_THEME)
        
        self.field.SetFont(self.normalFont)
        self.field.SetSize(self.field.GetBestSize())
     
        filename = open(os.path.join(self.dirname, self.filename), "r")
        text_in = filename.read()
        filename.close()
        
        hello_in = text_in.decode("utf-8", "ignore")
        self.field.SetValue(hello_in)
        
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(self.field, 1, wx.EXPAND, 0)
        
        self.SetSizer(sizer)
        sizer.Fit(self)
        
#---------------------------------------------------------------------------
        
class PageDevelopers(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        html = HtmlWindow(self)
        html.SetPage(u'''<html><body><div align="left">
        <br>
        <br>
        <p><b>● BeatriX</b> <i>(original library developer)</i>
        <br>
        <br><b>● Igor Gutnik</b> <i>(he has ported the entire project under linux </i>
        <br><i>and he has render this library available on many platforms)</i>
        <br>
        <br><b>● JCie</b> <i>(PyLookInside GUI developer)</i>
        <p></div></body></html>''')
        
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(html, 1, wx.EXPAND, 0)
        
        self.SetSizer(sizer)
        sizer.Fit(self)
        
#---------------------------------------------------------------------------

class PageContributors(wx.Panel):
    def __init__(self, parent):
        wx.Panel.__init__(self, parent)
        
        html = HtmlWindow(self)
        html.SetPage(u'''<html><body><div align="left">
        <br>
        <br>
        <p>Contributors have done a very useful job to improve and to
        fix bugs on BeaEngine. Thanks to them, BeaEngine is stable and
        efficient.</p>
        <br>
        <p><b><u>List below :</u></b></p>
        <br>
        <p><b><i>andrewl, Ange Albertini, bax, William Pomian, Pyrae,
        Vincent Roy, Kharneth, Eedy, Neitsa, KumaT, Rafal Cyran,
        29a metal, sessiondiy, Tim, vince, ouadji, Helle.</i></b></p>
        <p></div></body></html>''')
        
        sizer = wx.BoxSizer(wx.HORIZONTAL)
        sizer.Add(html, 1, wx.EXPAND, 0)
        
        self.SetSizer(sizer)
        sizer.Fit(self)
        
#---------------------------------------------------------------------------
        
class My_AboutNotebook(wx.Dialog):
    def __init__(self, parent):
        wx.Dialog.__init__(self, parent, -1,
                           title=u"About...", size=(500, 400))
        
        # Bind the close event to an events handler
        self.Bind(wx.EVT_CLOSE, self.OnCloseWindow)
        
        #-------------------------------------------------------------------
        
        bmp = wx.Bitmap("Bitmaps/copyright_Header.png", wx.BITMAP_TYPE_PNG)
        img = wx.StaticBitmap(self, -1)
        img.SetBitmap(bmp)
        
        #-------------------------------------------------------------------
        
        notebook = wx.Notebook(self)
        
        page1 = PageCopyright(notebook)
        page2 = PageLicence(notebook)
        page3 = PageDevelopers(notebook)
        page4 = PageContributors(notebook)
        
        notebook.AddPage(page1, u"Copyright")
        notebook.AddPage(page2, u"License")
        notebook.AddPage(page3, u"Developers")
        notebook.AddPage(page4, u"Contributors")
        
        #-------------------------------------------------------------------
        
        btnOK = wx.Button(self, id=wx.ID_OK, label=u"&OK")
        btnOK.SetFocus()
        
        # Bind the button event to an events handler
        self.Bind(wx.EVT_BUTTON, self.OnOK, btnOK)
        
        #-------------------------------------------------------------------
        
        imgSizer = wx.BoxSizer(wx.VERTICAL)
        imgSizer.Add(img, 0, wx.EXPAND | wx.TOP |
                     wx.ALIGN_CENTER_HORIZONTAL)
        
        #------------
        
        notebookSizer = wx.BoxSizer(wx.VERTICAL)
        btnSizer = wx.BoxSizer(wx.VERTICAL)
        
        notebookSizer.Add(notebook, 1, wx.TOP | wx.EXPAND, 15)
        btnSizer.Add(btnOK, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, 10)
        
        #------------
        
        topSizer = wx.BoxSizer(wx.VERTICAL)
        topSizer.Add(imgSizer, 0, wx.EXPAND, 0)        
        topSizer.Add(notebookSizer, 1, wx.EXPAND, 0)
        topSizer.Add(btnSizer, 0, wx.ALIGN_RIGHT)
        
        #------------
        
        self.SetAutoLayout(True)
        self.SetSizer(topSizer)
        
        #-------------------------------------------------------------------
        
        self.CenterOnParent(wx.BOTH)
        
        btnOK = self.ShowModal()
        
    #-----------------------------------------------------------------------
        
    def OnCloseWindow(self, event):
        self.Destroy()
        
        
    def OnOK(self, event):
        self.EndModal(False)
        
        
