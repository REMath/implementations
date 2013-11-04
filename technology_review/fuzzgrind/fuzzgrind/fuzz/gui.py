#!/usr/bin/env python

#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


# http://faq.pygtk.org/index.py?req=index


import gobject
import pango
import pygtk
pygtk.require('2.0')
import gtk
gtk.gdk.threads_init()

import os
import re
import sys
import time
import threading

import config
import fuzz
import graph


CONFIG_FILE = 'fuzz/settings.cfg'


class VboxWithProgressBar:
    '''Generic vertical box with a progress bar'''
    
    def __init__(self, gui):
        self.gui = gui
        
        self.vbox = gtk.VBox()
        
        self.progressbar = gtk.ProgressBar()
        self.vbox.pack_start(self.progressbar)
        
        self.clear()

    def init_progressbar(self, nb):
        '''
        Initialize progress bar
        @param nb_constraint: progress bar length (total fraction number)
        @type  nb_constraint: int
        '''
        
        self.nb = float(nb)
        self.current_state = 0
        self.progressbar.set_fraction(0.0)
        self.progressbar.set_text('%d/%d' % (self.current_state, int(self.nb)))
        self.start_time()
    
    def update_progressbar(self):
        '''Increment the progress bar status by one'''
        
        self.current_state += 1
        fraction = float(self.current_state) / self.nb
        self.progressbar.set_fraction(fraction)
        self.progressbar.set_text('%d/%d' % (self.current_state, int(self.nb)))
        
        if self.current_state == int(self.nb):
            self.stop_time()
    
    def start_time(self):
        self.init_time = time.time()
    
    def stop_time(self):
        stop_time = time.time()
        s = int(stop_time - self.init_time) % 60
        m = int(stop_time - self.init_time) / 60
        t = str(s)
        if m == 0:
            t = '%ds' % s
        else:
            t = '%dm%.02ds' % (m, s)
        if False: # turn it to True to view each step execution time
            self.progressbar.set_text('%s (%s)' % (self.progressbar.get_text(), t))
    
    def clear(self):
        '''Reset progress bar state'''
        
        self.progressbar.set_fraction(0.0)
        self.progressbar.set_text(' ')


class ConstraintSolver(VboxWithProgressBar):  
    def update_progressbar(self, input):
        '''Add new inputs to the result list and update hexdump'''
        
        VboxWithProgressBar.update_progressbar(self)
        if input:
            parent = self.gui.fuzzing_frame.ee.input.number
            # add new input to the result list
            gtk.gdk.threads_enter()
            self.gui.fuzzing_frame.r.liststore.append([input.number, parent, False, 0, False, 'white'])
            gtk.gdk.threads_leave()
            # add new input to the input list
            self.gui.fuzzing_frame.ee.inputs[input.number] = input
            # scroll to the last input
            if self.gui.setting_frame.check_autoscroll.get_active():
                self.gui.fuzzing_frame.r.treeview.scroll_to_cell(input.number)
            
            # update hexdump
            if self.gui.setting_frame.check_autohexdump.get_active():
                new = self.gui.fuzzing_frame.ee.inputs[input.number].filename
                parent = self.gui.fuzzing_frame.ee.inputs[parent].filename
                gtk.gdk.threads_enter()
                self.gui.hd_frame.update_buf(parent, new)
                gtk.gdk.threads_leave()


class Scorer(VboxWithProgressBar):        
    def update_progressbar(self, input):
        '''Update input score'''
        
        VboxWithProgressBar.update_progressbar(self)
        self.gui.fuzzing_frame.r.update_value(input.number, 3, input.note)


class FaultChecker(VboxWithProgressBar):        
    def update_progressbar(self, input_number, fault):
        '''Update fault status'''
        
        VboxWithProgressBar.update_progressbar(self)
        if fault:
            self.gui.fuzzing_frame.r.update_value(input_number, 4, True)
            self.gui.fuzzing_frame.r.update_value(input_number, 5, 'red')


class PulseProgressBar(threading.Thread):
    '''
    Progress bar having no accurate way of knowing the amount of work to do,
    update itself periodically
    '''
        
    def __init__(self, progressbar):
        threading.Thread.__init__(self)
        self.progressbar = progressbar
        self.stopthread = threading.Event()
    
    def run(self):
        self.progressbar.set_text(' ')
        while not self.stopthread.isSet():
            gtk.gdk.threads_enter()
            self.progressbar.pulse()
            gtk.gdk.threads_leave()
            time.sleep(0.1)
        self.progressbar.set_fraction(1.0)
            
    def stop(self):
        self.stopthread.set()


class ExecutionExpander(VboxWithProgressBar):
    def __init__(self, gui):
        VboxWithProgressBar.__init__(self, gui)
        self.inputs = { 0: fuzz.Input(0, fuzz.PARAM['INPUT_FILE'], fuzz.PARAM.get('MIN_BOUND', 0)) }

    def start_progressbar(self, input):
        self.gui.fuzzing_frame.ca.clear()
        self.gui.fuzzing_frame.cs.clear()
        self.gui.fuzzing_frame.fault_checker.clear()
        
        self.input = input
        self.gui.setting_frame.entry_input_number.set_text(str(input.number))
        
        self.gui.fuzzing_frame.input_scorer.clear()
        self.pg = PulseProgressBar(self.progressbar)
        self.start_time()
        self.pg.start()
    
    def stop_progressbar(self):
        self.stop_time()
        self.pg.stop()
        self.gui.fuzzing_frame.r.update_value(self.input.number, 2, True)

        
class Result:
    def __init__(self, gui):
        self.gui = gui
        
        self.liststore = gtk.ListStore(gobject.TYPE_INT, gobject.TYPE_INT, gobject.TYPE_BOOLEAN, gobject.TYPE_INT, gobject.TYPE_BOOLEAN, str)
        self.liststore.set_sort_column_id(0, gtk.SORT_ASCENDING)
        self.liststore.append([0, 0, False, 0, False, 'white'])
        
        self.treeview = gtk.TreeView(self.liststore)
        self.treeview.connect('cursor-changed', self.on_cursor_changed, None)
        
        renderer_toggle = gtk.CellRendererToggle()
        renderer_toggle.set_property('activatable', True)
        
        self.col_input = gtk.TreeViewColumn('Input', gtk.CellRendererText(), text=0, background=5)
        self.col_parent = gtk.TreeViewColumn('Parent', gtk.CellRendererText(), text=1)
        self.col_expanded = gtk.TreeViewColumn('Expanded', renderer_toggle, active=2)
        self.col_score = gtk.TreeViewColumn('Score', gtk.CellRendererText(), text=3)
        self.col_fault = gtk.TreeViewColumn('Fault', renderer_toggle, active=4)
        self.col_empty = gtk.TreeViewColumn(' ')
        
        # create columns and add callback to handle click on the header button
        columns = [ self.col_input, self.col_parent, self.col_expanded, self.col_score, self.col_fault, self.col_empty ]
        for column_id, col in enumerate(columns):
            col.connect('clicked', self.on_clicked, column_id)
            self.treeview.append_column(col)
        self.treeview.set_headers_clickable(True)
        
        self.sw = gtk.ScrolledWindow()
        self.sw.set_shadow_type(gtk.SHADOW_ETCHED_OUT)
        self.sw.set_policy(gtk.POLICY_NEVER, gtk.POLICY_AUTOMATIC)
        self.sw.add(self.treeview)
    
    def update_value(self, row, col, value):
        '''Update a value of a row'''
        
        gtk.gdk.threads_enter()
        sort_column_id, order = self.liststore.get_sort_column_id()
        self.liststore.set_sort_column_id(0, gtk.SORT_ASCENDING)
        
        treeiter = self.liststore.get_iter(row)
        self.liststore.set_value(treeiter, col, value)
        
        self.liststore.set_sort_column_id(sort_column_id, order)
        gtk.gdk.threads_leave()
        
    def on_clicked(self, column, column_id):
        '''
        Callback called on click on columns header. Change the sort column 
        id.
        '''
        
        sort_column_id, order = self.liststore.get_sort_column_id()
        if sort_column_id == column_id and order == gtk.SORT_ASCENDING:
            order = gtk.SORT_DESCENDING
        else:
            order = gtk.SORT_ASCENDING
        self.liststore.set_sort_column_id(column_id, order)
        
    def on_cursor_changed(self, a, b):
        '''
        Callback called on row selection. Update the hexdump frame corresponding
        to the selected row.
        '''
        
        selection = self.treeview.get_selection()
        (_, treeiter) = selection.get_selected()
        n = self.liststore.get_value(treeiter, 0)
        p = self.liststore.get_value(treeiter, 1)

        new = self.gui.fuzzing_frame.ee.inputs[n].filename
        parent = self.gui.fuzzing_frame.ee.inputs[p].filename

        self.gui.hd_frame.update_buf(parent, new)
    

class FuzzingFrame:
    def __init__(self, gui):
        self.ee = ExecutionExpander(gui)
        self.ca = VboxWithProgressBar(gui)
        self.cs = ConstraintSolver(gui)
        self.fault_checker = FaultChecker(gui)
        self.input_scorer = Scorer(gui)
        self.r = Result(gui)
    
        table = gtk.Table(rows=6, columns=2, homogeneous=False)
        table.set_row_spacings(5)
        table.set_col_spacings(10)
        
        # add labels
        for i, text in enumerate([ 'Execution Expander', 'Constraint Analysis', 'Constraint Solver', 'Fault Checker', 'Input Scorer' ]):
            align = gtk.Alignment(0, 0, 0, 0)
            label = gtk.Label(text)
            align.add(label)
            table.attach(align, 0, 1, i, i + 1, xoptions=gtk.FILL, yoptions=gtk.SHRINK)
        
        # add vbox with progress bar
        for i, element in enumerate([ self.ee, self.ca, self.cs, self.fault_checker, self.input_scorer ]):
            table.attach(element.vbox, 1, 2, i, i + 1, yoptions=gtk.SHRINK)
        
        table.attach(self.r.sw, 0, 2, 5, 6)
        
        # add padding between the frame and the scrolledwindow
        vbox = gtk.VBox(spacing=5)
        vbox.set_border_width(10) 
        vbox.pack_start(table, expand=True, fill=True)
        
        self.frame = gtk.Frame('Fuzzing')
        self.frame.add(vbox)
    

class SettingFrame:
    def __init__(self, gui, thread):
        self.gui = gui
        self.thread = thread
    
        table = gtk.Table(rows=7, columns=2, homogeneous=False)
        table.set_row_spacings(5)
        table.set_col_spacings(20)
        
        liststore = gtk.ListStore(gobject.TYPE_STRING)
        cell = gtk.CellRendererText()
        self.combobox_program = gtk.ComboBox(liststore)
        self.combobox_program.pack_start(cell, True)
        self.combobox_program.add_attribute(cell, 'text', 0)
        self.combobox_program.connect('changed', self.change_target)
        
        self.entry_fault_checker = gtk.Entry()
        self.entry_fault_checker.set_state(gtk.STATE_INSENSITIVE)
        
        self.entry_max_bound = gtk.Entry()
        self.entry_max_bound.set_state(gtk.STATE_INSENSITIVE)
        
        self.entry_input_number = gtk.Entry()
        self.entry_input_number.set_text('0')
        self.entry_input_number.set_state(gtk.STATE_INSENSITIVE)
        
        self.check_autoscroll = gtk.CheckButton()
        self.check_autoscroll.set_active(True)
        
        self.check_autohexdump = gtk.CheckButton()
        self.check_autohexdump.set_active(True)
        
        # initialize target list
        targets = config.get_targets(CONFIG_FILE)
        targets.sort()
        for i, t in enumerate(targets):
            liststore.append([ t ])
            if t == self.thread.target:
                self.combobox_program.set_active(i)

        # add labels
        settings = [ ('Target', self.combobox_program),
                     ('Fault Checker', self.entry_fault_checker),
                     ('Maximum bound', self.entry_max_bound),
                     ('Current input', self.entry_input_number),
                     ('Auto scroll', self.check_autoscroll),
                     ('Auto hexdump', self.check_autohexdump) ]
        for i, (label_text, entry) in enumerate(settings):
            align = gtk.Alignment(0, 0, 0, 0)
            label = gtk.Label(label_text)
            align.add(label)
            table.attach(align, 0, 1, i, i + 1, xoptions=gtk.FILL, yoptions=gtk.SHRINK)
            if entry:
                table.attach(entry, 1, 2, i, i + 1)
        
        # add control button
        control = gtk.Button(stock='gtk-media-play')
        control.get_children()[0].get_children()[0].get_children()[1].set_label('')
        control.connect('clicked', self.control)
        table.attach(control, 1, 2, 6, 7)
        self.running = False

        # add padding inside the frame
        vbox = gtk.VBox()
        vbox.set_border_width(10) 
        vbox.pack_start(table, expand=True, fill=True) 
        
        self.frame = gtk.Frame('Settings')
        self.frame.add(vbox)
    
    def control(self, widget, data=None):
        if not self.running:
            stock = 'gtk-media-pause'
            widget.set_image(gtk.image_new_from_pixbuf(widget.render_icon(stock, gtk.ICON_SIZE_BUTTON)))
            widget.stock = stock
            widget.set_label('')
            widget.set_sensitive(False)
            self.combobox_program.set_sensitive(False)
            self.thread.start()
        else:
            pass
        
        self.running = not self.running
        
    def change_target(self, widget, data=None):
        target = widget.get_active_text()
        fuzz.PARAM = config.get_config(CONFIG_FILE, target)
        
        self.entry_fault_checker.set_text(fuzz.PARAM['FAULT_CHECKER'].__name__[6:])
        self.entry_max_bound.set_text(str(fuzz.PARAM['MAX_BOUND']))
        if 'hd_frame' in dir(self.gui):
            filename = fuzz.PARAM['INPUT_FILE']
            self.gui.fuzzing_frame.ee.inputs[0].filename = filename
            self.gui.hd_frame.update_buf(filename, filename)
            self.thread.target = target
        
        
class HexdumpFrame:
    def __init__(self, gui):
        self.gui = gui
        
        view = gtk.TextView()
        self.view = view
        self.buffer = view.get_buffer()
        scrolled_window = gtk.ScrolledWindow()
        scrolled_window.set_policy(gtk.POLICY_NEVER, gtk.POLICY_AUTOMATIC)
        scrolled_window.set_shadow_type(gtk.SHADOW_ETCHED_OUT)
        scrolled_window.add(view)
        
        pangoFont = pango.FontDescription('monospace 10')
        view.modify_font(pangoFont)
        tag_reg = self.buffer.create_tag('fg_red', foreground='red')#, weight=pango.WEIGHT_BOLD)

        
        # add padding between the frame and the scrolledwindows
        vbox = gtk.VBox()
        vbox.set_border_width(10) 
        vbox.pack_start(scrolled_window, expand=True, fill=True)

        self.frame = gtk.Frame('Input Hexdump')
        self.frame.add(vbox)
        
        self.lock = False
        
        # dump first input
        filename = self.gui.fuzzing_frame.ee.inputs[0].filename
        self.update_buf(filename, filename)
    
    def update_buf(self, filename_orig, filename_new):
        if self.lock:
            return
        else:
            self.lock = True
        
        fp = open(filename_orig)
        orig = fp.read()
        fp.close()
        
        fp = open(filename_new)
        new = fp.read()
        fp.close()
        
        dump = self.hexdump(new)
        self.buffer.set_text(dump)

        # highlight differences
        assert len(new) <= len(orig)
        for i in range(0, len(new)):
            if new[i] != orig[i]:
                self.highlight_diff(i)
        
        try:
            input_number = int(re.findall('/(\d+)', filename_new)[-1])
        except IndexError:
            input_number = 0
        self.frame.set_label('Hexdump of input #%d' % input_number)
        self.lock = False
    
    def hexdump(self, source, width=16, verbose=0):
        '''http://nedbatchelder.com/code/utilities/hexdump.py'''
        
        def ascii(x):
            if 32 <= x <= 126: return chr(x)
            else: return '.'
        ascmap = [ ascii(x) for x in range(256) ]
        
        pos = 0
        lastbuf, lastline, result = '', '', ''
        spaceCol = width // 2
        hexwidth = 3 * width  + 1
            
        for i in range(0, len(source), width):
            buf = source[i:i+width]

            if len(buf) == 0:
                return result
       
            hex, asc = '', ''
            for i, c in enumerate(buf):
                if i == spaceCol:
                    hex = hex + ' '
                hex = hex + ('%02x' % ord(c)) + ' '
                asc = asc + ascmap[ord(c)]
            line = '%04x  %-*s |%s|\n' % (pos, hexwidth, hex, asc)

            result += line
                
            pos = pos + len(buf)
            lastbuf = buf
            lastline = line
            
        return result
        
    def highlight_diff(self, i):
        # hexadecimal values
        offset = (i / 16) * 75
        offset += 6 + (i % 16) * 3
        if (i % 16) >= 8:
            offset += 1
        iter_start = self.buffer.get_iter_at_offset(offset)
        iter_end = self.buffer.get_iter_at_offset(offset + 2)
        self.buffer.apply_tag_by_name('fg_red', iter_start, iter_end)
        
        # ascii values
        offset = (i / 16) * 75
        offset += 57 + (i % 16)
        iter_start = self.buffer.get_iter_at_offset(offset)
        iter_end = self.buffer.get_iter_at_offset(offset + 1)
        self.buffer.apply_tag_by_name('fg_red', iter_start, iter_end)
    

class GraphFrame:
    def __init__(self, gui):        
        self.graph = graph.Graph()

        # add padding inside the frame
        vbox = gtk.VBox()
        vbox.set_border_width(10) 
        vbox.pack_start(self.graph, expand=True, fill=True) 
        
        self.frame = gtk.Frame('Graph')
        self.frame.add(vbox)


class Gui:
    def __init__(self, thread):
        self.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self.window.set_default_size(1024, 768)
        self.window.connect('destroy', self.destroy)
        self.window.set_border_width(10)
        #self.window.maximize()
    
        table = gtk.Table(2, 2)
        table.set_row_spacings(10)
        table.set_col_spacings(10)
        self.window.add(table)

        # settings and fuzzing
        self.fuzzing_frame = FuzzingFrame(self)
        self.setting_frame = SettingFrame(self, thread)
        vbox = gtk.VBox(spacing=10)
        vbox.pack_start(self.setting_frame.frame, expand=False)
        vbox.pack_start(self.fuzzing_frame.frame, expand=True, fill=True)
        table.attach(vbox, 0, 1, 0, 2, xoptions=gtk.FILL|gtk.EXPAND)
        
        show_graph = False
        
        # input graph
        self.graph_frame = GraphFrame(self)
        if show_graph:
            table.attach(self.graph_frame.frame, 1, 2, 0, 1, xoptions=gtk.SHRINK|gtk.FILL)

        # hexdump
        self.hd_frame = HexdumpFrame(self)
        table.attach(self.hd_frame.frame, 1, 2, int(show_graph), 2, xoptions=gtk.SHRINK)
        
        self.window.show_all()
        
        '''image = 'fuzz/background.jpg'
        pixbuf = gtk.gdk.pixbuf_new_from_file_at_size(image,gtk.gdk.screen_width(), gtk.gdk.screen_height())
        pixbuf = pixbuf.scale_simple(gtk.gdk.screen_width(), gtk.gdk.screen_height(), gtk.gdk.INTERP_BILINEAR)
        pixmap, mask = pixbuf.render_pixmap_and_mask()
        view = self.hd_frame.view
        tv_win = view.get_window(gtk.TEXT_WINDOW_TEXT)
        tv_win.set_back_pixmap(pixmap, False)'''
        
    def destroy(self, widget, data=None):
        gtk.main_quit()

    def main(self):
        gtk.main()
        sys.exit(0)


class MyThread(threading.Thread):
    def __init__(self,):
        super(MyThread, self).__init__()
        if len(sys.argv) > 1:
            self.target = sys.argv[1]
        else:
            self.target = 'test'
        fuzz.DEBUG_LAST             = False
        fuzz.VERIF_SOLVABLE         = False
        fuzz.CONSTRAINT_SUBSUMPTION = False
        fuzz.PARAM = config.get_config(CONFIG_FILE, self.target)
    def run(self):
        fuzz.ninput = fuzz.PARAM.get('N', 0)
        input_seed = fuzz.Input(0, fuzz.PARAM['INPUT_FILE'], fuzz.PARAM['MIN_BOUND'])
        self.worklist = [ input_seed ]

        fuzz.search(self.target, self.worklist, [
            self.gui.fuzzing_frame.cs.init_progressbar,
            self.gui.fuzzing_frame.cs.update_progressbar,
            self.gui.fuzzing_frame.ca.init_progressbar,
            self.gui.fuzzing_frame.ca.update_progressbar,
            self.gui.fuzzing_frame.ee.start_progressbar,
            self.gui.fuzzing_frame.ee.stop_progressbar,
            self.gui.fuzzing_frame.input_scorer.init_progressbar,
            self.gui.fuzzing_frame.input_scorer.update_progressbar,
            self.gui.fuzzing_frame.fault_checker.init_progressbar,
            self.gui.fuzzing_frame.fault_checker.update_progressbar,
            None ])


if __name__ == '__main__':
    t = MyThread()
    gui = Gui(t)
    
    t.gui = gui
    
    gui.main()
