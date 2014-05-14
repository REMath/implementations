#!/usr/bin/env python

#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.

import gtk
import math


HBOX   = 20
WBOX   = 20
HSPACE = 50 / 2
WSPACE = 10 / 2
RADIUS = 10

NOT_EXECUTED = 0
EXECUTED     = 1
EXECUTING    = 2

BORDER_COLOR = {
    NOT_EXECUTED: (0.7, 0.7, 0.7),
    EXECUTED:     (0, 0, 0),
    EXECUTING:    (0, 0, 1)
}

BACKGROUND_COLOR = {
    NOT_EXECUTED: (0.9, 0.9, 0.9),
    EXECUTED:     (1, 1, 1),
    EXECUTING:    (0.925, 0.925, 1)
}
        

class Block:
    def __init__(self, status=EXECUTED):
        self.x = self.y = 0
        self.links = []
        self.status = status
    
    def add_link(self, condition):
        self.links.append(condition)
    
    def draw_box(self, context, x, y):
        bg_color = BACKGROUND_COLOR[self.status]
        bd_color = BORDER_COLOR[self.status]
        
        context.rectangle(x + 0.5, y + 0.5, WBOX, HBOX)
        context.set_source_rgb(*bg_color)
        context.fill_preserve()
        context.set_source_rgb(*bd_color)
        context.stroke()
    
    def draw_link(self, context, condition):
        context.set_source_rgb(0, 0, 0)
        context.move_to(self.x + WBOX / 2 + 0.5, self.y + HBOX + 0.5)
        context.line_to(condition.x + 0.5, condition.y + 0.5)
        context.stroke()
    
    def move(self, context, x, y=0):
        self.x += x
        self.y += y
        
        for c in self.links:
            c.move(x, y)
    
    def draw(self, context, x, y):
        self.x = x
        self.y = y
        self.draw_box(context, x, y)
        
        # draw a link to each condition
        for c in self.links:
            c.draw(context, x + WBOX / 2, y + HBOX + HSPACE)
            self.draw_link(context, c)
        

class Condition:
    def __init__(self, taken, l, r):
        self.x = self.y = 0
        self.l = l
        self.r = r
    
    def draw_circle(self, context, x, y):
        context.arc(x + 0.5, y + 0.5, RADIUS, 0, 2 * math.pi)
        context.set_source_rgb(1, 1, 1)
        context.fill_preserve()
        context.set_source_rgb(0, 0, 0)
        context.stroke()
    
    def draw_link(self, context, block):
        color = BORDER_COLOR[block.status]
        context.set_source_rgb(*color)
        context.move_to(self.x + 0.5, self.y + 0.5)
        context.line_to(block.x + 0.5 + WBOX / 2, block.y + 0.5)
        context.stroke()
    
    def draw(self, context, x, y):
        self.x = x
        self.y = y
        
        y += RADIUS / 2 + HSPACE
        self.l.draw(context, x - (WBOX / 2 + WSPACE + WBOX), y)
        self.r.draw(context, x - (WBOX / 2) + WSPACE + WBOX, y)
        self.draw_link(context, self.l)
        self.draw_link(context, self.r)
        
        self.draw_circle(context, self.x, self.y)
                

class Graph(gtk.DrawingArea):
    def __init__(self):
        self.root       = Block()
        self.blocks     = []
        self.conditions = {}
        self.current    = self.root
        
        gtk.DrawingArea.__init__(self)
        self.set_size_request(640, 480) # XXX - comment me
        self.connect("expose_event", self.expose)
        
        self.add_condition(0x0804861a, True)
        self.current = self.root
        self.add_condition(0x0804861e, False)
        
    def expose(self, widget, event):
        self.context = widget.window.cairo_create()
        self.context.rectangle(event.area.x, event.area.y, event.area.width, event.area.height)
        self.context.clip()
        self.context.set_line_width(1)
        self.draw(self.context)
        
        return False
    
    def add_condition(self, address, taken):
        '''
        Create a new condition, linked to 2 code blocks. If condition already 
        exists, link it to the taken block.
        '''
        if address not in self.conditions.keys():
            n1 = Block()
            n2 = Block()
            c = Condition(taken, n1, n2)
            self.conditions[address] = c
            self.current.add_link(c)
            if taken:
                self.current = n1
            else:
                self.current = n2
        else:
            c.set_link()
    
    def draw(self, context):
        self.root.draw(context, (640 - WBOX) / 2, 10)
        
        return False
        

def main():
    window = gtk.Window()
    g = Graph()
    
    window.add(g)
    window.connect("destroy", gtk.main_quit)
    window.show_all()
    
    gtk.main()
    
if __name__ == "__main__":
    main()
