#!/usr/bin/env python3

from tkinter import *
import threading
import math
import time

CANVAS_HEIGHT = 720
CANVAS_WIDTH  = 1280

ANIMATION_STEP  = 0.001
ANIMATION_SPEED = 5

def parametrized_equaiton_factory(Vx0, Vy0, x0, y0, alpha):
    def function(t):
        if alpha == 0:
            return (Vx0*t + x0 + CANVAS_WIDTH/2, Vy0*t + y0 + CANVAS_HEIGHT/2)
        return (Vx0/alpha*math.sin(alpha*t) + x0*math.cos(alpha*t) + CANVAS_WIDTH/2,
                Vy0/alpha*math.sin(alpha*t) + y0*math.cos(alpha*t) + CANVAS_HEIGHT/2)
    return function 


class App(Tk):

    def __init__(self):
        Tk.__init__(self)
        self.title('Task 11.1 model')
        self.protocol('WM_DELETE_WINDOW', self.__on_exit)
        self.configure()


        canvas = Canvas(self, width=CANVAS_WIDTH, height=CANVAS_HEIGHT)
        canvas.pack(side=TOP, expand=False)
        self.canvas = canvas

        bot_frame = Frame(self)
        bot_frame.pack()

        bot_left_frame = Frame(bot_frame)
        bot_left_frame.pack(side=LEFT, fill=X)

        bot_right_frame = Frame(bot_frame)
        bot_right_frame.pack(side=RIGHT, fill=X)

        def labeled_slider(parent, text, command, from_, to):
            t = StringVar()
            t.set(text)
            
            f = Frame(parent)
            f.pack()

            label = Label(f, textvariable=t)
            label.pack(side=LEFT)

            slider = Scale(f, from_=from_, to=to, orient=HORIZONTAL, command=command, length=300)
            slider.pack(side=RIGHT)

            return slider

        self.params = {}
        self.params['Vx0'] = (1, -200, 200)
        self.params['Vy0'] = (1, -200, 200)
        self.params['y0'] = (1, -CANVAS_HEIGHT//2, CANVAS_HEIGHT//2)
        self.params['x0'] = (1, -CANVAS_WIDTH//2, CANVAS_WIDTH//2)
        self.params['speed'] = (1, 1, 50)
        self.params['a'] = (1, 0, 100)

        def create_sliders(parent, texts):
            for t in texts:
                def handler(t):
                    return lambda e: self.__handle_param(t, e)

                slider = labeled_slider(parent, t, handler(t), self.params[t][1], self.params[t][2])
                slider.set(self.params[t][0])
                self.__dict__[t + '_slider'] = slider

        create_sliders(bot_left_frame, ['Vx0', 'Vy0', 'a'])
        create_sliders(bot_right_frame, ['x0', 'y0', 'speed'])

    def __handle_param(self, param, e):
        global ANIMATION_SPEED

        self.params[param] = (float(e), self.params[param][1], self.params[param][2])
        ANIMATION_SPEED = self.params['speed'][0]
        self.__restart_animation()
            
    def __restart_animation(self):
        self.animation.stop()
        self.canvas.delete('all')
        self.__run_animation()

    def __run_animation(self):
        function = parametrized_equaiton_factory(self.params['Vx0'][0],
                                                 self.params['Vy0'][0],
                                                 self.params['x0'][0],
                                                 self.params['y0'][0],
                                                 self.params['a'][0])
        
        animation = AnimationTask(self.canvas, function)
        animation.start()

        self.animation = animation
    
    def run(self):
        self.__run_animation()
        self.mainloop()

    def __on_exit(self):
        self.animation.stop()
        self.destroy()

class AnimationTask(threading.Thread):

    def __init__(self, canvas, function):
        threading.Thread.__init__(self)
        self.canvas = canvas
        self.function = function
        self.t = 0;
        self.last_point = function(self.t)
        self.point = self.__draw_point(*self.last_point, color='#ffff00')
        self.stopped = False

    def run(self):
        self.__draw_point(CANVAS_WIDTH//2, CANVAS_HEIGHT//2)

        while not self.stopped:
            self.t += ANIMATION_STEP*ANIMATION_SPEED
            new_point = self.function(self.t)
            
            self.canvas.create_line(*self.last_point, *new_point, width=1, fill='#0000ff')
            self.__update_point(*new_point, self.point)

            self.last_point = new_point
            time.sleep(ANIMATION_STEP)

    def stop(self):
        self.stopped = True

    def __draw_circle(self, x, y, r, fill='', outline='#00ff00'):
        x1, y1 = x - r, y - r
        x2, y2 = x + r, y + r
        return self.canvas.create_oval(
            x1, y1, x2, y2, fill=fill, outline=outline)

    def __draw_point(self, x, y, color='#ff0000'):
        return self.__draw_circle(x, y, 1, color, color)

    def __update_circle(self, x, y, r, fig):
        x1, y1 = x - r, y - r
        x2, y2 = x + r, y + r
        self.canvas.coords(fig, x1, y1, x2, y2)

    def __update_point(self, x, y, fig):
        self.__update_circle(x, y, 1, fig)

    
if __name__ == '__main__':
    App().run()
