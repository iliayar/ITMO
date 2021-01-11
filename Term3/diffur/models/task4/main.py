#!/usr/bin/env python3

from tkinter import *
import threading
import math
import time

CANVAS_HEIGHT = 720
CANVAS_WIDTH  = 1280

ANIMATION_STEP  = 0.001
ANIMATION_SPEED = 5

CUBE_SIZE = 20

def parametrized_equaiton_factory(x10, x20, alpha):
    def function(t):
        return (2/5*(x10 + x20)*math.cos(1/math.sqrt(6)*alpha*t) + 1/5*(3*x10 - 2*x20)*math.cos(alpha*t),
                3/5*(x10 + x20)*math.cos(1/math.sqrt(6)*alpha*t) - 1/5*(3*x10 - 2*x20)*math.cos(alpha*t))
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
        self.params['x1'] = (0, 0, CANVAS_WIDTH)
        self.params['x2'] = (0, 0, CANVAS_WIDTH)
        self.params['speed'] = (1, 1, 50)
        self.params['a'] = (1, 0, 100)

        def create_sliders(parent, texts):
            for t in texts:
                def handler(t):
                    return lambda e: self.__handle_param(t, e)

                slider = labeled_slider(parent, t, handler(t), self.params[t][1], self.params[t][2])
                slider.set(self.params[t][0])
                self.__dict__[t + '_slider'] = slider

        create_sliders(bot_left_frame, ['x1', 'a'])
        create_sliders(bot_right_frame, ['x2', 'speed'])
    
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
        function = parametrized_equaiton_factory(self.params['x1'][0],
                                                 self.params['x2'][0],
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
        self.stopped = False
        self.__draw_line(CANVAS_WIDTH//2, CANVAS_HEIGHT//2 - CUBE_SIZE,
                         CANVAS_WIDTH//2, CANVAS_HEIGHT//2 + CUBE_SIZE//2)
        self.__draw_line(0, CANVAS_HEIGHT//2 + CUBE_SIZE//2 + 2,
                         CANVAS_WIDTH, CANVAS_HEIGHT//2 + CUBE_SIZE//2 + 2)

    def run(self):
        
        x10, x20 = self.function(0)
        x10 += CANVAS_WIDTH//2
        x20 += CANVAS_WIDTH//2
        
        self.cube1 = self.__draw_cube(x10, CANVAS_HEIGHT//2)
        self.cube2 = self.__draw_cube(x20, CANVAS_HEIGHT//2)
        self.spring1 = self.__draw_line(CANVAS_WIDTH//2, CANVAS_HEIGHT//2 + 2,
                                        x10 - CUBE_SIZE//2, CANVAS_HEIGHT//2 + 2, color='yellow')
        self.spring2 = self.__draw_line(x10 + CUBE_SIZE//2, CANVAS_HEIGHT//2 - 2,
                                        x20 - CUBE_SIZE//2, CANVAS_HEIGHT//2 - 2, color='green')

        while not self.stopped:
            self.t += ANIMATION_STEP*ANIMATION_SPEED

            x1, x2 = self.function(self.t)
            x1 += CANVAS_WIDTH//2
            x2 += CANVAS_WIDTH//2

            self.__update_cube(self.cube1, x1, CANVAS_HEIGHT//2)
            self.__update_cube(self.cube2, x2, CANVAS_HEIGHT//2)
            self.__update_line(self.spring1, CANVAS_WIDTH//2, CANVAS_HEIGHT//2 + 2,
                               x1 - CUBE_SIZE//2, CANVAS_HEIGHT//2 + 2)
            self.__update_line(self.spring2, x1 + CUBE_SIZE//2, CANVAS_HEIGHT//2 - 2,
                               x2 - CUBE_SIZE//2, CANVAS_HEIGHT//2 - 2)

            time.sleep(ANIMATION_STEP)

    def stop(self):
        self.stopped = True

    def __draw_cube(self, x, y):
        return self.canvas.create_rectangle(x - CUBE_SIZE//2, y - CUBE_SIZE//2,
                                            x + CUBE_SIZE//2, y + CUBE_SIZE//2, fill='red')
    def __update_cube(self, fig, x, y):
        self.canvas.coords(fig, x - CUBE_SIZE//2, y - CUBE_SIZE//2,
                           x + CUBE_SIZE//2, y + CUBE_SIZE//2)

    def __draw_line(self, x1, y1, x2, y2, color='grey'):
        return self.canvas.create_line(x1, y1, x2, y2, width=2, fill=color)

    def __update_line(self, fig, x1, y1, x2, y2):
        self.canvas.coords(fig, x1, y1, x2, y2)
        
    
if __name__ == '__main__':
    App().run()
