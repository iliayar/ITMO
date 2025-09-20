import numpy as np
from typing import List, Tuple, Union

def my_interpolate(xs: List[float], ys: List[float]):
    xs = np.array(xs)
    ys = np.array(ys)
    
    hs = np.diff(xs)
    ds = np.diff(ys) / hs
    
    d_signs = np.sign(ds)
    zeros = (d_signs[1:] != d_signs[:-1]) | (ds[1:] == 0) | (ds[:-1] == 0)
    
    w1s = 2 * hs[1:] + hs[:-1]
    w2s = hs[1:] + 2 * hs[:-1]
    
    wmeans = (w1s + w2s) / (w1s / ds[:-1] + w2s / ds[1:])
    
    
    derivs = np.empty(xs.shape, dtype=xs.dtype)
    derivs[1:-1][zeros]  = 0.0
    derivs[1:-1][~zeros] = wmeans[~zeros]
    
    t = (derivs[1:] + derivs[:-1] - 2 * ds) / hs
    
    koefs = np.empty((4,) + hs.shape, dtype=t.dtype)
    koefs[0] = t / hs
    koefs[1] = (ds - derivs[:-1]) / hs - t
    koefs[2] = derivs[:-1]
    koefs[3] = ys[:-1]
        
    def eval(x: float):
        point = xs[xs < x].shape[0]
        rank = koefs.shape[0] - 1
        
        if point == xs.shape[0]:
            interval = koefs.shape[1] - 1
            point = xs.shape[0] - 1
        elif point == 0:
            point = 0
            interval = 0
        else:
            point -= 1
            interval = point
        
        return koefs[:, interval] @ (x - xs[point])**(rank - np.arange(rank + 1))
    
    return eval
