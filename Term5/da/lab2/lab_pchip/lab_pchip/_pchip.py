import numpy as np
from typing import List, Tuple, Union

def pchip(xs: List[float], ys: List[float]):
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
        i = len(xs[xs < x])
        rank = koefs.shape[0] - 1
        
        if i == koefs.shape[1]:
            i = koefs.shape[1] - 1
        if i != 0:
            i -= 1
        
        return koefs[:, i] @ (x - xs[i])**(rank - np.arange(rank + 1))
    
    return eval
