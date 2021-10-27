from itertools import product
import statsmodels.api as sm
from tqdm import tqdm
from statsmodels.tsa.statespace.sarimax import SARIMAXResultsWrapper
import numpy as np

def bruteforce_params(y_train: np.ndarray, s: int, d: int, D: int, qs: int, Qs: int, ps: int, Ps: int) -> SARIMAXResultsWrapper:
    parameters = product(ps, qs, Ps, Qs)
    parameters_list = list(parameters)

    best_aic = float("inf")

    for param in tqdm(parameters_list):
        try:
            model = sm.tsa.statespace.SARIMAX(
                y_train, 
                order=(param[0], d, param[1]), 
                seasonal_order=(param[2], D, param[3], s)
            ).fit(disp=-1)
        except ValueError:
#             print('wrong parameters:', param)
            continue
        aic = model.aic
        if aic < best_aic:
            best_model = model
            best_aic = aic
            best_param = param
            
    return best_model

def MAPE(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    return (np.abs(y_true - y_pred) / y_true)[y_true != 0].mean()
