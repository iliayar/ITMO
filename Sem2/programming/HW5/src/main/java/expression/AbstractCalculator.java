package expression;

import expression.DivisonByZeroException;

public abstract class AbstractCalculator<T extends Number> implements Calculator<T> {

    boolean checked;

    AbstractCalculator() {
        this.checked = true;
    }
    AbstractCalculator(boolean checked) {
        this.checked = checked;
    }
    protected boolean checkAdd(T a, T b, T MAX_VALUE, T MIN_VALUE) {
        if(a == null || b == null) {
            return false;
        }
        if(MAX_VALUE == null || MIN_VALUE == null) {
            return true;
        }
        if (checked &&
            ((compareTo(a, valueOf(0)) > 0 && compareTo(b, valueOf(0)) > 0 && compareTo(a, subtract(MAX_VALUE, b)) > 0) ||
             (compareTo(a, valueOf(0)) < 0 && compareTo(b, valueOf(0)) < 0 && compareTo(a, subtract(MIN_VALUE, b)) < 0))) {
            return false;
        }
        return true;
    }

    protected boolean checkSubtract(T a, T b, T MAX_VALUE, T MIN_VALUE) {
        if (a == null || b == null) {
            return false;
        }
        if (MAX_VALUE == null || MIN_VALUE == null) {
            return true;
        }
        if (checked &&
            ((compareTo(a, valueOf(0)) > 0 && compareTo(b, valueOf(0)) < 0 && compareTo(a, add(MAX_VALUE, b)) > 0) ||
             (compareTo(a, valueOf(0)) < 0 && compareTo(b, valueOf(0)) > 0 && compareTo(a, add(MIN_VALUE, b)) < 0))) {
            return false;
        }
        return true;
    }

    protected boolean checkDivide(T a, T b, T MAX_VALUE, T MIN_VALUE) {
        if (a == null || b == null) {
            return false;
        }
        if (compareTo(b, valueOf(0)) == 0) {
            // throw new DivisonByZeroException(a, b);
            return false;
        }
        if (MAX_VALUE == null || MIN_VALUE == null) {
            return true;
        }
        if (checked && compareTo(b, valueOf(-1)) == 0 && compareTo(a, MIN_VALUE) == 0) {
            return false;
        }
        return true;
    }

    protected boolean checkNegate(T a, T MAX_VALUE, T MIN_VALUE) {
        if (a == null) {
            return false;
        }
        if (MAX_VALUE == null || MIN_VALUE == null) {
            return true;
        }
        if (checked && compareTo(a, MIN_VALUE) == 0) {
            return false;
        }
        return true;
    }

    protected boolean checkMultiply(T a, T b, T MAX_VALUE, T MIN_VALUE) {
        if (a == null || b == null) {
            return false;
        }
        if (MAX_VALUE == null || MIN_VALUE == null) {
            return true;
        }
        if (checked &&
            ((compareTo(a, valueOf(0)) > 0 && ((compareTo(b, valueOf(0)) > 0 && compareTo(b, divide(MAX_VALUE, a)) > 0) ||
                                              (compareTo(b, valueOf(0)) < 0 && compareTo(b, divide(MIN_VALUE, a)) < 0))) ||
            (compareTo(a, valueOf(0)) < 0 && ((compareTo(b, valueOf(0)) > 0 && compareTo(a, divide(MIN_VALUE, b)) < 0) ||
                                              (compareTo(b, valueOf(0)) < 0 && compareTo(b, divide(MAX_VALUE, a)) < 0))))) {
            return false;
        }
        return true;
    }

	@Override
	public T max(T a, T b) {
      if(a == null || b == null) {
          return null;
      }
      return compareTo(a, b) > 0 ? a : b;
	}

	@Override
	public T min(T a, T b) {
      if(a == null || b == null) {
          return null;
      }
      return compareTo(a, b) < 0 ? a : b;
	}


}
