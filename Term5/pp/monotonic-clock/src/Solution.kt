/**
 * В теле класса решения разрешено использовать только переменные делегированные в класс RegularInt.
 * Нельзя volatile, нельзя другие типы, нельзя блокировки, нельзя лазить в глобальные переменные.
 *
 * @author Yaroshevskiy Ilya
 */
class Solution : MonotonicClock {
    
    private var c11 by RegularInt(0)
    private var c12 by RegularInt(0)
    private var c13 by RegularInt(0)
    private var c21 by RegularInt(0)
    private var c22 by RegularInt(0)
    private var c23 by RegularInt(0)

    private var r11 by RegularInt(0)
    private var r12 by RegularInt(0)
    private var r13 by RegularInt(0)
    private var r21 by RegularInt(0)
    private var r22 by RegularInt(0)
    private var r23 by RegularInt(0)

    override fun write(time: Time) {
	c21 = time.d1
	c22 = time.d2
	c23 = time.d3
	c13 = time.d3
	c12 = time.d2
	c11 = time.d1
	
    }

    override fun read(): Time {
	r11 = c11
	r12 = c12
	r13 = c13
	r23 = c23
	r22 = c22
	r21 = c21
	if(r11 == r21 && r12 == r22 && r13 == r23) {
	    return Time(r11, r12, r13)
	} else if (r11 == r21 && r12 == r22) {
	    return Time(r11, r12, r13 + 1)
	} else if (r11 == r21) {
	    return Time(r11, r12 + 1, 0)
	} else {
	    return Time(r11 + 1, 0, 0)
	}
    }
}
