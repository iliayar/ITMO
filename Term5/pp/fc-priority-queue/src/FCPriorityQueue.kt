import java.util.*
import java.util.concurrent.locks.ReentrantLock
import kotlinx.atomicfu.atomicArrayOfNulls

const val COMBINE_ARRAY_SIZE = 10

private class RESULT(val res: Any?) {}
private class ACTION(val act: () -> Any?) {}

class FCPriorityQueue<E : Comparable<E>> {
    private val q = PriorityQueue<E>()
    private val tasks = atomicArrayOfNulls<Any?>(COMBINE_ARRAY_SIZE)
    private val lock = ReentrantLock()

    private fun runTasks() {
	for (i in 0..tasks.size-1) {
	    val f = tasks[i].value
	    if (f is ACTION) {
		tasks[i].getAndSet(RESULT(f.act()))
	    }
	}
    }

    private fun execute(t: () -> Any?): Any? {
	if(lock.tryLock()) {
	    val res = t()
	    runTasks()
	    lock.unlock()
	    return res
	} else {
	    val i = Thread.currentThread().id.toInt() % COMBINE_ARRAY_SIZE
	    while (!tasks[i].compareAndSet(null, ACTION(t))) {}
	    while (true) {
		val r = tasks[i].value
		if (r is RESULT) {
		    tasks[i].getAndSet(null)
		    return r.res
		}
		if (lock.tryLock()) {
		    val t = tasks[i].getAndSet(null)
		    var res: Any? = null
		    if (t is RESULT) {
			res = t.res
		    } else if (t is ACTION) {
			res = t.act()
		    }
		    runTasks()
		    lock.unlock()
		    return res
		}
	    }
	}
    }

    /**
     * Retrieves the element with the highest priority
     * and returns it as the result of this function;
     * returns `null` if the queue is empty.
     */
    fun poll(): E? {
        // return q.poll()
	return execute { q.poll() } as E?
    }

    /**
     * Returns the element with the highest priority
     * or `null` if the queue is empty.
     */
    fun peek(): E? {
        // return q.peek()
	return execute { q.peek() } as E?
    }

    /**
     * Adds the specified element to the queue.
     */
    fun add(element: E) {
        // q.add(element)
	execute { q.add(element) }
    }
}
