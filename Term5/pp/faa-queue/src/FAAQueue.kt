import kotlinx.atomicfu.*

class FAAQueue<T> {
    private val head: AtomicRef<Segment> // Head pointer, similarly to the Michael-Scott queue (but the first node is _not_ sentinel)
    private val tail: AtomicRef<Segment> // Tail pointer, similarly to the Michael-Scott queue

    init {
        val firstNode = Segment()
        head = atomic(firstNode)
        tail = atomic(firstNode)
    }

    /**
     * Adds the specified element [x] to the queue.
     */
    fun enqueue(x: T) {
	while (true) {
	    val tail = tail.value
	    val enqIdx = tail.enqIdx.getAndAdd(1)
	    if (enqIdx >= SEGMENT_SIZE) {
		// try to insert new node with "x"
		// TODO()
		val newTail = Segment(x)
		val tailNext = tail.next.value
		if (tail == this.tail.value) {
		    if (tailNext == null) {
			if (tail.next.compareAndSet(tailNext, newTail)) {
			    this.tail.compareAndSet(tail, newTail)
			    return
			}
		    } else {
			this.tail.compareAndSet(tail, tailNext)
		    }
		}
	    } else {
		if (tail.elements[enqIdx].compareAndSet(null, x)) {
		    return
		}
	    }
	}
    }

    /**
     * Retrieves the first element from the queue
     * and returns it; returns `null` if the queue
     * is empty.
     */
    fun dequeue(): T? {
	while (true) {
	    val head = head.value
	    val deqIdx = head.deqIdx.getAndAdd(1)
	    if (deqIdx >= SEGMENT_SIZE) {
		val headNext = head.next.value ?: return null
		this.head.compareAndSet(head, headNext)
		continue
	    }
	    val res = head.elements[deqIdx].getAndSet(DONE)
	    if (res == null) continue
	    return res as T?
	}
    }

    /**
     * Returns `true` if this queue is empty;
     * `false` otherwise.
     */
    val isEmpty: Boolean get() {
        while (true) {
	    val head = head.value
            if (head.isEmpty) {
		val headNext = head.next.value
                if (headNext == null) return true
		this.head.compareAndSet(head, headNext)
                continue
            } else {
                return false
            }
        }
    }
}

private class Segment {
    val next: AtomicRef<Segment?> = atomic(null)
    val enqIdx = atomic(0) // index for the next enqueue operation
    val deqIdx = atomic(0) // index for the next dequeue operation
    val elements = atomicArrayOfNulls<Any>(SEGMENT_SIZE)

    constructor() // for the first segment creation

    constructor(x: Any?) { // each next new segment should be constructed with an element
        enqIdx.getAndSet(0)
        elements[0].getAndSet(x)
    }

    val isEmpty: Boolean get() {
	val deqIdx = deqIdx.value
	val enqIdx = enqIdx.value
	return deqIdx >= enqIdx || deqIdx >= SEGMENT_SIZE
    }

}

private val DONE = Any() // Marker for the "DONE" slot state; to avoid memory leaks
const val SEGMENT_SIZE = 2 // DO NOT CHANGE, IMPORTANT FOR TESTS

