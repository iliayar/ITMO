
import kotlinx.atomicfu.*

class DynamicArrayImpl<E> : DynamicArray<E> {
    private val core = atomic(Core<E>(INITIAL_CAPACITY))
    private val size_ = atomic(0)

    override fun get(index: Int): E {
	checkIndex(index)
	while (true) {
	    val core = core.value
	    val value = core.get(index)

	    if (value is Moved) {
		extend(core)
	    } else {
		return value.value
	    }
	}
    }

    override fun put(index: Int, element: E) {
	checkIndex(index)
	while (true) {
	    val core = core.value
	    val value = core.get(index)

	    if (value is Moved) {
		extend(core)
	    } else if (core.put(index, value, element)) {
		return
	    }
	}
    }

    override fun pushBack(element: E) {
	while (true) {
	    val size = size
	    val core = core.value

	    if (size >= core.capacity) {
		extend(core)
	    } else if (core.put(size, null, element)) {
		size_.incrementAndGet()
		return
	    }
	}
    }

    override val size: Int get() {
	return size_.value
    }

    private fun extend(old: Core<E>) {
	core.compareAndSet(old, old.mkNext())
    }

    fun checkIndex(index: Int) {
	if (index >= size) {
	    throw IllegalArgumentException()
	}
    }
}

private open class Flagged<E>(
    val value: E
) { }

private class Moved<E>(value: E) : Flagged<E>(value) {}

private class Core<E>(
    val capacity: Int,
) {
    private val array = atomicArrayOfNulls<Flagged<E>>(capacity)
    private val next: AtomicRef<Core<E>?> = atomic(null)

    fun put(index: Int, old: Flagged<E>?, new: E): Boolean {
	return array[index].compareAndSet(old, Flagged(new))
    }

    fun get(index: Int): Flagged<E> {
	return array[index].value!!
    }

    fun mkNext(): Core<E> {
	next.compareAndSet(null, Core(capacity * 2))
	val next = next.value!!
	for (i in 0..capacity-1) {
	    while(true) {
		val value = array[i].value
		if (value != null && array[i].compareAndSet(value, Moved(value.value))) {
		    next.array[i].compareAndSet(null, Flagged(value.value))
		    break
		}
	    }
	}
	return next
    }
}

private const val INITIAL_CAPACITY = 1 // DO NOT CHANGE ME
