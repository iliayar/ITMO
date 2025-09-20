package dijkstra

import java.util.*
import java.util.concurrent.Phaser
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.ReentrantLock
import kotlin.Comparator
import kotlin.concurrent.thread
import kotlin.system.exitProcess
import kotlin.repeat
import kotlinx.atomicfu.locks.withLock

private val NODE_DISTANCE_COMPARATOR = Comparator<Node> { o1, o2 -> Integer.compare(o1!!.distance, o2!!.distance) }

class PriorityMultiQueue<T>(
    val workers: Int,
    val comparator: Comparator<T>) {
    val qs = List(workers * 2) { _ -> PriorityQueue(comparator) }
    val locks = List(workers * 2) { _ -> ReentrantLock() }

    fun add(element: T): Boolean {
	val random = ThreadLocalRandom.current()
	while (true) {
	    val index = random.nextInt(qs.size)
	    if (locks[index].tryLock()) {
		val res = qs[index].add(element)
		locks[index].unlock()
		return res
	    }
	}
    }

    fun isEmpty(): Boolean {
	locks.forEach { lock -> lock.lock() }
	val res = qs.all { q -> q.isEmpty() }
	locks.forEach { lock -> lock.unlock() }
	return res
    }

    fun poll(): T? {
	val random = ThreadLocalRandom.current()
	while (true) {
	    var (first, second) = random.run { Pair(nextInt(qs.size), nextInt(qs.size)) }
	    if (first > second) {
		first = second.also { second = first }
	    }

	    if (locks[first].tryLock()) {
		if(locks[second].tryLock()) {
		    val firstVal = qs[first].peek()
		    val secondVal = qs[second].peek()
		    val index: Int?
		    if (firstVal == null && secondVal == null) {
			index = null
		    } else if (firstVal == null) {
			index = second
		    } else if (secondVal == null) {
			index = first
		    } else {
			if (this.comparator.compare(firstVal, secondVal) < 0) {
			    index = first
			}  else {
			    index = second
			} 
		    }
		    val res: T? = if (index == null) null else qs[index].poll()
		    locks[first].unlock()
		    locks[second].unlock()
		    return res
		}
		locks[first].unlock()
	    }
	}
    }
}

// Returns `Integer.MAX_VALUE` if a path has not been found.
fun shortestPathParallel(start: Node) {
    val workers = Runtime.getRuntime().availableProcessors()
    // The distance to the start node is `0`
    start.distance = 0
    // Create a priority (by distance) queue and add the start node into it
    val q = PriorityMultiQueue(workers, NODE_DISTANCE_COMPARATOR) // TODO replace me with a multi-queue based PQ!
    q.add(start)
    // Run worker threads and wait until the total work is done
    val onFinish = Phaser(workers + 1) // `arrive()` should be invoked at the end by each worker
    var activeNodes: AtomicInteger = AtomicInteger(1)
    repeat(workers) {
        thread {
            while (true) {
               val cur: Node? = q.poll()
               if (cur == null) {
                   if (activeNodes.get() == 0) break else continue
               }
               for (e in cur.outgoingEdges) {
		   while(true) {
		       val oldDistance = e.to.distance
		       val newDistance = cur.distance + e.weight
		       if (oldDistance > newDistance) {
			   if(e.to.casDistance(oldDistance, newDistance)) {
			       if(q.add(e.to)) {
				   activeNodes.incrementAndGet()
			       }
			       break
			   }
		       } else {
			   break
		       }
		       
		   }
               }
	       activeNodes.decrementAndGet()
            }
            onFinish.arrive()
        }
    }
    onFinish.arriveAndAwaitAdvance()
}
