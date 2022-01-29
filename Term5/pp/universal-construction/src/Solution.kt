/*
 * @author Yaroshevskiy Ilya
 */ 

import kotlin.concurrent.getOrSet

class Solution : AtomicCounter {
    private val root: Node = Node(0)
    private val last: ThreadLocal<Node> = ThreadLocal()

    override fun getAndAdd(x: Int): Int {
	while (true) {
	    val cur = last.getOrSet { root }
	    val node = Node(cur.x + x)
	    last.set(cur.next.decide(node))
	    if(last.get() == node) {
		return cur.x
	    }
	}
    }

    private class Node(
	val x: Int) {
	val next: Consensus<Node> = Consensus()
    }
}
