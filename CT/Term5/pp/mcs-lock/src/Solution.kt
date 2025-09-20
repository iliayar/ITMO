import java.util.concurrent.atomic.*

class Solution(val env: Environment) : Lock<Solution.Node> {
    // todo: необходимые поля (val, используем AtomicReference)
    val tail = AtomicReference<Node>(null)

    override fun lock(): Node {
        val my = Node() // сделали узел
	my.locked.value = true
	val pred = tail.getAndSet(my)
	if (pred != null) {
	    pred.next.value = my
	    while (my.locked.value) { env.park() }
	}
        return my // вернули узел
    }

    override fun unlock(node: Node) {
	if (node.next.value == null) {
	    if (tail.compareAndSet(node, null)) {
		return
	    } else {
		while (node.next.value == null) {}
	    }
	}
	node.next.value.locked.value = false
	env.unpark(node.next.value.thread)
    }

    class Node {
        val thread = Thread.currentThread() // запоминаем поток, которые создал узел
        // todo: необходимые поля (val, используем AtomicReference)
	val locked = AtomicReference<Boolean>(false)
	val next = AtomicReference<Node>(null)
    }
}
