import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.stress.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import kotlin.test.*

@StressCTest
class LinearizabilityTest : VerifierState() {
    private val c = Solution()

    @Operation
    fun add(x: Int) = c.getAndAdd(x)

    @Test
    fun testLinearizability() {
        LinChecker.check(LinearizabilityTest::class.java)
    }

    override fun extractState(): Any = c.getAndAdd(0)
}