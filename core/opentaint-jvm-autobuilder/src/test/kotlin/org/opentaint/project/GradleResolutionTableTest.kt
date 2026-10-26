package org.opentaint.project

import kotlin.io.path.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import java.nio.file.Files

class GradleResolutionTableTest {
    @Test
    fun `folds per-project reports into one coordinate-keyed table`() {
        val dir = Files.createTempDirectory("table").also { it.createDirectories() }
        dir.resolve("table-_os-v2.json").writeText(
            """[{"coord":"org.opensearch.client:opensearch-rest-client:2.18.0","file":"/g/os2/opensearch-rest-client-2.18.0.jar"}]""")
        dir.resolve("table-_os-v3.json").writeText(
            """[{"coord":"org.opensearch.client:opensearch-rest-client:3.5.0","file":"/g/os3/opensearch-rest-client-3.5.0.jar"}]""")

        val table = parseResolutionTable(dir)

        assertEquals(Path("/g/os2/opensearch-rest-client-2.18.0.jar"),
            table["org.opensearch.client:opensearch-rest-client:2.18.0"])
        assertEquals(Path("/g/os3/opensearch-rest-client-3.5.0.jar"),
            table["org.opensearch.client:opensearch-rest-client:3.5.0"])
        assertNull(table["org.opensearch.client:opensearch-rest-client:1.0.0"])
    }
}
