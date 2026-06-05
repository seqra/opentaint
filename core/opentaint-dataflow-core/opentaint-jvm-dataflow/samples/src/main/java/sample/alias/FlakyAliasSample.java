package sample.alias;

import java.nio.ByteBuffer;
import sample.AliasSettings;
import sample.BaseSample;

public final class FlakyAliasSample extends BaseSample {

    interface Pooled<T> {
        T getResource();
    }

    private Pooled<ByteBuffer> buffer;

    @AliasSettings(interProcDepth = 1)
    public int write(java.nio.ByteBuffer src) {
        Object copyForNonEmptyAlias = identity(src);
        java.nio.ByteBuffer[] arr = new java.nio.ByteBuffer[]{src};
        flushBufferWithUserData(arr);
        sinkOneValue(copyForNonEmptyAlias);
        identity(arr);
        return 0;
    }

    long flushBufferWithUserData(final ByteBuffer[] byteBuffers) {
        final ByteBuffer byteBuffer = buffer.getResource();

        ByteBuffer[] writeBufs = new ByteBuffer[100 + 1];
        writeBufs[0] = byteBuffer;

        for (int i = 0; i < 100; i++) {
            writeBufs[i] = byteBuffers[i];
            byteBuffers[i].remaining();
        }

        sinkOneValue(writeBufs);
        return 0;
    }
}
