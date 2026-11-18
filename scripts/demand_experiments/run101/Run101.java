import java.lang.instrument.*;
import java.security.ProtectionDomain;
import jdk.internal.org.objectweb.asm.*;

public class Run101 {
    public static void premain(String args, Instrumentation instrumentation) {
        instrumentation.addTransformer(new ClassFileTransformer() {
            @Override
            public byte[] transform(ClassLoader loader, String name, Class<?> type,
                                    ProtectionDomain domain, byte[] bytes) {
                if (!"org/opentaint/dataflow/bidi/driver/HardRunLimitPolicy".equals(name)) return null;
                var reader = new ClassReader(bytes);
                var writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
                reader.accept(new ClassVisitor(Opcodes.ASM8, writer) {
                    @Override
                    public MethodVisitor visitMethod(int access, String method, String desc,
                            String signature, String[] exceptions) {
                        var visitor = super.visitMethod(access, method, desc, signature, exceptions);
                        if (!method.equals("<init>") || !desc.equals("(Lorg/opentaint/dataflow/bidi/driver/IterationPolicy;I)V")) return visitor;
                        return new MethodVisitor(Opcodes.ASM8, visitor) {
                            @Override
                            public void visitCode() {
                                super.visitCode();
                                visitIntInsn(Opcodes.BIPUSH, 101);
                                visitVarInsn(Opcodes.ISTORE, 2);
                            }
                        };
                    }
                }, 0);
                System.err.println("RUN101_TEST_POLICY lastForwardRun=101");
                return writer.toByteArray();
            }
        });
    }
}
