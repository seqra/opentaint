package security.permissions;

import java.lang.reflect.ReflectPermission;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.file.attribute.PosixFilePermissions;
import java.security.PermissionCollection;
import java.security.Permissions;
import java.util.HashSet;
import java.util.Set;


/**
 * Samples for permissions-related rules in java/security/permissions.yaml.
 */
public class PermissionsSamples {

    // ===== dangerous-permissions =====

    public PermissionCollection grantDangerousRuntimeAndReflectPermissions() {
        PermissionCollection pc = new Permissions();

        // VULNERABLE: explicitly grant createClassLoader permission
        RuntimePermission runtimePermission = new RuntimePermission("createClassLoader");
        pc.add(runtimePermission);

        // VULNERABLE: explicitly grant suppressAccessChecks permission
        ReflectPermission reflectPermission = new ReflectPermission("suppressAccessChecks");
        pc.add(reflectPermission);

        return pc;
    }

    public PermissionCollection grantLimitedSafePermissions() {
        PermissionCollection pc = new Permissions();

        // SAFE: grant a benign permission instead of dangerous ones
        RuntimePermission harmless = new RuntimePermission("loadLibrary.*");
        pc.add(harmless);

        return pc;
    }

    // ===== overly-permissive-file-permission-inline =====

    public void createWorldReadableAndWritableFile(String filePath) throws Exception {
        Path path = Paths.get(filePath);

        // VULNERABLE: world-readable and writable via symbolic notation (OTHERS_* bits set)
        Set<PosixFilePermission> permissions = PosixFilePermissions.fromString("rw-rw-rw-");
        Files.setPosixFilePermissions(path, permissions);
    }

    public void addExplicitOthersExecutePermission(Path file) throws Exception {
        Set<PosixFilePermission> permissions = new HashSet<>();

        // VULNERABLE: explicitly add OTHERS_EXECUTE and then apply
        permissions.add(PosixFilePermission.OTHERS_EXECUTE);
        Files.setPosixFilePermissions(file, permissions);
    }

    public void createOwnerOnlyFile(String filePath) throws Exception {
        Path path = Paths.get(filePath);

        // SAFE: owner read/write, no permissions for group/others
        Set<PosixFilePermission> permissions = PosixFilePermissions.fromString("rw-------");
        Files.setPosixFilePermissions(path, permissions);
    }
}
