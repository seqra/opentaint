package test.samples;

import org.springframework.data.repository.Repository;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class SpringRepositoryStaticFlowSample {
    private final FileRepository repository;

    public SpringRepositoryStaticFlowSample(FileRepository repository) {
        this.repository = repository;
    }

    @GetMapping
    public void update(String path) {
        StoredFile file = repository.findByUuid("id");
        if (file == null) {
            file = new StoredFile();
        }
        file.setPath(path);
        repository.save(file);
    }

    @GetMapping
    public void download() {
        StoredFile file = repository.findByUuid("id");
        sink(file.getPath());
    }

    public static void sink(String path) {
    }

    public interface FileRepository extends Repository<StoredFile, String> {
        StoredFile save(StoredFile file);

        StoredFile findByUuid(String uuid);
    }

    public static final class StoredFile {
        private String path;

        public String getPath() {
            return path;
        }

        public void setPath(String path) {
            this.path = path;
        }
    }
}
