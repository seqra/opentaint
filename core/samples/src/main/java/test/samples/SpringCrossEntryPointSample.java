package test.samples;

import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.data.repository.Repository;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class SpringCrossEntryPointSample {
    @Autowired
    private PluginService pluginService;

    @GetMapping
    public void uploadNewPlugin(PluginUpload pluginUpload) {
        pluginService.savePlugin(pluginUpload);
    }

    @GetMapping
    public void uploadPlainString(String jarFilePath) {
        pluginService.savePlainString(jarFilePath);
    }

    @GetMapping
    public void deletePlugins() {
        pluginService.deletePlugins();
    }

    @GetMapping
    public void deletePluginsPlainField() {
        pluginService.deletePluginsPlainField();
    }

    @GetMapping
    public void uploadAndDeleteRepo(PluginUpload pluginUpload) {
        pluginService.savePlugin(pluginUpload);
        pluginService.deletePlugins();
    }

    @GetMapping
    public void uploadAndDeletePlainField(PluginUpload pluginUpload) {
        pluginService.savePlugin(pluginUpload);
        pluginService.deletePluginsPlainField();
    }

    public static void sink(String path) {
        System.out.println(path);
    }

    public static class PluginUpload {
        private String jarFile;

        public String getJarFile() {
            return this.jarFile;
        }
    }

    public static class PluginMetadata {
        private String jarFilePath;

        public String getJarFilePath() {
            return this.jarFilePath;
        }

        public void setJarFilePath(String jarFilePath) {
            this.jarFilePath = jarFilePath;
        }
    }

    public interface MetadataDao extends Repository<PluginMetadata, Long> {
        PluginMetadata save(PluginMetadata metadata);

        List<PluginMetadata> findAll();
    }

    public static class PluginService {
        @Autowired
        private MetadataDao metadataDao;

        private String plainField;

        public void savePlugin(PluginUpload pluginUpload) {
            PluginMetadata metadata = new PluginMetadata();
            metadata.setJarFilePath(pluginUpload.getJarFile());
            metadataDao.save(metadata);
            this.plainField = pluginUpload.getJarFile();
        }

        public void savePlainString(String jarFilePath) {
            this.plainField = jarFilePath;
        }

        public void deletePlugins() {
            for (PluginMetadata metadata : metadataDao.findAll()) {
                SpringCrossEntryPointSample.sink(metadata.getJarFilePath());
            }
        }

        public void deletePluginsPlainField() {
            SpringCrossEntryPointSample.sink(this.plainField);
        }
    }
}
