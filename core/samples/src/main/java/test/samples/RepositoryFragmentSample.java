package test.samples;

import java.util.List;

public final class RepositoryFragmentSample {

    public interface BaseRepository<T, ID> {
        T findById(ID id);

        List<T> findAll();
    }

    public interface ProductRepositoryCustom {
        String listByStore(String criteria);

        String getByFriendlyUrl(String url);
    }

    public interface ProductRepository extends BaseRepository<String, Long>, ProductRepositoryCustom {
        String findBySku(String sku);
    }

    public static final class ProductRepositoryImpl implements ProductRepositoryCustom {
        @Override
        public String listByStore(String criteria) {
            sink(criteria);
            return criteria;
        }

        @Override
        public String getByFriendlyUrl(String url) {
            return url;
        }
    }

    private final ProductRepository productRepository;

    public RepositoryFragmentSample(ProductRepository productRepository) {
        this.productRepository = productRepository;
    }

    public void listProducts(String criteria) {
        productRepository.listByStore(criteria);
    }

    public static void sink(String query) {
    }
}
