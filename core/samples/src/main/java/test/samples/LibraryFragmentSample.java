package test.samples;

import test.library.LibraryFragment;

public final class LibraryFragmentSample {

    public interface LibraryBackedRepository extends LibraryFragment {
        String findBySku(String sku);
    }

    public static final class LibraryFragmentImpl implements LibraryFragment {
        @Override
        public String libraryQuery(String criteria) {
            sink(criteria);
            return criteria;
        }

        @Override
        public String libraryLookup(String url) {
            return url;
        }
    }

    private final LibraryBackedRepository repository;

    public LibraryFragmentSample(LibraryBackedRepository repository) {
        this.repository = repository;
    }

    public void listProducts(String criteria) {
        repository.libraryQuery(criteria);
    }

    public static void sink(String query) {
    }
}
