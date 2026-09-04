package test.samples;

import java.util.List;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class CollectionElementGetterSample {
    @GetMapping
    public void searchViaList(ProductCriteria searchCriterias) {
        facade(searchCriterias);
    }

    @GetMapping
    public void searchDirectField(ProductCriteria searchCriterias) {
        sink(searchCriterias.getName());
    }

    @GetMapping
    public void searchListOfStrings(ProductCriteria searchCriterias) {
        StringBuilder qs = new StringBuilder();
        for (String code : searchCriterias.getCodes()) {
            qs.append(code);
        }
        sink(qs.toString());
    }

    @GetMapping
    public void searchShopizerShape(String lang, ProductCriteria searchCriterias, Integer count) {
        if (searchCriterias.getSku() != null) {
            searchCriterias.setCode(searchCriterias.getSku());
        }
        facadeShopizer(searchCriterias);
    }

    private void facadeShopizer(ProductCriteria criterias) {
        serviceShopizer(criterias);
    }

    private void serviceShopizer(ProductCriteria criteria) {
        criteria.setPageSize(10);
        repositoryShopizer(criteria);
    }

    private void repositoryShopizer(ProductCriteria criteria) {
        StringBuilder builderSelect = new StringBuilder();
        StringBuilder builderWhere = new StringBuilder();
        builderSelect.append("select p from Product p");
        if (criteria.getStatus() != null) {
            builderWhere.append(" and p.status=:st");
        }
        if (criteria.getAttributeCriteria() != null && !criteria.getAttributeCriteria().isEmpty()) {
            int c = 0;
            for (AttributeCriteria attributeCriteria : criteria.getAttributeCriteria()) {
                if (c == 0) {
                    builderWhere.append(" and po.code =:").append(attributeCriteria.getAttributeCode());
                    builderWhere.append(" and povd.description like :").append("val").append(c)
                            .append(attributeCriteria.getAttributeCode());
                }
                c++;
            }
            if (criteria.getLanguage() != null) {
                builderWhere.append(" and povd.language.code=:lang");
            }
        }
        if (criteria.getAvailable() != null) {
            builderWhere.append(" and p.available=true");
        }
        String hql = builderSelect.toString() + builderWhere.toString();
        sink(hql);
    }

    private void facade(ProductCriteria criterias) {
        service(criterias);
    }

    private void service(ProductCriteria criteria) {
        StringBuilder qs = new StringBuilder();
        for (AttributeCriteria attributeCriteria : criteria.getAttributeCriteria()) {
            qs.append(attributeCriteria.getAttributeCode());
        }
        sink(qs.toString());
    }

    public static void sink(String query) {
        System.out.println(query);
    }

    public static class AttributeCriteria {
        private String attributeCode;

        private String attributeValue;

        public String getAttributeCode() {
            return this.attributeCode;
        }

        public String getAttributeValue() {
            return this.attributeValue;
        }
    }

    public static class Criteria {
        private int startIndex;

        private int maxCount;

        private String code;

        private String language;

        private String user;

        private String search;

        private int pageSize;

        public String getCode() {
            return this.code;
        }

        public void setCode(String code) {
            this.code = code;
        }

        public String getLanguage() {
            return this.language;
        }

        public String getUser() {
            return this.user;
        }

        public String getSearch() {
            return this.search;
        }

        public void setPageSize(int pageSize) {
            this.pageSize = pageSize;
        }

        public int getMaxCount() {
            return this.maxCount;
        }

        public int getStartIndex() {
            return this.startIndex;
        }
    }

    public static class ProductCriteria extends Criteria {
        private String name;

        private String productName;

        private List<String> codes;

        private List<AttributeCriteria> attributeCriteria;

        private String origin;

        private Boolean available;

        private List<Long> categoryIds;

        private List<String> availabilities;

        private List<Long> productIds;

        private List<Long> optionValueIds;

        private String sku;

        private String status;

        private Long manufacturerId;

        public String getName() {
            return this.name;
        }

        public String getProductName() {
            return this.productName;
        }

        public List<String> getCodes() {
            return this.codes;
        }

        public List<AttributeCriteria> getAttributeCriteria() {
            return this.attributeCriteria;
        }

        public String getOrigin() {
            return this.origin;
        }

        public Boolean getAvailable() {
            return this.available;
        }

        public List<Long> getCategoryIds() {
            return this.categoryIds;
        }

        public List<String> getAvailabilities() {
            return this.availabilities;
        }

        public List<Long> getProductIds() {
            return this.productIds;
        }

        public List<Long> getOptionValueIds() {
            return this.optionValueIds;
        }

        public String getSku() {
            return this.sku;
        }

        public String getStatus() {
            return this.status;
        }

        public Long getManufacturerId() {
            return this.manufacturerId;
        }
    }
}
