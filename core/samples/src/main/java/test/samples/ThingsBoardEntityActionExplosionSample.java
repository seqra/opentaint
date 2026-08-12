package test.samples;

public class ThingsBoardEntityActionExplosionSample {
    private static String source() {
        return "tainted";
    }

    private static void sink(String value) {
    }

    public static void entityActionExplosion(int entityKind, int action) {
        String tainted = source();
        Object[] additionalInfo = new Object[]{tainted, tainted, tainted};
        switch (entityKind) {
            case 0:
                pushEntityActionToRuleEngine(
                        new AssetId(tainted), new Asset(tainted), new AdminUser(tainted), action, additionalInfo);
                break;
            case 1:
                pushEntityActionToRuleEngine(
                        new DeviceId(tainted), new Device(tainted), new CustomerUser(tainted), action, additionalInfo);
                break;
            case 2:
                pushEntityActionToRuleEngine(
                        new DashboardId(tainted), new Dashboard(tainted), new AdminUser(tainted), action, additionalInfo);
                break;
            case 3:
                pushEntityActionToRuleEngine(
                        new RuleChainId(tainted), new RuleChain(tainted), new CustomerUser(tainted), action, additionalInfo);
                break;
            case 4:
                pushEntityActionToRuleEngine(
                        new AssetId(tainted), new Asset(tainted), new CustomerUser(tainted), action, additionalInfo);
                break;
            default:
                pushEntityActionToRuleEngine(
                        new DeviceId(tainted), new Device(tainted), new AdminUser(tainted), action, additionalInfo);
                break;
        }
    }

    public static void singleEntityAction(int action) {
        String tainted = source();
        pushEntityActionToRuleEngine(
                new AssetId(tainted),
                new Asset(tainted),
                new AdminUser(tainted),
                action,
                new Object[]{tainted, tainted, tainted});
    }

    public static void controlOnlyFanout(int selector) {
        String value = source();
        if (selector == 0) {
            // control-only branch
        } else if (selector == 1) {
            // control-only branch
        } else if (selector == 2) {
            // control-only branch
        } else if (selector == 3) {
            // control-only branch
        } else if (selector == 4) {
            // control-only branch
        } else if (selector == 5) {
            // control-only branch
        } else if (selector == 6) {
            // control-only branch
        } else if (selector == 7) {
            // control-only branch
        }
        sink(value);
    }

    public static void contextSupportedSideEffectBatch() {
        String tainted = source();
        safeContextSink(processContext(new SafeContextA(), tainted));
        safeContextSink(processContext(new SafeContextB(), tainted));
        safeContextSink(processContext(new SafeContextC(), tainted));
        safeContextSink(processContext(new SafeContextD(), tainted));
        safeContextSink(processContext(new SafeContextE(), tainted));
        safeContextSink(processContext(new SafeContextF(), tainted));
        taintedContextSink(processContext(new TaintedContext(), tainted));
    }

    public static void singleContextSupportedSideEffect() {
        taintedContextSink(processContext(new TaintedContext(), source()));
    }

    private static String processContext(Context context, String value) {
        ContextBox box = new ContextBox();
        storeContextValue(box, value);
        return context.select(box.value);
    }

    private static void storeContextValue(ContextBox box, String value) {
        box.value = value;
    }

    private static void safeContextSink(String value) {
    }

    private static void taintedContextSink(String value) {
    }

    private static void pushEntityActionToRuleEngine(
            EntityId entityId,
            HasName entity,
            User user,
            int action,
            Object... additionalInfo) {
        MetaData metaData = new MetaData();
        if (user != null) {
            metaData.putValue("userId", user.getId());
            metaData.putValue("userName", user.getName());
            metaData.putValue("userEmail", user.getEmail());
            if (user.getFirstName() != null) {
                metaData.putValue("userFirstName", user.getFirstName());
            }
            if (user.getLastName() != null) {
                metaData.putValue("userLastName", user.getLastName());
            }
        }

        if (action == 0) {
            metaData.putValue("assignedCustomerId", extractParameter(String.class, 0, additionalInfo));
            metaData.putValue("assignedCustomerName", extractParameter(String.class, 1, additionalInfo));
        } else if (action == 1) {
            metaData.putValue("unassignedCustomerId", extractParameter(String.class, 0, additionalInfo));
            metaData.putValue("unassignedCustomerName", extractParameter(String.class, 1, additionalInfo));
        } else if (action == 2) {
            metaData.putValue("assignedTenantId", extractParameter(String.class, 0, additionalInfo));
            metaData.putValue("assignedTenantName", extractParameter(String.class, 1, additionalInfo));
        } else if (action == 3) {
            metaData.putValue("assignedEdgeId", extractParameter(String.class, 0, additionalInfo));
            metaData.putValue("assignedEdgeName", extractParameter(String.class, 1, additionalInfo));
        } else if (action == 4) {
            metaData.putValue("comment", extractParameter(String.class, 0, additionalInfo));
        }

        EntityNode entityNode = new EntityNode();
        if (entity != null) {
            entityNode.put("entityName", entity.getName());
            entityNode.put("entityType", entityId.getEntityType());
            if (action == 5) {
                entityNode.put("attributeScope", extractParameter(String.class, 0, additionalInfo));
                entityNode.put("attributeValue", extractParameter(String.class, 1, additionalInfo));
            } else if (action == 6) {
                entityNode.put("timeseriesKey", extractParameter(String.class, 0, additionalInfo));
                entityNode.put("timeseriesValue", extractParameter(String.class, 1, additionalInfo));
            } else if (action == 7) {
                entityNode.put("relation", extractParameter(String.class, 2, additionalInfo));
            }
        }

        sink(metaData.value);
        sink(entityNode.value);
    }

    private static <T> T extractParameter(Class<T> type, int index, Object... additionalInfo) {
        if (additionalInfo != null && additionalInfo.length > index) {
            Object value = additionalInfo[index];
            if (type.isInstance(value)) {
                return type.cast(value);
            }
        }
        return null;
    }

    private interface EntityId {
        String getEntityType();
    }

    private interface HasName {
        String getName();
    }

    private interface User {
        String getId();
        String getName();
        String getEmail();
        String getFirstName();
        String getLastName();
    }

    private abstract static class ValueHolder {
        final String value;

        ValueHolder(String value) {
            this.value = value;
        }
    }

    private static final class AssetId extends ValueHolder implements EntityId {
        AssetId(String value) { super(value); }
        public String getEntityType() { return value; }
    }

    private static final class DeviceId extends ValueHolder implements EntityId {
        DeviceId(String value) { super(value); }
        public String getEntityType() { return value; }
    }

    private static final class DashboardId extends ValueHolder implements EntityId {
        DashboardId(String value) { super(value); }
        public String getEntityType() { return value; }
    }

    private static final class RuleChainId extends ValueHolder implements EntityId {
        RuleChainId(String value) { super(value); }
        public String getEntityType() { return value; }
    }

    private static final class Asset extends ValueHolder implements HasName {
        Asset(String value) { super(value); }
        public String getName() { return value; }
    }

    private static final class Device extends ValueHolder implements HasName {
        Device(String value) { super(value); }
        public String getName() { return value; }
    }

    private static final class Dashboard extends ValueHolder implements HasName {
        Dashboard(String value) { super(value); }
        public String getName() { return value; }
    }

    private static final class RuleChain extends ValueHolder implements HasName {
        RuleChain(String value) { super(value); }
        public String getName() { return value; }
    }

    private abstract static class BaseUser extends ValueHolder implements User {
        BaseUser(String value) { super(value); }
        public String getId() { return value; }
        public String getName() { return value; }
        public String getEmail() { return value; }
        public String getFirstName() { return value; }
        public String getLastName() { return value; }
    }

    private static final class AdminUser extends BaseUser {
        AdminUser(String value) { super(value); }
    }

    private static final class CustomerUser extends BaseUser {
        CustomerUser(String value) { super(value); }
    }

    private static final class MetaData {
        String value;

        void putValue(String key, String value) {
            this.value = value;
        }
    }

    private static final class EntityNode {
        String value;

        void put(String key, String value) {
            this.value = value;
        }
    }

    private interface Context {
        String select(String value);
    }

    private static final class SafeContextA implements Context {
        public String select(String value) { return "safe-a"; }
    }

    private static final class SafeContextB implements Context {
        public String select(String value) { return "safe-b"; }
    }

    private static final class SafeContextC implements Context {
        public String select(String value) { return "safe-c"; }
    }

    private static final class SafeContextD implements Context {
        public String select(String value) { return "safe-d"; }
    }

    private static final class SafeContextE implements Context {
        public String select(String value) { return "safe-e"; }
    }

    private static final class SafeContextF implements Context {
        public String select(String value) { return "safe-f"; }
    }

    private static final class TaintedContext implements Context {
        public String select(String value) { return value; }
    }

    private static final class ContextBox {
        String value;
    }
}
