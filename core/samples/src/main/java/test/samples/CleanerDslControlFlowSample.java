package test.samples;

public class CleanerDslControlFlowSample {
    public static class Node {
        public Node child;
        public Node sibling;
        public Level2 k;
    }

    public static class Level2 {
        public Level3 k;
    }

    public static class Level3 {
        public Node value;
    }

    public Node sourceM1() {
        return new Node();
    }

    public Node sourceM2() {
        return new Node();
    }

    public Node sourceM3() {
        return new Node();
    }

    public Node sourceM4() {
        return new Node();
    }

    public Node sourceM5() {
        return new Node();
    }

    public void cleanM1Plain(Node value) { }

    public void cleanM1Any(Node value) { }

    public void cleanM2Any(Node value) { }

    public void cleanM3Any(Node value) { }

    public void cleanM4Any(Node value) { }

    public void cleanM5Any(Node value) { }

    public void cleanM12Any(Node value) { }

    public void cleanM34Any(Node value) { }

    public void cleanAllAny(Node value) { }

    public void sequentialMarks() {
        Node value = sourceM1();
        value.child = sourceM2();
        value.k.k.value = sourceM3();
        sequenceStartSink(value);

        cleanM1Plain(value);
        sequenceAfterM1Sink(value);

        cleanM2Any(value);
        sequenceAfterM2Sink(value);

        value.sibling = sourceM4();
        sequenceAfterM4SourceSink(value);

        cleanM3Any(value);
        sequenceAfterM3Sink(value);

        cleanM4Any(value);
        sequenceAllCleanSink(value);

        value.k.k.value = sourceM1();
        cleanM1Plain(value);
        sequenceNestedAfterPlainSink(value);

        cleanM1Any(value);
        sequenceNestedAfterAnySink(value);
    }

    public void divergentBranches(Node value, boolean firstBranch, boolean secondBranch) {
        if (firstBranch) {
            cleanM12Any(value);
        } else {
            cleanM34Any(value);
        }
        divergentJoinSink(value);

        cleanM5Any(value);
        divergentAfterM5Sink(value);

        if (secondBranch) {
            cleanM12Any(value);
        } else {
            helperCleanM12(value);
        }
        convergentJoinSink(value);
    }

    public void earlyReturnSummaries(Node maybeValue, Node alwaysValue, boolean clean) {
        Node maybeCleaned = maybeCleanM12(maybeValue, clean);
        maybeCleanReturnSink(maybeCleaned);

        Node alwaysCleaned = alwaysCleanM12(alwaysValue, clean);
        alwaysCleanReturnSink(alwaysCleaned);
    }

    private Node maybeCleanM12(Node value, boolean clean) {
        if (clean) {
            cleanM12Any(value);
        }
        return value;
    }

    private Node alwaysCleanM12(Node value, boolean direct) {
        if (direct) {
            cleanM12Any(value);
        } else {
            helperCleanM12(value);
        }
        return value;
    }

    private void helperCleanM12(Node value) {
        cleanM12Any(value);
    }

    public void aliasesAndReassignment(Node value) {
        Node alias = value;
        cleanM12Any(alias);
        aliasOriginalSink(value);

        Node oldAlias = alias;
        alias = sourceM1();
        reassignedOldSink(oldAlias);
        reassignedNewSink(alias);

        cleanAllAny(oldAlias);
        unsanitizedOriginalSink(value);
        independentReassignmentSink(alias);
    }

    public void deepCleanerPipeline(Node cleanedValue, Node controlValue) {
        Node cleaned = pipeline1(cleanedValue);
        deepPipelineCleanedSink(cleaned);

        Node unchanged = identity1(controlValue);
        deepPipelineControlSink(unchanged);
    }

    private Node pipeline1(Node value) {
        Node result = pipeline2(value);
        cleanM1Any(result);
        return result;
    }

    private Node pipeline2(Node value) {
        Node result = pipeline3(value);
        cleanM2Any(result);
        return result;
    }

    private Node pipeline3(Node value) {
        Node result = pipeline4(value);
        cleanM3Any(result);
        return result;
    }

    private Node pipeline4(Node value) {
        Node result = pipeline5(value);
        cleanM4Any(result);
        return result;
    }

    private Node pipeline5(Node value) {
        cleanM5Any(value);
        return value;
    }

    private Node identity1(Node value) {
        return identity2(value);
    }

    private Node identity2(Node value) {
        return identity3(value);
    }

    private Node identity3(Node value) {
        return identity4(value);
    }

    private Node identity4(Node value) {
        return identity5(value);
    }

    private Node identity5(Node value) {
        return value;
    }

    public void doWhileCleaner(Node value, boolean repeat) {
        do {
            cleanM1Any(value);
            if (repeat) {
                cleanM2Any(value);
            }
        } while (repeat);
        doWhileSink(value);
    }

    public void zeroOrMoreCleaner(Node value, boolean repeat) {
        while (repeat) {
            cleanM34Any(value);
        }
        zeroOrMoreSink(value);
    }

    public void independentBranchValues(Node left, Node right, boolean firstBranch) {
        if (firstBranch) {
            cleanM12Any(left);
            cleanM34Any(right);
        } else {
            cleanM34Any(left);
            cleanM12Any(right);
        }

        independentLeftJoinSink(left);
        independentRightJoinSink(right);

        cleanAllAny(left);
        independentLeftCleanedSink(left);
        independentRightUnchangedSink(right);
    }

    public void cleanThenRetain() {
        Node value = new Node();
        value.child = sourceM1();
        cleanAllAny(value);
        cleanBeforeNewSourceSink(value);

        value.child = sourceM2();
        newSourceAfterCleanSink(value);

        cleanM2Any(value);
        newSourceCleanedSink(value);
    }

    public void sequenceStartSink(Node value) { }
    public void sequenceAfterM1Sink(Node value) { }
    public void sequenceAfterM2Sink(Node value) { }
    public void sequenceAfterM4SourceSink(Node value) { }
    public void sequenceAfterM3Sink(Node value) { }
    public void sequenceAllCleanSink(Node value) { }
    public void sequenceNestedAfterPlainSink(Node value) { }
    public void sequenceNestedAfterAnySink(Node value) { }
    public void divergentJoinSink(Node value) { }
    public void divergentAfterM5Sink(Node value) { }
    public void convergentJoinSink(Node value) { }
    public void maybeCleanReturnSink(Node value) { }
    public void alwaysCleanReturnSink(Node value) { }
    public void aliasOriginalSink(Node value) { }
    public void reassignedOldSink(Node value) { }
    public void reassignedNewSink(Node value) { }
    public void unsanitizedOriginalSink(Node value) { }
    public void independentReassignmentSink(Node value) { }
    public void deepPipelineCleanedSink(Node value) { }
    public void deepPipelineControlSink(Node value) { }
    public void doWhileSink(Node value) { }
    public void zeroOrMoreSink(Node value) { }
    public void independentLeftJoinSink(Node value) { }
    public void independentRightJoinSink(Node value) { }
    public void independentLeftCleanedSink(Node value) { }
    public void independentRightUnchangedSink(Node value) { }
    public void cleanBeforeNewSourceSink(Node value) { }
    public void newSourceAfterCleanSink(Node value) { }
    public void newSourceCleanedSink(Node value) { }
}
