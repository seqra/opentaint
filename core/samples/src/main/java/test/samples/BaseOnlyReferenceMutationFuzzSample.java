package test.samples;

public class BaseOnlyReferenceMutationFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }
    private static String identity(String value) { return value; }
    private static Box alias(Box box) { return box; }

    private static void setLabel(Box box, String value) { box.setLabel(value); }
    private static void setPeer(Box box, Peer value) { box.setPeer(value); }
    private static void setBoth(Box box, String first, String second) { box.setMetadata(first, second); }
    private static void setReferences(Box box, Peer peer, Node node) { box.setReferences(peer, node); }
    private static void nestedSetLabel(Box box, String value) { setLabel(box, value); }
    private static Box touchAndReturn(Box box, String value) { box.setLabel(value); return box; }
    private static Holder makeHolder(Box box) { return new Holder(box); }
    private static Holder makeHolder(Box box, String name) { return new Holder(box, name); }
    private static Holder makeAliasedHolder(Box box) { return new Holder(alias(box)); }
    private static Pair makePairFirst(Box box) { return new Pair(box, new Box()); }
    private static Pair makePairSecond(Box box) { return new Pair(new Box(), box); }
    private static Triple makeTripleFirst(Box box) { return new Triple(box, new Box(), new Box()); }
    private static Quad makeQuadFirst(Box box) { return new Quad(box, new Box(), new Box(), new Box()); }
    private static Quad makeQuadSecond(Box box) { return new Quad(new Box(), box, new Box(), new Box()); }
    private static Quad makeQuadThird(Box box) { return new Quad(new Box(), new Box(), box, new Box()); }
    private static Quad makeQuadFourth(Box box) { return new Quad(new Box(), new Box(), new Box(), box); }
    private static void installBox(Holder holder, Box box) { holder.setBox(box); }
    private static void installBox(Holder holder, Box box, String name) { holder.setBoxAndName(box, name); }
    private static void installPrimary(AlternateHolder holder, Box box) { holder.setPrimary(box); }
    private static void installSecondary(AlternateHolder holder, Box box) { holder.setSecondary(box); }
    private static void nestedInstallPrimary(AlternateHolder holder, Box box) { installPrimary(holder, box); }
    private static AlternateHolder makeAlternatePrimary(Box box) { return new AlternateHolder(box, new Box()); }
    private static KeyedHolder makeKeyedLeft(Box box) { return new KeyedHolder(box, new Box(), new Box()); }
    private static KeyedHolder makeKeyedCenter(Box box) { return new KeyedHolder(new Box(), box, new Box()); }

    public static void directStringMetadataSetter() {
        Box box = new Box(); box.setPayload(source()); box.setLabel("safe"); sink(box.getPayload());
    }

    public static void directCategorySetter() {
        Box box = new Box(); box.setPayload(source()); box.setCategory("safe"); sink(box.getPayload());
    }

    public static void directPeerSetter() {
        Box box = new Box(); box.setPayload(source()); box.setPeer(new Peer()); sink(box.getPayload());
    }

    public static void directNodeSetter() {
        Box box = new Box(); box.setPayload(source()); box.setNode(new Node()); sink(box.getPayload());
    }

    public static void nullPeerSetter() {
        Box box = new Box(); box.setPayload(source()); box.setPeer(null); sink(box.getPayload());
    }

    public static void identityMetadataSetter() {
        Box box = new Box(); box.setPayload(source()); box.setLabel(identity("safe")); sink(box.getPayload());
    }

    public static void aliasedReceiverSetter() {
        Box box = new Box(); box.setPayload(source()); alias(box).setLabel("safe"); sink(box.getPayload());
    }

    public static void castReceiverSetter() {
        Box box = new Box(); box.setPayload(source()); ((Box) box).setCategory("safe"); sink(box.getPayload());
    }

    public static void twoDifferentReferenceSetters() {
        Box box = new Box(); box.setPayload(source()); box.setLabel("safe"); box.setPeer(new Peer()); sink(box.getPayload());
    }

    public static void sameReferenceSetterTwice() {
        Box box = new Box(); box.setPayload(source()); box.setLabel("first"); box.setLabel("second"); sink(box.getPayload());
    }

    public static void holderConstructorAfterTaint() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(box); sink(holder.box.getPayload());
    }

    public static void namedHolderConstructorAfterTaint() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(box, "safe"); sink(holder.box.getPayload());
    }

    public static void holderFactoryAfterTaint() {
        Box box = new Box(); box.setPayload(source()); Holder holder = makeHolder(box); sink(holder.box.getPayload());
    }

    public static void namedHolderFactoryAfterTaint() {
        Box box = new Box(); box.setPayload(source()); Holder holder = makeHolder(box, "safe"); sink(holder.box.getPayload());
    }

    public static void envelopeConstructorAfterTaint() {
        Box box = new Box(); box.setPayload(source()); Envelope envelope = new Envelope(new Holder(box)); sink(envelope.holder.box.getPayload());
    }

    public static void pairConstructorFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Pair pair = new Pair(box, new Box()); sink(pair.first.getPayload());
    }

    public static void pairConstructorSecondArgument() {
        Box box = new Box(); box.setPayload(source()); Pair pair = new Pair(new Box(), box); sink(pair.second.getPayload());
    }

    public static void assignBoxThroughHolderSetter() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); holder.setBox(box); sink(holder.box.getPayload());
    }

    public static void holderConstructorAliasArgument() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(alias(box)); sink(holder.box.getPayload());
    }

    public static void holderConstructorLocalAlias() {
        Box box = new Box(); box.setPayload(source()); Box other = box; Holder holder = new Holder(other); sink(holder.box.getPayload());
    }

    public static void holderConstructorCastArgument() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder((Box) box); sink(holder.box.getPayload());
    }

    public static void holderConstructorNullMetadata() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(box, null); sink(holder.box.getPayload());
    }

    public static void holderConstructorIdentityMetadata() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(box, identity("safe")); sink(holder.box.getPayload());
    }

    public static void tripleConstructorFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Triple value = new Triple(box, new Box(), new Box()); sink(value.first.getPayload());
    }

    public static void tripleConstructorMiddleArgument() {
        Box box = new Box(); box.setPayload(source()); Triple value = new Triple(new Box(), box, new Box()); sink(value.second.getPayload());
    }

    public static void tripleConstructorLastArgument() {
        Box box = new Box(); box.setPayload(source()); Triple value = new Triple(new Box(), new Box(), box); sink(value.third.getPayload());
    }

    public static void tripleFactoryFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Triple value = makeTripleFirst(box); sink(value.first.getPayload());
    }

    public static void pairFactoryFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Pair value = makePairFirst(box); sink(value.first.getPayload());
    }

    public static void pairFactorySecondArgument() {
        Box box = new Box(); box.setPayload(source()); Pair value = makePairSecond(box); sink(value.second.getPayload());
    }

    public static void holderFactoryAliasedArgument() {
        Box box = new Box(); box.setPayload(source()); Holder holder = makeAliasedHolder(box); sink(holder.box.getPayload());
    }

    public static void holderFactoryCastArgument() {
        Box box = new Box(); box.setPayload(source()); Holder holder = makeHolder((Box) box); sink(holder.box.getPayload());
    }

    public static void nestedHolderFactory() {
        Box box = new Box(); box.setPayload(source()); Envelope value = new Envelope(makeHolder(box)); sink(value.holder.box.getPayload());
    }

    public static void doubleEnvelopeConstructor() {
        Box box = new Box(); box.setPayload(source()); DoubleEnvelope value = new DoubleEnvelope(new Envelope(new Holder(box))); sink(value.envelope.holder.box.getPayload());
    }

    public static void envelopeWithMetadataConstructor() {
        Box box = new Box(); box.setPayload(source()); NamedEnvelope value = new NamedEnvelope(new Holder(box), "safe"); sink(value.holder.box.getPayload());
    }

    public static void holderSetterViaHelper() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); installBox(holder, box); sink(holder.box.getPayload());
    }

    public static void holderSetterWithMetadataViaHelper() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); installBox(holder, box, "safe"); sink(holder.box.getPayload());
    }

    public static void holderSetterAliasArgument() {
        Box box = new Box(); box.setPayload(source()); Box other = box; Holder holder = new Holder(); holder.setBox(other); sink(holder.box.getPayload());
    }

    public static void holderSetterCastArgument() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); holder.setBox((Box) box); sink(holder.box.getPayload());
    }

    public static void holderOverwriteSafeThenTainted() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(new Box()); holder.setBox(box); sink(holder.box.getPayload());
    }

    public static void holderOverwriteTaintedTwice() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); holder.setBox(box); holder.setBox(box); sink(holder.box.getPayload());
    }

    public static void alternateHolderPrimaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(); holder.setPrimary(box); sink(holder.primary.getPayload());
    }

    public static void alternateHolderSecondaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(); holder.setSecondary(box); sink(holder.secondary.getPayload());
    }

    public static void alternateConstructorPrimaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(box, new Box()); sink(holder.primary.getPayload());
    }

    public static void alternateConstructorSecondaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(new Box(), box); sink(holder.secondary.getPayload());
    }

    public static void alternateOverwritePrimaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(new Box(), new Box()); holder.setPrimary(box); sink(holder.primary.getPayload());
    }

    public static void alternateOverwriteSecondaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder holder = new AlternateHolder(new Box(), new Box()); holder.setSecondary(box); sink(holder.secondary.getPayload());
    }

    public static void namedHolderSetBoxAndName() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); holder.setBoxAndName(box, "safe"); sink(holder.box.getPayload());
    }

    public static void namedHolderSetBoxAndNullName() {
        Box box = new Box(); box.setPayload(source()); Holder holder = new Holder(); holder.setBoxAndName(box, null); sink(holder.box.getPayload());
    }

    public static void pairThenEnvelopeFirstField() {
        Box box = new Box(); box.setPayload(source()); Pair pair = new Pair(box, new Box()); PairEnvelope value = new PairEnvelope(pair); sink(value.pair.first.getPayload());
    }

    public static void pairThenEnvelopeSecondField() {
        Box box = new Box(); box.setPayload(source()); Pair pair = new Pair(new Box(), box); PairEnvelope value = new PairEnvelope(pair); sink(value.pair.second.getPayload());
    }

    public static void quadConstructorFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(box, new Box(), new Box(), new Box()); sink(value.first.getPayload());
    }

    public static void quadConstructorSecondArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(new Box(), box, new Box(), new Box()); sink(value.second.getPayload());
    }

    public static void quadConstructorThirdArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(new Box(), new Box(), box, new Box()); sink(value.third.getPayload());
    }

    public static void quadConstructorFourthArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(new Box(), new Box(), new Box(), box); sink(value.fourth.getPayload());
    }

    public static void quadFactoryFirstArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = makeQuadFirst(box); sink(value.first.getPayload());
    }

    public static void quadFactorySecondArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = makeQuadSecond(box); sink(value.second.getPayload());
    }

    public static void quadFactoryThirdArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = makeQuadThird(box); sink(value.third.getPayload());
    }

    public static void quadFactoryFourthArgument() {
        Box box = new Box(); box.setPayload(source()); Quad value = makeQuadFourth(box); sink(value.fourth.getPayload());
    }

    public static void keyedConstructorLeftField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(box, new Box(), new Box()); sink(value.left.getPayload());
    }

    public static void keyedConstructorCenterField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(new Box(), box, new Box()); sink(value.center.getPayload());
    }

    public static void keyedConstructorRightField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(new Box(), new Box(), box); sink(value.right.getPayload());
    }

    public static void keyedSetterLeftField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(); value.setLeft(box); sink(value.left.getPayload());
    }

    public static void keyedSetterCenterField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(); value.setCenter(box); sink(value.center.getPayload());
    }

    public static void keyedSetterRightField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(); value.setRight(box); sink(value.right.getPayload());
    }

    public static void alternatePrimaryViaHelper() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); installPrimary(value, box); sink(value.primary.getPayload());
    }

    public static void alternateSecondaryViaHelper() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); installSecondary(value, box); sink(value.secondary.getPayload());
    }

    public static void alternatePrimaryViaNestedHelper() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); nestedInstallPrimary(value, box); sink(value.primary.getPayload());
    }

    public static void alternatePrimaryViaFactory() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = makeAlternatePrimary(box); sink(value.primary.getPayload());
    }

    public static void alternatePrimaryNullThenTainted() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setPrimary(null); value.setPrimary(box); sink(value.primary.getPayload());
    }

    public static void alternateSecondaryNullThenTainted() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setSecondary(null); value.setSecondary(box); sink(value.secondary.getPayload());
    }

    public static void alternatePrimarySafeThenTaintedViaHelper() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(new Box(), new Box()); installPrimary(value, box); sink(value.primary.getPayload());
    }

    public static void holderNullThenTainted() {
        Box box = new Box(); box.setPayload(source()); Holder value = new Holder(); value.setBox(null); value.setBox(box); sink(value.box.getPayload());
    }

    public static void holderTaintedNullThenTainted() {
        Box box = new Box(); box.setPayload(source()); Holder value = new Holder(); value.setBox(box); value.setBox(null); value.setBox(box); sink(value.box.getPayload());
    }

    public static void quadEnvelopeFirstField() {
        Box box = new Box(); box.setPayload(source()); QuadEnvelope value = new QuadEnvelope(new Quad(box, new Box(), new Box(), new Box())); sink(value.quad.first.getPayload());
    }

    public static void quadEnvelopeFourthField() {
        Box box = new Box(); box.setPayload(source()); QuadEnvelope value = new QuadEnvelope(new Quad(new Box(), new Box(), new Box(), box)); sink(value.quad.fourth.getPayload());
    }

    public static void alternateEnvelopePrimaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateEnvelope value = new AlternateEnvelope(new AlternateHolder(box, new Box())); sink(value.holder.primary.getPayload());
    }

    public static void alternateEnvelopeSecondaryField() {
        Box box = new Box(); box.setPayload(source()); AlternateEnvelope value = new AlternateEnvelope(new AlternateHolder(new Box(), box)); sink(value.holder.secondary.getPayload());
    }

    public static void alternateSetBothFirstArgument() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setBoth(box, new Box()); sink(value.primary.getPayload());
    }

    public static void alternateSetBothSecondArgument() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setBoth(new Box(), box); sink(value.secondary.getPayload());
    }

    public static void keyedSetAllCenterArgument() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(); value.setAll(new Box(), box, new Box()); sink(value.center.getPayload());
    }

    public static void quadConstructorFirstWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(box, null, null, null); sink(value.first.getPayload());
    }

    public static void quadConstructorSecondWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(null, box, null, null); sink(value.second.getPayload());
    }

    public static void quadConstructorThirdWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(null, null, box, null); sink(value.third.getPayload());
    }

    public static void quadConstructorFourthWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); Quad value = new Quad(null, null, null, box); sink(value.fourth.getPayload());
    }

    public static void keyedConstructorLeftWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(box, null, null); sink(value.left.getPayload());
    }

    public static void keyedConstructorCenterWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(null, box, null); sink(value.center.getPayload());
    }

    public static void keyedConstructorRightWithNullPeers() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(null, null, box); sink(value.right.getPayload());
    }

    public static void keyedEnvelopeLeftField() {
        Box box = new Box(); box.setPayload(source()); KeyedEnvelope value = new KeyedEnvelope(new KeyedHolder(box, new Box(), new Box())); sink(value.holder.left.getPayload());
    }

    public static void keyedEnvelopeCenterField() {
        Box box = new Box(); box.setPayload(source()); KeyedEnvelope value = new KeyedEnvelope(new KeyedHolder(new Box(), box, new Box())); sink(value.holder.center.getPayload());
    }

    public static void keyedEnvelopeRightField() {
        Box box = new Box(); box.setPayload(source()); KeyedEnvelope value = new KeyedEnvelope(new KeyedHolder(new Box(), new Box(), box)); sink(value.holder.right.getPayload());
    }

    public static void doubleAlternateEnvelopePrimaryField() {
        Box box = new Box(); box.setPayload(source()); DoubleAlternateEnvelope value = new DoubleAlternateEnvelope(new AlternateEnvelope(new AlternateHolder(box, new Box()))); sink(value.envelope.holder.primary.getPayload());
    }

    public static void doubleAlternateEnvelopeSecondaryField() {
        Box box = new Box(); box.setPayload(source()); DoubleAlternateEnvelope value = new DoubleAlternateEnvelope(new AlternateEnvelope(new AlternateHolder(new Box(), box))); sink(value.envelope.holder.secondary.getPayload());
    }

    public static void keyedOverwriteLeftSafeThenTainted() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(new Box(), new Box(), new Box()); value.setLeft(box); sink(value.left.getPayload());
    }

    public static void keyedOverwriteCenterSafeThenTainted() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(new Box(), new Box(), new Box()); value.setCenter(box); sink(value.center.getPayload());
    }

    public static void keyedOverwriteRightSafeThenTainted() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = new KeyedHolder(new Box(), new Box(), new Box()); value.setRight(box); sink(value.right.getPayload());
    }

    public static void alternateSetBothFirstWithNullPeer() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setBoth(box, null); sink(value.primary.getPayload());
    }

    public static void alternateSetBothSecondWithNullPeer() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(); value.setBoth(null, box); sink(value.secondary.getPayload());
    }

    public static void keyedFactoryLeftField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = makeKeyedLeft(box); sink(value.left.getPayload());
    }

    public static void keyedFactoryCenterField() {
        Box box = new Box(); box.setPayload(source()); KeyedHolder value = makeKeyedCenter(box); sink(value.center.getPayload());
    }

    public static void alternateConstructorPrimaryWithNullPeer() {
        Box box = new Box(); box.setPayload(source()); AlternateHolder value = new AlternateHolder(box, null); sink(value.primary.getPayload());
    }

    public static void helperStringSetter() {
        Box box = new Box(); box.setPayload(source()); setLabel(box, "safe"); sink(box.getPayload());
    }

    public static void helperPeerSetter() {
        Box box = new Box(); box.setPayload(source()); setPeer(box, new Peer()); sink(box.getPayload());
    }

    public static void nestedHelperStringSetter() {
        Box box = new Box(); box.setPayload(source()); nestedSetLabel(box, "safe"); sink(box.getPayload());
    }

    public static void helperReturnsMutatedReceiver() {
        Box box = new Box(); box.setPayload(source()); box = touchAndReturn(box, "safe"); sink(box.getPayload());
    }

    public static void helperOnAliasedReceiver() {
        Box box = new Box(); box.setPayload(source()); Box other = box; setLabel(other, "safe"); sink(box.getPayload());
    }

    public static void directThenHelperSetter() {
        Box box = new Box(); box.setPayload(source()); box.setCategory("safe"); setLabel(box, "safe"); sink(box.getPayload());
    }

    public static void helperThenDirectSetter() {
        Box box = new Box(); box.setPayload(source()); setLabel(box, "safe"); box.setCategory("safe"); sink(box.getPayload());
    }

    public static void twoArgumentInstanceSetter() {
        Box box = new Box(); box.setPayload(source()); box.setMetadata("left", "right"); sink(box.getPayload());
    }

    public static void twoArgumentHelperSetter() {
        Box box = new Box(); box.setPayload(source()); setBoth(box, "left", "right"); sink(box.getPayload());
    }

    public static void twoReferenceInstanceSetter() {
        Box box = new Box(); box.setPayload(source()); box.setReferences(new Peer(), new Node()); sink(box.getPayload());
    }

    public static void twoReferenceHelperSetter() {
        Box box = new Box(); box.setPayload(source()); setReferences(box, new Peer(), new Node()); sink(box.getPayload());
    }

    public static void multiArgumentSetterWithAliases() {
        Box box = new Box(); box.setPayload(source()); String left = "left"; String right = left; box.setMetadata(left, right); sink(box.getPayload());
    }

    public static void multiArgumentSetterWithNull() {
        Box box = new Box(); box.setPayload(source()); box.setMetadata(null, "right"); sink(box.getPayload());
    }

    public static void overwritePeerTwice() {
        Box box = new Box(); box.setPayload(source()); box.setPeer(new Peer()); box.setPeer(new Peer()); sink(box.getPayload());
    }

    public static void overwriteNodeWithNull() {
        Box box = new Box(); box.setPayload(source()); box.setNode(new Node()); box.setNode(null); sink(box.getPayload());
    }

    public static void overwriteLabelNullThenValue() {
        Box box = new Box(); box.setPayload(source()); box.setLabel(null); box.setLabel("safe"); sink(box.getPayload());
    }

    public static void overwriteCategoryViaIdentity() {
        Box box = new Box(); box.setPayload(source()); box.setCategory("first"); box.setCategory(identity("second")); sink(box.getPayload());
    }

    public static void prebuiltContainerFieldSetter() {
        Container container = new Container(new Box()); container.box.setPayload(source()); container.box.setLabel("safe"); sink(container.box.getPayload());
    }

    public static void prebuiltDoubleContainerFieldSetter() {
        DoubleContainer root = new DoubleContainer(new Container(new Box())); root.container.box.setPayload(source()); root.container.box.setCategory("safe"); sink(root.container.box.getPayload());
    }

    public static void fieldChainAliasSetter() {
        Container container = new Container(new Box()); container.box.setPayload(source()); Box local = container.box; local.setPeer(new Peer()); sink(container.box.getPayload());
    }

    public static void fieldChainHelperSetter() {
        Container container = new Container(new Box()); container.box.setPayload(source()); setLabel(container.box, "safe"); sink(container.box.getPayload());
    }

    public static void siblingFieldSetterAfterNestedTaint() {
        Container container = new Container(new Box()); container.box.setPayload(source()); container.setName("safe"); sink(container.box.getPayload());
    }

    private static class Box {
        private String payload;
        private String label;
        private String category;
        private Peer peer;
        private Node node;
        void setPayload(String value) { payload = value; }
        String getPayload() { return payload; }
        void setLabel(String value) { label = value; }
        void setCategory(String value) { category = value; }
        void setPeer(Peer value) { peer = value; }
        void setNode(Node value) { node = value; }
        void setMetadata(String first, String second) { label = first; category = second; }
        void setReferences(Peer first, Node second) { peer = first; node = second; }
    }

    private static final class Peer { }
    private static final class Node { }

    private static final class Holder {
        private Box box;
        private String name;
        Holder() { }
        Holder(Box box) { this.box = box; }
        Holder(Box box, String name) { this.box = box; this.name = name; }
        void setBox(Box value) { box = value; }
        void setBoxAndName(Box value, String name) { box = value; this.name = name; }
    }

    private static final class Envelope {
        private final Holder holder;
        Envelope(Holder holder) { this.holder = holder; }
    }

    private static final class Pair {
        private final Box first;
        private final Box second;
        Pair(Box first, Box second) { this.first = first; this.second = second; }
    }

    private static final class Triple {
        private final Box first;
        private final Box second;
        private final Box third;
        Triple(Box first, Box second, Box third) { this.first = first; this.second = second; this.third = third; }
    }

    private static final class Quad {
        private final Box first;
        private final Box second;
        private final Box third;
        private final Box fourth;
        Quad(Box first, Box second, Box third, Box fourth) { this.first = first; this.second = second; this.third = third; this.fourth = fourth; }
    }

    private static final class AlternateHolder {
        private Box primary;
        private Box secondary;
        AlternateHolder() { }
        AlternateHolder(Box primary, Box secondary) { this.primary = primary; this.secondary = secondary; }
        void setPrimary(Box value) { primary = value; }
        void setSecondary(Box value) { secondary = value; }
        void setBoth(Box first, Box second) { primary = first; secondary = second; }
    }

    private static final class KeyedHolder {
        private Box left;
        private Box center;
        private Box right;
        KeyedHolder() { }
        KeyedHolder(Box left, Box center, Box right) { this.left = left; this.center = center; this.right = right; }
        void setLeft(Box value) { left = value; }
        void setCenter(Box value) { center = value; }
        void setRight(Box value) { right = value; }
        void setAll(Box left, Box center, Box right) { this.left = left; this.center = center; this.right = right; }
    }

    private static final class QuadEnvelope {
        private final Quad quad;
        QuadEnvelope(Quad quad) { this.quad = quad; }
    }

    private static final class AlternateEnvelope {
        private final AlternateHolder holder;
        AlternateEnvelope(AlternateHolder holder) { this.holder = holder; }
    }

    private static final class KeyedEnvelope {
        private final KeyedHolder holder;
        KeyedEnvelope(KeyedHolder holder) { this.holder = holder; }
    }

    private static final class DoubleAlternateEnvelope {
        private final AlternateEnvelope envelope;
        DoubleAlternateEnvelope(AlternateEnvelope envelope) { this.envelope = envelope; }
    }

    private static final class DoubleEnvelope {
        private final Envelope envelope;
        DoubleEnvelope(Envelope envelope) { this.envelope = envelope; }
    }

    private static final class NamedEnvelope {
        private final Holder holder;
        private final String name;
        NamedEnvelope(Holder holder, String name) { this.holder = holder; this.name = name; }
    }

    private static final class PairEnvelope {
        private final Pair pair;
        PairEnvelope(Pair pair) { this.pair = pair; }
    }

    private static final class Container {
        private final Box box;
        private String name;
        Container(Box box) { this.box = box; }
        void setName(String value) { name = value; }
    }

    private static final class DoubleContainer {
        private final Container container;
        DoubleContainer(Container container) { this.container = container; }
    }
}
