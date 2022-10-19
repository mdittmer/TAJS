package ca.uwaterloo.tajs.souffle;

import java.io.BufferedInputStream;
import java.io.InputStream;
import java.net.URL;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.nio.ByteBuffer;

import org.apache.log4j.Logger;

import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.SourceLocation;


import static dk.brics.tajs.util.Collections.newList;
import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

public class IdentityTracker {
    private static final MessageDigest emptyMessageDigest = prepareEmptyMessageDigest();
    private static MessageDigest prepareEmptyMessageDigest() {
        MessageDigest md = null;
        try {
            md = MessageDigest.getInstance("SHA-256");
            md.clone();
            return md;
        } catch (Exception e) {
            System.err.println(e);
            e.printStackTrace(System.err);
            System.exit(1);
        }
        return md;
    }
    private static final Logger log = Logger.getLogger(IdentityTracker.class);

    private Tracker nodes;
    private Tracker basicBlocks;
    private Tracker functions;

    public IdentityTracker() {
        Map<URL, MessageDigest> sharedSources = newMap();
        this.nodes = new Tracker("Node", sharedSources);
        this.basicBlocks = new Tracker("BasicBlock", sharedSources);
        this.functions = new Tracker("Function", sharedSources);
    }

    public int getID(AbstractNode node) throws Exception {
        return nodes.getUnique(node);
    }

    public int getID(BasicBlock basicBlock) throws Exception {
        return basicBlocks.getUnique(basicBlock);
    }

    public int getID(Function function) throws Exception {
        return functions.getUnique(function);
    }

    private class Identified {
        private AbstractNode node;
        private BasicBlock basicBlock;
        private Function function;

        public Identified(AbstractNode node) {
            this.node = node;
            this.basicBlock = null;
            this.function = null;
        }

        public Identified(BasicBlock basicBlock) {
            this.node = null;
            this.basicBlock = basicBlock;
            this.function = null;
        }

        public Identified(Function function) {
            this.node = null;
            this.basicBlock = null;
            this.function = function;
        }

        public int getIndex() {
            if (this.node != null) {
                return this.node.getIndex();
            } else if (this.basicBlock != null) {
                return this.basicBlock.getIndex();
            } else {
                return this.function.getIndex();
            }
        }

        public SourceLocation getStartSourceLocation() {
            if (this.node != null) {
                return this.node.getSourceLocation();
            } else if (this.basicBlock != null) {
                return this.basicBlock.getFirstNode().getSourceLocation();
            } else {
                return this.function.getSourceLocation();
            }
        }

        public SourceLocation getEndSourceLocation() {
            if (this.node != null) {
                return this.node.getSourceLocation();
            } else if (this.basicBlock != null) {
                return this.basicBlock.getLastNode().getSourceLocation();
            } else {
                return this.function.getSourceLocation();
            }
        }

        @Override
        public String toString() {
            if (this.node != null) {
                return this.node.toString();
            } else if (this.basicBlock != null) {
                return this.basicBlock.toString();
            } else {
                return this.function.toString();
            }
        }

        public Class getUnderlyingClass() {
            if (this.node != null) {
                return this.node.getClass();
            } else if (this.basicBlock != null) {
                return this.basicBlock.getClass();
            } else {
                return this.function.getClass();
            }
        }
    }

    private class Tracker {
        private String description;
        private Map<URL, MessageDigest> sources;
        private Map<Integer, Integer> tajsToUnique;
        private Map<Integer, Integer> uniqueToTajs;
        private Map<Integer, Identified> debuggingElements;

        public Tracker(String description, Map<URL, MessageDigest> sources) {
            this.description = description;
            this.sources = sources;
            this.tajsToUnique = newMap();
            this.uniqueToTajs = newMap();
            this.debuggingElements = newMap();
        }

        public int getUnique(AbstractNode node) throws Exception {
            return getUniqueFromIdentified(new Identified(node));
        }

        public int getUnique(BasicBlock basicBlock) throws Exception {
            return getUniqueFromIdentified(new Identified(basicBlock));
        }

        public int getUnique(Function function) throws Exception {
            return getUniqueFromIdentified(new Identified(function));
        }

        private int getUniqueFromIdentified(Identified identified) throws Exception {
            Integer cached = tajsToUnique.get(identified.getIndex());
            if (cached != null) {
                return cached;
            }

            MessageDigest md = getMessageDigest(identified);
            int id = Arrays.hashCode(md.digest());

            Integer collission = uniqueToTajs.get(id);
            for (int i = 0; collission != null && i < 1000; i++) {
                log.warn(description + " ID collision: " + identified.getIndex() + " and " + collission + " both map to ID " + id);
                md.update(ByteBuffer.allocate(4).putInt(id).array());
                id = Arrays.hashCode(md.digest());
                collission = uniqueToTajs.get(id);
            }
            if (collission != null) {
                throw new Exception(
                    description + " ID collision: " + identified.getIndex() + " and " + collission + " both map to ID " + id + "\n" +
                    identified.toString() + "\n" +
                    debuggingElements.get(collission));
            }

            tajsToUnique.put(identified.getIndex(), id);
            uniqueToTajs.put(id, identified.getIndex());
            debuggingElements.put(identified.getIndex(), identified);

            return id;
        }

        private MessageDigest getMessageDigest(Identified identified) {
            SourceLocation startSourceLocation = identified.getStartSourceLocation();
            SourceLocation endSourceLocation = identified.getEndSourceLocation();
            URL url = startSourceLocation != null ? startSourceLocation.getLocation() : null;
            assert (startSourceLocation != null);
            assert (endSourceLocation != null);
            assert (url != null);

            MessageDigest md = sources.get(url);
            try {
                if (md == null) {
                    md = (MessageDigest)emptyMessageDigest.clone();
                    md.update(url.toString().getBytes());
                    md.update((byte)0x00);
                    try (InputStream is = url.openStream(); BufferedInputStream bis = new BufferedInputStream(is); DigestInputStream dis = new DigestInputStream(bis, md)) {
                        while (dis.read() != -1) {}
                        md = dis.getMessageDigest();
                        sources.put(url, md);
                    }
                }
                md = (MessageDigest)md.clone();
            } catch (Exception e) {
                System.err.println(e);
                e.printStackTrace(System.err);
                System.exit(1);
            }
            assert (md != null);

            StringBuilder sb = new StringBuilder();
            sb.append(":");
            sb.append(startSourceLocation.getLineNumber());
            sb.append(":");
            sb.append(startSourceLocation.getColumnNumber());
            sb.append("-");
            sb.append(endSourceLocation.getEndLineNumber());
            sb.append(":");
            sb.append(endSourceLocation.getEndColumnNumber());
            sb.append("::<");
            sb.append(identified.getUnderlyingClass().getCanonicalName());
            sb.append(">");

            if (identified.basicBlock != null) {
                appendIdentifyingString(sb, identified.basicBlock);
            } else if (identified.node != null) {
                appendIdentifyingString(sb, identified.node);
            }

            md.update(sb.toString().getBytes());
            return md;
        }

        private void appendIdentifyingString(StringBuilder sb, AbstractNode n) {
            BasicBlock bb = n.getBlock();
            Function f = bb.getFunction();
            assert (bb != null);
            assert (f != null);

            sb.append("::<basic-block-node-index>::");
            List<AbstractNode> ns = bb.getNodes();
            for (int i = 0; i < ns.size(); i++) {
                if (ns.get(i).equals(n)) {
                    sb.append("[");
                    sb.append(i);
                    sb.append("]");
                    break;
                }
            }

            appendIdentifyingString(sb, bb);
            appendIdentifyingString(sb, f);
        }

        private void appendIdentifyingString(StringBuilder sb, BasicBlock bb) {
            sb.append("::<inner-outer-basic-block-path>::");
            boolean basicBlockFound = appendBasicBlockIndexString(sb, bb, bb.getFunction().getBlocks(), newSet());
            assert (basicBlockFound);
        }

        private boolean appendBasicBlockIndexString(StringBuilder sb, BasicBlock bb, Collection<BasicBlock> bbc, Set<BasicBlock> visited) {
            if (bbc == null) {
                return false;
            }

            List<BasicBlock> sortedBlocks = newList(bbc);
            sortedBlocks.sort(Comparator.comparingInt(BasicBlock::getTopologicalOrder));

            for (int i = 0; i < sortedBlocks.size(); i++) {
                BasicBlock next = sortedBlocks.get(i);
                if (visited.contains(next)) {
                    continue;
                }
                visited.add(next);
                if (next.equals(bb) || appendBasicBlockIndexString(sb, bb, next.getSuccessors(), visited)) {
                    sb.append("{");
                    sb.append(i);
                    sb.append("}");
                    return true;
                }
            }
            BasicBlock eh = bb.getExceptionHandler();
            if (eh != null && !visited.contains(eh)) {
                visited.add(eh);
                if (eh.equals(bb) || appendBasicBlockIndexString(sb, bb, eh.getSuccessors(), visited)) {
                    sb.append("{exception-handler}");
                    return true;
                }
            }

            return false;
        }

        private void appendIdentifyingString(StringBuilder sb, Function f) {
            sb.append("::<inner-outer-function-block-path>::");
            appendFunctionIndexString(sb, f);
        }

        private void appendFunctionIndexString(StringBuilder sb, Function f) {
            if (f == null) {
                return;
            }

            SourceLocation sl = f.getSourceLocation();
            assert (sl != null);
            sb.append("(");
            sb.append(sl.getLineNumber());
            sb.append(":");
            sb.append(sl.getColumnNumber());
            sb.append("-");
            sb.append(sl.getEndLineNumber());
            sb.append(":");
            sb.append(sl.getEndColumnNumber());
            sb.append(")");

            appendFunctionIndexString(sb, f.getOuterFunction());
        }
    }
}
