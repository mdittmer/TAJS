package ca.uwaterloo.tajs.souffle;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Formatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import javax.xml.transform.Source;

import com.google.gson.Gson;

import org.apache.commons.text.StringEscapeUtils;
import org.apache.commons.text.translate.UnicodeUnescaper;
import org.apache.log4j.Logger;
import org.apache.commons.text.translate.CharSequenceTranslator;
import org.apache.commons.text.translate.AggregateTranslator;
import org.apache.commons.text.translate.LookupTranslator;
import org.apache.commons.text.translate.EntityArrays;

import dk.brics.tajs.analysis.signatures.types.Parameter;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.EventType;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.SourceLocation;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginWithNode;
import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.CatchNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareFunctionNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.DeletePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.EndForInNode;
import dk.brics.tajs.flowgraph.jsnodes.EndLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.EndWithNode;
import dk.brics.tajs.flowgraph.jsnodes.EventDispatcherNode;
import dk.brics.tajs.flowgraph.jsnodes.ExceptionalReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.HasNextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.IfNode;
import dk.brics.tajs.flowgraph.jsnodes.NewObjectNode;
import dk.brics.tajs.flowgraph.jsnodes.NextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.Node;
import dk.brics.tajs.flowgraph.jsnodes.NodeVisitor;
import dk.brics.tajs.flowgraph.jsnodes.NopNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.ThrowNode;
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.WritePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.WriteVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode.Type;
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Collectors;
import dk.brics.tajs.util.PathAndURLUtils;

import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

public class DatalogGenerator {
    private static final String[] factTypes = {
        "basicBlockFirstNode",
        "basicBlockLastNode",
        "basicBlockNode",
        "basicBlockScope",
        "beginForInNode",
        "beginLoopNode",
        "beginWithNode",
        "binaryOperatorNode",
        "callNode",
        "catchLocalVariable",
        "catchNode",
        "constantNode",
        "declareFunctionNode",
        "declareVariableNode",
        "deletePropertyNode",
        "endForInNode",
        "endLoopNode",
        "endWithNode",
        "eventDispatcherNode",
        "exceptionalReturnNode",
        "fromToNodeEdge",
        "functionBasicBlock",
        "functionEntryBasicBlock",
        "functionEstimatedSourceLocation",
        "functionExceptionalExitBasicBlock",
        "functionLocalVariable",
        "functionOrdinaryExitBasicBlock",
        "functionParameter",
        "hasNextPropertyNode",
        "ifNode",
        "mainFunction",
        "newObjectNode",
        "nextPropertyNode",
        "nodeSourceLocation",
        "nopNode",
        "packageMainSourceLocation",
        "readPropertyNode",
        "readVariableNode",
        "returnNode",
        "throwNode",
        "unaryOperatorNode",
        "writePropertyNode",
        "writeVariableNode",
    };

    private static final MessageDigest emptyMessageDigest = prepareEmptyMessageDigest();
    private static MessageDigest prepareEmptyMessageDigest() {
        MessageDigest md = null;
        try {
            md = MessageDigest.getInstance("SHA-256");
            md.clone();
            return md;
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }
        return md;
    }

    private Path outDir;
    private String mainPath;
    private Map<String, PrintWriter> factWriters;
    private IdentityTracker identityTracker;
    private Visitor visitor;

    public DatalogGenerator(Path outDir) throws IOException {
        this.outDir = outDir;
        Files.createDirectories(outDir);
        this.factWriters = newMap();
        this.identityTracker = new IdentityTracker();
        this.visitor = new Visitor(this);
        for (String factType : factTypes) {
            factWriters.put(factType, new PrintWriter(new FileWriter(outDir.resolve(factType + ".facts").toFile(), true)));
        }
    }

    private static final Logger log = Logger.getLogger(DatalogGenerator.class);

    public static final CharSequenceTranslator escapeForStringLiteral;
    static {
        final Map<CharSequence, CharSequence> escapeMap = new HashMap<>();
        escapeMap.put("\"", "\\\"");
        escapeMap.put("\\", "\\\\");
        escapeForStringLiteral = new AggregateTranslator(
            new LookupTranslator(Collections.unmodifiableMap(escapeMap)),
            new LookupTranslator(EntityArrays.JAVA_CTRL_CHARS_ESCAPE) // ,
            // Do not escape unicode: Souffle cannot handle backslash-"u"-hexdigits literals.
            // JavaUnicodeEscaper.outsideOf(32, 0x7f)
        );
    }

    private int getID(AbstractNode node) {
        try {
            return identityTracker.getID(node);
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }
        return 1;
    }

    private int getID(Function function) {
        try {
            return identityTracker.getID(function);
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }
        return 1;
    }

    private int getID(BasicBlock basicBlock) {
        try {
            return identityTracker.getID(basicBlock);
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }
        return 1;
    }

    private static String toSouffleSymbol(Object o) {
        return escapeForStringLiteral.translate(o.toString());
    }

    private static String toSouffleString(Object o) {
        return o == null ? "nil" : "[\"" + toSouffleSymbol(o) + "\"]";
    }

    private static String toSouffleBool(boolean b) {
        return b ? "1" : "0";
    }

    private static String toSouffleIntList(int[] list) {
        // Store list "inside out". This facilitates pattern matching that
        // assigns `0` to the base case of [param, nil], and increment a counter
        // that will correspond to `functionParameter` indices.
        int[] reversed = list.clone();

        StringBuilder head = new StringBuilder();
        StringBuilder tail = new StringBuilder("nil");
        for (int x : reversed) {
            head.append("[" + x + ",");
            tail.append("]");
        }
        return head.toString() + tail.toString();
    }

    private static String binaryOpToSouffleSymbolInner(BinaryOperatorNode.Op op) {
        switch (op) {
            case ADD:
                return "ADD";
            case SUB:
                return "SUB";
            case MUL:
                return "MUL";
            case DIV:
                return "DIV";
            case REM:
                return "REM";
            case AND:
                return "AND";
            case OR:
                return "OR";
            case XOR:
                return "XOR";
            case EQ:
                return "EQ";
            case NE:
                return "NE";
            case LT:
                return "LT";
            case GE:
                return "GE";
            case LE:
                return "LE";
            case GT:
                return "GT";
            case SHL:
                return "SHL";
            case SHR:
                return "SHR";
            case USHR:
                return "USHR";
            case SEQ:
                return "SEQ";
            case SNE:
                return "SNE";
            case IN:
                return "IN";
            case INSTANCEOF:
                return "INSTANCEOF";
            default:
                throw new AnalysisException("Unexpected operator");
        }
    }

    private static String literalConstructorKindToSouffleStringInner(CallNode.LiteralConstructorKinds literalConstructorKind) {
        if (literalConstructorKind == null) {
            return null;
        }
        switch (literalConstructorKind) {
            case ARRAY:
                return "ARRAY";
            case REGEXP:
                return "REGEXP";
            default:
                throw new AnalysisException("Unexpected literal constructor kind");
        }
    }

    private static String constantNodeTypeToSouffleSymbolInner(ConstantNode.Type type) {
        switch (type) {
            case NUMBER:
                return "NUMBER";
            case STRING:
                return "STRING";
            case BOOLEAN:
                return "BOOLEAN";
            case NULL:
                return "NULL";
            case UNDEFINED:
                return "UNDEFINED";
            default:
                throw new AnalysisException("Unexpected type: " + type);
        }
    }

    private static String domEventTypeToSouffleStringInner(EventType domEventType) {
        if (domEventType == null) {
            return null;
        }
        switch (domEventType) {
            case DOM_CONTENT_LOADED:
                return "DOM_CONTENT_LOADED";
            case LOAD:
                return "LOAD";
            case UNLOAD:
                return "UNLOAD";
            case KEYBOARD:
                return "KEYBOARD";
            case MOUSE:
                return "MOUSE";
            case UNKNOWN:
                return "UNKNOWN";
            case OTHER:
                return "OTHER";
            case AJAX:
                return "AJAX";
            case TIMEOUT:
                return "TIMEOUT";
            default:
                throw new AnalysisException("Unexpected DOM event type: " + domEventType);
        }
    }

    private static String eventDispatcherNodeTypeToSouffleSymbolInner(EventDispatcherNode.Type type) {
        switch (type) {
            case DOM_CONTENT_LOADED:
                return "DOM_CONTENT_LOADED";
            case DOM_LOAD:
                return "DOM_LOAD";
            case DOM_UNLOAD:
                return "DOM_UNLOAD";
            case DOM_OTHER:
                return "DOM_OTHER";
            case ASYNC:
                return "ASYNC";
            case TYPE_TESTS:
                return "TYPE_TESTS";
            default:
                throw new AnalysisException("Unexpected event dispatcher node type: " + type);
        }
    }

    private static String unaryOperatorToSouffleSymbolInner(UnaryOperatorNode.Op op) {
        switch (op) {
            case COMPLEMENT:
                return "COMPLEMENT";
            case NOT:
                return "NOT";
            case MINUS:
                return "MINUS";
            case PLUS:
                return "PLUS";
            case TYPEOF:
                return "TYPEOF";
            default:
                throw new AnalysisException("Unexpected operator: " + op);
        }
    }

    private static String writePropertyNodeKindToSouffleSymbolInner(WritePropertyNode.Kind kind) {
        switch (kind) {
            case GETTER:
                return "GETTER";
            case SETTER:
                return "SETTER";
            case ORDINARY:
                return "ORDINARY";
            default:
                throw new AnalysisException("Unexpected write property kind: " + kind);
        }
    }

    private void writeFact(String predicate, Object... values) {
        PrintWriter pw = factWriters.get(predicate);
        assert (pw !=null);
        String[] strings = new String[values.length];
        for (int i = 0; i < values.length; i++) {
            strings[i] = values[i].toString();
        }
        String line = String.join("\t", strings);
        pw.println(line);
    }

    public void gatherPackageJson(Path inDir) {
        Set<Path> packageJsons = newSet();
        try {
            packageJsons = Files.walk(inDir)
                .filter(path -> path.getFileName().toString().equals("package.json"))
                .collect(Collectors.toSet());
        } catch (IOException e) {
            log.warn("Failed to gather package.json files: " + e);
        }
        for (Path packageJson : packageJsons) {
            try {
                Path pkgPath = packageJson.getParent();
                PackageJson pkg = new Gson().fromJson(Files.newBufferedReader(packageJson), PackageJson.class);
                if (pkg.main != null) {
                    Path mainPath = pkgPath.resolve(pkg.main);
                    writeFact("packageMainSourceLocation", packageJson, toSouffleString(mainPath));
                } else {
                    writeFact("packageMainSourceLocation", packageJson, toSouffleString(null));
                }
            } catch (Exception e) {
                log.warn("Failed to parse " + packageJson + ": " + e);
            }
        }
    }

    public void visitGraph(FlowGraph g) {
        Function main = g.getMain();
        SourceLocation mainSourceLocation = main.getSourceLocation();
        URL mainURL = mainSourceLocation.getLocation();

        mainPath = mainURL != null && mainURL.getProtocol().equals("file") ? mainURL.getPath() : null;

        try {
            if (mainURL == null) {
                log.warn("Main function with no source location: <Function " + getID(main) + ">");
            } else if (mainPath == null) {
                log.warn("Main function with non-file source location: " + mainURL);
            } else {
                log.info("Visiting graph with main function at " + mainURL);
            }

            writeFact("mainFunction",
                getID(main));
            for (Function f : g.getFunctions()) {
                log.info("DatalogGenerator visiting function  " + f.getSourceLocation().getLocation() + ":" + f.getSourceLocation().getLineNumber() + ":" + f.getSourceLocation().getColumnNumber());
                if (f.hasOuterFunction()) {
                    Function o = f.getOuterFunction();
                    log.info("DatalogGenerator outer function  " + o.getSourceLocation().getLocation() + ":" + o.getSourceLocation().getLineNumber() + ":" + o.getSourceLocation().getColumnNumber());
                } else {
                    log.info("DatalogGenerator NO outer function");
                }
                visitFunction(mainPath, f);
            }
            for (PrintWriter pw : factWriters.values()) {
                pw.flush();
            }
        } finally {
            mainPath = null;
        }
    }

    private void visitFunction(String mainPath, Function f) {
        // Define basic function information.
        SourceLocation sl = f.getSourceLocation();
        URL location = sl.getLocation();
        if (location == null) {
            log.warn("Function with no source location: <Function " + getID(f) + ">");
        } else if (!location.getProtocol().equals("file")) {
            log.warn("Function with non-file source location: " + location);
        }
        writeFact("functionEstimatedSourceLocation",
            getID(f),
            toSouffleString(location == null ? null : location.getPath()),
            sl.getLineNumber(),
            sl.getColumnNumber(),
            sl.getEndLineNumber(),
            sl.getEndColumnNumber());

        List<String> parameterNames = f.getParameterNames();
        for (int i = 0; i < parameterNames.size(); i++) {
            writeFact("functionParameter",
                getID(f),
                i,
                toSouffleSymbol(parameterNames.get(i)));
        }
        BasicBlock e = f.getEntry();
        if (e != null) {
            writeFact("functionEntryBasicBlock",
                getID(f),
                getID(e));
        }
        BasicBlock oe = f.getOrdinaryExit();
        if (oe != null) {
            writeFact("functionOrdinaryExitBasicBlock",
                getID(f),
                getID(oe));
        }
        BasicBlock ee = f.getExceptionalExit();
        if (ee != null) {
            writeFact("functionExceptionalExitBasicBlock",
                getID(f),
                getID(ee));
        }

        // Trace visited blocks.
        Set<BasicBlock> visited = newSet();
        // Keep a stack for nesting of `with (...) { ... }` blocks for denoting
        // scope.
        Stack<WithFrontier> withStack = new Stack<WithFrontier>();
        // Start with a frontier that defines no with-scoping-object.
        withStack.push(new WithFrontier(null));
        withStack.peek().enqueue(e);

        // Process with-stack until empty.
        while (!withStack.isEmpty()) {
            // Process top of with-stack's queue of basic blocks until empty.
            while (!withStack.peek().isEmpty()) {
                // Define simple basic block data.
                WithFrontier wf = withStack.peek();
                FrontierBasicBlock fbb = wf.dequeue();
                BasicBlock b = fbb.getBasicBlock();

                // Skip completely visited basic blocks.
                if (visited.contains(b)) {
                    continue;
                }

                int bsi = fbb.getStartIndex();
                writeFact("functionBasicBlock",
                    getID(f),
                    getID(b));

                // Before processing nodes, associate basic block with current
                // with-scoping-object and catch-scope-variable (if any).
                BeginWithNode fbwn = wf.getBeginWithNode();
                String fs = fbwn != null ?
                    "$WithScope(" + getID(fbwn) + ")" :
                    "$FunctionScope(" + getID(f) + ")";
                writeFact("basicBlockScope",
                    getID(b),
                    fs);

                AbstractNode fn = b.getFirstNode();
                writeFact("basicBlockFirstNode",
                    getID(b),
                    getID(fn));
                AbstractNode ln = b.getLastNode();
                writeFact("basicBlockLastNode",
                    getID(b),
                    getID(ln));

                // Process basic block's nodes in order.
                List<AbstractNode> ns = b.getNodes();
                AbstractNode p = null;
                int i;
                for (i = bsi; i < ns.size(); i++) {
                    AbstractNode n = ns.get(i);

                    // logState("BEGIN  " + getID(n) + "  " + n, withStack, visited);

                    // Associate adjacent nodes (control flow).
                    if (p != null) {
                        writeFact("fromToNodeEdge",
                            getID(p),
                            getID(n));
                    }
                    if (n.canThrowExceptions()) {
                        BasicBlock eh = b.getExceptionHandler();
                        writeFact("fromToNodeEdge",
                            getID(n),
                            getID(eh.getFirstNode()));
                        wf.enqueue(eh);
                    }

                    // Document all local-to-node facts.
                    n.visitBy((node) -> {
                        log.info("    VISIT    " + getID(node) + "  " + node);
                        visitNode(node);
                        node.visitBy(visitor);
                    });

                    // Push when (possibly catch-followed-by) begin-with.
                    if (n instanceof BeginWithNode) {
                        if (b.getLastNode() != n) {
                            throw new AnalysisException("Expected BeginWithNode to be last node in its basic block");
                        }
                        withStack.push(new WithFrontier((BeginWithNode)n));
                    }

                    // If leaving a `with {}` scope, successor control flows
                    // actually belong to second-from-top-of-stack. Pop before
                    // updating `wf` below, and push back after successor
                    // control flow updates.
                    WithFrontier fwf = withStack.peek();
                    if (n instanceof EndWithNode) {
                        withStack.pop();

                        // If end-with is *not* at the end of its basic block,
                        // enqueue partial-basic-block to
                        // second-from-top-of-stack. Processing of this basic
                        // block will be finished later, so `break` before
                        // reaching end of node list.
                        if (b.getLastNode() != n) {
                            withStack.peek().enqueue(b, i + 1);
                            writeFact("fromToNodeEdge",
                                getID(n),
                                getID(ns.get(i + 1)));
                            withStack.push(fwf);
                            // logState("EARLY END  " + getID(n) + "  " + n, withStack, visited);
                            break;
                        }
                    }

                    // Reset frontier to possibly-updated-above frontier. I.e.,
                    // if we just entered a with-block, then processing
                    // below should operate on newly pushed top-of-stack; if we
                    // just exited a with-block, then processing below should
                    // operate on just-below-top-of-stack (due to `pop()`
                    // above).
                    wf = withStack.peek();

                    // Based on new frontier, capture control flow between
                    // basic blocks, and enqueue not-yet-visited basic blocks
                    // for processing as part of current with-block.
                    if (b.getLastNode() == n) {
                        for (BasicBlock s : b.getSuccessors()) {
                            writeFact("fromToNodeEdge",
                                getID(n),
                                getID(s.getFirstNode()));

                            wf.enqueue(s);
                        }
                    }

                    // If leaving a `with {}` scope, successor control flows
                    // were actually added to second-from-top-of-stack. Push
                    // `fwf` back onto stack in case it still has basic blocks
                    // to process.
                    if (n instanceof EndWithNode) {
                        withStack.push(fwf);
                    }

                    p = n;

                    // logState("END  " + getID(n) + "  " + n, withStack, visited);
                }

                // Mark basic block as visited if and only if all nodes were
                // processed. Any special cases where not all nodes were
                // processed must (re-)enqueue a (partial) basic block to be
                // completed later.
                if (i == ns.size()) {
                    visited.add(b);
                }
            }

            withStack.pop();
        }
    }

    private void visitNode(Node n) {
        SourceLocation sl = n.getSourceLocation();
        URL location = sl.getLocation();
        if (location == null) {
            log.warn("Node with no source location: <Node " + getID(n) + ">");
        } else if (!location.getProtocol().equals("file")) {
            log.warn("Node with non-file source location: " + location);
        }
        BasicBlock b = n.getBlock();

        writeFact("nodeSourceLocation",
            getID(n),
            toSouffleString(location == null ? null : location.getPath()),
            sl.getLineNumber(),
            sl.getColumnNumber(),
            sl.getEndLineNumber(),
            sl.getEndColumnNumber());
        writeFact("basicBlockNode",
            getID(b),
            getID(n));
    }

    // private void logState(String label, Stack<WithFrontier> withStack, Set<BasicBlock> visited) {
    //     log.info(" :::: " + label);
    //     Stack<WithFrontier> stack = (Stack<WithFrontier>)withStack.clone();
    //     while (!stack.empty()) {
    //         WithFrontier f = stack.pop();
    //         BeginWithNode bwn = f.getBeginWithNode();
    //         log.info("  " + (bwn == null ? "<null>" : getID(bwn) + "  " + bwn));
    //         for (FrontierBasicBlock fbb : f.frontier) {
    //             BasicBlock b = fbb.getBasicBlock();
    //             int s = fbb.getStartIndex();
    //             log.info("    BB" + getID(b) + " @ " + s + (visited.contains(b) ? "  <VISITED>" : ""));
    //             List<AbstractNode> ns = b.getNodes();
    //             for (int i = s; i < ns.size(); i++) {
    //                 AbstractNode n = ns.get(i);
    //                 log.info("      N" + getID(n) + "  " + n);
    //             }
    //         }
    //     }
    // }

    public class PackageJson {
        public String main;
    }

    private class FrontierBasicBlock {
        private BasicBlock basicBlock;
        private int startIndex;

        public FrontierBasicBlock(BasicBlock basicBlock) {
            this.basicBlock = basicBlock;
            this.startIndex = 0;
        }

        public FrontierBasicBlock(BasicBlock basicBlock, int startIndex) {
            this.basicBlock = basicBlock;
            this.startIndex = startIndex;
        }

        public BasicBlock getBasicBlock() {
            return basicBlock;
        }

        public int getStartIndex() {
            return startIndex;
        }
    }

    private class WithFrontier {
        private BeginWithNode beginWithNode; // null => function (non-`with`) scope.
        private Queue<FrontierBasicBlock> frontier;

        public WithFrontier(BeginWithNode beginWithNode) {
            this.beginWithNode = beginWithNode;
            frontier = new ArrayDeque<FrontierBasicBlock>();
        }

        public boolean isEmpty() {
            return frontier.isEmpty();
        }

        public FrontierBasicBlock dequeue() {
            return frontier.isEmpty() ? null : frontier.remove();
        }

        public void enqueue(BasicBlock b) {
            frontier.add(new FrontierBasicBlock(b));
        }

        public void enqueue(BasicBlock b, int i) {
            frontier.add(new FrontierBasicBlock(b, i));
        }

        public BeginWithNode getBeginWithNode() {
            return beginWithNode;
        }
    }

    private class Visitor implements NodeVisitor {
        private DatalogGenerator dg;

        public Visitor(DatalogGenerator dg) {
            this.dg = dg;
        }

        @Override
        public void visit(BinaryOperatorNode n) {
            dg.writeFact("binaryOperatorNode",
                getID(n),
                n.getResultRegister(),
                n.getArg1Register(),
                n.getArg2Register(),
                toSouffleSymbol(binaryOpToSouffleSymbolInner(n.getOperator())));
        }

        @Override
        public void visit(CallNode n) {
            int[] argumentRegisters = new int[n.getNumberOfArgs()];
            for (int i = 0; i < n.getNumberOfArgs(); i++) {
                argumentRegisters[i] = n.getArgRegister(i);
            }
            dg.writeFact("callNode",
                getID(n),
                n.getResultRegister(),
                toSouffleString(literalConstructorKindToSouffleStringInner(n.getLiteralConstructorKind())),
                toSouffleBool(n.isConstructorCall()),
                n.getBaseRegister(),
                n.getFunctionRegister(),
                n.getPropertyRegister(),
                toSouffleString(n.getPropertyString()),
                toSouffleIntList(argumentRegisters));
        }

        @Override
        public void visit(CatchNode n) {
            String catchVariableName = n.getVariableName();
            if (catchVariableName != null) {
                dg.writeFact("catchLocalVariable",
                    getID(n),
                    toSouffleSymbol(n.getVariableName()));
            }
            dg.writeFact("catchNode",
                getID(n),
                toSouffleString(n.getVariableName()),
                n.getValueRegister(),
                n.getScopeObjRegister());
        }

        @Override
        public void visit(ConstantNode n) {
            // TODO: Souffle does not support double-precision floating-point values.
            double number = n.getNumber();
            if (n.getType() == Type.NUMBER) {
                if (number > Float.MAX_VALUE) {
                    log.warn("Rounding double-precision floating-point constant down from " + number + " to single-precision value " + Float.MAX_VALUE);
                    number = Float.MAX_VALUE;
                } else if (number < -Float.MAX_VALUE) {
                    log.warn("Rounding double-precision floating-point constant up from " + number + " to single-precision value " + -Float.MAX_VALUE);
                    number = -Float.MAX_VALUE;
                }
            }
            dg.writeFact("constantNode",
                getID(n),
                n.getResultRegister(),
                toSouffleSymbol(constantNodeTypeToSouffleSymbolInner(n.getType())),
                number,
                toSouffleString(n.getString()),
                toSouffleBool(n.getBoolean()));
        }

        @Override
        public void visit(DeletePropertyNode n) {
            dg.writeFact("deletePropertyNode",
                getID(n),
                n.getResultRegister(),
                n.getBaseRegister(),
                n.getPropertyRegister(),
                toSouffleString(n.getPropertyString()),
                toSouffleString(n.getVariableName()));
        }

        @Override
        public void visit(BeginWithNode n) {
            dg.writeFact("beginWithNode",
                getID(n),
                n.getObjectRegister());
        }

        @Override
        public void visit(ExceptionalReturnNode n) {
            dg.writeFact("exceptionalReturnNode",
                getID(n));
        }

        @Override
        public void visit(DeclareFunctionNode n) {
            dg.writeFact("declareFunctionNode",
                getID(n),
                n.getResultRegister(),
                getID(n.getFunction()),
                toSouffleBool(n.isExpression()),
                toSouffleString(domEventTypeToSouffleStringInner(n.getDomEventType())));
        }

        @Override
        public void visit(BeginForInNode n) {
            dg.writeFact("beginForInNode",
                getID(n),
                n.getObjectRegister(),
                n.getPropertyListRegister());
        }

        @Override
        public void visit(IfNode n) {
            dg.writeFact("ifNode",
                getID(n),
                n.getConditionRegister());
        }

        @Override
        public void visit(EndWithNode n) {
            dg.writeFact("endWithNode",
                getID(n));
        }

        @Override
        public void visit(NewObjectNode n) {
            dg.writeFact("newObjectNode",
                getID(n),
                n.getResultRegister());
        }

        @Override
        public void visit(NextPropertyNode n) {
            dg.writeFact("nextPropertyNode",
                getID(n),
                n.getPropertyListRegister(),
                n.getPropertyRegister());
        }

        @Override
        public void visit(HasNextPropertyNode n) {
            dg.writeFact("hasNextPropertyNode",
                getID(n),
                n.getResultRegister(),
                n.getPropertyListRegister());
        }

        @Override
        public void visit(NopNode n) {
            dg.writeFact("nopNode",
                getID(n),
                toSouffleString(n.getText()));
        }

        @Override
        public void visit(ReadPropertyNode n) {
            dg.writeFact("readPropertyNode",
                getID(n),
                n.getResultRegister(),
                n.getBaseRegister(),
                n.getPropertyRegister(),
                toSouffleString(n.getPropertyString()));
        }

        @Override
        public void visit(ReadVariableNode n) {
            dg.writeFact("readVariableNode",
                getID(n),
                n.getResultRegister(),
                toSouffleSymbol(n.getVariableName()),
                n.getResultBaseRegister(),
                toSouffleBool(n.isKeepAbsent()));
        }

        @Override
        public void visit(ReturnNode n) {
            dg.writeFact("returnNode",
                getID(n),
                n.getReturnValueRegister());
        }

        @Override
        public void visit(ThrowNode n) {
            dg.writeFact("throwNode",
                getID(n),
                n.getValueRegister());
        }

        @Override
        public void visit(UnaryOperatorNode n) {
            dg.writeFact("unaryOperatorNode",
                getID(n),
                n.getResultRegister(),
                n.getArgRegister(),
                toSouffleSymbol(unaryOperatorToSouffleSymbolInner(n.getOperator())));
        }

        @Override
        public void visit(DeclareVariableNode n) {
            dg.writeFact("functionLocalVariable",
                getID(n.getBlock().getFunction()),
                toSouffleSymbol(n.getVariableName()));
            dg.writeFact("declareVariableNode",
                getID(n),
                toSouffleSymbol(n.getVariableName()));
        }

        @Override
        public void visit(WritePropertyNode n) {
            dg.writeFact("writePropertyNode",
                getID(n),
                n.getBaseRegister(),
                n.getPropertyRegister(),
                toSouffleString(n.getPropertyString()),
                n.getValueRegister(),
                toSouffleSymbol(writePropertyNodeKindToSouffleSymbolInner(n.getKind())),
                toSouffleBool(n.isDecl()));
        }

        @Override
        public void visit(WriteVariableNode n) {
            dg.writeFact("writeVariableNode",
                getID(n),
                toSouffleSymbol(n.getVariableName()),
                n.getValueRegister());
        }

        @Override
        public void visit(EventDispatcherNode n) {
            dg.writeFact("eventDispatcherNode",
                getID(n),
                toSouffleSymbol(eventDispatcherNodeTypeToSouffleSymbolInner(n.getType())));
        }

        @Override
        public void visit(EndForInNode n) {
            dg.writeFact("endForInNode",
                getID(n));
        }

        @Override
        public void visit(BeginLoopNode n) {
            dg.writeFact("beginLoopNode",
                getID(n),
                toSouffleBool(n.isNested()));
        }

        @Override
        public void visit(EndLoopNode n) {
            dg.writeFact("endLoopNode",
                getID(n));
        }
    }
}
