/*
 * Copyright 2009-2020 Aarhus University
 * Copyright 2022 University of Waterloo
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package dk.brics.tajs;

import dk.brics.tajs.analysis.Analysis;
import dk.brics.tajs.analysis.InitialStateBuilder;
import dk.brics.tajs.analysis.Transfer;
import dk.brics.tajs.analysis.nativeobjects.NodeJSRequire;
import dk.brics.tajs.blendedanalysis.BlendedAnalysisOptions;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.HostEnvSources;
import dk.brics.tajs.flowgraph.JavaScriptSource;
import dk.brics.tajs.flowgraph.JavaScriptSource.Kind;
import dk.brics.tajs.flowgraph.SourceLocation;
import dk.brics.tajs.js2flowgraph.FlowGraphBuilder;
import dk.brics.tajs.js2flowgraph.HTMLParser;
import dk.brics.tajs.lattice.Context;
import dk.brics.tajs.lattice.Obj;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.PKey;
import dk.brics.tajs.lattice.ScopeChain;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.monitoring.AnalysisMonitor;
import dk.brics.tajs.monitoring.AnalysisPhase;
import dk.brics.tajs.monitoring.AnalysisTimeLimiter;
import dk.brics.tajs.monitoring.CompositeMonitor;
import dk.brics.tajs.monitoring.IAnalysisMonitoring;
import dk.brics.tajs.monitoring.MaxMemoryUsageMonitor;
import dk.brics.tajs.monitoring.MemoryUsageDiagnosisMonitor;
import dk.brics.tajs.monitoring.ProgramExitReachabilityChecker;
import dk.brics.tajs.monitoring.ProgressMonitor;
import dk.brics.tajs.monitoring.TAJSAssertionReachabilityCheckerMonitor;
import dk.brics.tajs.monitoring.inspector.datacollection.InspectorFactory;
import dk.brics.tajs.monitoring.soundness.SoundnessTesterMonitor;
import dk.brics.tajs.options.ExperimentalOptions;
import dk.brics.tajs.options.OptionValues;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.options.TAJSEnvironmentConfig;
import dk.brics.tajs.preprocessing.Babel;
import dk.brics.tajs.preprocessing.BabelDir;
import dk.brics.tajs.preprocessing.SrcDir;
import dk.brics.tajs.solver.SolverSynchronizer;
import dk.brics.tajs.typetesting.ITypeTester;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Canonicalizer;
import dk.brics.tajs.util.Collectors;
import dk.brics.tajs.util.Lists;
import dk.brics.tajs.util.Loader;
import dk.brics.tajs.util.Pair;
import dk.brics.tajs.util.PathAndURLUtils;
import dk.brics.tajs.util.Strings;
import net.htmlparser.jericho.Source;
import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.apache.log4j.Level;
import org.kohsuke.args4j.CmdLineException;

import ca.uwaterloo.tajs.souffle.DatalogGenerator;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.Properties;
import java.util.Set;

import static dk.brics.tajs.util.Collections.newList;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Main class for the TAJS flowgraph output only.
 */
public class FlowGraphOnlyMain {

    private static Logger log = Logger.getLogger(FlowGraphOnlyMain.class);

    // TODO: Determine how files are (re)named by babel when they have
    // ECMAScript > 3 -implying extensions and make sure not source files get
    // skipped.
    private static final Set<String> jsFileExensions = newSet(Arrays.asList(".js"));

    private FlowGraphOnlyMain() {
    }

    /**
     * Runs the analysis on the given source files.
     * Run without arguments to see the usage.
     * Terminates with System.exit.
     */
    public static void main(String[] args) {
        try {
            initLogging();
            InitResult initResult = init(args);
            if (initResult.getFlowGraphs() == null)
                System.exit(-1);
            run(initResult);
            System.exit(0);
        } catch (AnalysisException e) {
            if (Options.get().isDebugOrTestEnabled()) {
                throw e;
            }
            log.error("Error: " + e.getMessage());
            //e.printStackTrace();
            System.exit(-2);
        }
    }

    /**
     * Resets all internal counters, caches, and canonicalized static fields.
     */
    public static void reset() {
        Canonicalizer.reset();
        ExperimentalOptions.ExperimentalOptionsManager.reset();
        Options.reset();
        State.reset();
        Value.reset();
        Obj.reset();
        Strings.reset();
        ScopeChain.reset();
        NodeJSRequire.reset();
        PathAndURLUtils.reset();
        PKey.StringPKey.reset();
        ObjectLabel.reset();
        InitialStateBuilder.reset();
        BlendedAnalysisOptions.reset();
    }

    /**
     * Reads the input and prepares an analysis object, using the default monitoring.
     */
    public static InitResult init(String[] args) throws AnalysisException {
        try {
            OptionValues options = new OptionValues();
            options.parse(args);

            options.enableFlowgraph();
            if (options.getOutDir() == null) {
                options.setOutDir("out");
            }

            options.checkConsistency();

            // Special case: interpret `-babel` option as "babel dir mode" where
            // one argument is expected: a directory that babel will use to
            // determine source files.
            if (options.isBabelEnabled() && options.getArguments().size() != 1) {
                throw new CmdLineException(null, "In flowgraph-only mode the -babel option changes how arguments are interpreted.\nSpecifying -babel implies exactly two", null);
            }
            Options.set(options);

        } catch (CmdLineException e) {
            showHeader();
            log.info(e.getMessage() + "\n");
            log.info("Usage: CLASSPATH=...  java dk.brics.tajs.FlowGraphOnlyMain [OPTION]... [FILE]...\n");
            Options.showUsage();
            return null;
        }

        try {
            Files.walk(Paths.get(Options.get().getOutDir()))
                .sorted(Comparator.reverseOrder())
                .map(Path::toFile)
                .forEach(File::delete);
        } catch (IOException e) {
            log.warn("Error deleting out directory: " + e);
        }

        TAJSEnvironmentConfig.init();

        showHeader();

        Path inDir = null;
        if (Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomatically()
                || Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomaticallyForHTMLFiles()
                || Options.get().isBabelEnabled() || Options.get().getSrcDir() != null) {
            inDir = preprocess();
        } else {
            inDir = PathAndURLUtils.getCommonAncestorDirectory(getRelevantFiles());
        }

        enterPhase(AnalysisPhase.INITIALIZATION);
        List<FlowGraph> flowGraphs = newList();
        try {
            // split into JS files and HTML files
            URL htmlFile = null;
            List<URL> jsFiles = newList();
            List<URL> resolvedFiles = resolveInputs(Options.get().getArguments());
            for (URL fn : resolvedFiles) {
                if (isHTMLFileName(fn.toString())) {
                    if (htmlFile != null)
                        throw new AnalysisException("Only one HTML file can be analyzed at a time");
                    htmlFile = fn;
                } else if (jsFileExensions.contains(PathAndURLUtils.getFileExtension(Path.of(fn.getPath())))) {
                    jsFiles.add(fn);
                }
            }

            if (Options.get().isNodeJS()) {
                NodeJSRequire.init();
                if (resolvedFiles.size() != 1 || htmlFile != null) {
                    throw new AnalysisException("A single JavaScript file is expected for NodeJS analysis");
                }
                // noop, the bootstrapping has been done by addLoadersForHostFunctionSources above
            } else if (!jsFiles.isEmpty()) {
                if (htmlFile != null)
                    throw new AnalysisException("Cannot analyze an HTML file and JavaScript files at the same time");
                // build flowgraphs for JS files
                for (URL jsFile : jsFiles) {
                    if (!Options.get().isQuietEnabled())
                        log.info("Loading " + jsFile);
                    FlowGraphBuilder builder = getNextFlowGraphBuilder(jsFile, flowGraphs);
                    builder.transformStandAloneCode(Loader.getString(jsFile, Charset.forName("UTF-8")), new SourceLocation.StaticLocationMaker(jsFile));
                    flowGraphs.add(builder.close());
                }
            } else {
                // build flowgraph for JavaScript code in or referenced from HTML file
                FlowGraphBuilder builder = getNextFlowGraphBuilder(Lists.getLast(resolvedFiles), null);
                Options.get().enableIncludeDom(); // always enable DOM if any HTML files are involved
                if (!Options.get().isQuietEnabled())
                    log.info("Loading " + htmlFile);
                HTMLParser p = new HTMLParser(htmlFile);
                for (Pair<URL, JavaScriptSource> js : p.getJavaScript()) {
                    if (!Options.get().isQuietEnabled() && js.getSecond().getKind() == Kind.FILE)
                        log.info("Loading " + PathAndURLUtils.getRelativeToWorkingDirectory(PathAndURLUtils.toPath(js.getFirst(), false)));
                    builder.transformWebAppCode(js.getSecond(), new SourceLocation.StaticLocationMaker(js.getFirst()));
                }
                flowGraphs.add(builder.close());
            }

        } catch (IOException e) {
            log.error("Error: Unable to load and parse " + e.getMessage());
            return null;
        }

        leavePhase(AnalysisPhase.INITIALIZATION);

        return new InitResult(inDir, flowGraphs);
    }

    private static FlowGraphBuilder getNextFlowGraphBuilder(URL url, List<FlowGraph> flowGraphs) {
        int nextFunctionId = 0;
        int nextBlockId = 0;
        int nextNodeId = 0;
        for (FlowGraph flowGraph : flowGraphs) {
            flowGraph.getNumberOfFunctions();
            nextFunctionId += flowGraph.getNumberOfFunctions();
            nextBlockId += flowGraph.getNumberOfBlocks();
            nextNodeId += flowGraph.getNumberOfNodes();
        }
        FlowGraphBuilder builder = FlowGraphBuilder.makeForMainWithFirstFunctionId(new SourceLocation.StaticLocationMaker(url), nextFunctionId, nextBlockId, nextNodeId);
        builder.addLoadersForHostFunctionSources(HostEnvSources.getAccordingToOptions());
        return builder;
    }

    /**
     * TODO: implement checkValidOptions() for flowgraph-only mode.
     */

    /**
     * If the main file is a .html file, then set onlyInclude for instrumentation to
     * be the main file as well as all script files used by the main file.
     * Also performs Babel preprocessing.
     */
    private static Path preprocess() throws AnalysisException {
        Set<Path> relevantFiles = getRelevantFiles();
        Path testFile = Lists.getLast(Options.get().getArguments());
        Path commonAncestor = PathAndURLUtils.getCommonAncestorDirectory(relevantFiles);
        Path rootDirFromMainDirectory = PathAndURLUtils.toRealPath(testFile).getParent().relativize(commonAncestor);
        if (Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomatically()
            || Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomaticallyForHTMLFiles()) {
            Options.get().getSoundnessTesterOptions().setOnlyIncludesForInstrumentation(Optional.of(relevantFiles));
            Options.get().getSoundnessTesterOptions().setRootDirFromMainDirectory(rootDirFromMainDirectory);
        }

        String srcDir = Options.get().getSrcDir();
        Path inDir = srcDir != null ? Paths.get(srcDir) : commonAncestor;
        boolean isBabelEnabled = Options.get().isBabelEnabled();
        if (isBabelEnabled || srcDir != null) {
            enterPhase(AnalysisPhase.PREPROCESSING);
            if (isBabelEnabled) {
                if (srcDir != null) {
                    inDir = BabelDir.translate(inDir);
                } else {
                    inDir = Babel.translate(inDir, relevantFiles);
                }
            } else {
                try {
                    inDir = SrcDir.translate(inDir);
                } catch (IOException e) {
                    throw new AnalysisException("Failed to translate source: " + e);
                }
            }
            leavePhase(AnalysisPhase.PREPROCESSING);
        }
        return inDir;
    }

    private static Set<Path> getRelevantFiles() {
        Set<Path> relevantFiles = newSet();
        Path testFile = Lists.getLast(Options.get().getArguments());
        if (Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomaticallyForHTMLFiles() && (testFile.toString().endsWith(".html") || testFile.toString().endsWith(".htm"))) {
            relevantFiles.add(testFile);
            relevantFiles.addAll(HTMLParser.getScriptsInHTMLFile(PathAndURLUtils.toRealPath(testFile)));
        } else {
            for (Path file : Options.get().getArguments()) {
                relevantFiles.add(file);
            }
        }
        return relevantFiles.stream().map(PathAndURLUtils::toRealPath).collect(Collectors.toSet());
    }

    private static List<URL> resolveInputs(List<Path> files) {
        return files.stream().map(f -> PathAndURLUtils.normalizeFileURL(PathAndURLUtils.toURL(f))).collect(Collectors.toList());
    }

    private static boolean isHTMLFileName(String fileName) {
        String f = fileName.toLowerCase();
        return f.endsWith(".html") || f.endsWith(".xhtml") || f.endsWith(".htm");
    }

    /**
     * Configures log4j.
     */
    public static void initLogging() {
        Properties prop = new Properties();
        prop.put("log4j.rootLogger", "INFO, tajs"); // DEBUG / INFO / WARN / ERROR
        prop.put("log4j.appender.tajs", "org.apache.log4j.ConsoleAppender");
        prop.put("log4j.appender.tajs.layout", "org.apache.log4j.PatternLayout");
        prop.put("log4j.appender.tajs.layout.ConversionPattern", "%m%n");
        PropertyConfigurator.configure(prop);

        // Manually set log level for less verbose output.
        log.setLevel(Level.WARN);
        Logger dgLogger = Logger.getLogger(DatalogGenerator.class);
        dgLogger.setLevel(Level.WARN);
    }

    /**
     * Runs the analysis.
     *
     * @throws AnalysisException if internal error
     */
    public static void run(InitResult initResult) throws AnalysisException {
        Path outDir = Paths.get(Options.get().getOutDir());
        Path flowGraphsDir = outDir.resolve("flowgraphs");
        Path factsDir = flowGraphsDir.resolve("facts");

        try {
            Files.createDirectories(outDir);
            Files.createDirectories(flowGraphsDir);
            Files.createDirectories(factsDir);
            DatalogGenerator dg = new DatalogGenerator(factsDir);
            dg.gatherPackageJson(initResult.getInDir());
            for (FlowGraph flowGraph : initResult.getFlowGraphs()) {
                dumpFlowGraph(flowGraph, flowGraphsDir);
                dg.visitGraph(flowGraph);
            }
        } catch (IOException e) {
            throw new AnalysisException(e);
        }
    }

    /**
     * Outputs the flowgraph (in graphviz dot file).
     */
    private static void dumpFlowGraph(FlowGraph g, Path flowGraphsDir) {
        // dump the flowgraph to file
        Path sourcePath = Paths.get(g.getMain().getSourceLocation().getLocation().getPath());
        Optional<Path> relativeToTAJS = PathAndURLUtils.getRelativeToTAJS(sourcePath);

        // prefer TAJS-dir-relative name
        String canonicalSourcePath;
        if (relativeToTAJS.isPresent()) {
            canonicalSourcePath = relativeToTAJS.get().toString();
        } else {
            log.warn("Using absolute path for source that could not be made relative to TAJS dir");
            canonicalSourcePath = sourcePath.toString();
        }

        String baseName = canonicalSourcePath.replace("/", "_");
        String fileName = baseName + ".dot";
        try (PrintWriter pw = new PrintWriter(new FileWriter(flowGraphsDir.resolve(fileName).toFile()))) {
            g.toDot(pw);
        } catch (IOException e) {
            throw new AnalysisException(e);
        }
        log.info(g.toString());
    }

    private static void enterPhase(AnalysisPhase phase) {
        String phaseName = prettyPhaseName(phase);
        showPhaseStart(phaseName);
    }

    private static void showHeader() {
        if (!Options.get().isQuietEnabled()) {
            log.info("TAJS - Type Analyzer for JavaScript\n" +
                "Copyright 2009-2020 Aarhus University\n");
        }
    }

    private static void showPhaseStart(String phaseName) {
        if (!Options.get().isQuietEnabled()) {
            log.info("===========  " + phaseName + " ===========");
        }
    }

    private static void leavePhase(AnalysisPhase phase) {
    }

    private static String prettyPhaseName(AnalysisPhase phase) {
        switch (phase) {
            case PREPROCESSING:
                return "Preprocessing";
            case INITIALIZATION:
                return "Loading files";
            default:
                throw new RuntimeException("Unhandled phase enum: " + phase);
        }
    }
}
