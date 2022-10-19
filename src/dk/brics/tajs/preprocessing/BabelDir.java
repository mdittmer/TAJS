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


package dk.brics.tajs.preprocessing;

import dk.brics.tajs.analysis.Analysis;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.options.TAJSEnvironmentConfig;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Collectors;
import dk.brics.tajs.util.Lists;
import dk.brics.tajs.util.PathAndURLUtils;
import org.apache.log4j.Logger;
import org.kohsuke.args4j.CmdLineException;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static dk.brics.tajs.util.Collections.newSet;

public class BabelDir {

    private static final Logger log = Logger.getLogger(BabelDir.class);

    private static final String babelPlugins = Stream.of(
        "@babel/plugin-proposal-class-properties",
        "@babel/plugin-proposal-object-rest-spread",
        "@babel/plugin-proposal-private-methods",
        "@babel/plugin-transform-arrow-functions",
        "@babel/plugin-transform-async-to-generator",
        "@babel/plugin-transform-block-scoping",
        "@babel/plugin-transform-classes",
        "@babel/plugin-transform-computed-properties",
        "@babel/plugin-transform-destructuring",
        "@babel/plugin-transform-for-of",
        "@babel/plugin-transform-modules-commonjs",
        "@babel/plugin-transform-parameters",
        "@babel/plugin-transform-regenerator",
        "@babel/plugin-transform-shorthand-properties",
        "@babel/plugin-transform-spread",
        "@babel/plugin-transform-template-literals"
    ).collect(java.util.stream.Collectors.joining(","));

    private static final Pattern successPattern = Pattern.compile("Successfully compiled (\\d+) files? with Babel\\.");

    private static final Set<String> supportedFileExtensions = newSet(Arrays.asList(".es6", ".js", ".es", ".jsx", ".mjs"));

    /**
     * TODO: Document this.
     *
     * @param dir TODO: Document this.
     */
    public static Path translate(Path dir) {
        log.info("BABEL DIR TRANSLATE");
        List<Path> args = Options.get().getArguments();
        Path realCommonAncestor = PathAndURLUtils.toRealPath(dir);
        Path babelRoot = Paths.get(Options.get().getOutDir()).resolve("babel");
        Path babelPath = TAJSEnvironmentConfig.get().getBabel();

        try {
            Files.walk(babelRoot)
                .sorted(Comparator.reverseOrder())
                .map(Path::toFile)
                .forEach(File::delete);
        } catch (IOException e) {
            log.warn("Error deleting babel output directory: " + e);
        }

        /* If we run babel with the project root as input directory, it will copy all files in it! */
        if (PathAndURLUtils.getWorkingDirectory().startsWith(realCommonAncestor)) {
            throw new IllegalArgumentException(
                    "Babel: The current working directory is in the subtree of the common ancestor of the analysed files!" +
                            "\nWorking directory: " + PathAndURLUtils.getWorkingDirectory() +
                            "\nCommon ancestor (derived from babel dir): " + realCommonAncestor
            );
        }

        List<String> cmd = Arrays.asList(
                babelPath.toString(),
                "--root-mode", "upward",            // Find the nearest babel.config.js in the file-system
                "--extensions", String.join(",", supportedFileExtensions),
                "--keep-file-extension",
                "--verbose",
                "--plugins", babelPlugins,          // Plugins used for transformations
                "--out-dir", babelRoot.toString(),  // Output directory
                realCommonAncestor.toString()
        );

        try {
            // Run the babel command
            log.info("(cd " + babelPath.getParent().toFile() + "; " + String.join(" ", cmd) + ")");
            Process process = new ProcessBuilder(cmd).directory(babelPath.getParent().toFile()).start();
            String output, err;

            try (BufferedReader stdBr = new BufferedReader(new InputStreamReader(process.getInputStream()));
                    BufferedReader errBr = new BufferedReader(new InputStreamReader(process.getErrorStream()))) {

                output = stdBr.lines().collect(java.util.stream.Collectors.joining("\n"));
                err = errBr.lines().collect(java.util.stream.Collectors.joining("\n"));
                process.waitFor();
            }

            if (process.exitValue() != 0)
                throw new AnalysisException("Error occurred while running babel:\n" + err);

            if (!Options.get().isQuietEnabled())
                System.out.println(output);

            Matcher m = successPattern.matcher(output);
            if (!m.find()) {
                log.warn("Babel might not have run successfully!\n" + output);
            } else {
                log.info(m.group());
            }
        } catch (InterruptedException | IOException e) {
            throw new AnalysisException("Error occurred while running babel:\n" + e);
        }

        Set<Path> packageJsonFiles = newSet();
        Set<Path> babelFiles = newSet();
        try {
            babelFiles = Files.walk(babelRoot).filter(Files::isRegularFile).collect(Collectors.toSet());
        } catch (IOException e) {
            log.warn("Failed to collect babel output files:\n" + e + "\nFiles listed as TAJS arguments will not have their paths translated\nSoundness tester options may also be affected");
            return babelRoot;
        }

        // Override soundness tester options with new files
        if (Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomaticallyForHTMLFiles()
            || Options.get().getSoundnessTesterOptions().isGenerateOnlyIncludeAutomatically()) {

            Options.get().getSoundnessTesterOptions().setOnlyIncludesForInstrumentation(Optional.of(babelFiles));
            // rootDirFromMainFile can keep its value
        }

        for (Path babelFile : babelFiles) {
            log.info("BABEL OUTPUT FILE " + babelFile);
        }

        // Set arguments to babel output files + any arguments that were not
        // transformed by babel.
        //
        // TODO: Is three still a need for a "program entry convention" from
        // last or first entry in args?
        Set<Path> argFiles = newSet(babelFiles);

        // Copy package.json files into babel output directory to ensure
        // alignment with TAJS input source files.
        try {
            packageJsonFiles = Files.walk(realCommonAncestor)
                .filter(path -> path.getFileName().toString().equals("package.json"))
                .collect(Collectors.toSet());
            for (Path f : packageJsonFiles) { log.info("PACKAGE JSON" + f); }
            packageJsonFiles.stream().forEach(packageJson -> {
                Path source = packageJson;
                Path target = babelRoot.resolve(realCommonAncestor.relativize(packageJson));
                try {
                    Files.copy(source, target);
                } catch (IOException e) {
                    log.warn("Failed to copy package.json file" + source + " -> " + target + "\n" + e + "\nThis may affect NodeJS module loading analysis");
                }
                argFiles.add(target);
            });
        } catch (IOException e) {
            log.warn("Failed to collect package.json files:\n" + e + "\nThis may affect NodeJS module loading analysis");
        }

        // Set arguments to argFiles, taking care to put (possibly babel'ized)
        // program entry as the last argument.
        Path programEntry = Lists.getLast(args);
        Path babelProgramEntry = babelRoot.resolve(realCommonAncestor.relativize(PathAndURLUtils.toRealPath(programEntry)));
        Path actualProgramEntry = null;
        if (argFiles.contains(babelProgramEntry)) {
            argFiles.remove(babelProgramEntry);
            actualProgramEntry = babelProgramEntry;
        } else {
            actualProgramEntry = programEntry;
        }
        args.clear();
        args.addAll(argFiles);
        args.add(actualProgramEntry);

        return babelRoot;
    }
}
