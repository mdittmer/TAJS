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

import dk.brics.tajs.options.Options;
import dk.brics.tajs.util.Lists;

import org.apache.log4j.Logger;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static dk.brics.tajs.util.Collections.newSet;

public class SrcDir {

    private static final Logger log = Logger.getLogger(SrcDir.class);

    private static final Set<String> supportedFileExtensions = newSet(Arrays.asList(".js", ".cjs", ".json"));

    /**
     * TODO: Document this.
     *
     * @param dir TODO: Document this.
     */
    public static Path translate(Path dir) throws IOException {
        if (Options.get().getArguments().size() != 1) {
            throw new IOException("SrcDir expects exactly one cmdline argument");
        }

        Path srcRoot = Paths.get(Options.get().getOutDir()).resolve("src");

        try {
            Files.walk(srcRoot)
                .sorted(Comparator.reverseOrder())
                .map(Path::toFile)
                .forEach(File::delete);
        } catch (IOException e) {
            log.warn("Error deleting source output directory: " + e);
        }

        Files.createDirectories(srcRoot);

        Set<Path> inFilePaths = Files.walk(dir)
            .filter(path -> supportedFileExtensions.stream().anyMatch(ext -> path.getFileName().toString().endsWith(ext)))
            .map(Path::toFile)
            .filter(File::isFile)
            .map(File::getPath)
            .map(Paths::get)
            .collect(Collectors.toSet());

        Set<Path> argFiles = newSet();
        for (Path srcPath : inFilePaths) {
            Path source = srcPath;
            Path target = srcRoot.resolve(dir.relativize(srcPath));
            try {
                Files.createDirectories(target.getParent());
            } catch (IOException e) {}
            Files.copy(source, target);
            argFiles.add(target);
        }

        // Set arguments to argFiles, taking care to put (possibly copied)
        // program entry as the last argument.
        List<Path> args = Options.get().getArguments();
        Path programEntry = Lists.getLast(args);
        Path srcProgramEntry = srcRoot.resolve(dir.relativize(programEntry));
        Path actualProgramEntry = null;
        if (argFiles.contains(srcProgramEntry)) {
            argFiles.remove(srcProgramEntry);
            actualProgramEntry = srcProgramEntry;
        } else {
            actualProgramEntry = programEntry;
        }
        args.clear();
        args.addAll(argFiles);
        args.add(actualProgramEntry);

        return srcRoot;
    }
}
