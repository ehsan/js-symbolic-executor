/*
 * Copyright 2010 Google Inc.
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

package symbolicexecutor;

import com.google.common.io.Files;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;

/**
 * Helper class to load files and compute paths off a given base directory. 
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class FileLoader {
  private final String basePath;

  /**
   * Creates a FileLoader with the current directory as the base directory.
   */
  public FileLoader() {
    this(".");
  }

  /**
   * @param basePath The base directory for finding files. This will be
   *        prepended to any non-absolute path names for files that should be
   *        loaded.
   */
  public FileLoader(String basePath) {
    this.basePath = new File(basePath).getAbsolutePath() + File.separator;
  }

  /**
   * Reads all characters from a file into a String, using the base path unless
   * the file's path name is absolute.
   * @see Files#toString()
   */
  public String toString(String filename) throws IOException {
    return Files.toString(new File(getPath(filename)),
        Charset.defaultCharset());
  }

  /**
   * @return filename, if it is an absolute path; otherwise, filename prepended
   *         with the previously supplied basePath.
   */
  public String getPath(String filename) {
    File file = new File(filename);
    if (file.isAbsolute()) {
      return filename;
    }
    return basePath + filename;
  }
}
