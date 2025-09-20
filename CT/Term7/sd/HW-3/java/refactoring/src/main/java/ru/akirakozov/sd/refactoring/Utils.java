package ru.akirakozov.sd.refactoring;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.stream.Collectors;

public class Utils {
  public static String getResource(ClassLoader classLoader, String filename) {
    InputStream inputStream = classLoader.getResourceAsStream(filename);
    BufferedReader input = new BufferedReader(new InputStreamReader(inputStream));

    String script = input.lines().collect(Collectors.joining("\n"));
    return script;
  }
}
