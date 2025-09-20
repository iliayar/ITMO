package ru.akirakozov.sd.refactoring;

import static org.junit.jupiter.api.Assertions.*;

import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.database.SQLite;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.Statement;

public class ServerTest {

  private static final String HOST = "http://localhost:8080";

  private static App app;

  private static SQLite database;

  @BeforeEach
  public void cleanDb() throws Exception {
    try (Connection c = DriverManager.getConnection("jdbc:sqlite:test.db")) {
      String sql = "DELETE FROM Product";
      Statement stmt = c.createStatement();

      stmt.executeUpdate(sql);
      stmt.close();
    }
  }

  @BeforeAll
  static public void runServer() {
    try {
      database = new SQLite("test.db");
      database.init();
      app = new App(database, 8080);
      app.start();
    } catch (Exception e) {
      System.err.println("Failed start app: " + e.toString());
    }
  }

  @AfterAll
  static public void stopServer() {
    try {
      app.stop();
      database.close();
    } catch (Exception e) {
    }
  }

  public String get(String path, Map<String, String> queryValues) throws Exception {
    String query = "";
    if (!queryValues.isEmpty()) {
      StringBuilder queryBuilder = new StringBuilder();
      int i = 0;
      for (Entry<String, String> e : queryValues.entrySet()) {
        queryBuilder.append(i == 0 ? "?" : "&");
        queryBuilder.append(URLEncoder.encode(e.getKey(), "UTF-8"));
        queryBuilder.append("=");
        queryBuilder.append(URLEncoder.encode(e.getValue(), "UTF-8"));
        i++;
      }
      query = queryBuilder.toString();
    }

    URL url = new URL(HOST + path + query);
    HttpURLConnection con = (HttpURLConnection) url.openConnection();
    con.setRequestMethod("GET");

    int statusCode = con.getResponseCode();

    assertEquals(statusCode, 200);

    BufferedReader in = new BufferedReader(new InputStreamReader(con.getInputStream()));
    String line;
    StringBuffer content = new StringBuffer();
    while ((line = in.readLine()) != null) {
      content.append(line + "\n");
    }
    in.close();
    con.disconnect();

    return content.toString();
  }

  void addProduct(String name, long price) throws Exception {
    Map<String, String> query = new HashMap<>();
    query.put("name", name);
    query.put("price", String.valueOf(price));
    String resp = get("/add-product", query);
    assertEquals(resp, "OK\n");
  }

  @Test
  public void testAddProducts() throws Exception {
    addProduct("Test1", 1);
    addProduct("Test2", 2);
    addProduct("Test3", 3);
  }

  @Test
  public void testGetProducts() throws Exception {
    String resp;

    addProduct("Test1", 1);
    addProduct("Test2", 2);

    resp = get("/get-products", new HashMap<>());
    assertEquals(resp, "<html><body>\n"
                 + "Test1\t1</br>\n"
                 + "Test2\t2</br>\n"
        + "</body></html>\n");

    addProduct("Test3", 3);

    resp = get("/get-products", new HashMap<>());
    assertEquals(resp, "<html><body>\n"
                 + "Test1\t1</br>\n"
                 + "Test2\t2</br>\n"
                 + "Test3\t3</br>\n"
        + "</body></html>\n");

  }

  @Test
  public void testQueryMax() throws Exception {
    String resp;
    Map<String, String> query = new HashMap<>();
    query.put("command", "max");

    addProduct("Test1", 1);
    addProduct("Test2", 2);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "<h1>Product with max price: </h1>\n"
                 + "Test2\t2</br>\n"
        + "</body></html>\n");

    addProduct("Test3", 3);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "<h1>Product with max price: </h1>\n"
                 + "Test3\t3</br>\n"
        + "</body></html>\n");

  }

  @Test
  public void testQueryMin() throws Exception {
    String resp;
    Map<String, String> query = new HashMap<>();
    query.put("command", "min");

    addProduct("Test1", 1);
    addProduct("Test2", 2);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "<h1>Product with min price: </h1>\n"
                 + "Test1\t1</br>\n"
        + "</body></html>\n");

    addProduct("Test3", 0);


    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "<h1>Product with min price: </h1>\n"
                 + "Test3\t0</br>\n"
        + "</body></html>\n");

  }

  @Test
  public void testQuerySum() throws Exception {
    String resp;
    Map<String, String> query = new HashMap<>();
    query.put("command", "sum");

    addProduct("Test1", 1);
    addProduct("Test2", 2);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "Summary price: \n"
                 + "3\n"
        + "</body></html>\n");

    addProduct("Test3", 3);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "Summary price: \n"
                 + "6\n"
        + "</body></html>\n");

  }

  @Test
  public void testQueryCount() throws Exception {
    String resp;
    Map<String, String> query = new HashMap<>();
    query.put("command", "count");


    addProduct("Test1", 1);
    addProduct("Test2", 2);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "Number of products: \n"
                 + "2\n"
        + "</body></html>\n");

    addProduct("Test3", 3);

    resp = get("/query", query);
    assertEquals(resp, "<html><body>\n"
                 + "Number of products: \n"
                 + "3\n"
        + "</body></html>\n");

  }
}
