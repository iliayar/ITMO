package ru.akirakozov.sd.refactoring.servlet;

import java.io.IOException;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.templates.HTMLTemplate;
import ru.akirakozov.sd.refactoring.templates.Template;

public abstract class AbstractGetHtmlServlet extends HttpServlet {

  protected Database database;
  protected Template template;
  
  public AbstractGetHtmlServlet(Database database) {
    this.database = database;
    this.template = new HTMLTemplate();
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    try {
      response.getWriter().write(handle(request));
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    response.setContentType("text/html");
    response.setStatus(HttpServletResponse.SC_OK);
  }

  abstract protected String handle(HttpServletRequest request) throws Exception;

}
