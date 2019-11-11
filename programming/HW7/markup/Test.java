package markup;

import java.util.*;

public class Test {

    public static void main(String[] args) {
        Paragraph paragraph = new Paragraph(List.of(
            new Strong(List.of(
                new Text("1"),
                new Strikeout(List.of(
                    new Text("2"),
                    new Header(List.of(
                        new Text("3"),
                        new Text("4")
                    ),2),
                    new Text("5")
                )),
                new Text("6")
            ))
        ));
        StringBuilder sb = new StringBuilder();
        paragraph.toHtml(sb);
        System.out.println("sb: " + sb.toString());
    }

}